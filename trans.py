"""
알라딘 TTB: ISBN → 역자·저자 식별(ItemLookUp) → 커리어 수집
→ 하이브리드 원서 언어·국가 판정(저자·도서 우선, 번역가 전공/커리어 폴백, LLM 단일 호출).

- AuthorId 보완: 도서 상세 HTML에서 BeautifulSoup으로 AuthorSearch= 링크 매칭
- 원서 판정: determine_origin_country_by_llm (OpenAI JSON) 또는 휴리스틱 폴백
"""
from __future__ import annotations

import html as html_stdlib
import json
import os
import re
import urllib.error
import urllib.request
from collections import defaultdict
from typing import Any, Dict, List, Mapping, MutableMapping, Optional, Tuple

import requests
import streamlit as st
from bs4 import BeautifulSoup

# ---------------------------------------------------------------------------
# 설정 · 상수
# ---------------------------------------------------------------------------

ITEM_LOOKUP = "http://www.aladin.co.kr/ttb/api/ItemLookUp.aspx"
ITEM_SEARCH = "http://www.aladin.co.kr/ttb/api/ItemSearch.aspx"
ALADIN_WAUTHOR_OVERVIEW = "https://www.aladin.co.kr/author/wauthor_overview.aspx"
ALADIN_WSEARCH = "https://www.aladin.co.kr/search/wsearchresult.aspx"
ALADIN_WPRODUCT = "https://www.aladin.co.kr/shop/wproduct.aspx"
WSEARCH_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)
ITEM_ID_HTML_RE = re.compile(r"itemid=(\d+)", re.I)  # ItemId / itemid 대소문자 무시
BIO_PROFILE_KEYWORDS = ("대학교", "학과", "졸업", "역서", "번역", "전공", "출신", "소개")
API_VERSION = "20131101"
OPT_LOOKUP = "authors,categoryIdList,fulldescription,Story,toc"

# ItemLookUp 역자 추출용 (역할 표기 다양성)
TRANSLATOR_ROLE_STRICT = ("옮긴이", "역자", "옮김", "번역")


def _role_is_translator(role: str) -> bool:
    r = (role or "").strip()
    if not r:
        return False
    if any(m in r for m in TRANSLATOR_ROLE_STRICT):
        return True
    if "역" in r and not any(x in r for x in ("지은이", "지음", "감수", "교정", "편집")):
        return True
    return False


# 역자 커리어 필터: 사용자 지정 역할 키워드만 사용
_TRANSLATOR_MARKERS_FOR_CATALOG = ("옮긴이", "역자", "역", "옮김")


def _author_name_equals_target(target: str, author_name: str) -> bool:
    return target.strip() == (author_name or "").strip()


def _fallback_translator_role_from_raw_author(raw_author: str, target_name: str) -> bool:
    """
    ItemSearch 등에서 subInfo.authors가 비었을 때, book['author'] 한 줄에서
    타겟 이름과 역자 표기가 같은 쉼표 구간에 묶였는지 Regex로 판별.
    """
    t = target_name.strip()
    blob = (raw_author or "").strip()
    if not t or not blob:
        return False
    esc = re.escape(t)

    for chunk in re.split(r"\s*,\s*", blob):
        ch = chunk.strip()
        if t not in ch:
            continue

        # 이 구간이 "이름 (지은이|그림|…)"만 담당하면 역자로 보지 않음
        if re.fullmatch(
            rf"{esc}\s*\(\s*(?:지은이|지음|그림|편집|감수|일러스트|사진|촬영)\s*\)",
            ch,
            re.UNICODE,
        ):
            continue

        # 이름 직후 괄호 안에 역자 키워드
        if re.search(
            rf"{esc}\s*\([^)]*(?:옮긴이|역자|옮김|번역)[^)]*\)",
            ch,
            re.UNICODE,
        ):
            return True
        # 이름 (역) — '역' 단독 역할
        if re.search(rf"{esc}\s*\(\s*역\s*\)", ch, re.UNICODE):
            return True
        # 괄호 없이 "이름 옮김" 등
        if re.search(
            rf"{esc}\s+(?:옮긴이|역자|옮김|번역)(?=\s*(?:,|$))",
            ch,
            re.UNICODE,
        ):
            return True
        # 유연 패턴: 이름 + 선택 '(' + … 역자 키워드 … + 선택 ')'
        # '역'은 앞뒤가 비한글일 때만 (역사, 지은이 등 오탐 완화)
        if re.search(
            rf"{esc}\s*\(?[^)]*"
            r"(?:옮긴이|역자|옮김|번역|(?<![가-힣])역(?![가-힣]))"
            r"[^)]*\)?",
            ch,
            re.UNICODE,
        ):
            return True
    return False


def is_translator_role(book: dict, target_name: str) -> bool:
    """
    subInfo.authors가 있으면 구조화된 역할로 판별.
    authors가 비었거나 없으면 book['author'] 원시 문자열 Regex 폴백.
    """
    sub = book.get("subInfo") or {}
    authors = sub.get("authors")
    if isinstance(authors, list) and len(authors) > 0:
        for auth in authors:
            if not isinstance(auth, dict):
                continue
            if not _author_name_equals_target(target_name, (auth.get("authorName") or "")):
                continue
            desc = (auth.get("authorTypeDesc") or "") + ""
            name_t = (auth.get("authorTypeName") or "") + ""
            role_blob = f"{desc} {name_t}"
            if any(marker in role_blob for marker in _TRANSLATOR_MARKERS_FOR_CATALOG):
                return True
        return False
    return _fallback_translator_role_from_raw_author(book.get("author") or "", target_name)


# ---------------------------------------------------------------------------
# 알라딘 API
# ---------------------------------------------------------------------------


def _get_json(url: str, params: dict, timeout: int = 15) -> dict:
    r = requests.get(url, params=params, timeout=timeout)
    r.raise_for_status()
    return r.json()


def item_lookup(
    isbn_clean: str,
    ttbkey: str,
    opt_result: str = OPT_LOOKUP,
    item_id_type: Optional[str] = None,
) -> dict:
    if item_id_type:
        itype = item_id_type
    else:
        itype = "ISBN13" if len(isbn_clean) == 13 else "ISBN"
    params = {
        "ttbkey": ttbkey.strip(),
        "itemIdType": itype,
        "ItemId": isbn_clean,
        "output": "js",
        "Version": API_VERSION,
        "OptResult": opt_result,
    }
    return _get_json(ITEM_LOOKUP, params)


def _aladin_web_headers() -> Dict[str, str]:
    return {
        "User-Agent": WSEARCH_USER_AGENT,
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Accept-Language": "ko-KR,ko;q=0.9,en-US;q=0.8,en;q=0.7",
        "Referer": "https://www.aladin.co.kr/",
    }


def _extract_item_ids_from_html(html: str) -> List[str]:
    """HTML 본문에서 itemid= 숫자 패턴 추출 (대소문자·파라미터 순서 무관)."""
    if not html:
        return []
    seen: set[str] = set()
    out: List[str] = []
    for iid in ITEM_ID_HTML_RE.findall(html):
        if iid not in seen:
            seen.add(iid)
            out.append(iid)
    return out


def _fetch_html_item_ids(url: str, params: dict) -> Tuple[List[str], int]:
    resp = requests.get(
        url,
        params=params,
        headers=_aladin_web_headers(),
        timeout=15,
    )
    resp.raise_for_status()
    text = resp.text or ""
    return _extract_item_ids_from_html(text), len(text)


def get_item_ids_by_author_id(author_id: int, name: str = "") -> List[str]:
    """
    알라딘 통합 검색 및 프로필 개요 페이지에서 ItemId 수집 (투트랙 방식).
    알라딘 서버는 wsearchresult에서 반드시 '이름@ID' 형식을 요구함.
    """
    item_ids = []
    len_search, len_overview = 0, 0

    # 1. wsearchresult.aspx (통합 검색 - 이름@ID 필수)
    # requests가 params를 통해 자동으로 URL 인코딩(%EC...)을 처리함.
    search_query = f"{name}@{author_id}" if name else f"@{author_id}"
    search_params = {
        "AuthorSearch": search_query,
    }
    try:
        ids_1, len_search = _fetch_html_item_ids(ALADIN_WSEARCH, search_params)
        item_ids.extend(ids_1)
    except Exception:
        pass

    # 2. wauthor_overview.aspx (개요 페이지의 '대표작' 크롤링 보완)
    # 이 페이지는 @ID 만으로도 정상 동작함
    overview_params = {
        "AuthorSearch": f"@{author_id}"
    }
    try:
        ids_2, len_overview = _fetch_html_item_ids(ALADIN_WAUTHOR_OVERVIEW, overview_params)
        item_ids.extend(ids_2)
    except Exception:
        pass

    # 중복 제거
    final_ids = list(dict.fromkeys(item_ids))

    if not final_ids:
        st.warning(
            f"⚠️ 도서 ID 추출 실패. 검색응답({len_search}자), 개요응답({len_overview}자). "
            "알라딘 봇 차단(CAPTCHA)이거나 데이터가 없습니다."
        )

    return final_ids


def _html_to_bio_text_lines(raw_html: str) -> List[str]:
    """script/style 제거 후 HTML 태그를 벗긴 순수 텍스트 줄 목록."""
    if not raw_html:
        return []
    s = re.sub(r"<script\b[^>]*>[\s\S]*?</script>", "", raw_html, flags=re.I)
    s = re.sub(r"<style\b[^>]*>[\s\S]*?</style>", "", s, flags=re.I)
    s = re.sub(r"<br\s*/?>", "\n", s, flags=re.I)
    s = re.sub(r"</p>", "\n", s, flags=re.I)
    s = re.sub(r"<[^>]+>", "\n", s)
    s = html_stdlib.unescape(s)
    lines: List[str] = []
    for line in s.splitlines():
        line = re.sub(r"\s+", " ", line).strip()
        if len(line) >= 8:
            lines.append(line)
    return lines


def scrape_author_bio_from_overview(author_id: int) -> str:
    """
    wauthor_overview 프로필 HTML에서 학력·번역 경력 키워드가 포함된 소개 블록 추출.
    """
    try:
        resp = requests.get(
            ALADIN_WAUTHOR_OVERVIEW,
            params={"AuthorSearch": f"@{author_id}"},
            headers=_aladin_web_headers(),
            timeout=15,
        )
        resp.raise_for_status()
    except requests.RequestException:
        return ""

    lines = _html_to_bio_text_lines(resp.text or "")
    hits = [ln for ln in lines if any(kw in ln for kw in BIO_PROFILE_KEYWORDS)]
    return "\n\n".join(dict.fromkeys(hits))


def item_search_translator_catalog(
    translator_display_name: str, ttbkey: str, max_results: int = 50
) -> dict:
    params = {
        "ttbkey": ttbkey.strip(),
        "QueryType": "Author",
        "Query": translator_display_name.strip(),
        "MaxResults": str(max_results),
        "start": "1",
        "SearchTarget": "Book",
        "output": "js",
        "Version": API_VERSION,
        "OptResult": "authors",
    }
    return _get_json(ITEM_SEARCH, params)


def item_lookup_minimal(isbn13: str, ttbkey: str) -> dict:
    params = {
        "ttbkey": ttbkey.strip(),
        "itemIdType": "ISBN13",
        "ItemId": isbn13.replace("-", "").strip(),
        "output": "js",
        "Version": API_VERSION,
        "OptResult": "authors",
    }
    return _get_json(ITEM_LOOKUP, params)


# ---------------------------------------------------------------------------
# 역자 식별 · 저자 페이지 URL
# ---------------------------------------------------------------------------


def aladin_author_page_url(author_id: Optional[int]) -> Optional[str]:
    if author_id is None:
        return None
    return f"https://www.aladin.co.kr/author/wauthor_overview.aspx?AuthorSearch=@{author_id}"


def _author_dict_extra_link(auth: dict) -> Optional[str]:
    for k, v in auth.items():
        if not isinstance(v, str) or "aladin.co.kr" not in v:
            continue
        if "wauthor" in v or "author" in v.lower():
            return v.split()[0] if v else None
    return None


def extract_translators_from_item(item: dict) -> List[dict]:
    out: List[dict] = []
    raw_author = item.get("author") or ""
    authors_list = (item.get("subInfo") or {}).get("authors") or []

    for auth in authors_list:
        if not isinstance(auth, dict):
            continue
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "") + ""
        if not _role_is_translator(role):
            continue
        name = (auth.get("authorName") or "").strip()
        if not name:
            continue
        aid = auth.get("authorId")
        try:
            aid_int = int(aid) if aid is not None else None
        except (TypeError, ValueError):
            aid_int = None
        link = _author_dict_extra_link(auth) or aladin_author_page_url(aid_int)
        out.append(
            {
                "name": name,
                "authorId": aid_int,
                "authorPageUrl": link,
                "role": role,
                "_raw": auth,
            }
        )

    if not out and raw_author:
        for part in raw_author.split(","):
            if any(k in part for k in ["옮긴이", "역자", "옮김", "역"]):
                name = re.sub(
                    r"\(.*?\)|옮긴이|역자|옮김|지은이|지음|역",
                    "",
                    part,
                    flags=re.I,
                ).strip()
                if name:
                    out.append(
                        {
                            "name": name,
                            "authorId": None,
                            "authorPageUrl": None,
                            "role": "문자열파싱",
                            "_raw": None,
                        }
                    )
    return out


def _role_is_writer(role: str) -> bool:
    r = (role or "").strip()
    return any(k in r for k in ("지은이", "지음", "글"))


def extract_writers_from_item(item: dict) -> List[dict]:
    out: List[dict] = []
    raw_author = item.get("author") or ""
    authors_list = (item.get("subInfo") or {}).get("authors") or []

    for auth in authors_list:
        if not isinstance(auth, dict):
            continue
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "") + ""
        if not _role_is_writer(role):
            continue
        name = (auth.get("authorName") or "").strip()
        if not name:
            continue
        aid = auth.get("authorId")
        try:
            aid_int = int(aid) if aid is not None else None
        except (TypeError, ValueError):
            aid_int = None
        link = _author_dict_extra_link(auth) or aladin_author_page_url(aid_int)
        out.append(
            {
                "name": name,
                "authorId": aid_int,
                "authorPageUrl": link,
                "role": role,
                "_raw": auth,
            }
        )

    if not out and raw_author:
        for part in raw_author.split(","):
            if any(k in part for k in ["지은이", "지음", "글"]):
                if any(k in part for k in ["옮긴이", "역자", "옮김"]):
                    continue
                name = re.sub(
                    r"\(.*?\)|지은이|지음|글|옮긴이|역자|옮김",
                    "",
                    part,
                    flags=re.I,
                ).strip()
                if name:
                    out.append(
                        {
                            "name": name,
                            "authorId": None,
                            "authorPageUrl": None,
                            "role": "문자열파싱",
                            "_raw": None,
                        }
                    )
    return out


def _product_page_item_id(item: dict, isbn_fallback: str = "") -> Optional[str]:
    """도서 상세 웹페이지용 ItemId (API itemId 우선, 없으면 ISBN13)."""
    for key in ("itemId", "item_id"):
        v = item.get(key)
        if v is not None and str(v).strip():
            return str(v).strip()
    isbn = (item.get("isbn13") or item.get("isbn") or isbn_fallback or "").replace(
        "-", ""
    ).strip()
    return isbn or None


def fetch_product_page_html(item_id: str) -> str:
    headers = {"User-Agent": WSEARCH_USER_AGENT}
    resp = requests.get(
        ALADIN_WPRODUCT,
        params={"ItemId": item_id},
        headers=headers,
        timeout=15,
    )
    resp.raise_for_status()
    return resp.text


AUTHOR_SEARCH_HREF_ID_RE = re.compile(
    r"AuthorSearch=(?:[^&]*?@)?(\d+)", re.I
)


def _extract_author_id_from_href(href: str) -> Optional[int]:
    """href 속성에서 AuthorSearch=…@숫자 또는 숫자 ID 추출."""
    if not href or "AuthorSearch=" not in href:
        return None
    m = AUTHOR_SEARCH_HREF_ID_RE.search(href)
    if not m:
        return None
    try:
        return int(m.group(1))
    except (TypeError, ValueError):
        return None


def resolve_author_id_from_product_html(
    html: str, target_name: str
) -> Optional[int]:
    """
    상품 페이지 HTML에서 href에 'AuthorSearch='가 포함된 <a> 태그를 탐색하고,
    앵커 텍스트가 target_name(역자·저자 등)과 일치할 때 href에서 숫자 ID를 반환한다.
    """
    t = (target_name or "").strip()
    if not t or not html:
        return None

    soup = BeautifulSoup(html, "html.parser")
    for anchor in soup.find_all("a", href=True):
        href = anchor.get("href") or ""
        if "AuthorSearch=" not in href:
            continue
        text = anchor.get_text(separator=" ", strip=True)
        text = re.sub(r"\s+", " ", text).strip()
        if not _author_name_equals_target(t, text):
            continue
        aid = _extract_author_id_from_href(href)
        if aid is not None:
            return aid
    return None


def scrape_author_id_from_product_page(
    item_id: str, translator_name: str
) -> Optional[int]:
    try:
        html = fetch_product_page_html(item_id)
    except requests.RequestException:
        return None
    return resolve_author_id_from_product_html(html, translator_name)


def enrich_translators_author_id_from_web(
    translators: List[dict],
    item: dict,
    isbn_fallback: str = "",
) -> List[dict]:
    """
    authorId가 비어 있는 역자에 대해 도서 상세 페이지 HTML에서 ID를 보완한다.
    """
    pid = _product_page_item_id(item, isbn_fallback)
    if not pid:
        return translators
    needs = [tr for tr in translators if tr.get("authorId") is None]
    if not needs:
        return translators

    html: Optional[str] = None
    for tr in needs:
        if html is None:
            try:
                html = fetch_product_page_html(pid)
            except requests.RequestException:
                return translators
        aid = resolve_author_id_from_product_html(html, tr["name"])
        if aid is None:
            continue
        tr["authorId"] = aid
        tr["authorPageUrl"] = aladin_author_page_url(aid)
        role = (tr.get("role") or "").strip()
        if role == "문자열파싱":
            tr["role"] = "문자열파싱(웹크롤링ID보완)"
        elif "웹크롤링ID보완" not in role:
            tr["role"] = f"{role}(웹크롤링ID보완)" if role else "웹크롤링ID보완"
    return translators


def extract_writer_names_from_item(item: dict) -> List[str]:
    names: List[str] = []
    for auth in (item.get("subInfo") or {}).get("authors") or []:
        if not isinstance(auth, dict):
            continue
        role = (auth.get("authorTypeDesc") or auth.get("authorTypeName") or "") + ""
        if any(k in role for k in ["지은이", "지음", "글"]):
            n = (auth.get("authorName") or "").strip()
            if n:
                names.append(n)
    if not names and item.get("author"):
        for part in item["author"].split(","):
            if "지은이" in part or "지음" in part:
                n = re.sub(r"\(.*?\)|지은이|지음|글", "", part).strip()
                if n:
                    names.append(n)
    return list(dict.fromkeys(names))


def collect_biography_text(item: dict, translator_name: str) -> str:
    chunks: List[str] = []
    sub = item.get("subInfo") or {}
    for auth in sub.get("authors") or []:
        if not isinstance(auth, dict):
            continue
        if translator_name and (auth.get("authorName") or "").strip() != translator_name.strip():
            continue
        for key in (
            "authorBio",
            "biography",
            "authorIntro",
            "intro",
            "description",
            "authorDescription",
            "profile",
        ):
            val = auth.get(key)
            if isinstance(val, str) and val.strip():
                chunks.append(val.strip())
        for k, v in auth.items():
            if k in ("authorName", "authorId", "authorTypeDesc", "authorTypeName"):
                continue
            if isinstance(v, str) and len(v) > 40:
                chunks.append(v.strip())

    for key in ("fulldescription", "fullDescription", "Story", "story", "toc", "Toc"):
        v = item.get(key) or sub.get(key)
        if isinstance(v, str) and len(v) > 80:
            chunks.append(v[:5000])

    return "\n\n".join(dict.fromkeys(chunks))


# ---------------------------------------------------------------------------
# 동명이인: 카테고리 (대분류만 느슨하게)
# ---------------------------------------------------------------------------


def category_segments(cat: Optional[str]) -> List[str]:
    if not cat:
        return []
    s = cat.replace("국내도서", "").replace("외국도서", "").replace("eBook", "")
    return [p.strip() for p in s.split(">") if p.strip()]


def category_overlap_loose(target_cat: str, book_cat: str) -> bool:
    """대분류(첫 세그먼트)만 같으면 True. 한쪽이 비어 있으면 필터를 가리지 않음."""
    ta = category_segments(target_cat)
    ba = category_segments(book_cat)
    if not ta or not ba:
        return True
    return ta[0] == ba[0]


# ---------------------------------------------------------------------------
# authors 보강 (검색 응답에 역할 정보가 없을 때)
# ---------------------------------------------------------------------------


def enrich_catalog_with_authors_lookup(
    books: List[dict], ttbkey: str, target_name: str, max_lookups: int = 25
) -> List[dict]:
    out: List[dict] = []
    lookups = 0
    for b in books:
        if is_translator_role(b, target_name):
            out.append(b)
            continue
        if lookups >= max_lookups:
            continue
        isbn = (b.get("isbn13") or b.get("isbn") or "").replace("-", "").strip()
        if len(isbn) != 13:
            continue
        try:
            data = item_lookup_minimal(isbn, ttbkey)
            lookups += 1
        except (requests.RequestException, KeyError, ValueError):
            continue
        items = data.get("item") or []
        if not items:
            continue
        merged = {**b, "subInfo": {**(b.get("subInfo") or {}), **(items[0].get("subInfo") or {})}}
        if is_translator_role(merged, target_name):
            out.append(merged)
    return out


# ---------------------------------------------------------------------------
# 원제 문자 체계 · 메타 휴리스틱
# ---------------------------------------------------------------------------

RE_KANA = re.compile(r"[\u3040-\u309F\u30A0-\u30FF]")
RE_HAN = re.compile(r"[\u4E00-\u9FFF]")
RE_LATIN = re.compile(r"[A-Za-z]")


COUNTRY_LANG_HINTS: List[Tuple[str, str]] = [
    (r"영국|영어|영문|미국|American|English", "메타_영어권"),
    (r"일본|日|ジャパン", "메타_일본"),
    (r"중국|中文|汉语", "메타_중국"),
    (r"프랑스|프랑스어|French", "메타_프랑스"),
    (r"독일|German|Deutsch", "메타_독일"),
    (r"이탈리아|Italian", "메타_이탈리아"),
    (r"스페인|Spanish|Español", "메타_스페인"),
    (r"러시아|Russian|俄", "메타_러시아"),
    (r"한국|국내", "메타_한국"),
]


def _script_weights_on_text(text: str) -> Dict[str, float]:
    w: Dict[str, float] = {}
    if not text:
        return w
    if RE_KANA.search(text):
        w["원제_가나(일본어)"] = w.get("원제_가나(일본어)", 0.0) + 2.0
    if RE_HAN.search(text):
        w["원제_한자(중국어)"] = w.get("원제_한자(중국어)", 0.0) + 1.0
        w["원제_한자(일본어)"] = w.get("원제_한자(일본어)", 0.0) + 1.0
    if RE_LATIN.search(text):
        w["원제_라틴(영미·유럽권)"] = w.get("원제_라틴(영미·유럽권)", 0.0) + 1.5
    return w


def infer_signals_from_book(book: dict) -> Dict[str, Any]:
    title = (book.get("title") or "") + " " + (book.get("description") or "")
    sub = book.get("subInfo") or {}
    ot = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
    blob = f"{title} {ot}"

    hint_weights: MutableMapping[str, float] = defaultdict(float)
    for pat, label in COUNTRY_LANG_HINTS:
        if re.search(pat, blob, re.I):
            hint_weights[label] += 1.0

    script_src = ot if ot else title
    for k, v in _script_weights_on_text(script_src).items():
        hint_weights[k] += v

    if ot and RE_LATIN.search(ot) and not re.search(r"[가-힣]", ot):
        hint_weights["원제_라틴_보조(영어 가능)"] += 0.5

    return {
        "originalTitle": ot or None,
        "hint_weights": dict(hint_weights),
        "categoryName": book.get("categoryName"),
        "publisher": book.get("publisher"),
    }


def weighted_hint_counts(books: List[dict]) -> Tuple[Dict[str, float], List[dict]]:
    counts: Dict[str, float] = {}
    rows: List[dict] = []
    for b in books:
        sig = infer_signals_from_book(b)
        row = {
            "title": b.get("title"),
            **sig,
        }
        rows.append(row)
        for label, score in sig["hint_weights"].items():
            counts[label] = counts.get(label, 0.0) + float(score)
    return counts, rows


# ---------------------------------------------------------------------------
# 전공 → 언어 (Regex 보조 + LLM)
# ---------------------------------------------------------------------------

_MAJOR_LANG_RULES: List[Tuple[str, str]] = [
    (r"노어|러시아|슬라브", "러시아어"),
    (r"영미|영어|미국문학|영문", "영어"),
    (r"불어|프랑스", "프랑스어"),
    (r"독어|독일", "독일어"),
    (r"스페인|스페인어|히스패닉", "스페인어"),
    (r"이탈리아|이태리", "이탈리아어"),
    (r"일본|일어", "일본어"),
    (r"중국|중문|한문|중어", "중국어"),
    (r"아랍|터키|페르시아|이란", "아랍어권·중동어권"),
    (r"노르웨이|스웨덴|덴마크|북유럽", "북유럽어권"),
    (r"라틴아메리카|포르투갈|브라질", "포르투갈어"),
    (r"한국어|국어국문", "한국어"),
]


def infer_language_from_major_text(major: Optional[str]) -> Optional[str]:
    if not major:
        return None
    m = major.strip()
    for pat, lang in _MAJOR_LANG_RULES:
        if re.search(pat, m, re.I):
            return lang
    return None


def extract_univ_major_regex(text: str) -> Optional[Dict[str, Optional[str]]]:
    if not text or not text.strip():
        return None
    m = re.search(
        r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부))",
        text,
    )
    if not m:
        m = re.search(
            r"([가-힣A-Za-z·\s]{2,30}(?:대학교|대학|대))\s*에서\s*([가-힣A-Za-z·\s]{2,20}(?:학과|전공|학부))",
            text,
        )
    if not m:
        return None
    uni, maj = m.group(1).strip(), m.group(2).strip()
    inferred = infer_language_from_major_text(maj)
    return {
        "university": uni,
        "major": maj,
        "inferred_language": inferred,
    }


def extract_univ_major_llm(
    text: str, api_key: str, role: str = "역자"
) -> Optional[Dict[str, Optional[str]]]:
    if not api_key or not text.strip():
        return None
    if role == "저자":
        system = (
            "You read Korean biographies of authors (writers). "
            "Extract university, major, AND infer their native language or primary writing language "
            "from the major name and bio (e.g. 영어영문학과 → 영어, 일본어문학과 → 일본어). "
            "Use concise Korean language names for inferred_language (e.g. 영어, 일본어, 중국어, 프랑스어). "
            "If impossible, use null. "
            'Reply JSON only: {"university": string|null, "major": string|null, "inferred_language": string|null}'
        )
    else:
        system = (
            "You read Korean biographies of translators. "
            "Extract university, major, AND infer the primary source language they most likely "
            "translate from, based on the major name (e.g. 노어노문학과 → 러시아어, 영어영문학과 → 영어). "
            "Use concise Korean language names for inferred_language (e.g. 러시아어, 영어, 일본어, 독일어, 중국어). "
            "If impossible, use null. "
            'Reply JSON only: {"university": string|null, "major": string|null, "inferred_language": string|null}'
        )
    body = {
        "model": os.environ.get("OPENAI_MODEL", "gpt-4o-mini"),
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": text[:8000]},
        ],
        "response_format": {"type": "json_object"},
    }
    try:
        req = urllib.request.Request(
            "https://api.openai.com/v1/chat/completions",
            data=json.dumps(body).encode("utf-8"),
            headers={
                "Content-Type": "application/json",
                "Authorization": f"Bearer {api_key}",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=60) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        raw = data["choices"][0]["message"]["content"]
        obj = json.loads(raw)
        u = obj.get("university")
        mj = obj.get("major")
        inf = obj.get("inferred_language")
        return {
            "university": (u or "").strip() or None,
            "major": (mj or "").strip() or None,
            "inferred_language": (inf or "").strip() or None,
        }
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, KeyError, IndexError):
        return None


# ---------------------------------------------------------------------------
# 최종 원서 언어 판정
# ---------------------------------------------------------------------------


def _collapse_career_hints(hints: Mapping[str, float]) -> Dict[str, float]:
    collapsed: Dict[str, float] = defaultdict(float)
    for label, score in hints.items():
        if score <= 0:
            continue
        if label.startswith("메타_"):
            w = score * 0.6
            if "일본" in label:
                collapsed["일본어"] += w
            elif "중국" in label:
                collapsed["중국어"] += w
            elif "영어" in label:
                collapsed["영어"] += w
            elif "프랑스" in label:
                collapsed["프랑스어"] += w
            elif "독일" in label:
                collapsed["독일어"] += w
            elif "스페인" in label:
                collapsed["스페인어"] += w
            elif "이탈리아" in label:
                collapsed["이탈리아어"] += w
            elif "러시아" in label:
                collapsed["러시아어"] += w
            elif "한국" in label:
                collapsed["한국어"] += w
            continue
        if "가나" in label:
            collapsed["일본어"] += score
        elif "한자(중국" in label:
            collapsed["중국어"] += score
        elif "한자(일본" in label:
            collapsed["일본어"] += score
        elif "라틴" in label or "영미" in label or "영어" in label:
            collapsed["영어"] += score
        elif "프랑스" in label:
            collapsed["프랑스어"] += score
        elif "독일" in label:
            collapsed["독일어"] += score
        elif "스페인" in label:
            collapsed["스페인어"] += score
        elif "이탈리아" in label:
            collapsed["이탈리아어"] += score
        elif "러시아" in label:
            collapsed["러시아어"] += score
        elif "한국" in label:
            collapsed["한국어"] += score
        elif "중동" in label or "아랍" in label:
            collapsed["아랍어권"] += score
        elif "북유럽" in label:
            collapsed["북유럽어권"] += score
        elif "포르투갈" in label:
            collapsed["포르투갈어"] += score
    return dict(collapsed)


def build_book_info_from_item(item: dict) -> Dict[str, Any]:
    """하이브리드 판정용 도서 메타데이터 묶음."""
    sub = item.get("subInfo") or {}
    desc_parts: List[str] = []
    for key in ("fulldescription", "fullDescription", "Story", "story", "description"):
        v = item.get(key) or sub.get(key)
        if isinstance(v, str) and v.strip():
            desc_parts.append(v.strip())
    description = "\n\n".join(dict.fromkeys(desc_parts))[:8000]
    original_title = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
    title = (item.get("title") or "").strip()
    script_src = original_title or title
    return {
        "title": title or None,
        "original_title": original_title or None,
        "categoryName": item.get("categoryName"),
        "publisher": item.get("publisher"),
        "description": description or None,
        "script_weights": _script_weights_on_text(script_src),
    }


def build_author_info_for_llm(name: str, bio: str) -> Dict[str, Any]:
    """저자(지은이) 단서: 이름·소개·문자 체계 가중치."""
    bio_s = (bio or "").strip()
    name_s = (name or "").strip()
    script_blob = f"{name_s} {bio_s[:2000]}"
    return {
        "name": name_s,
        "bio_excerpt": bio_s[:3000] if bio_s else None,
        "script_weights": _script_weights_on_text(script_blob),
        "univ_major_regex": extract_univ_major_regex(bio_s) if bio_s else None,
    }


def build_translator_info_for_llm(
    name: str,
    bio: str,
    career_hint_counts: Mapping[str, float],
    filtered_book_count: int,
) -> Dict[str, Any]:
    """번역가 단서: 전공(Regex) + 커리어 분포(폴백용)."""
    bio_s = (bio or "").strip()
    reg = extract_univ_major_regex(bio_s) if bio_s else None
    return {
        "name": (name or "").strip(),
        "bio_excerpt": bio_s[:3000] if bio_s else None,
        "univ_major_regex": reg,
        "career_hint_counts": dict(career_hint_counts),
        "filtered_translator_book_count": filtered_book_count,
    }


def determine_origin_country_by_llm(
    authors_info: List[Dict[str, Any]],
    book_info: Dict[str, Any],
    translators_info: List[Dict[str, Any]],
    api_key: str,
) -> Optional[Dict[str, Any]]:
    """
    저자·도서 정보 우선, 번역가 전공/커리어는 폴백인 하이브리드 LLM 원서 언어·국가 판정.
    """
    if not api_key or not api_key.strip():
        return None

    system = (
        "당신은 외국 문학 번역서의 원서 언어와 출신 국가를 추론하는 전문가입니다.\n\n"
        "## 추론 우선순위 (반드시 준수)\n"
        "1순위 — 저자 정보: 저자 이름의 문자 체계(script_weights), 소개글(bio_excerpt), "
        "출신 대학·모국어·집필 언어 단서(univ_major_regex). "
        "번역가의 영문학·일문학 등 전공만으로 원서 언어를 단정하지 마세요.\n"
        "2순위 — 도서 메타데이터: 원제(original_title)의 문자 체계, 카테고리(categoryName), "
        "설명(description), 제목(title).\n"
        "3순위 — 폴백만: 1·2순위 확신도가 low이거나 결정적 단서가 없을 때만 "
        "번역가의 univ_major_regex·career_hint_counts를 참고하세요.\n"
        "  - 영문학 전공 역자가 북유럽·동유럽 등 비영어권 원서를 영어 경유로 중역한 사례가 많습니다. "
        "이 경우 inferred_language는 저자/원제 기준(예: 덴마크어)으로 두고 "
        "is_indirect_translation=true로 표시하세요.\n\n"
        "## author_signal_confidence 기준\n"
        "- high: 저자 이름·소개·원제 중 2개 이상에서 일관된 언어/국가 단서\n"
        "- medium: 일부 단서만 있거나 저자·원제가 상충\n"
        "- low: 저자·도서 단서가 거의 없음\n\n"
        "반드시 JSON 객체 하나만 반환하세요. 키:\n"
        '- reasoning_process (string, 한국어, 단계별 추론)\n'
        '- author_signal_confidence ("high"|"medium"|"low")\n'
        '- inferred_language (string, 한국어 표기 예: 덴마크어, 일본어, 영어)\n'
        '- inferred_country (string, 한국어 표기 예: 덴마크, 일본, 미국)\n'
        '- is_indirect_translation (boolean)\n'
    )
    payload = {
        "authors": authors_info,
        "book": book_info,
        "translators": translators_info,
    }
    body = {
        "model": os.environ.get("OPENAI_MODEL", "gpt-4o-mini"),
        "messages": [
            {"role": "system", "content": system},
            {
                "role": "user",
                "content": json.dumps(payload, ensure_ascii=False, indent=2),
            },
        ],
        "response_format": {"type": "json_object"},
    }
    try:
        req = urllib.request.Request(
            "https://api.openai.com/v1/chat/completions",
            data=json.dumps(body).encode("utf-8"),
            headers={
                "Content-Type": "application/json",
                "Authorization": f"Bearer {api_key.strip()}",
            },
            method="POST",
        )
        with urllib.request.urlopen(req, timeout=90) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        raw = data["choices"][0]["message"]["content"]
        obj = json.loads(raw)
        conf = (obj.get("author_signal_confidence") or "low").strip().lower()
        if conf not in ("high", "medium", "low"):
            conf = "low"
        return {
            "reasoning_process": (obj.get("reasoning_process") or "").strip(),
            "author_signal_confidence": conf,
            "inferred_language": (obj.get("inferred_language") or "").strip() or "판별 불가",
            "inferred_country": (obj.get("inferred_country") or "").strip() or "판별 불가",
            "is_indirect_translation": bool(obj.get("is_indirect_translation")),
            "source": "llm",
        }
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError, KeyError, IndexError):
        return None


def _language_from_script_weights(weights: Mapping[str, float]) -> Optional[str]:
    """문자 체계 가중치 → 대표 언어 라벨."""
    if not weights:
        return None
    lang_map = {
        "원제_가나(일본어)": "일본어",
        "원제_한자(중국어)": "중국어",
        "원제_한자(일본어)": "일본어",
        "원제_라틴(영미·유럽권)": "영어",
        "원제_라틴_보조(영어 가능)": "영어",
    }
    best_label: Optional[str] = None
    best_score = 0.0
    for label, score in weights.items():
        lang = lang_map.get(label)
        if lang and score > best_score:
            best_score = score
            best_label = lang
    return best_label if best_score > 0 else None


def determine_origin_country_fallback(
    authors_info: List[Dict[str, Any]],
    book_info: Dict[str, Any],
    translators_info: List[Dict[str, Any]],
    aggregated_career_hints: Mapping[str, float],
) -> Dict[str, Any]:
    """
    OpenAI 키 없을 때: 저자·도서 우선, 번역가 전공은 마지막 폴백인 휴리스틱.
    """
    steps: List[str] = []
    author_conf = "low"

    combined_script: Dict[str, float] = defaultdict(float)
    for a in authors_info:
        for k, v in (a.get("script_weights") or {}).items():
            combined_script[k] += float(v)
    for k, v in (book_info.get("script_weights") or {}).items():
        combined_script[k] += float(v) * 1.2

    author_lang = _language_from_script_weights(combined_script)
    if author_lang:
        steps.append(f"1순위: 저자·도서 문자 체계 → {author_lang}")
        author_conf = "high" if sum(combined_script.values()) >= 2.5 else "medium"
    else:
        steps.append("1순위: 저자·도서 문자 체계 단서 부족")

    collapsed = _collapse_career_hints(aggregated_career_hints)
    career_lang: Optional[str] = None
    if collapsed:
        career_lang = max(collapsed.items(), key=lambda kv: kv[1])[0]

    translator_major_lang: Optional[str] = None
    for tr in translators_info:
        reg = tr.get("univ_major_regex") or {}
        inf = reg.get("inferred_language") if isinstance(reg, dict) else None
        if inf:
            translator_major_lang = inf
            break

    conclusion_lang = author_lang
    is_indirect = False

    if not conclusion_lang and collapsed:
        conclusion_lang = career_lang
        steps.append(f"2순위: 역자 커리어 메타·원제 힌트 → {career_lang}")
        author_conf = "medium"
    elif not conclusion_lang:
        steps.append("2순위: 커리어 힌트 부족")

    if not conclusion_lang and translator_major_lang:
        conclusion_lang = translator_major_lang
        steps.append(
            f"3순위(폴백): 번역가 전공 추정 → {translator_major_lang} "
            "(저자·도서 단서 부족)"
        )
        author_conf = "low"
    elif translator_major_lang and conclusion_lang and translator_major_lang != conclusion_lang:
        is_indirect = True
        steps.append(
            f"번역가 전공({translator_major_lang})과 저자·도서 추정({conclusion_lang}) "
            "불일치 → 중역(간접 번역) 의심"
        )

    if not conclusion_lang:
        conclusion_lang = "판별 불가"
        steps.append("최종: 판별 불가")

    country_map = {
        "일본어": "일본",
        "중국어": "중국",
        "영어": "미국",
        "프랑스어": "프랑스",
        "독일어": "독일",
        "스페인어": "스페인",
        "러시아어": "러시아",
        "한국어": "한국",
        "북유럽어권": "북유럽",
        "덴마크어": "덴마크",
    }
    inferred_country = country_map.get(conclusion_lang, "미상")

    return {
        "reasoning_process": "\n".join(steps),
        "author_signal_confidence": author_conf,
        "inferred_language": conclusion_lang,
        "inferred_country": inferred_country,
        "is_indirect_translation": is_indirect,
        "source": "heuristic",
    }


def determine_final_language(
    inferred_from_major: Optional[str],
    career_hints: Mapping[str, float],
) -> Dict[str, Any]:
    tier = 3
    reason = "커리어·전공 단서 부족"
    conclusion = "판별 불가"
    major_s = (inferred_from_major or "").strip()
    if major_s:
        return {
            "conclusion": major_s,
            "tier": 1,
            "reason": "전공(소개) 기반 추론 언어",
            "career_runner_up": None,
            "raw_career_collapse": _collapse_career_hints(career_hints),
        }

    collapsed = _collapse_career_hints(career_hints)
    if collapsed:
        best_lang, best_score = max(collapsed.items(), key=lambda kv: kv[1])
        if best_score > 0:
            conclusion = best_lang
            tier = 2
            reason = "필터링된 커리어 도서 메타·원제 문자 힌트 가중 합산"
            return {
                "conclusion": conclusion,
                "tier": tier,
                "reason": reason,
                "career_runner_up": collapsed,
                "raw_career_collapse": collapsed,
            }

    return {
        "conclusion": conclusion,
        "tier": tier,
        "reason": reason,
        "career_runner_up": None,
        "raw_career_collapse": collapsed,
    }


# ---------------------------------------------------------------------------
# Streamlit UI
# ---------------------------------------------------------------------------

st.set_page_config(page_title="알라딘 번역가 분석", layout="wide")
st.title("알라딘 번역가 · 커리어 · 원서 언어 추론")

with st.sidebar:
    st.markdown("**옵션**")
    use_category_filter = st.checkbox(
        "대분류 카테고리 필터(동명이인, 느슨)", value=True
    )
    enrich_missing_authors = st.checkbox(
        "authors 누락 시 ISBN LookUp으로 보강(느림, 호출↑)", value=False
    )
    openai_key = st.text_input(
        "OpenAI API 키(선택, 하이브리드 원서 언어·국가 LLM)",
        type="password",
        value=os.environ.get("OPENAI_API_KEY", ""),
    )

with st.form("main"):
    ttb_key = st.text_input("TTB 키", type="password")
    isbn = st.text_input("ISBN (13 또는 10)")
    submitted = st.form_submit_button("분석 실행")

if submitted:
    if not ttb_key or not isbn:
        st.error("TTB 키와 ISBN을 입력하세요.")
    else:
        isbn_clean = isbn.replace("-", "").strip()
        try:
            with st.spinner("상품 조회(ItemLookUp)…"):
                data = item_lookup(isbn_clean, ttb_key)
            if data.get("errorCode"):
                st.error(f"API 오류: {data.get('errorMessage')}")
            else:
                items = data.get("item") or []
                if not items:
                    st.warning("도서를 찾을 수 없습니다.")
                else:
                    item = items[0]
                    target_cat = item.get("categoryName") or ""
                    target_pub = (item.get("publisher") or "").strip()
                    translators = extract_translators_from_item(item)
                    if any(tr.get("authorId") is None for tr in translators):
                        with st.spinner(
                            "API에 AuthorId 없음 → 도서 페이지에서 역자 ID 보완(웹 크롤링)…"
                        ):
                            translators = enrich_translators_author_id_from_web(
                                translators, item, isbn_clean
                            )
                        found = sum(1 for tr in translators if tr.get("authorId"))
                        st.caption(
                            f"웹 페이지 AuthorId 보완: **{found}**/{len(translators)}명 "
                            f"(상품 ItemId=`{_product_page_item_id(item, isbn_clean)}`)"
                        )
                    writers = extract_writers_from_item(item)
                    if any(wr.get("authorId") is None for wr in writers):
                        with st.spinner(
                            "API에 AuthorId 없음 → 도서 페이지에서 저자 ID 보완(웹 크롤링)…"
                        ):
                            writers = enrich_translators_author_id_from_web(
                                writers, item, isbn_clean
                            )

                    st.subheader("현재 도서")
                    st.write(
                        {
                            "title": item.get("title"),
                            "publisher": target_pub,
                            "categoryName": target_cat,
                            "isbn13": item.get("isbn13") or isbn_clean,
                        }
                    )

                    authors_info_collected: List[Dict[str, Any]] = []
                    translators_info_collected: List[Dict[str, Any]] = []
                    aggregated_career_hints: Dict[str, float] = {}
                    translator_ui_rows: List[Dict[str, Any]] = []

                    if writers:
                        st.subheader("저자(지은이) · 데이터 수집")
                        for wr in writers:
                            st.divider()
                            st.success(f"저자: **{wr['name']}**")
                            st.markdown("**저자 Author ID · 알라딘 저자 페이지**")
                            st.write(
                                {
                                    "writerAuthorId": wr.get("authorId"),
                                    "writerAuthorPageUrl": wr.get("authorPageUrl")
                                    or aladin_author_page_url(wr.get("authorId")),
                                }
                            )
                            wr_bio = collect_biography_text(item, wr["name"])
                            if not (wr_bio or "").strip() and wr.get("authorId"):
                                with st.spinner(
                                    "API 소개글 없음 → 웹 프로필에서 저자 소개글 수집…"
                                ):
                                    scraped_wr_bio = scrape_author_bio_from_overview(
                                        int(wr["authorId"])
                                    )
                                if (scraped_wr_bio or "").strip():
                                    wr_bio = scraped_wr_bio.strip()
                                    st.caption(
                                        "wauthor_overview 프로필에서 저자 소개글 보완"
                                    )
                            authors_info_collected.append(
                                build_author_info_for_llm(wr["name"], wr_bio or "")
                            )
                            with st.expander("저자 소개·Regex 단서", expanded=False):
                                if wr_bio:
                                    st.text_area(
                                        "writer_biography_raw",
                                        wr_bio[:4000],
                                        height=140,
                                        key=f"bio_writer_{wr['name']}",
                                    )
                                    wr_reg = extract_univ_major_regex(wr_bio)
                                    if wr_reg:
                                        st.info(f"저자 Regex: `{wr_reg}`")
                                else:
                                    st.caption("저자 소개 텍스트가 비어 있을 수 있습니다.")

                    if not translators:
                        st.warning("번역가 정보가 없습니다.")
                    else:
                        st.subheader("번역가(역자) · 커리어 데이터 수집")
                        for tr in translators:
                            st.divider()
                            st.success(f"번역가: **{tr['name']}**")
                            st.markdown("**역자 Author ID · 알라딘 역자 페이지**")
                            st.write(
                                {
                                    "translatorAuthorId": tr.get("authorId"),
                                    "translatorAuthorPageUrl": tr.get("authorPageUrl")
                                    or aladin_author_page_url(tr.get("authorId")),
                                }
                            )

                            bio_text = collect_biography_text(item, tr["name"])
                            if not (bio_text or "").strip() and tr.get("authorId"):
                                with st.spinner(
                                    "API 소개글 없음 → 웹 프로필에서 역자 소개글 수집…"
                                ):
                                    scraped_bio = scrape_author_bio_from_overview(
                                        int(tr["authorId"])
                                    )
                                if (scraped_bio or "").strip():
                                    bio_text = scraped_bio.strip()
                                    st.caption(
                                        "wauthor_overview 프로필에서 소개글 보완 "
                                        "(Regex·LLM 입력용)"
                                    )
                            reg: Optional[Dict[str, Optional[str]]] = None
                            with st.expander("역자 소개·Regex 단서", expanded=False):
                                if bio_text:
                                    st.text_area(
                                        "biography_raw",
                                        bio_text[:4000],
                                        height=140,
                                        key=f"bio_{tr['name']}",
                                    )
                                    reg = extract_univ_major_regex(bio_text)
                                    if reg:
                                        st.info(f"역자 Regex: `{reg}`")
                                else:
                                    st.caption("역자 소개 텍스트가 비어 있을 수 있습니다.")

                            raw_list: List[dict] = []
                            author_id = tr.get("authorId")
                            if author_id is not None:
                                st.caption(
                                    f"AuthorId **{author_id}** 기반 도서 수집 "
                                    f"(통합 검색 wsearchresult → ItemLookUp, 상위 30권)"
                                )
                                with st.spinner(
                                    f"통합 검색(AuthorSearch=@{author_id}, Book)에서 "
                                    f"도서 ID 수집…"
                                ):
                                    item_ids = get_item_ids_by_author_id(
                                        int(author_id), tr["name"]
                                    )
                                st.caption(
                                    f"통합 검색에서 **{len(item_ids)}**개 ItemId 추출 "
                                    f"(API 조회는 상위 30개)"
                                )
                                lookup_ids = item_ids[:30]
                                for idx, iid in enumerate(lookup_ids, start=1):
                                    with st.spinner(
                                        f"ItemLookUp ({idx}/{len(lookup_ids)}) "
                                        f"ItemId={iid}…"
                                    ):
                                        try:
                                            lk = item_lookup(
                                                iid,
                                                ttb_key,
                                                opt_result="authors",
                                                item_id_type="ItemId",
                                            )
                                        except requests.RequestException:
                                            continue
                                        for it in lk.get("item") or []:
                                            if isinstance(it, dict):
                                                raw_list.append(it)
                                st.markdown(
                                    f"**역자 검색 원본**: {len(raw_list)}권 "
                                    f"(AuthorId=`{author_id}`, "
                                    f"검색 AuthorSearch=`@{author_id}`)"
                                )
                            else:
                                st.caption(
                                    "AuthorId 없음 → 역자명 ItemSearch 폴백 (동명이인 혼입 가능)"
                                )
                                with st.spinner(
                                    "역자명 ItemSearch (OptResult=authors) 최대 50권…"
                                ):
                                    author_json = item_search_translator_catalog(
                                        tr["name"], ttb_key, 50
                                    )
                                raw_list = author_json.get("item") or []
                                st.markdown(
                                    f"**역자 검색 원본**: {len(raw_list)}권 "
                                    f"(Query=`{tr['name']}`, 이름 기반 폴백)"
                                )

                            n_role_raw = sum(
                                1 for b in raw_list if is_translator_role(b, tr["name"])
                            )
                            work_list: List[dict] = list(raw_list)
                            if enrich_missing_authors and n_role_raw < max(1, len(raw_list)) * 0.3:
                                with st.spinner("ISBN LookUp으로 authors 보강(제한)…"):
                                    work_list = enrich_catalog_with_authors_lookup(
                                        raw_list, ttb_key, tr["name"], max_lookups=25
                                    )
                                st.caption(
                                    f"보강 후 `is_translator_role` 통과 후보: **{len(work_list)}**권 "
                                    f"(원본 대비 역자 명시 적을 때만 보강)"
                                )

                            filtered = [
                                b
                                for b in work_list
                                if is_translator_role(b, tr["name"])
                                and (
                                    not use_category_filter
                                    or category_overlap_loose(
                                        target_cat, b.get("categoryName") or ""
                                    )
                                )
                            ]
                            if use_category_filter and len(filtered) == 0 and work_list:
                                st.warning(
                                    "카테고리 필터를 적용하면 분석 대상이 0권이 되어, "
                                    "필터를 임시 해제하고 분석을 진행합니다. "
                                    "(동명이인 데이터가 섞여 있을 수 있습니다.)"
                                )
                                filtered = list(work_list)

                            n_role_work = sum(
                                1 for b in work_list if is_translator_role(b, tr["name"])
                            )
                            st.caption(
                                f"`is_translator_role` 통과: **{n_role_work}**권 / 작업 목록 "
                                f"**{len(work_list)}**권 → 최종 필터 후 **{len(filtered)}**권"
                            )

                            counts, detail_rows = weighted_hint_counts(filtered)
                            for label, score in counts.items():
                                aggregated_career_hints[label] = (
                                    aggregated_career_hints.get(label, 0.0) + float(score)
                                )
                            translators_info_collected.append(
                                build_translator_info_for_llm(
                                    tr["name"],
                                    bio_text or "",
                                    counts,
                                    len(filtered),
                                )
                            )
                            translator_ui_rows.append(
                                {
                                    "name": tr["name"],
                                    "counts": counts,
                                    "detail_rows": detail_rows,
                                    "reg": reg,
                                    "filtered_count": len(filtered),
                                }
                            )
                            st.markdown("**커리어 언어·원제 힌트**")
                            st.json(dict(sorted(counts.items(), key=lambda x: -x[1])))

                            with st.expander("필터 통과 도서 요약"):
                                st.dataframe(
                                    [
                                        {
                                            "title": r["title"],
                                            "publisher": r.get("publisher"),
                                            "hints": json.dumps(
                                                r.get("hint_weights") or {},
                                                ensure_ascii=False,
                                            ),
                                            "originalTitle": r.get("originalTitle"),
                                        }
                                        for r in detail_rows[:50]
                                    ],
                                    use_container_width=True,
                                )

                            with st.expander("API 디버그: 현재 도서 역자 authors"):
                                st.json(
                                    [
                                        a
                                        for a in (item.get("subInfo") or {}).get("authors") or []
                                        if isinstance(a, dict)
                                        and tr["name"] in (a.get("authorName") or "")
                                    ]
                                )

                    book_info = build_book_info_from_item(item)

                    if writers or translators:
                        st.markdown("---")
                        st.subheader("최종 원서 언어 · 국가 판정 (하이브리드)")

                        origin_result: Optional[Dict[str, Any]] = None
                        if openai_key.strip():
                            with st.spinner(
                                "하이브리드 LLM: 저자·도서 우선, 번역가 폴백 (단일 호출)…"
                            ):
                                origin_result = determine_origin_country_by_llm(
                                    authors_info_collected,
                                    book_info,
                                    translators_info_collected,
                                    openai_key.strip(),
                                )
                            if origin_result is None:
                                st.warning(
                                    "LLM 호출 실패 — 휴리스틱 폴백으로 판정합니다."
                                )
                        if origin_result is None:
                            origin_result = determine_origin_country_fallback(
                                authors_info_collected,
                                book_info,
                                translators_info_collected,
                                aggregated_career_hints,
                            )
                            if not openai_key.strip():
                                st.caption(
                                    "OpenAI API 키가 없어 휴리스틱(저자·도서 우선)으로 판정했습니다."
                                )

                        st.success(
                            f"**원서 언어:** {origin_result['inferred_language']} · "
                            f"**원서 국가:** {origin_result['inferred_country']}"
                        )
                        m1, m2, m3, m4 = st.columns(4)
                        with m1:
                            st.metric(
                                "원서 언어",
                                origin_result["inferred_language"],
                            )
                        with m2:
                            st.metric(
                                "원서 국가",
                                origin_result["inferred_country"],
                            )
                        with m3:
                            st.metric(
                                "저자 단서 확신도",
                                origin_result["author_signal_confidence"],
                            )
                        with m4:
                            indirect = origin_result.get("is_indirect_translation")
                            st.metric(
                                "중역(간접 번역) 의심",
                                "예" if indirect else "아니오",
                            )

                        st.markdown("**추론 과정**")
                        st.info(origin_result.get("reasoning_process") or "(없음)")

                        with st.expander("판정 입력·결과 JSON"):
                            st.json(
                                {
                                    "book_info": book_info,
                                    "authors_info": authors_info_collected,
                                    "translators_info": translators_info_collected,
                                    "aggregated_career_hints": aggregated_career_hints,
                                    "origin_result": origin_result,
                                }
                            )

                        if translator_ui_rows:
                            with st.expander("역자별 커리어 힌트 요약"):
                                st.dataframe(
                                    [
                                        {
                                            "translator": row["name"],
                                            "filtered_books": row["filtered_count"],
                                            "top_hints": json.dumps(
                                                dict(
                                                    sorted(
                                                        row["counts"].items(),
                                                        key=lambda x: -x[1],
                                                    )[:5]
                                                ),
                                                ensure_ascii=False,
                                            ),
                                            "major_regex": json.dumps(
                                                row["reg"] or {},
                                                ensure_ascii=False,
                                            ),
                                        }
                                        for row in translator_ui_rows
                                    ],
                                    use_container_width=True,
                                )

        except requests.RequestException as e:
            st.error(f"HTTP 오류: {e}")
        except Exception as e:
            st.error(f"오류: {e}")
