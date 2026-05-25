"""
알라딘 TTB: ISBN → 역자·저자 식별(ItemLookUp) → 역자명 ItemSearch(1회) 커리어 수집
→ 하이브리드 원서 언어·국가 판정(저자·도서 우선, 번역가 전공/커리어 폴백, LLM 단일 호출).

- AuthorId·원제 보완: 도서 상세 HTML 1회 fetch 후 ID·originalTitle 파싱 재사용
- 커리어: item_search_translator_catalog (ItemSearch 최대 50권, 역자당 1회)
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
ALADIN_WPRODUCT = "https://www.aladin.co.kr/shop/wproduct.aspx"
WSEARCH_USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
)
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


# wauthor_overview: 메뉴·네비·링크 등 본문 외 레이아웃 태그 (decompose 대상)
_BIO_SCRAPE_DECOMPOSE_TAGS = (
    "script",
    "style",
    "meta",
    "noscript",
    "header",
    "footer",
    "nav",
    "aside",
    "menu",
    "form",
    "button",
    "input",
    "select",
    "label",
    "iframe",
    "link",
    "ul",
    "ol",
    "li",
    "a",
)

# 저자 소개 본문 후보 영역 (id/class 힌트, 없으면 전체 문서에서 p/div만 추출)
_BIO_SCRAPE_ROOT_PATTERNS: List[Tuple[str, str]] = [
    ("id", re.compile(r"author|writer|profile|bio", re.I)),
    ("class", re.compile(r"author|writer|profile|bio|intro", re.I)),
]


def _bio_text_from_p_and_div(root: BeautifulSoup) -> str:
    """중첩 div 중복을 줄이며 p·리프 div에서만 본문 단락을 모음."""
    chunks: List[str] = []
    for p in root.find_all("p"):
        text = p.get_text(separator=" ", strip=True)
        if len(text) >= 8:
            chunks.append(text)
    for div in root.find_all("div"):
        if div.find(["div", "p", "ul", "ol", "nav", "table"]):
            continue
        text = div.get_text(separator=" ", strip=True)
        if len(text) >= 20:
            chunks.append(text)
    return "\n\n".join(dict.fromkeys(chunks))


def scrape_author_bio_from_overview(author_id: int) -> str:
    """
    wauthor_overview 프로필 HTML에서 저자 소개 본문만 추출합니다.
    nav/ul/li/a 등 메뉴·링크 텍스트는 decompose로 제거하고 p·div 단락만 수집합니다.
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

    soup = BeautifulSoup(resp.text or "", "html.parser")

    for tag_name in _BIO_SCRAPE_DECOMPOSE_TAGS:
        for element in soup.find_all(tag_name):
            element.decompose()

    root: Any = soup
    for attr, pattern in _BIO_SCRAPE_ROOT_PATTERNS:
        found = soup.find(attrs={attr: pattern})
        if found is not None:
            root = found
            break

    bio_text = _bio_text_from_p_and_div(root)
    if bio_text:
        return bio_text

    return _bio_text_from_p_and_div(soup)


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


def _product_page_html_for_item(
    item: dict,
    isbn_fallback: str = "",
    cached_html: Optional[str] = None,
) -> Optional[str]:
    """상품 상세 HTML 1회만 fetch. cached_html이 있으면 재요청하지 않음."""
    if cached_html is not None:
        return cached_html
    pid = _product_page_item_id(item, isbn_fallback)
    if not pid:
        return None
    try:
        return fetch_product_page_html(pid)
    except requests.RequestException:
        return None


_ORIGINAL_TITLE_LABELS = frozenset({"원제", "Original Title", "原題", "原题"})


def _clean_original_title_candidate(text: str) -> Optional[str]:
    t = re.sub(r"\s+", " ", (text or "").strip())
    if len(t) < 2:
        return None
    if t in _ORIGINAL_TITLE_LABELS:
        return None
    if re.search(r"^(HOME|로그인|장바구니|국내도서|외국도서|통합검색)", t):
        return None
    return t


def scrape_original_title_from_html(html: str) -> Optional[str]:
    """
    알라딘 wproduct 상세 HTML에서 원제(Original Title) 추출.
    p_goodstit_info, '원제' 라벨 인접 텍스트, Ere_subTitle 등을 순차 시도.
    """
    if not (html or "").strip():
        return None

    soup = BeautifulSoup(html, "html.parser")

    info = soup.find(class_=re.compile(r"p_goodstit_info", re.I))
    if info:
        h1 = info.find("h1")
        h1_text = h1.get_text(strip=True) if h1 else ""
        for tag in info.find_all(["span", "h2", "h3", "em", "a"]):
            if h1 and tag in h1.descendants:
                continue
            cand = _clean_original_title_candidate(tag.get_text(separator=" ", strip=True))
            if cand and cand != h1_text and len(cand) >= 2:
                if not re.search(r"(지음|옮김|역자|출판|펴냄)\s*$", cand):
                    return cand
        if h1_text:
            for line in info.get_text(separator="\n", strip=True).splitlines():
                line = line.strip()
                if not line or line == h1_text:
                    continue
                cand = _clean_original_title_candidate(line)
                if cand and not re.search(
                    r"(지음|옮김|역자|출판|펴냄|\d{4}년|\d{4}-\d{2})",
                    cand,
                ):
                    return cand

    for lab in soup.find_all(["span", "dt", "th", "label", "b", "strong"]):
        if lab.get_text(strip=True) not in _ORIGINAL_TITLE_LABELS:
            continue
        for nxt in (
            lab.find_next_sibling(),
            lab.find_next(["dd", "span", "td", "div", "a"]),
        ):
            if nxt is None:
                continue
            cand = _clean_original_title_candidate(nxt.get_text(separator=" ", strip=True))
            if cand:
                return cand
        parent = lab.parent
        if parent:
            for cell in parent.find_all(["dd", "span", "td", "a"], limit=5):
                if cell is lab:
                    continue
                cand = _clean_original_title_candidate(cell.get_text(separator=" ", strip=True))
                if cand:
                    return cand

    for cls_pat in (r"Ere_subTitle", r"subTitle", r"original", r"ori_title"):
        el = soup.find(class_=re.compile(cls_pat, re.I))
        if el:
            cand = _clean_original_title_candidate(el.get_text(separator=" ", strip=True))
            if cand:
                return cand

    for m in re.finditer(
        r"원제\s*</[^>]{1,40}>\s*(?:</[^>]{1,40}>\s*){0,3}<[^>]{1,80}[^>]*>([^<]{2,300})",
        html,
        re.I | re.S,
    ):
        cand = _clean_original_title_candidate(html_stdlib.unescape(m.group(1)))
        if cand:
            return cand

    return None


def enrich_item_original_title_from_web(
    item: dict,
    isbn_fallback: str = "",
    product_html: Optional[str] = None,
) -> Tuple[dict, Optional[str]]:
    """
    subInfo.originalTitle이 비어 있으면 상품 상세 HTML에서 원제를 채운다.
    product_html이 있으면 네트워크 요청 없이 재사용한다.
    """
    sub = item.setdefault("subInfo", {})
    existing = (sub.get("originalTitle") or sub.get("subTitle") or "").strip()
    if existing:
        return item, product_html

    html = _product_page_html_for_item(item, isbn_fallback, product_html)
    if not html:
        return item, product_html

    scraped = scrape_original_title_from_html(html)
    if scraped:
        sub["originalTitle"] = scraped

    return item, html


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
    item_id: str,
    translator_name: str,
    product_html: Optional[str] = None,
) -> Optional[int]:
    html = product_html
    if html is None:
        try:
            html = fetch_product_page_html(item_id)
        except requests.RequestException:
            return None
    return resolve_author_id_from_product_html(html, translator_name)


def enrich_translators_author_id_from_web(
    people: List[dict],
    item: dict,
    isbn_fallback: str = "",
    product_html: Optional[str] = None,
) -> Tuple[List[dict], Optional[str]]:
    """
    authorId가 비어 있는 역자·저자에 대해 도서 상세 페이지 HTML에서 ID를 보완한다.
    product_html이 있으면 fetch 없이 재사용하고, fetch한 HTML을 반환한다.
    """
    needs = [p for p in people if p.get("authorId") is None]
    if not needs:
        return people, product_html

    html = _product_page_html_for_item(item, isbn_fallback, product_html)
    if not html:
        return people, product_html

    for person in needs:
        aid = resolve_author_id_from_product_html(html, person["name"])
        if aid is None:
            continue
        person["authorId"] = aid
        person["authorPageUrl"] = aladin_author_page_url(aid)
        role = (person.get("role") or "").strip()
        if role == "문자열파싱":
            person["role"] = "문자열파싱(웹크롤링ID보완)"
        elif "웹크롤링ID보완" not in role:
            person["role"] = (
                f"{role}(웹크롤링ID보완)" if role else "웹크롤링ID보완"
            )
    return people, html


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
    하이브리드 LLM 원서 언어·국가 판정.
    원제 철자 우선(규칙 F), IP 고유명사(규칙 D), 국가명=주제 방어(규칙 G), 번역가 폴백(규칙 C).
    Few-shot: De Bourgondiërs→네덜란드어, 네덜란드 경제사+영문 역자→영어.
    """
    if not api_key or not api_key.strip():
        return None

    system = (
        "당신은 **한국어로 번역·출간된 외국 도서**의 **원서 언어·원서 국가**만 추론하는 전문가입니다.\n"
        "입력은 알라딘 **번역서** 데이터입니다. 한국어 제목·'국내도서' 분류는 **번역본 유통 정보**일 뿐, "
        "원서가 한국어라는 증거가 **절대 아닙니다**.\n"
        "아래 [최우선 금지·강제 규칙]을 최우선 적용하세요. 예외 없음.\n\n"
        "══════════════════════════════════════════════════════\n"
        "## [최우선] 절대 금지·강제 규칙 (이 섹션을 다른 모든 규칙보다 먼저 적용)\n"
        "══════════════════════════════════════════════════════\n\n"
        "### 규칙 A. '국내도서' ≠ 한국어 원서 (매우 중요, 위반 시 치명적 오판)\n"
        "book.categoryName에 '국내도서', '국내', '한국' 등이 있어도, 그것은 "
        "**한국 출판사가 한국어로 번역·출간한 책**이라는 알라딘 **유통 분류**일 뿐입니다.\n"
        "**절대 금지:**\n"
        "  · '국내도서'만 보고 inferred_language='한국어' 판정\n"
        "  · '국내도서'만 보고 inferred_country='한국'을 **원서 국가**로 판정\n"
        "  · categoryName을 근거로 '한국인 저자의 한국어 원서'라고 결론\n"
        "국내도서는 원서 언어·국가 추론의 **근거로 사용하지 마세요**. "
        "reasoning_process에서도 '국내도서이므로 한국어 원서'라는 논리는 **쓰지 마세요**.\n\n"
        "### 규칙 B. 외국인 이름 음차 — bio가 비어도 한국어 원서로 보지 말 것\n"
        "authors[].bio_excerpt가 null, 공백, '대학교재/전문서적' 등 **무의미한 짧은 문구**만 있어도, "
        "authors[].name이 **외국 인명의 한글 음차**이면 한국인·한국어 원서 판정 **절대 금지**:\n"
        "  · 예: 아나스타샤 메이블, 톰 스미스, 레오 톨스토이, 조지 오웰, 스티븐 킹, "
        "마르크 트웨인, 어니스트 헤밍웨이, 파울 코엘료, 찰스 디킨스, 제인 오스틴 등\n"
        "  · 한글 표기라도 전형적 한국 성씨(김·이·박·최·정·강·조·윤·장·임)만 있는 이름이 **아니면** "
        "외국인 저자로 간주\n"
        "  · author_signal_confidence=low 가능 — 단, **규칙 D(제목 고유명사)를 먼저 검사**한 뒤 "
        "규칙 D로 결론이 안 나면 규칙 C(번역가 폴백)로 넘어가세요\n"
        "  · bio 부재를 이유로 inferred_language='한국어' 기본값 **금지**\n\n"
        "### 규칙 D. 도서 제목(title)의 결정적 고유명사 최우선 적용 (규칙 C보다 먼저)\n"
        "저자 정보가 비어있거나 author_signal_confidence=low여도, book.title·book.description에 "
        "특정 국가·문화권을 **명확히 지시하는 글로벌 고유명사·문화 키워드**가 있으면 "
        "**번역가 폴백(규칙 C)으로 넘어가기 전에** 해당 본고장을 원서 국가·언어로 **즉시** 판정하세요.\n"
        "  · 일본: 지브리, Ghibli, 라퓨타, Laputa, 토토로, 모노노케, 미야자키, 애니메이션 원작 일본 IP 등 "
        "→ inferred_language=일본어, inferred_country=일본\n"
        "  · 미국: 마블, Marvel, 디즈니, Disney, 픽사, Pixar, 스타워즈, Star Wars, 해리포터(영미판 맥락) 등 "
        "→ inferred_language=영어, inferred_country=미국(또는 해당 IP 본고장)\n"
        "  · 영국: 셜록, Sherlock, 007, 롤링 등 영국 IP 맥락 → 영어·영국\n"
        "판정 예: title='지브리의 식탁 : 천공의 성 라퓨타' → **일본** (역자가 영문과여도 미국 판정 금지).\n"
        "**규칙 A와의 관계:** 규칙 A는 '국내도서·한글 제목만으로 한국어 원서'를 금지하는 것이지, "
        "지브리·라퓨타 같은 **결정적 고유명사**까지 무시하라는 뜻이 **아닙니다**. "
        "한글 번역 제목 안의 고유명사도 반드시 분석하세요.\n"
        "reasoning_process에 고유명사 매칭과 본고장 판정을 **명시**하세요.\n"
        "**규칙 D에 해당하지 않음:** 제목·설명에 등장하는 **일반 국가명·지역명**(예: 네덜란드 경제사, "
        "프랑스 혁명사)은 책의 **주제**일 뿐, 원서가 그 국가 언어로 쓰였다는 증거가 **아님**(규칙 F 참고).\n\n"
        "### 규칙 F. 원제(original_title) 철자·관사·어문법 분석 (번역가 전공·주제보다 우선)\n"
        "book.original_title(또는 라틴/네덜란드어/독일어 등 비한글 원제)이 있으면 **반드시** "
        "철자·관사·어미를 분석해 집필 언어를 판정하세요. 다음은 번역가 전공·한글 제목 주제보다 "
        "**우선**합니다.\n"
        "  · 벨기에·스위스·캐나다 등 **다언어 국가**: 저자 출신·역자 프랑스어 전공·주제(부르고뉴 등)만으로 "
        "프랑스어 원서로 단정 **금지**. 원제 철자가 결정적이면 그 언어를 채택.\n"
        "  · 예: 'De Bourgondiërs' → ë, 관사 De, -iërs 어미 → **네덜란드어** (프랑스어 De Bourguignons "
        "와 다름). inferred_country=벨기에(저자 출신), inferred_language=**네덜란드어**.\n"
        "  · 영어/프랑스어/독일어 원제도 동일: 철자·관용 표현으로 원어를 먼저 확정한 뒤 국가를 매핑.\n"
        "reasoning_process에 '원제 철자·관사 분석 → 언어 확정' 단계를 **명시**하세요.\n\n"
        "### 규칙 G. 제목·설명의 국가명 = 주제일 뿐 (국가명 낚시 방어)\n"
        "한글 title·description에 '네덜란드', '프랑스', '독일' 등 **일반 국가·지역명**만 있고 "
        "규칙 D의 결정적 IP/고유명사(지브리·마블 등)가 없으면, 그 국가를 inferred_country로 "
        "**즉시 단정하지 마세요**. 이는 **그 나라에 관한 책**이라는 주제 신호일 뿐입니다.\n"
        "  · 저자 단서가 없고(author_signal_confidence=low) 역자 career_hint_counts가 "
        "메타_영어권·원제_라틴 등 **특정 권역에 압도적**이면 → 그 권역 언어의 원서로 판정 "
        "(예: 네덜란드 경제사 + 영문학 역자 + 영미 커리어 → **영어** 원서, 미국 또는 영국).\n"
        "  · 규칙 F의 비한글 original_title이 있으면 규칙 G보다 **규칙 F 우선**.\n\n"
        "### 규칙 C. 저자 단서 부실 시 번역가 폴백 **즉시·적극** 가동 (규칙 D·F·G 적용 후)\n"
        "**규칙 D로 결론이 나지 않았을 때만** 다음에 해당하면 translators[]로 넘어가세요:\n"
        "  ① author_signal_confidence=low (bio 부실·무의미·외국인 음차 이름만 있음 등)\n"
        "  ② 저자 이름이 외국인 음차이거나 bio로 원서 국가를 특정 불가\n"
        "  ③ 국내도서·한글 original_title만으로 한국어 원서처럼 보이나 **고유명사 단서 없음**\n"
        "**3순위에서 적극 수용:**\n"
        "  · translators[].univ_major_regex.inferred_language (예: 영문과 → 영어)\n"
        "  · translators[].career_hint_counts (예: 메타_영어권, 원제_라틴 등 누적이 큰 축)\n"
        "  · 신호가 뚜렷하면 이를 inferred_language·inferred_country의 **주 결론**으로 채택\n"
        "  · **단, 규칙 D의 지브리·라퓨타 등 일본 IP가 title에 있으면 영문과 역자라도 미국 판정 금지**\n"
        "reasoning_process에 '규칙 D 미해당 → 저자 단서 부족 → 번역가 폴백' 순서를 기술하세요.\n"
        "예외: bio에 해외 대학·활동이 **명확**하면(규칙 E) 번역가 전공보다 저자 bio 우선 "
        "(영문과 역자+덴마크 원서 중역 등 → is_indirect_translation=true).\n\n"
        "══════════════════════════════════════════════════════\n"
        "## 추론 우선순위 (규칙 A~D 적용 후)\n"
        "══════════════════════════════════════════════════════\n"
        "1순위 — 저자(name, bio_excerpt, script_weights, univ_major_regex):\n"
        "  · bio가 풍부·해외 활동 명확 → 여기서 결론(규칙 E).\n"
        "  · bio 부실 + 외국인 음차 → 규칙 D 검사 후 미결 시 규칙 C.\n"
        "2순위 — 도서 메타(title, description, original_title):\n"
        "  · **규칙 F: original_title 철자·관사 → 원서 언어**(번역가 전공보다 우선).\n"
        "  · **규칙 D: 결정적 IP·고유명사**(지브리·마블 등) → 본고장 확정.\n"
        "  · **규칙 G: 일반 국가명은 주제** — 단독으로 원서 국가 단정 금지.\n"
        "  · **국내도서·한글 original_title만**으로 한국어 원서 판정 금지(규칙 A).\n"
        "  · author_signal_confidence=low, D·F 미해당 → 규칙 G 검토 후 규칙 C.\n"
        "3순위 — 번역가(univ_major_regex, career_hint_counts):\n"
        "  · 규칙 D 미해당 + 규칙 C 조건에서 **필수·적극** 사용.\n\n"
        "## [필수] 규칙 E. 한국계·해외파 저자 (bio가 있을 때)\n"
        "저자 이름이 한글·한국식(예: 송, 김, 박 성씨, 한국계 미국인 이름)이어도, "
        "bio_excerpt에서 아래가 주축이면 집필 언어·원서 국가를 한국이 아닌 해당 해외로 판정하세요:\n"
        "  · 영미권 대학·기관: Stanford, Harvard, MIT, Yale, Princeton, Columbia, NYU, "
        "Berkeley, UCLA, Oxford, Cambridge, LSE 등 (한국어 표기: 스탠퍼드, 뉴욕대, 예일, MIT 등 포함)\n"
        "  · 영미권 언론·매체: Forbes, New York Times, Wall Street Journal, BBC, NPR, "
        "포브스, 뉴욕타임스 등\n"
        "  · 해외 활동 맥락: 영문 프로그램명·직함(Professor at …, PhD from …), "
        "미국·영국·캐나다·호주 거주·근무, Silicon Valley, Wall Street 등\n"
        "판정 예: 이름 '엘리사 송' + 스탠퍼드·뉴욕대·포브스 → inferred_language=영어, "
        "inferred_country=미국 (한국어 원서로 판정 금지).\n"
        "이름이 한국식이라는 이유만으로 author_signal_confidence를 낮추거나 "
        "한국어·한국을 기본값으로 쓰지 마세요.\n\n"
        "## [필수] 가짜 original_title 무시\n"
        "original_title에 한국어 부제만 있어도 원서가 한국어라는 뜻 **아님**. "
        "저자 bio 해외이면 original_title 무시. "
        "저자 bio 부실 + 외국인 이름이면 original_title·국내도서만 무시 — "
        "title의 고유명사(규칙 D)는 **무시하지 말 것**.\n\n"
        "## author_signal_confidence\n"
        "- high: bio에 해외 대학·활동·언론 등 결정적 맥락, 또는 규칙 D 고유명사로 원서 권역 확정\n"
        "- medium: bio 일부 단서, bio vs 메타 상충 시 bio 우선(국내도서는 근거로 쓰지 않음)\n"
        "- low: bio 없음/무의미 + 외국인 음차 등 → **규칙 D 먼저**, 미해당 시 규칙 C. "
        "국내도서·한글 제목만으로 한국어 원서 판정 **금지**\n\n"
        "## reasoning_process (한국어, 순서 고정)\n"
        "① 분석 맥락(번역서·국내도서≠원서) → ② 저자(name·bio·출신) → ③ **규칙 F: original_title "
        "철자·관사** → ④ **규칙 D: IP·고유명사** / **규칙 G: 국가명=주제 여부** → "
        "⑤ 국내도서·가짜 한글 원제 배제 → ⑥ 규칙 C 번역가 폴백 → ⑦ 최종 결론\n\n"
        "══════════════════════════════════════════════════════\n"
        "## Few-shot: reasoning_process 작성 형식 (동일 논리 구조로 모방)\n"
        "══════════════════════════════════════════════════════\n\n"
        "[예시 1: 다언어 국가와 원제의 철자 분석]\n"
        "입력: 저자=바르트 팬 로(벨기에 출신), 제목=부르고뉴, 역자=프랑스어 전공, "
        "원제=De Bourgondiërs\n"
        "추론 과정: 벨기에는 다언어 국가(프랑스어/네덜란드어 등)이므로 번역가의 전공(프랑스어)이나 "
        "책 주제(부르고뉴)만으로 단정 지어선 안 된다. 원제 'De Bourgondiërs'의 철자법과 관사(De)를 "
        "분석보면 네덜란드어임이 명백하다. 따라서 번역가 커리어보다 원제 철자를 우선시한다.\n"
        "출력: inferred_country=벨기에, inferred_language=네덜란드어\n\n"
        "[예시 2: 제목 고유명사·국가명 낚시 방어]\n"
        "입력: 저자=미상, 제목=네덜란드 경제사, 역자=영문학 전공(과거 영미권 도서 50권 번역)\n"
        "추론 과정: 제목이나 책설명란에 '네덜란드'라는 국가명이 있지만, 이는 책의 '주제'일 뿐 "
        "저자의 출신이나 원서 국가를 보장하지 않는다(규칙 G). 저자 정보가 없는 상태에서 역자의 "
        "커리어가 영미권(영어)에 압도적으로 집중되어 있으므로, 이 책은 영미권 저자가 쓴 "
        "'네덜란드에 관한 영어 원서'로 판정하는 것이 타당하다.\n"
        "출력: inferred_country=미국(또는 영국), inferred_language=영어\n\n"
        "실제 입력에 대해서도 위와 같이 **추론 과정:** 문장으로 단계를 밟고, "
        "규칙 F→D→G→C 순서를 명시한 뒤 JSON을 반환하세요.\n\n"
        "반드시 JSON 객체 하나만 반환하세요. 키:\n"
        '- reasoning_process (string, 한국어, 단계별 추론)\n'
        '- author_signal_confidence ("high"|"medium"|"low")\n'
        '- inferred_language (string, 한국어 표기 예: 영어, 덴마크어, 일본어)\n'
        '- inferred_country (string, 한국어 표기 예: 미국, 덴마크, 일본)\n'
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
                    product_html: Optional[str] = None

                    translators = extract_translators_from_item(item)
                    if any(tr.get("authorId") is None for tr in translators):
                        with st.spinner(
                            "API에 AuthorId 없음 → 도서 상세 페이지 1회 로드·ID 보완…"
                        ):
                            translators, product_html = enrich_translators_author_id_from_web(
                                translators, item, isbn_clean, product_html
                            )
                        found = sum(1 for tr in translators if tr.get("authorId"))
                        st.caption(
                            f"웹 페이지 AuthorId 보완: **{found}**/{len(translators)}명 "
                            f"(상품 ItemId=`{_product_page_item_id(item, isbn_clean)}`)"
                        )
                    writers = extract_writers_from_item(item)
                    if any(wr.get("authorId") is None for wr in writers):
                        with st.spinner(
                            "API에 AuthorId 없음 → 도서 상세 페이지(재사용) 저자 ID 보완…"
                        ):
                            writers, product_html = enrich_translators_author_id_from_web(
                                writers, item, isbn_clean, product_html
                            )

                    sub_info = item.setdefault("subInfo", {})
                    if not (sub_info.get("originalTitle") or "").strip():
                        with st.spinner(
                            "API 원제 없음 → 도서 상세 페이지(재사용)에서 원제 추출…"
                        ):
                            item, product_html = enrich_item_original_title_from_web(
                                item, isbn_clean, product_html
                            )
                        if (sub_info.get("originalTitle") or "").strip():
                            st.caption(
                                f"웹 페이지 원제 보완: **{sub_info['originalTitle']}**"
                            )

                    st.subheader("현재 도서")
                    st.write(
                        {
                            "title": item.get("title"),
                            "originalTitle": (item.get("subInfo") or {}).get(
                                "originalTitle"
                            ),
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

                            with st.spinner(
                                f"역자명으로 도서 50권 일괄 검색 중… "
                                f"(Query=`{tr['name']}`)"
                            ):
                                catalog_json = item_search_translator_catalog(
                                    tr["name"], ttb_key, 50
                                )
                            raw_list: List[dict] = catalog_json.get("item") or []
                            st.markdown(
                                f"**역자 검색 원본**: {len(raw_list)}권 "
                                f"(ItemSearch Query=`{tr['name']}`, OptResult=authors)"
                            )
                            if tr.get("authorId") is not None:
                                st.caption(
                                    f"AuthorId `{tr['authorId']}`는 프로필·소개글용이며, "
                                    "과거 번역 이력은 역자명 ItemSearch 1회로 수집합니다 "
                                    "(동명이인 혼입 가능)."
                                )
                            else:
                                st.caption(
                                    "AuthorId 없음 — 역자명 ItemSearch로 커리어 수집 "
                                    "(동명이인 혼입 가능)."
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
