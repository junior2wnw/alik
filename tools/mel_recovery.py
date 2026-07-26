#!/usr/bin/env python3
from __future__ import annotations

import csv
import gzip
import hashlib
import html as htmlmod
import io
import json
import os
import re
import shutil
import sys
import time
import traceback
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Iterable
from urllib.parse import parse_qsl, urlencode, urljoin, urlsplit, urlunsplit

import requests
from bs4 import BeautifulSoup
from PIL import Image, ImageStat
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from warcio.archiveiterator import ArchiveIterator

OUT = Path(os.environ.get("MEL_OUT", "mel-recovery-output"))
IMG_DIR = OUT / "images"
RAW_DIR = OUT / "raw"
OUT.mkdir(parents=True, exist_ok=True)
IMG_DIR.mkdir(parents=True, exist_ok=True)
RAW_DIR.mkdir(parents=True, exist_ok=True)

UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/150 Safari/537.36 MelbordaHistoryRecovery/1.0"
TIMEOUT = 35
MAX_LIVE_PAGES = int(os.environ.get("MAX_LIVE_PAGES", "1400"))
MAX_ARCHIVE_PAGES = int(os.environ.get("MAX_ARCHIVE_PAGES", "1000"))
MAX_CC_PAGES = int(os.environ.get("MAX_CC_PAGES", "500"))
MAX_CANDIDATES = int(os.environ.get("MAX_CANDIDATES", "1800"))
MAX_RECOVERED_BYTES = int(os.environ.get("MAX_RECOVERED_BYTES", str(350 * 1024 * 1024)))

KNOWN_IMAGE_HOSTS = (
    "radikal.ru", "radikal.cc", "photofile.ru", "foto.mail.ru", "foto.my.mail.ru",
    "content.foto.mail.ru", "keep4u.ru", "imageshack.us", "fastpic.ru", "savepic.ru",
    "saveimg.ru", "ipicture.ru", "piccy.info", "imgsrc.ru", "fotki.yandex.ru", "yandex.ru",
    "narod.ru", "liveinternet.ru", "photobucket.com", "flickr.com", "googleusercontent.com",
    "vk.com", "vkuserphoto.ru", "userapi.com", "mycdn.me", "odnoklassniki.ru", "rambler.ru",
)
IMG_EXT = re.compile(r"\.(?:jpe?g|png|gif|webp|bmp|tiff?|avif)(?:$|[?#])", re.I)
ABS_URL = re.compile(r"https?://[^\s\"'<>\]\[()]+", re.I)
BBCODE_IMG = re.compile(r"\[img(?:=[^\]]+)?\]\s*(https?://[^\s\[]+)\s*\[/img\]", re.I)
REL_TOPIC = re.compile(r"(?:href|location(?:\.href)?)\s*=\s*[\"'](\?[^\"']+)[\"']", re.I)


def log(msg: str) -> None:
    print(time.strftime("%H:%M:%S"), msg, flush=True)


def session() -> requests.Session:
    s = requests.Session()
    retry = Retry(total=4, connect=4, read=4, backoff_factor=1.0,
                  status_forcelist=(429, 500, 502, 503, 504),
                  allowed_methods=frozenset(["GET", "HEAD"]))
    s.mount("http://", HTTPAdapter(max_retries=retry, pool_connections=40, pool_maxsize=40))
    s.mount("https://", HTTPAdapter(max_retries=retry, pool_connections=40, pool_maxsize=40))
    s.headers.update({"User-Agent": UA, "Accept": "*/*"})
    return s

S = session()
ERRORS: list[dict[str, str]] = []


def err(stage: str, url: str, exc: Any) -> None:
    ERRORS.append({"stage": stage, "url": url, "error": str(exc)[:1000]})


def get(url: str, *, timeout: int = TIMEOUT, headers: dict[str, str] | None = None,
        stream: bool = False, allow_redirects: bool = True) -> requests.Response | None:
    try:
        r = S.get(url, timeout=timeout, headers=headers, stream=stream, allow_redirects=allow_redirects)
        return r
    except Exception as e:
        err("get", url, e)
        return None


def decode_body(data: bytes, content_type: str = "") -> str:
    charsets = []
    m = re.search(r"charset=([\w-]+)", content_type, re.I)
    if m:
        charsets.append(m.group(1))
    charsets += ["utf-8", "cp1251", "windows-1251", "koi8-r", "latin1"]
    for enc in charsets:
        try:
            return data.decode(enc)
        except Exception:
            pass
    return data.decode("utf-8", "replace")


def normalize_url(u: str, base: str | None = None) -> str | None:
    if not u:
        return None
    u = htmlmod.unescape(u.strip().strip("'\"<>[]()"))
    u = u.replace("\\/", "/")
    if u.startswith("//"):
        u = "http:" + u
    if base:
        u = urljoin(base, u)
    if not u.lower().startswith(("http://", "https://")):
        return None
    try:
        p = urlsplit(u)
        if not p.hostname:
            return None
        host = p.hostname.lower().rstrip(".")
        port = p.port
        netloc = host if not port or (p.scheme == "http" and port == 80) or (p.scheme == "https" and port == 443) else f"{host}:{port}"
        path = re.sub(r"/{2,}", "/", p.path or "/")
        query = urlencode(sorted(parse_qsl(p.query, keep_blank_values=True)), doseq=True)
        return urlunsplit((p.scheme.lower(), netloc, path, query, ""))
    except Exception:
        return None


def probable_image(u: str, forced: bool = False) -> bool:
    try:
        host = (urlsplit(u).hostname or "").lower()
        path = urlsplit(u).path.lower()
    except Exception:
        return False
    if forced or IMG_EXT.search(u):
        return True
    return any(host == h or host.endswith("." + h) for h in KNOWN_IMAGE_HOSTS) and not path.endswith((".html", ".htm", ".php"))


def page_context(node: Any, limit: int = 500) -> str:
    try:
        parent = node.parent
        for _ in range(4):
            if parent is None:
                break
            text = " ".join(parent.get_text(" ", strip=True).split())
            if len(text) >= 25:
                return text[:limit]
            parent = parent.parent
    except Exception:
        pass
    return ""


def extract_image_refs(text: str, page_url: str, source: str, capture_time: str = "") -> list[dict[str, str]]:
    refs: list[dict[str, str]] = []
    try:
        soup = BeautifulSoup(text, "html.parser")
        for tag in soup.find_all(["img", "a", "source", "input"]):
            for attr in ("src", "href", "data-src", "data-original", "data-lazy-src"):
                val = tag.get(attr)
                if not val:
                    continue
                u = normalize_url(str(val), page_url)
                if u and probable_image(u, forced=(tag.name == "img" or attr in ("src", "data-src", "data-original", "data-lazy-src"))):
                    refs.append({"url": u, "page_url": page_url, "source": source,
                                 "capture_time": capture_time, "context": page_context(tag)})
    except Exception as e:
        err("parse_html", page_url, e)

    for m in BBCODE_IMG.finditer(text):
        u = normalize_url(m.group(1), page_url)
        if u:
            refs.append({"url": u, "page_url": page_url, "source": source,
                         "capture_time": capture_time, "context": text[max(0, m.start()-250):m.end()+250].replace("\n", " ")[:500]})
    for m in ABS_URL.finditer(text):
        u = normalize_url(m.group(0), page_url)
        if u and probable_image(u):
            refs.append({"url": u, "page_url": page_url, "source": source,
                         "capture_time": capture_time, "context": text[max(0, m.start()-200):m.end()+200].replace("\n", " ")[:500]})
    # stable dedupe within page
    seen = set()
    out = []
    for x in refs:
        k = (x["url"], x["page_url"], x["source"])
        if k not in seen:
            seen.add(k)
            out.append(x)
    return out


def extract_page_links(text: str, page_url: str) -> list[str]:
    links = []
    try:
        soup = BeautifulSoup(text, "html.parser")
        for a in soup.find_all("a", href=True):
            u = normalize_url(a.get("href"), page_url)
            if u:
                links.append(u)
    except Exception:
        pass
    for m in REL_TOPIC.finditer(text):
        u = normalize_url(m.group(1), page_url)
        if u:
            links.append(u)
    return list(dict.fromkeys(links))


def is_forum_page(u: str) -> bool:
    try:
        p = urlsplit(u)
        host = (p.hostname or "").lower()
        if host not in ("mel.borda.ru", "wap.mel.borda.ru"):
            return False
        low = u.lower()
        if any(x in low for x in ("login", "register", "profile", "help", "search", "admin", "javascript:")):
            return False
        return True
    except Exception:
        return False


def crawl_live() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    seeds = ["http://mel.borda.ru/", "https://mel.borda.ru/", "http://wap.mel.borda.ru/", "https://wap.mel.borda.ru/"]
    q = deque(seeds)
    seen: set[str] = set()
    pages: list[dict[str, str]] = []
    refs: list[dict[str, str]] = []
    while q and len(seen) < MAX_LIVE_PAGES:
        u = q.popleft()
        u = normalize_url(u)
        if not u or u in seen:
            continue
        seen.add(u)
        r = get(u)
        if not r:
            continue
        ctype = r.headers.get("content-type", "")
        pages.append({"url": u, "final_url": r.url, "status": str(r.status_code), "source": "live", "bytes": str(len(r.content)), "content_type": ctype})
        if r.status_code != 200 or ("html" not in ctype.lower() and b"<html" not in r.content[:2000].lower()):
            continue
        text = decode_body(r.content, ctype)
        refs.extend(extract_image_refs(text, r.url, "live"))
        for v in extract_page_links(text, r.url):
            if is_forum_page(v) and v not in seen:
                q.append(v)
        if len(seen) % 100 == 0:
            log(f"live pages={len(seen)} refs={len(refs)} queue={len(q)}")
        time.sleep(0.03)
    return pages, refs


def parse_cdx_json(r: requests.Response) -> list[dict[str, str]]:
    try:
        data = r.json()
        if isinstance(data, list) and data and isinstance(data[0], list):
            hdr = data[0]
            return [dict(zip(hdr, row)) for row in data[1:]]
    except Exception:
        pass
    rows = []
    text = r.text
    for line in text.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
            if isinstance(obj, dict):
                rows.append({str(k): str(v) for k, v in obj.items()})
        except Exception:
            parts = line.split()
            if len(parts) >= 7:
                rows.append(dict(zip(["urlkey", "timestamp", "original", "mimetype", "statuscode", "digest", "length"], parts[:7])))
    return rows


def wayback_domain() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    all_rows: list[dict[str, str]] = []
    for pattern in ("mel.borda.ru/*", "wap.mel.borda.ru/*"):
        url = "https://web.archive.org/cdx/search/cdx"
        try:
            r = S.get(url, params={"url": pattern, "output": "json", "fl": "timestamp,original,mimetype,statuscode,digest,length",
                                   "filter": "statuscode:200", "collapse": "urlkey", "limit": "50000"}, timeout=90)
            if r.status_code == 200:
                all_rows.extend(parse_cdx_json(r))
            else:
                err("wayback_cdx", r.url, f"HTTP {r.status_code}: {r.text[:300]}")
        except Exception as e:
            err("wayback_cdx", pattern, e)
    # one capture per original URL, HTML-like only
    chosen: dict[str, dict[str, str]] = {}
    for row in all_rows:
        orig = row.get("original", "")
        mime = row.get("mimetype", "")
        if not orig:
            continue
        if "html" not in mime and not ("?" in orig or orig.rstrip("/").endswith("borda.ru")):
            continue
        old = chosen.get(orig)
        if old is None or row.get("timestamp", "") > old.get("timestamp", ""):
            chosen[orig] = row
    rows = list(chosen.values())[:MAX_ARCHIVE_PAGES]
    refs: list[dict[str, str]] = []
    pages: list[dict[str, str]] = []
    for i, row in enumerate(rows, 1):
        ts, orig = row.get("timestamp", ""), row.get("original", "")
        replay = f"https://web.archive.org/web/{ts}id_/{orig}"
        r = get(replay, timeout=50)
        if not r:
            continue
        pages.append({"url": orig, "final_url": r.url, "status": str(r.status_code), "source": "wayback", "bytes": str(len(r.content)), "content_type": r.headers.get("content-type", ""), "capture_time": ts})
        if r.status_code == 200:
            text = decode_body(r.content, r.headers.get("content-type", ""))
            refs.extend(extract_image_refs(text, orig, "wayback", ts))
        if i % 100 == 0:
            log(f"wayback pages={i}/{len(rows)} refs={len(refs)}")
        time.sleep(0.08)
    (RAW_DIR / "wayback_cdx.json").write_text(json.dumps(all_rows, ensure_ascii=False, indent=2), encoding="utf-8")
    return pages, refs


def arquivo_domain() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    items: list[dict[str, Any]] = []
    endpoints = [
        ("https://arquivo.pt/textsearch", {"versionHistory": "http://mel.borda.ru/", "maxItems": 500}),
        ("https://arquivo.pt/textsearch", {"versionHistory": "https://mel.borda.ru/", "maxItems": 500}),
        ("https://arquivo.pt/textsearch", {"q": '"mel.borda.ru"', "maxItems": 500}),
    ]
    for endpoint, params in endpoints:
        try:
            r = S.get(endpoint, params=params, timeout=90)
            if r.status_code == 200:
                obj = r.json()
                items.extend(obj.get("response_items", []) if isinstance(obj, dict) else [])
            else:
                err("arquivo_search", r.url, f"HTTP {r.status_code}")
        except Exception as e:
            err("arquivo_search", endpoint, e)
    # Also try CDX endpoint variants
    for endpoint in ("https://arquivo.pt/wayback/cdx", "https://arquivo.pt/textsearch/cdx"):
        try:
            r = S.get(endpoint, params={"url": "mel.borda.ru/*", "output": "json", "filter": "statuscode:200", "collapse": "urlkey"}, timeout=90)
            if r.status_code == 200:
                for row in parse_cdx_json(r):
                    items.append({"originalURL": row.get("original", ""), "tstamp": row.get("timestamp", ""),
                                  "linkToArchive": f"https://arquivo.pt/wayback/{row.get('timestamp','')}/{row.get('original','')}"})
        except Exception as e:
            err("arquivo_cdx", endpoint, e)
    uniq: dict[tuple[str, str], dict[str, Any]] = {}
    for x in items:
        orig = str(x.get("originalURL") or x.get("originalUrl") or x.get("url") or "")
        link = str(x.get("linkToArchive") or x.get("link") or "")
        ts = str(x.get("tstamp") or x.get("timestamp") or "")
        if orig and link:
            uniq[(orig, ts)] = {"original": orig, "link": link, "timestamp": ts}
    refs: list[dict[str, str]] = []
    pages: list[dict[str, str]] = []
    for i, x in enumerate(list(uniq.values())[:MAX_ARCHIVE_PAGES], 1):
        r = get(x["link"], timeout=50)
        if not r:
            continue
        pages.append({"url": x["original"], "final_url": r.url, "status": str(r.status_code), "source": "arquivo", "bytes": str(len(r.content)), "content_type": r.headers.get("content-type", ""), "capture_time": x["timestamp"]})
        if r.status_code == 200:
            text = decode_body(r.content, r.headers.get("content-type", ""))
            refs.extend(extract_image_refs(text, x["original"], "arquivo", x["timestamp"]))
        if i % 100 == 0:
            log(f"arquivo pages={i}/{len(uniq)} refs={len(refs)}")
    (RAW_DIR / "arquivo_items.json").write_text(json.dumps(items, ensure_ascii=False, indent=2), encoding="utf-8")
    return pages, refs


def cc_indexes() -> list[dict[str, Any]]:
    r = get("https://index.commoncrawl.org/collinfo.json", timeout=90)
    if not r or r.status_code != 200:
        return []
    try:
        return r.json()
    except Exception as e:
        err("cc_collinfo", r.url, e)
        return []


def cc_domain() -> tuple[list[dict[str, str]], list[dict[str, str]], list[dict[str, Any]]]:
    indexes = cc_indexes()
    records: list[dict[str, Any]] = []
    # prioritize 2008-2018, then newer captures
    def rank(x: dict[str, Any]) -> tuple[int, str]:
        m = re.search(r"CC-MAIN-(\d{4})", str(x.get("id", "")))
        year = int(m.group(1)) if m else 9999
        preferred = 0 if 2008 <= year <= 2018 else 1
        return (preferred, str(x.get("id", "")))
    for idx in sorted(indexes, key=rank):
        api = idx.get("cdx-api")
        if not api:
            continue
        for pattern in ("mel.borda.ru/*", "wap.mel.borda.ru/*"):
            try:
                r = S.get(api, params={"url": pattern, "output": "json", "filter": "status:200"}, timeout=90)
                if r.status_code == 200:
                    for line in r.text.splitlines():
                        try:
                            obj = json.loads(line)
                            obj["crawl"] = idx.get("id", "")
                            records.append(obj)
                        except Exception:
                            pass
                elif r.status_code not in (404, 400):
                    err("cc_index", r.url, f"HTTP {r.status_code}")
            except Exception as e:
                err("cc_index", str(api), e)
        if len({x.get("url") for x in records}) >= MAX_CC_PAGES * 2:
            break
    # choose one HTML response per URL
    chosen: dict[str, dict[str, Any]] = {}
    for x in records:
        u = str(x.get("url", ""))
        mime = str(x.get("mime", x.get("mime-detected", ""))).lower()
        if not u or ("html" not in mime and "?" not in u):
            continue
        chosen.setdefault(u, x)
    refs: list[dict[str, str]] = []
    pages: list[dict[str, str]] = []
    for i, x in enumerate(list(chosen.values())[:MAX_CC_PAGES], 1):
        try:
            filename = x["filename"]
            offset = int(x["offset"])
            length = int(x["length"])
            data_url = "https://data.commoncrawl.org/" + filename
            r = S.get(data_url, headers={"Range": f"bytes={offset}-{offset + length - 1}"}, timeout=90)
            if r.status_code not in (200, 206):
                continue
            payload = b""
            for record in ArchiveIterator(io.BytesIO(r.content)):
                if record.rec_type == "response":
                    payload = record.content_stream().read()
                    break
            if not payload:
                continue
            u = str(x.get("url", ""))
            ts = str(x.get("timestamp", ""))
            pages.append({"url": u, "final_url": u, "status": str(x.get("status", "200")), "source": "commoncrawl", "bytes": str(len(payload)), "content_type": str(x.get("mime", "")), "capture_time": ts, "crawl": str(x.get("crawl", ""))})
            text = decode_body(payload, str(x.get("mime", "")))
            refs.extend(extract_image_refs(text, u, "commoncrawl", ts))
        except Exception as e:
            err("cc_warc", str(x.get("url", "")), e)
        if i % 50 == 0:
            log(f"commoncrawl pages={i}/{min(len(chosen), MAX_CC_PAGES)} refs={len(refs)}")
    (RAW_DIR / "commoncrawl_records.json").write_text(json.dumps(records, ensure_ascii=False, indent=2), encoding="utf-8")
    return pages, refs, indexes


def url_variants(u: str) -> list[str]:
    out = [u]
    try:
        p = urlsplit(u)
        alt_scheme = "https" if p.scheme == "http" else "http"
        out.append(urlunsplit((alt_scheme, p.netloc, p.path, p.query, "")))
        path = p.path
        replacements = [
            ("/small/", "/original/"), ("/middle/", "/original/"), ("/preview/", "/"),
            ("/thumb/", "/"), ("/thumbs/", "/"), ("_thumb.", "."), ("-thumb.", "."),
            ("_small.", "."), ("-small.", "."), ("_s.", "."), ("_m.", "."),
        ]
        for a, b in replacements:
            if a in path.lower():
                idx = path.lower().find(a)
                np = path[:idx] + b + path[idx + len(a):]
                out.append(urlunsplit((p.scheme, p.netloc, np, p.query, "")))
        host = (p.hostname or "").lower()
        if host.startswith("www."):
            out.append(urlunsplit((p.scheme, p.netloc[4:], p.path, p.query, "")))
        else:
            out.append(urlunsplit((p.scheme, "www." + p.netloc, p.path, p.query, "")))
    except Exception:
        pass
    return list(dict.fromkeys(v for v in (normalize_url(x) for x in out) if v))


def image_info(data: bytes) -> dict[str, Any] | None:
    if len(data) < 1200:
        return None
    try:
        with Image.open(io.BytesIO(data)) as im:
            im.load()
            w, h = im.size
            fmt = (im.format or "").upper()
            if w < 80 or h < 80:
                return None
            gray = im.convert("L").resize((64, 64))
            stat = ImageStat.Stat(gray)
            variance = float(stat.var[0])
            return {"width": w, "height": h, "format": fmt, "variance": round(variance, 3)}
    except Exception:
        return None


def ext_for(fmt: str) -> str:
    return {"JPEG": ".jpg", "PNG": ".png", "GIF": ".gif", "WEBP": ".webp", "BMP": ".bmp", "TIFF": ".tif"}.get(fmt.upper(), ".img")


def fetch_direct(u: str, referer: str = "") -> tuple[bytes, str] | None:
    headers = {"Referer": referer} if referer else None
    r = get(u, timeout=40, headers=headers)
    if not r or r.status_code != 200:
        return None
    if "text/html" in r.headers.get("content-type", "").lower() and r.content[:200].lstrip().lower().startswith((b"<html", b"<!doctype")):
        return None
    return r.content, r.url


def wayback_captures(u: str) -> list[dict[str, str]]:
    try:
        r = S.get("https://web.archive.org/cdx/search/cdx", params={"url": u, "output": "json",
                    "fl": "timestamp,original,mimetype,statuscode,digest,length", "filter": "statuscode:200",
                    "collapse": "digest", "limit": 30}, timeout=60)
        if r.status_code == 200:
            rows = parse_cdx_json(r)
            rows.sort(key=lambda x: int(x.get("length") or 0), reverse=True)
            return rows
    except Exception as e:
        err("wayback_image_cdx", u, e)
    return []


def fetch_wayback(u: str) -> tuple[bytes, str, str] | None:
    for row in wayback_captures(u):
        ts = row.get("timestamp", "")
        orig = row.get("original", u)
        replay = f"https://web.archive.org/web/{ts}id_/{orig}"
        r = get(replay, timeout=50)
        if r and r.status_code == 200 and image_info(r.content):
            return r.content, replay, ts
    return None


def fetch_arquivo(u: str) -> tuple[bytes, str, str] | None:
    try:
        r = S.get("https://arquivo.pt/textsearch", params={"versionHistory": u, "maxItems": 50}, timeout=60)
        if r.status_code != 200:
            return None
        obj = r.json()
        items = obj.get("response_items", []) if isinstance(obj, dict) else []
        items.sort(key=lambda x: int(x.get("contentLength") or 0), reverse=True)
        for x in items:
            link = x.get("linkToArchive")
            if not link:
                continue
            rr = get(str(link), timeout=50)
            if rr and rr.status_code == 200 and image_info(rr.content):
                return rr.content, str(link), str(x.get("tstamp", ""))
    except Exception as e:
        err("arquivo_image", u, e)
    return None


def recover_one(item: tuple[str, list[dict[str, str]]]) -> dict[str, Any]:
    u, refs = item
    referer = refs[0].get("page_url", "") if refs else ""
    attempts = []
    for v in url_variants(u):
        attempts.append(("live", v))
        got = fetch_direct(v, referer)
        if got:
            data, final = got
            info = image_info(data)
            if info:
                return {"status": "found", "method": "live", "original_url": u, "found_url": final,
                        "capture_time": "", "data": data, "info": info, "refs": refs, "attempts": attempts}
    for v in url_variants(u):
        attempts.append(("wayback", v))
        got = fetch_wayback(v)
        if got:
            data, final, ts = got
            info = image_info(data)
            if info:
                return {"status": "found", "method": "wayback", "original_url": u, "found_url": final,
                        "capture_time": ts, "data": data, "info": info, "refs": refs, "attempts": attempts}
    for v in url_variants(u):
        attempts.append(("arquivo", v))
        got = fetch_arquivo(v)
        if got:
            data, final, ts = got
            info = image_info(data)
            if info:
                return {"status": "found", "method": "arquivo", "original_url": u, "found_url": final,
                        "capture_time": ts, "data": data, "info": info, "refs": refs, "attempts": attempts}
    return {"status": "missing", "original_url": u, "refs": refs, "attempts": attempts}


def write_csv(path: Path, rows: Iterable[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8-sig", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        for row in rows:
            w.writerow(row)


def main() -> int:
    started = time.time()
    all_pages: list[dict[str, str]] = []
    all_refs: list[dict[str, str]] = []

    for name, fn in (("live", crawl_live), ("wayback", wayback_domain), ("arquivo", arquivo_domain)):
        log(f"START {name}")
        try:
            pages, refs = fn()
            all_pages.extend(pages)
            all_refs.extend(refs)
            log(f"DONE {name}: pages={len(pages)} refs={len(refs)}")
        except Exception as e:
            err(name, "", traceback.format_exc())
            log(f"FAIL {name}: {e}")

    log("START commoncrawl")
    ccidx: list[dict[str, Any]] = []
    try:
        pages, refs, ccidx = cc_domain()
        all_pages.extend(pages)
        all_refs.extend(refs)
        log(f"DONE commoncrawl: pages={len(pages)} refs={len(refs)}")
    except Exception as e:
        err("commoncrawl", "", traceback.format_exc())
        log(f"FAIL commoncrawl: {e}")

    grouped: dict[str, list[dict[str, str]]] = defaultdict(list)
    for ref in all_refs:
        u = normalize_url(ref.get("url", ""))
        if not u:
            continue
        ref["url"] = u
        if len(grouped[u]) < 25:
            grouped[u].append(ref)

    def candidate_score(item: tuple[str, list[dict[str, str]]]) -> tuple[int, int, str]:
        u, refs = item
        host = (urlsplit(u).hostname or "").lower()
        external = 0 if host not in ("mel.borda.ru", "wap.mel.borda.ru") and not host.endswith(".borda.ru") else 1
        known = 0 if any(host == h or host.endswith("." + h) for h in KNOWN_IMAGE_HOSTS) else 1
        return (external, known, u)

    candidates = sorted(grouped.items(), key=candidate_score)[:MAX_CANDIDATES]
    log(f"unique image URLs={len(grouped)} recovery candidates={len(candidates)}")

    recovered: list[dict[str, Any]] = []
    missing: list[dict[str, Any]] = []
    seen_hash: dict[str, str] = {}
    total_bytes = 0
    with ThreadPoolExecutor(max_workers=8) as ex:
        futs = {ex.submit(recover_one, item): item[0] for item in candidates}
        for n, fut in enumerate(as_completed(futs), 1):
            u = futs[fut]
            try:
                result = fut.result()
            except Exception as e:
                err("recover_one", u, e)
                continue
            if result.get("status") == "found":
                data = result.pop("data")
                sha = hashlib.sha256(data).hexdigest()
                info = result.get("info", {})
                duplicate_of = seen_hash.get(sha, "")
                if not duplicate_of and total_bytes + len(data) <= MAX_RECOVERED_BYTES:
                    filename = f"{len(seen_hash)+1:04d}_{sha[:16]}{ext_for(str(info.get('format','')))}"
                    (IMG_DIR / filename).write_bytes(data)
                    seen_hash[sha] = filename
                    total_bytes += len(data)
                else:
                    filename = duplicate_of
                result.update({"sha256": sha, "filename": filename, "bytes": len(data), "duplicate": bool(duplicate_of)})
                recovered.append(result)
            else:
                missing.append(result)
            if n % 50 == 0:
                log(f"recovery {n}/{len(candidates)} found={len(recovered)} unique_files={len(seen_hash)}")

    page_fields = ["source", "capture_time", "url", "final_url", "status", "content_type", "bytes", "crawl"]
    write_csv(OUT / "pages.csv", all_pages, page_fields)

    ref_rows = []
    for u, refs in grouped.items():
        for r in refs:
            ref_rows.append(r)
    write_csv(OUT / "image_references.csv", ref_rows, ["url", "page_url", "source", "capture_time", "context"])

    rec_rows = []
    for x in recovered:
        refs = x.get("refs", [])
        rec_rows.append({
            "filename": x.get("filename", ""), "method": x.get("method", ""),
            "original_url": x.get("original_url", ""), "found_url": x.get("found_url", ""),
            "capture_time": x.get("capture_time", ""), "width": x.get("info", {}).get("width", ""),
            "height": x.get("info", {}).get("height", ""), "variance": x.get("info", {}).get("variance", ""),
            "bytes": x.get("bytes", ""), "sha256": x.get("sha256", ""), "duplicate": x.get("duplicate", ""),
            "page_url": refs[0].get("page_url", "") if refs else "",
            "context": refs[0].get("context", "") if refs else "",
        })
    write_csv(OUT / "recovered.csv", rec_rows, ["filename", "method", "original_url", "found_url", "capture_time", "width", "height", "variance", "bytes", "sha256", "duplicate", "page_url", "context"])

    miss_rows = []
    for x in missing:
        refs = x.get("refs", [])
        miss_rows.append({"original_url": x.get("original_url", ""),
                          "page_url": refs[0].get("page_url", "") if refs else "",
                          "source": refs[0].get("source", "") if refs else "",
                          "capture_time": refs[0].get("capture_time", "") if refs else "",
                          "context": refs[0].get("context", "") if refs else ""})
    write_csv(OUT / "missing.csv", miss_rows, ["original_url", "page_url", "source", "capture_time", "context"])

    (OUT / "recovered.json").write_text(json.dumps(recovered, ensure_ascii=False, indent=2, default=str), encoding="utf-8")
    (OUT / "missing.json").write_text(json.dumps(missing, ensure_ascii=False, indent=2, default=str), encoding="utf-8")
    (OUT / "errors.json").write_text(json.dumps(ERRORS, ensure_ascii=False, indent=2), encoding="utf-8")
    summary = {
        "started_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(started)),
        "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "duration_sec": round(time.time() - started, 1),
        "pages_examined": len(all_pages),
        "image_reference_mentions": len(all_refs),
        "unique_image_urls": len(grouped),
        "candidates_checked": len(candidates),
        "recovered_url_hits": len(recovered),
        "recovered_unique_files": len(seen_hash),
        "recovered_bytes": total_bytes,
        "missing_after_checks": len(missing),
        "errors": len(ERRORS),
        "commoncrawl_indexes_seen": len(ccidx),
    }
    (OUT / "summary.json").write_text(json.dumps(summary, ensure_ascii=False, indent=2), encoding="utf-8")
    (OUT / "README.txt").write_text(
        "Melborda recovery raw evidence.\n"
        "recovered.csv links each saved image to the original URL and forum page/context.\n"
        "No image should be accepted into the historical import until manually inspected.\n",
        encoding="utf-8")
    log("SUMMARY " + json.dumps(summary, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
