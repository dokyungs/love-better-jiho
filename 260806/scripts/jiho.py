#!/usr/bin/env python3
"""지호 1년 성장 로그 파이프라인.

사용법 (프로젝트 루트에서):
    python3 scripts/jiho.py scan       # staging/ + organized/ 메타데이터 → data/meta.json
    python3 scripts/jiho.py dedupe     # 이미 받은 사진(내용 동일)이면 trash/ 로 격리
    python3 scripts/jiho.py geocode    # GPS 좌표 → 지명 (Nominatim, 결과는 캐시)
    python3 scripts/jiho.py organize   # staging/ → organized/YYYY-MM/YYYY-MM-DD__장소/
    python3 scripts/jiho.py thumbs     # 갤러리용 썸네일 (sips / ffmpeg / qlmanage)
    python3 scripts/jiho.py sheets     # 요약 작성용 컨택트시트
    python3 scripts/jiho.py build      # index.html + LOG.md 생성
    python3 scripts/jiho.py all        # 위 전체를 순서대로
    python3 scripts/jiho.py serve      # 편집 가능한 갤러리 로컬 서버 (--lan: 다른 기기에서도 접속)
    python3 scripts/jiho.py undo       # 마지막 이동(정리/중복격리) 되돌리기
    python3 scripts/jiho.py trash      # 중복 보관함 확인 / --empty 로 완전 삭제
    python3 scripts/jiho.py merge      # 브라우저에서 내보낸 수정본 반영

새 사진은 staging/ 에 넣고 `./scripts/run_all.sh` 만 다시 돌리면 된다.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import html
import json
import math
import os
import re
import shutil
import socket
import subprocess
import sys
import threading
import time
import unicodedata
import urllib.parse
import urllib.request
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from jihometa import IMAGE_EXT, MOTION_SUFFIX, VIDEO_EXT, extract_motion, probe  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
STAGING = ROOT / "staging"
ORGANIZED = ROOT / "organized"
REVIEW = ROOT / "review"
TRASH = ROOT / "trash"          # 중복본을 바로 지우지 않고 여기로 옮긴다
DATA = ROOT / "data"
THUMBS = ROOT / "gallery" / "thumbs"
SHEETS = ROOT / "gallery" / "sheets"

META_JSON = DATA / "meta.json"                # 자동 생성 (직접 고치지 말 것)
PLACES_JSON = DATA / "places.json"            # 좌표 → 지명 캐시 (자동)
PLACE_OVERRIDES = DATA / "places_overrides.json"  # 좌표 그룹 지명 수정 (수동/웹편집)
SUMMARY_JSON = DATA / "summaries.json"        # 파일명 → 한 줄 요약
OVERRIDES_JSON = DATA / "overrides.json"      # 파일별 날짜/장소 수정
DAY_PLACES_JSON = DATA / "day_places.json"    # 날짜별 장소 일괄 지정 (GPS 없는 사진용)
NOTES_JSON = DATA / "notes.json"              # 생일·제목·날짜별 메모
MANIFEST = DATA / "move_manifest.jsonl"       # organize 이동 기록 (undo 용)

TZ_OFFSET = 9.0          # Asia/Seoul
GEO_PRECISION = 3        # 좌표 반올림 자리수(≈100m) → 같은 장소로 묶는 단위
IGNORE = {".DS_Store", "Thumbs.db"}
NO_PLACE = "장소 미상"


# --------------------------------------------------------------------- 공통

def load_json(path: Path, default):
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print(f"  ! {path.name} 파싱 실패 — 기본값 사용", file=sys.stderr)
    return default


def save_json(path: Path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    tmp.replace(path)


def media_files(root: Path):
    if not root.exists():
        return
    for p in sorted(root.rglob("*")):
        if p.is_file() and p.name not in IGNORE and not p.name.startswith("."):
            if p.name.endswith(MOTION_SUFFIX):
                continue          # 모션 포토에서 뽑은 클립은 사진에 딸린 것이라 따로 세지 않는다
            if p.suffix.lower() in IMAGE_EXT | VIDEO_EXT:
                yield p


def file_hash(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def geo_key(lat, lon) -> str | None:
    if lat is None or lon is None:
        return None
    return f"{round(lat, GEO_PRECISION):.3f},{round(lon, GEO_PRECISION):.3f}"


def safe_name(s: str) -> str:
    s = unicodedata.normalize("NFC", s)
    s = re.sub(r"[/\\:*?\"<>|]", "", s).strip()
    return re.sub(r"\s+", "-", s)[:60] or "unknown"


def norm_datetime(s: str | None) -> str | None:
    """'2026-06-13', '2026-06-13 09:03', '2026-06-13T09:03:24' 등을 표준형으로."""
    if not s:
        return None
    s = s.strip().replace("T", " ")
    m = re.match(r"(\d{4})[-/.](\d{1,2})[-/.](\d{1,2})(?:[ ]+(\d{1,2}):(\d{2})(?::(\d{2}))?)?$", s)
    if not m:
        return None
    y, mo, d, hh, mm, ss = m.groups()
    return (f"{int(y):04d}-{int(mo):02d}-{int(d):02d} "
            f"{int(hh or 0):02d}:{int(mm or 0):02d}:{int(ss or 0):02d}")


def birthday(notes) -> dt.date | None:
    try:
        return dt.date.fromisoformat(notes.get("birthday", ""))
    except ValueError:
        return None


def age_label(day: str | None, bday: dt.date | None) -> str | None:
    """생일 기준 'D+123 · 4개월 2일' 라벨."""
    if not day or not bday:
        return None
    try:
        d = dt.date.fromisoformat(day[:10])
    except ValueError:
        return None
    days = (d - bday).days
    if days < 0:
        return f"출생 {-days}일 전"
    months = (d.year - bday.year) * 12 + (d.month - bday.month) - (1 if d.day < bday.day else 0)
    if months <= 0:
        return f"D+{days}"
    y, mo = divmod(bday.month - 1 + months, 12)
    try:
        anchor = bday.replace(year=bday.year + y, month=mo + 1)
    except ValueError:                     # 2/30 같은 날짜 → 그 달 말일로
        anchor = bday.replace(year=bday.year + y, month=mo + 1, day=28)
    rem = (d - anchor).days
    return f"D+{days} · {months}개월 {rem}일" if rem else f"D+{days} · {months}개월"


# ------------------------------------------------------------ 수동 수정 반영

def resolve_places():
    """자동 지오코딩 캐시 + 사람이 고친 지명을 합친 최종 매핑."""
    places = load_json(PLACES_JSON, {})
    for key, val in load_json(PLACE_OVERRIDES, {}).items():
        entry = dict(places.get(key, {}))
        entry.update(val if isinstance(val, dict) else {"label": val})
        entry["manual"] = True
        places[key] = entry
    return places


def apply_overrides(items, places=None, overrides=None):
    """probe 결과 위에 사람이 고친 날짜/장소를 덮어써 최종 뷰를 만든다.

    장소 우선순위:
      1. 파일별 수동 지정          (data/overrides.json)
      2. 사진 자체의 GPS           (data/places.json + places_overrides.json)
      3. 날짜별 수동 지정          (data/day_places.json)
      4. 같은 날 다른 사진의 GPS   — 그날 GPS가 한 곳뿐일 때만, "추정"으로 표시
    """
    places = places if places is not None else resolve_places()
    overrides = overrides if overrides is not None else load_json(OVERRIDES_JSON, {})
    day_places = load_json(DAY_PLACES_JSON, {})

    out = []
    for m in items:
        m = dict(m)
        ov = overrides.get(m["file"], {})
        if ov.get("taken_local"):
            m["taken_local"] = norm_datetime(ov["taken_local"]) or m["taken_local"]
            m["date_source"] = "manual"
        m["place_auto"] = places.get(m.get("geo_key") or "", {}).get("label")
        m["place_manual"] = ov.get("place")
        out.append(m)

    # 날짜별로 GPS 라벨이 딱 하나면 그날의 나머지 사진에도 같은 장소로 추정
    same_day: dict[str, set] = {}
    for m in out:
        if m.get("taken_local") and m["place_auto"]:
            same_day.setdefault(m["taken_local"][:10], set()).add(m["place_auto"])
    inferred = {d: next(iter(s)) for d, s in same_day.items() if len(s) == 1}

    for m in out:
        day = (m.get("taken_local") or "")[:10]
        if m["place_manual"]:
            m["place"], m["place_source"] = m["place_manual"], "manual"
        elif m["place_auto"]:
            m["place"], m["place_source"] = m["place_auto"], "gps"
        elif day_places.get(day):
            m["place"], m["place_source"] = day_places[day], "manual-day"
        elif inferred.get(day):
            m["place"], m["place_source"] = inferred[day], "inferred"
        else:
            m["place"], m["place_source"] = None, None
    return out


# --------------------------------------------------------------------- scan

def cmd_scan(args):
    """staging/ · organized/ · review/ 의 모든 미디어를 훑어 data/meta.json 갱신."""
    old = {m["path"]: m for m in load_json(META_JSON, {"items": []})["items"]}
    items = []
    for root, area in ((STAGING, "staging"), (ORGANIZED, "organized"), (REVIEW, "review")):
        for p in media_files(root):
            rel = str(p.relative_to(ROOT))
            prev = old.get(rel)
            if prev and not args.force and prev.get("bytes") == p.stat().st_size:
                info = dict(prev)                # 변경 없음 → 재파싱 생략
            else:
                info = probe(p, TZ_OFFSET)
            if not info.get("sha256") or args.force:
                info["sha256"] = file_hash(p)    # 중복 판정용
            info["path"] = rel
            info["area"] = area
            info["geo_key"] = geo_key(info.get("lat"), info.get("lon"))
            clip = p.with_name(p.name.rsplit(".", 1)[0] + MOTION_SUFFIX)
            info["motion"] = str(clip.relative_to(ROOT)) if clip.exists() else None
            items.append(info)

    items.sort(key=lambda m: (m["taken_local"] or "9999", m["file"]))
    save_json(META_JSON, {"generated": dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
                          "count": len(items), "items": items})

    dated = sum(1 for m in items if m["taken_local"])
    gps = sum(1 for m in items if m["geo_key"])
    print(f"scan: {len(items)}개 (촬영일시 {dated} / GPS {gps}) → {META_JSON.relative_to(ROOT)}")
    if len(items) - dated:
        print(f"  · 날짜 없음 {len(items) - dated}개 → organize 시 review/ 로")
    return items


# ------------------------------------------------------------------ geocode

def _nominatim(lat, lon):
    url = "https://nominatim.openstreetmap.org/reverse?" + urllib.parse.urlencode({
        "format": "jsonv2", "lat": f"{lat}", "lon": f"{lon}",
        "zoom": "16", "accept-language": "ko",
    })
    req = urllib.request.Request(url, headers={"User-Agent": "jiho-growth-log/1.0 (personal)"})
    with urllib.request.urlopen(req, timeout=20) as r:
        return json.loads(r.read().decode("utf-8"))


def _label_from(addr: dict, fallback: str) -> str:
    """주소 컴포넌트에서 '서울 마포구 상암동' 같은 짧은 지명을 만든다."""
    city = (addr.get("city") or addr.get("province") or addr.get("state") or "")
    for suffix in ("특별자치시", "특별자치도", "특별시", "광역시"):
        city = city.replace(suffix, "")
    gu = addr.get("borough") or addr.get("city_district") or addr.get("county") or ""
    dong = (addr.get("quarter") or addr.get("neighbourhood") or addr.get("suburb")
            or addr.get("village") or addr.get("town") or "")
    seen, parts = set(), []
    for p in (city, gu, dong):
        if p and p not in seen:
            seen.add(p)
            parts.append(p)
    return " ".join(parts) or fallback or NO_PLACE


def cmd_geocode(args):
    meta = load_json(META_JSON, {"items": []})
    places = load_json(PLACES_JSON, {})
    keys = sorted({m["geo_key"] for m in meta["items"] if m.get("geo_key")})
    todo = [k for k in keys if k not in places or args.force]
    print(f"geocode: 좌표 그룹 {len(keys)}개 · 조회 필요 {len(todo)}개")

    for i, key in enumerate(todo, 1):
        lat, lon = (float(x) for x in key.split(","))
        try:
            res = _nominatim(lat, lon)
            addr = res.get("address", {})
            places[key] = {"label": _label_from(addr, res.get("name", "")),
                           "poi": res.get("name") or None,
                           "display": res.get("display_name"),
                           "lat": lat, "lon": lon}
            poi = places[key]["poi"]
            print(f"  [{i}/{len(todo)}] {key} → {places[key]['label']}" + (f"  ({poi})" if poi else ""))
        except Exception as e:                   # 네트워크 실패분은 다음 실행에서 재시도
            print(f"  [{i}/{len(todo)}] {key} 실패: {e}", file=sys.stderr)
        save_json(PLACES_JSON, places)
        if i < len(todo):
            time.sleep(1.1)                      # Nominatim 이용 정책: 초당 1회 이하
    return places


# ------------------------------------------------------------------- motion

def cmd_motion(args):
    """모션 포토(.MP.jpg 등)에 붙어 있는 짧은 동영상을 뽑아낸다.

    구글 포토의 '모션 포토'는 JPEG 뒤에 1~3초짜리 MP4 가 그대로 붙어 있다.
    다시 받을 필요 없이 이미 가진 파일에서 바로 꺼내 갤러리에서 재생한다.
    뽑아낸 클립은 원본 옆에 `<이름>.motion.mp4` 로 저장하고, 사진에 딸린
    것으로 취급해 갤러리 개수에는 따로 세지 않는다.
    """
    meta = load_json(META_JSON, {"items": []})
    cand = [m for m in meta["items"]
            if m["kind"] == "image" and re.search(r"\.MP\.jpg$|^MVIMG_|^\d{6}_MVIMG_",
                                                  m["file"], re.I)]
    made = have = none = 0
    for m in cand:
        src = ROOT / m["path"]
        dest = src.with_name(src.name.rsplit(".", 1)[0] + MOTION_SUFFIX)
        if dest.exists():
            have += 1
            continue
        if extract_motion(src, dest):
            made += 1
        else:
            none += 1
            if args.verbose:
                print(f"  · 내장 영상 없음: {m['file']}")
    print(f"motion: 모션 포토 후보 {len(cand)}개 → 추출 {made} / 기존 {have} / 영상 없음 {none}")


# ------------------------------------------------------------------- dedupe

def cmd_dedupe(args):
    """staging/ 안의 중복본을 골라낸다.

    이미 organized/ · review/ 에 들어간 파일과 내용(SHA-256)이 같으면 중복으로 본다.
    staging 안에서 같은 내용이 여러 번 들어온 경우도 첫 번째만 남긴다.
    안전을 위해 곧바로 삭제하지 않고 trash/ 로 옮기며, 원본이 실제로 존재하는지
    확인한 뒤에만 옮긴다. (완전 삭제는 `jiho.py trash --empty`)
    """
    meta = load_json(META_JSON, {"items": []})
    keep: dict[str, str] = {}          # sha256 → 남길 파일 경로
    for m in meta["items"]:
        if m["area"] != "staging" and m.get("sha256"):
            keep.setdefault(m["sha256"], m["path"])

    dupes, seen_staged = [], {}
    for m in meta["items"]:
        if m["area"] != "staging":
            continue
        h = m.get("sha256")
        if not h:
            continue
        original = keep.get(h) or seen_staged.get(h)
        if original is None:
            seen_staged[h] = m["path"]
            continue
        if not (ROOT / original).exists():   # 원본이 없으면 중복 처리하지 않는다
            continue
        dupes.append((m, original))

    if not dupes:
        print("dedupe: 중복 없음")
        return []
    print(f"dedupe: 중복 {len(dupes)}개" + ("  [dry-run]" if args.dry_run else ""))
    for m, original in dupes:
        print(f"  {m['file']}  ==  {original}")
    if args.dry_run:
        return dupes

    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    dest_dir = TRASH / stamp
    dest_dir.mkdir(parents=True, exist_ok=True)
    with MANIFEST.open("a", encoding="utf-8") as log:
        at = dt.datetime.now().isoformat(timespec="seconds")
        for m, original in dupes:
            src = ROOT / m["path"]
            if not src.exists():
                continue
            dest = dest_dir / src.name
            n = 2
            while dest.exists():
                dest = dest_dir / f"{src.stem}~{n}{src.suffix}"
                n += 1
            shutil.move(str(src), str(dest))
            log.write(json.dumps({"at": at, "from": m["path"],
                                  "to": str(dest.relative_to(ROOT)),
                                  "dup_of": original}, ensure_ascii=False) + "\n")
    _prune_empty(STAGING)
    print(f"  → {dest_dir.relative_to(ROOT)}/ 로 이동 (되돌리기: jiho.py undo)")
    return dupes


def cmd_trash(args):
    if not TRASH.exists():
        print("trash: 비어 있습니다.")
        return
    files = [p for p in TRASH.rglob("*") if p.is_file()]
    total = sum(p.stat().st_size for p in files)
    print(f"trash: {len(files)}개 / {total / 1e6:.0f}MB")
    for p in sorted(files):
        print(f"  {p.relative_to(ROOT)}")
    if args.empty:
        if files and not args.yes:
            ans = input(f"정말 {len(files)}개를 완전히 삭제할까요? [y/N] ").strip().lower()
            if ans != "y":
                print("  취소")
                return
        shutil.rmtree(TRASH, ignore_errors=True)
        print("  완전 삭제했습니다.")


# -------------------------------------------------------------------- merge

def cmd_merge(args):
    """브라우저에서 내보낸 pending_edits.json 을 data/*.json 에 반영."""
    path = Path(args.path) if args.path else DATA / "pending_edits.json"
    if not path.exists():
        print(f"merge: {path} 가 없습니다.")
        return
    pending = load_json(path, {})
    n = 0
    for key, patch in pending.items():
        if key.startswith("__note__"):
            _save_note({"day": key[len("__note__"):], "text": patch.get("note", "")})
        elif key.startswith("__dayplace__"):
            _save_day_place({"day": key[len("__dayplace__"):], "label": patch.get("dayplace", "")})
        else:
            _save_item({"file": key, **patch})
        n += 1
    print(f"merge: {n}개 반영 완료 — `jiho.py build` 로 갤러리를 다시 만드세요.")


# ----------------------------------------------------------------- organize

def cmd_organize(args):
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    moves = []

    for m in items:
        # staging 은 항상, review 는 날짜가 생겼을 때만 옮긴다.
        if m["area"] == "staging":
            pass
        elif m["area"] == "review" and m.get("taken_local"):
            pass
        else:
            continue
        src = ROOT / m["path"]
        taken = m.get("taken_local")
        if not taken:
            dest_dir, newname = REVIEW / "no-date", src.name
        else:
            day = taken[:10]
            folder = f"{day}__{safe_name(m['place'])}" if m.get("place") else day
            dest_dir = ORGANIZED / day[:7] / folder
            base = re.sub(r"^\d{6}_", "", src.name)      # 재정리 시 시각 접두사 중복 방지
            newname = f"{taken[11:].replace(':', '')}_{base}"
        dest = dest_dir / newname
        if dest.resolve() == src.resolve():
            continue
        n = 2
        while dest.exists():
            dest = dest_dir / f"{Path(newname).stem}~{n}{Path(newname).suffix}"
            n += 1
        moves.append((src, dest))

    if not moves:
        print("organize: 정리할 파일이 없습니다.")
        return
    print(f"organize: {len(moves)}개 이동" + ("  [dry-run]" if args.dry_run else ""))
    by_dir = {}
    for src, dest in moves:
        by_dir.setdefault(dest.parent, []).append(dest.name)
    for d in sorted(by_dir):
        print(f"  {d.relative_to(ROOT)}  ({len(by_dir[d])}개)")
    if args.dry_run:
        return

    DATA.mkdir(parents=True, exist_ok=True)
    with MANIFEST.open("a", encoding="utf-8") as log:
        stamp = dt.datetime.now().isoformat(timespec="seconds")
        for src, dest in moves:
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(src), str(dest))
            log.write(json.dumps({"at": stamp, "from": str(src.relative_to(ROOT)),
                                  "to": str(dest.relative_to(ROOT))}, ensure_ascii=False) + "\n")
    _prune_empty(STAGING)
    _prune_empty(REVIEW)
    print(f"  이동 기록 → {MANIFEST.relative_to(ROOT)}  (되돌리기: jiho.py undo)")


def _prune_empty(root: Path):
    if not root.exists():
        return
    for d in sorted(root.rglob("*"), reverse=True):
        if d.is_dir() and not any(d.iterdir()):
            d.rmdir()


def cmd_undo(args):
    """가장 최근 organize 배치를 통째로 되돌린다."""
    lines = [json.loads(l) for l in
             (MANIFEST.read_text(encoding="utf-8").splitlines() if MANIFEST.exists() else [])
             if l.strip()]
    if not lines:
        print("undo: 되돌릴 이동 기록이 없습니다.")
        return
    last = lines[-1]["at"]
    batch = [l for l in lines if l["at"] == last]
    print(f"undo: {last} 배치 {len(batch)}개 되돌리는 중")
    for rec in reversed(batch):
        src, dest = ROOT / rec["to"], ROOT / rec["from"]
        if src.exists():
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(src), str(dest))
    MANIFEST.write_text("".join(json.dumps(l, ensure_ascii=False) + "\n"
                                for l in lines if l["at"] != last), encoding="utf-8")
    _prune_empty(ORGANIZED)
    print("  완료")


# ------------------------------------------------------------------- thumbs

def _thumb_path(m, size: int) -> Path:
    stem = re.sub(r"[^A-Za-z0-9._-]", "_", m["file"])
    return THUMBS / f"{size}_{stem}.jpg"


def _make_image_thumb(src: Path, dst: Path, size: int) -> bool:
    dst.parent.mkdir(parents=True, exist_ok=True)
    r = subprocess.run(["sips", "-Z", str(size), "-s", "format", "jpeg",
                        "-s", "formatOptions", "70", str(src), "--out", str(dst)],
                       capture_output=True)
    return r.returncode == 0 and dst.exists()


def _make_video_thumb(src: Path, dst: Path, size: int) -> bool:
    """ffmpeg 가 있으면 중간 프레임을, 없으면 qlmanage 포스터 프레임을 쓴다."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    if shutil.which("ffmpeg"):
        r = subprocess.run(["ffmpeg", "-y", "-loglevel", "error", "-ss", "0.5", "-i", str(src),
                            "-frames:v", "1", "-vf", f"scale={size}:-1", str(dst)],
                           capture_output=True)
        if r.returncode == 0 and dst.exists():
            return True
    tmp = dst.parent / ("_ql_" + dst.stem)
    tmp.mkdir(parents=True, exist_ok=True)
    subprocess.run(["qlmanage", "-t", "-s", str(size), "-o", str(tmp), str(src)],
                   capture_output=True)
    made = sorted(tmp.glob("*.png"))
    ok = False
    if made:
        subprocess.run(["sips", "-s", "format", "jpeg", "-s", "formatOptions", "70",
                        str(made[0]), "--out", str(dst)], capture_output=True)
        ok = dst.exists()
    shutil.rmtree(tmp, ignore_errors=True)
    return ok


def ensure_thumb(m, size: int) -> bool:
    dst = _thumb_path(m, size)
    if dst.exists():
        return True
    src = ROOT / m["path"]
    if not src.exists():
        return False
    return (_make_video_thumb if m["kind"] == "video" else _make_image_thumb)(src, dst, size)


def cmd_thumbs(args):
    meta = load_json(META_JSON, {"items": []})
    made = skipped = failed = 0
    for m in meta["items"]:
        if _thumb_path(m, args.size).exists() and not args.force:
            skipped += 1
            continue
        if args.force:
            _thumb_path(m, args.size).unlink(missing_ok=True)
        ok = ensure_thumb(m, args.size)
        made += ok
        failed += not ok
        if not ok:
            print(f"  ! 썸네일 실패: {m['file']}", file=sys.stderr)
    print(f"thumbs({args.size}px): 생성 {made} / 유지 {skipped} / 실패 {failed}")


# ------------------------------------------------------------------- sheets

def cmd_sheets(args):
    """요약이 아직 없는 항목만 모아 번호가 찍힌 격자 시트를 만든다.

    이 시트를 보고(사람이든 AI든) data/summaries.json 을 채우는 용도.
    """
    meta = load_json(META_JSON, {"items": []})
    summaries = load_json(SUMMARY_JSON, {})
    todo = [m for m in meta["items"] if not summaries.get(m["file"]) or args.force]
    if not todo:
        print("sheets: 요약이 필요한 항목이 없습니다.")
        return
    SHEETS.mkdir(parents=True, exist_ok=True)
    for m in todo:
        ensure_thumb(m, args.size)

    per, index = args.per_sheet, {}
    for si in range(0, len(todo), per):
        chunk, no = todo[si:si + per], si // per + 1
        index[f"sheet{no:02d}"] = [{"n": i + 1, "file": m["file"], "taken": m["taken_local"],
                                    "kind": m["kind"]} for i, m in enumerate(chunk)]
        _write_sheet(no, chunk, args.size)
    save_json(SHEETS / "index.json", index)
    print(f"sheets: {len(todo)}개 → {math.ceil(len(todo) / per)}장 ({SHEETS.relative_to(ROOT)}/)")


def _write_sheet(no: int, chunk, size: int):
    cells = []
    for i, m in enumerate(chunk, 1):
        rel = os.path.relpath(_thumb_path(m, size), SHEETS).replace(os.sep, "/")
        badge = "▶︎ " if m["kind"] == "video" else ""
        cells.append(f'<figure><span class=n>{i}</span>'
                     f'<img src="{html.escape(rel)}" loading="lazy">'
                     f'<figcaption>{badge}{html.escape(m["taken_local"] or "날짜없음")}</figcaption></figure>')
    (SHEETS / f"sheet{no:02d}.html").write_text(
        "<meta charset=utf-8><style>"
        "body{background:#111;color:#eee;font:13px/1.4 system-ui;margin:12px}"
        "main{display:grid;grid-template-columns:repeat(4,1fr);gap:10px}"
        "figure{margin:0;position:relative}"
        "img{width:100%;aspect-ratio:1;object-fit:cover;border-radius:6px;background:#222}"
        ".n{position:absolute;top:4px;left:4px;background:#000c;padding:1px 6px;border-radius:4px;"
        "font-weight:700}figcaption{opacity:.7;font-size:11px;margin-top:3px}</style>"
        f"<h3>sheet {no:02d}</h3><main>{''.join(cells)}</main>", encoding="utf-8")


# -------------------------------------------------------------------- build

def group_days(items):
    """날짜 → 장소 → 항목. 갤러리와 LOG.md 가 공유한다."""
    days = {}
    for m in items:
        if not m.get("taken_local"):
            continue
        day = m["taken_local"][:10]
        days.setdefault(day, {}).setdefault(m.get("place") or NO_PLACE, []).append(m)
    for day in days:
        for place in days[day]:
            days[day][place].sort(key=lambda m: m["taken_local"])
    return dict(sorted(days.items()))


def cmd_build(args):
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    summaries = load_json(SUMMARY_JSON, {})
    notes = load_json(NOTES_JSON, {})
    bday = birthday(notes)

    days = group_days(items)
    review = [m for m in items if not m.get("taken_local")]

    _write_log_md(days, review, summaries, notes, bday)
    _write_gallery(days, review, summaries, notes, bday, args.size)
    total = sum(len(v) for d in days.values() for v in d.values())
    print(f"build: index.html · LOG.md  ({len(days)}일 / {total}컷 / 확인필요 {len(review)})")
    missing = [m for m in items if not summaries.get(m["file"])]
    if missing:
        print(f"  · 요약 없는 항목 {len(missing)}개 — 갤러리에서 직접 쓰거나 `jiho.py sheets` 사용")


def _write_log_md(days, review, summaries, notes, bday):
    total = sum(len(v) for d in days.values() for v in d.values())
    L = [f"# {notes.get('title', '지호의 첫 1년')} — 성장 로그", ""]
    if bday:
        L.append(f"- 생일: **{bday.isoformat()}**")
    L += [f"- 기간: {min(days) if days else '-'} ~ {max(days) if days else '-'}",
          f"- 총 {total}컷 / {len(days)}일",
          f"- 생성: {dt.datetime.now():%Y-%m-%d %H:%M}", ""]
    for day, byplace in days.items():
        age = age_label(day, bday)
        L.append(f"## {day}" + (f"  ({age})" if age else ""))
        note = notes.get("days", {}).get(day)
        if note:
            L.append(f"> {note}")
        for place, ms in byplace.items():
            L.append(f"### {place}")
            for m in ms:
                s = summaries.get(m["file"], "")
                tag = "🎬" if m["kind"] == "video" else "📷"
                dur = f" _{m['duration_sec']}초_" if m.get("duration_sec") else ""
                L.append(f"- `{m['taken_local'][11:16]}` {tag} {s or '_(요약 없음)_'}{dur}  "
                         f"<sub>{m['file']}</sub>")
        L.append("")
    if review:
        L += ["## ⚠️ 확인 필요 (review/)", "",
              "촬영 일시를 찾지 못한 파일입니다. 갤러리 편집 모드에서 날짜를 넣어주세요.", ""]
        for m in review:
            L.append(f"- `{m['file']}` — {m['path']}")
        L.append("")
    (ROOT / "LOG.md").write_text("\n".join(L), encoding="utf-8")


def shot_shape(m) -> str:
    """화면에 보이는 방향. EXIF orientation 5~8 은 가로/세로가 뒤집혀 저장된다."""
    w, h = m.get("width"), m.get("height")
    if not w or not h:
        return "sq"
    if m["kind"] == "image" and (m.get("orientation") or 1) in (5, 6, 7, 8):
        w, h = h, w
    r = w / h
    return "ls" if r > 1.15 else "pt" if r < 0.87 else "sq"


def _shot_html(m, summaries, size, out=None, lite=False, keep=None):
    """lite=True 면 원본 대신 썸네일을 가리켜, 썸네일만으로 굴러가는 번들을 만든다."""
    out = out or ROOT
    thumb = _thumb_path(m, size)
    rel = os.path.relpath(thumb, out).replace(os.sep, "/")
    s = summaries.get(m["file"], "")
    vid = m["kind"] == "video"
    dur = f'<span class="dur">{m["duration_sec"]}s</span>' if m.get("duration_sec") else ""
    src_badge = {"exif": "EXIF", "manual": "수동"}.get(m.get("date_source") or "", "추정")
    motion = m.get("motion") or ""
    keep = keep if keep is not None else set()
    if lite:
        # 원본을 담지 않는 번들: 사진은 썸네일로, 영상/모션은 담은 것만 남긴다
        full = m["path"] if m["path"] in keep else rel
        motion = motion if motion in keep else ""
    else:
        full = m["path"]
    data = {
        "file": m["file"], "path": full, "kind": m["kind"] if (not lite or m["path"] in keep)
                                                  else "image", "motion": motion,
        "cap": s, "taken": m.get("taken_local") or "",
        "place": m.get("place") or "", "geokey": m.get("geo_key") or "",
        "auto": m.get("place_auto") or "", "dsrc": m.get("date_source") or "",
        "psrc": m.get("place_source") or "",
    }
    attrs = " ".join(f'data-{k}="{html.escape(str(v), quote=True)}"' for k, v in data.items())
    return (f'<figure class="shot {shot_shape(m)}{" vid" if vid else ""}'
            f'{" live" if motion else ""}{" nosum" if not s else ""}" {attrs}>'
            f'<img src="{html.escape(rel)}" loading="lazy" alt="">'
            f'{"<span class=play>▶</span>" if vid else ""}{dur}'
            f'{"<span class=livebadge>◉ LIVE</span>" if motion else ""}'
            f'<span class="src">{src_badge}</span>'
            f'<figcaption>{html.escape(s) or "<i>요약 없음</i>"}</figcaption></figure>')


def _text_vectors(ordered, summaries, notes, day_places):
    """요약문으로 검색·유사도용 TF-IDF 벡터를 만든다 (외부 라이브러리 없이).

    한국어는 띄어쓰기만으로는 잘 안 잘려서 글자 2-gram 을 같이 쓴다.
    '벚꽃'으로 검색하면 '벚꽃길'·'벚나무'가, '물놀이'로는 '튜브'가 붙은 컷이
    같이 걸리도록 하는 정도의 가벼운 의미 검색이다.
    """
    import math as _math
    from collections import Counter

    docs = []
    for m in ordered:
        day = (m.get("taken_local") or "")[:10]
        parts = [summaries.get(m["file"], ""), m.get("place") or "",
                 notes.get("days", {}).get(day, ""), day_places.get(day, ""),
                 "영상" if m["kind"] == "video" else "사진"]
        text = " ".join(p for p in parts if p)
        toks = [w for w in re.split(r"[\s,·—\-()]+", text) if len(w) > 1]
        grams = [text[i:i + 2] for i in range(len(text) - 1) if not text[i:i + 2].isspace()]
        docs.append(Counter(toks + [g for g in grams if " " not in g]))

    df = Counter()
    for d in docs:
        df.update(d.keys())
    N = max(len(docs), 1)
    idf = {t: _math.log(1 + N / (1 + c)) for t, c in df.items()}

    vecs = []
    for d in docs:
        v = {t: (1 + _math.log(c)) * idf.get(t, 0) for t, c in d.items()}
        norm = _math.sqrt(sum(x * x for x in v.values())) or 1.0
        top = sorted(v.items(), key=lambda kv: -kv[1])[:26]
        vecs.append({t: round(w / norm, 4) for t, w in top})
    return vecs, {t: round(w, 4) for t, w in idf.items()}


def _write_gallery(days, review, summaries, notes, bday, size, out=None, lite=False, keep=None):
    out = out or ROOT
    shot = lambda m: _shot_html(m, summaries, size, out, lite, keep)  # noqa: E731
    day_places = load_json(DAY_PLACES_JSON, {})
    # 월 단위로 묶어 네비게이션을 짧게 (73개 날짜 알약 → 11개 월 알약)
    months: dict[str, list[str]] = {}
    for day in days:
        months.setdefault(day[:7], []).append(day)

    cards, nav = [], []
    for ym, ymdays in months.items():
        cnt = sum(len(v) for d in ymdays for v in days[d].values())
        nav.append(f'<a href="#m{ym}" data-month="{ym}">'
                   f'<b>{int(ym[5:])}월</b><span>{ym[:4]}</span></a>')

    cur_month = None
    for day, byplace in days.items():
        if day[:7] != cur_month:
            cur_month = day[:7]
            mdays = months[cur_month]
            mcnt = sum(len(v) for d in mdays for v in days[d].values())
            span_age = age_label(mdays[0], bday) or ""
            span_age = span_age.split("·")[-1].strip() if "·" in span_age else span_age
            if cards:
                cards.append("</div>")      # 지난 달 격자 닫기
            # 달마다 격자를 따로 둬야 dense 배치가 달 경계를 넘어 카드를 끌어가지 않는다
            cards.append(
                f'<div class="monthsep" id="m{cur_month}" data-month="{cur_month}">'
                f'<h3>{cur_month[:4]}년 {int(cur_month[5:])}월</h3>'
                f'<span>{len(mdays)}일 · {mcnt}컷{f" · {html.escape(span_age)}" if span_age else ""}</span>'
                f'</div><div class="monthgrid">')
        age = age_label(day, bday) or ""
        anchor = f"d{day.replace('-', '')}"
        note = notes.get("days", {}).get(day, "")
        shots = "".join(shot(m) for place in byplace for m in byplace[place])
        placelist = "".join(
            f'<span class="place">{html.escape(p)}'
            f'{" <em>추정</em>" if any(x.get("place_source") == "inferred" for x in byplace[p]) else ""}'
            f'</span>' for p in byplace)
        cnt = sum(len(v) for v in byplace.values())
        span = 1 if cnt <= 4 else 2 if cnt <= 10 else 3   # 사진 많은 날은 넓게
        # 가로 사진은 두 칸을 먹으므로 그만큼 넓게 잡는다
        shapes = [shot_shape(x) for v in byplace.values() for x in v]
        weight = sum(2 if sh == "ls" else 1 for sh in shapes)
        cols = max(1, min(math.ceil(math.sqrt(weight)), 3 * span))
        if any(sh == "ls" for sh in shapes) and cnt > 1:
            cols = max(cols, 2)
        cards.append(
            f'<section class="day" id="{anchor}" data-day="{day}" style="--span:{span}">'
            f'<header><h2>{day}</h2><div class="meta">'
            f'{f"<span class=age>{html.escape(age)}</span>" if age else ""}'
            f'{placelist}<span class="cnt">{cnt}컷</span>'
            f'<span class="dayplace editonly" data-day="{day}" contenteditable="true"'
            f' data-ph="이 날 장소 일괄 지정">{html.escape(day_places.get(day, ""))}</span>'
            f'</div>'
            f'<p class="note" data-day="{day}">{html.escape(note)}</p>'
            f'</header><div class="grid" style="--cols:{cols}">{shots}</div></section>')

    if cards:
        cards.append("</div>")              # 마지막 달 격자 닫기
    if review:
        shots = "".join(shot(m) for m in review)
        cards.append('<div class="monthgrid">')
        cards.append(
            f'<section class="day needs" id="review" style="--span:3">'
            f'<header><h2>⚠︎ 확인 필요</h2><div class="meta">'
            f'<span class="cnt">{len(review)}개</span>'
            f'<span class="place">촬영 일시를 못 찾았습니다 — 클릭해서 날짜를 넣어주세요</span>'
            f'</div></header><div class="grid" style="--cols:{min(len(review), 6) or 1}">'
            f'{shots}</div></section>')
        cards.append('</div>')
        nav.append('<a href="#review" class="warn" data-month="review"><b>⚠︎</b><span>확인</span></a>')

    total = sum(len(v) for d in days.values() for v in d.values())
    nosum = sum(1 for d in days.values() for v in d.values()
                for m in v if not summaries.get(m["file"])) + \
            sum(1 for m in review if not summaries.get(m["file"]))
    # 히어로 배경 사진: notes.json 의 "hero"(파일명) → 없으면 웃는 얼굴 클로즈업 쪽으로
    all_items = [m for d in days.values() for v in d.values() for m in v]
    hero_pick = None
    want = notes.get("hero")
    for m in all_items:
        if want and m["file"] == want:
            hero_pick = m
            break
    if hero_pick is None:
        imgs = [m for m in all_items if m["kind"] == "image"]
        hero_pick = imgs[len(imgs) * 3 // 4] if imgs else (all_items[0] if all_items else None)
    if hero_pick is None:
        hero = ""
    elif lite and hero_pick["path"] not in (keep or set()):
        hero = os.path.relpath(_thumb_path(hero_pick, size), out).replace(os.sep, "/")
    else:
        hero = os.path.relpath(ROOT / hero_pick["path"], out).replace(os.sep, "/")

    ordered = all_items + review          # DOM 의 .shot 순서와 같아야 한다
    vecs, idf = _text_vectors(ordered, summaries, notes, day_places)

    (out / "index.html").write_text(
        _GALLERY_HTML
        .replace("{{TITLE}}", html.escape(notes.get("title", "지호의 첫 1년")))
        .replace("{{HERO}}", html.escape(hero))
        .replace("{{SPAN}}", f"{min(days)} ~ {max(days)}" if days else "")
        .replace("{{TOTAL}}", str(total)).replace("{{DAYS}}", str(len(days)))
        .replace("{{NOSUM}}", str(nosum)).replace("{{REVIEW}}", str(len(review)))
        .replace("{{NAV}}", "".join(nav)).replace("{{CARDS}}", "".join(cards))
        .replace("{{VECS}}", json.dumps(vecs, ensure_ascii=False, separators=(",", ":")))
        .replace("{{IDF}}", json.dumps(idf, ensure_ascii=False, separators=(",", ":"))),
        encoding="utf-8")


# -------------------------------------------------------------------- serve

_rebuild_timer = None
_rebuild_lock = threading.Lock()


def schedule_rebuild(size=480, delay=1.2):
    """편집이 저장될 때마다 index.html · LOG.md 를 자동으로 다시 만든다.

    연달아 저장하면 마지막 것만 반영되도록 잠깐 모아서(디바운스) 실행한다.
    """
    global _rebuild_timer

    def run():
        try:
            cmd_build(argparse.Namespace(size=size))
        except Exception as e:                                    # noqa: BLE001
            print(f"  ! 자동 빌드 실패: {e}", file=sys.stderr)

    with _rebuild_lock:
        if _rebuild_timer:
            _rebuild_timer.cancel()
        _rebuild_timer = threading.Timer(delay, run)
        _rebuild_timer.daemon = True
        _rebuild_timer.start()


class _Handler(SimpleHTTPRequestHandler):
    """정적 서빙 + 편집 저장 API."""

    def __init__(self, *a, **kw):
        super().__init__(*a, directory=str(ROOT), **kw)

    def log_message(self, fmt, *a):
        if "/api/" in (a[0] if a else ""):
            super().log_message(fmt, *a)

    def _json(self, obj, code=200):
        body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    readonly = False

    def do_POST(self):
        if not self.path.startswith("/api/"):
            self.send_error(404)
            return
        if self.readonly:
            self._json({"ok": False, "error": "읽기 전용 모드입니다"}, 403)
            return
        length = int(self.headers.get("Content-Length") or 0)
        try:
            payload = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError:
            self._json({"ok": False, "error": "bad json"}, 400)
            return

        try:
            if self.path == "/api/item":
                self._json(_save_item(payload))
                schedule_rebuild()
            elif self.path == "/api/place":
                self._json(_save_place(payload))
                schedule_rebuild()
            elif self.path == "/api/dayplace":
                self._json(_save_day_place(payload))
                schedule_rebuild()
            elif self.path == "/api/note":
                self._json(_save_note(payload))
                schedule_rebuild()
            elif self.path == "/api/rebuild":
                cmd_build(argparse.Namespace(size=payload.get("size", 480)))
                self._json({"ok": True})
            elif self.path == "/api/organize":
                cmd_all(argparse.Namespace(size=payload.get("size", 480)))
                self._json({"ok": True})
            else:
                self._json({"ok": False, "error": "unknown endpoint"}, 404)
        except Exception as e:                                    # noqa: BLE001
            self._json({"ok": False, "error": str(e)}, 500)


def _save_item(p):
    """한 파일의 요약 / 촬영일시 / 장소 수정 저장."""
    name = p.get("file")
    if not name:
        return {"ok": False, "error": "file 누락"}
    if "summary" in p:
        summaries = load_json(SUMMARY_JSON, {})
        text = (p["summary"] or "").strip()
        if text:
            summaries[name] = text
        else:
            summaries.pop(name, None)
        save_json(SUMMARY_JSON, summaries)

    ov = load_json(OVERRIDES_JSON, {})
    entry = dict(ov.get(name, {}))
    for key in ("taken_local", "place"):
        if key not in p:
            continue
        val = (p[key] or "").strip()
        if key == "taken_local" and val:
            norm = norm_datetime(val)
            if not norm:
                return {"ok": False, "error": f"날짜 형식을 못 읽었습니다: {val}"}
            val = norm
        if val:
            entry[key] = val
        else:
            entry.pop(key, None)
    if entry:
        ov[name] = entry
    else:
        ov.pop(name, None)
    save_json(OVERRIDES_JSON, ov)
    return {"ok": True, "taken_local": entry.get("taken_local"), "place": entry.get("place")}


def _save_place(p):
    """좌표 그룹 전체의 지명을 한 번에 바꾼다."""
    key, label = p.get("geo_key"), (p.get("label") or "").strip()
    if not key:
        return {"ok": False, "error": "geo_key 누락"}
    ov = load_json(PLACE_OVERRIDES, {})
    if label:
        ov[key] = {"label": label}
    else:
        ov.pop(key, None)
    save_json(PLACE_OVERRIDES, ov)
    return {"ok": True}


def _save_day_place(p):
    """GPS 없는 사진들을 위해 그 날짜 전체의 장소를 지정한다."""
    day, label = p.get("day"), (p.get("label") or "").strip()
    if not day:
        return {"ok": False, "error": "day 누락"}
    dp = load_json(DAY_PLACES_JSON, {})
    if label:
        dp[day] = label
    else:
        dp.pop(day, None)
    save_json(DAY_PLACES_JSON, dp)
    return {"ok": True}


def _save_note(p):
    """날짜별 메모 / 제목 / 생일 저장."""
    notes = load_json(NOTES_JSON, {})
    if "day" in p:
        notes.setdefault("days", {})
        text = (p.get("text") or "").strip()
        if text:
            notes["days"][p["day"]] = text
        else:
            notes["days"].pop(p["day"], None)
    for key in ("title", "birthday"):
        if key in p:
            notes[key] = p[key]
    save_json(NOTES_JSON, notes)
    return {"ok": True}


def cmd_bundle(args):
    """원본 없이 썸네일만으로 굴러가는 가벼운 정적 번들을 만든다.

    포트를 못 여는 환경에서 가족에게 공유할 때 쓴다. dist/ 폴더째 어디든
    (정적 호스팅·USB·에어드롭) 올리면 되고, 서버가 필요 없다.
    영상/모션 클립은 기본으로 빼고, --with-video / --with-motion 으로 넣는다.
    """
    dist = ROOT / args.out
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    summaries = load_json(SUMMARY_JSON, {})
    notes = load_json(NOTES_JSON, {})
    bday = birthday(notes)

    if dist.exists():
        shutil.rmtree(dist)
    (dist / "gallery").mkdir(parents=True)
    shutil.copytree(THUMBS, dist / "gallery" / "thumbs")

    keep: set[str] = set()
    for m in items:
        if args.with_video and m["kind"] == "video":
            keep.add(m["path"])
        if args.with_motion and m.get("motion"):
            keep.add(m["motion"])
    for rel in sorted(keep):
        src = ROOT / rel
        if not src.exists():
            continue
        dst = dist / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)

    days = group_days(items)
    review = [m for m in items if not m.get("taken_local")]
    _write_gallery(days, review, summaries, notes, bday, args.size,
                   out=dist, lite=True, keep=keep)

    total = sum(p.stat().st_size for p in dist.rglob("*") if p.is_file())
    print(f"bundle: {dist.relative_to(ROOT)}/  ({total / 1e6:.1f}MB, 파일 "
          f"{sum(1 for p in dist.rglob('*') if p.is_file())}개)")
    print(f"  · 사진 {sum(1 for m in items if m['kind'] == 'image')}장은 썸네일({args.size}px)로 들어갔습니다")
    if not args.with_video:
        print("  · 영상은 포스터만 — 넣으려면 --with-video (원본 218MB)")
    if not args.with_motion:
        print("  · 모션 클립 제외 — 넣으려면 --with-motion (58MB)")
    print(f"  · 확인: open {dist.relative_to(ROOT)}/index.html")


LOCAL_HOSTS = ("127.0.0.1", "localhost", "::1")


def _lan_addrs() -> list[str]:
    """다른 기기에서 이 컴퓨터를 부를 수 있는 주소들 (대표 IP → 호스트네임 순)."""
    out: list[str] = []
    try:  # 기본 경로로 나가는 인터페이스의 IP — 실제로 패킷을 보내지는 않는다
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        out.append(s.getsockname()[0])
        s.close()
    except OSError:
        pass
    host = socket.gethostname()
    try:
        for info in socket.getaddrinfo(host, None, socket.AF_INET):
            ip = info[4][0]
            if not ip.startswith("127."):
                out.append(ip)
    except OSError:
        pass
    if host:
        out.append(f"{host}.local")
    return list(dict.fromkeys(out))


def cmd_serve(args):
    if not (ROOT / "index.html").exists():
        cmd_build(argparse.Namespace(size=args.size))
    _Handler.readonly = args.readonly
    host = "0.0.0.0" if args.lan else args.host
    try:
        srv = ThreadingHTTPServer((host, args.port), _Handler)
    except OSError as e:
        sys.exit(f"serve: {host}:{args.port} 를 열 수 없습니다 — {e}\n"
                 f"  · 포트가 이미 쓰이는 중이면 --port 8766 처럼 다른 번호를 쓰세요.\n"
                 f"  · 그 IP 가 이 컴퓨터 것이 아니면 --lan (모든 주소에서 받기) 을 쓰세요.")
    shown = "127.0.0.1" if host in ("0.0.0.0", "::") else host
    print(f"serve: http://{shown}:{args.port}/  (Ctrl-C 로 종료)")
    if args.readonly:
        print("  · 읽기 전용 — 저장 API 를 막았습니다. 외부 공유용으로 안전합니다.")
    else:
        print("  · 사진을 클릭하면 요약·날짜·장소를 바로 고칠 수 있고 data/*.json 에 저장됩니다.")
    if host in LOCAL_HOSTS:
        print("  · 이 컴퓨터에서만 열립니다 — 다른 기기에서도 보려면 --lan 을 붙이세요.")
    else:
        print("  · 다른 기기에서는 이 주소로 접속하세요:")
        for a in _lan_addrs():
            print(f"      http://{a}:{args.port}/")
        print(f"    (열리지 않으면 이 컴퓨터의 방화벽에서 {args.port} 포트를 허용해 주세요)")
        if not args.readonly:
            print("  ! 같은 네트워크의 누구나 수정할 수 있습니다. 공유용이면 --readonly 를 같이 쓰세요.")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nserve: 종료")


# ---------------------------------------------------------------------- CLI

def cmd_all(args):
    ns = argparse.Namespace(force=False, dry_run=False, verbose=False, size=args.size)
    cmd_scan(ns)
    cmd_dedupe(ns)            # 이미 받은 사진이면 trash/ 로 빼둔다
    cmd_scan(ns)
    cmd_geocode(ns)
    cmd_organize(ns)
    cmd_motion(ns)            # 모션 포토 → 짧은 클립 (정리된 위치 기준)
    cmd_scan(ns)              # 경로가 바뀌었으니 다시 스캔
    cmd_thumbs(ns)
    cmd_build(ns)


def main():
    ap = argparse.ArgumentParser(description="지호 성장 로그 파이프라인")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("scan", help="메타데이터 추출")
    p.add_argument("--force", action="store_true", help="캐시 무시하고 전부 재파싱")
    p.set_defaults(func=cmd_scan)

    p = sub.add_parser("geocode", help="GPS → 지명")
    p.add_argument("--force", action="store_true")
    p.set_defaults(func=cmd_geocode)

    p = sub.add_parser("motion", help="모션 포토에서 짧은 동영상 추출")
    p.add_argument("-v", "--verbose", action="store_true")
    p.set_defaults(func=cmd_motion)

    p = sub.add_parser("dedupe", help="이미 받은 사진이면 trash/ 로")
    p.add_argument("-n", "--dry-run", action="store_true")
    p.set_defaults(func=cmd_dedupe)

    p = sub.add_parser("trash", help="중복 보관함 확인 / 비우기")
    p.add_argument("--empty", action="store_true", help="완전 삭제")
    p.add_argument("-y", "--yes", action="store_true", help="확인 없이 삭제")
    p.set_defaults(func=cmd_trash)

    p = sub.add_parser("merge", help="브라우저 pending_edits.json 반영")
    p.add_argument("path", nargs="?", help="기본값: data/pending_edits.json")
    p.set_defaults(func=cmd_merge)

    p = sub.add_parser("organize", help="staging → organized / review")
    p.add_argument("-n", "--dry-run", action="store_true")
    p.set_defaults(func=cmd_organize)

    p = sub.add_parser("undo", help="마지막 organize 되돌리기")
    p.set_defaults(func=cmd_undo)

    p = sub.add_parser("thumbs", help="썸네일 생성")
    p.add_argument("--size", type=int, default=480)
    p.add_argument("--force", action="store_true")
    p.set_defaults(func=cmd_thumbs)

    p = sub.add_parser("sheets", help="요약 작성용 컨택트시트")
    p.add_argument("--size", type=int, default=480)
    p.add_argument("--per-sheet", type=int, default=12)
    p.add_argument("--force", action="store_true")
    p.set_defaults(func=cmd_sheets)

    p = sub.add_parser("build", help="index.html + LOG.md")
    p.add_argument("--size", type=int, default=480)
    p.set_defaults(func=cmd_build)

    p = sub.add_parser("all", help="전체 파이프라인")
    p.add_argument("--size", type=int, default=480)
    p.set_defaults(func=cmd_all)

    p = sub.add_parser("bundle", help="원본 없이 썸네일만 담은 공유용 정적 번들")
    p.add_argument("--out", default="dist", help="출력 폴더 (기본 dist)")
    p.add_argument("--size", type=int, default=480)
    p.add_argument("--with-video", action="store_true", help="영상 원본도 포함 (+218MB)")
    p.add_argument("--with-motion", action="store_true", help="모션 클립도 포함 (+58MB)")
    p.set_defaults(func=cmd_bundle)

    p = sub.add_parser("serve", help="갤러리 로컬 서버 (편집 가능)")
    p.add_argument("--port", type=int, default=8765)
    p.add_argument("--host", default="127.0.0.1",
                   help="바인딩할 주소 (기본 127.0.0.1 — 이 컴퓨터에서만). "
                        "특정 랜카드 주소만 열려면 그 IP 를 적으세요")
    p.add_argument("--lan", action="store_true",
                   help="같은 네트워크의 다른 기기에서도 접속 허용 (--host 0.0.0.0 과 같음)")
    p.add_argument("--readonly", action="store_true", help="저장 API 차단 — 공유용")
    p.add_argument("--size", type=int, default=480)
    p.set_defaults(func=cmd_serve)

    args = ap.parse_args()
    args.func(args)


_GALLERY_HTML = r"""<!doctype html>
<html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{{TITLE}}</title>
<style>
:root{
  --bg:#fdf9f7;--card:#ffffff;--line:#f2e8e4;--fg:#4a403c;--dim:#a89892;
  --accent:#e79bb0;--accent-ink:#a85c73;--soft:#fdeef2;
  --warn:#d9953c;--ok:#7bb98e;
  --sh:0 2px 12px rgba(168,140,128,.09);--sh-lg:0 10px 34px rgba(168,140,128,.18);
  --r:18px;
}
*{box-sizing:border-box}
html{background:var(--bg)}
body{margin:0;background:transparent;color:var(--fg);
     font:15px/1.65 -apple-system,BlinkMacSystemFont,"Apple SD Gothic Neo",Pretendard,sans-serif}

/* 배경에 지호 사진이 아주 연하게 깔리고 천천히 바뀐다 */
#bgwash{position:fixed;inset:0;z-index:-1;pointer-events:none;overflow:hidden}
#bgwash i{position:absolute;inset:-4%;background-size:cover;background-position:center;
  opacity:0;transition:opacity 2.4s ease-in-out;filter:blur(3px) saturate(.8)}
#bgwash i.on{opacity:.13}
#bgwash::after{content:"";position:absolute;inset:0;
  background:radial-gradient(ellipse at 50% 30%,transparent 0%,var(--bg) 78%)}
@media(prefers-reduced-motion:reduce){#bgwash i{transition:none}}

/* ---------- 히어로: 지호 사진을 배경으로 ---------- */
header.top{position:relative;padding:0;border:0}
.hero{position:relative;min-height:min(58vh,460px);display:flex;flex-direction:column;
  align-items:center;justify-content:flex-end;text-align:center;padding:56px 20px 26px;overflow:hidden}
.hero .bg{position:absolute;inset:0;background-size:cover;background-position:center 28%}
.hero .veil{position:absolute;inset:0;background:linear-gradient(to bottom,
  rgba(255,252,250,.30) 0%,rgba(255,251,249,.55) 42%,rgba(253,249,247,.93) 82%,var(--bg) 100%)}
.hero .inner{position:relative;z-index:1}
.hero h1{margin:0;font-size:clamp(28px,5vw,40px);letter-spacing:-.03em;font-weight:700;
  color:#463b37;text-shadow:0 1px 14px rgba(255,255,255,.9),0 1px 3px rgba(255,255,255,.95)}
.hero .sub{margin:10px 0 0;color:#8d7d77;font-size:14px;
  text-shadow:0 1px 10px rgba(255,255,255,.95)}
.hero .sub b{color:var(--accent-ink);font-weight:600}

.tools{display:flex;justify-content:center;gap:7px;margin-top:18px;flex-wrap:wrap;position:relative;z-index:1}
.tools button{background:#fff;border:1px solid var(--line);color:var(--fg);box-shadow:var(--sh);
  border-radius:999px;padding:7px 15px;font-size:13px;cursor:pointer;font-family:inherit;
  transition:.15s}
.tools button:hover{border-color:var(--accent);color:var(--accent-ink);transform:translateY(-1px)}
.tools button.on{background:var(--accent);color:#fff;border-color:var(--accent);font-weight:600}
.search{position:relative;z-index:1;max-width:520px;margin:14px auto 0}
.search input{width:100%;border:1px solid var(--line);background:rgba(255,255,255,.96);
  color:var(--fg);border-radius:999px;padding:13px 44px 13px 20px;font:16px inherit;
  box-shadow:var(--sh);outline:0;transition:.15s}
.search input:focus{border-color:var(--accent);box-shadow:0 0 0 4px var(--soft),var(--sh)}
.search input::-webkit-search-cancel-button{display:none}
.search button{position:absolute;right:6px;top:50%;transform:translateY(-50%);width:32px;height:32px;
  border:0;border-radius:50%;background:transparent;color:var(--dim);font-size:20px;cursor:pointer;
  display:none}
.search.has button{display:block}
.search button:hover{background:var(--soft);color:var(--accent-ink)}
body.searching .monthsep{display:none}
body.searching .day.hide,body.searching .shot.hide{display:none}
body.searching .day .note,body.searching .day .meta .cnt{display:none}
#status{font-size:12px;color:var(--dim);min-height:18px;text-align:center;margin-top:10px;
  position:relative;z-index:1}
#status.err{color:var(--warn)}#status.ok{color:var(--ok)}

/* ---------- 날짜 네비 ---------- */
/* 월 단위 네비 — 11개라 가로 스크롤 없이 한눈에 들어온다 */
nav{position:sticky;top:0;z-index:5;display:flex;gap:7px;flex-wrap:wrap;justify-content:center;
    padding:11px 14px;background:rgba(253,249,247,.93);backdrop-filter:blur(12px);
    border-bottom:1px solid var(--line)}
nav a{flex:0 0 auto;text-decoration:none;color:var(--dim);background:#fff;
      border:1px solid var(--line);border-radius:14px;padding:6px 14px;line-height:1.2;
      display:flex;flex-direction:column;align-items:center;transition:.15s;min-width:56px}
nav a b{color:var(--fg);font-size:14px;font-weight:700}
nav a span{font-size:10px;opacity:.7;letter-spacing:.02em}
nav a:hover{border-color:var(--accent);background:var(--soft)}
nav a.cur{background:var(--accent);border-color:var(--accent);box-shadow:var(--sh)}
nav a.cur b,nav a.cur span{color:#fff;opacity:1}
nav a.warn b{color:var(--warn)}

/* 월 구분선 */
.monthsep{display:flex;align-items:baseline;gap:12px;flex-wrap:wrap;
  margin:20px 4px 2px;padding-bottom:9px;border-bottom:2px solid var(--soft);scroll-margin-top:72px}
.monthsep:first-child{margin-top:0}
.monthsep h3{margin:0;font-size:23px;letter-spacing:-.03em;color:#5a4a45;font-weight:700}
.monthsep span{font-size:12px;color:var(--dim)}

/* 날짜 카드를 사진 수에 맞춰 1~3칸씩 차지하게 깔아, 오른쪽 여백을 없앤다 */
main{max-width:1320px;margin:0 auto;padding:26px 16px 90px}
.monthgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(340px,1fr));
     gap:16px;align-items:start;grid-auto-flow:row dense;margin-bottom:8px}

/* ---------- 날짜 카드 ---------- */
.day{grid-column:span min(var(--span,1),3);
     background:var(--card);border:1px solid var(--line);border-radius:var(--r);
     padding:18px;scroll-margin-top:66px;box-shadow:var(--sh);
     display:flex;flex-direction:column}
.day.needs{border-color:#f0dcbb;background:#fffdf8}
.day header{border:0;padding:0;text-align:left}
.day h2{margin:0;font-size:20px;letter-spacing:-.02em;color:#493e3a}
.day .meta{display:flex;flex-wrap:wrap;gap:7px;margin-top:8px;font-size:12px;color:var(--dim)}
.day .meta span{background:#faf5f3;border:1px solid var(--line);border-radius:999px;padding:3px 10px}
.day .meta .age{color:var(--accent-ink);background:var(--soft);border-color:#f6dbe3;font-weight:600}
.day .meta .place em{font-style:normal;opacity:.6;font-size:10px;margin-left:3px}
.dayplace{min-width:120px;outline:0;border-style:dashed !important;color:var(--fg)}
.dayplace:empty::before{content:attr(data-ph);opacity:.5}
body:not(.edit) .editonly{display:none !important}
.note{margin:12px 0 0;color:#7d6f6a;font-size:13px;border-left:3px solid var(--accent);
      padding-left:11px;min-height:0}
.note:empty{display:none}
body.edit .note{display:block;min-height:22px;outline:0}
body.edit .note:empty::before{content:"이 날의 메모…";opacity:.45}

/* ---------- 사진 격자 ---------- */
.grid{flex:1 1 auto;min-height:0;display:grid;gap:9px;margin-top:14px;
  grid-template-columns:repeat(var(--cols,3),1fr);align-items:start}
/* 마지막 줄에 한 칸만 남으면 남은 폭을 채운다 */
/* 가로 사진은 두 칸 폭 → 세로 사진끼리는 양옆으로, 가로 사진은 위아래로 놓인다 */
.grid .shot.ls{grid-column:span 2}
.grid .shot:last-child{grid-column-end:-1}
.shot{margin:0;position:relative;cursor:zoom-in;border-radius:14px;overflow:hidden;
  background:#f6efec;box-shadow:var(--sh);transition:.2s;display:flex;flex-direction:column}
.shot:hover{box-shadow:var(--sh-lg);transform:translateY(-2px)}
/* 사진은 원래 비율 그대로 — 잘리지 않는다 */
.shot img{width:100%;height:auto;display:block;transition:transform .3s;background:#f7f1ee}
.shot:hover img{transform:scale(1.03)}
.shot figcaption{position:absolute;inset:auto 0 0 0;padding:20px 9px 8px;font-size:11px;
  line-height:1.4;color:#fff;background:linear-gradient(transparent,rgba(60,40,35,.82));
  opacity:0;transition:opacity .2s}
.shot:hover figcaption{opacity:1}
.shot figcaption i{opacity:.7}
/* 편집 모드: 캡션이 사진 아래 입력칸처럼 펼쳐져 바로 고칠 수 있다 */
body.edit .shot img{flex:1 1 auto}
body.edit .shot figcaption{position:static;opacity:1;background:#fffdfc;color:var(--fg);
  padding:8px 9px;font-size:12px;line-height:1.45;border-top:1px solid var(--line);
  outline:0;cursor:text;min-height:20px}
body.edit .shot figcaption:focus{background:#fff;box-shadow:inset 0 0 0 2px var(--soft)}
body.edit .shot figcaption i{opacity:.45}
body.edit .shot{cursor:default}
body.edit .shot img{cursor:zoom-in}
.shot .play{position:absolute;top:50%;left:50%;transform:translate(-50%,-50%);font-size:20px;
  color:#fff;text-shadow:0 2px 10px rgba(0,0,0,.5);pointer-events:none}
.shot .dur,.shot .src,.shot .livebadge{position:absolute;top:7px;
  background:rgba(255,255,255,.92);color:#6b5c57;border-radius:999px;padding:2px 7px;font-size:10px;
  box-shadow:0 1px 4px rgba(0,0,0,.12)}
.shot .dur{right:7px}
.shot .src{left:7px;opacity:0;transition:opacity .2s}
.shot:hover .src{opacity:1}
.shot .livebadge{right:7px;color:var(--accent-ink);font-weight:600;letter-spacing:.03em}
.shot.live:hover .livebadge{background:var(--accent);color:#fff}
.shot video.preview{position:absolute;inset:0;width:100%;height:100%;object-fit:cover}
body.edit .shot.nosum{outline:2px dashed var(--warn);outline-offset:-2px}
.rev{margin:12px 0 0;padding-left:18px;color:var(--dim);font-size:13px}
.rev code{color:var(--fg)}

/* ---------- 크게 보기 ---------- */
#help{position:fixed;inset:0;z-index:60;background:rgba(60,45,40,.35);backdrop-filter:blur(6px);
  display:none;align-items:center;justify-content:center;padding:20px}
#help.on{display:flex}
#help .panel{position:relative;max-width:620px;max-height:86vh;overflow:auto;background:var(--card);
  border:1px solid var(--line);border-radius:var(--r);padding:30px 32px;box-shadow:var(--sh-lg)}
#help h3{margin:0 0 18px;font-size:22px;color:#493e3a;letter-spacing:-.02em}
#help dt{font-weight:700;color:var(--accent-ink);margin-top:18px;font-size:15px}
#help dd{margin:6px 0 0;color:#6b5c57;font-size:14px;line-height:1.7}
#help code{background:var(--soft);border-radius:5px;padding:1px 6px;font-size:13px;color:var(--accent-ink)}
#help .x{position:absolute;top:12px;right:16px;background:none;border:0;font-size:28px;
  color:var(--dim);cursor:pointer;line-height:1}
#lb{position:fixed;inset:0;z-index:50;background:rgba(252,247,245,.93);
  backdrop-filter:blur(10px);display:none;padding:18px;overflow:hidden}
#lb.on{display:flex;align-items:center;justify-content:center;gap:22px}
/* 크게 볼 때도 배경에 랜덤 사진이 은은하게 깔린다 */
#lb .wash{position:absolute;inset:-4%;z-index:0;background-size:cover;background-position:center;
  opacity:.07;filter:blur(14px) saturate(.7);pointer-events:none;transition:opacity 1.2s}
#lb .stage{flex:1 1 auto;display:flex;align-items:center;justify-content:center;
  max-height:92vh;position:relative;z-index:1}
#lb img,#lb video{max-width:100%;max-height:88vh;border-radius:14px;object-fit:contain;
  box-shadow:var(--sh-lg)}
#lb .livetoggle{position:absolute;left:12px;bottom:12px;background:rgba(255,255,255,.94);
  border:1px solid var(--line);color:var(--fg);border-radius:999px;padding:6px 13px;
  font-size:12px;cursor:pointer;font-family:inherit;box-shadow:var(--sh)}
#lb .livetoggle.on{background:var(--accent);color:#fff;border-color:var(--accent);font-weight:600}
#lb aside{position:relative;z-index:1;flex:0 0 430px;max-height:88vh;overflow:auto;background:var(--card);
  border:1px solid var(--line);border-radius:var(--r);padding:26px;box-shadow:var(--sh-lg);
  align-self:center}
#lb aside h4{margin:0 0 6px;font-size:25px;color:#493e3a;letter-spacing:-.03em;font-weight:700}
#lb aside .sub{color:var(--dim);font-size:12px;word-break:break-all;margin-bottom:4px;line-height:1.55}
#lb label{display:block;font-size:14px;color:var(--accent-ink);margin:20px 0 7px;font-weight:700;
  letter-spacing:-.01em}
#lb textarea,#lb input{width:100%;background:#fdfaf9;border:1px solid var(--line);color:var(--fg);
  border-radius:13px;padding:13px 15px;font:19px/1.55 inherit;resize:vertical}
#lb textarea:focus,#lb input:focus{outline:0;border-color:var(--accent);background:#fff;
  box-shadow:0 0 0 3px var(--soft)}
/* 기본은 읽기 전용 — [✎ 수정]을 눌러야 고칠 수 있다 */
#lb textarea[readonly],#lb input[readonly]{background:transparent;border-color:#f7f0ed;
  cursor:pointer;resize:none;box-shadow:none}
#lb textarea[readonly]:hover,#lb input[readonly]:hover{border-color:var(--accent);background:#fffdfc}
#lb .hint{font-size:13px;color:var(--dim);margin-top:7px;line-height:1.55}
/* 수정 중에만 보이는 것 / 볼 때만 보이는 것 */
#lb .onlyedit{display:none}
#lb.editing .onlyedit{display:block}
#lb.editing .onlyview{display:none}
/* 아직 저장하지 않은 변경이 있다 — 눈에 띄게 */
#lb .unsaved{display:none;align-items:center;gap:8px;margin-top:18px;padding:11px 14px;
  border-radius:13px;background:#fff8ec;border:1px solid #f0dcbb;color:#8a6a30;font-size:13px;
  line-height:1.5}
#lb.dirty .unsaved{display:flex}
#lb .changed{border-color:var(--warn) !important;background:#fffdf7}
#lb.dirty .row #saveBtn{animation:pulse 1.7s ease-in-out infinite}
@keyframes pulse{0%,100%{box-shadow:0 0 0 0 rgba(217,149,60,.5)}50%{box-shadow:0 0 0 8px rgba(217,149,60,0)}}
@media(prefers-reduced-motion:reduce){#lb.dirty .row #saveBtn{animation:none}}
#lb .row button[disabled]{opacity:.45;cursor:default}
#lb .row button[disabled]:hover{border-color:var(--line)}
#lb .row button.primary[disabled]:hover{border-color:var(--accent)}
#lb .rel{display:grid;grid-template-columns:repeat(4,1fr);gap:7px}
#lb .rel img{width:100%;aspect-ratio:1;object-fit:cover;border-radius:9px;cursor:pointer;
  border:2px solid transparent;transition:.15s;background:#f6efec}
#lb .rel img:hover{border-color:var(--accent);transform:translateY(-2px)}
#lb .rel .day{grid-column:1/-1;font-size:11px;color:var(--dim);margin:2px 0 -2px}
#lb .row{display:flex;gap:9px;margin-top:22px}
#lb .row button{flex:1;border-radius:13px;padding:14px;border:1px solid var(--line);
  background:#fff;color:var(--fg);cursor:pointer;font:16px inherit;font-weight:600}
#lb .row button:hover{border-color:var(--accent)}
#lb .row button.primary{background:var(--accent);color:#fff;border-color:var(--accent);font-weight:600}
#lb .close{position:absolute;top:14px;right:18px;background:none;border:0;color:#8d7d77;
  font-size:32px;cursor:pointer;z-index:2;line-height:1}
/* 좌우 이동: 보이는 건 동그란 버튼이지만 클릭 영역은 세로 전체 기둥 */
#lb .arrow{position:absolute;top:0;bottom:0;width:96px;transform:none;padding:0;
  background:transparent;border:0;cursor:pointer;z-index:8;font-size:0;
  display:flex;align-items:center;justify-content:center;-webkit-tap-highlight-color:transparent}
#lb .arrow::before{display:flex;align-items:center;justify-content:center;
  width:58px;height:58px;border-radius:50%;background:#fff;
  border:1px solid #ecd9d2;box-shadow:0 4px 18px rgba(140,100,90,.28);
  color:var(--accent-ink);font-size:32px;line-height:1;padding-bottom:5px;transition:.15s}
#lb .prev::before{content:"\2039"}
#lb .next::before{content:"\203A"}
#lb .arrow:hover::before{background:var(--accent);color:#fff;border-color:var(--accent);
  transform:scale(1.08)}
#lb .arrow:active::before{transform:scale(.96)}
#lb .prev{left:0}#lb .next{right:456px}
#lb .livetoggle{z-index:9}
#lb .close{z-index:9}

@media(max-width:860px){#lb.on{flex-direction:column;overflow:auto}
  #lb aside{flex:1 1 auto;width:100%;max-height:none}
  /* 세로 배치에서는 기둥이 입력폼을 덮지 않도록 사진 영역까지만 */
  #lb .arrow{top:0;bottom:auto;height:52vh;width:76px}
  #lb .prev{left:0}#lb .next{right:0}
  #lb img,#lb video{max-height:46vh}}
@media(max-width:560px){.grid{grid-template-columns:repeat(auto-fill,minmax(112px,1fr));gap:8px}
  .shot figcaption{opacity:1;font-size:10px}
  .hero{min-height:44vh;padding-top:36px}}
</style></head><body>
<div id="bgwash"><i></i><i></i></div>
<header class="top">
  <div class="hero">
    <div class="bg" style="background-image:url('{{HERO}}')"></div>
    <div class="veil"></div>
    <div class="inner">
      <h1>{{TITLE}}</h1>
      <p class="sub">{{SPAN}} · <b>{{DAYS}}일</b> · <b>{{TOTAL}}컷</b></p>
    </div>
  </div>
  <div class="tools">
    <button id="editBtn" title="목록에서 사진 아래 설명을 바로 고칩니다">✎ 격자에서 바로 수정</button>
    <button id="nextBtn" title="설명이 비어 있는 다음 사진으로 건너뜁니다">다음 미작성 →</button>
    <button id="rebuildBtn" title="바뀐 내용으로 이 페이지와 LOG.md 를 다시 만듭니다">↻ 다시 빌드</button>
    <button id="organizeBtn" title="staging 폴더의 새 사진을 날짜·장소별로 정리합니다">📂 새 사진 정리</button>
    <button id="exportBtn" title="서버 없이 열었을 때 브라우저에 쌓인 수정본을 파일로 내려받습니다">⇩ 수정본 내보내기</button>
    <button id="helpBtn" title="각 버튼 설명">? 도움말</button>
  </div>
  <div class="search">
    <input id="q" type="search" placeholder="무엇이든 검색 — 벚꽃, 물놀이, 첫 미용실, 할머니…"
           autocomplete="off">
    <button id="qClear" title="지우기">&times;</button>
  </div>
  <div id="status"></div>
</header>
<nav>{{NAV}}</nav>
<main>{{CARDS}}</main>

<div id="help"><div class="panel">
  <button class="x">&times;</button>
  <h3>이 버튼들이 하는 일</h3>
  <dl>
    <dt>✎ 격자에서 바로 수정</dt>
    <dd>목록에서 사진 아래 설명이 입력칸으로 펼쳐집니다. 바로 고치고 다른 곳을 클릭하면 저장됩니다.
        날짜 카드의 메모와 '이 날 장소 일괄 지정'도 이때 나타납니다.</dd>
    <dt>다음 미작성 →</dt>
    <dd>설명이 아직 비어 있는 사진만 골라 차례로 열어줍니다. 빈 곳을 채울 때 씁니다.</dd>
    <dt>↻ 다시 빌드</dt>
    <dd>지금까지 고친 내용으로 <b>이 페이지(index.html)와 LOG.md 를 다시 만듭니다.</b>
        설명만 고친 거라면 자동으로 반영되니 누를 일이 거의 없고,
        <b>장소·날짜를 바꿔서 사진이 다른 날짜·장소로 묶여야 할 때</b> 누르면 됩니다.</dd>
    <dt>📂 새 사진 정리</dt>
    <dd><code>staging/</code> 폴더에 새로 넣은 사진·영상을 한 번에 처리합니다:
        이미 있는 사진이면 걸러내고 → 촬영일시·GPS를 읽어 → 지명을 붙이고 →
        <code>organized/날짜__장소/</code> 로 옮기고 → 썸네일을 만들고 → 페이지를 다시 만듭니다.
        사진이 많으면 몇 분 걸립니다.</dd>
    <dt>⇩ 수정본 내보내기</dt>
    <dd>서버 없이 파일을 직접 열었을 때(<code>file://</code>)는 고친 내용이 파일에 못 들어가고
        브라우저에만 쌓입니다. 그걸 <code>pending_edits.json</code> 으로 내려받는 버튼입니다.
        받은 파일을 <code>data/</code> 에 넣고 <code>jiho.py merge</code> 를 실행하면 반영됩니다.
        <b>서버로 열었다면 저장이 곧바로 파일에 들어가므로 쓸 일이 없습니다.</b></dd>
    <dt>사진 크게 보기 → ✎ 수정</dt>
    <dd>사진을 크게 열면 요약·촬영 일시·장소는 <b>읽기 전용</b>입니다.
        <b>✎ 수정</b>을 누르면(또는 그 칸을 그냥 눌러도) 입력칸이 열리고 <b>저장</b> 버튼이 나타납니다.
        고친 곳은 노란 테두리로 표시되고 "아직 저장하지 않은 변경이 있습니다" 알림이 뜹니다.
        저장하지 않은 채 다른 사진으로 넘어가거나 닫으면 한 번 더 물어봅니다.
        <code>Ctrl(⌘)+Enter</code> 로도 저장할 수 있습니다.</dd>
    <dt>사진 크게 보기 → 장소 일괄</dt>
    <dd>그 사진의 <b>GPS 좌표가 같은 사진 전부</b>의 장소 이름을 한 번에 바꿉니다.
        예를 들어 자동으로 "서울 마포구 아현동"이라고 붙은 곳을 "우리 집"으로 바꾸면,
        같은 좌표에서 찍힌 사진이 모두 "우리 집"이 됩니다.
        GPS가 없는 사진에는 쓸 수 없고, 그럴 땐 날짜 카드의 '이 날 장소 일괄 지정'을 쓰세요.
        (옆의 <b>저장</b>은 지금 보고 있는 사진 하나만 바꿉니다.)</dd>
    <dt>검색창</dt>
    <dd>사진 설명·장소·날짜를 대상으로 찾습니다. 정확한 단어가 아니어도 비슷한 말이면 걸립니다
        (예: <code>물놀이</code> → 튜브 탄 컷, <code>꽃</code> → 벚꽃·유채꽃).</dd>
  </dl>
</div></div>
<div id="lb">
  <div class="wash"></div>
  <button class="close">&times;</button>
  <button class="arrow prev">&#8249;</button><button class="arrow next">&#8250;</button>
  <div class="stage"></div>
  <aside>
    <h4 id="lbTitle"></h4><div class="sub" id="lbSub"></div>
    <label>요약</label>
    <textarea id="fSum" rows="4" placeholder="이 순간을 한 줄로…" readonly></textarea>
    <label>촬영 일시</label>
    <input id="fDate" placeholder="2026-06-13 09:03" readonly>
    <div class="hint" id="dHint"></div>
    <label>장소</label>
    <input id="fPlace" placeholder="예: 서울 마포구 상암동" readonly>
    <div class="hint" id="pHint"></div>
    <div class="unsaved">✎ 아직 저장하지 않은 변경이 있습니다 — <b>[저장]</b>을 눌러야 반영됩니다</div>
    <div class="row">
      <button class="onlyview" id="editFieldsBtn" title="요약·촬영 일시·장소를 고칩니다">✎ 수정</button>
      <button class="primary onlyedit" id="saveBtn" disabled>저장</button>
      <button class="onlyedit" id="cancelBtn">취소</button>
      <button class="onlyedit" id="savePlaceBtn" title="같은 좌표의 사진 전부에 적용">장소 일괄</button>
    </div>
    <label id="relLabel">이 무렵 사진</label>
    <div class="rel" id="fRel"></div>
  </aside>
</div>

<script>
const $=s=>document.querySelector(s), shots=[...document.querySelectorAll('.shot')];
const VECS={{VECS}}, IDF={{IDF}};   // 요약문 TF-IDF (빌드 때 계산)

// 질의어 → 벡터 (글자 2-gram + 단어)
function qvec(q){
  q=q.trim(); if(!q) return null;
  const toks=q.split(/[\s,·—\-()]+/).filter(w=>w.length>1);
  const grams=[]; for(let i=0;i<q.length-1;i++){const g=q.slice(i,i+2); if(!/\s/.test(g)) grams.push(g);}
  const v={}; let norm=0;
  for(const tk of toks.concat(grams)){ const w=IDF[tk]; if(!w) continue; v[tk]=(v[tk]||0)+w; }
  for(const k in v) norm+=v[k]*v[k];
  norm=Math.sqrt(norm)||1;
  for(const k in v) v[k]/=norm;
  return Object.keys(v).length?v:null;
}
function cos(a,b){ let s=0; const [x,y]=Object.keys(a).length<Object.keys(b).length?[a,b]:[b,a];
  for(const k in x){ if(y[k]) s+=x[k]*y[k]; } return s; }

// 배경 워시: 사진 썸네일 중 무작위로 골라 아주 연하게, 15초마다 교차 전환
(function(){
  const wash=document.getElementById('bgwash'); if(!wash) return;
  const layers=[...wash.querySelectorAll('i')];
  const pool=shots.map(s=>s.querySelector('img')?.getAttribute('src')).filter(Boolean);
  if(!pool.length) return;
  for(let i=pool.length-1;i>0;i--){const j=Math.floor(Math.random()*(i+1));[pool[i],pool[j]]=[pool[j],pool[i]];}
  let n=0, front=0;
  function step(){
    const back=1-front, src=pool[n++%pool.length];
    const img=new Image();
    img.onload=()=>{
      layers[back].style.backgroundImage=`url("${src}")`;
      layers[back].classList.add('on'); layers[front].classList.remove('on');
      front=back;
      const lw=document.querySelector('#lb .wash');
      if(lw) lw.style.backgroundImage=`url("${src}")`;
    };
    img.src=src;
  }
  step(); setInterval(step, 15000);
})();
const lb=$('#lb'), stage=lb.querySelector('.stage'), st=$('#status');
let cur=0, live=true, pending=JSON.parse(localStorage.getItem('jiho.pending')||'{}');

function say(msg,kind=''){st.textContent=msg;st.className=kind;
  if(msg)setTimeout(()=>{if(st.textContent===msg){st.textContent='';st.className=''}},3500);}

async function api(path,body){
  if(!live) throw new Error('offline');
  const r=await fetch(path,{method:'POST',headers:{'Content-Type':'application/json'},
                            body:JSON.stringify(body)});
  const j=await r.json();
  if(!j.ok) throw new Error(j.error||'저장 실패');
  return j;
}
// file:// 로 열었는지 확인 → 오프라인이면 로컬 저장 후 내보내기
fetch('/api/item',{method:'POST',headers:{'Content-Type':'application/json'},
                   body:JSON.stringify({})}).then(r=>r.json()).catch(()=>{
  live=false; say('서버 없이 열렸습니다 — 수정은 브라우저에 저장되고 [수정본 내보내기]로 반영합니다','err');
});

function stash(file,patch){
  pending[file]=Object.assign(pending[file]||{},patch);
  localStorage.setItem('jiho.pending',JSON.stringify(pending));
}

let liveOn=true;   // 모션 포토를 열었을 때 기본으로 움직이게
function render(){
  const d=shots[cur].dataset;
  if(d.kind==='video'){
    stage.innerHTML=`<video src="${d.path}" controls autoplay playsinline></video>`;
  }else if(d.motion && liveOn){
    stage.innerHTML=`<video src="${d.motion}" autoplay loop muted playsinline></video>`
      +`<button class="livetoggle on" title="정지 사진으로">◉ LIVE</button>`;
  }else{
    stage.innerHTML=`<img src="${d.path}">`
      +(d.motion?`<button class="livetoggle" title="움직이는 사진으로">◉ LIVE</button>`:'');
  }
  const t=stage.querySelector('.livetoggle');
  if(t) t.onclick=e=>{e.stopPropagation();liveOn=!liveOn;render();};
}
// ── 읽기 전용 ↔ 수정 상태 ──────────────────────────────
// 라이트박스는 열자마자 읽기 전용이다. [✎ 수정]을 눌러야 입력칸이 열리고
// 저장 버튼이 나타난다. 값이 바뀌면 그 사실이 눈에 보이게 표시된다.
const FIELDS=['#fSum','#fDate','#fPlace'];
let base={sum:'',date:'',place:''};
const vals=()=>({sum:$('#fSum').value,date:$('#fDate').value,place:$('#fPlace').value});
const isDirty=()=>lb.classList.contains('dirty');

function markDirty(){
  const v=vals(), chg=[v.sum!==base.sum,v.date!==base.date,v.place!==base.place];
  FIELDS.forEach((sel,k)=>$(sel).classList.toggle('changed',chg[k]));
  const any=chg.some(Boolean);
  lb.classList.toggle('dirty',any);
  $('#saveBtn').disabled=!any;
  return any;
}
function setEditing(on){
  lb.classList.toggle('editing',on);
  FIELDS.forEach(sel=>$(sel).readOnly=!on);
  if(!on){ FIELDS.forEach(sel=>$(sel).classList.remove('changed'));
           lb.classList.remove('dirty'); $('#saveBtn').disabled=true; }
}
function fillFields(){          // 지금 사진의 값으로 되돌리고 기준선을 새로 잡는다
  const d=shots[cur].dataset;
  $('#fSum').value=d.cap||''; $('#fDate').value=d.taken||''; $('#fPlace').value=d.place||'';
  base=vals(); markDirty();
}
// 저장하지 않은 변경이 있으면 다른 사진으로 넘어가거나 닫기 전에 묻는다
async function leaveGuard(){
  if(!isDirty()) return true;
  if(confirm('저장하지 않은 변경이 있습니다.\n\n확인 = 저장하고 이동\n취소 = 변경을 버리고 이동'))
    return await save();
  return true;
}
async function go(i){ if(await leaveGuard()) show(i); }

function show(i){
  cur=(i+shots.length)%shots.length; const s=shots[cur], d=s.dataset;
  render();
  setEditing(false);
  $('#lbTitle').textContent = d.taken || '(촬영 일시 없음)';
  $('#lbSub').textContent = `${d.file} · ${d.path}`;
  fillFields();
  $('#dHint').textContent = d.dsrc ? `출처: ${d.dsrc}` : '메타데이터에 촬영 일시가 없습니다';
  renderRelated(cur);
  const psrc={manual:'직접 입력',gps:'사진 GPS','manual-day':'그 날짜 지정',
              inferred:'같은 날 다른 사진의 GPS로 추정'}[d.psrc]||'미지정';
  $('#pHint').textContent = (d.geokey
    ? `GPS ${d.geokey}${d.auto?` · 자동판정 "${d.auto}"`:''}`
    : 'GPS 정보 없음') + ` · 현재 출처: ${psrc}`;
  lb.classList.add('on');
}
async function close(){
  if(!await leaveGuard()) return;
  setEditing(false); lb.classList.remove('on'); stage.innerHTML='';
}

// 비슷한 사진: 요약문 의미 유사도 우선, 부족하면 같은 날 컷으로 채운다
const REL_COUNT=8;
function renderRelated(i){
  const box=$('#fRel'); if(!box) return;
  const me=VECS[i]||{}, day=(shots[i].dataset.taken||'').slice(0,10);
  const scored=shots.map((s,k)=>({s,k,sc:k===i?-1:cos(me,VECS[k]||{})}))
                    .filter(o=>o.sc>0.05).sort((a,b)=>b.sc-a.sc);
  let pick=scored.slice(0,REL_COUNT);
  if(pick.length<REL_COUNT){
    const have=new Set(pick.map(o=>o.k).concat([i]));
    const near=shots.map((s,k)=>({s,k,sc:0})).filter(o=>!have.has(o.k))
      .sort((a,b)=>{
        const da=(a.s.dataset.taken||'').slice(0,10)===day?0:1;
        const db=(b.s.dataset.taken||'').slice(0,10)===day?0:1;
        return da-db || Math.abs(a.k-i)-Math.abs(b.k-i);
      });
    pick=pick.concat(near.slice(0,REL_COUNT-pick.length));
  }
  box.innerHTML=pick.map(o=>{
    const src=o.s.querySelector('img')?.getAttribute('src')||'';
    const cap=(o.s.dataset.cap||'').replace(/"/g,'&quot;');
    return `<img src="${src}" data-i="${o.k}" title="${o.s.dataset.taken} · ${cap}" loading="lazy">`;
  }).join('');
  box.querySelectorAll('img').forEach(im=>im.onclick=()=>go(+im.dataset.i));
  $('#relLabel').textContent = scored.length ? '비슷한 사진' : '이 무렵 사진';
}

// 의미 검색: 요약·장소·메모를 대상으로 점수순 필터
(function(){
  const box=document.querySelector('.search'), input=$('#q');
  if(!input) return;
  const days=[...document.querySelectorAll('.day')];
  function run(){
    const q=input.value.trim();
    box.classList.toggle('has',!!q);
    if(!q){
      document.body.classList.remove('searching');
      shots.forEach(s=>s.classList.remove('hide'));
      days.forEach(d=>d.classList.remove('hide'));
      say('');
      return;
    }
    document.body.classList.add('searching');
    const v=qvec(q), lower=q.toLowerCase();
    let hits=0;
    shots.forEach((s,k)=>{
      const hay=((s.dataset.cap||'')+' '+(s.dataset.place||'')+' '+(s.dataset.taken||'')).toLowerCase();
      const sub=hay.includes(lower);
      const sim=v?cos(v,VECS[k]||{}):0;
      const ok=sub||sim>0.12;
      s.classList.toggle('hide',!ok);
      if(ok) hits++;
    });
    days.forEach(d=>d.classList.toggle('hide',
      !d.querySelector('.shot:not(.hide)')));
    say(hits?`"${q}" — ${hits}장`:`"${q}" — 결과 없음`, hits?'ok':'err');
  }
  let tm; input.addEventListener('input',()=>{clearTimeout(tm);tm=setTimeout(run,140);});
  input.addEventListener('keydown',e=>{if(e.key==='Escape'){input.value='';run();}});
  $('#qClear').onclick=()=>{input.value='';run();input.focus();};
})();

async function save(){
  const s=shots[cur], d=s.dataset;
  const patch={file:d.file, summary:$('#fSum').value, taken_local:$('#fDate').value,
               place:$('#fPlace').value};
  try{
    if(live){ const j=await api('/api/item',patch); say('저장했습니다 · 파일에도 자동 반영됩니다','ok'); }
    else { stash(d.file,patch); say('브라우저에 저장했습니다 (내보내기 필요)','ok'); }
    d.cap=patch.summary; d.taken=patch.taken_local; d.place=patch.place;
    s.querySelector('figcaption').innerHTML = patch.summary
      ? patch.summary.replace(/[<>&]/g,c=>({'<':'&lt;','>':'&gt;','&':'&amp;'}[c])) : '<i>요약 없음</i>';
    s.classList.toggle('nosum',!patch.summary);
    $('#lbTitle').textContent = patch.taken_local || '(촬영 일시 없음)';
    base=vals(); setEditing(false);      // 저장했으니 다시 읽기 전용으로
    return true;
  }catch(e){ say('저장 실패: '+e.message,'err'); return false; }
}

$('#editFieldsBtn').onclick=()=>{ setEditing(true); $('#fSum').focus(); };
function cancelEdit(){
  const had=isDirty();
  if(had && !confirm('고친 내용을 버리고 원래대로 되돌릴까요?')) return false;
  fillFields(); setEditing(false);
  if(had) say('변경을 되돌렸습니다');
  return true;
}
$('#cancelBtn').onclick=cancelEdit;
$('#saveBtn').onclick=save;
// 읽기 전용 칸을 그냥 눌러도 수정이 시작된다
FIELDS.forEach(sel=>{
  const el=$(sel);
  el.addEventListener('input',markDirty);
  el.addEventListener('mousedown',e=>{
    if(!el.readOnly) return;
    e.preventDefault(); setEditing(true); el.focus();
  });
});
$('#savePlaceBtn').onclick=async()=>{
  const d=shots[cur].dataset, label=$('#fPlace').value.trim();
  if(!d.geokey) return say('GPS 좌표가 없어 일괄 적용할 수 없습니다','err');
  try{ await api('/api/place',{geo_key:d.geokey,label});
       d.place=label; base.place=label; markDirty();
       say(`좌표 ${d.geokey} 의 모든 사진 장소를 "${label}" 로 바꿨습니다`,'ok'); }
  catch(e){ say('실패: '+e.message,'err'); }
};
shots.forEach((s,i)=>s.addEventListener('click',e=>{
  // 편집 모드에서 캡션을 누른 경우엔 라이트박스를 열지 않는다
  if(document.body.classList.contains('edit') && e.target.closest('figcaption')) return;
  show(i);
}));

// 격자 캡션 인라인 편집
shots.forEach(s=>{
  const cap=s.querySelector('figcaption');
  cap.contentEditable='true';
  cap.addEventListener('focus',()=>{ if(!s.dataset.cap) cap.textContent=''; });
  cap.addEventListener('keydown',e=>{
    if(e.key==='Enter'){e.preventDefault();cap.blur();}
    if(e.key==='Escape'){cap.textContent=s.dataset.cap||'';cap.blur();}
  });
  cap.addEventListener('blur',async()=>{
    const text=cap.textContent.trim();
    if(text===(s.dataset.cap||'')){ if(!text) cap.innerHTML='<i>요약 없음</i>'; return; }
    try{
      if(live) await api('/api/item',{file:s.dataset.file,summary:text});
      else stash(s.dataset.file,{summary:text});
      s.dataset.cap=text; s.classList.toggle('nosum',!text);
      if(!text) cap.innerHTML='<i>요약 없음</i>';
      say('요약 저장','ok');
    }catch(e){ say('저장 실패: '+e.message,'err'); cap.textContent=s.dataset.cap||''; }
  });
});
// 모션 포토는 썸네일에 마우스를 올리면 그 자리에서 살짝 움직인다 (그때 처음 불러온다)
shots.filter(s=>s.dataset.motion).forEach(s=>{
  let v=null;
  s.addEventListener('mouseenter',()=>{
    if(v){v.play().catch(()=>{});return;}
    v=document.createElement('video');
    Object.assign(v,{src:s.dataset.motion,autoplay:true,loop:true,muted:true,playsInline:true});
    v.className='preview'; s.appendChild(v);
  });
  s.addEventListener('mouseleave',()=>{if(v)v.pause();});
});
lb.querySelector('.close').onclick=close;
lb.querySelector('.prev').onclick=e=>{e.stopPropagation();go(cur-1)};
lb.querySelector('.next').onclick=e=>{e.stopPropagation();go(cur+1)};
lb.addEventListener('click',e=>{if(e.target===lb)close()});
document.addEventListener('keydown',e=>{
  if(!lb.classList.contains('on'))return;
  const typing=/INPUT|TEXTAREA/.test(document.activeElement.tagName);
  // 수정 중이면 Esc 는 먼저 수정을 접는다 — 한 번 더 눌러야 닫힌다
  if(e.key==='Escape'){ if(lb.classList.contains('editing')) cancelEdit(); else close(); return; }
  if((e.metaKey||e.ctrlKey)&&e.key==='Enter'){e.preventDefault();
    if(lb.classList.contains('editing')) save(); else $('#editFieldsBtn').click();}
  if(typing)return;
  if(e.key==='ArrowLeft')go(cur-1); if(e.key==='ArrowRight')go(cur+1);
});
// 저장 안 한 채로 창을 닫거나 새로고침하면 브라우저가 한 번 더 묻는다
window.addEventListener('beforeunload',e=>{ if(isDirty()){e.preventDefault();e.returnValue='';} });

// 스크롤 위치에 따라 현재 달을 네비에서 강조
(function(){
  const links=new Map([...document.querySelectorAll('nav a[data-month]')].map(a=>[a.dataset.month,a]));
  const seps=[...document.querySelectorAll('.monthsep,#review')];
  if(!seps.length) return;
  const mark=m=>{links.forEach(a=>a.classList.remove('cur'));
                 const a=links.get(m); if(a){a.classList.add('cur');
                   a.scrollIntoView({block:'nearest',inline:'nearest'});}};
  const io=new IntersectionObserver(es=>{
    const vis=es.filter(e=>e.isIntersecting)
                .sort((a,b)=>a.boundingClientRect.top-b.boundingClientRect.top);
    if(vis.length) mark(vis[0].target.dataset.month||'review');
  },{rootMargin:'-64px 0px -70% 0px',threshold:0});
  seps.forEach(s=>io.observe(s));
})();

const help=$('#help');
$('#helpBtn').onclick=()=>help.classList.add('on');
help.querySelector('.x').onclick=()=>help.classList.remove('on');
help.addEventListener('click',e=>{if(e.target===help)help.classList.remove('on')});
document.addEventListener('keydown',e=>{if(e.key==='Escape')help.classList.remove('on')});

$('#editBtn').onclick=e=>{document.body.classList.toggle('edit');
  e.target.classList.toggle('on',document.body.classList.contains('edit'));};
$('#nextBtn').onclick=async()=>{
  const i=shots.findIndex((s,k)=>k>cur&&s.classList.contains('nosum'));
  const j=i>=0?i:shots.findIndex(s=>s.classList.contains('nosum'));
  if(j<0)return say('요약이 비어 있는 항목이 없습니다','ok');
  if(!await leaveGuard())return;
  document.body.classList.add('edit'); $('#editBtn').classList.add('on');
  show(j); setEditing(true); setTimeout(()=>$('#fSum').focus(),60);
};
$('#rebuildBtn').onclick=async()=>{ say('다시 빌드 중…');
  try{ await api('/api/rebuild',{}); location.reload(); }catch(e){ say('실패: '+e.message,'err'); } };
$('#organizeBtn').onclick=async()=>{
  if(!confirm('staging/ 의 새 파일을 정리하고 갤러리를 다시 만듭니다. 진행할까요?'))return;
  say('정리 중… (사진이 많으면 시간이 걸립니다)');
  try{ await api('/api/organize',{}); location.reload(); }catch(e){ say('실패: '+e.message,'err'); } };
$('#exportBtn').onclick=()=>{
  const blob=new Blob([JSON.stringify(pending,null,2)],{type:'application/json'});
  const a=document.createElement('a');
  a.href=URL.createObjectURL(blob); a.download='pending_edits.json'; a.click();
  say('pending_edits.json 저장 — data/ 에 넣고 `jiho.py merge` 실행');
};
// 날짜별 메모 / 날짜별 장소 인라인 편집
function inline(sel,send,label){
  document.querySelectorAll(sel).forEach(n=>{
    n.contentEditable='true'; let before=n.textContent;
    n.addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();n.blur();}});
    n.addEventListener('blur',async()=>{
      const text=n.textContent.trim(); if(text===before.trim())return; before=text;
      try{ if(live) await api(send.path,send.body(n,text)); else stash(send.key(n),{[send.field]:text});
           say(label+' 저장 · 다시 빌드하면 반영됩니다','ok'); }
      catch(e){ say(label+' 저장 실패: '+e.message,'err'); }
    });
  });
}
inline('.note',{path:'/api/note',field:'note',
  body:(n,t)=>({day:n.dataset.day,text:t}), key:n=>'__note__'+n.dataset.day},'메모');
inline('.dayplace',{path:'/api/dayplace',field:'dayplace',
  body:(n,t)=>({day:n.dataset.day,label:t}), key:n=>'__dayplace__'+n.dataset.day},'날짜 장소');
</script></body></html>
"""


if __name__ == "__main__":
    main()
