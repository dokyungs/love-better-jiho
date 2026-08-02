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

돌잔치 영상용 태그(쓸 컷 / 인물 / 얼굴 위치 / 자막 / 비공개)는 serve 로 띄운
갤러리의 [🎬 영상 태깅] 에서 모으고 data/edits.json 에 쌓인다.
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
import tempfile
import textwrap
import threading
import time
import unicodedata
import urllib.parse
import urllib.request
import zipfile
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from jihometa import IMAGE_EXT, MOTION_SUFFIX, VIDEO_EXT, extract_motion, probe  # noqa: E402

MOTION_WEB_SUFFIX = ".motion.web.mp4"

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
EDITS_JSON = DATA / "edits.json"              # 영상 제작용 태그 (선별·인물·얼굴 위치…)
CHAPTERS_JSON = DATA / "chapters.json"        # 영상 챕터 (제목·기간·목표 길이)
MUSIC_JSON = DATA / "music.json"              # 배경음악 BPM·첫 박·후렴 구간
MUSIC_LYRICS_JSON = DATA / "asr" / "o_my_baby.json"  # 음원에서 자동 추출한 가사·타이밍
PLAN_JSON = DATA / "video_plan.json"          # 계산된 컷 리스트 (자동 생성)
PLOT_LAYOUT_JSON = DATA / "plot_layout.json"  # 플롯에서 직접 합치기·분리한 화면 구성
MANIFEST = DATA / "move_manifest.jsonl"       # organize 이동 기록 (undo 용)

TZ_OFFSET = 9.0          # Asia/Seoul
GEO_PRECISION = 3        # 좌표 반올림 자리수(≈100m) → 같은 장소로 묶는 단위
IGNORE = {".DS_Store", "Thumbs.db"}
NO_PLACE = "장소 미상"

# ---- 영상 태그 --------------------------------------------------------
# 돌잔치 영상을 자동으로 만들려면 "이 사진을 쓸지 / 누가 나오는지 / 어디를
# 잘라야 얼굴이 살아남는지"가 데이터에 있어야 한다. 사진마다 한 번씩 눌러
# 모으는 값들이고, 전부 data/edits.json 한 곳에 들어간다.
PICK_LABELS = {0: "제외", 1: "보통", 2: "꼭"}
FACE_LABELS = {"s": "작게", "m": "보통", "l": "크게"}
SHORT_MAX = 40           # 화면 자막용 짧은 문구 길이 상한
# 인물 태그 기본 목록 — 지호는 거의 모든 컷에 있으니 넣지 않는다("누가 같이
# 나왔나"를 모으는 것이 목적). notes.json 의 "roster" 로 바꿀 수 있다.
DEFAULT_ROSTER = ["엄마", "아빠", "할머니", "할아버지",
                  "외할머니", "외할아버지", "이모", "삼촌", "친구"]
# 마일스톤 — 챕터 뼈대와 "처음으로…" 자막 카드의 재료
DEFAULT_MILESTONES = ["백일", "200일", "돌", "첫 뒤집기", "첫 이유식",
                      "첫 니", "첫 걸음", "첫 옹알이", "여행", "명절"]

# ---- 영상 계획 --------------------------------------------------------
DEFAULT_TARGET_SEC = 300         # 영상 전체 목표 길이 (5분)
BEATS = {2: 4, 1: 2}             # 꼭 = 4박, 보통 = 2박 동안 머문다
BEATS_CHORUS = {2: 2, 1: 1}      # 후렴에서는 절반으로 — 빠르게 몰아친다
FALLBACK_SEC = {2: 3.0, 1: 1.8}  # BPM 을 모를 때 쓰는 초 단위 길이
CLIP_MAX_SEC = 6.0               # in/out 을 안 잡은 영상에서 기본으로 쓸 길이
MOODS = ["잔잔하게", "밝게", "신나게", "뭉클하게"]

# ---- 한 화면에 몇 장을 넣을까 -----------------------------------------
# 화면(16:9)에 사진 한 장을 꽉 채우면 두 가지가 문제가 된다.
#   1) 사진이 화면보다 작으면 늘려야 하고 → 뿌옇다
#   2) 세로 사진을 가로 화면에 채우면 위아래가 크게 잘린다 (69% 손실)
# 여러 장을 나눠 넣으면 칸이 작아져 늘릴 필요가 없고, 세로 사진은 세로로 긴
# 칸에 들어가 거의 안 잘린다. 스틸컷을 여러 장 붙인 것 같은 화면이 된다.
FRAME_DEFAULT = (1920, 1080)
MAX_UPSCALE = 1.15               # 이보다 더 늘려야 하면 '해상도 부족'
KEEP_MIN = 0.45                  # 사진의 45% 미만만 남으면 '너무 잘림'
GROUP_MODES = ("auto", "fill", "off")   # 해상도 부족만 / 잘림까지 / 안 묶음
GROUP_BEATS = {2: 1.6, 3: 2.1, 4: 2.5, 5: 2.8, 6: 3.0}  # 여러 장은 읽을 시간이 더 필요하다
CELLS = {                        # 화면을 나눈 칸 (x, y, 너비, 높이 — 0~1 비율)
    "full":  [(0, 0, 1, 1)],
    "row2":  [(0, 0, .5, 1), (.5, 0, .5, 1)],
    "row3":  [(0, 0, 1 / 3, 1), (1 / 3, 0, 1 / 3, 1), (2 / 3, 0, 1 / 3, 1)],
    "col2":  [(0, 0, 1, .5), (0, .5, 1, .5)],
    "col3":  [(0, 0, 1, 1 / 3), (0, 1 / 3, 1, 1 / 3), (0, 2 / 3, 1, 1 / 3)],
    "hero_left3": [(0, 0, 2 / 3, 1), (2 / 3, 0, 1 / 3, .5), (2 / 3, .5, 1 / 3, .5)],
    "hero_right3": [(0, 0, 1 / 3, .5), (0, .5, 1 / 3, .5), (1 / 3, 0, 2 / 3, 1)],
    "grid4": [(0, 0, .5, .5), (.5, 0, .5, .5), (0, .5, .5, .5), (.5, .5, .5, .5)],
    "row4":  [(0, 0, .25, 1), (.25, 0, .25, 1), (.5, 0, .25, 1), (.75, 0, .25, 1)],
    "col4":  [(0, 0, 1, .25), (0, .25, 1, .25), (0, .5, 1, .25), (0, .75, 1, .25)],
    "grid6": [(0, 0, 1 / 3, .5), (1 / 3, 0, 1 / 3, .5), (2 / 3, 0, 1 / 3, .5),
              (0, .5, 1 / 3, .5), (1 / 3, .5, 1 / 3, .5), (2 / 3, .5, 1 / 3, .5)],
}

# ThreadingHTTPServer can receive several rapid tag clicks at once.  Serialize
# each read-modify-write transaction so edits.json cannot be truncated or lose
# a sibling update.
DATA_WRITE_LOCK = threading.RLock()


def locked_data_write(fn):
    def wrapped(*args, **kwargs):
        with DATA_WRITE_LOCK:
            return fn(*args, **kwargs)
    wrapped.__name__ = fn.__name__
    return wrapped


# --------------------------------------------------------------------- 공통

def load_json(path: Path, default):
    if path.exists():
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            print(f"  ! {path.name} 파싱 실패 — 기본값 사용", file=sys.stderr)
    return default


def save_json(path: Path, obj):
    with DATA_WRITE_LOCK:
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = path.with_suffix(path.suffix + ".tmp")
        tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        tmp.replace(path)


FULL_BACKUP_DIR = DATA / "backups" / "full"
FULL_BACKUP_STATE = DATA / "backups" / "full-backup-state.json"


def _full_backup_sources() -> list[Path]:
    """편집 상태 전체와 사람이 검토하는 생성 문서를 모은다 (원본 미디어 제외)."""
    files = [p for p in DATA.rglob("*")
             if p.is_file() and (DATA / "backups") not in p.parents
             and not p.name.endswith(".tmp")]
    for name in ("index.html", "VIDEO_PLOT.html", "VIDEO_PLAN.md", "LOG.md"):
        p = ROOT / name
        if p.exists():
            files.append(p)
    return sorted(set(files), key=lambda p: str(p.relative_to(ROOT)))


def _full_backup_signature(files: list[Path]) -> str:
    digest = hashlib.sha256()
    for p in files:
        st = p.stat()
        digest.update(str(p.relative_to(ROOT)).encode("utf-8"))
        digest.update(f"\0{st.st_size}\0{st.st_mtime_ns}\n".encode("ascii"))
    return digest.hexdigest()


@locked_data_write
def create_full_backup(reason="manual", if_changed=False):
    """갤러리·콘티 편집 상태 전체를 복구 가능한 ZIP 한 개로 보관한다."""
    files = _full_backup_sources()
    signature = _full_backup_signature(files)
    previous = load_json(FULL_BACKUP_STATE, {})
    if if_changed and previous.get("signature") == signature:
        return {"ok": True, "created": False,
                "backup": previous.get("backup"), "count": len(files)}

    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S-%f")
    FULL_BACKUP_DIR.mkdir(parents=True, exist_ok=True)
    dest = FULL_BACKUP_DIR / f"jiho-work-{stamp}.zip"
    tmp = dest.with_suffix(".zip.tmp")
    made = dt.datetime.now().astimezone().isoformat(timespec="seconds")
    with zipfile.ZipFile(tmp, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=6) as zf:
        for p in files:
            zf.write(p, str(p.relative_to(ROOT)))
        zf.writestr("BACKUP_INFO.json", json.dumps({
            "created": made, "reason": reason, "signature": signature,
            "files": [str(p.relative_to(ROOT)) for p in files],
            "note": "원본 사진·영상은 프로젝트에 그대로 있으며, 이 ZIP은 편집 상태 전체입니다."
        }, ensure_ascii=False, indent=2) + "\n")
    tmp.replace(dest)
    rel = str(dest.relative_to(ROOT))
    save_json(FULL_BACKUP_STATE, {"signature": signature, "backup": rel,
                                  "created": made, "reason": reason})
    return {"ok": True, "created": True, "backup": rel,
            "count": len(files), "bytes": dest.stat().st_size}


def _auto_backup_loop(stop: threading.Event, interval=300):
    """서버가 켜진 동안 5분마다 변경 여부를 보고, 달라졌을 때만 백업한다."""
    while not stop.wait(interval):
        try:
            result = create_full_backup(reason="auto-5min", if_changed=True)
            if result.get("created"):
                print(f"backup: 자동 전체 백업 → {result['backup']}")
        except Exception as e:                                    # noqa: BLE001
            print(f"  ! 자동 전체 백업 실패: {e}", file=sys.stderr)


# ------------------------------------------------------- 저용량 검토 영상 렌더

RENDER_DIR = ROOT / "renders"
RENDER_OUTPUT = RENDER_DIR / "jiho-preview-low.mp4"
RENDER_WIDTH, RENDER_HEIGHT, RENDER_FPS = 640, 360, 15
RENDER_LIMIT_BYTES = 50_000_000
RENDER_TARGET_BYTES = 45_000_000
RENDER_MAX_VIDEO_BPS = 800_000
RENDER_AUDIO_BPS = 64_000
RENDER_SEGMENT_CRF = 21
RENDER_PRESETS = {
    "low": {"label": "저용량", "width": 640, "height": 360, "fps": 15,
            "limit": 50_000_000, "target": 45_000_000, "max_bps": 800_000,
            "audio_bps": 64_000, "crf": 21, "output": "jiho-preview-low.mp4"},
    "2x": {"label": "2배", "width": 960, "height": 540, "fps": 30,
           "limit": 100_000_000, "target": 90_000_000, "max_bps": 2_500_000,
           "audio_bps": 96_000, "crf": 20, "output": "jiho-preview-2x.mp4"},
    "4x": {"label": "4배", "width": 1280, "height": 720, "fps": 30,
           "limit": 200_000_000, "target": 180_000_000, "max_bps": 5_500_000,
           "audio_bps": 128_000, "crf": 19, "output": "jiho-preview-4x.mp4"},
    "1080p": {"label": "1080P", "width": 1920, "height": 1080, "fps": 30,
              "limit": 650_000_000, "target": 550_000_000, "max_bps": 18_000_000,
              "audio_bps": 192_000, "crf": 18, "output": "jiho-final-1080p.mp4"},
}
FFMPEG_FULL = Path("/opt/homebrew/opt/ffmpeg-full/bin/ffmpeg")
FFPROBE_FULL = Path("/opt/homebrew/opt/ffmpeg-full/bin/ffprobe")
FFMPEG_BIN = str(FFMPEG_FULL if FFMPEG_FULL.is_file() else (shutil.which("ffmpeg") or "ffmpeg"))
FFPROBE_BIN = str(FFPROBE_FULL if FFPROBE_FULL.is_file() else (shutil.which("ffprobe") or "ffprobe"))
RENDER_FONTS = {
    "maru_buri": ROOT / "fonts" / "MaruBuri-SemiBold.ttf",
    "nanum_myeongjo": ROOT / "fonts" / "NanumMyeongjo-Regular.ttf",
    "apple_myungjo": Path("/System/Library/Fonts/Supplemental/AppleMyungjo.ttf"),
    "nanum_pen": ROOT / "fonts" / "NanumPenScript-Regular.ttf",
    "nanum_brush": ROOT / "fonts" / "NanumBrushScript-Regular.ttf",
    "apple_gothic": Path("/System/Library/Fonts/Supplemental/AppleGothic.ttf"),
}
RENDER_FONT_STYLES = {
    "maru_buri": {"size": 23, "wrap": 26, "line_spacing": 4, "border": 0},
    "nanum_myeongjo": {"size": 22, "wrap": 27, "line_spacing": 4, "border": 0},
    "apple_myungjo": {"size": 20, "wrap": 29, "line_spacing": 4, "border": 0},
    "nanum_pen": {"size": 34, "wrap": 19, "line_spacing": 4, "border": 0},
    "nanum_brush": {"size": 33, "wrap": 20, "line_spacing": 4, "border": 0},
    "apple_gothic": {"size": 23, "wrap": 26, "line_spacing": 4, "border": 0},
}
_caption_measure_cache = {}


def _wrap_caption(text, font, style, max_width):
    """실제 FreeType 픽셀 폭이 화면을 넘을 때만 자동 줄바꿈한다."""
    def measured(line):
        return _measure_caption_box(line or " ", font, style)[0]

    def split_token(token):
        chunks, current = [], ""
        for char in token:
            candidate = current + char
            if current and measured(candidate) > max_width:
                chunks.append(current)
                current = char
            else:
                current = candidate
        if current:
            chunks.append(current)
        return chunks or [""]

    lines = []
    # splitlines()는 사용자가 직접 넣은 줄바꿈을 먼저 보존한다.
    for raw in str(text or "").splitlines() or [""]:
        raw = raw.strip()
        if not raw:
            lines.append("")
            continue
        words = raw.split(" ")
        current = ""
        for word in words:
            pieces = split_token(word) if measured(word) > max_width else [word]
            for piece_i, piece in enumerate(pieces):
                candidate = f"{current} {piece}".strip()
                if current and measured(candidate) > max_width:
                    lines.append(current)
                    current = piece
                else:
                    current = candidate
                if piece_i < len(pieces) - 1:
                    lines.append(current)
                    current = ""
        if current:
            lines.append(current)
    return lines or [""]


def _measure_caption_box(text, font, style):
    """FFmpeg/FreeType가 실제 그린 자막의 픽셀 경계를 측정한다."""
    key = (str(text), str(font), int(style["size"]), int(style["line_spacing"]))
    if key in _caption_measure_cache:
        return _caption_measure_cache[key]
    with tempfile.TemporaryDirectory(prefix="jiho-caption-") as tmp:
        text_file = Path(tmp) / "caption.txt"
        text_file.write_text(str(text), encoding="utf-8")
        vf = (f"drawtext=fontfile='{font}':textfile='{text_file}':fontcolor=white:"
              f"fontsize={style['size']}:line_spacing={style['line_spacing']}:x=0:y=0,"
              "bbox=min_val=32")
        result = subprocess.run(
            [FFMPEG_BIN, "-hide_banner", "-loglevel", "info", "-f", "lavfi", "-i",
             f"color=black:s={RENDER_WIDTH}x{RENDER_HEIGHT}:d=0.05", "-vf", vf,
             "-frames:v", "1", "-f", "null", "-"],
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    match = re.search(r"\bw:(\d+) h:(\d+) crop=", result.stderr or "")
    measured = ((int(match.group(1)), int(match.group(2))) if match else
                (max(style["size"], max(map(len, str(text).splitlines())) * style["size"]),
                 max(style["size"], len(str(text).splitlines()) *
                     (style["size"] + style["line_spacing"]))))
    _caption_measure_cache[key] = measured
    return measured
_render_lock = threading.Lock()
_render_status = ({"state": "done",
                   "message": f"기존 영상 · {RENDER_OUTPUT.stat().st_size/1_000_000:.1f}MB",
                   "done": 1, "total": 1,
                   "output": str(RENDER_OUTPUT.relative_to(ROOT)),
                   "bytes": RENDER_OUTPUT.stat().st_size}
                  if RENDER_OUTPUT.exists() else
                  {"state": "idle", "message": "아직 만든 검토 영상이 없습니다",
                   "done": 0, "total": 0, "output": None})


def _set_render_status(**patch):
    with _render_lock:
        _render_status.update(patch)


def render_status():
    with _render_lock:
        return {"ok": True, **_render_status}


def _select_render_preset(name):
    """단일 렌더 작업이 사용할 해상도·프레임률·용량 목표를 설정한다."""
    global RENDER_OUTPUT, RENDER_WIDTH, RENDER_HEIGHT, RENDER_FPS
    global RENDER_LIMIT_BYTES, RENDER_TARGET_BYTES, RENDER_MAX_VIDEO_BPS
    global RENDER_AUDIO_BPS, RENDER_SEGMENT_CRF
    name = str(name or "low").lower()
    if name not in RENDER_PRESETS:
        name = "low"
    preset = RENDER_PRESETS[name]
    RENDER_WIDTH, RENDER_HEIGHT = preset["width"], preset["height"]
    RENDER_FPS = preset["fps"]
    RENDER_LIMIT_BYTES, RENDER_TARGET_BYTES = preset["limit"], preset["target"]
    RENDER_MAX_VIDEO_BPS = preset["max_bps"]
    RENDER_AUDIO_BPS, RENDER_SEGMENT_CRF = preset["audio_bps"], preset["crf"]
    RENDER_OUTPUT = RENDER_DIR / preset["output"]
    return name, preset


def _ffmpeg(cmd, what):
    cmd = list(cmd)
    if cmd and cmd[0] == "ffmpeg":
        cmd[0] = FFMPEG_BIN
    result = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                            text=True)
    if result.returncode:
        tail = (result.stderr or "")[-3000:].strip()
        raise RuntimeError(f"{what} 실패" + (f"\n{tail}" if tail else ""))


def _even_edge(value, limit):
    return max(0, min(limit, int(round(value / 2) * 2)))


def _tile_box(cell):
    x1 = _even_edge(float(cell[0]) * RENDER_WIDTH, RENDER_WIDTH - 2)
    y1 = _even_edge(float(cell[1]) * RENDER_HEIGHT, RENDER_HEIGHT - 2)
    x2 = _even_edge((float(cell[0]) + float(cell[2])) * RENDER_WIDTH, RENDER_WIDTH)
    y2 = _even_edge((float(cell[1]) + float(cell[3])) * RENDER_HEIGHT, RENDER_HEIGHT)
    return x1, y1, max(2, x2 - x1), max(2, y2 - y1)


def _rotation_filter(rotation):
    return {90: "transpose=clock", 180: "hflip,vflip",
            270: "transpose=cclock"}.get(int(rotation or 0) % 360, "")


def _render_segment(cut, duration, fade, dest, lyric="", caption_font="nanum_brush",
                    caption_position=None):
    """컷 하나를 선택한 16:9 렌더 프레임으로 정규화한다."""
    segment_duration = float(duration) + float(fade)
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
           "-f", "lavfi", "-i",
           f"color=c=black:s={RENDER_WIDTH}x{RENDER_HEIGHT}:r={RENDER_FPS}:d={segment_duration:.3f}"]
    for tile in cut.get("tiles") or []:
        path = ROOT / str(tile.get("path") or "")
        if not path.exists():
            raise FileNotFoundError(f"원본을 찾을 수 없습니다: {tile.get('path')}")
        if tile.get("kind") == "image":
            # 정지 이미지 입력도 출력과 같은 프레임률로 생성해야 fps 필터에서
            # 주기적으로 프레임이 복제·삭제되어 줌이 떨리는 현상이 생기지 않는다.
            cmd += ["-loop", "1", "-framerate", str(RENDER_FPS),
                    "-t", f"{segment_duration:.3f}", "-i", str(path)]
        else:
            clip = tile.get("clip") or [0, None]
            start = max(0.0, float(clip[0] or 0))
            cmd += ["-ss", f"{start:.3f}", "-i", str(path)]

    filters = ["[0:v]format=yuv420p[base0]"]
    base = "base0"
    for i, tile in enumerate(cut.get("tiles") or [], 1):
        x, y, width, height = _tile_box(tile.get("cell") or [0, 0, 1, 1])
        chain = ["setpts=PTS-STARTPTS"]
        rotation = _rotation_filter(tile.get("rotation"))
        if rotation:
            chain.append(rotation)
        safe = tile.get("safe")
        if isinstance(safe, list) and len(safe) == 4:
            sx1, sy1, sx2, sy2 = [max(0.0, min(1.0, float(v))) for v in safe]
            if sx2 - sx1 > .001 and sy2 - sy1 > .001:
                chain.append(f"crop=iw*{sx2-sx1:.8f}:ih*{sy2-sy1:.8f}:"
                             f"iw*{sx1:.8f}:ih*{sy1:.8f}")
        if tile.get("kind") == "image" and tile.get("effect") == "zoom_in":
            frames = max(2, int(round(segment_duration * RENDER_FPS)))
            inset = .5 * (1 - 1 / 1.06)
            progress = f"min(on/{frames - 1},1)"
            # 원본 픽셀을 정수 좌표로 잘라 옮기는 zoompan 대신, 원본 해상도의
            # 네 모서리를 부동소수점 좌표로 매 프레임 변환한다. cubic 보간 후
            # 최종 출력 크기로 단 한 번만 축소하므로 선명한 대각선도 흔들리지 않는다.
            chain.append(
                f"perspective=x0='W*{inset:.10f}*{progress}':"
                f"y0='H*{inset:.10f}*{progress}':"
                f"x1='W*(1-{inset:.10f}*{progress})':"
                f"y1='H*{inset:.10f}*{progress}':"
                f"x2='W*{inset:.10f}*{progress}':"
                f"y2='H*(1-{inset:.10f}*{progress})':"
                f"x3='W*(1-{inset:.10f}*{progress})':"
                f"y3='H*(1-{inset:.10f}*{progress})':"
                "interpolation=cubic:sense=source:eval=frame")
        if tile.get("fit") == "cover":
            chain += [f"scale={width}:{height}:force_original_aspect_ratio=increase",
                      f"crop={width}:{height}"]
        else:
            try:
                media_x, media_y = [max(0.0, min(1.0, float(v)))
                                    for v in (tile.get("media_position") or [.5, .5])[:2]]
            except (TypeError, ValueError):
                media_x, media_y = .5, .5
            chain += [f"scale={width}:{height}:force_original_aspect_ratio=decrease",
                      f"pad={width}:{height}:(ow-iw)*{media_x:.4f}:"
                      f"(oh-ih)*{media_y:.4f}:black"]
        chain += ["setsar=1", f"fps={RENDER_FPS}",
                  f"tpad=stop_mode=clone:stop_duration={segment_duration:.3f}",
                  f"trim=duration={segment_duration:.3f}", "format=yuv420p"]
        filters.append(f"[{i}:v]{','.join(chain)}[tile{i}]")
        out = f"base{i}"
        filters.append(f"[{base}][tile{i}]overlay={x}:{y}:shortest=1[{out}]")
        base = out
    clean_lyric = str(lyric or "").strip()
    if clean_lyric and clean_lyric != "가사 없음":
        style = dict(RENDER_FONT_STYLES.get(
            str(caption_font), RENDER_FONT_STYLES["nanum_brush"]))
        font_scale = RENDER_WIDTH / 640
        style["size"] = max(1, int(round(style["size"] * font_scale)))
        style["line_spacing"] = max(1, int(round(style["line_spacing"] * font_scale)))
        font = RENDER_FONTS.get(str(caption_font), RENDER_FONTS["maru_buri"])
        if not font.is_file():
            font = RENDER_FONTS["nanum_pen"]
        lyric_file = dest.with_suffix(".lyric.txt")
        lyric_lines = _wrap_caption(clean_lyric, font, style, int(RENDER_WIDTH * .92))
        wrapped_lyric = "\n".join(lyric_lines)
        lyric_file.write_text(wrapped_lyric, encoding="utf-8")
        try:
            pos_x, pos_y = [float(v) for v in (caption_position or [.5, .86])[:2]]
        except (TypeError, ValueError):
            pos_x, pos_y = .5, .86
        pos_x, pos_y = max(.0, min(1., pos_x)), max(.0, min(1., pos_y))
        measured_width, _measured_height = _measure_caption_box(wrapped_lyric, font, style)
        box_width = max(2, min(int(RENDER_WIDTH * .92), measured_width))
        x_expr = f"max(0,min(w-{box_width},w*{pos_x:.4f}-{box_width / 2:.1f}))"
        y_expr = f"max(0,min(h-text_h,h*{pos_y:.4f}-text_h/2))"
        filters.append(f"[{base}]trim=duration={segment_duration:.3f},"
                       "setpts=PTS-STARTPTS,format=yuv420p[captionbase]")
        filters.append(f"[captionbase]drawtext=fontfile='{font}':textfile='{lyric_file}':"
                       f"fontcolor=white:fontsize={style['size']}:line_spacing={style['line_spacing']}:"
                       f"boxw={box_width}:text_align=C:x='{x_expr}':y='{y_expr}':"
                       f"fix_bounds=true:borderw={style['border']}:bordercolor=black@0:"
                       f"shadowx={max(1, round(font_scale))}:"
                       f"shadowy={max(1, round(2 * font_scale))}:"
                       "shadowcolor=black@.70[outv]")
    else:
        filters.append(f"[{base}]trim=duration={segment_duration:.3f},"
                       f"setpts=PTS-STARTPTS,format=yuv420p[outv]")
    cmd += ["-filter_complex", ";".join(filters), "-map", "[outv]", "-an",
            "-r", str(RENDER_FPS), "-c:v", "libx264", "-preset", "ultrafast",
            "-crf", str(RENDER_SEGMENT_CRF), "-pix_fmt", "yuv420p", str(dest)]
    _ffmpeg(cmd, f"{cut.get('file') or '슬라이드'} 변환")


def _source_has_audio(path):
    result = subprocess.run([FFPROBE_BIN, "-v", "error", "-select_streams", "a:0",
                             "-show_entries", "stream=index", "-of", "csv=p=0", str(path)],
                            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, text=True)
    return result.returncode == 0 and bool(result.stdout.strip())


def _measure_loudness(path, start, duration):
    """EBU R128 첫 패스로 클립 음량을 읽어 두 번째 패스용 파라미터를 만든다."""
    result = subprocess.run([FFMPEG_BIN, "-hide_banner", "-nostats", "-v", "info",
                             "-ss", f"{start:.3f}", "-t", f"{duration:.3f}",
                             "-i", str(path), "-vn", "-af",
                             "loudnorm=I=-16:TP=-1.5:LRA=11:print_format=json",
                             "-f", "null", "-"], stdout=subprocess.DEVNULL,
                            stderr=subprocess.PIPE, text=True)
    matches = re.findall(r'\{\s*"input_i"[\s\S]*?\}', result.stderr or "")
    if not matches:
        return {"filter": "loudnorm=I=-16:TP=-1.5:LRA=11", "input_i": None}
    try:
        measured = json.loads(matches[-1])
        values = [measured[k] for k in ("input_i", "input_tp", "input_lra",
                                        "input_thresh", "target_offset")]
        if any(str(v).lower() in ("-inf", "inf", "nan") for v in values):
            raise ValueError("측정 불가")
        filt = ("loudnorm=I=-16:TP=-1.5:LRA=11:"
                f"measured_I={values[0]}:measured_TP={values[1]}:"
                f"measured_LRA={values[2]}:measured_thresh={values[3]}:"
                f"offset={values[4]}:linear=true")
        return {"filter": filt, "input_i": float(values[0])}
    except (KeyError, ValueError, TypeError, json.JSONDecodeError):
        return {"filter": "loudnorm=I=-16:TP=-1.5:LRA=11", "input_i": None}


def _xfade_files(paths, durations, fade, dest, final=False, music=None, total=None,
                 audio_events=None, music_volume=1.0, source_volume=.70):
    cmd = ["ffmpeg", "-y", "-hide_banner", "-loglevel", "error"]
    for path in paths:
        cmd += ["-i", str(path)]
    music_index = None
    if final and music and music.exists():
        music_index = len(paths)
        cmd += ["-i", str(music)]
    audio_inputs = []
    for event in (audio_events or []):
        input_i = len(paths) + (1 if music_index is not None else 0) + len(audio_inputs)
        cmd += ["-ss", f"{event['source_start']:.3f}", "-t", f"{event['duration']:.3f}",
                "-i", str(event["path"])]
        audio_inputs.append((input_i, event))
    if len(paths) == 1:
        parts = [f"[0:v]setpts=PTS-STARTPTS,tpad=stop_mode=clone:"
                 f"stop_duration={float(durations[0]):.3f},"
                 f"trim=duration={float(durations[0]):.3f},format=yuv420p[vout]"]
    else:
        parts, offset = [], 0.0
        # 중간 묶음 파일이 인코더 타임베이스 때문에 몇 프레임 짧아져도
        # 다음 묶음의 시작 시각과 전체 길이가 당겨지지 않도록 정규화한다.
        normalized = []
        for i, duration in enumerate(durations):
            expected = float(duration) + (float(fade) if i < len(paths) - 1 else 0.0)
            label = f"vin{i}"
            parts.append(f"[{i}:v]setpts=PTS-STARTPTS,tpad=stop_mode=clone:"
                         f"stop_duration={expected:.3f},trim=duration={expected:.3f},"
                         f"format=yuv420p[{label}]")
            normalized.append(label)
        previous = normalized[0]
        for i in range(1, len(paths)):
            offset += float(durations[i - 1])
            out = "vout" if i == len(paths) - 1 else f"xf{i}"
            parts.append(f"[{previous}][{normalized[i]}]xfade=transition=fade:duration={fade:.3f}:"
                         f"offset={offset:.3f}[{out}]")
            previous = out
    audio_output = None
    if final and music_index is not None:
        parts.append(f"[{music_index}:a]atrim=duration={float(total):.3f},"
                     f"asetpts=PTS-STARTPTS,aresample=48000,volume={music_volume:.3f},"
                     f"apad=whole_dur={float(total):.3f},"
                     f"atrim=duration={float(total):.3f}[music]")
    voice_labels = []
    for voice_i, (input_i, event) in enumerate(audio_inputs):
        delay = max(0, int(round(float(event["timeline_start"]) * 1000)))
        label = f"voice{voice_i}"
        parts.append(f"[{input_i}:a]atrim=duration={event['duration']:.3f},"
                     f"asetpts=PTS-STARTPTS,aresample=48000,{event['loudnorm_filter']},"
                     f"aformat=sample_rates=48000:channel_layouts=stereo,"
                     f"volume={source_volume:.3f},"
                     f"adelay={delay}:all=1[{label}]")
        voice_labels.append(label)
    if voice_labels:
        # 무음 베드를 첫 입력으로 두면 원본 클립이 짧거나 뒤늦게 시작해도
        # 사이드체인의 길이는 언제나 완성 영상과 정확히 같다. adelay는 각
        # 영상의 실제 등장 위치만큼 샘플 자체를 앞에 채우므로 처음에 몰리지 않는다.
        parts.append(f"anullsrc=r=48000:cl=stereo:d={float(total):.3f}[voicebed]")
        parts.append("[voicebed]" + "".join(f"[{x}]" for x in voice_labels) +
                     f"amix=inputs={len(voice_labels) + 1}:normalize=0:"
                     f"duration=first,atrim=duration={float(total):.3f}[voices]")
        if music_index is not None:
            # 노래는 항상 지정한 음량 그대로 둔다. 영상 원음만 위에서 선택한
            # source_volume으로 줄인 뒤 더하며, 원음 때문에 노래를 duck하지 않는다.
            parts.append(f"[music][voices]amix=inputs=2:weights='1 1':"
                         f"normalize=0:duration=first,atrim=duration={float(total):.3f},"
                         f"alimiter=limit=.99[aout]")
        else:
            parts.append("[voices]alimiter=limit=.95[aout]")
        audio_output = "aout"
    elif music_index is not None:
        parts.append("[music]alimiter=limit=.95[aout]")
        audio_output = "aout"
    cmd += ["-filter_complex", ";".join(parts), "-map", "[vout]"]
    if audio_output:
        cmd += ["-map", f"[{audio_output}]", "-c:a", "aac", "-b:a", str(RENDER_AUDIO_BPS)]
    else:
        cmd += ["-an"]
    if final:
        total = max(.2, float(total or sum(durations)))
        video_bps = int(max(160_000, min(RENDER_MAX_VIDEO_BPS,
            ((RENDER_TARGET_BYTES * 8 / total) -
             (RENDER_AUDIO_BPS if audio_output else 0)) * .95)))
        cmd += ["-t", f"{total:.3f}", "-c:v", "libx264", "-preset", "veryfast",
                "-b:v", str(video_bps), "-maxrate", str(int(video_bps * 1.25)),
                "-bufsize", str(video_bps * 2), "-pix_fmt", "yuv420p",
                "-movflags", "+faststart", str(dest)]
    else:
        cmd += ["-c:v", "libx264", "-preset", "ultrafast",
                "-crf", str(RENDER_SEGMENT_CRF),
                "-pix_fmt", "yuv420p", str(dest)]
    _ffmpeg(cmd, "크로스페이드 합성")


def _preview_render_worker(render_options=None):
    work = None
    try:
        render_options = render_options or {}
        quality, preset = _select_render_preset(render_options.get("quality"))
        music_volume = max(0.0, min(2.0, float(render_options.get("music_volume", 1.0))))
        source_volume = max(0.0, min(2.0, float(render_options.get("source_volume", .70))))
        caption_font = str(render_options.get("caption_font") or "nanum_brush")
        if caption_font not in RENDER_FONTS:
            caption_font = "nanum_brush"
        plan = load_json(PLAN_JSON, {})
        all_cuts = [cut for chapter in plan.get("chapters", []) for cut in chapter.get("cuts", [])]
        cut_by_key = {"|".join(tile["file"] for tile in cut.get("tiles", [])): cut
                      for cut in all_cuts}
        render_sections = plan.get("render_sections") or []
        caption_positions = ((plan.get("plot_layout") or {}).get("caption_positions") or {})
        render_items, used_keys, black_seconds = [], [], 0.0
        if render_sections:
            for section in render_sections:
                budget = max(0.0, float(section.get("to") or 0) -
                             float(section.get("from") or 0))
                lyric = str(section.get("lyric") or "")
                section_id = str(section.get("id") or "")
                section_caption_position = caption_positions.get(f"section:{section_id}")
                spent = 0.0
                for key in section.get("keys") or []:
                    cut = cut_by_key.get(key)
                    remaining = budget - spent
                    if not cut or remaining < 1 / RENDER_FPS:
                        break
                    duration = min(max(.0, float(cut.get("dur") or 0)), remaining)
                    if duration < 1 / RENDER_FPS:
                        break
                    cut = dict(cut)
                    if section_caption_position:
                        cut["caption_position"] = section_caption_position
                    render_items.append((cut, duration, section_id, lyric))
                    used_keys.append(key)
                    spent += duration
                gap = max(0.0, budget - spent)
                if gap >= 1 / RENDER_FPS:
                    render_items.append(({"file": f"검은 화면 · {section.get('title')}",
                                          "tiles": [],
                                          "caption_position": section_caption_position}, gap,
                                         section_id, lyric))
                    black_seconds += gap
        else:
            for key in plan.get("render_keys") or []:
                if key in cut_by_key:
                    cut = cut_by_key[key]
                    render_items.append((cut, max(.2, float(cut.get("dur") or 0)), "", ""))
                    used_keys.append(key)
        if not render_items:
            raise RuntimeError("왼쪽 콘티에 배치된 슬라이드가 없습니다")
        cuts = [item[0] for item in render_items]
        durations = [item[1] for item in render_items]
        lyrics_for_items = [item[3] for item in render_items]
        # 기존 전환보다 50% 길게: 사진이 동시에 사라지고 나타나는 여운을
        # 조금 더 주되, 아주 짧은 슬라이드에서는 길이의 67.5%를 넘지 않는다.
        fade = min(.525, max(.12, min(durations) * .675)) if len(cuts) > 1 else 0.0
        total = sum(durations)
        RENDER_DIR.mkdir(parents=True, exist_ok=True)
        work = Path(tempfile.mkdtemp(prefix="jiho-render-", dir=RENDER_DIR))
        segments = []
        _set_render_status(state="running",
                           message=(f"{preset['label']} {RENDER_WIDTH}×{RENDER_HEIGHT} 변환 중"
                                    f" · 검은 화면 {black_seconds:.1f}초"),
                           done=0,
                           total=len(cuts) + math.ceil(len(cuts) / 32) + 1,
                           quality=quality, quality_label=preset["label"],
                           width=RENDER_WIDTH, height=RENDER_HEIGHT, fps=RENDER_FPS)
        for i, (cut, dur, lyric) in enumerate(zip(cuts, durations, lyrics_for_items)):
            path = work / f"segment-{i:04d}.mp4"
            _render_segment(cut, dur, fade if i < len(cuts) - 1 else 0.0, path, lyric,
                            caption_font=caption_font,
                            caption_position=cut.get("caption_position"))
            segments.append(path)
            _set_render_status(done=i + 1,
                               message=f"슬라이드 변환 중 · {i + 1}/{len(cuts)}")

        chunks, chunk_durations = [], []
        for group_i, start in enumerate(range(0, len(segments), 32)):
            group_paths = segments[start:start + 32]
            group_durs = durations[start:start + 32]
            chunk = work / f"chunk-{group_i:03d}.mp4"
            _xfade_files(group_paths, group_durs, fade, chunk)
            chunks.append(chunk)
            chunk_durations.append(sum(group_durs))
            _set_render_status(done=len(cuts) + group_i + 1,
                               message=f"크로스페이드 묶는 중 · {group_i + 1}/{math.ceil(len(cuts)/32)}")

        music_path = ROOT / str(plan.get("music", {}).get("file") or "")
        edits = load_json(EDITS_JSON, {})
        audio_events, timeline = [], 0.0
        for cut, dur in zip(cuts, durations):
            for tile in cut.get("tiles", []):
                kind = tile.get("kind")
                file_name = str(tile.get("file") or "")
                explicit_audio = (edits.get(file_name, {}) or {}).get("audio")
                is_live_photo = kind == "motion" or ".LS." in file_name.upper()
                # 일반 동영상은 원음을 기본으로 살린다. 갤러리에서 명시적으로
                # mute한 것만 빼고, 라이브/모션 포토는 명시적 keep이 없으면 무음이다.
                if (kind not in ("video", "motion") or explicit_audio == "mute" or
                        (is_live_photo and explicit_audio != "keep")):
                    continue
                source = ROOT / str(tile.get("path") or "")
                if not source.is_file() or not _source_has_audio(source):
                    continue
                clip = tile.get("clip") or [0, None]
                source_start = max(0.0, float(clip[0] or 0))
                available = (max(.05, float(clip[1]) - source_start)
                             if len(clip) > 1 and clip[1] is not None else dur)
                audio_events.append({"path": source, "source_start": source_start,
                                     "timeline_start": timeline,
                                     "duration": min(dur, available),
                                     "file": tile.get("file")})
            timeline += dur
        for audio_i, event in enumerate(audio_events, 1):
            _set_render_status(message=f"원본 소리 음량 분석 중 · {audio_i}/{len(audio_events)}")
            measured = _measure_loudness(event["path"], event["source_start"],
                                         event["duration"])
            event["loudnorm_filter"] = measured["filter"]
            event["measured_lufs"] = measured["input_i"]
        temp_output = work / "preview-final.mp4"
        _set_render_status(message=f"최종 압축·음량 자동 믹스 중 · 원본 소리 {len(audio_events)}개")
        _xfade_files(chunks, chunk_durations, fade, temp_output, final=True,
                     music=music_path if music_path.is_file() else None, total=total,
                     audio_events=audio_events, music_volume=music_volume,
                     source_volume=source_volume)
        if temp_output.stat().st_size > RENDER_LIMIT_BYTES:
            smaller = work / "preview-smaller.mp4"
            bps = max(120_000, int(
                ((RENDER_LIMIT_BYTES * 8 / max(.2, total)) -
                 (RENDER_AUDIO_BPS if audio_events or music_path.is_file() else 0)) * .92))
            _ffmpeg(["ffmpeg", "-y", "-hide_banner", "-loglevel", "error",
                     "-i", str(temp_output), "-c:v", "libx264", "-preset", "veryfast",
                     "-b:v", str(bps), "-maxrate", str(int(bps * 1.2)),
                     "-bufsize", str(bps * 2), "-c:a", "copy", "-movflags", "+faststart",
                     str(smaller)], f"{preset['label']} 용량 재압축")
            temp_output = smaller
        temp_output.replace(RENDER_OUTPUT)
        size = RENDER_OUTPUT.stat().st_size
        _set_render_status(state="done",
                           message=(f"{preset['label']} {RENDER_WIDTH}×{RENDER_HEIGHT} 완료"
                                    f" · {size/1_000_000:.1f}MB"),
                           done=len(cuts) + math.ceil(len(cuts) / 32) + 1,
                           output=str(RENDER_OUTPUT.relative_to(ROOT)), bytes=size,
                           duration=round(total, 2), fade=fade,
                           cuts=len(used_keys), segments=len(cuts),
                           black_seconds=round(black_seconds, 2),
                           original_audio=len(audio_events),
                           music_volume=music_volume, source_volume=source_volume,
                           caption_font=caption_font,
                           quality=quality, quality_label=preset["label"],
                           width=RENDER_WIDTH, height=RENDER_HEIGHT, fps=RENDER_FPS,
                           measured_lufs={e["file"]: e.get("measured_lufs")
                                          for e in audio_events})
    except Exception as e:                                        # noqa: BLE001
        _set_render_status(state="error", message=str(e), error=str(e))
        print(f"  ! 검토 영상 렌더 실패: {e}", file=sys.stderr)
    finally:
        if work and work.exists():
            shutil.rmtree(work, ignore_errors=True)


def start_preview_render(options=None):
    if not shutil.which("ffmpeg"):
        return {"ok": False, "error": "ffmpeg가 설치되어 있지 않습니다"}
    with _render_lock:
        if _render_status.get("state") in ("queued", "running"):
            return {"ok": True, **_render_status, "already_running": True}
        requested = str((options or {}).get("quality") or "low").lower()
        if requested not in RENDER_PRESETS:
            requested = "low"
        preset = RENDER_PRESETS[requested]
        _render_status.update({"state": "queued",
                               "message": f"{preset['label']} 렌더링 준비 중",
                               "done": 0, "total": 0, "output": None, "error": None})
    threading.Thread(target=_preview_render_worker, args=(dict(options or {}),),
                     daemon=True).start()
    return render_status()


def summary_for(summaries, name: str) -> str:
    """Return a caption for both organized and original selected filenames.

    organize prefixes filenames with HHMMSS_.  A later selection can contain the
    original basename again, so keep previously written captions useful without
    duplicating or rewriting the user's summary data.
    """
    if summaries.get(name):
        return summaries[name]
    suffix = "_" + name
    matches = [text for key, text in summaries.items() if key.endswith(suffix) and text]
    return matches[0] if len(matches) == 1 else ""


def media_files(root: Path):
    if not root.exists():
        return
    for p in sorted(root.rglob("*")):
        if p.is_file() and p.name not in IGNORE and not p.name.startswith("."):
            if p.name.endswith((MOTION_SUFFIX, MOTION_WEB_SUFFIX)):
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
        if "taken_local" in ov:
            # null 은 EXIF 날짜로 되돌아가지 않는 명시적인 "날짜 없음"이다.
            # 오래된 가족사진처럼 연대순 대신 갤러리 마지막에 둘 때 사용한다.
            if ov["taken_local"]:
                m["taken_local"] = norm_datetime(ov["taken_local"]) or m["taken_local"]
            else:
                m["taken_local"] = None
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
            web_clip = p.with_name(p.name.rsplit(".", 1)[0] + MOTION_WEB_SUFFIX)
            raw_clip = p.with_name(p.name.rsplit(".", 1)[0] + MOTION_SUFFIX)
            clip = web_clip if web_clip.exists() else raw_clip
            info["motion"] = str(clip.relative_to(ROOT)) if clip.exists() else None
            info["motion_duration_sec"] = (probe(clip, TZ_OFFSET).get("duration_sec")
                                           if clip.exists() else None)
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
    # Do not trust filenames alone: sharing/exporting a Motion Photo often
    # removes the .MP or MVIMG marker while leaving the embedded movie intact.
    cand = [m for m in meta["items"] if m["kind"] == "image"]
    made = have = none = converted = convert_failed = 0
    for m in cand:
        src = ROOT / m["path"]
        dest = src.with_name(src.name.rsplit(".", 1)[0] + MOTION_SUFFIX)
        if dest.exists():
            have += 1
        elif extract_motion(src, dest):
            made += 1
        else:
            none += 1
            if args.verbose and re.search(r"\.MP\.jpg$|^MVIMG_|^\d{6}_MVIMG_", m["file"], re.I):
                print(f"  · 내장 영상 없음: {m['file']}")
            continue

        # Google Motion Photo clips are commonly HEVC. Safari support varies
        # and Chrome can show a black frame, so keep the raw derivative and
        # make a small H.264 browser copy next to it.
        web = src.with_name(src.name.rsplit(".", 1)[0] + MOTION_WEB_SUFFIX)
        if web.exists() and web.stat().st_size > 0:
            continue
        tmp = web.with_suffix(".tmp.mp4")
        r = subprocess.run(["avconvert", "--source", str(dest),
                            "--preset", "Preset640x480", "--output", str(tmp),
                            "--replace", "--disableMetadataFilter"], capture_output=True)
        if r.returncode == 0 and tmp.exists() and tmp.stat().st_size > 0:
            tmp.replace(web)
            converted += 1
        else:
            tmp.unlink(missing_ok=True)
            convert_failed += 1
            if args.verbose:
                print(f"  · 브라우저용 변환 실패: {m['file']}")
    print(f"motion: 모션 포토 후보 {len(cand)}개 → 추출 {made} / 기존 {have} / "
          f"영상 없음 {none} / H.264 변환 {converted} / 변환 실패 {convert_failed}")


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
        elif key.startswith("__tag__"):
            _save_tag({"file": key[len("__tag__"):], **patch})
        elif key.startswith("__roster__"):
            _save_note({k: v for k, v in patch.items() if k in ("roster", "milestones")})
        elif key.startswith("__chapters__"):
            _save_chapters(patch)
        elif key.startswith("__music__"):
            _save_music(patch)
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
    """Render through Quick Look first so Pixel HDR/gain-map JPEGs do not turn black."""
    dst.parent.mkdir(parents=True, exist_ok=True)
    tmp = dst.parent / ("_ql_img_" + dst.stem)
    tmp.mkdir(parents=True, exist_ok=True)
    try:
        subprocess.run(["qlmanage", "-t", "-s", str(size), "-o", str(tmp), str(src)],
                       capture_output=True, timeout=8)
    except subprocess.TimeoutExpired:
        pass
    made = sorted(tmp.glob("*.png"))
    if made:
        subprocess.run(["sips", "-s", "format", "jpeg", "-s", "formatOptions", "70",
                        str(made[0]), "--out", str(dst)], capture_output=True)
    shutil.rmtree(tmp, ignore_errors=True)
    if dst.exists():
        return True
    # Fallback for formats Quick Look does not understand.
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
    try:
        subprocess.run(["qlmanage", "-t", "-s", str(size), "-o", str(tmp), str(src)],
                       capture_output=True, timeout=8)
    except subprocess.TimeoutExpired:
        # A damaged or unusual movie must not block every later thumbnail.
        pass
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
    todo = [m for m in meta["items"] if not summary_for(summaries, m["file"]) or args.force]
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

    edits = load_edits()

    days = group_days(items)
    review = [m for m in items if not m.get("taken_local")]

    _write_log_md(days, review, summaries, notes, bday, edits)
    _write_gallery(days, review, summaries, notes, bday, args.size, edits=edits)
    total = sum(len(v) for d in days.values() for v in d.values())
    print(f"build: index.html · LOG.md  ({len(days)}일 / {total}컷 / 확인필요 {len(review)})")
    missing = [m for m in items if not summary_for(summaries, m["file"])]
    if missing:
        print(f"  · 요약 없는 항목 {len(missing)}개 — 갤러리에서 직접 쓰거나 `jiho.py sheets` 사용")
    print("  · " + tag_progress(items, edits))


def tag_progress(items, edits) -> str:
    """영상 태깅이 얼마나 됐는지 한 줄로."""
    picked = [edits.get(m["file"], {}).get("pick") for m in items]
    done = sum(1 for p in picked if p is not None)
    must = sum(1 for p in picked if p == 2)
    drop = sum(1 for p in picked if p == 0)
    focus = sum(1 for m in items if (edits.get(m["file"], {}).get("safe") or
                                     edits.get(m["file"], {}).get("focus")))
    priv = sum(1 for m in items if edits.get(m["file"], {}).get("private"))
    return (f"영상 태깅 {done}/{len(items)} — 꼭 {must} · 제외 {drop} · "
            f"필수 영역 {focus} · 비공개 {priv}")


def _write_log_md(days, review, summaries, notes, bday, edits=None):
    edits = edits or {}
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
                s = summary_for(summaries, m["file"])
                tag = "🎬" if m["kind"] == "video" else "📷"
                dur = f" _{m['duration_sec']}초_" if m.get("duration_sec") else ""
                e = edits.get(m["file"], {})
                mark = {2: " ★", 0: " ✕"}.get(e.get("pick"), "") + (" 🔒" if e.get("private") else "")
                who = f" _({', '.join(e['people'])})_" if e.get("people") else ""
                L.append(f"- `{m['taken_local'][11:16]}` {tag}{mark} {s or '_(요약 없음)_'}{dur}{who}  "
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
    if int(m.get("_rotation") or 0) % 180:
        w, h = h, w
    r = w / h
    return "ls" if r > 1.15 else "pt" if r < 0.87 else "sq"


def _shot_html(m, summaries, size, out=None, lite=False, keep=None, edits=None):
    """lite=True 면 원본 대신 썸네일을 가리켜, 썸네일만으로 굴러가는 번들을 만든다."""
    out = out or ROOT
    thumb = _thumb_path(m, size)
    rel = os.path.relpath(thumb, out).replace(os.sep, "/")
    # Thumbnail contents can change at the same path (notably after fixing HDR
    # rendering).  Version the URL so browsers never keep an old black image.
    rel_url = rel + (f"?v={thumb.stat().st_mtime_ns}" if thumb.exists() else "")
    s = summary_for(summaries, m["file"])
    vid = m["kind"] == "video"
    dur = f'<span class="dur">{m["duration_sec"]}s</span>' if m.get("duration_sec") else ""
    src_badge = {"exif": "EXIF", "manual": "수동"}.get(m.get("date_source") or "", "추정")
    motion = m.get("motion") or ""
    keep = keep if keep is not None else set()
    if lite:
        # 원본을 담지 않는 번들: 사진은 썸네일로, 영상/모션은 담은 것만 남긴다
        full = m["path"] if m["path"] in keep else rel_url
        motion = motion if motion in keep else ""
    else:
        full = m["path"]
    if vid and not thumb.exists() and not lite:
        # Safari/Quick Look cannot decode some Android VP9-in-MOV files.  A
        # native <video> thumbnail stays black, so show an honest, clickable
        # fallback card until the file is converted for the final render.
        preview = (f'<div class="thumb-fallback"><b>▶ 영상</b>'
                   f'<span>{html.escape(m["file"])}</span>'
                   f'<small>미리보기 변환 필요 · VP9</small></div>')
    else:
        preview = f'<img src="{html.escape(rel_url)}" loading="lazy" alt="">'
    data = {
        "file": m["file"], "path": full, "kind": m["kind"] if (not lite or m["path"] in keep)
                                                  else "image", "motion": motion,
        "cap": s, "taken": m.get("taken_local") or "",
        "place": m.get("place") or "", "geokey": m.get("geo_key") or "",
        "auto": m.get("place_auto") or "", "dsrc": m.get("date_source") or "",
        "psrc": m.get("place_source") or "", "shape": shot_shape(m),
    }
    # 영상 태그 — 갤러리에서 눌러 모으고, 다시 열었을 때 그대로 보이게 심어둔다
    e = (edits or {}).get(m["file"], {})
    pick, foc, safe, clip = e.get("pick"), e.get("focus"), e.get("safe"), e.get("clip")
    # 일반 썸네일에는 긴 요약이 아니라 실제 영상에 들어갈 짧은 자막만 보인다.
    caption = e.get("short") or ""
    data.update({
        "pick": "" if pick is None else str(pick),
        "priv": "1" if e.get("private") else "",
        "focus": f"{foc[0]},{foc[1]}" if foc else "",
        "safe": ",".join(str(v) for v in safe) if safe else "",
        "face": e.get("face") or "",
        "ppl": ",".join(e.get("people") or []),
        "short": e.get("short") or "",
        "tg": ",".join(e.get("tags") or []),
        "clip": f"{clip[0]},{clip[1]}" if clip else "",
        "audio": e.get("audio") or "",
        "dur": m.get("duration_sec") or "",
        "solo": "1" if e.get("solo") else "",
        "rot": e.get("rotation") or 0,
        "w": _disp_size(m)[0] or "", "h": _disp_size(m)[1] or "",
    })
    attrs = " ".join(f'data-{k}="{html.escape(str(v), quote=True)}"' for k, v in data.items())
    shape = shot_shape(m)
    rot = int(e.get("rotation") or 0) % 360
    if rot in (90, 270):
        shape = {"ls": "pt", "pt": "ls"}.get(shape, shape)
    dw, dh = _disp_size(m)
    ratio = (dw / dh) if dw and dh else 1
    return (f'<figure class="shot {shape}{" vid" if vid else ""}'
            f'{" live" if motion else ""}{" nosum" if not s else ""}'
            f'{f" rot{rot}" if rot else ""}'
            f'{f" pick{pick}" if pick is not None else " untagged"}'
            f'{" priv" if e.get("private") else ""}" style="--ratio:{ratio:.6f}" {attrs}>'
            f'{preview}'
            f'{"<span class=play>▶</span>" if vid else ""}{dur}'
            f'{"<span class=livebadge>◉ LIVE</span>" if motion else ""}'
            f'<span class="src">{src_badge}</span>'
            f'{_tagmark_html(e)}'
            f'<figcaption>{html.escape(caption) or "<i>영상 자막 없음</i>"}</figcaption></figure>')


def _tagmark_html(e) -> str:
    """격자에서 한눈에 보이는 태그 표시 — 선별 등급 / 비공개 / 얼굴 위치."""
    marks = "".join(filter(None, [
        {2: "★", 1: "·", 0: "✕"}.get(e.get("pick"), ""),
        "🔒" if e.get("private") else "",
        "▣" if e.get("safe") else "◎" if e.get("focus") else "",
        "↻" if e.get("rotation") else "",
        "✂" if e.get("clip") else "",
        "🔊" if e.get("audio") == "keep" else "",
        "◻" if e.get("solo") else "",
        f"<em>{len(e['people'])}</em>" if e.get("people") else "",
    ]))
    return f'<span class="tagmark">{marks}</span>' if marks else ""


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
        parts = [summary_for(summaries, m["file"]), m.get("place") or "",
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


def _write_gallery(days, review, summaries, notes, bday, size, out=None, lite=False, keep=None,
                   edits=None):
    out = out or ROOT
    edits = edits if edits is not None else load_edits()
    shot = lambda m: _shot_html(m, summaries, size, out, lite, keep, edits)  # noqa: E731
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
                for m in v if not summary_for(summaries, m["file"])) + \
            sum(1 for m in review if not summary_for(summaries, m["file"]))
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
        .replace("{{IDF}}", json.dumps(idf, ensure_ascii=False, separators=(",", ":")))
        .replace("{{ROSTER}}", json.dumps(roster_of(notes), ensure_ascii=False,
                                          separators=(",", ":")))
        .replace("{{MILESTONES}}", json.dumps(milestones_of(notes), ensure_ascii=False,
                                              separators=(",", ":")))
        .replace("{{CHAPTERS}}", json.dumps(load_chapters(), ensure_ascii=False,
                                            separators=(",", ":")))
        .replace("{{MUSIC}}", json.dumps(load_music(), ensure_ascii=False,
                                         separators=(",", ":")))
        .replace("{{MOODS}}", json.dumps(MOODS, ensure_ascii=False, separators=(",", ":"))),
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
        # Python 3.14 can pass HTTPStatus here for an error response.
        if "/api/" in str(a[0] if a else ""):
            super().log_message(fmt, *a)

    def end_headers(self):
        # 이 페이지는 레이블을 저장할 때마다 다시 생성된다. 브라우저가 예전
        # index.html/스크립트를 재사용하면 방금 추가한 기능이 안 보이므로 캐시하지 않는다.
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()

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
        # Browser uses this only to distinguish the editing server from a
        # static/file:// page.  It must not write data or schedule a rebuild.
        if self.path == "/api/ping":
            self._json({"ok": True, "plan_version":
                        PLAN_JSON.stat().st_mtime_ns if PLAN_JSON.exists() else 0})
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
            elif self.path == "/api/tag":
                # 회전·필수 영역·영상 구간 등은 콘티가 바로 읽는 값이므로
                # 저장 응답 전에 플롯도 갱신한다. 갤러리 HTML 재생성만 디바운스한다.
                result = _save_tag(payload)
                if result.get("ok"):
                    cmd_plan(argparse.Namespace(with_untagged=True, stretch=True))
                self._json(result)
                schedule_rebuild(delay=5.0)
            elif self.path == "/api/tags":
                # 화면에 보이는 레이블 전체를 한 번에 확정 저장한다. 수동 저장 전
                # 파일은 data/backups/ 에 복사해 실수나 파일 손상 때 복구할 수 있다.
                result = _save_tags(payload)
                if result.get("ok"):
                    cmd_plan(argparse.Namespace(with_untagged=True, stretch=True))
                self._json(result)
                schedule_rebuild(delay=1.0)
            elif self.path == "/api/chapters":
                if payload.get("draft"):     # 저장하지 않고 초안만 만들어 돌려준다
                    meta = load_json(META_JSON, {"items": []})
                    notes = load_json(NOTES_JSON, {})
                    self._json({"ok": True, "chapters": _draft_chapters(
                        apply_overrides(meta["items"]), notes,
                        int(payload.get("target_sec") or DEFAULT_TARGET_SEC),
                        int(payload.get("count") or 6))})
                else:
                    self._json(_save_chapters(payload))
            elif self.path == "/api/music":
                self._json(_save_music(payload))
            elif self.path == "/api/plot-layout":
                result = _save_plot_layout(payload)
                if result.get("ok"):
                    cmd_plan(argparse.Namespace(with_untagged=True, stretch=True))
                self._json(result)
            elif self.path == "/api/plan":
                # 선별 기준은 단순하다: '제외'와 비공개만 빼고 전부 넣는다.
                cmd_plan(argparse.Namespace(with_untagged=True, stretch=True))
                self._json({"ok": True, "plan": load_json(PLAN_JSON, {})})
            elif self.path == "/api/backup":
                self._json(create_full_backup(reason="manual", if_changed=False))
            elif self.path == "/api/render-preview":
                self._json(start_preview_render(payload))
            elif self.path == "/api/render-status":
                self._json(render_status())
            elif self.path == "/api/rebuild":
                cmd_build(argparse.Namespace(size=payload.get("size", 480)))
                cmd_plan(argparse.Namespace(with_untagged=True, stretch=True))
                self._json({"ok": True})
            elif self.path == "/api/organize":
                cmd_all(argparse.Namespace(size=payload.get("size", 480)))
                self._json({"ok": True})
            else:
                self._json({"ok": False, "error": "unknown endpoint"}, 404)
        except Exception as e:                                    # noqa: BLE001
            self._json({"ok": False, "error": str(e)}, 500)


@locked_data_write
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
        if key == "taken_local" and not val:
            entry[key] = None             # EXIF 날짜를 명시적으로 숨긴다
        elif val:
            entry[key] = val
        else:
            entry.pop(key, None)
    if entry:
        ov[name] = entry
    else:
        ov.pop(name, None)
    save_json(OVERRIDES_JSON, ov)
    return {"ok": True, "taken_local": entry.get("taken_local"), "place": entry.get("place")}


@locked_data_write
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


@locked_data_write
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


@locked_data_write
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
    for key in ("roster", "milestones"):   # 인물 / 마일스톤 목록 (갤러리에서 추가)
        if key not in p:
            continue
        seen, names = set(), []
        for name in p[key] or []:
            name = str(name).strip()
            if name and name not in seen:
                seen.add(name)
                names.append(name)
        notes[key] = names
    save_json(NOTES_JSON, notes)
    return {"ok": True}


# --------------------------------------------------------------- 영상 태그

def load_edits() -> dict:
    return load_json(EDITS_JSON, {})


def roster_of(notes) -> list[str]:
    r = [str(x).strip() for x in (notes.get("roster") or []) if str(x).strip()]
    return r or list(DEFAULT_ROSTER)


def milestones_of(notes) -> list[str]:
    r = [str(x).strip() for x in (notes.get("milestones") or []) if str(x).strip()]
    return r or list(DEFAULT_MILESTONES)


def _clean_tag(entry: dict, p: dict) -> dict:
    """넘어온 값만 골라 정규화해서 덮어쓴다. 빈 값이면 그 키를 지운다."""
    if "pick" in p:
        v = p["pick"]
        if v in (None, "", -1):
            entry.pop("pick", None)
        else:
            entry["pick"] = max(0, min(2, int(v)))
    if "private" in p:
        if p["private"]:
            entry["private"] = True
        else:
            entry.pop("private", None)
    if "solo" in p:                       # 다른 사진과 묶지 말고 한 화면에 크게
        if p["solo"]:
            entry["solo"] = True
        else:
            entry.pop("solo", None)
    if "rotation" in p:
        try:
            rot = int(p["rotation"] or 0) % 360
        except (TypeError, ValueError):
            rot = 0
        if rot in (90, 180, 270):
            entry["rotation"] = rot
        else:
            entry.pop("rotation", None)
    if "focus" in p:
        f = p["focus"]
        if not f:
            entry.pop("focus", None)
        else:
            x, y = (round(min(1.0, max(0.0, float(v))), 4) for v in (f[0], f[1]))
            entry["focus"] = [x, y]
    if "safe" in p:
        box = p["safe"]
        if not box:
            entry.pop("safe", None)
        else:
            vals = [min(1.0, max(0.0, float(v))) for v in box[:4]]
            x1, x2 = sorted((vals[0], vals[2]))
            y1, y2 = sorted((vals[1], vals[3]))
            if x2 - x1 >= 0.01 and y2 - y1 >= 0.01:
                entry["safe"] = [round(x1, 4), round(y1, 4), round(x2, 4), round(y2, 4)]
            else:
                entry.pop("safe", None)
    if "face" in p:
        v = (p["face"] or "").strip()
        if v in FACE_LABELS:
            entry["face"] = v
        else:
            entry.pop("face", None)
    if "people" in p:
        seen, names = set(), []
        for name in p["people"] or []:
            name = str(name).strip()
            if name and name not in seen:
                seen.add(name)
                names.append(name)
        if names:
            entry["people"] = names
        else:
            entry.pop("people", None)
    if "short" in p:
        text = re.sub(r"\s+", " ", (p["short"] or "")).strip()[:SHORT_MAX]
        if text:
            entry["short"] = text
        else:
            entry.pop("short", None)
    if "tags" in p:                       # 마일스톤 (첫 걸음·백일·여행…)
        seen, tags = set(), []
        for t in p["tags"] or []:
            t = str(t).strip()
            if t and t not in seen:
                seen.add(t)
                tags.append(t)
        if tags:
            entry["tags"] = tags
        else:
            entry.pop("tags", None)
    if "clip" in p:                       # 영상에서 쓸 구간 [시작초, 끝초]
        c = p["clip"]
        if not c:
            entry.pop("clip", None)
        else:
            a, b = (round(max(0.0, float(v)), 2) for v in (c[0], c[1]))
            if b <= a:
                raise ValueError(f"영상 구간의 끝이 시작보다 빠릅니다 ({a}초 → {b}초)")
            entry["clip"] = [a, b]
    if "audio" in p:                      # 아기 웃음소리처럼 살려야 하는 소리
        entry["audio"] = "keep" if p["audio"] == "keep" else "mute"
        if entry["audio"] == "mute":
            entry.pop("audio", None)      # 음소거가 기본 — 굳이 저장하지 않는다
    return entry


@locked_data_write
def _save_tag(p):
    """한 파일의 영상 태그(선별·비공개·얼굴 위치·인물·짧은 자막) 저장."""
    name = p.get("file")
    if not name:
        return {"ok": False, "error": "file 누락"}
    edits = load_edits()
    try:
        entry = _clean_tag(dict(edits.get(name, {})), p)
    except (TypeError, ValueError, IndexError) as e:
        return {"ok": False, "error": f"값을 저장하지 못했습니다 — {e}"}
    if entry:
        edits[name] = entry
    else:
        edits.pop(name, None)
    save_json(EDITS_JSON, edits)
    return {"ok": True, "tag": entry}


@locked_data_write
def _save_tags(p):
    """브라우저의 현재 레이블 전체를 검증해 원자적으로 저장하고 이전 판을 백업한다."""
    raw = p.get("tags")
    if not isinstance(raw, dict):
        return {"ok": False, "error": "tags 누락"}

    clean = {}
    try:
        for name, values in raw.items():
            if not isinstance(name, str) or not isinstance(values, dict):
                raise ValueError("잘못된 레이블 형식")
            entry = _clean_tag({}, values)
            if entry:
                clean[name] = entry
    except (TypeError, ValueError, IndexError) as e:
        return {"ok": False, "error": f"레이블 전체를 저장하지 못했습니다 — {e}"}

    backup = None
    old = load_edits()
    if old:
        stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S-%f")
        backup = DATA / "backups" / f"edits-{stamp}.json"
        save_json(backup, old)
    save_json(EDITS_JSON, clean)
    return {"ok": True, "count": len(clean),
            "backup": str(backup.relative_to(ROOT)) if backup else None}


@locked_data_write
def _save_plot_layout(p):
    """플롯에서 선택한 수동 합치기·분리 규칙을 검증해 저장한다."""
    groups, separate, order = p.get("groups") or [], p.get("separate") or [], p.get("order") or []
    durations, sections = p.get("durations") or {}, p.get("sections") or []
    assignments = p.get("section_assignments") or {}
    caption_positions = p.get("caption_positions") or {}
    media_positions = p.get("media_positions") or {}
    # 이미 열려 있던 구버전 콘티 탭이 저장해도 새 효과 설정을 지우지 않는다.
    effects = (p.get("effects") if "effects" in p else
               (load_json(PLOT_LAYOUT_JSON, {}).get("effects") or {})) or {}
    section_starts = p.get("section_starts") or {}
    section_lyrics = p.get("section_lyrics") or {}
    fit_modes = p.get("fit_modes") or {}
    layouts = p.get("layouts") or {}
    final_end = p.get("final_end")
    if (not isinstance(groups, list) or not isinstance(separate, list) or
            not isinstance(order, list) or not isinstance(durations, dict) or
            not isinstance(sections, list) or not isinstance(assignments, dict) or
            not isinstance(caption_positions, dict) or not isinstance(section_starts, dict) or
            not isinstance(media_positions, dict) or not isinstance(effects, dict) or
            not isinstance(section_lyrics, dict) or not isinstance(fit_modes, dict) or
            not isinstance(layouts, dict)):
        return {"ok": False, "error": "잘못된 플롯 구성"}
    clean_groups, occupied = [], set()
    for group in groups:
        if not isinstance(group, list):
            return {"ok": False, "error": "잘못된 합치기 목록"}
        names = [str(x) for x in group if str(x)]
        if len(names) < 2:
            return {"ok": False, "error": "한 화면에는 2장 이상을 선택해야 합니다"}
        if len(set(names)) != len(names) or occupied.intersection(names):
            return {"ok": False, "error": "한 파일이 여러 묶음에 중복됐습니다"}
        clean_groups.append(names); occupied.update(names)
    clean_sep = list(dict.fromkeys(str(x) for x in separate if str(x) and str(x) not in occupied))
    clean_order = list(dict.fromkeys(str(x) for x in order if str(x)))
    clean_durations = {}
    try:
        for key, value in durations.items():
            sec = round(float(value), 2)
            if str(key) and 0.2 <= sec <= 60:
                clean_durations[str(key)] = sec
    except (TypeError, ValueError):
        return {"ok": False, "error": "슬라이드 시간은 0.2~60초 숫자로 입력해주세요"}
    clean_sections = []
    for i, section in enumerate(sections):
        if not isinstance(section, dict):
            return {"ok": False, "error": "추가 섹션을 확인해주세요"}
        clean = {"id": str(section.get("id") or f"custom-{i}"),
                 "title": str(section.get("title") or "새 섹션").strip() or "새 섹션",
                 "lyric": str(section.get("lyric") or "").strip()}
        if str(section.get("start") or ""):
            clean["start"] = str(section["start"])
        else:
            try:
                at = round(float(section.get("at")), 2)
            except (TypeError, ValueError):
                return {"ok": False, "error": "빈 섹션의 시작 시간을 확인해주세요"}
            if not 0 <= at <= 36000:
                return {"ok": False, "error": "빈 섹션 시작 시간은 0초 이상이어야 합니다"}
            clean["at"] = at
        clean_sections.append(clean)
    clean_assignments = {str(key): str(value) for key, value in assignments.items()
                         if str(key) and str(value)}
    clean_caption_positions = {}
    try:
        for key, value in caption_positions.items():
            if isinstance(value, list) and len(value) == 2:
                x, y = float(value[0]), float(value[1])
                if 0 <= x <= 1 and 0 <= y <= 1:
                    clean_caption_positions[str(key)] = [round(x, 4), round(y, 4)]
    except (TypeError, ValueError):
        return {"ok": False, "error": "글귀 위치 좌표를 확인해주세요"}
    clean_media_positions = {}
    try:
        for key, value in media_positions.items():
            if isinstance(value, list) and len(value) == 2:
                x, y = float(value[0]), float(value[1])
                if 0 <= x <= 1 and 0 <= y <= 1:
                    clean_media_positions[str(key)] = [round(x, 4), round(y, 4)]
    except (TypeError, ValueError):
        return {"ok": False, "error": "사진·영상 화면 위치 좌표를 확인해주세요"}
    clean_section_starts = {}
    try:
        for key, value in section_starts.items():
            sec = round(float(value), 2)
            if str(key) and 0 <= sec <= 36000:
                clean_section_starts[str(key)] = sec
    except (TypeError, ValueError):
        return {"ok": False, "error": "섹션 시작 시간은 초 단위 숫자로 입력해주세요"}
    clean_section_lyrics = {str(key): str(value).strip()[:500]
                            for key, value in section_lyrics.items()
                            if str(key) and str(value).strip()}
    clean_fit_modes = {str(key): str(value) for key, value in fit_modes.items()
                       if str(key) and value in ("pillarbox", "cover")}
    clean_effects = {str(key): str(value) for key, value in effects.items()
                     if str(key) and value in ("none", "zoom_in")}
    clean_layouts = {str(key): str(value) for key, value in layouts.items()
                     if str(key) and re.fullmatch(
                         r"(?:row2|col2|row3|col3|hero_left3|hero_right3|grid4|row4|col4|grid\d+x\d+|row\d+|col\d+)",
                         str(value))}
    try:
        clean_final_end = round(float(final_end), 2) if final_end is not None else None
    except (TypeError, ValueError):
        return {"ok": False, "error": "영상 종료 시간을 확인해주세요"}
    if clean_final_end is not None and not 0.2 <= clean_final_end <= 36000:
        return {"ok": False, "error": "영상 종료 시간은 0.2초 이상이어야 합니다"}
    save_json(PLOT_LAYOUT_JSON, {"groups": clean_groups, "separate": clean_sep,
                                 "order": clean_order, "durations": clean_durations,
                                 "sections": clean_sections,
                                 "section_assignments": clean_assignments,
                                 "caption_positions": clean_caption_positions,
                                 "media_positions": clean_media_positions,
                                 "effects": clean_effects,
                                 "section_starts": clean_section_starts,
                                 "section_lyrics": clean_section_lyrics,
                                 "fit_modes": clean_fit_modes,
                                 "layouts": clean_layouts,
                                 "final_end": clean_final_end})
    return {"ok": True, "groups": len(clean_groups), "separate": len(clean_sep),
            "order": len(clean_order), "durations": len(clean_durations),
            "sections": len(clean_sections), "assignments": len(clean_assignments)}


# ------------------------------------------------------------ 챕터 · 음악

def load_chapters() -> dict:
    c = load_json(CHAPTERS_JSON, {})
    mode = c.get("group_mode")
    return {"target_sec": int(c.get("target_sec") or DEFAULT_TARGET_SEC),
            "width": int(c.get("width") or FRAME_DEFAULT[0]),
            "height": int(c.get("height") or FRAME_DEFAULT[1]),
            "max_upscale": float(c.get("max_upscale") or MAX_UPSCALE),
            "group_mode": mode if mode in GROUP_MODES else "auto",
            "chapters": [x for x in c.get("chapters", []) if isinstance(x, dict)]}


def load_music() -> dict:
    m = load_json(MUSIC_JSON, {})
    return {"file": m.get("file") or "", "bpm": float(m.get("bpm") or 0),
            "offset": float(m.get("offset") or 0),
            "sections": [x for x in m.get("sections", []) if isinstance(x, dict)]}


def load_music_lyrics() -> list[dict]:
    """음원에서 자동 추출한 가사 타이밍. 정확도는 콘티에서 사람이 검토한다."""
    raw = load_json(MUSIC_LYRICS_JSON, {})
    out = []
    for seg in raw.get("segments") or []:
        try:
            start, end = round(float(seg.get("start")), 2), round(float(seg.get("end")), 2)
        except (TypeError, ValueError):
            continue
        text = str(seg.get("text") or "").strip()
        if not text or text == "음악" or end <= start:
            continue
        if text == "힘들 때도 있지만 그래도 아름다워":
            split_at = next((round(float(w["start"]), 2) for w in seg.get("words", [])
                             if str(w.get("word") or "").strip() == "그래도"), 181.36)
            confidence = round(float(seg.get("avg_logprob") or -1), 3)
            out.extend([
                {"from": start, "to": split_at, "text": "힘들 때도 있지만",
                 "confidence": confidence, "review": True},
                {"from": split_at, "to": end, "text": "그래도 아름다워",
                 "confidence": confidence, "review": True},
            ])
            continue
        out.append({"from": start, "to": end, "text": text,
                    "confidence": round(float(seg.get("avg_logprob") or -1), 3),
                    "review": True})
    # 이미 저장된 lyric-XX 섹션 ID는 그대로 유지하면서, 긴 구절만 하위 ID로
    # 나눈다. 그래야 뒤쪽 섹션의 시작 시간·가사 수정값·카드 배치가 밀리지 않는다.
    split_out = []
    for i, row in enumerate(out):
        section_id = f"lyric-{i:02d}"
        if row["text"] == "밤새 아파 울음 그치지 않는 날은 한없이 한없이 다 들어가고":
            boundary = 58.24
            split_out.extend([
                {**row, "to": boundary, "text": "밤새 아파 울음 그치지 않는 날은",
                 "section_id": section_id},
                {**row, "from": boundary, "text": "한없이 한없이 다 들어가고",
                 "section_id": section_id + "b"},
            ])
        elif row["text"] == "Oh my baby 놀라운 세상 내가 바뀌어진 하루 너 우리에게 온 날부터":
            first_end, second_end = 68.48, 71.64
            split_out.extend([
                {**row, "to": first_end, "text": "Oh my baby 놀라운 세상",
                 "section_id": section_id},
                {**row, "from": first_end, "to": second_end, "text": "내가 바뀌어진 하루",
                 "section_id": section_id + "b"},
                {**row, "from": second_end, "text": "너 우리에게 온 날부터",
                 "section_id": section_id + "c"},
            ])
        else:
            split_out.append({**row, "section_id": section_id})
    return split_out


@locked_data_write
def _save_chapters(p):
    """영상 챕터 목록 저장 — 제목/기간/목표 길이가 영상의 뼈대가 된다."""
    out = []
    for c in p.get("chapters") or []:
        title = str(c.get("title") or "").strip()
        frm, to = norm_datetime(c.get("from") or ""), norm_datetime(c.get("to") or "")
        if not title or not frm or not to:
            return {"ok": False, "error": f"챕터 '{title or '(제목 없음)'}' 의 제목·기간을 확인해주세요"}
        frm, to = frm[:10], to[:10]
        if to < frm:
            return {"ok": False, "error": f"'{title}' 의 기간이 거꾸로입니다 ({frm} → {to})"}
        out.append({"title": title, "from": frm, "to": to,
                    "sec": max(1, int(c.get("sec") or 30)),
                    "mood": str(c.get("mood") or "").strip(),
                    "note": str(c.get("note") or "").strip()})
    out.sort(key=lambda c: c["from"])
    cur = load_chapters()
    mode = p.get("group_mode", cur["group_mode"])
    data = {"target_sec": max(10, int(p.get("target_sec") or DEFAULT_TARGET_SEC)),
            "width": max(320, int(p.get("width") or cur["width"])),
            "height": max(320, int(p.get("height") or cur["height"])),
            "max_upscale": max(1.0, min(3.0, float(p.get("max_upscale") or cur["max_upscale"]))),
            "group_mode": mode if mode in GROUP_MODES else "auto",
            "chapters": out}
    save_json(CHAPTERS_JSON, data)
    return {"ok": True, "chapters": len(out)}


@locked_data_write
def _save_music(p):
    """배경음악의 BPM·첫 박 위치·후렴 구간. 컷을 박자에 맞추는 데 쓴다."""
    secs = []
    for s in p.get("sections") or []:
        try:
            a, b = round(float(s.get("from")), 2), round(float(s.get("to")), 2)
        except (TypeError, ValueError):
            return {"ok": False, "error": "후렴 구간은 '48-80' 처럼 초 단위로 적어주세요"}
        if b > a:
            secs.append({"name": str(s.get("name") or "chorus").strip() or "chorus",
                         "from": a, "to": b})
    try:
        data = {"file": str(p.get("file") or "").strip(),
                "bpm": round(max(0.0, float(p.get("bpm") or 0)), 2),
                "offset": round(max(0.0, float(p.get("offset") or 0)), 3),
                "sections": sorted(secs, key=lambda s: s["from"])}
    except (TypeError, ValueError):
        return {"ok": False, "error": "BPM·오프셋은 숫자로 적어주세요"}
    save_json(MUSIC_JSON, data)
    return {"ok": True}


def cmd_bundle(args):
    """원본 없이 썸네일만으로 굴러가는 가벼운 정적 번들을 만든다.

    포트를 못 여는 환경에서 가족에게 공유할 때 쓴다. dist/ 폴더째 어디든
    (정적 호스팅·USB·에어드롭) 올리면 되고, 서버가 필요 없다.
    영상/모션 클립은 기본으로 빼고, --with-video / --with-motion 으로 넣는다.
    '비공개'로 표시한 사진은 남에게 보여줄 번들이므로 기본으로 뺀다.
    """
    dist = ROOT / args.out
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    summaries = load_json(SUMMARY_JSON, {})
    notes = load_json(NOTES_JSON, {})
    edits = load_edits()
    bday = birthday(notes)

    hidden = [m for m in items if edits.get(m["file"], {}).get("private")]
    if hidden and not args.with_private:
        items = [m for m in items if not edits.get(m["file"], {}).get("private")]

    if dist.exists():
        shutil.rmtree(dist)
    (dist / "gallery").mkdir(parents=True)
    shutil.copytree(THUMBS, dist / "gallery" / "thumbs")
    if hidden and not args.with_private:
        # 페이지에서 빠져도 썸네일 파일이 남으면 주소만 알면 보인다 — 같이 지운다
        for m in hidden:
            stem = re.sub(r"[^A-Za-z0-9._-]", "_", m["file"])
            for p in (dist / "gallery" / "thumbs").glob(f"*_{stem}.jpg"):
                p.unlink()

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
                   out=dist, lite=True, keep=keep, edits=edits)

    total = sum(p.stat().st_size for p in dist.rglob("*") if p.is_file())
    print(f"bundle: {dist.relative_to(ROOT)}/  ({total / 1e6:.1f}MB, 파일 "
          f"{sum(1 for p in dist.rglob('*') if p.is_file())}개)")
    print(f"  · 사진 {sum(1 for m in items if m['kind'] == 'image')}장은 썸네일({args.size}px)로 들어갔습니다")
    if not args.with_video:
        print("  · 영상은 포스터만 — 넣으려면 --with-video (원본 218MB)")
    if not args.with_motion:
        print("  · 모션 클립 제외 — 넣으려면 --with-motion (58MB)")
    if hidden:
        print(f"  · 비공개 {len(hidden)}장 " + ("포함됨 (--with-private)" if args.with_private
                                              else "제외 — 썸네일까지 뺐습니다"))
    print(f"  · 확인: open {dist.relative_to(ROOT)}/index.html")


# ------------------------------------------------------------------- 영상 계획

def _draft_chapters(items, notes, target_sec=DEFAULT_TARGET_SEC, n=6) -> list[dict]:
    """사진이 몰려 있는 정도에 맞춰 챕터 초안을 만든다.

    재료가 비슷하게 들어가도록 '날짜'가 아니라 '컷 수'로 균등 분할하고,
    그 구간에 적어둔 메모가 있으면 제목으로 쓴다.
    """
    from collections import Counter
    counts = Counter((m.get("taken_local") or "")[:10] for m in items if m.get("taken_local"))
    counts.pop("", None)
    days = sorted(counts)
    if not days:
        return []
    bday = birthday(notes)
    total = sum(counts.values())
    per = total / max(1, min(n, len(days)))

    groups, cur, acc = [], [], 0
    for d in days:
        cur.append(d)
        acc += counts[d]
        if acc >= per and len(groups) < n - 1:
            groups.append(cur)
            cur, acc = [], 0
    if cur:
        groups.append(cur)

    out = []
    for i, g in enumerate(groups):
        memo = next((notes.get("days", {}).get(d) for d in g if notes.get("days", {}).get(d)), None)
        if memo:                       # '긴 설명 — 짧은 말' 이면 짧은 쪽을 제목으로
            memo = min(re.split(r"\s*[—–]\s*", memo), key=len).strip() or memo
        age = age_label(g[len(g) // 2], bday) or ""
        age = age.split("·")[-1].strip() if "·" in age else age
        cuts = sum(counts[d] for d in g)
        out.append({"title": memo or (f"{age} 무렵" if age else f"{i + 1}부"),
                    "from": g[0], "to": g[-1],
                    "sec": max(10, round(target_sec * cuts / total)),
                    "mood": MOODS[i % len(MOODS)], "note": ""})
    return out


def cmd_chapters(args):
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    notes = load_json(NOTES_JSON, {})
    conf = load_chapters()
    # 화면 설정만 바꾸는 경우 (챕터는 그대로 둔다)
    screen = {k: v for k, v in (("group_mode", args.mode), ("max_upscale", args.max_upscale))
              if v is not None}
    if args.size:
        m = re.match(r"\s*(\d+)\s*[x×*]\s*(\d+)\s*$", args.size)
        if not m:
            sys.exit("chapters: --size 는 1920x1080 처럼 적어주세요")
        screen["width"], screen["height"] = int(m.group(1)), int(m.group(2))
    if screen:
        r = _save_chapters({**conf, **screen})
        if not r["ok"]:
            sys.exit("chapters: " + r["error"])
        conf = load_chapters()
        print(f"chapters: 화면 {conf['width']}×{conf['height']} · 최대 확대 "
              f"{conf['max_upscale']}배 · 묶기 {conf['group_mode']}")
    if args.init or not conf["chapters"]:
        draft = _draft_chapters(items, notes, args.target or conf["target_sec"], args.count)
        if not args.init:
            print("chapters: data/chapters.json 이 아직 없습니다 — 아래는 초안입니다")
        else:
            _save_chapters({"target_sec": args.target or conf["target_sec"], "chapters": draft})
            print(f"chapters: 초안 {len(draft)}개를 {CHAPTERS_JSON.relative_to(ROOT)} 에 저장했습니다")
        conf = {"target_sec": args.target or conf["target_sec"], "chapters": draft}
    total = sum(c["sec"] for c in conf["chapters"])
    print(f"  목표 {conf['target_sec']}초 / 챕터 합계 {total}초")
    for c in conf["chapters"]:
        print(f"  · {c['from']} ~ {c['to']}  {c['sec']:>3}초  {c['mood'] or '-':<6} {c['title']}")
    if not args.init:
        print("  · 갤러리 [🎞 챕터·음악] 에서 고치거나 `jiho.py chapters --init` 로 저장하세요")


def cmd_music(args):
    m = load_music()
    if args.file is not None:
        m["file"] = args.file
    if args.bpm is not None:
        m["bpm"] = args.bpm
    if args.offset is not None:
        m["offset"] = args.offset
    if args.chorus is not None:
        m["sections"] = [{"name": "chorus", "from": a, "to": b}
                         for a, b in _parse_ranges(args.chorus)]
    r = _save_music(m)
    if not r["ok"]:
        sys.exit("music: " + r["error"])
    beat = 60.0 / m["bpm"] if m["bpm"] else 0
    print(f"music: {m['file'] or '(파일 미지정)'}  BPM {m['bpm'] or '-'}  첫 박 {m['offset']}초")
    if beat:
        print(f"  · 1박 {beat:.3f}초 — 꼭 {BEATS[2]}박({BEATS[2] * beat:.1f}초) / "
              f"보통 {BEATS[1]}박({BEATS[1] * beat:.1f}초)")
    else:
        print(f"  · BPM 을 넣으면 컷이 박자에 맞습니다. 지금은 {FALLBACK_SEC[2]}/{FALLBACK_SEC[1]}초 고정")
    for s in m["sections"]:
        print(f"  · {s['name']} {s['from']}~{s['to']}초 — 이 구간은 컷을 절반 길이로 몰아칩니다")


def _parse_ranges(text: str) -> list[tuple[float, float]]:
    """'48-80, 140-172' → [(48,80),(140,172)]"""
    out = []
    for part in re.split(r"[,;]", text or ""):
        m = re.match(r"\s*([\d.]+)\s*[-~]\s*([\d.]+)\s*$", part)
        if m:
            a, b = float(m.group(1)), float(m.group(2))
            if b > a:
                out.append((a, b))
    return out


def _in_chorus(t: float, music) -> bool:
    return any(s["from"] <= t < s["to"] for s in music["sections"])


def _disp_size(m) -> tuple[int, int]:
    """화면에 보이는 크기. EXIF orientation 5~8 은 가로/세로가 뒤집혀 저장된다."""
    w, h = m.get("width") or 0, m.get("height") or 0
    if m["kind"] == "image" and (m.get("orientation") or 1) in (5, 6, 7, 8):
        w, h = h, w
    if int(m.get("_rotation") or 0) % 180:
        w, h = h, w
    return w, h


def _fit(m, cell, frame) -> tuple[float, float]:
    """이 칸을 꽉 채울 때 (늘려야 하는 배율, 사진이 안 잘리고 남는 넓이 비율)."""
    w, h = _disp_size(m)
    cw, ch = frame[0] * cell[2], frame[1] * cell[3]
    if not w or not h:
        return 1.0, 1.0
    s = max(cw / w, ch / h)                       # 칸을 덮는 배율
    keep = min(1.0, (cw / s) / w) * min(1.0, (ch / s) / h)
    return s, keep


def _cells_for(ms, n, frame) -> tuple[str, list]:
    """세로 사진이 많으면 옆으로 나란히, 가로 사진뿐이면 위아래로 쌓는다."""
    if n >= 5:
        # 7장 이상도 16:9 안에 모두 들어가도록 화면비를 고려한 자동 격자.
        cols = max(1, math.ceil(math.sqrt(n * frame[0] / frame[1])))
        rows = math.ceil(n / cols)
        cells = [(col / cols, row / rows, 1 / cols, 1 / rows)
                 for row in range(rows) for col in range(cols)][:n]
        return f"grid{cols}x{rows}", cells
    port = sum(1 for m in ms if _disp_size(m)[1] > _disp_size(m)[0])
    name = ("row2" if port * 2 >= len(ms) else "col2") if n == 2 else "row3" if n == 3 else "grid4"
    return name, CELLS[name]


def _layout_candidates(n, frame) -> list[tuple[str, str, list]]:
    """합친 화면에서 사용자가 고를 수 있는 16:9 배치 후보."""
    if n == 2:
        names = [("row2", "좌우 2분할"), ("col2", "위아래 2분할")]
    elif n == 3:
        names = [("row3", "가로 3분할"), ("col3", "세로 3분할"),
                 ("hero_left3", "왼쪽 크게 + 오른쪽 2장"),
                 ("hero_right3", "오른쪽 크게 + 왼쪽 2장")]
    elif n == 4:
        names = [("grid4", "2×2 격자"), ("row4", "가로 4분할"),
                 ("col4", "세로 4분할")]
    else:
        cols = max(1, math.ceil(math.sqrt(n * frame[0] / frame[1])))
        rows = math.ceil(n / cols)
        grid = [(col / cols, row / rows, 1 / cols, 1 / rows)
                for row in range(rows) for col in range(cols)][:n]
        return [(f"grid{cols}x{rows}", f"{cols}×{rows} 격자", grid),
                (f"row{n}", f"가로 {n}분할", [(i / n, 0, 1 / n, 1) for i in range(n)]),
                (f"col{n}", f"세로 {n}분할", [(0, i / n, 1, 1 / n) for i in range(n)])]
    return [(name, label, CELLS[name]) for name, label in names]


def _apply_layout_overrides(units, choices, frame):
    """콘티 카드에서 고른 합친 화면 배치를 자동 배치보다 우선한다."""
    for unit in units:
        if unit.get("n", 1) < 2:
            continue
        key = "|".join(x[0]["file"] for x in unit["items"])
        wanted = str((choices or {}).get(key) or "")
        candidate = next((x for x in _layout_candidates(unit["n"], frame)
                          if x[0] == wanted), None)
        if candidate:
            unit["layout"], unit["cells"] = candidate[0], candidate[2]
    return units


def _needs_group(m, e, frame, max_up, mode) -> str:
    """이 컷을 다른 컷과 묶어야 하는 이유 (없으면 '')."""
    if mode == "off" or m["kind"] != "image" or m.get("motion") or e.get("solo"):
        return ""
    up, keep = _fit(m, CELLS["full"][0], frame)
    if up > max_up:
        return f"해상도 부족({up:.2f}배 확대)"
    if mode == "fill" and keep < KEEP_MIN and e.get("pick") != 2:
        return f"화면에 채우면 {round((1 - keep) * 100)}% 잘림"
    return ""


def _chunk_run(run, frame, max_up, mode="auto"):
    """묶어야 할 컷들을 2~4장씩 나눈다.

    해상도 때문에 묶는 것(auto)이면 되도록 적게 묶어 크게 보이도록 하고,
    화면을 채우려고 묶는 것(fill)이면 사진이 가장 덜 잘리는 장수를 고른다.
    """
    out, i = [], 0
    while i < len(run):
        best, best_keep = None, -1.0
        for n in (2, 3, 4):
            if i + n > len(run):
                break
            ms = [x[0] for x in run[i:i + n]]
            _, cells = _cells_for(ms, n, frame)
            fits = [_fit(m, c, frame) for m, c in zip(ms, cells)]
            if any(up > max_up for up, _k in fits):
                continue
            keep = sum(k for _u, k in fits) / n
            if mode != "fill":
                best = n                       # 조건만 맞으면 가장 적게 묶는다
                break
            if keep > best_keep + 0.08:        # 눈에 띄게 덜 잘릴 때만 더 묶는다
                best, best_keep = n, keep
        if best is None:                       # 4장으로도 안 되면 있는 만큼 묶는다
            best = min(4, len(run) - i)
        if best < 2:                           # 혼자 남으면 그냥 단독으로
            out.append(run[i:i + 1])
            i += 1
            continue
        out.append(run[i:i + best])
        i += best
    # 마지막에 한 장만 남았으면 앞 묶음에 붙여본다 — 붙여서 더 잘리면 그냥 둔다
    if len(out) >= 2 and len(out[-1]) == 1 and len(out[-2]) < 4:
        merged = out[-2] + out[-1]
        up, keep = _chunk_quality(merged, frame)
        was = (_chunk_quality(out[-2], frame)[1] * len(out[-2])
               + _chunk_quality(out[-1], frame)[1]) / len(merged)
        if up <= max_up and keep >= was:
            out.pop()
            out[-1] = merged
    return out


def _chunk_quality(chunk, frame) -> tuple[float, float]:
    """이 묶음의 (가장 큰 확대 배율, 평균으로 남는 넓이)."""
    ms = [x[0] for x in chunk]
    n = len(ms)
    _, cells = ("full", CELLS["full"]) if n == 1 else _cells_for(ms, n, frame)
    fits = [_fit(m, c, frame) for m, c in zip(ms, cells)]
    return max(u for u, _k in fits), sum(k for _u, k in fits) / n


def _make_units(group, frame, max_up, mode, warn):
    """컷 목록을 '한 화면' 단위로 묶는다. 묶이지 않은 것은 혼자 한 화면."""
    units, run = [], []

    def flush():
        if not run:
            return
        for chunk in _chunk_run(run, frame, max_up, mode):
            if len(chunk) == 1:
                units.append(_unit([chunk[0]], frame, max_up))
            else:
                units.append(_unit(chunk, frame, max_up))
        run.clear()

    for x in group:
        m, e, pick, _ = x
        why = _needs_group(m, e, frame, max_up, mode)
        if why:
            run.append(x)
        else:
            flush()
            units.append(_unit([x], frame, max_up))
    flush()

    # 묶은 뒤에도 늘려야 하는 칸이 남으면 알려준다 (혼자 남았거나 너무 작거나)
    for u in units:
        for (m, e, _p, _d), cell in zip(u["items"], u["cells"]):
            up = _fit(m, cell, frame)[0]
            if up > max_up and m["kind"] == "image":
                w, h = _disp_size(m)
                warn.append(f"{'묶어도 ' if u['n'] > 1 else ''}해상도가 모자랍니다: "
                            f"{m['file']} ({w}×{h}, {up:.2f}배 확대)")
    return units


def _montage_silent_newborn(units, bday, frame, max_up, separate=None):
    """D+0~30의 자막 없는 연속 사진을 2~6장 성장 몽타주로 묶는다."""
    if not bday:
        return units
    separate = set(separate or [])
    out, run = [], []

    def eligible(u):
        if u["n"] != 1:
            return False
        m, e, pick, day = u["items"][0]
        if (m["file"] in separate or m["kind"] != "image" or m.get("motion") or
                pick == 2 or e.get("short")):
            return False
        try:
            age = (dt.date.fromisoformat(day) - bday).days
        except (TypeError, ValueError):
            return False
        return 0 <= age <= 30

    def flush():
        nonlocal run
        while len(run) >= 2:
            remain = len(run)
            n = remain if remain <= 6 else (5 if remain - 6 == 1 else 6)
            chunk, run = run[:n], run[n:]
            out.append(_unit([u["items"][0] for u in chunk], frame, max_up))
        out.extend(run)
        run = []

    prev_day = None
    for u in units:
        if not eligible(u):
            flush(); out.append(u); prev_day = None
            continue
        day = dt.date.fromisoformat(u["items"][0][3])
        if prev_day is not None and (day - prev_day).days > 2:
            flush()
        run.append(u); prev_day = day
    flush()
    return out


def _apply_manual_groups(units, groups, frame, max_up):
    """플롯에서 사용자가 합친 파일 묶음을 자동 구성보다 우선 적용한다."""
    group_of = {name: tuple(group) for group in groups for name in group}
    item_of = {x[0]["file"]: x for u in units for x in u["items"]}
    emitted, out = set(), []
    for u in units:
        names = [x[0]["file"] for x in u["items"]]
        manual = next((group_of[n] for n in names if n in group_of), None)
        if not manual:
            out.append(u); continue
        if manual in emitted:
            continue
        items = [item_of[n] for n in manual if n in item_of]
        if len(items) >= 2:
            out.append(_unit(items, frame, max_up)); emitted.add(manual)
        else:
            out.append(u)
    return out


def _unit(items, frame, max_up) -> dict:
    n = len(items)
    ms = [x[0] for x in items]
    layout, cells = ("full", CELLS["full"]) if n == 1 else _cells_for(ms, n, frame)
    kind = (("motion" if ms[0].get("motion") else ms[0]["kind"])
            if n == 1 else "collage")
    return {"items": items, "n": n, "layout": layout, "cells": cells, "kind": kind,
            "pick": max(x[2] for x in items)}


def _clip_seconds(m, e) -> float:
    """영상에서 실제로 재생할 길이 — 구간을 안 잡았으면 앞부분을 조금만."""
    clip = e.get("clip")
    if clip:
        return round(clip[1] - clip[0], 2)
    return round(min(CLIP_MAX_SEC, m.get("duration_sec") or CLIP_MAX_SEC), 2)


def _motion_seconds(m) -> float:
    """Use the full short Motion Photo clip in the final movie."""
    return round(min(CLIP_MAX_SEC, m.get("motion_duration_sec") or 3.0), 2)


def _cut_seconds(m, e, pick, beat, chorus, stretch=1.0) -> float:
    """이 컷이 화면에 머무는 시간.

    사진은 박자에 맞춰 머물고(후렴에서는 절반), 영상은 잡아둔 구간 길이를 그대로
    쓰되 다음 컷이 박에서 밀리지 않도록 박 단위로 올림한다.
    """
    if m["kind"] == "video" or m.get("motion"):
        dur = _motion_seconds(m) if m.get("motion") else _clip_seconds(m, e)
        return round(math.ceil(dur / beat) * beat, 3) if beat else round(dur, 2)
    n = (BEATS_CHORUS if chorus else BEATS)[pick]
    if beat:
        return round(max(1, round(n * stretch)) * beat, 3)
    return round(FALLBACK_SEC[pick] * (0.5 if chorus else 1.0) * stretch, 3)


def _unit_seconds(u, beat, chorus, stretch=1.0) -> float:
    """한 화면이 머무는 시간. 여러 장을 묶은 화면은 읽을 시간을 더 준다."""
    m, e, pick, _ = u["items"][0]
    base = _cut_seconds(m, e, u["pick"], beat, chorus, stretch)
    if u["n"] == 1:
        return base
    moving = [x for x in u["items"] if x[0]["kind"] == "video" or x[0].get("motion")]
    if moving:
        # 한 화면에 움직이는 타일이 있으면 가장 긴 클립이 끝날 때까지 유지한다.
        return max(_cut_seconds(x[0], x[1], x[2], beat, chorus, stretch) for x in moving)
    mult = (GROUP_BEATS[u["n"]] if u["n"] in GROUP_BEATS else
            min(8.0, 3.0 + 0.35 * math.sqrt(u["n"] - 6)))
    if beat:
        return round(max(1, round(base / beat * mult)) * beat, 3)
    return round(base * mult, 3)


def _layout(units, t0, beat, music, stretch=1.0):
    """컷들을 시간축에 늘어놓는다. 후렴에 걸리는지는 그 컷의 시작 시각으로 정한다."""
    t, durs = t0, []
    for u in units:
        dur = _unit_seconds(u, beat, _in_chorus(t - music["offset"], music), stretch)
        durs.append(dur)
        t = round(t + dur, 3)
    return durs, round(t - t0, 3)


def cmd_plan(args):
    """태그 + 챕터 + 음악을 합쳐 '몇 번째 컷을 몇 초씩' 까지 계산한다."""
    meta = load_json(META_JSON, {"items": []})
    items = apply_overrides(meta["items"])
    summaries = load_json(SUMMARY_JSON, {})
    notes = load_json(NOTES_JSON, {})
    edits = load_edits()
    bday = birthday(notes)
    conf, music = load_chapters(), load_music()
    lyrics = load_music_lyrics() if music.get("file") else []
    plot_layout = load_json(PLOT_LAYOUT_JSON, {"groups": [], "separate": [], "order": [],
                                                "durations": {}, "sections": [],
                                                "section_assignments": {},
                                                "caption_positions": {},
                                                "media_positions": {},
                                                "effects": {},
                                                "section_starts": {},
                                                "section_lyrics": {},
                                                "fit_modes": {}, "layouts": {}})
    order_rank = {name: i for i, name in enumerate(plot_layout.get("order") or [])}
    beat = 60.0 / music["bpm"] if music["bpm"] else 0
    frame = (conf["width"], conf["height"])

    chapters = conf["chapters"]
    warn = []
    if not chapters:
        chapters = _draft_chapters(items, notes, conf["target_sec"])
        warn.append("chapters.json 이 없어 초안으로 계산했습니다 — [🎞 챕터·음악] 에서 정해주세요")
    if not beat:
        warn.append("음악 BPM 이 없어 컷 길이를 고정값으로 잡았습니다 — `jiho.py music --bpm 92`")

    # 후보 컷: 비공개·제외만 빼고 전부. 미선택은 자동으로 '보통' 취급한다.
    # 날짜를 의도적으로 지운 가족사진은 __end__ 로 두어 마지막 챕터 끝에 붙인다.
    cand, excluded_source = [], []
    for m in items:
        e = edits.get(m["file"], {})
        if e.get("private"):
            continue
        if e.get("pick") == 0:
            excluded_source.append({"file": m["file"], "path": m["path"],
                                    "thumb": os.path.relpath(_thumb_path(m, 480), ROOT).replace(os.sep, "/"),
                                    "kind": "motion" if m.get("motion") else m["kind"],
                                    "caption": e.get("short") or "", "taken": m.get("taken_local") or ""})
            continue
        day = (m.get("taken_local") or "")[:10] or "__end__"
        m = dict(m)
        m["_rotation"] = int(e.get("rotation") or 0)
        cand.append((m, e, e.get("pick") if e.get("pick") is not None else 1, day))

    # 수동으로 합친 묶음은 촬영일 챕터가 달라도 첫 번째 선택 항목의 챕터로
    # 모은다. 그래야 서로 먼 시기의 두 장도 실제 한 unit으로 생성할 수 있다.
    def natural_chapter(day):
        if day == "__end__":
            return len(chapters) - 1
        return next((i for i, chapter in enumerate(chapters)
                     if chapter["from"] <= day <= chapter["to"]), None)

    natural_by_file = {x[0]["file"]: natural_chapter(x[3]) for x in cand}
    forced_chapter = {}
    for manual_group in plot_layout.get("groups") or []:
        anchor = next((name for name in manual_group
                       if natural_by_file.get(name) is not None), None)
        if anchor is None:
            continue
        target = natural_by_file[anchor]
        forced_chapter.update({name: target for name in manual_group
                               if name in natural_by_file})

    used = set()
    out_chapters, t = [], 0.0
    for ch_i, ch in enumerate(chapters):
        group = sorted([x for x in cand
                        if forced_chapter.get(x[0]["file"],
                                              natural_by_file.get(x[0]["file"])) == ch_i],
                       key=lambda x: (0, order_rank[x[0]["file"]])
                       if x[0]["file"] in order_rank else
                       (1, x[0].get("taken_local") or "9999"))
        for x in group:
            used.add(x[0]["file"])
        budget, cstart = float(ch["sec"]), t
        # 해상도가 낮거나 화면에 안 맞는 컷은 2~4장씩 한 화면으로 묶는다
        units = _make_units(group, frame, conf["max_upscale"], conf["group_mode"], warn)
        units = _montage_silent_newborn(units, bday, frame, conf["max_upscale"],
                                        plot_layout.get("separate"))
        units = _apply_manual_groups(units, plot_layout.get("groups") or [], frame,
                                     conf["max_upscale"])
        units = _apply_layout_overrides(units, plot_layout.get("layouts") or {}, frame)
        # '제외'가 아닌 컷은 목표 시간을 넘더라도 절대 자동 탈락시키지 않는다.
        keep = list(units)
        # 남는 시간이 있으면 컷을 조금씩 늘려 메운다 (최대 1.8배)
        durs, total = _layout(keep, cstart, beat, music)
        if total > budget * 1.05:
            warn.append(f"'{ch['title']}' 은 모든 컷을 넣어 목표 {budget:.0f}초보다 "
                        f"{total - budget:.0f}초 길어졌습니다")
        if args.stretch and total and total < budget:
            # 박자에 맞추느라 길이가 '몇 박' 단위로만 늘어난다 —
            # 예산을 넘지 않는 선에서 가장 크게 늘어나는 배율을 고른다
            for s in (1.8, 1.6, 1.5, 1.4, 1.3, 1.25, 1.2, 1.1):
                if s * total > budget * 1.05:
                    continue
                d2, t2 = _layout(keep, cstart, beat, music, s)
                if t2 <= budget * 1.05 and t2 > total:
                    durs, total = d2, t2
                    break

        # 콘티에서 직접 입력한 화면 표시 시간은 자동 박자 계산보다 우선한다.
        manual_durations = plot_layout.get("durations") or {}
        for i, unit in enumerate(keep):
            duration_key = "|".join(x[0]["file"] for x in unit["items"])
            if duration_key in manual_durations:
                durs[i] = round(max(0.2, min(60.0,
                                float(manual_durations[duration_key]))), 2)
        total = round(sum(durs), 3)

        cuts = []
        for u, dur in zip(keep, durs):
            tiles = []
            for (m, e, pick, day), cell in zip(u["items"], u["cells"]):
                cap = e.get("short") or ""
                if (pick == 2 and m["kind"] == "image" and
                        not (e.get("safe") or e.get("focus")) and u["n"] == 1):
                    warn.append(f"필수 영역 없음(★ 꼭): {m['file']}")
                is_motion = bool(m.get("motion"))
                src = (_motion_seconds(m) if is_motion else
                       _clip_seconds(m, e) if m["kind"] == "video" else None)
                up, kept = _fit(m, cell, frame)
                display_day = "" if day == "__end__" else day
                tiles.append({
                    "file": m["file"],
                    "path": m.get("motion") if is_motion else m["path"],
                    "still_path": m["path"] if is_motion else "",
                    "thumb": os.path.relpath(_thumb_path(m, 480), ROOT).replace(os.sep, "/"),
                    "kind": "motion" if is_motion else m["kind"],
                    "motion": m.get("motion") or "", "cell": [round(v, 4) for v in cell],
                    "caption": cap, "pick": pick, "day": display_day,
                    "taken": m.get("taken_local") or "",
                    "age": age_label(display_day, bday) or "",
                    "safe": e.get("safe"), "focus": e.get("focus"), "face": e.get("face") or "",
                    "rotation": int(e.get("rotation") or 0),
                    "people": e.get("people") or [], "tags": e.get("tags") or [],
                    "clip": e.get("clip"), "src_dur": src, "audio": e.get("audio") or "mute",
                    "place": m.get("place") or "",
                    "size": list(_disp_size(m)), "upscale": round(up, 3), "keep": round(kept, 3),
                    # 기본은 긴 쪽 맞춤(전체 보기). 사진별로 콘티에서 변경 가능하다.
                    "fit": ((plot_layout.get("fit_modes") or {}).get(m["file"])
                            if (plot_layout.get("fit_modes") or {}).get(m["file"])
                            in ("pillarbox", "cover") else "pillarbox"),
                    "media_position": (plot_layout.get("media_positions") or {}).get(
                        m["file"], [0.5, 0.5]),
                    "effect": (plot_layout.get("effects") or {}).get(m["file"], "none"),
                })
            first = tiles[0]
            cap = next((x["caption"] for x in tiles if x["pick"] == 2 and x["caption"]),
                       next((x["caption"] for x in tiles if x["caption"]), ""))
            age_nums = [int(m.group(1)) for x in tiles
                        if (m := re.match(r"D\+(\d+)", x.get("age") or ""))]
            cut_age = first["age"]
            if len(set(age_nums)) > 1:
                cut_age = f"D+{min(age_nums)}–{max(age_nums)}"
            cut_key = "|".join(x["file"] for x in tiles)
            cut_lyrics = [x for x in lyrics if x["from"] < t + dur and x["to"] > t]
            cuts.append({
                "at": round(t, 3), "dur": dur, "kind": u["kind"], "layout": u["layout"],
                "n": u["n"], "pick": u["pick"], "caption": cap,
                "day": first["day"], "age": cut_age, "place": first["place"],
                "people": sorted({p for x in tiles for p in x["people"]}),
                "tags": sorted({g for x in tiles for g in x["tags"]}),
                "lyrics": cut_lyrics,
                "caption_position": (plot_layout.get("caption_positions") or {}).get(
                    cut_key, [0.5, 0.86]),
                "beat_aligned": bool(beat) and u["kind"] not in ("video", "motion"),
                "tiles": tiles,
                # 한 장짜리 화면은 편집기가 바로 쓰도록 대표 값을 같이 둔다
                **({"file": first["file"], "path": first["path"], "safe": first["safe"],
                    "focus": first["focus"],
                    "face": first["face"], "clip": first["clip"], "src_dur": first["src_dur"],
                    "rotation": first["rotation"], "audio": first["audio"],
                    "motion": first["motion"], "fit": first["fit"]}
                   if u["n"] == 1 else {}),
            })
            t = round(t + dur, 3)
        out_chapters.append({"title": ch["title"], "from": ch["from"], "to": ch["to"],
                             "mood": ch.get("mood", ""), "target_sec": ch["sec"],
                             "start_sec": round(cstart, 3), "dur_sec": round(t - cstart, 3),
                             "cuts": cuts, "dropped": 0})

    if t < conf["target_sec"] * 0.9:
        warn.append(f"목표 {conf['target_sec']}초보다 {round(conf['target_sec'] - t)}초 짧습니다 — "
                    f"챕터 길이를 줄이거나 컷을 더 골라주세요")
    elif t > conf["target_sec"] * 1.1:
        warn.append(f"제외하지 않은 컷을 모두 넣어 목표보다 "
                    f"{round(t - conf['target_sec'])}초 길어졌습니다")
    orphan = [x[0]["file"] for x in cand if x[0]["file"] not in used]
    if orphan:
        warn.append(f"어느 챕터에도 안 들어간 컷 {len(orphan)}개 — 챕터 기간을 넓혀주세요")
    seen_people = {p for c in out_chapters for cut in c["cuts"] for p in cut["people"]}
    missing = [p for p in roster_of(notes) if p not in seen_people]
    if missing and seen_people:      # 인물 태그를 아예 안 했으면 굳이 알리지 않는다
        warn.append("한 번도 안 나온 사람: " + ", ".join(missing))

    allcuts = [c for ch in out_chapters for c in ch["cuts"]]
    groups = [c for c in allcuts if c["n"] > 1]
    plan = {"generated": dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "title": notes.get("title", ""), "event": notes.get("event_name", ""),
            "target_sec": conf["target_sec"], "total_sec": round(t, 3),
            "cuts": len(allcuts), "photos": sum(c["n"] for c in allcuts),
            "grouped_cuts": len(groups), "grouped_photos": sum(c["n"] for c in groups),
            "frame": {"width": frame[0], "height": frame[1],
                      "max_upscale": conf["max_upscale"], "group_mode": conf["group_mode"]},
            "caption_style": {"font": "fonts/NanumPenScript-Regular.ttf",
                              "family": "NanumPen", "default_position": [0.5, 0.86]},
            "excluded": sorted(excluded_source, key=lambda x: x["taken"] or "9999"),
            "music": music, "lyrics": lyrics,
            "beat_sec": round(beat, 4) if beat else 0,
            "plot_layout": plot_layout,
            "chapters": out_chapters, "warnings": warn}
    save_json(PLAN_JSON, plan)
    _write_plan_md(plan)
    _write_plot_html(plan)

    mm, ss = divmod(int(plan["total_sec"]), 60)
    print(f"plan: {plan['cuts']}화면 / {plan['photos']}컷 / {mm}분 {ss}초  "
          f"(목표 {conf['target_sec']}초)")
    if groups:
        print(f"  · {plan['grouped_photos']}장을 {len(groups)}개 화면에 나눠 담았습니다 "
              f"(해상도·화면비 때문에 — {frame[0]}×{frame[1]}, 모드 {conf['group_mode']})")
    for c in out_chapters:
        print(f"  · {c['dur_sec']:>6.1f}초 {len(c['cuts']):>3}컷  {c['title']}"
              + (f"  [{c['dropped']}컷 뺌]" if c["dropped"] else ""))
    if warn:
        head = warn[:6]
        print(f"  ! 확인할 것 {len(warn)}건")
        for w in head:
            print(f"    - {w}")
        if len(warn) > len(head):
            print(f"    … 나머지 {len(warn) - len(head)}건은 VIDEO_PLAN.md 에 있습니다")
    print(f"  · {PLAN_JSON.relative_to(ROOT)} · VIDEO_PLAN.md · VIDEO_PLOT.html")


def _most_redundant(keep) -> int:
    """뺄 화면 고르기 — 우선순위가 낮고, 앞뒤와 시간상 가장 붙어 있는 것."""
    def ts(u):
        try:
            return dt.datetime.strptime(u["items"][0][0]["taken_local"],
                                        "%Y-%m-%d %H:%M:%S").timestamp()
        except (ValueError, TypeError):
            return 0.0

    worst, worst_key = 0, None
    for i, u in enumerate(keep):
        gaps = [abs(ts(u) - ts(keep[j])) for j in (i - 1, i + 1) if 0 <= j < len(keep)]
        key = (u["pick"], min(gaps) if gaps else 0.0)
        if worst_key is None or key < worst_key:
            worst, worst_key = i, key
    return worst


LAYOUT_LABEL = {"full": "", "row2": "◫ 2장", "row3": "▥ 3장",
                "col2": "⊟ 2장", "grid4": "▦ 4장", "grid6": "▦ 6장"}


def _write_plan_md(plan):
    f = plan["frame"]
    L = [f"# {plan['title']} — {plan['event'] or '영상'} 계획", "",
         f"- 총 {plan['cuts']}화면 / 사진·영상 {plan['photos']}컷 / "
         f"{int(plan['total_sec']) // 60}분 {int(plan['total_sec']) % 60}초 "
         f"(목표 {plan['target_sec']}초)",
         f"- 화면: {f['width']}×{f['height']} · 묶기 {f['group_mode']}"
         + (f" · {plan['grouped_photos']}장을 {plan['grouped_cuts']}개 화면에 나눠 담음"
            if plan["grouped_cuts"] else ""),
         f"- 음악: {plan['music']['file'] or '(미지정)'}"
         + (f" · BPM {plan['music']['bpm']} · 1박 {plan['beat_sec']}초" if plan["beat_sec"]
            else " · BPM 미지정"),
         f"- 생성: {plan['generated']}", ""]
    for c in plan["chapters"]:
        mm, ss = divmod(int(c["start_sec"]), 60)
        L += [f"## {c['title']}  ({mm}:{ss:02d} ~ · {c['dur_sec']:.1f}초 · {len(c['cuts'])}화면)",
              f"> {c['from']} ~ {c['to']}" + (f" · {c['mood']}" if c["mood"] else ""), "",
              "| 시각 | 길이 | 화면 | 자막 | 파일 |", "|---|---|---|---|---|"]
        for cut in c["cuts"]:
            m2, s2 = divmod(int(cut["at"]), 60)
            mark = "★" if cut["pick"] == 2 else ""
            kind = "🎬" if cut["kind"] == "video" else ""
            files = ", ".join(f"`{x['file']}`" for x in cut["tiles"])
            L.append(f"| {m2}:{s2:02d} | {cut['dur']:.1f}s | {LAYOUT_LABEL.get(cut['layout'], '')}"
                     f" | {mark}{kind} {cut['caption'] or '_(없음)_'} | {files} |")
        L.append("")
    if plan["warnings"]:
        L += ["## ⚠︎ 확인할 것", ""] + [f"- {w}" for w in plan["warnings"]] + [""]
    (ROOT / "VIDEO_PLAN.md").write_text("\n".join(L), encoding="utf-8")


def _plot_time(sec) -> str:
    sec = int(float(sec or 0))
    return f"{sec // 60}:{sec % 60:02d}"


def _write_plot_html(plan):
    """영상으로 렌더링하기 전 사람 눈으로 순서·자막·구간을 검토하는 HTML."""
    sections, story_groups, backlog_cards, cut_i = [], [], [], 0
    video_backlog_count = motion_backlog_count = 0
    # 가사 한 구절(Whisper 세그먼트)마다 콘티 섹션 하나. 긴 무가사 틈은 간주로 분리한다.
    song_end = 252.82
    layout_config = plan.get("plot_layout", {}) or {}
    try:
        final_end = max(song_end, float(layout_config.get("final_end") or song_end))
    except (TypeError, ValueError):
        final_end = song_end
    lyric_rows = plan.get("lyrics", [])
    verse_specs = []
    if lyric_rows and lyric_rows[0]["from"] > 0:
        verse_specs.append((0.0, lyric_rows[0]["from"], "전주", "intro", "가사 없음"))
    for i, row in enumerate(lyric_rows):
        next_from = lyric_rows[i + 1]["from"] if i + 1 < len(lyric_rows) else song_end
        long_gap = next_from - row["to"] > 4.0
        lyric_end = row["to"] if long_gap else next_from
        verse_specs.append((row["from"], lyric_end, f"가사 {i + 1:02d}",
                            str(row.get("section_id") or f"lyric-{i:02d}"), row["text"]))
        if long_gap:
            verse_specs.append((row["to"], next_from, "간주", f"gap-{i:02d}", "가사 없음"))
    last_end = lyric_rows[-1]["to"] if lyric_rows else 0
    if last_end < song_end and (not verse_specs or verse_specs[-1][1] < song_end):
        verse_specs.append((last_end, song_end, "후주", "outro", "가사 없음"))
    verse_specs.append((song_end, float("inf"), "음악 추가 필요", "after-music", "가사 없음"))
    custom_sections = [x for x in layout_config.get("sections", []) if isinstance(x, dict)]
    custom_starts = {x.get("start"): x for x in custom_sections if x.get("start")}
    custom_by_id = {str(x.get("id")): x for x in custom_sections}
    assignments = layout_config.get("section_assignments") or {}
    groups_by_id, active_spec, active_group_id = {}, None, None

    def verse_for(at):
        return next((x for x in verse_specs if x[0] <= at < x[1]), verse_specs[-1])

    # 카드를 넣기 전에 모든 기본·사용자 섹션을 먼저 만든다. 카드가 0장이 되어도
    # 섹션은 빈 드롭 영역으로 남아 다시 슬라이드를 받을 수 있어야 한다.
    for spec in verse_specs:
        groups_by_id[spec[3]] = {"spec": spec, "id": spec[3], "title": spec[2],
                                 "lyric": spec[4], "from": spec[0],
                                 "to": final_end if math.isinf(spec[1]) else spec[1],
                                 "sort_at": spec[0], "custom": False, "cards": [],
                                 "keys": [], "slide_sec": 0.0}
    file_times = {tile["file"]: cut["at"] for chapter in plan["chapters"]
                  for cut in chapter["cuts"] for tile in cut["tiles"]}
    for custom in custom_sections:
        custom_id = str(custom.get("id"))
        start_at = (float(custom.get("at")) if custom.get("at") is not None
                    else float(file_times.get(custom.get("start"), final_end)))
        final_end = max(final_end, start_at + .01)
        spec = verse_for(start_at)
        groups_by_id[custom_id] = {"spec": spec, "id": custom_id,
                                   "title": custom.get("title") or "새 섹션",
                                   "lyric": custom.get("lyric") or "가사 없음",
                                   "from": start_at, "to": start_at,
                                   "sort_at": start_at, "custom": True, "cards": [], "keys": [],
                                   "slide_sec": 0.0}

    for ch in plan["chapters"]:
        for cut in ch["cuts"]:
            thumbs = []
            for tile_i, tile in enumerate(cut["tiles"]):
                cell = tile.get("cell") or [0, 0, 1, 1]
                cell_style = (f'left:{cell[0]*100:.4f}%;top:{cell[1]*100:.4f}%;'
                              f'width:{cell[2]*100:.4f}%;height:{cell[3]*100:.4f}%')
                thumbs.append(
                    f'<span class="thumb-cell" style="{cell_style}"><img data-tile="{tile_i}" '
                    f'src="{html.escape(tile.get("thumb") or "", quote=True)}" '
                    f'alt="{html.escape(tile["file"], quote=True)}" loading="lazy"></span>')
            kinds = sorted({x["kind"] for x in cut["tiles"]})
            kind = "motion" if "motion" in kinds else "video" if "video" in kinds else "image"
            regular_video = any(x["kind"] == "video" for x in cut["tiles"])
            files = ", ".join(x["file"] for x in cut["tiles"])
            fit_controls = "".join(
                f'<label><span>{html.escape(tile["file"]) if len(cut["tiles"]) > 1 else "화면 맞춤"}</span>'
                f'<select class="fitMode" data-file="{html.escape(tile["file"], quote=True)}">'
                f'<option value="pillarbox"{" selected" if tile.get("fit") != "cover" else ""}>'
                f'긴 쪽 맞춤 · 전체 보기</option>'
                f'<option value="cover"{" selected" if tile.get("fit") == "cover" else ""}>'
                f'짧은 쪽 맞춤 · 화면 채우기</option></select></label>'
                for tile in cut["tiles"])
            effect_controls = "".join(
                f'<label><span>{html.escape(tile["file"]) if len(cut["tiles"]) > 1 else "사진 움직임"}</span>'
                f'<select class="effectMode" data-file="{html.escape(tile["file"], quote=True)}">'
                f'<option value="none"{" selected" if tile.get("effect") != "zoom_in" else ""}>'
                f'움직임 없음</option>'
                f'<option value="zoom_in"{" selected" if tile.get("effect") == "zoom_in" else ""}>'
                f'천천히 확대 · 6%</option></select></label>'
                for tile in cut["tiles"] if tile.get("kind") == "image")
            badges = ["★ 꼭" if cut["pick"] == 2 else "보통",
                      "LIVE" if kind == "motion" else "영상" if kind == "video" else "사진"]
            if regular_video:
                badges.append("🔊 원본 소리")
            if any(x.get("safe") for x in cut["tiles"]):
                badges.append("필수 영역")
            if any(x.get("clip") for x in cut["tiles"]):
                badges.append("구간 지정")
            if not cut.get("caption"):
                badges.append("자막 없음")
            key = "|".join(x["file"] for x in cut["tiles"])
            layout_control = ""
            if len(cut["tiles"]) > 1:
                options = "".join(
                    f'<option value="{html.escape(name, quote=True)}"'
                    f'{" selected" if name == cut.get("layout") else ""}>'
                    f'{html.escape(label)}</option>'
                    for name, label, _cells in _layout_candidates(
                        len(cut["tiles"]),
                        (int(plan["frame"]["width"]), int(plan["frame"]["height"]))))
                layout_control = (
                    f'<label class="layoutChoice"><span>합친 화면 레이아웃</span>'
                    f'<select class="layoutMode" data-key="{html.escape(key, quote=True)}">'
                    f'{options}</select></label>')
            thumb_cols = max(1, len({round(x["cell"][0], 4) for x in cut["tiles"]}))
            thumb_rows = max(1, len({round(x["cell"][1], 4) for x in cut["tiles"]}))
            thumb_style = (f'grid-template-columns:repeat({thumb_cols},1fr);'
                           f'grid-template-rows:repeat({thumb_rows},1fr)')
            card_html = (
                f'<article class="cut {kind}" data-kind="{kind}" data-i="{cut_i}" '
                f'data-chapter="{html.escape(ch["title"], quote=True)}" '
                f'data-key="{html.escape(key, quote=True)}" data-at="{cut["at"]}">'
                f'<div class="dragGrip" title="잡고 드래그해서 순서 이동">⠿ 순서 이동</div>'
                f'<button class="preview" aria-label="컷 미리보기">'
                f'<span class="num">{cut_i + 1}</span><span class="when">'
                f'{_plot_time(cut["at"])} · {cut["dur"]:.1f}초</span>'
                f'<span class="thumbs n{len(thumbs)}" style="{thumb_style}">{"".join(thumbs)}</span></button>'
                f'<div class="info"><div class="badges">'
                f'{"".join(f"<b>{html.escape(x)}</b>" for x in badges)}</div>'
                f'<h3>{html.escape(cut.get("caption") or "영상 자막 없음")}</h3>'
                f'<p>{html.escape(cut.get("age") or cut.get("day") or "마지막 장면")}</p>'
                f'<small title="{html.escape(files, quote=True)}">{html.escape(files)}</small>'
                f'<label class="timing">표시 시간 <input class="duration" type="number" min="0.2" max="60" step="0.1" value="{cut["dur"]:.2f}">초</label>'
                f'<div class="fitModes">{fit_controls}{effect_controls}</div>{layout_control}'
                f'<button class="excludeOne" type="button">✕ 이 슬라이드 제외</button>'
                f'<div class="arrange"><label class="select"><input class="groupcheck" type="checkbox"> 슬라이드 선택</label>'
                f'<button class="earlier" title="슬라이드를 한 칸 앞으로">← 앞</button>'
                f'<button class="later" title="슬라이드를 한 칸 뒤로">뒤 →</button></div>'
                f'</div></article>')
            spec = verse_for(cut["at"])
            custom = custom_starts.get(cut["tiles"][0]["file"])
            if spec != active_spec:
                active_spec, active_group_id = spec, spec[3]
            if custom:
                active_group_id = str(custom.get("id"))
            target_id = str(assignments.get(key) or active_group_id)
            target_custom = custom_by_id.get(target_id)
            target_spec = next((x for x in verse_specs if x[3] == target_id), spec)
            if target_id not in groups_by_id:
                is_custom = bool(target_custom)
                title = target_custom.get("title") if is_custom else target_spec[2]
                lyric = target_custom.get("lyric") if is_custom else target_spec[4]
                groups_by_id[target_id] = {"spec": target_spec, "id": target_id,
                                           "title": title, "lyric": lyric or "가사 없음",
                                           "from": cut["at"], "to": cut["at"] + cut["dur"],
                                           "sort_at": cut["at"] if is_custom else target_spec[0],
                                           "custom": is_custom, "cards": [], "keys": [],
                                           "slide_sec": 0.0}
            group = groups_by_id[target_id]
            placed = (target_id in ("intro", "lyric-00") or key in assignments or
                      bool(target_custom))
            if placed:
                group["cards"].append(card_html)
                group["keys"].append(key)
                group["slide_sec"] += float(cut["dur"])
                group["from"] = min(group["from"], cut["at"])
                group["to"] = max(group["to"], cut["at"] + cut["dur"])
            else:
                backlog_cards.append((cut["at"], card_html))
                if regular_video:
                    video_backlog_count += 1
                if kind == "motion":
                    motion_backlog_count += 1
            cut_i += 1

    story_groups = sorted(groups_by_id.values(), key=lambda g: g["sort_at"])
    # A lyric section may contain cards originating in different source chapters.
    # The chapter loop above is useful for building the cards, but must not override
    # the order the user explicitly established in the storyboard.
    saved_order_rank = {name: i for i, name in enumerate(layout_config.get("order") or [])}
    for group in story_groups:
        pairs = list(zip(group["cards"], group["keys"]))
        pairs.sort(key=lambda pair: (
            min((saved_order_rank[name] for name in pair[1].split("|")
                 if name in saved_order_rank), default=10**9),
            group["keys"].index(pair[1])))
        group["cards"] = [card for card, _key in pairs]
        group["keys"] = [key for _card, key in pairs]
    # 검토 영상은 오른쪽 미배치 패널을 제외하고, 왼쪽 콘티의 실제 섹션·카드
    # 순서만 사용한다. 키를 PLAN_JSON에도 넣어 렌더러와 화면이 같은 대상을 본다.
    plan["render_keys"] = [key for group in story_groups for key in group["keys"]]
    start_overrides = plan.get("plot_layout", {}).get("section_starts") or {}
    lyric_overrides = plan.get("plot_layout", {}).get("section_lyrics") or {}
    music_starts = []
    for g in story_groups:
        default_start = g["from"] if g["custom"] else g["spec"][0]
        value = float(start_overrides.get(str(g["id"]), default_start))
        if g["id"] == "intro":
            value = 0.0
        elif g["id"] == "after-music":
            value = song_end
        if music_starts:
            value = max(music_starts[-1], value)
        music_starts.append(round(value, 2))
    render_sections = []
    for group_i, g in enumerate(story_groups):
        music_from = music_starts[group_i]
        music_to = (music_starts[group_i + 1] if group_i + 1 < len(music_starts)
                    else final_end)
        section_lyric = str(lyric_overrides.get(str(g["id"]), g["lyric"]) or "가사 없음")
        # 카드가 없는 '음악 추가 필요' 꼬리는 노래 뒤 수 분짜리 검은 화면이
        # 되는 것을 막는다. 실제 카드가 배치되면 정상 섹션으로 포함한다.
        if g["id"] != "after-music" or g["keys"] or final_end > song_end + .005:
            render_sections.append({"id": str(g["id"]), "title": g["title"],
                                    "from": music_from, "to": music_to,
                                    "lyric": section_lyric,
                                    "keys": list(g["keys"])})
        section_sec = max(0.0, music_to - music_from)
        excess_sec = max(0.0, float(g.get("slide_sec") or 0) - section_sec)
        shortage_sec = max(0.0, section_sec - float(g.get("slide_sec") or 0))
        excess_html = (f'<b class="sectionExcess">영상 +{excess_sec:.2f}초 초과</b>'
                       if excess_sec > 0.005 else "")
        shortage_html = (f'<b class="sectionShortage">영상 {shortage_sec:.2f}초 부족</b>'
                         if shortage_sec > 0.005 else "")
        fixed_start = g["id"] in ("intro", "after-music")
        timing = (f'<label class="sectionTiming">시작 <input class="sectionStart" '
                  f'data-id="{html.escape(str(g["id"]), quote=True)}" type="number" '
                  f'min="0" step="0.01" value="{music_from:.2f}"'
                  f'{" disabled" if fixed_start else ""}>초</label>')
        if group_i == len(story_groups) - 1:
            minimum_end = max(song_end, music_from + .01)
            timing += (f'<label class="sectionTiming sectionEndTiming">끝 '
                       f'<input class="sectionEnd" type="number" min="{minimum_end:.2f}" '
                       f'max="36000" step="0.1" value="{final_end:.2f}">초</label>')
        remove = (f'<button class="removeSection" data-id="{html.escape(str(g["id"]), quote=True)}">섹션 삭제</button>'
                  if g["custom"] else "")
        drop_start = ('<div class="dropStart">↤ 이 섹션 맨 앞에 놓기</div>'
                      if g["cards"] else "")
        # HTML 속성의 실제 개행은 파서가 공백으로 정규화한다. 문자 참조로
        # 내보내야 dataset.lyric에서도 사용자가 넣은 줄바꿈이 그대로 살아난다.
        section_lyric_attr = html.escape(section_lyric, quote=True).replace("\n", "&#10;")
        sections.append(
            f'<section class="chapter story-section" data-id="{html.escape(str(g["id"]), quote=True)}" '
            f'data-title="{html.escape(g["title"], quote=True)}" '
            f'data-lyric="{section_lyric_attr}" '
            f'data-from="{music_from}" data-to="{music_to}"><header class="story-head"><div>'
            f'<button class="lyric-heading" data-from="{music_from}"><time>'
            f'{_plot_time(music_from)}–{_plot_time(music_to)} <em>({section_sec:.2f}초)</em>'
            f'{excess_html}{shortage_html}</time>'
            f'<strong>{html.escape(g["title"])}</strong></button><p class="editableLyric" '
            f'tabindex="0" title="클릭해서 가사 수정">{html.escape(section_lyric)}</p></div>'
            f'<aside>{timing}<label class="sectionDone"><input type="checkbox"> 섹션 완료</label>'
            f'<span class="screenCount" data-count="{len(g["cards"])}">{len(g["cards"])}화면</span>'
            f'<button class="editSectionCaptionPos" type="button">자막 위치</button>'
            f'<button class="addSelectedHere" type="button" disabled>선택 항목 넣기</button>'
            f'<button class="sortChronological" type="button">시간순 정렬</button>'
            f'{remove}</aside></header><div class="cuts">{drop_start}{"".join(g["cards"])}</div></section>')

    plan["render_sections"] = render_sections
    plan["render_total_sec"] = round(final_end, 2)
    save_json(PLAN_JSON, plan)

    warning_html = "".join(f"<li>{html.escape(w)}</li>" for w in plan.get("warnings", []))
    backlog_html = "".join(card for _at, card in sorted(backlog_cards))
    excluded_html = "".join(
        f'<article class="excluded-source" data-file="{html.escape(x["file"], quote=True)}">'
        f'<img src="{html.escape(x.get("thumb") or "", quote=True)}" '
        f'alt="{html.escape(x["file"], quote=True)}" loading="lazy">'
        f'<div><b>{html.escape(x.get("caption") or "영상 자막 없음")}</b>'
        f'<small>{html.escape(x["file"])}</small>'
        f'<button class="reinclude" type="button" data-file="{html.escape(x["file"], quote=True)}">'
        f'다시 포함</button></div></article>'
        for x in plan.get("excluded", []))
    music_src = html.escape(plan.get("music", {}).get("file") or "", quote=True)
    data = json.dumps(plan, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    template = r'''<!doctype html><html lang="ko"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>영상 플롯 검토</title>
<style>
@font-face{font-family:MaruBuri;src:url('fonts/MaruBuri-SemiBold.ttf') format('truetype');font-display:swap}
@font-face{font-family:NanumMyeongjo;src:url('fonts/NanumMyeongjo-Regular.ttf') format('truetype');font-display:swap}
@font-face{font-family:NanumPen;src:url('fonts/NanumPenScript-Regular.ttf') format('truetype');font-display:swap}
@font-face{font-family:NanumBrush;src:url('fonts/NanumBrushScript-Regular.ttf') format('truetype');font-display:swap}
:root{--bg:#f7f3f1;--card:#fff;--fg:#403734;--dim:#887974;--line:#e8dcd7;--pink:#d97791;--ink:#76485a}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:14px/1.5 -apple-system,BlinkMacSystemFont,"Noto Sans KR",sans-serif}
.top{position:sticky;top:0;z-index:20;background:rgba(255,252,250,.94);backdrop-filter:blur(12px);border-bottom:1px solid var(--line);padding:17px 22px}
.top .inner{max-width:1500px;margin:auto;display:flex;align-items:center;gap:18px;flex-wrap:wrap}.top h1{font-size:22px;margin:0}.summary{color:var(--dim)}
.serverStatus{border:0;border-radius:999px;padding:5px 9px;background:#eaf6ed;color:#337048;font:11px inherit;cursor:default}.serverStatus.offline,.serverStatus.unsaved{background:#ffe7e7;color:#a32f3d;font-weight:700;cursor:pointer}
.lastSaved{font-size:11px;color:var(--dim);white-space:nowrap}.offlinePopup{position:fixed;inset:0;z-index:1000;display:none;align-items:center;justify-content:center;padding:20px;background:#2d2020cc;backdrop-filter:blur(5px)}.offlinePopup.on{display:flex}.offlineCard{width:min(460px,94vw);padding:28px;border-radius:20px;background:#fff;text-align:center;box-shadow:0 24px 80px #0006}.offlineCard strong{display:block;font-size:24px;color:#a32f3d}.offlineCard p{margin:10px 0 18px;color:var(--dim)}.offlineCard button{border:0;border-radius:10px;background:var(--ink);color:#fff;padding:10px 18px;cursor:pointer;font:14px inherit}
.progress{margin-left:auto;min-width:180px}.bar{height:7px;background:#eee3df;border-radius:9px;overflow:hidden}.bar i{display:block;height:100%;width:0;background:var(--pink)}
.tools{max-width:1500px;margin:12px auto 0;display:flex;gap:7px;flex-wrap:wrap;align-items:center}.tools button,.back,.renderResult{border:1px solid var(--line);background:#fff;color:var(--fg);border-radius:999px;padding:7px 12px;cursor:pointer;text-decoration:none;font:inherit}.tools button.on{background:var(--ink);color:#fff}.back{margin-left:auto}.renderResult{border-color:#76957c;color:#2f6840;font-weight:700}.renderResult[hidden]{display:none}.renderLevel{display:flex;align-items:center;gap:4px;color:var(--dim);font-size:11px;white-space:nowrap}.renderLevel input,.renderLevel select{border:1px solid var(--line);border-radius:8px;background:#fff;padding:5px 4px;font:11px inherit}.renderLevel input{width:50px;text-align:right}.renderLevel select{max-width:150px;color:var(--fg)}.renderProgress{display:none;align-items:center;gap:7px;min-width:210px;color:var(--ink);font-size:11px;font-weight:700}.renderProgress.on{display:flex}.renderProgress progress{width:130px;height:10px;accent-color:var(--pink)}
.musicbox{max-width:1500px;margin:9px auto 0}.musichead{display:flex;align-items:center;gap:10px;flex-wrap:wrap}.musichead h2{font-size:14px;margin:0}.musichead audio{width:min(500px,100%);height:34px}.musichead small{color:var(--dim);font-size:11px}.followSong{display:flex;align-items:center;gap:5px;color:var(--ink);font-size:12px;white-space:nowrap;cursor:pointer}.followSong input{accent-color:var(--pink)}#addEmptySection{border:1px solid #d8a7b5;background:#fff;color:var(--ink);border-radius:9px;padding:6px 9px;cursor:pointer;font:12px inherit}
.sectionDone{display:flex;align-items:center;gap:4px;padding:4px 7px;border-radius:8px;background:#f2ece9;color:var(--dim);font-size:11px;cursor:pointer}.sectionDone input{accent-color:#5b966b}.story-section.section-done{border-color:#8eb89a;background:#f7fff8}.story-section.section-done .sectionDone{background:#dff1e3;color:#306941;font-weight:700}
.layoutChoice{display:flex;flex-direction:column;gap:3px;margin-top:8px;padding:7px;border-radius:9px;background:#f7f0f3;color:var(--ink);font-size:10px}.layoutChoice select{width:100%;border:1px solid #d8a7b5;border-radius:7px;background:#fff;padding:6px;color:var(--ink);font:11px inherit}
.sectionEndTiming{padding:3px 6px;border-radius:8px;background:#fff0d9;color:#87570f;font-weight:700}.sectionEndTiming input{border-color:#e0ad5e}
.bulkMove{max-width:1500px;margin:8px auto 0;padding:9px 11px;border:1px solid #d8a7b5;border-radius:12px;background:#fff3f7;display:flex;align-items:center;gap:8px;flex-wrap:wrap;color:var(--ink);font-size:12px}.bulkMove[hidden]{display:none}.bulkMove b{margin-right:2px}.bulkMove select{min-width:260px;max-width:520px;border:1px solid #d8a7b5;border-radius:8px;background:#fff;padding:7px;font:12px inherit}.bulkMove button{border:0;border-radius:8px;background:var(--ink);color:#fff;padding:7px 12px;cursor:pointer;font:12px inherit;font-weight:700}
.plot-workspace{max-width:1840px;margin:25px auto 90px;padding:0 18px;display:grid;grid-template-columns:minmax(0,1fr) 350px;gap:18px;align-items:start}.story-main{min-width:0}.chapter{margin:0 0 28px}.story-section{padding:12px;border:1px solid var(--line);border-radius:18px;background:#fff9f8;scroll-margin-top:190px}.story-head{display:flex;align-items:flex-start;justify-content:space-between;gap:14px;border-bottom:2px solid #ead5dc;padding:0 3px 10px;margin-bottom:12px}.story-head>div{min-width:0;flex:1}.story-head p{margin:5px 3px 0;color:var(--ink);font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.editableLyric{min-height:27px;padding:3px 7px;border:1px dashed transparent;border-radius:7px;cursor:text}.editableLyric:hover,.editableLyric:focus{border-color:#d8a7b5;background:#fff;outline:none}.editableLyric.editing{white-space:normal;overflow:visible;text-overflow:clip;box-shadow:0 0 0 2px #d9779122}.story-head aside{display:flex;align-items:center;gap:7px;color:var(--dim);white-space:nowrap}.sectionTiming{display:flex;align-items:center;gap:4px;color:var(--ink);font-size:11px}.sectionTiming input{width:72px;border:1px solid var(--line);border-radius:7px;padding:4px 5px;font:11px inherit}.sectionTiming input:disabled{background:#eee8e6;color:#999}.lyric-heading{display:flex;align-items:baseline;gap:10px;border:0;background:none;padding:0;color:var(--fg);cursor:pointer;text-align:left}.lyric-heading time{display:flex;align-items:center;gap:5px;font-weight:800;color:var(--pink);white-space:nowrap}.lyric-heading time em{font-style:normal;color:var(--dim);font-weight:600}.lyric-heading time .sectionExcess,.lyric-heading time .sectionShortage{padding:2px 6px;border-radius:999px;font-size:10px}.lyric-heading time .sectionExcess{background:#ffe7e7;color:#b1263b}.lyric-heading time .sectionShortage{background:#fff1d6;color:#986014}.lyric-heading strong{font-size:20px}.story-section.active{border-color:#d97791;box-shadow:0 0 0 2px #d9779122}.story-section.active .lyric-heading strong{color:var(--ink)}.removeSection,.sortChronological,.addSelectedHere{border:1px solid var(--line);background:#fff;border-radius:8px;padding:4px 7px;color:var(--dim);cursor:pointer;font:11px inherit}.removeSection{color:#a45b65}.addSelectedHere{display:none;border-color:#d895a8;color:#8f3f58;background:#fff2f6;font-weight:700}.select-mode .addSelectedHere{display:inline-block}.addSelectedHere:disabled,.sortChronological:disabled{opacity:.35;cursor:default}
.story-head p.editableLyric{white-space:pre-wrap;overflow:visible;text-overflow:clip;word-break:keep-all}
.backlog{position:sticky;top:190px;height:calc(100vh - 210px);min-height:360px;display:flex;flex-direction:column;border:1px solid #d9c8c3;border-radius:18px;background:#fff;overflow:hidden;box-shadow:0 8px 28px #64483e18}.backlog-head{padding:13px 14px 11px;border-bottom:1px solid var(--line);background:#fff9f7}.backlog-head h2{font-size:17px;margin:0}.backlog-head p{margin:3px 0 9px;color:var(--dim);font-size:11px}.showExcluded{display:flex;align-items:center;gap:6px;margin-top:8px;font-size:12px;color:var(--ink);cursor:pointer}.showExcluded input{accent-color:var(--pink)}#backlogSelectBtn{border:1px solid #d8a7b5;background:#fff;color:var(--ink);border-radius:9px;padding:6px 9px;cursor:pointer;font:12px inherit}#backlogSelectBtn.on{background:var(--ink);color:#fff}.backlog-scroll{flex:1;overflow:auto;padding:10px}.backlog-cuts{display:flex;flex-direction:column;gap:10px;min-height:140px}.backlog-cuts:empty::after{content:'모든 슬라이드가 왼쪽 콘티에 배치되었습니다';display:flex;min-height:120px;align-items:center;justify-content:center;text-align:center;border:2px dashed var(--line);border-radius:12px;color:var(--dim)}.backlog .cut{flex:none}.backlog .preview{height:175px}.backlog .arrange .earlier,.backlog .arrange .later{display:none}.backlog.drop-target{border-color:var(--pink);box-shadow:0 0 0 3px #d9779133}.excluded-list{display:none;margin-top:14px;padding-top:14px;border-top:2px solid #e5dddd;flex-direction:column;gap:9px}.backlog.show-excluded .excluded-list{display:flex}.excluded-source{display:grid;grid-template-columns:100px minmax(0,1fr);gap:9px;padding:8px;border:1px solid #d8d3d1;border-radius:12px;background:#e7e5e4;color:#777;filter:grayscale(1);opacity:.8}.excluded-source img{width:100px;height:82px;object-fit:contain;background:#d2d0cf;border-radius:8px}.excluded-source div{min-width:0}.excluded-source b,.excluded-source small{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.excluded-source b{font-size:12px}.excluded-source small{font-size:10px;margin:3px 0 8px}.reinclude{border:1px solid #aaa;background:#f5f4f3;color:#555;border-radius:7px;padding:4px 7px;cursor:pointer;font:11px inherit}
.backlogFilters{display:flex;flex-direction:column;gap:6px;margin-top:8px}.backlogFilters .showExcluded{margin-top:0}.backlogKind{display:grid;grid-template-columns:repeat(3,1fr);gap:4px}.backlogKind button{border:1px solid var(--line);border-radius:8px;background:#fff;color:var(--dim);padding:6px 3px;font:11px inherit;cursor:pointer}.backlogKind button.on{border-color:var(--ink);background:var(--ink);color:#fff;font-weight:700}.backlog[data-kind-filter="video"] .backlog-cuts .cut:not(.video),.backlog[data-kind-filter="motion"] .backlog-cuts .cut:not(.motion){display:none}.backlogFilterEmpty{display:none;min-height:120px;align-items:center;justify-content:center;text-align:center;border:2px dashed var(--line);border-radius:12px;color:var(--dim);padding:15px}.backlog.no-kind-result .backlogFilterEmpty{display:flex}
.story-section.drop-target{border-color:#d97791;background:#fff0f4;box-shadow:0 0 0 3px #d9779133}.story-section.drop-target .cuts{min-height:120px}.story-section.drop-target .cuts::after{content:'여기에 놓으면 이 섹션 마지막으로 이동';grid-column:1/-1;display:flex;align-items:center;justify-content:center;min-height:100px;border:2px dashed #d97791;border-radius:12px;color:#a45169;background:#fff8fa}
.cuts{display:grid;grid-template-columns:repeat(auto-fill,minmax(210px,1fr));gap:11px}.cuts:empty{min-height:110px;border:2px dashed #e8ccd5;border-radius:12px}.cuts:empty::after{content:'빈 섹션 · 슬라이드를 이곳으로 드래그하세요';grid-column:1/-1;display:flex;align-items:center;justify-content:center;color:#aa7e8a}.cut{position:relative;background:var(--card);border:1px solid var(--line);border-radius:14px;overflow:hidden;box-shadow:0 2px 8px #795d5410}.cut.dragging{opacity:.25}.cut.selected{border-color:#d97791;box-shadow:0 0 0 3px #d9779140}.cut.drop-before{box-shadow:-7px 0 0 #d97791}.cut.drop-after{box-shadow:7px 0 0 #d97791}.dragGrip{height:27px;display:flex;align-items:center;justify-content:center;background:#fff8fa;border-bottom:1px solid var(--line);color:#9a596c;font-size:11px;font-weight:800;cursor:grab;user-select:none;-webkit-user-select:none;touch-action:none}.dragGrip:active{cursor:grabbing}.preview{display:block;position:relative;width:100%;height:145px;padding:0;border:0;background:#ece6e3;cursor:pointer;overflow:hidden}.thumbs{position:relative;display:block;width:100%;height:100%}.thumb-cell{position:absolute;display:block;min-width:0;min-height:0;overflow:hidden;background:#eee7e4;border:1px solid #fff}.thumb-cell img{position:absolute;max-width:none;max-height:none;object-fit:fill;transform-origin:center}.num,.when{position:absolute;z-index:2;top:7px;background:#fffefcdd;border-radius:999px;padding:3px 8px;font-size:11px}.num{left:7px;font-weight:800}.when{right:7px}.info{padding:11px 12px 12px}.badges{display:flex;gap:4px;flex-wrap:wrap}.badges b{font-size:9px;background:#f8e8ed;color:var(--ink);padding:2px 6px;border-radius:999px}.info h3{font-size:14px;margin:7px 0 2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.info p{margin:0;color:var(--dim);font-size:11px}.info small{display:block;color:#aaa;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.select{font-size:11px;color:var(--dim);display:none}.select-mode .select{display:inline}.select-mode .preview{cursor:copy}.arrange{display:flex;align-items:center;gap:4px;margin-top:8px}.arrange .select{margin-right:auto}.arrange button{border:1px solid var(--line);background:#fff;border-radius:7px;padding:2px 6px;color:var(--dim);cursor:pointer;font:10px inherit}
.dropStart{display:none;grid-column:1/-1;min-height:46px;align-items:center;justify-content:center;border:2px dashed #d97791;border-radius:10px;background:#fff3f7;color:#95445d;font-weight:800}.drag-active .dropStart{display:flex}.dropStart.drop-target{background:#fbdde7;box-shadow:0 0 0 3px #d9779133}
.cut.notRendered{filter:grayscale(.85);opacity:.46}.cut.notRendered::after,.cut.partRendered::after{position:absolute;z-index:7;left:8px;right:8px;top:34px;padding:7px 8px;border-radius:9px;text-align:center;font-size:11px;font-weight:900;pointer-events:none;box-shadow:0 2px 10px #0003}.cut.notRendered::after{content:'영상에 안 나옴 · 섹션 시간 초과';background:#842f3ee8;color:#fff}.cut.partRendered::after{content:'영상 끝부분 잘림 · 섹션 시간 초과';background:#ffe3a8ed;color:#805008}.screenCount.hasOmitted{color:#b1263b;font-weight:900}
.timing{display:flex;align-items:center;gap:5px;margin-top:8px;color:var(--ink);font-size:11px}.timing input{width:65px;border:1px solid var(--line);border-radius:7px;padding:4px 6px;font:12px inherit}.fitModes{display:flex;flex-direction:column;gap:5px;margin-top:8px}.fitModes label{display:flex;flex-direction:column;gap:2px;min-width:0;color:var(--dim);font-size:10px}.fitModes label span{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.fitMode,.effectMode{width:100%;border:1px solid var(--line);border-radius:7px;background:#fff;padding:5px 6px;color:var(--ink);font:11px inherit}.effectMode{border-color:#d8a7b5;background:#fff8fa}.excludeOne{width:100%;margin-top:7px;border:1px solid #efd1d6;background:#fff8f8;color:#a33d4b;border-radius:8px;padding:5px;cursor:pointer;font:11px inherit}.excludeOne:hover{background:#ffe9eb}
details.warn{max-width:1500px;margin:18px auto;padding:0 22px}details.warn summary{cursor:pointer;color:#9b682b}details.warn ul{max-height:240px;overflow:auto;background:#fff;border:1px solid var(--line);padding:14px 14px 14px 34px;border-radius:12px}
dialog{width:min(1200px,96vw,calc(88vh * 16 / 9));height:auto;border:0;border-radius:18px;padding:0;box-shadow:0 20px 70px #36262155}dialog::backdrop{background:#362621b8}.modal-head{display:flex;align-items:center;gap:7px;padding:10px 13px;border-bottom:1px solid var(--line)}.modal-head h2{font-size:15px;margin:0;flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.modal-head button,.modal-head a{border:1px solid var(--line);background:#fff;color:var(--fg);border-radius:10px;min-width:42px;height:38px;padding:0 9px;font:12px inherit;line-height:36px;text-align:center;text-decoration:none;cursor:pointer;white-space:nowrap}.modal-head #prevCut,.modal-head #nextCut{font-size:25px;padding:0}.modal-head button:disabled{opacity:.3;cursor:default}.modal-head button.on{background:var(--ink);border-color:var(--ink);color:#fff}.modal-head .close{border:0;background:none;font-size:27px;padding:0}.modal-media{position:relative;width:100%;aspect-ratio:16/9;background:#211e1d;overflow:hidden}.modal-media .tile{position:absolute;padding:5px;display:flex;align-items:center;justify-content:center;overflow:hidden}.modal-media img,.modal-media video{display:block;width:100%;height:100%;object-fit:contain}.modal.pan-mode .tile{outline:2px dashed #ffd0dc;outline-offset:-5px;cursor:grab;touch-action:none}.modal.pan-mode .tile:active{cursor:grabbing}.modal.pan-mode video{pointer-events:none}.modal.pan-mode .caption-overlay{pointer-events:none;opacity:.35}.modal.caption-moving .modal-media::before,.modal.caption-moving .modal-media::after{content:'';position:absolute;z-index:7;pointer-events:none;background:#ffb6c9aa}.modal.caption-moving .modal-media::before{left:50%;top:0;bottom:0;width:1px}.modal.caption-moving .modal-media::after{top:50%;left:0;right:0;height:1px}.caption-overlay{position:absolute;z-index:8;transform:translate(-50%,-50%);max-width:92%;padding:0;color:#fff;text-align:center;white-space:pre;overflow:visible;text-shadow:0 2px 5px #000,0 0 12px #000;cursor:move;touch-action:none;user-select:none}.caption-overlay::after{content:'텍스트 중심 기준 · 드래그';position:absolute;left:50%;top:100%;transform:translateX(-50%);font:10px sans-serif;color:#fff9;background:#0008;border-radius:999px;padding:2px 5px;text-shadow:none;white-space:nowrap}.caption-overlay.moving{outline:1px dashed #ffd0dc;border-radius:7px}.caption-overlay.moving::before{content:'';position:absolute;left:50%;top:50%;width:7px;height:7px;transform:translate(-50%,-50%);border:2px solid #ff9bb6;border-radius:50%;background:#fff;box-shadow:0 0 0 2px #0005}@keyframes gentleZoom{from{scale:1}to{scale:1.06}}
.positionEditor{display:flex;gap:12px;align-items:flex-start;padding:8px 13px;border-bottom:1px solid var(--line);background:#fff9f8;max-height:155px;overflow:auto}.captionCoords,.mediaPositionRow{display:flex;align-items:center;gap:6px;flex-wrap:wrap}.captionCoords{min-width:310px}.positionEditor label{display:flex;align-items:center;gap:3px;font-size:11px;color:var(--dim)}.positionEditor input{width:65px;border:1px solid var(--line);border-radius:7px;padding:5px 6px;font:12px inherit;text-align:right}.positionEditor small{font-size:10px;color:#9a8983}.mediaPositionRows{display:flex;flex:1;flex-direction:column;gap:5px}.mediaPositionRow{padding-left:10px;border-left:1px solid var(--line)}.mediaPositionRow b{max-width:230px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:11px}.mediaPositionRow input:disabled{background:#eee;color:#aaa}.editSectionCaptionPos{border-color:#d8a7b5!important;color:#8f3f58!important}
body[data-filter="video"] .cut:not(.video),body[data-filter="motion"] .cut:not(.motion),body[data-filter="image"] .cut:not(.image),body[data-filter="open"] .cut.done{display:none}
@media(max-width:1050px){.plot-workspace{grid-template-columns:1fr}.backlog{position:relative;top:auto;height:65vh;grid-row:1;margin-bottom:10px}}
@media(max-width:600px){.cuts{grid-template-columns:repeat(2,minmax(0,1fr))}.preview{height:115px}.top{padding:12px}.info small{display:none}.story-section{padding:7px}.story-head p{white-space:normal;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}.lyric-heading strong{font-size:17px}.musichead small{display:none}.plot-workspace{padding:0 8px}.backlog .preview{height:145px}}
</style></head><body data-filter="all">
<header class="top"><div class="inner"><h1>🎞 영상 플롯 검토</h1><span class="summary">{{SUMMARY}}</span><button id="serverStatus" class="serverStatus">● 서버 연결 확인 중</button><span id="lastSaved" class="lastSaved">마지막 저장 확인 중</span><div class="progress"><span id="prog">0 / {{CUTS}} 검토</span><div class="bar"><i></i></div></div><a class="back" href="index.html">갤러리로</a></div>
<div class="tools"><button class="on" data-f="all">전체</button><button data-f="open">미검토</button><button data-f="image">사진</button><button data-f="motion">LIVE</button><button data-f="video">영상</button><button id="selectModeBtn">☑ 슬라이드 선택</button><button id="merge" hidden>선택 슬라이드 합치기</button><button id="split" hidden>선택 슬라이드 분리</button><button id="addSection" hidden>선택 위치에 섹션 추가</button><button id="excludeSelected" hidden>✕ 선택 제외</button><label class="renderLevel">노래 <input id="renderMusicVolume" type="number" min="0" max="200" step="5" value="100">%</label><label class="renderLevel">영상 원음 <input id="renderSourceVolume" type="number" min="0" max="200" step="5" value="70">%</label><label class="renderLevel">자막 폰트 <select id="renderCaptionFont"><option value="maru_buri">마루부리 · 세련된 명조</option><option value="nanum_pen">나눔 펜 손글씨</option><option value="nanum_brush">나눔 붓 손글씨</option><option value="nanum_myeongjo">나눔 명조</option><option value="apple_myungjo">애플 명조</option><option value="apple_gothic">애플 고딕</option></select></label><button id="renderPreview">🎬 저용량 검토 영상 만들기</button><span id="renderProgress" class="renderProgress"><progress id="renderProgressBar" max="100" value="0"></progress><b id="renderProgressText">0%</b></span><a id="renderResult" class="renderResult" target="_blank" hidden>완성 영상 열기</a><button id="backupAll">💾 전체 백업</button><button id="clear">검토 체크 초기화</button><span id="layoutStatus"></span></div>
<div id="bulkMove" class="bulkMove" hidden><b id="bulkMoveCount">선택 0개</b><label>이동할 섹션 <select id="bulkMoveSection"><option value="">섹션을 선택하세요</option></select></label><button id="bulkMoveButton" type="button">선택 항목 이동</button></div>
<section class="musicbox"><div class="musichead"><h2>🎵 O My Baby</h2><audio id="song" controls preload="metadata" src="{{MUSIC_SRC}}"></audio><label class="followSong"><input id="followSong" type="checkbox"> 재생 위치 따라가기</label><button id="addEmptySection" type="button">＋ 빈 섹션 추가</button><label class="renderLevel">영상 최종 종료 <input id="finalEnd" type="number" min="252.82" max="36000" step="0.1" value="{{FINAL_END}}">초</label><small id="musicNote">가사 절 제목을 누르면 해당 위치 재생 · 자동 추출 문구 검토 필요</small></div></section></header>
<details class="warn"><summary>⚠ 확인할 사항 {{WARNS}}개</summary><ul>{{WARNINGS}}</ul></details>
<div class="plot-workspace"><main class="story-main">{{SECTIONS}}</main><aside id="backlogPane" class="backlog" data-kind-filter="all"><header class="backlog-head"><h2>미배치 슬라이드 · {{BACKLOG_COUNT}}개</h2><p>시간순 · 왼쪽 가사 섹션으로 드래그하세요</p><button id="backlogSelectBtn" type="button">☑ 여러 장 선택</button><div class="backlogFilters"><div class="backlogKind" aria-label="미배치 종류 필터"><button type="button" data-backlog-kind="all">전체</button><button type="button" data-backlog-kind="video">동영상 {{VIDEO_BACKLOG_COUNT}}</button><button type="button" data-backlog-kind="motion">LIVE {{MOTION_BACKLOG_COUNT}}</button></div><label class="showExcluded"><input id="showExcluded" type="checkbox"> 제외 항목 포함 ({{EXCLUDED_COUNT}}개)</label></div></header><div class="backlog-scroll"><div id="backlogCuts" class="backlog-cuts">{{BACKLOG}}</div><div class="backlogFilterEmpty">이 종류의 미배치 슬라이드가 없습니다</div><section class="excluded-list">{{EXCLUDED}}</section></div></aside></div><div id="offlinePopup" class="offlinePopup" role="alertdialog" aria-modal="true"><div class="offlineCard"><strong>서버 연결이 끊겼습니다</strong><p>지금 변경한 내용은 자동 저장되지 않습니다.<br>서버를 다시 시작한 뒤 연결을 확인해 주세요.</p><button id="retryServer" type="button">연결 다시 확인</button></div></div><dialog id="modal"><div class="modal-head"><button id="prevCut" aria-label="이전 슬라이드" title="이전 슬라이드 (←)">‹</button><h2></h2><a id="cropEdit" target="_blank">남길 영역</a><button id="panMediaBtn">사진·영상 위치 이동</button><button id="saveMediaPos" disabled>화면 위치 저장</button><button id="saveCaptionPos">섹션 자막 위치 저장</button><button id="nextCut" aria-label="다음 슬라이드" title="다음 슬라이드 (→)">›</button><button class="close" aria-label="닫기">×</button></div><div id="positionEditor" class="positionEditor"><div class="captionCoords"><b>자막 중심</b><label>X <input id="captionPosX" type="number" min="0" max="100" step="0.1">%</label><label>Y <input id="captionPosY" type="number" min="0" max="100" step="0.1">%</label><small>화면 왼쪽·위가 0%, 오른쪽·아래가 100%</small></div><div id="mediaPositionRows" class="mediaPositionRows"></div></div><div class="modal-media"></div></dialog>
<script>const PLAN={{DATA}},PLAN_VERSION={{PLAN_VERSION}},CUTS=PLAN.chapters.flatMap(c=>c.cuts),cards=[...document.querySelectorAll('.cut')];
let completedSections=new Set(JSON.parse(localStorage.getItem('jiho.plot.sectionReview')||'[]'));const saveSectionReview=()=>localStorage.setItem('jiho.plot.sectionReview',JSON.stringify([...completedSections]));
let layout=JSON.parse(JSON.stringify(PLAN.plot_layout||{groups:[],separate:[],order:[],durations:{},sections:[],section_assignments:{},caption_positions:{},media_positions:{},effects:{},section_starts:{},section_lyrics:{},fit_modes:{},layouts:{},final_end:252.82})),dragging=null,selectMode=false;layout.durations=layout.durations||{};layout.sections=layout.sections||[];layout.section_assignments=layout.section_assignments||{};layout.caption_positions=layout.caption_positions||{};layout.media_positions=layout.media_positions||{};layout.effects=layout.effects||{};layout.section_starts=layout.section_starts||{};layout.section_lyrics=layout.section_lyrics||{};layout.fit_modes=layout.fit_modes||{};layout.layouts=layout.layouts||{};layout.final_end=+layout.final_end||252.82;
const song=document.querySelector('#song'),followSong=document.querySelector('#followSong'),lyricButtons=[...document.querySelectorAll('.lyric-heading')];let activeLyric=null;followSong.checked=localStorage.getItem('jiho.plot.followSong')==='1';followSong.onchange=()=>localStorage.setItem('jiho.plot.followSong',followSong.checked?'1':'0');
lyricButtons.forEach(b=>b.onclick=()=>{const t=+b.dataset.from;song.currentTime=t;song.play().catch(()=>{});b.closest('.story-section')?.scrollIntoView({behavior:'smooth',block:'start'})});
song.addEventListener('keydown',e=>{if(e.code==='Space'){e.preventDefault();e.stopPropagation();song.blur()}});
function editLyric(p){if(p.contentEditable==='true')return;const section=p.closest('.story-section'),id=section.dataset.id,original=p.textContent.trim();p.contentEditable='true';p.classList.add('editing');p.dataset.cancel='';p.focus();const range=document.createRange();range.selectNodeContents(p);const selection=getSelection();selection.removeAllRanges();selection.addRange(range);p.onkeydown=e=>{if(e.key==='Escape'){e.preventDefault();p.dataset.cancel='1';p.blur()}else if(e.key==='Enter'&&!e.shiftKey){e.preventDefault();p.blur()}};p.onblur=()=>{p.contentEditable='false';p.classList.remove('editing');const cancelled=p.dataset.cancel==='1',text=(cancelled?original:p.innerText.trim())||'가사 없음';p.textContent=text;p.onkeydown=null;p.onblur=null;if(cancelled||text===original)return;layout.section_lyrics[id]=text;section.dataset.lyric=text;commitLayout()}}
document.querySelectorAll('.editableLyric').forEach(p=>{p.onclick=()=>editLyric(p);p.onkeydown=e=>{if(e.key==='Enter'){e.preventDefault();editLyric(p)}}});
song.addEventListener('loadedmetadata',()=>{const gap=PLAN.total_sec-song.duration,txt=document.querySelector('#musicNote');if(gap>1)txt.textContent+=` · 곡 ${Math.floor(song.duration/60)}:${String(Math.floor(song.duration%60)).padStart(2,'0')} / 콘티 뒤 ${Math.floor(gap/60)}:${String(Math.floor(gap%60)).padStart(2,'0')}는 다른 음악 또는 반복 필요`});
song.addEventListener('timeupdate',()=>{const t=song.currentTime,s=[...document.querySelectorAll('.story-section')].find(x=>+x.dataset.from<=t&&t<+x.dataset.to);if(s!==activeLyric){activeLyric?.classList.remove('active');activeLyric=s||null;activeLyric?.classList.add('active');if(activeLyric&&followSong.checked)activeLyric.scrollIntoView({behavior:'smooth',block:'start'})}});
const filesOf=c=>CUTS[+c.dataset.i].tiles.map(t=>t.file),selected=()=>cards.filter(c=>c.querySelector('.groupcheck').checked),cardFor=i=>document.querySelector(`.cut[data-i="${i}"]`);
const bulkMove=document.querySelector('#bulkMove'),bulkMoveCount=document.querySelector('#bulkMoveCount'),bulkMoveSection=document.querySelector('#bulkMoveSection'),bulkMoveButton=document.querySelector('#bulkMoveButton');document.querySelectorAll('.story-section').forEach(s=>{const option=document.createElement('option'),from=+s.dataset.from||0;option.value=s.dataset.id;option.textContent=`${Math.floor(from/60)}:${String(Math.floor(from%60)).padStart(2,'0')} · ${s.dataset.title}`;bulkMoveSection.appendChild(option)});
const planOrder=()=>CUTS.flatMap(c=>c.tiles.map(t=>t.file));
function currentOrder(){const base=planOrder(),valid=new Set(base),saved=(layout.order||[]).filter(x=>valid.has(x)),seen=new Set(saved);return [...saved,...base.filter(x=>!seen.has(x))]}
function recordRelativeOrder(c,target,after){let order=currentOrder();const moved=filesOf(c),targetFiles=filesOf(target),set=new Set(moved);order=order.filter(x=>!set.has(x));const anchor=after?order.lastIndexOf(targetFiles[targetFiles.length-1])+1:order.indexOf(targetFiles[0]);order.splice(Math.max(0,anchor),0,...moved);layout.order=order}
function recordSequence(cs){const sortedFiles=cs.flatMap(filesOf),set=new Set(sortedFiles),queue=[...sortedFiles];layout.order=currentOrder().map(file=>set.has(file)?queue.shift():file)}
const chronologicalKey=c=>{const times=CUTS[+c.dataset.i].tiles.map(t=>t.taken||`${t.day||'9999'} ${t.file}`);return times.sort()[0]||'9999'};
const chapterCards=c=>cards.filter(x=>x.dataset.chapter===c.dataset.chapter).sort((a,b)=>+a.dataset.i-+b.dataset.i);
function assignToSection(c,section){const id=section?.dataset.id;if(id)layout.section_assignments[c.dataset.key]=id}
function assignToTarget(c,target){const a=c.closest('.story-section')?.dataset.id,b=target.closest('.story-section')?.dataset.id;if(a&&b&&a!==b)assignToSection(c,target.closest('.story-section'))}
function moveCard(c,delta){if(!c.closest('.story-section'))return;const siblings=[...c.closest('.cuts').querySelectorAll('.cut')],i=siblings.indexOf(c),target=siblings[i+delta];if(!target)return;recordRelativeOrder(c,target,delta>0);delta<0?target.before(c):target.after(c);commitLayout()}
function progress(){const sections=[...document.querySelectorAll('.story-section')],valid=new Set(sections.map(s=>s.dataset.id));completedSections=new Set([...completedSections].filter(id=>valid.has(id)));sections.forEach(s=>{const on=completedSections.has(s.dataset.id),box=s.querySelector('.sectionDone input');s.classList.toggle('section-done',on);if(box)box.checked=on});document.querySelector('#prog').textContent=`${completedSections.size} / ${sections.length} 섹션 완료`;document.querySelector('.bar i').style.width=(sections.length?completedSections.size/sections.length*100:0)+'%'}
function paintRenderCoverage(){document.querySelectorAll('.story-section').forEach(section=>{const sectionSec=Math.max(0,(+section.dataset.to||0)-(+section.dataset.from||0)),sectionCards=[...section.querySelectorAll('.cut')],total=sectionCards.reduce((sum,c)=>sum+Math.max(0,+c.querySelector('.duration')?.value||0),0);let remaining=sectionSec,stopped=false,omitted=0,partial=0;sectionCards.forEach(c=>{c.classList.remove('notRendered','partRendered');const dur=Math.max(0,+c.querySelector('.duration')?.value||0);if(stopped||remaining<1/15){c.classList.add('notRendered');omitted++;stopped=true;return}if(dur>remaining+.005){c.classList.add('partRendered');partial++;remaining=0;stopped=true}else remaining-=dur});const time=section.querySelector('.lyric-heading time'),seconds=time?.querySelector('em');if(seconds)seconds.textContent=`(${sectionSec.toFixed(2)}초)`;time?.querySelectorAll('.sectionExcess,.sectionShortage').forEach(x=>x.remove());const delta=total-sectionSec;if(time&&Math.abs(delta)>.005){const badge=document.createElement('b');badge.className=delta>0?'sectionExcess':'sectionShortage';badge.textContent=delta>0?`영상 +${delta.toFixed(2)}초 초과`:`영상 ${(-delta).toFixed(2)}초 부족`;time.appendChild(badge)}const count=section.querySelector('.screenCount');if(count){count.classList.toggle('hasOmitted',omitted>0||partial>0);count.textContent=`${count.dataset.count}화면${omitted?` · ${omitted}화면 미출력`:''}${partial?' · 1화면 일부':''}`}})}
function selectionUI(){const cs=selected(),backlogSelected=cs.filter(c=>c.closest('#backlogCuts'));document.body.classList.toggle('select-mode',selectMode);cards.forEach(c=>c.classList.toggle('selected',c.querySelector('.groupcheck').checked));const mode=document.querySelector('#selectModeBtn'),backlogMode=document.querySelector('#backlogSelectBtn');mode.classList.toggle('on',selectMode);mode.textContent=selectMode?`☑ 선택 중 ${cs.length}개 · 끝내기`:'☑ 슬라이드 선택';backlogMode.classList.toggle('on',selectMode);backlogMode.textContent=selectMode?`☑ 미배치 ${backlogSelected.length}개 선택됨`:'☑ 여러 장 선택';document.querySelectorAll('.addSelectedHere').forEach(b=>{b.disabled=!backlogSelected.length;b.textContent=backlogSelected.length?`선택 ${backlogSelected.length}개 넣기`:'선택 항목 넣기'});document.querySelectorAll('.sortChronological').forEach(b=>b.disabled=b.closest('.story-section').querySelectorAll('.cut').length<2);document.querySelector('#merge').hidden=!selectMode||cs.length<2;document.querySelector('#split').hidden=!selectMode||!cs.length;document.querySelector('#addSection').hidden=!selectMode||cs.length!==1;document.querySelector('#excludeSelected').hidden=!selectMode||!cs.length}
const selectionUIBase=selectionUI;selectionUI=()=>{selectionUIBase();const count=selected().length;bulkMove.hidden=!selectMode||!count;bulkMoveCount.textContent=`선택 ${count}개`};
const serverStatus=document.querySelector('#serverStatus'),lastSaved=document.querySelector('#lastSaved'),offlinePopup=document.querySelector('#offlinePopup');let serverOnline=null,unsavedLayout=false;
function paintSaved(){const raw=localStorage.getItem('jiho.plot.lastSaved');if(!raw)return lastSaved.textContent='아직 자동 저장 기록 없음';const d=new Date(+raw);lastSaved.textContent=`마지막 저장 ${d.toLocaleTimeString('ko-KR',{hour:'2-digit',minute:'2-digit',second:'2-digit'})}`}
function markSaved(){localStorage.setItem('jiho.plot.lastSaved',String(Date.now()));paintSaved()}
function paintServer(){serverStatus.className='serverStatus'+(serverOnline===false?' offline':unsavedLayout?' unsaved':'');serverStatus.textContent=serverOnline===false?'● 서버 연결 끊김 · 변경 저장 안 됨':unsavedLayout?'● 저장 안 된 변경 있음 · 눌러 다시 저장':'● 서버 연결됨';offlinePopup.classList.toggle('on',serverOnline===false)}
async function checkServer(){const controller=new AbortController(),timer=setTimeout(()=>controller.abort(),2500);try{const r=await fetch('/api/ping',{method:'POST',cache:'no-store',signal:controller.signal});const j=await r.json();serverOnline=!!j.ok;if(serverOnline&&j.plan_version&&j.plan_version!==PLAN_VERSION&&!unsavedLayout){location.reload();return}}catch(_e){serverOnline=false}finally{clearTimeout(timer);paintServer()}}
serverStatus.onclick=()=>{if(serverOnline&&unsavedLayout)commitLayout();else checkServer()};document.querySelector('#retryServer').onclick=checkServer;paintSaved();checkServer();setInterval(checkServer,5000);
document.querySelector('#backupAll').onclick=async e=>{const b=e.currentTarget,old=b.textContent,st=document.querySelector('#layoutStatus');if(serverOnline===false)return alert('서버 연결이 끊겨 백업할 수 없습니다');b.disabled=true;b.textContent='백업 중…';st.textContent='갤러리·콘티 전체 데이터 백업 중…';try{const r=await fetch('/api/backup',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}),j=await r.json();if(!j.ok)throw Error(j.error||'백업 실패');st.textContent=`전체 백업 완료 · ${j.backup}`;alert(`전체 백업을 만들었습니다.\n${j.backup}\n\n${j.count}개 작업 파일이 들어 있습니다.`)}catch(err){st.textContent='백업 실패: '+err.message;alert('백업 실패: '+err.message)}finally{b.disabled=false;b.textContent=old}};
const renderPreview=document.querySelector('#renderPreview'),renderResult=document.querySelector('#renderResult'),renderProgress=document.querySelector('#renderProgress'),renderProgressBar=document.querySelector('#renderProgressBar'),renderProgressText=document.querySelector('#renderProgressText'),renderCaptionFont=document.querySelector('#renderCaptionFont');renderCaptionFont.value=localStorage.getItem('jiho.render.captionFont')||'maru_buri';renderCaptionFont.onchange=()=>localStorage.setItem('jiho.render.captionFont',renderCaptionFont.value);let renderPoll=null;function paintRender(j){const st=document.querySelector('#layoutStatus'),busy=j.state==='queued'||j.state==='running',hasTotal=Number.isFinite(+j.total)&&+j.total>0,pct=hasTotal?Math.max(0,Math.min(100,Math.round(+j.done/+j.total*100))):(busy?0:100);renderPreview.disabled=busy;renderPreview.textContent=busy?`🎬 영상 만드는 중 ${pct}%`:'🎬 저용량 검토 영상 만들기';renderProgress.classList.toggle('on',busy);renderProgressBar.value=pct;renderProgressText.textContent=hasTotal?`${pct}% · ${j.done}/${j.total}`:`${pct}%`;if(j.state!=='idle')st.textContent=`검토 영상 · ${j.message||j.state}${busy?' · '+pct+'%':''}`;if(j.output){renderResult.href='/'+j.output.split('/').map(encodeURIComponent).join('/');renderResult.hidden=false}else renderResult.hidden=true;if(busy){clearTimeout(renderPoll);renderPoll=setTimeout(checkRender,1500)}}async function checkRender(){try{const r=await fetch('/api/render-status',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}),j=await r.json();if(j.ok)paintRender(j)}catch(_e){}}renderPreview.onclick=async()=>{if(serverOnline===false)return alert('서버 연결이 끊겨 영상을 만들 수 없습니다');const musicVolume=Math.max(0,Math.min(200,+document.querySelector('#renderMusicVolume').value||0)),sourceVolume=Math.max(0,Math.min(200,+document.querySelector('#renderSourceVolume').value||0)),captionFont=renderCaptionFont.value,captionFontName=renderCaptionFont.selectedOptions[0].textContent;if(!confirm(`섹션 시간에 맞춘 640×360 검토 영상을 만들까요?\n빈 시간은 검은 화면, 넘치는 슬라이드는 섹션 끝에서 자릅니다.\n가사는 중앙 아래에 표시합니다.\n노래 ${musicVolume}% · 정규화한 영상 원음 ${sourceVolume}% · ${captionFontName}`))return;try{const r=await fetch('/api/render-preview',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({music_volume:musicVolume/100,source_volume:sourceVolume/100,caption_font:captionFont})}),j=await r.json();if(!j.ok)throw Error(j.error||'렌더링 시작 실패');paintRender(j)}catch(err){alert('검토 영상 시작 실패: '+err.message)}};renderResult.onclick=()=>song.pause();checkRender();
const qualityLabel=document.createElement('label');qualityLabel.className='renderLevel';qualityLabel.innerHTML='영상 품질 <select id="renderQuality"><option value="low">저용량 · 360p · 최대 50MB</option><option value="2x">2배 · 540p · 최대 100MB</option><option value="4x">4배 · 720p · 최대 200MB</option><option value="1080p">1080P · 최종본</option></select>';renderPreview.before(qualityLabel);const renderQuality=qualityLabel.querySelector('select');renderQuality.value=localStorage.getItem('jiho.render.quality')||'low';if(!renderQuality.value)renderQuality.value='low';renderQuality.onchange=()=>{localStorage.setItem('jiho.render.quality',renderQuality.value);renderPreview.textContent=`🎬 ${renderQuality.selectedOptions[0].textContent.split(' · ')[0]} 영상 만들기`};renderQuality.onchange();
const originalPaintRender=paintRender;paintRender=function(j){originalPaintRender(j);const busy=j.state==='queued'||j.state==='running',label=j.quality_label||renderQuality.selectedOptions[0].textContent.split(' · ')[0];renderQuality.disabled=busy;if(busy)renderPreview.textContent=`🎬 ${label} 만드는 중 ${Math.max(0,Math.min(100,Math.round((+j.done||0)/(+j.total||1)*100)))}%`;else renderPreview.textContent=`🎬 ${renderQuality.selectedOptions[0].textContent.split(' · ')[0]} 영상 만들기`};
const CAPTION_STYLES={maru_buri:{size:23,wrap:26,lineSpacing:4,family:'MaruBuri'},nanum_myeongjo:{size:22,wrap:27,lineSpacing:4,family:'NanumMyeongjo'},apple_myungjo:{size:20,wrap:29,lineSpacing:4,family:'AppleMyungjo'},nanum_pen:{size:34,wrap:19,lineSpacing:4,family:'NanumPen'},nanum_brush:{size:33,wrap:20,lineSpacing:4,family:'NanumBrush'},apple_gothic:{size:23,wrap:26,lineSpacing:4,family:'AppleGothic'}};
const captionMeasureCanvas=document.createElement('canvas'),captionMeasureContext=captionMeasureCanvas.getContext('2d');
function wrapCaption(text,style){captionMeasureContext.font=`${style.size}px ${style.family},cursive`;const maxWidth=640*.92,measure=s=>captionMeasureContext.measureText(s||' ').width,splitToken=token=>{const chunks=[];let current='';for(const char of token){const candidate=current+char;if(current&&measure(candidate)>maxWidth){chunks.push(current);current=char}else current=candidate}if(current)chunks.push(current);return chunks.length?chunks:['']},out=[];for(let raw of String(text||'').split(/\r?\n/)){raw=raw.trim();if(!raw){out.push('');continue}let current='';for(const word of raw.split(' ')){const pieces=measure(word)>maxWidth?splitToken(word):[word];pieces.forEach((piece,i)=>{const candidate=(current+' '+piece).trim();if(current&&measure(candidate)>maxWidth){out.push(current);current=piece}else current=candidate;if(i<pieces.length-1){out.push(current);current=''}})}if(current)out.push(current)}return out.join('\n')}
function applyCaptionPreviewStyle(){if(!captionOverlayEl)return;const style=CAPTION_STYLES[renderCaptionFont.value]||CAPTION_STYLES.nanum_brush,scale=media.clientWidth/640;captionOverlayEl.style.fontFamily=`${style.family},cursive`;captionOverlayEl.style.fontSize=(style.size*scale)+'px';captionOverlayEl.style.lineHeight=((style.size+style.lineSpacing)/style.size);captionOverlayEl.textContent=wrapCaption(captionOverlayEl.dataset.caption,style);requestAnimationFrame(()=>{if(draftCaptionPos){draftCaptionPos=clampCaptionPos(draftCaptionPos);paintCaptionOverlay()}})}
document.fonts?.ready.then(()=>applyCaptionPreviewStyle());
if(!localStorage.getItem('jiho.render.captionFont'))renderCaptionFont.value='nanum_brush';renderCaptionFont.onchange=()=>{localStorage.setItem('jiho.render.captionFont',renderCaptionFont.value);applyCaptionPreviewStyle()};
renderPreview.onclick=async()=>{if(serverOnline===false)return alert('서버 연결이 끊겨 영상을 만들 수 없습니다');const musicVolume=Math.max(0,Math.min(200,+document.querySelector('#renderMusicVolume').value||0)),sourceVolume=Math.max(0,Math.min(200,+document.querySelector('#renderSourceVolume').value||0)),captionFont=renderCaptionFont.value,captionFontName=renderCaptionFont.selectedOptions[0].textContent,quality=renderQuality.value,qualityName=renderQuality.selectedOptions[0].textContent;if(!confirm(`${qualityName} 영상을 만들까요?\n섹션 시간에 맞추고, 빈 시간은 검은 화면으로 둡니다.\n노래 ${musicVolume}% · 정규화한 영상 원음 ${sourceVolume}% · ${captionFontName}`))return;try{const r=await fetch('/api/render-preview',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({music_volume:musicVolume/100,source_volume:sourceVolume/100,caption_font:captionFont,quality})}),j=await r.json();if(!j.ok)throw Error(j.error||'렌더링 시작 실패');paintRender(j)}catch(err){alert('영상 시작 실패: '+err.message)}};
async function commitLayout(){layout.order=currentOrder();unsavedLayout=true;paintServer();const st=document.querySelector('#layoutStatus');st.textContent='저장 중…';sessionStorage.setItem('jiho.plot.scroll',scrollY);if(serverOnline===false){st.textContent='서버 연결 끊김 — 저장되지 않았습니다';paintServer();return}try{const r=await fetch('/api/plot-layout',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(layout)}),j=await r.json();if(!j.ok)throw Error(j.error||'저장 실패');unsavedLayout=false;markSaved();location.reload()}catch(e){serverOnline=false;unsavedLayout=true;paintServer();st.textContent='저장 실패: '+e.message}}
async function excludeFiles(rawFiles){const files=[...new Set(rawFiles)];if(!files.length)return;const detail=files.length===1?files[0]:`${files.length}개 사진·영상`;if(!confirm(`${detail}을 영상에서 제외할까요?\n메인 갤러리의 제외 레이블에도 반영됩니다.`))return;if(serverOnline===false){unsavedLayout=true;paintServer();return alert('서버 연결이 끊겨 제외를 저장할 수 없습니다')}try{for(const file of files){const r=await fetch('/api/tag',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({file,pick:0})}),j=await r.json();if(!j.ok)throw Error(j.error||file+' 저장 실패')}const r=await fetch('/api/plan',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}),j=await r.json();if(!j.ok)throw Error(j.error||'콘티 재생성 실패');markSaved();location.reload()}catch(e){serverOnline=false;paintServer();alert('제외 저장 실패: '+e.message)}}
async function reincludeFile(file){if(!confirm(`${file}을 영상에 다시 포함할까요?`))return;if(serverOnline===false)return alert('서버 연결이 끊겨 저장할 수 없습니다');try{const r=await fetch('/api/tag',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({file,pick:1})}),j=await r.json();if(!j.ok)throw Error(j.error||'저장 실패');const pr=await fetch('/api/plan',{method:'POST',headers:{'Content-Type':'application/json'},body:'{}'}),pj=await pr.json();if(!pj.ok)throw Error(pj.error||'콘티 재생성 실패');markSaved();location.reload()}catch(e){serverOnline=false;paintServer();alert('다시 포함 저장 실패: '+e.message)}}
document.querySelectorAll('.reinclude').forEach(b=>b.onclick=()=>reincludeFile(b.dataset.file));
cards.forEach(c=>{c.querySelectorAll('img').forEach(img=>img.draggable=false);c.querySelector('.groupcheck').onchange=selectionUI;c.querySelector('.excludeOne').onclick=()=>excludeFiles(filesOf(c));c.querySelector('.duration').onchange=e=>{const v=+e.target.value;if(!Number.isFinite(v)||v<.2||v>60)return alert('표시 시간은 0.2~60초로 입력해주세요');layout.durations[c.dataset.key]=v;commitLayout()};c.querySelector('.preview').onclick=()=>{if(selectMode){const box=c.querySelector('.groupcheck');box.checked=!box.checked;selectionUI()}else openCut(+c.dataset.i)};c.querySelector('.earlier').onclick=()=>moveCard(c,-1);c.querySelector('.later').onclick=()=>moveCard(c,1);c.ondragstart=e=>{dragging=c;c.classList.add('dragging');document.body.classList.add('drag-active');if(e.dataTransfer){e.dataTransfer.effectAllowed='move';e.dataTransfer.setData('text/plain',c.dataset.key)}};c.ondragend=()=>{c.classList.remove('dragging');document.body.classList.remove('drag-active');document.querySelectorAll('.drop-target,.drop-before,.drop-after').forEach(x=>x.classList.remove('drop-target','drop-before','drop-after'));dragging=null};c.ondragover=e=>{if(!c.closest('.story-section')||!dragging||dragging===c)return;e.preventDefault();e.stopPropagation();if(e.dataTransfer)e.dataTransfer.dropEffect='move';const r=c.getBoundingClientRect(),after=e.clientY>r.top+r.height/2||(Math.abs(e.clientY-(r.top+r.height/2))<r.height/3&&e.clientX>r.left+r.width/2);document.querySelectorAll('.drop-before,.drop-after').forEach(x=>x.classList.remove('drop-before','drop-after'));c.classList.add(after?'drop-after':'drop-before')};c.ondragleave=()=>c.classList.remove('drop-before','drop-after');c.ondrop=e=>{const section=c.closest('.story-section');if(!section)return;e.preventDefault();e.stopPropagation();if(!dragging||dragging===c)return;assignToSection(dragging,section);const after=c.classList.contains('drop-after');c.classList.remove('drop-before','drop-after');recordRelativeOrder(dragging,c,after);after?c.after(dragging):c.before(dragging);commitLayout()}});
let pointerDrag=null;const clearDropMarks=()=>document.querySelectorAll('.drop-target,.drop-before,.drop-after').forEach(x=>x.classList.remove('drop-target','drop-before','drop-after'));const hitAt=(selector,x,y)=>document.elementsFromPoint(x,y).map(el=>el.closest?.(selector)).find(Boolean)||null;const recordDomOrder=()=>{layout.order=[...document.querySelectorAll('.story-section .cut, #backlogCuts .cut')].flatMap(filesOf)};
function movePointerDrag(e){const p=pointerDrag;if(!p||e.pointerId!==p.id)return;e.preventDefault();if(!p.moved&&Math.hypot(e.clientX-p.x,e.clientY-p.y)<4)return;p.moved=true;if(e.clientY<205)scrollBy(0,-14);else if(e.clientY>innerHeight-35)scrollBy(0,14);clearDropMarks();p.target=p.zone=p.section=p.backlog=null;const zone=hitAt('.dropStart',e.clientX,e.clientY);if(zone){p.zone=zone;zone.classList.add('drop-target');return}const target=hitAt('.cut',e.clientX,e.clientY);if(target&&target!==p.card&&target.closest('.story-section')){const r=target.getBoundingClientRect(),sameRow=e.clientY>=r.top&&e.clientY<=r.bottom;p.after=sameRow?e.clientX>r.left+r.width/2:e.clientY>r.top+r.height/2;p.target=target;target.classList.add(p.after?'drop-after':'drop-before');return}const section=hitAt('.story-section',e.clientX,e.clientY);if(section){p.section=section;section.classList.add('drop-target');return}const backlog=hitAt('#backlogPane',e.clientX,e.clientY);if(backlog){p.backlog=backlog;backlog.classList.add('drop-target')}}
function endPointerDrag(e){const p=pointerDrag;if(!p||e.pointerId!==p.id)return;e.preventDefault();e.stopPropagation();pointerDrag=null;clearDropMarks();p.card.classList.remove('dragging');document.body.classList.remove('drag-active');dragging=null;if(!p.moved)return;let section=null;if(p.zone){section=p.zone.closest('.story-section');const first=[...section.querySelectorAll('.cut')].find(c=>c!==p.card);first?first.before(p.card):p.zone.after(p.card)}else if(p.target){section=p.target.closest('.story-section');p.after?p.target.after(p.card):p.target.before(p.card)}else if(p.section){section=p.section;p.section.querySelector('.cuts').appendChild(p.card)}else if(p.backlog){delete layout.section_assignments[p.card.dataset.key];document.querySelector('#backlogCuts').appendChild(p.card);recordDomOrder();commitLayout();return}else return;assignToSection(p.card,section);recordDomOrder();commitLayout()}
cards.forEach(c=>{const grip=c.querySelector('.dragGrip');grip.onpointerdown=e=>{if(e.button!==0||pointerDrag)return;e.preventDefault();e.stopPropagation();dragging=c;pointerDrag={card:c,id:e.pointerId,x:e.clientX,y:e.clientY,moved:false,target:null,zone:null,section:null,backlog:null,after:false};c.classList.add('dragging');document.body.classList.add('drag-active');grip.setPointerCapture?.(e.pointerId)};grip.onpointermove=movePointerDrag;grip.onpointerup=endPointerDrag;grip.onpointercancel=endPointerDrag});
document.querySelectorAll('.fitMode').forEach(select=>select.onchange=()=>{layout.fit_modes[select.dataset.file]=select.value;commitLayout()});
document.querySelectorAll('.effectMode').forEach(select=>select.onchange=()=>{layout.effects[select.dataset.file]=select.value;commitLayout()});
document.querySelectorAll('.layoutMode').forEach(select=>select.onchange=()=>{layout.layouts[select.dataset.key]=select.value;commitLayout()});
document.querySelectorAll('.dropStart').forEach(zone=>{zone.ondragover=e=>{if(!dragging)return;e.preventDefault();e.stopPropagation();zone.classList.add('drop-target')};zone.ondragleave=()=>zone.classList.remove('drop-target');zone.ondrop=e=>{e.preventDefault();e.stopPropagation();zone.classList.remove('drop-target');if(!dragging)return;const section=zone.closest('.story-section'),first=[...section.querySelectorAll('.cut')].find(c=>c!==dragging);assignToSection(dragging,section);if(first){recordRelativeOrder(dragging,first,false);first.before(dragging)}else zone.after(dragging);commitLayout()}});
document.querySelectorAll('.story-section').forEach(section=>{const done=section.querySelector('.sectionDone input');done.onchange=()=>{done.checked?completedSections.add(section.dataset.id):completedSections.delete(section.dataset.id);saveSectionReview();progress()};section.ondragover=e=>{if(!dragging)return;e.preventDefault();document.querySelectorAll('.drop-target').forEach(x=>x.classList.toggle('drop-target',x===section))};section.ondragleave=e=>{if(!section.contains(e.relatedTarget))section.classList.remove('drop-target')};section.ondrop=e=>{if(e.target.closest('.cut,.dropStart'))return;e.preventDefault();section.classList.remove('drop-target');if(!dragging)return;assignToSection(dragging,section);section.querySelector('.cuts').appendChild(dragging);commitLayout()}});progress();
const backlogPane=document.querySelector('#backlogPane'),backlogCuts=document.querySelector('#backlogCuts'),showExcluded=document.querySelector('#showExcluded'),backlogKindButtons=[...document.querySelectorAll('[data-backlog-kind]')];showExcluded.checked=localStorage.getItem('jiho.plot.showExcluded')==='1';let backlogKind=localStorage.getItem('jiho.plot.backlogKind')||'all';if(!['all','video','motion'].includes(backlogKind))backlogKind='all';const paintBacklogFilters=()=>{backlogPane.classList.toggle('show-excluded',showExcluded.checked);backlogPane.dataset.kindFilter=backlogKind;backlogKindButtons.forEach(b=>b.classList.toggle('on',b.dataset.backlogKind===backlogKind));backlogPane.classList.toggle('no-kind-result',backlogKind!=='all'&&!backlogCuts.querySelector(`.cut.${backlogKind}`))};paintBacklogFilters();showExcluded.onchange=()=>{localStorage.setItem('jiho.plot.showExcluded',showExcluded.checked?'1':'0');paintBacklogFilters()};backlogKindButtons.forEach(b=>b.onclick=()=>{backlogKind=b.dataset.backlogKind;localStorage.setItem('jiho.plot.backlogKind',backlogKind);paintBacklogFilters()});backlogPane.ondragover=e=>{if(!dragging||e.target.closest('.cut'))return;e.preventDefault();backlogPane.classList.add('drop-target')};backlogPane.ondragleave=e=>{if(!backlogPane.contains(e.relatedTarget))backlogPane.classList.remove('drop-target')};backlogPane.ondrop=e=>{if(e.target.closest('.cut'))return;e.preventDefault();backlogPane.classList.remove('drop-target');if(!dragging)return;delete layout.section_assignments[dragging.dataset.key];backlogCuts.appendChild(dragging);commitLayout()};
function toggleSelection(){selectMode=!selectMode;if(!selectMode)cards.forEach(c=>c.querySelector('.groupcheck').checked=false);selectionUI()}
document.querySelector('#selectModeBtn').onclick=toggleSelection;document.querySelector('#backlogSelectBtn').onclick=toggleSelection;
document.querySelectorAll('.addSelectedHere').forEach(b=>b.onclick=()=>{const section=b.closest('.story-section'),cs=selected().filter(c=>c.closest('#backlogCuts')).sort((a,b)=>chronologicalKey(a).localeCompare(chronologicalKey(b)));if(!cs.length)return alert('오른쪽 미배치 패널에서 슬라이드를 먼저 선택해 주세요');cs.forEach(c=>{assignToSection(c,section);section.querySelector('.cuts').appendChild(c)});recordSequence(cs);commitLayout()});
bulkMoveButton.onclick=()=>{const id=bulkMoveSection.value,section=[...document.querySelectorAll('.story-section')].find(s=>s.dataset.id===id),cs=selected();if(!section)return alert('이동할 섹션을 선택해주세요');if(!cs.length)return alert('이동할 슬라이드를 선택해주세요');if(!confirm(`선택한 ${cs.length}개 슬라이드를 ‘${section.dataset.title}’ 섹션으로 한 번에 이동할까요?`))return;cs.forEach(c=>{assignToSection(c,section);section.querySelector('.cuts').appendChild(c)});layout.order=[...document.querySelectorAll('.story-section .cut, #backlogCuts .cut')].flatMap(filesOf);commitLayout()};
document.querySelectorAll('.sortChronological').forEach(b=>b.onclick=()=>{const section=b.closest('.story-section'),cs=[...section.querySelectorAll('.cut')];if(cs.length<2)return;if(!confirm(`‘${section.dataset.title}’ 섹션의 ${cs.length}개 슬라이드를 촬영 시간순으로 다시 정렬할까요?\n직접 정한 섹션 내부 순서는 바뀝니다.`))return;cs.sort((a,b)=>chronologicalKey(a).localeCompare(chronologicalKey(b))).forEach(c=>section.querySelector('.cuts').appendChild(c));recordSequence(cs);commitLayout()});document.querySelectorAll('.duration').forEach(input=>input.addEventListener('input',paintRenderCoverage));selectionUI();paintRenderCoverage();
document.querySelector('#excludeSelected').onclick=()=>excludeFiles(selected().flatMap(filesOf));
const oldScroll=+sessionStorage.getItem('jiho.plot.scroll')||0;sessionStorage.removeItem('jiho.plot.scroll');if(oldScroll)requestAnimationFrame(()=>scrollTo(0,oldScroll));
document.querySelector('#merge').onclick=()=>{const cs=selected();if(cs.length<2)return alert('합칠 슬라이드를 2개 이상 선택해 주세요');const firstSection=cs[0].closest('.story-section'),containers=new Set(cs.map(c=>c.closest('.story-section')?.dataset.id||'backlog'));if(containers.size>1&&!confirm(`서로 다른 섹션의 ${cs.length}개 슬라이드를 합칠까요?\n합친 화면은 첫 번째 선택 항목의 ‘${firstSection?.dataset.title||'미배치'}’ 위치에 놓입니다.`))return;const files=cs.flatMap(filesOf),set=new Set(files),sectionId=firstSection?.dataset.id;layout.groups=(layout.groups||[]).filter(g=>!g.some(x=>set.has(x)));layout.separate=(layout.separate||[]).filter(x=>!set.has(x));cs.forEach(c=>delete layout.section_assignments[c.dataset.key]);layout.groups.push(files);if(sectionId)layout.section_assignments[files.join('|')]=sectionId;commitLayout()};
document.querySelector('#split').onclick=()=>{const cs=selected();if(!cs.length)return alert('분리할 슬라이드를 선택해 주세요');const files=cs.flatMap(filesOf),set=new Set(files);layout.groups=(layout.groups||[]).filter(g=>!g.some(x=>set.has(x)));layout.separate=[...new Set([...(layout.separate||[]),...files])];cs.forEach(c=>{const sectionId=c.closest('.story-section')?.dataset.id;delete layout.section_assignments[c.dataset.key];if(sectionId)filesOf(c).forEach(file=>layout.section_assignments[file]=sectionId)});commitLayout()};
document.querySelector('#addSection').onclick=()=>{const cs=selected();if(cs.length!==1)return alert('새 섹션이 시작될 슬라이드 하나만 선택해 주세요');const title=prompt('새 섹션 제목을 입력해주세요','새 섹션');if(!title)return;const lyric=prompt('이 섹션에 표시할 가사나 설명을 입력해주세요','')||'';const start=filesOf(cs[0])[0];layout.sections=layout.sections.filter(x=>x.start!==start);delete layout.section_assignments[cs[0].dataset.key];layout.sections.push({id:'custom-'+Date.now(),title,lyric,start});commitLayout()};
document.querySelector('#addEmptySection').onclick=()=>{const suggested=(song.currentTime>0?song.currentTime:252.82).toFixed(2),raw=prompt('빈 섹션 시작 시간을 초 단위로 입력해주세요.\n현재 노래 재생 위치가 기본값입니다.',suggested);if(raw===null)return;const at=+raw;if(!Number.isFinite(at)||at<0)return alert('0 이상의 시작 시간을 입력해주세요');const title=prompt('빈 섹션 제목을 입력해주세요',at>=252.8?'마지막 인사':'간주');if(!title)return;const lyric=prompt('검은 화면에 표시할 글을 입력해주세요.\n글 없이 검은 화면만 두려면 비워두세요.',at>=252.8?'감사합니다':'')||'';layout.sections.push({id:'custom-'+Date.now(),title,lyric,at});if(at>=layout.final_end)layout.final_end=Math.ceil((at+3)*10)/10;commitLayout()};
function previewFinalEnd(e){const value=+e.target.value,lastSection=[...document.querySelectorAll('.story-section')].at(-1);if(Number.isFinite(value)&&lastSection){lastSection.dataset.to=value;paintRenderCoverage()}}function changeFinalEnd(e){const value=+e.target.value,lastSection=[...document.querySelectorAll('.story-section')].at(-1),lastStart=+(lastSection?.dataset.from||0),minimum=Math.max(252.82,lastStart+.01);if(!Number.isFinite(value)||value<minimum){alert(`마지막 섹션 끝은 ${minimum.toFixed(2)}초 이상이어야 합니다`);e.target.value=layout.final_end.toFixed(2);return}layout.final_end=value;document.querySelectorAll('#finalEnd,.sectionEnd').forEach(input=>input.value=value.toFixed(2));commitLayout()}document.querySelectorAll('#finalEnd,.sectionEnd').forEach(input=>{input.oninput=previewFinalEnd;input.onchange=changeFinalEnd});
document.querySelectorAll('.removeSection').forEach(b=>b.onclick=e=>{e.stopPropagation();if(confirm('이 섹션 구분을 삭제할까요?')){layout.sections=layout.sections.filter(x=>x.id!==b.dataset.id);Object.keys(layout.section_assignments).forEach(k=>{if(layout.section_assignments[k]===b.dataset.id)delete layout.section_assignments[k]});commitLayout()}});
const sectionStartInputs=[...document.querySelectorAll('.sectionStart')];sectionStartInputs.forEach((input,i)=>{input.oninput=()=>{const value=+input.value;if(!Number.isFinite(value))return;const section=input.closest('.story-section');section.dataset.from=value;if(i){sectionStartInputs[i-1].closest('.story-section').dataset.to=value}paintRenderCoverage()};input.onchange=()=>{const value=+input.value,prev=i?+sectionStartInputs[i-1].value:-.01,next=i+1<sectionStartInputs.length?+sectionStartInputs[i+1].value:Infinity;if(!Number.isFinite(value)||value<prev+.01||value>next-.01){alert(`섹션 시작은 이전 ${prev.toFixed(2)}초보다 뒤, 다음 ${Number.isFinite(next)?next.toFixed(2):'끝'}초보다 앞이어야 합니다`);location.reload();return}layout.section_starts[input.dataset.id]=value;commitLayout()}});
document.querySelectorAll('[data-f]').forEach(b=>b.onclick=()=>{document.body.dataset.filter=b.dataset.f;document.querySelectorAll('[data-f]').forEach(x=>x.classList.toggle('on',x===b))});
document.querySelector('#clear').textContent='섹션 완료 초기화';document.querySelector('#clear').onclick=()=>{if(confirm('섹션 완료 체크를 모두 지울까요?')){completedSections.clear();saveSectionReview();progress()}};
const modal=document.querySelector('#modal'),media=modal.querySelector('.modal-media'),prevCut=document.querySelector('#prevCut'),nextCut=document.querySelector('#nextCut'),saveCaptionPos=document.querySelector('#saveCaptionPos'),cropEdit=document.querySelector('#cropEdit'),panMediaBtn=document.querySelector('#panMediaBtn'),saveMediaPos=document.querySelector('#saveMediaPos'),captionPosX=document.querySelector('#captionPosX'),captionPosY=document.querySelector('#captionPosY'),mediaPositionRows=document.querySelector('#mediaPositionRows');let openIndex=-1,openSectionId='',draftCaptionPos=null,captionOverlayEl=null,panMode=false,draftMediaPositions={},mediaPositionInputs={};
new MutationObserver(()=>{if(openIndex<0)return;const cut=CUTS[openIndex];[...media.querySelectorAll('.tile')].forEach((wrap,i)=>{const el=wrap.querySelector('img');if(!el)return;const tile=cut?.tiles?.[i];el.style.animation=tile?.effect==='zoom_in'?`gentleZoom ${Math.max(.2,+cut.dur||3)}s linear forwards`:'none'})}).observe(media,{childList:true,subtree:true});
const storyCutIndices=()=>[...document.querySelectorAll('.story-section .cut')].map(c=>+c.dataset.i);
function navigateStory(delta){const sequence=storyCutIndices(),pos=sequence.indexOf(openIndex),next=sequence[pos+delta];if(pos>=0&&next!==undefined)openCut(next)}
modal.querySelector('.close').onclick=()=>modal.close();modal.onclick=e=>{if(e.target===modal)modal.close()};prevCut.onclick=()=>navigateStory(-1);nextCut.onclick=()=>navigateStory(1);saveCaptionPos.onclick=()=>{if(!openSectionId||!draftCaptionPos)return;layout.caption_positions['section:'+openSectionId]=draftCaptionPos;document.querySelector(`.story-section[data-id="${CSS.escape(openSectionId)}"]`)?.querySelectorAll('.cut').forEach(c=>delete layout.caption_positions[c.dataset.key]);commitLayout()};
function clampCaptionPos(pos){if(!captionOverlayEl||!media.clientWidth||!media.clientHeight)return[pos[0],pos[1]];const minX=Math.min(.5,(captionOverlayEl.offsetWidth/2+7)/media.clientWidth),minY=Math.min(.5,(captionOverlayEl.offsetHeight/2+7)/media.clientHeight);let x=Math.max(minX,Math.min(1-minX,+pos[0]||0)),y=Math.max(minY,Math.min(1-minY,+pos[1]||0));if(Math.abs(x-.5)<.015)x=.5;if(Math.abs(y-.5)<.015)y=.5;return[x,y]}
function syncCaptionCoords(){const enabled=!!draftCaptionPos;captionPosX.disabled=captionPosY.disabled=!enabled;if(enabled){captionPosX.value=(draftCaptionPos[0]*100).toFixed(1);captionPosY.value=(draftCaptionPos[1]*100).toFixed(1)}}function paintCaptionOverlay(){if(!captionOverlayEl||!draftCaptionPos)return;captionOverlayEl.style.left=(draftCaptionPos[0]*100)+'%';captionOverlayEl.style.top=(draftCaptionPos[1]*100)+'%';syncCaptionCoords()}function editCaptionCoords(){if(!draftCaptionPos)return;const x=+captionPosX.value/100,y=+captionPosY.value/100;if(!Number.isFinite(x)||!Number.isFinite(y))return;draftCaptionPos=clampCaptionPos([x,y]);paintCaptionOverlay()}captionPosX.oninput=captionPosY.oninput=editCaptionCoords;
function addCaptionOverlay(c,text,sectionId){const caption=(text&&text!=='가사 없음')?text:'';saveCaptionPos.disabled=!caption||!sectionId;captionOverlayEl=null;if(!caption){draftCaptionPos=null;syncCaptionCoords();return}draftCaptionPos=[...(layout.caption_positions['section:'+sectionId]||c?.caption_position||[.5,.86])];const el=document.createElement('div');captionOverlayEl=el;el.className='caption-overlay';el.dataset.caption=caption;applyCaptionPreviewStyle();el.onpointerdown=e=>{el.setPointerCapture(e.pointerId);e.preventDefault();el.classList.add('moving');modal.classList.add('caption-moving')};el.onpointermove=e=>{if(!el.hasPointerCapture(e.pointerId))return;const r=media.getBoundingClientRect();draftCaptionPos=clampCaptionPos([(e.clientX-r.left)/r.width,(e.clientY-r.top)/r.height]);paintCaptionOverlay()};el.onpointerup=el.onpointercancel=e=>{if(el.hasPointerCapture(e.pointerId))el.releasePointerCapture(e.pointerId);el.classList.remove('moving');modal.classList.remove('caption-moving')};media.appendChild(el);requestAnimationFrame(()=>{applyCaptionPreviewStyle();draftCaptionPos=clampCaptionPos(draftCaptionPos);paintCaptionOverlay()})}
function keepInsideClip(el,clip){if(!clip)return;const [start,end]=clip,nearEnd=Math.max(start,end-.03);el.addEventListener('play',()=>{if(el.currentTime<start||el.currentTime>=end)el.currentTime=start});el.addEventListener('seeking',()=>{if(el.currentTime<start-.03)el.currentTime=start;else if(el.currentTime>end)el.currentTime=nearEnd});el.addEventListener('timeupdate',()=>{if(!el.paused&&el.currentTime>=end-.03){el.pause();el.currentTime=start}})}
function mediaGeometry(el,frame,t){const nw=el.naturalWidth||el.videoWidth,nh=el.naturalHeight||el.videoHeight,aw=frame.clientWidth,ah=frame.clientHeight;if(!nw||!nh||!aw||!ah)return null;const rot=+(t.rotation||0),swap=rot%180!==0,ow=swap?nh:nw,oh=swap?nw:nh,safe=Array.isArray(t.safe)&&t.safe.length===4?t.safe:null;let baseW=ow,baseH=oh,cx=ow/2,cy=oh/2;if(safe){baseW=Math.max(.01,(safe[2]-safe[0])*ow);baseH=Math.max(.01,(safe[3]-safe[1])*oh);cx=(safe[0]+safe[2])/2*ow;cy=(safe[1]+safe[3])/2*oh}const scale=t.fit==='cover'?Math.max(aw/baseW,ah/baseH):Math.min(aw/baseW,ah/baseH);return{nw,nh,aw,ah,ow,oh,baseW,baseH,cx,cy,scale,rot,gapX:Math.max(0,aw-baseW*scale),gapY:Math.max(0,ah-baseH*scale)}}
function fitEditedMedia(el,frame,t){const paint=()=>{const g=mediaGeometry(el,frame,t);if(!g)return;const pos=Array.isArray(t.media_position)?t.media_position:[.5,.5],targetX=g.baseW*g.scale/2+g.gapX*Math.max(0,Math.min(1,+pos[0]||0)),targetY=g.baseH*g.scale/2+g.gapY*Math.max(0,Math.min(1,+pos[1]||0));el.style.width=(g.nw*g.scale)+'px';el.style.height=(g.nh*g.scale)+'px';el.style.left=(targetX-(g.cx-g.ow/2)*g.scale)+'px';el.style.top=(targetY-(g.cy-g.oh/2)*g.scale)+'px';el.style.maxWidth='none';el.style.maxHeight='none';el.style.position='absolute';el.style.transform=`translate(-50%,-50%) rotate(${g.rot}deg)`;el.style.transformOrigin='center'};if(el.tagName==='IMG'&&el.complete)requestAnimationFrame(paint);else if(el.tagName==='VIDEO'&&el.readyState>=1)requestAnimationFrame(paint);else el.addEventListener(el.tagName==='IMG'?'load':'loadedmetadata',()=>requestAnimationFrame(paint),{once:true})}
document.querySelectorAll('.cut .thumb-cell img').forEach(img=>{const card=img.closest('.cut'),tile=CUTS[+card.dataset.i].tiles[+img.dataset.tile];fitEditedMedia(img,img.parentElement,tile)});
function setPanMode(on){panMode=!!on;modal.classList.toggle('pan-mode',panMode);panMediaBtn.classList.toggle('on',panMode);panMediaBtn.textContent=panMode?'위치 이동 중 · 끝내기':'사진·영상 위치 이동'}panMediaBtn.onclick=()=>setPanMode(!panMode);saveMediaPos.onclick=()=>{Object.entries(draftMediaPositions).forEach(([file,pos])=>layout.media_positions[file]=pos);commitLayout()};
function syncMediaCoords(file,pos){const inputs=mediaPositionInputs[file];if(inputs){inputs[0].value=(pos[0]*100).toFixed(1);inputs[1].value=(pos[1]*100).toFixed(1)}}function addMediaPositionRow(t,wrap,el){const row=document.createElement('div');row.className='mediaPositionRow';const name=document.createElement('b');name.textContent=t.file;name.title=t.file;row.appendChild(name);const inputs=[];['X','Y'].forEach((axis,i)=>{const label=document.createElement('label'),input=document.createElement('input');label.append(axis+' ');input.type='number';input.min='0';input.max='100';input.step='.1';label.append(input,'%');row.appendChild(label);inputs.push(input)});const hint=document.createElement('small');hint.textContent='남는 여백 안 위치';row.appendChild(hint);mediaPositionRows.appendChild(row);mediaPositionInputs[t.file]=inputs;const pos=Array.isArray(t.media_position)?t.media_position:[.5,.5];syncMediaCoords(t.file,pos);const apply=()=>{const x=+inputs[0].value/100,y=+inputs[1].value/100;if(!Number.isFinite(x)||!Number.isFinite(y))return;const next=[Math.max(0,Math.min(1,x)),Math.max(0,Math.min(1,y))];t.media_position=next;draftMediaPositions[t.file]=next;saveMediaPos.disabled=false;fitEditedMedia(el,wrap,t)};inputs.forEach(input=>input.oninput=apply);const refreshAxes=()=>{const g=mediaGeometry(el,wrap,t);if(!g)return;inputs[0].disabled=g.gapX<1;inputs[1].disabled=g.gapY<1;hint.textContent=g.gapX>=1&&g.gapY>=1?'좌우·상하 여백 안 위치':g.gapX>=1?'좌우 여백 안 위치':g.gapY>=1?'상하 여백 안 위치':'남는 여백 없음'};if((el.tagName==='IMG'&&el.complete)||(el.tagName==='VIDEO'&&el.readyState>=1))requestAnimationFrame(refreshAxes);else el.addEventListener(el.tagName==='IMG'?'load':'loadedmetadata',refreshAxes,{once:true})}
function enableMediaPan(wrap,el,t){let drag=null;wrap.onpointerdown=e=>{if(!panMode||e.button!==0)return;const g=mediaGeometry(el,wrap,t);if(!g||(g.gapX<1&&g.gapY<1))return;e.preventDefault();e.stopPropagation();const start=Array.isArray(t.media_position)?[...t.media_position]:[.5,.5];drag={id:e.pointerId,x:e.clientX,y:e.clientY,start,g};wrap.setPointerCapture(e.pointerId)};wrap.onpointermove=e=>{if(!drag||e.pointerId!==drag.id)return;e.preventDefault();const pos=[drag.g.gapX>=1?Math.max(0,Math.min(1,drag.start[0]+(e.clientX-drag.x)/drag.g.gapX)):drag.start[0],drag.g.gapY>=1?Math.max(0,Math.min(1,drag.start[1]+(e.clientY-drag.y)/drag.g.gapY)):drag.start[1]];t.media_position=pos;draftMediaPositions[t.file]=pos;syncMediaCoords(t.file,pos);saveMediaPos.disabled=false;fitEditedMedia(el,wrap,t)};wrap.onpointerup=wrap.onpointercancel=e=>{if(drag&&e.pointerId===drag.id)drag=null}}
function openCut(i){if(i<0||i>=CUTS.length)return;media.querySelectorAll('video').forEach(v=>v.pause());openIndex=i;const c=CUTS[i],story=cardFor(i)?.closest('.story-section'),section=story?.dataset.title||'미배치 슬라이드',sectionLyric=story?.dataset.lyric||'',sequence=storyCutIndices(),storyPos=sequence.indexOf(i),position=storyPos>=0?`콘티 ${storyPos+1}/${sequence.length}`:'미배치 미리보기';openSectionId=story?.dataset.id||'';modal.querySelector('h2').textContent=`${section}${sectionLyric&&sectionLyric!=='가사 없음'?' · '+sectionLyric:''} | ${position} · ${c.caption||'영상 자막 없음'}`;cropEdit.href='index.html?file='+encodeURIComponent(c.tiles[0].file);cropEdit.hidden=false;prevCut.disabled=storyPos<=0;nextCut.disabled=storyPos<0||storyPos===sequence.length-1;media.innerHTML='';mediaPositionRows.innerHTML='';mediaPositionInputs={};setPanMode(false);panMediaBtn.disabled=false;draftMediaPositions={};saveMediaPos.disabled=true;c.tiles.forEach(t=>{const wrap=document.createElement('div'),cell=t.cell||[0,0,1,1];wrap.className='tile';wrap.style.left=(cell[0]*100)+'%';wrap.style.top=(cell[1]*100)+'%';wrap.style.width=(cell[2]*100)+'%';wrap.style.height=(cell[3]*100)+'%';let el;if(t.kind==='image'){el=document.createElement('img');el.src=t.path}else{el=document.createElement('video');el.src=t.path;el.controls=true;el.autoplay=true;el.playsInline=true;const clip=t.clip;keepInsideClip(el,clip);el.addEventListener('loadedmetadata',()=>{if(clip)el.currentTime=clip[0];el.play().catch(()=>{})})}wrap.appendChild(el);media.appendChild(wrap);fitEditedMedia(el,wrap,t);enableMediaPan(wrap,el,t);addMediaPositionRow(t,wrap,el)});addCaptionOverlay(c,sectionLyric,openSectionId);if(!modal.open)modal.showModal()}
function openSectionCaptionEditor(section){media.querySelectorAll('video').forEach(v=>v.pause());openIndex=-1;openSectionId=section.dataset.id;modal.querySelector('h2').textContent=`${section.dataset.title} · 검은 화면 자막 위치`;cropEdit.hidden=true;prevCut.disabled=nextCut.disabled=true;media.innerHTML='';mediaPositionRows.innerHTML='';mediaPositionInputs={};setPanMode(false);panMediaBtn.disabled=true;draftMediaPositions={};saveMediaPos.disabled=true;addCaptionOverlay(null,section.dataset.lyric,openSectionId);if(!modal.open)modal.showModal()}document.querySelectorAll('.editSectionCaptionPos').forEach(button=>button.onclick=e=>{e.stopPropagation();openSectionCaptionEditor(button.closest('.story-section'))});
document.addEventListener('keydown',e=>{if(!modal.open)return;if(e.key==='ArrowLeft'){e.preventDefault();navigateStory(-1)}else if(e.key==='ArrowRight'){e.preventDefault();navigateStory(1)}});
modal.addEventListener('close',()=>{media.querySelectorAll('video').forEach(v=>v.pause());setPanMode(false);modal.classList.remove('caption-moving');openIndex=-1;openSectionId=''});</script></body></html>'''
    summary = (f'{plan["cuts"]}화면 · {plan["photos"]}컷 · '
               f'{_plot_time(plan["total_sec"])} · 목표 {_plot_time(plan["target_sec"])}')
    out = (template.replace("{{SUMMARY}}", html.escape(summary))
           .replace("{{CUTS}}", str(plan["cuts"]))
           .replace("{{WARNS}}", str(len(plan.get("warnings", []))))
           .replace("{{WARNINGS}}", warning_html)
           .replace("{{MUSIC_SRC}}", music_src)
           .replace("{{FINAL_END}}", f"{final_end:.2f}")
           .replace("{{SECTIONS}}", "".join(sections))
           .replace("{{BACKLOG}}", backlog_html)
           .replace("{{BACKLOG_COUNT}}", str(len(backlog_cards)))
           .replace("{{VIDEO_BACKLOG_COUNT}}", str(video_backlog_count))
           .replace("{{MOTION_BACKLOG_COUNT}}", str(motion_backlog_count))
           .replace("{{EXCLUDED}}", excluded_html)
           .replace("{{EXCLUDED_COUNT}}", str(len(plan.get("excluded", []))))
           .replace("{{PLAN_VERSION}}", str(PLAN_JSON.stat().st_mtime_ns
                                             if PLAN_JSON.exists() else 0))
           .replace("{{DATA}}", data))
    (ROOT / "VIDEO_PLOT.html").write_text(out, encoding="utf-8")


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
    backup_stop = threading.Event()
    backup_thread = None
    if not args.readonly:
        backup_thread = threading.Thread(target=_auto_backup_loop,
                                         args=(backup_stop,), daemon=True)
        backup_thread.start()
        print("  · 변경이 있으면 5분마다 편집 상태 전체를 자동 백업합니다.")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nserve: 종료")
    finally:
        backup_stop.set()
        srv.server_close()


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

    p = sub.add_parser("chapters", help="영상 챕터 확인 / 초안 만들기")
    p.add_argument("--init", action="store_true", help="초안을 만들어 data/chapters.json 에 저장")
    p.add_argument("--count", type=int, default=6, help="챕터 개수 (기본 6)")
    p.add_argument("--target", type=int, help=f"영상 전체 목표 길이(초, 기본 {DEFAULT_TARGET_SEC})")
    p.add_argument("--size", help="영상 해상도 (예: 1920x1080, 세로면 1080x1920)")
    p.add_argument("--mode", choices=GROUP_MODES,
                   help="여러 장을 한 화면에 묶기 — auto: 해상도 부족할 때만, "
                        "fill: 화면에 안 맞는 세로 사진까지, off: 안 묶음")
    p.add_argument("--max-upscale", type=float, dest="max_upscale",
                   help=f"이 배율보다 크게 늘려야 하면 묶는다 (기본 {MAX_UPSCALE})")
    p.set_defaults(func=cmd_chapters)

    p = sub.add_parser("music", help="배경음악 BPM·첫 박·후렴 구간 설정")
    p.add_argument("--file", help="음악 파일 경로 (예: music/main.m4a)")
    p.add_argument("--bpm", type=float, help="분당 박자 수")
    p.add_argument("--offset", type=float, help="첫 박이 시작하는 위치(초)")
    p.add_argument("--chorus", help="후렴 구간 — '48-80, 140-172' 처럼 초 단위")
    p.set_defaults(func=cmd_music)

    p = sub.add_parser("plan", help="태그+챕터+음악 → 컷 리스트(영상 계획)")
    p.add_argument("--with-untagged", action="store_true",
                   help="아직 고르지 않은 사진도 '보통'으로 넣기")
    p.add_argument("--no-stretch", dest="stretch", action="store_false",
                   help="컷이 모자라도 길이를 늘리지 않기")
    p.set_defaults(func=cmd_plan, stretch=True)

    p = sub.add_parser("bundle", help="원본 없이 썸네일만 담은 공유용 정적 번들")
    p.add_argument("--out", default="dist", help="출력 폴더 (기본 dist)")
    p.add_argument("--size", type=int, default=480)
    p.add_argument("--with-video", action="store_true", help="영상 원본도 포함 (+218MB)")
    p.add_argument("--with-motion", action="store_true", help="모션 클립도 포함 (+58MB)")
    p.add_argument("--with-private", action="store_true",
                   help="'비공개'로 표시한 사진도 포함 (기본은 제외)")
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
.tools button,.tools a.plotlink{background:#fff;border:1px solid var(--line);color:var(--fg);box-shadow:var(--sh);
  border-radius:999px;padding:7px 15px;font-size:13px;cursor:pointer;font-family:inherit;
  transition:.15s}
.tools a.plotlink{text-decoration:none}.tools button:hover,.tools a.plotlink:hover{border-color:var(--accent);color:var(--accent-ink);transform:translateY(-1px)}
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
.shot img,.shot video.thumb{width:100%;height:auto;display:block;transition:transform .3s;background:#f7f1ee}
.shot:hover img,.shot:hover video.thumb{transform:scale(1.03)}
.shot.rot90,.shot.rot270{aspect-ratio:calc(1 / var(--ratio));min-height:0}
.shot.rot90>img,.shot.rot270>img,.shot.rot90>video.preview,.shot.rot270>video.preview{
  position:absolute;left:50%;top:50%;width:calc(100% * var(--ratio));
  max-width:none;height:auto}
.shot.rot90>img,.shot.rot90>video.preview{transform:translate(-50%,-50%) rotate(90deg)}
.shot.rot270>img,.shot.rot270>video.preview{transform:translate(-50%,-50%) rotate(270deg)}
.shot.rot180>img,.shot.rot180>video.preview{transform:rotate(180deg)}
.shot.rot90:hover>img{transform:translate(-50%,-50%) rotate(90deg) scale(1.03)}
.shot.rot270:hover>img{transform:translate(-50%,-50%) rotate(270deg) scale(1.03)}
.shot.rot180:hover>img{transform:rotate(180deg) scale(1.03)}
/* 필수 영역이 있으면 브라우저가 그 부분만 잘라 만든 미리보기를 사용한다.
   잘라낸 이미지는 이미 회전까지 반영되어 있으므로 격자에서 다시 돌리지 않는다. */
.shot.safe-thumb>img,.shot.safe-thumb.rot90>img,.shot.safe-thumb.rot180>img,
.shot.safe-thumb.rot270>img{position:static;left:auto;top:auto;width:100%;height:auto;
  max-width:100%;transform:none!important}
.shot .thumb-fallback{width:100%;aspect-ratio:16/10;display:flex;flex-direction:column;
  align-items:center;justify-content:center;gap:7px;padding:18px;text-align:center;
  background:linear-gradient(145deg,#f9e9ee,#f3eee9);color:var(--accent-ink)}
.shot.pt .thumb-fallback{aspect-ratio:4/5}
.shot .thumb-fallback b{font-size:18px}.shot .thumb-fallback span{max-width:100%;font-size:10px;
  color:#75645e;word-break:break-all}.shot .thumb-fallback small{font-size:10px;color:var(--dim)}
.shot figcaption{position:absolute;inset:auto 0 0 0;padding:20px 9px 8px;font-size:11px;
  line-height:1.4;color:#fff;background:linear-gradient(transparent,rgba(60,40,35,.82));
  opacity:0;transition:opacity .2s;z-index:6}
.shot:hover figcaption{opacity:1}
.shot figcaption i{opacity:.7}
/* 편집 모드: 캡션이 사진 아래 입력칸처럼 펼쳐져 바로 고칠 수 있다 */
body.edit .shot img,body.edit .shot video.thumb{flex:1 1 auto}
body.edit .shot figcaption{position:static;opacity:1;background:#fffdfc;color:var(--fg);
  padding:8px 9px;font-size:12px;line-height:1.45;border-top:1px solid var(--line);
  outline:0;cursor:text;min-height:20px}
body.edit .shot figcaption:focus{background:#fff;box-shadow:inset 0 0 0 2px var(--soft)}
body.edit .shot figcaption i{opacity:.45}
body.edit .shot{cursor:default}
body.edit .shot img,body.edit .shot video.thumb{cursor:zoom-in}
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
.shot video.preview{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;
  opacity:0;pointer-events:none;transition:opacity .18s ease;background:transparent}
.shot video.preview.ready{opacity:1}
.shot.rot90>video.preview,.shot.rot270>video.preview{inset:auto;left:50%;top:50%;
  width:calc(100% * var(--ratio));height:auto;max-width:none}
.shot.rot90>video.preview{transform:translate(-50%,-50%) rotate(90deg)}
.shot.rot270>video.preview{transform:translate(-50%,-50%) rotate(270deg)}
.shot.rot180>video.preview{transform:rotate(180deg)}
body.edit .shot.nosum{outline:2px dashed var(--warn);outline-offset:-2px}
/* 영상 태그가 격자에서도 보이게 — ★꼭 / ✕제외 / 🔒비공개 / ◎얼굴위치 */
.shot .tagmark{position:absolute;left:7px;bottom:7px;z-index:3;background:rgba(255,255,255,.94);
  border-radius:999px;padding:2px 8px;font-size:11px;color:var(--accent-ink);letter-spacing:.05em;
  box-shadow:0 1px 4px rgba(0,0,0,.14)}
.shot .tagmark em{font-style:normal;opacity:.6;font-size:10px;margin-left:2px}
.shot.pick0{opacity:.4;filter:grayscale(.75)}
.shot.pick0:hover{opacity:.9;filter:none}
.shot.pick2{outline:2px solid var(--accent);outline-offset:-2px}
body.onlyuntagged .shot:not(.untagged),body.onlyuntagged .day.hide{display:none}
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
/* ---------- 챕터 · 음악 ---------- */
#chap{position:fixed;inset:0;z-index:60;background:rgba(60,45,40,.35);backdrop-filter:blur(6px);
  display:none;align-items:center;justify-content:center;padding:20px}
#chap.on{display:flex}
#chap .panel{position:relative;max-width:760px;width:100%;max-height:88vh;overflow:auto;
  background:var(--card);border:1px solid var(--line);border-radius:var(--r);padding:28px 30px;
  box-shadow:var(--sh-lg)}
#chap h3{margin:0 0 6px;font-size:22px;color:#493e3a;letter-spacing:-.02em}
#chap h4{margin:26px 0 10px;font-size:16px;color:var(--accent-ink)}
#chap .lead{margin:0 0 18px;color:#7d6f6a;font-size:13px;line-height:1.65}
#chap .x{position:absolute;top:12px;right:16px;background:none;border:0;font-size:28px;
  color:var(--dim);cursor:pointer;line-height:1}
#chap .crow{display:grid;grid-template-columns:1fr 104px 104px 68px 96px 30px;gap:6px;
  margin-bottom:6px;align-items:center}
#chap .chead{font-size:11px;color:var(--dim);padding:0 2px}
#chap input,#chap select{width:100%;border:1px solid var(--line);background:#fdfaf9;color:var(--fg);
  border-radius:9px;padding:9px 10px;font:14px inherit;outline:0}
#chap input:focus,#chap select:focus{border-color:var(--accent);background:#fff}
#chap .crow .del{border:1px solid var(--line);background:#fff;border-radius:9px;cursor:pointer;
  color:var(--dim);font-size:16px;line-height:1;padding:8px 0}
#chap .crow .del:hover{border-color:var(--warn);color:var(--warn)}
#chap .row{display:flex;gap:8px;align-items:center;margin-top:14px;flex-wrap:wrap}
#chap .row button{border:1px solid var(--line);background:#fff;color:var(--fg);border-radius:11px;
  padding:11px 16px;font:14px inherit;cursor:pointer}
#chap .row button:hover{border-color:var(--accent)}
#chap .row button.primary{background:var(--accent);border-color:var(--accent);color:#fff;font-weight:700}
#chap .row label{font-size:13px;color:var(--dim);display:flex;align-items:center;gap:6px}
#chap .row label input{width:78px}
#chap .musicgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:9px}
#chap .musicgrid label{font-size:12px;color:var(--dim);display:flex;flex-direction:column;gap:5px}
#chap .planout{margin-top:18px;font-size:13px;line-height:1.7;color:#6b5c57}
#chap .planout .big{font-size:17px;color:var(--accent-ink);font-weight:700}
#chap .planout ul{margin:8px 0 0;padding-left:18px}
#chap .planout .w{color:#8a6a30}
@media(max-width:640px){#chap .crow{grid-template-columns:1fr 1fr;gap:5px}
  #chap .crow .del{grid-column:2}}
#lb{position:fixed;inset:0;z-index:50;background:rgba(252,247,245,.93);
  backdrop-filter:blur(10px);display:none;padding:18px;overflow:hidden}
#lb.on{display:flex;align-items:center;justify-content:center;gap:22px}
/* 크게 볼 때도 배경에 랜덤 사진이 은은하게 깔린다 */
#lb .wash{position:absolute;inset:-4%;z-index:0;background-size:cover;background-position:center;
  opacity:.07;filter:blur(14px) saturate(.7);pointer-events:none;transition:opacity 1.2s}
#lb .media-col{flex:1 1 auto;min-width:0;max-height:92vh;position:relative;z-index:1}
#lb .media-row{height:92vh;display:grid;grid-template-columns:56px minmax(0,1fr) 56px;
  align-items:center;gap:10px}
#lb .stage{min-width:0;min-height:0;height:100%;display:flex;align-items:center;justify-content:center;
  max-height:92vh;position:relative}
#lb img,#lb video{max-width:100%;max-height:88vh;border-radius:14px;object-fit:contain;
  box-shadow:var(--sh-lg)}
/* 영상에서 제외한 컷은 상세창에서도 바로 알아보이게 흐리게 표시한다. */
#lb.excluded .stage img,#lb.excluded .stage video{filter:grayscale(1);opacity:.38}
#lb.excluded .stage::after{content:"영상에서 제외됨";position:absolute;left:50%;top:50%;
  transform:translate(-50%,-50%);z-index:8;padding:9px 16px;border-radius:999px;
  background:rgba(73,62,58,.84);color:#fff;font:700 14px/1.2 inherit;pointer-events:none;
  box-shadow:0 3px 14px rgba(0,0,0,.18)}
#lb.excluded aside{background:#f1efee;border-color:#d8d2cf}
#lb.excluded aside>label,#lb.excluded aside>textarea,#lb.excluded aside>input,
#lb.excluded aside>.hint,#lb.excluded aside>.unsaved,#lb.excluded aside>#relLabel,
#lb.excluded aside>#fRel{opacity:.48}
#lb.excluded .tagbox{background:#e7e4e2;border-color:#d2cbc7}
#lb.excluded .tagbox>label:not(:first-child),#lb.excluded .tagbox>.hint,
#lb.excluded .tagbox>.short,#lb.excluded .tagbox>.chips,#lb.excluded .tagbox>.clipbox,
#lb.excluded .tagbox>#clearFocusBtn,#lb.excluded .tagbox>#safeModeBtn,
#lb.excluded .tagbox>#rotateBox,#lb.excluded .tagbox>#fitHint,
#lb.excluded .tagbox>#soloBtn{opacity:.45}
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
/* ---------- 영상 태그 ---------- */
/* 돌잔치 영상을 자동으로 만들 때 쓰는 값들. 누르면 바로 저장된다(따로 [저장] 없음). */
#lb .tagbox{margin-top:18px;padding:15px 16px 17px;border-radius:16px;
  background:#fdf7f4;border:1px solid #f1e3dd}
#lb .tagbox>label:first-child{margin-top:0}
#lb .tagbox .keys{float:right;font-size:11px;color:var(--dim);font-weight:400;letter-spacing:.02em}
#lb .seg{display:flex;gap:7px}
#lb .seg button{flex:1;border:1px solid var(--line);background:#fff;border-radius:11px;
  padding:10px 0;font:14px inherit;cursor:pointer;color:var(--fg);transition:.12s}
#lb .seg button:hover{border-color:var(--accent)}
#lb .seg button.on{background:var(--accent);border-color:var(--accent);color:#fff;font-weight:700}
#lb .seg button.on.no{background:#b0998f;border-color:#b0998f}   /* 제외는 눈에 덜 띄는 색 */
#lb .chips{display:flex;flex-wrap:wrap;gap:6px}
#lb .chips button{border:1px solid var(--line);background:#fff;border-radius:999px;
  padding:7px 12px;font:13px inherit;cursor:pointer;color:var(--fg);transition:.12s}
#lb .chips button:hover{border-color:var(--accent)}
#lb .chips button.on{background:var(--accent-ink);border-color:var(--accent-ink);color:#fff;font-weight:600}
#lb .chips button i{font-style:normal;opacity:.45;font-size:10px;margin-left:5px;text-transform:uppercase}
#lb .chips button.on i{opacity:.8}
#lb .chips .add{border-style:dashed;color:var(--dim)}
#lb .short{display:flex;gap:7px}
#lb .short input{flex:1 1 auto;font-size:16px;padding:11px 13px}
#lb .short button{flex:0 0 auto;padding:0 13px;border:1px solid var(--line);background:#fff;
  border-radius:11px;cursor:pointer;font:13px inherit;color:var(--dim)}
#lb .short button:hover{border-color:var(--accent);color:var(--accent-ink)}
#lb .tagbox .row{margin-top:16px}
/* 영상 구간 — 영상일 때만 보인다 */
#lb .clipbox{display:none}
#lb.isvideo .clipbox{display:block}
#lb .clipnow{font-size:13px;color:var(--accent-ink);background:#fff;border:1px solid var(--line);
  border-radius:11px;padding:9px 12px;margin-bottom:7px;font-variant-numeric:tabular-nums}
#lb .clipnow b{font-weight:700}
#lb .clipExact{display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr) auto;gap:7px;
  align-items:end;margin:0 0 8px}
#lb .clipExact label{display:grid;gap:4px;margin:0;color:var(--dim);font-size:10px;font-weight:600}
#lb .clipExact input{width:100%;box-sizing:border-box;border:1px solid var(--line);border-radius:9px;
  background:#fff;color:var(--fg);padding:8px 9px;font:13px/1.2 inherit;font-variant-numeric:tabular-nums}
#lb .clipExact input:focus{outline:2px solid color-mix(in srgb,var(--accent) 28%,transparent);border-color:var(--accent)}
#lb .clipExact button{height:34px;border:1px solid var(--accent);border-radius:9px;background:#fff;
  color:var(--accent-ink);padding:0 11px;font:600 12px/1 inherit;cursor:pointer;white-space:nowrap}
#lb .clipExact button:hover{background:var(--accent);color:#fff}
@media(max-width:520px){#lb .clipExact{grid-template-columns:1fr 1fr}#lb .clipExact button{grid-column:1/-1}}
#lb .cliprange{position:relative;height:38px;margin:2px 2px 10px;touch-action:none;cursor:pointer}
#lb .cliptrack{position:absolute;left:8px;right:8px;top:16px;height:6px;border-radius:99px;
  background:#eadfda}
#lb .clipfill{position:absolute;top:0;height:100%;border-radius:99px;background:var(--accent)}
#lb .cliphandle{position:absolute;top:5px;width:26px;height:26px;margin-left:-13px;padding:0;
  border:3px solid #fff;border-radius:50%;background:var(--accent-ink);box-shadow:0 2px 8px rgba(80,50,45,.3);
  cursor:ew-resize;touch-action:none}
#lb .cliphandle::after{content:attr(data-label);position:absolute;top:25px;left:50%;transform:translateX(-50%);
  color:var(--dim);font:10px/1.2 inherit;white-space:nowrap}
#lb .seg.four button{font-size:13px;padding:9px 0}
#lb .tagbox .safeAspect{display:flex;align-items:center;gap:7px;margin:5px 0 2px;padding:8px 10px;
  border:1px solid var(--line);border-radius:10px;background:#fff9f7;color:var(--accent-ink);cursor:pointer}
#lb .tagbox .safeAspect input{width:16px;height:16px;margin:0;accent-color:var(--accent)}
#lb .tagbox .safeAspect span{margin-left:auto;color:var(--dim);font-size:10px;font-weight:400}
#lb .safePixels{margin:6px 0;padding:9px 10px;border:1px solid var(--line);border-radius:10px;background:#fff}
#lb .safePixels>small{display:block;margin-bottom:6px;color:var(--dim);font-size:10px}
#lb .safePixelGrid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:6px}
#lb .safePixelGrid label{display:grid;grid-template-columns:auto minmax(0,1fr);align-items:center;gap:5px;
  margin:0;color:var(--dim);font-size:10px;white-space:nowrap}
#lb .safePixelGrid input{min-width:0;width:100%;padding:5px 6px;border:1px solid var(--line);
  border-radius:7px;background:#fff;color:var(--fg);font:12px inherit;font-variant-numeric:tabular-nums}
#lb #applySafePixels{font-weight:700;color:var(--accent-ink)}
/* 키보드가 없는 기기(폰·태블릿)에서도 얼굴 위치를 지울 수 있게 */
#lb .linkbtn{background:none;border:0;color:var(--dim);font:12px inherit;cursor:pointer;
  text-decoration:underline;padding:5px 0 0}
#lb .linkbtn:hover{color:var(--accent-ink)}
#lb .row button.on{background:var(--accent-ink);border-color:var(--accent-ink);color:#fff}
/* 얼굴 위치 표시 — 사진 위 그 지점에 찍히는 과녁 */
#lb:not(.isvideo) .stage img,#lb:not(.isvideo) .stage video{cursor:crosshair;touch-action:none}
#lb.isvideo.safe-mode .stage video{cursor:crosshair;touch-action:none}
#lb.isvideo.safe-mode .stage{outline:2px dashed var(--accent);outline-offset:4px;border-radius:14px}
#lb .stage .focus{position:absolute;width:34px;height:34px;margin:-17px 0 0 -17px;border-radius:50%;
  border:2px solid #fff;box-shadow:0 0 0 2px var(--accent),0 3px 12px rgba(0,0,0,.35);
  pointer-events:none;z-index:4}
#lb .stage .focus::after{content:"";position:absolute;inset:13px;border-radius:50%;background:var(--accent)}
#lb .stage .safe-region{position:absolute;border:3px solid #fff;border-radius:8px;
  box-shadow:0 0 0 2px var(--accent),0 3px 14px rgba(0,0,0,.3);background:rgba(231,155,176,.13);
  pointer-events:none;z-index:5}
#lb .stage .safe-region::after{content:"반드시 남길 영역";position:absolute;left:4px;top:4px;
  padding:2px 6px;border-radius:999px;background:rgba(255,255,255,.92);color:var(--accent-ink);
  font:10px/1.4 inherit;white-space:nowrap}
#lb .stage .safe-region.draft{border-style:dashed}
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
/* 버튼 | 미디어 | 버튼 3열 — 버튼 폭만큼 미디어가 줄어들어 서로 겹치지 않는다. */
#lb .arrow{position:static;width:56px;height:72px;padding:0;background:transparent;border:0;
  cursor:pointer;font-size:0;-webkit-tap-highlight-color:transparent}
#lb .arrow::before{display:flex;align-items:center;justify-content:center;width:52px;height:52px;
  border-radius:50%;background:rgba(255,255,255,.94);border:1px solid #ecd9d2;
  box-shadow:0 2px 10px rgba(140,100,90,.14);color:var(--accent-ink);
  font:400 32px/1 inherit;padding-bottom:4px;transition:.15s}
#lb .prev::before{content:"\2039"}
#lb .next::before{content:"\203A"}
#lb .arrow:hover::before{background:var(--accent);color:#fff;border-color:var(--accent);
  transform:translateY(-1px)}
#lb .arrow:active::before{transform:scale(.96)}
#lb .livetoggle{z-index:9}
#lb .close{z-index:9}

@media(max-width:860px){#lb.on{flex-direction:column;overflow:auto}
  #lb aside{flex:1 1 auto;width:100%;max-height:none}
  #lb .media-col{flex:0 0 auto;width:100%;max-height:none}
  #lb .media-row{height:auto;grid-template-columns:42px minmax(0,1fr) 42px;gap:4px}
  #lb .arrow{width:42px;height:58px}
  #lb .arrow::before{width:40px;height:40px;font-size:27px}
  #lb .stage{flex:0 0 auto;height:auto;max-height:46vh}
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
    <button id="tagBtn" title="돌잔치 영상에 쓸 컷을 고르고 인물·얼굴 위치를 찍습니다">🎬 영상 태깅</button>
    <button id="untaggedBtn" title="아직 고르지 않은 사진만 남깁니다">태깅 안 한 것만</button>
    <button id="saveLabelsBtn" title="현재 화면의 레이블 전체를 파일에 저장하고 이전 판을 백업합니다">💾 레이블 저장</button>
    <button id="chapBtn" title="영상의 챕터·음악을 정하고 컷 리스트를 계산합니다">🎞 챕터·음악</button>
    <a class="plotlink" href="VIDEO_PLOT.html" title="가사 절별 콘티와 슬라이드 시간을 편집합니다">🎵 콘티 페이지</a>
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
    <dt>🎬 영상 태깅 / 태깅 안 한 것만</dt>
    <dd>돌잔치 영상을 자동으로 만들 때 쓸 값을 사진마다 모읍니다. 아직 고르지 않은 사진을
        차례로 열어주고, 진행 상황(<code>63/130</code>)을 알려줍니다.
        <b>여기서는 누르는 즉시 저장됩니다</b> — 아래 요약·날짜·장소와 달리 [저장]이 없습니다.
        <ul style="margin:8px 0 0;padding-left:18px">
        <li><b>영상에 쓸까</b> — <code>1</code> 제외 / <code>2</code> 보통 / <code>3</code> 꼭.
            같은 걸 다시 누르면 해제됩니다. 제외한 컷은 격자에서 흐리게 보입니다.</li>
        <li><b>같이 나온 사람</b> — <code>A S D F …</code> 로 토글. "할머니와 지호"처럼
            사람별 장면을 묶고, 모든 가족이 최소 한 번 나오게 하는 데 씁니다.
            지호는 거의 모든 컷에 있으니 목록에 넣지 않았습니다.</li>
        <li><b>영상 자막</b> — 화면에 띄울 짧은 문구(12~14자). [요약에서]를 누르면 초안이 들어갑니다.</li>
        <li><b>얼굴 위치</b> — 사진에서 얼굴을 클릭해 점을 찍습니다(<code>C</code> 로 지움).
            가로 사진을 세로 영상에 넣거나 확대·이동 효과를 줄 때 <b>얼굴이 잘리지 않게</b> 하는 기준점입니다.</li>
        <li><b>🔒 비공개</b> — <code>P</code>. 목욕·병원 사진처럼 하객 앞에 띄우면 안 되는 컷.
            <code>jiho.py bundle</code> 로 만드는 공유용 번들에서 썸네일까지 빠집니다.</li>
        <li><b>마일스톤</b> — 백일·첫 걸음·여행처럼 <b>챕터를 나누고 "처음으로…" 자막 카드를
            만드는 재료</b>입니다. 해당하는 사진에만 붙이면 됩니다.</li>
        <li><b>영상 구간</b>(영상에서만) — 재생하다가 <code>I</code> 로 시작, <code>O</code> 로 끝을
            찍습니다. 안 잡으면 앞 6초만 씁니다. <code>M</code> 은 소리 — <b>아기 웃음·옹알이가
            든 컷은 소리를 살리고</b>, 그 구간만 배경음악을 줄이도록 계획에 표시됩니다.</li>
        <li><b>한 화면에 몇 장</b> — 세로 사진을 가로 화면에 꽉 채우면 위아래가 크게 잘리고,
            해상도가 모자란 사진은 늘려서 뿌옇게 됩니다. 그런 컷은 <b>2~4장을 한 화면에 나눠
            담아</b> 스틸컷을 붙인 것처럼 보여줍니다(칸이 작아지니 늘릴 필요도 없고 덜 잘립니다).
            자동 판단이 마음에 안 들면 <b>[◻ 단독으로]</b> 로 고정할 수 있습니다.</li>
        <li><code>N</code> 은 아직 안 고른 다음 사진, <code>←</code> <code>→</code> 는 이전·다음입니다.</li>
        </ul></dd>
    <dt>🎞 챕터·음악</dt>
    <dd>영상의 뼈대입니다. <b>챕터</b>마다 기간과 목표 길이(초)를 정하고, <b>음악</b>의 BPM·첫 박·후렴
        구간을 적습니다. [초안 만들기]는 사진이 몰린 정도에 맞춰 챕터를 자동으로 나눠줍니다.
        <ul style="margin:8px 0 0;padding-left:18px">
        <li><b>▶ 영상 계획 만들기</b> — 태그해 둔 컷 중에서 <b>어떤 컷을 몇 번째에 몇 초씩</b> 쓸지
            계산해 <code>VIDEO_PLAN.md</code>(읽기용)와 <code>data/video_plan.json</code>(편집
            프로그램용)으로 내보냅니다.</li>
        <li>BPM 을 넣으면 컷이 <b>박자에 맞고</b>, 후렴 구간에서는 절반 길이로 몰아칩니다.
            영상은 다음 컷이 박에서 밀리지 않도록 뒤를 조금 채웁니다.</li>
        <li><b>화면</b> — 해상도(가로 16:9 / 세로 9:16 …)와 <b>여러 장 묶기</b> 를 정합니다.
            <code>해상도가 모자랄 때만</code>(기본)은 늘려야 뿌예지는 컷만 묶고,
            <code>화면에 안 맞는 사진까지</code>는 <b>세로 사진도 2~3장씩 나란히</b> 넣어
            화면을 채웁니다. ★ 꼭 으로 고른 컷은 묶지 않고 크게 보여줍니다.</li>
        <li><b>제외·비공개만 영상에서 빠집니다.</b> 아직 고르지 않은 컷도 보통으로 취급해
            모두 넣고, 챕터 목표 시간이 모자라면 컷을 버리지 않고 영상 길이를 늘립니다.</li>
        </ul>
        터미널에서는 <code>jiho.py chapters --init</code>, <code>jiho.py music --bpm 92</code>,
        <code>jiho.py plan</code> 으로도 할 수 있습니다.</dd>
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
<div id="chap"><div class="panel">
  <button class="x">&times;</button>
  <h3>🎞 챕터 · 음악</h3>
  <p class="lead">영상의 뼈대입니다. 챕터마다 <b>기간</b>과 <b>목표 길이</b>를 정해두면,
     [영상 계획 만들기]가 태그해 둔 컷을 골라 <b>몇 번째에 몇 초씩</b> 넣을지까지 계산해
     <code>VIDEO_PLAN.md</code> 와 <code>data/video_plan.json</code> 으로 내보냅니다.
     음악 BPM 을 넣으면 컷이 박자에 맞고, 후렴 구간에서는 절반 길이로 몰아칩니다.</p>
  <div class="crow chead"><span>제목</span><span>시작</span><span>끝</span><span>초</span>
    <span>분위기</span><span></span></div>
  <div id="chapList"></div>
  <div class="row">
    <button id="addChap">+ 챕터</button>
    <button id="draftChap" title="사진이 몰린 정도에 맞춰 자동으로 나눕니다">초안 만들기</button>
    <label>전체 목표 <input id="chapTarget" type="number" min="10" step="10"> 초</label>
  </div>
  <h4>화면</h4>
  <div class="musicgrid">
    <label>해상도
      <select id="fSize">
        <option value="1920x1080">가로 16:9 — 1920×1080</option>
        <option value="3840x2160">가로 4K — 3840×2160</option>
        <option value="1080x1920">세로 9:16 — 1080×1920</option>
        <option value="1080x1080">정사각 — 1080×1080</option>
      </select></label>
    <label>여러 장 묶기
      <select id="fMode">
        <option value="auto">해상도가 모자랄 때만</option>
        <option value="fill">화면에 안 맞는 사진까지 (세로 사진)</option>
        <option value="off">안 묶음</option>
      </select></label>
    <label>최대 확대<input id="fUp" type="number" step="0.05" min="1" placeholder="1.15"></label>
  </div>
  <h4>음악</h4>
  <div class="musicgrid">
    <label>파일<input id="mFile" placeholder="music/main.m4a"></label>
    <label>BPM<input id="mBpm" type="number" step="0.1" placeholder="92"></label>
    <label>첫 박(초)<input id="mOff" type="number" step="0.01" placeholder="0.35"></label>
    <label>후렴 구간<input id="mChorus" placeholder="48-80, 140-172"></label>
  </div>
  <div class="row">
    <button class="primary" id="saveChap">저장</button>
    <button id="makePlan">▶ 영상 계획 만들기</button>
    <label>제외·비공개만 빼고 모든 사진과 영상을 포함합니다</label>
  </div>
  <div class="planout" id="planOut"></div>
</div></div>
<div id="lb">
  <div class="wash"></div>
  <button class="close">&times;</button>
  <div class="media-col">
    <div class="media-row">
      <button class="arrow prev" aria-label="이전 사진">&#8249;</button>
      <div class="stage"></div>
      <button class="arrow next" aria-label="다음 사진">&#8250;</button>
    </div>
  </div>
  <aside>
    <h4 id="lbTitle"></h4><div class="sub" id="lbSub"></div>
    <div class="tagbox">
      <label>영상에 쓸까 <span class="keys">1 2 3</span></label>
      <div class="seg" id="fPick">
        <button data-v="0" class="no">✕ 제외</button>
        <button data-v="1">· 보통</button>
        <button data-v="2">★ 꼭</button>
      </div>
      <label>같이 나온 사람 <span class="keys">A S D F G H J K L</span></label>
      <div class="chips" id="fPeople"></div>
      <label>마일스톤 <span class="keys">챕터·자막 카드의 재료</span></label>
      <div class="chips" id="fTags"></div>
      <div class="clipbox">
        <label>영상 구간 <span class="keys">I 시작 · O 끝 · M 소리</span></label>
        <div class="clipnow" id="clipNow"></div>
        <div class="clipExact">
          <label>시작 초<input id="clipStartExact" type="number" min="0" step="0.01" inputmode="decimal"></label>
          <label>끝 초<input id="clipEndExact" type="number" min="0" step="0.01" inputmode="decimal"></label>
          <button id="applyClipExact" type="button">정확한 구간 적용</button>
        </div>
        <div class="cliprange" id="clipRange">
          <div class="cliptrack"><div class="clipfill"></div></div>
          <button class="cliphandle in" data-which="in" data-label="시작" aria-label="구간 시작"></button>
          <button class="cliphandle out" data-which="out" data-label="끝" aria-label="구간 끝"></button>
        </div>
        <div class="seg four">
          <button id="clipIn">I 시작</button><button id="clipOut">O 끝</button>
          <button id="clipPlay">▶ 구간</button><button id="clipClear">지우기</button>
        </div>
        <button class="linkbtn" id="audioBtn"></button>
      </div>
      <label>영상 자막 <span class="keys">12~14자</span></label>
      <div class="short">
        <input id="fShort" maxlength="40" placeholder="예: 백일, 처음 웃던 날">
        <button id="shortFromSum" title="요약 앞부분을 가져옵니다">요약에서</button>
      </div>
      <label>반드시 남길 영역 <span class="keys">사진 위에서 드래그 · C 지우기</span></label>
      <label class="safeAspect"><input id="safeAspectLock" type="checkbox" checked> 16:9 가로 비율 고정 <span>체크 해제 시 자유 비율</span></label>
      <div class="hint" id="focusHint"></div>
      <div class="safePixels" id="safePixels" hidden>
        <small id="safePixelSize"></small>
        <div class="safePixelGrid">
          <label>시작 X <input id="safeX1" type="number" min="0" step="1"></label>
          <label>시작 Y <input id="safeY1" type="number" min="0" step="1"></label>
          <label>끝 X <input id="safeX2" type="number" min="0" step="1"></label>
          <label>끝 Y <input id="safeY2" type="number" min="0" step="1"></label>
        </div>
        <button class="linkbtn" id="applySafePixels" type="button">픽셀 좌표 적용</button>
      </div>
      <button class="linkbtn" id="safeModeBtn" hidden>▣ 영상에서 필수 영역 선택</button>
      <button class="linkbtn" id="clearFocusBtn" hidden>필수 영역 지우기</button>
      <div id="rotateBox">
        <label>사진 회전 <span class="keys">원본은 바꾸지 않음</span></label>
        <div class="seg" id="fRotate">
          <button data-step="-90">↶ 왼쪽</button><button data-reset="1">원래대로</button>
          <button data-step="90">오른쪽 ↷</button>
        </div>
      </div>
      <label>한 화면에 몇 장 <span class="keys">해상도·화면비로 자동 판단</span></label>
      <div class="hint" id="fitHint"></div>
      <button class="linkbtn" id="soloBtn"></button>
      <div class="row">
        <button id="privBtn" title="공유 번들·상영 화면에서 뺍니다">🔒 비공개</button>
        <button id="nextTagBtn" title="아직 고르지 않은 다음 사진으로">아직 안 고른 다음 →</button>
      </div>
      <div class="row">
        <button class="primary" id="saveLabelsHereBtn" title="지금까지 입력한 모든 레이블을 파일에 저장하고 이전 판을 백업합니다">💾 지금까지 레이블 전체 저장</button>
      </div>
    </div>
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
// 편집 서버인지 확인. 서버에서는 곧바로 파일에 저장되므로 내보내기 버튼이 필요 없다.
fetch('/api/ping',{method:'POST'}).then(r=>r.json()).then(j=>{
  if(!j.ok) throw new Error('offline');
  $('#exportBtn')?.remove();
}).catch(()=>{
  live=false; say('서버 없이 열렸습니다 — 수정은 브라우저에 저장되고 [수정본 내보내기]로 반영합니다','err');
});

function stash(file,patch){
  pending[file]=Object.assign(pending[file]||{},patch);
  localStorage.setItem('jiho.pending',JSON.stringify(pending));
}

let liveOn=true, safeMode=false;   // 모션 포토 재생 / 일반 영상 필수 영역 선택 모드
const safeAspectLock=$('#safeAspectLock');
safeAspectLock.checked=localStorage.getItem('jiho.safeAspect16x9')!=='0';
safeAspectLock.onchange=()=>localStorage.setItem('jiho.safeAspect16x9',safeAspectLock.checked?'1':'0');
function safeMediaPixels(t){const media=stage.querySelector('img,video'),d=shots[cur].dataset;let w=media?.naturalWidth||media?.videoWidth||+d.w||0,h=media?.naturalHeight||media?.videoHeight||+d.h||0;if(t.rotation%180)[w,h]=[h,w];return [Math.round(w),Math.round(h)]}
function renderSafePixels(t){const box=$('#safePixels');box.hidden=!t.safe;if(!t.safe)return;const paint=()=>{const [w,h]=safeMediaPixels(t);if(!w||!h){$('#safePixelSize').textContent='원본 픽셀 크기를 불러오는 중…';return}const [x1,y1,x2,y2]=t.safe;$('#safePixelSize').textContent=`회전 적용 기준 ${w} × ${h}px · 선택 ${Math.round((x2-x1)*w)} × ${Math.round((y2-y1)*h)}px`;for(const [id,value,max] of [['safeX1',x1*w,w],['safeY1',y1*h,h],['safeX2',x2*w,w],['safeY2',y2*h,h]]){const input=$('#'+id);input.max=max;input.value=Math.round(value)}};paint();const media=stage.querySelector('img,video');if(media&&!(media.naturalWidth||media.videoWidth))media.addEventListener(media.tagName==='IMG'?'load':'loadedmetadata',paint,{once:true})}
function keepVideoInSelectedClip(v,s){
  const selected=()=>s.dataset.clip?s.dataset.clip.split(',').map(Number):null;
  const bounds=()=>{
    const c=selected();if(!c)return null;
    const total=v.duration||Infinity;
    return [Math.max(0,c[0]),Math.min(total,c[1])];
  };
  const start=()=>{
    const c=bounds();if(!c)return;
    v.currentTime=c[0];v.play().catch(()=>{});
  };
  v.addEventListener('loadedmetadata',start,{once:true});
  v.addEventListener('play',()=>{
    const c=bounds();if(!c)return;
    if(v.currentTime<c[0]-.05||v.currentTime>=c[1]-.05)v.currentTime=c[0];
  });
  v.addEventListener('timeupdate',()=>{
    const c=bounds();if(!c||v.paused)return;
    if(v.currentTime>=c[1]-.03){v.pause();v.currentTime=c[0];}
  });
}
function render(){
  const s=shots[cur],d=s.dataset;
  if(d.kind==='video'){
    stage.innerHTML=`<video src="${d.path}" controls autoplay playsinline></video>`;
    keepVideoInSelectedClip(stage.querySelector('video'),s);
  }else if(d.motion && liveOn){
    stage.innerHTML=`<video src="${d.motion}" autoplay loop muted playsinline></video>`
      +`<button class="livetoggle on" title="정지 사진으로">◉ LIVE</button>`;
  }else{
    stage.innerHTML=`<img src="${d.path}">`
      +(d.motion?`<button class="livetoggle" title="움직이는 사진으로">◉ LIVE</button>`:'');
  }
  const t=stage.querySelector('.livetoggle');
  if(t) t.onclick=e=>{e.stopPropagation();liveOn=!liveOn;render();};
  applyStageRotation();
}
function applyStageRotation(){
  const media=stage.querySelector('img,video');if(!media)return;
  const rot=+(shots[cur].dataset.rot||0);
  const fit=()=>{
    media.style.cssText='';
    if(!rot){drawFocus();return;}
    const nw=media.naturalWidth||media.videoWidth, nh=media.naturalHeight||media.videoHeight;
    const aw=stage.clientWidth, ah=stage.clientHeight;
    if(!nw||!nh||!aw||!ah)return;
    const swap=rot===90||rot===270;
    const scale=Math.min(aw/(swap?nh:nw),ah/(swap?nw:nh));
    media.style.width=(nw*scale)+'px';media.style.height=(nh*scale)+'px';
    media.style.maxWidth='none';media.style.maxHeight='none';
    media.style.transform=`rotate(${rot}deg)`;media.style.transformOrigin='center';
    drawFocus();
  };
  if(media.tagName==='IMG'&&media.complete)fit();
  else if(media.tagName==='VIDEO'&&media.readyState>=1)fit();
  else media.addEventListener(media.tagName==='IMG'?'load':'loadedmetadata',fit,{once:true});
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
  safeMode=false;lb.classList.remove('safe-mode');
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
  lb.classList.toggle('isvideo', d.kind==='video');
  renderTags();          // 사진 위 과녁을 그리려면 라이트박스가 보인 뒤여야 한다
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
    paintCaption(s);
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
// ── 영상 태그 ──────────────────────────────────────────
// 돌잔치 영상을 자동으로 만들려면 "쓸 컷인지 / 누가 나오는지 / 어디를 잘라야
// 얼굴이 살아남는지"가 데이터에 있어야 한다. 130장을 빠르게 훑는 작업이라
// 여기서는 누르는 즉시 저장한다 — 요약·날짜·장소의 [✎ 수정]과 다른 방식이다.
const PKEYS='asdfghjkl';
let roster={{ROSTER}}, milestones={{MILESTONES}};
const esc=s=>String(s).replace(/[<>&"]/g,c=>({'<':'&lt;','>':'&gt;','&':'&amp;','"':'&quot;'}[c]));
// 일반 썸네일은 영상 자막만 보여준다. 격자 요약 편집 모드에서만 요약을 표시한다.
function paintCaption(s){
  const editing=document.body.classList.contains('edit');
  const text=editing?(s.dataset.cap||''):(s.dataset.short||'');
  s.querySelector('figcaption').innerHTML=text?esc(text):`<i>${editing?'요약 없음':'영상 자막 없음'}</i>`;
}

const tagOf=s=>({
  pick:   s.dataset.pick===''?null:+s.dataset.pick,
  priv:   s.dataset.priv==='1',
  focus:  s.dataset.focus?s.dataset.focus.split(',').map(Number):null,
  safe:   s.dataset.safe?s.dataset.safe.split(',').map(Number):null,
  rotation:+(s.dataset.rot||0),
  face:   s.dataset.face||'',
  people: s.dataset.ppl?s.dataset.ppl.split(','):[],
  short:  s.dataset.short||'',
  solo:   s.dataset.solo==='1',
  tags:   s.dataset.tg?s.dataset.tg.split(','):[],
  clip:   s.dataset.clip?s.dataset.clip.split(',').map(Number):null,
  audio:  s.dataset.audio||'mute',
});
function tagStats(){
  let done=0,must=0,drop=0;
  shots.forEach(s=>{const p=s.dataset.pick; if(p==='')return;
                    done++; if(p==='2')must++; if(p==='0')drop++;});
  return {done,must,drop,total:shots.length};
}
// 격자 쪽 표시(테두리·배지)를 데이터에 맞춘다
function paintShot(s){
  const t=tagOf(s);
  s.classList.remove('pick0','pick1','pick2','untagged');
  s.classList.add(t.pick===null?'untagged':'pick'+t.pick);
  s.classList.toggle('priv',t.priv);
  const marks=[t.pick===2?'★':t.pick===1?'·':t.pick===0?'✕':'', t.priv?'🔒':'',
               t.safe?'▣':t.focus?'◎':'', t.rotation?'↻':'', t.clip?'✂':'',
               t.audio==='keep'?'🔊':'', t.solo?'◻':'',
               t.people.length?`<em>${t.people.length}</em>`:''].filter(Boolean).join('');
  let el=s.querySelector('.tagmark');
  if(!marks){ if(el) el.remove(); return; }
  if(!el){ el=document.createElement('span'); el.className='tagmark';
           s.insertBefore(el,s.querySelector('figcaption')); }
  el.innerHTML=marks;
}
function applyTag(s,patch){
  if('pick' in patch)    s.dataset.pick  = patch.pick===null?'':String(patch.pick);
  if('private' in patch) s.dataset.priv  = patch.private?'1':'';
  if('focus' in patch)   s.dataset.focus = patch.focus?patch.focus.map(v=>+v.toFixed(4)).join(','):'';
  if('safe' in patch)    s.dataset.safe  = patch.safe?patch.safe.map(v=>+v.toFixed(4)).join(','):'';
  if('rotation' in patch)s.dataset.rot   = String((+patch.rotation||0)%360);
  if('face' in patch)    s.dataset.face  = patch.face||'';
  if('people' in patch)  s.dataset.ppl   = (patch.people||[]).join(',');
  if('short' in patch){  s.dataset.short = patch.short||''; paintCaption(s); }
  if('tags' in patch)    s.dataset.tg    = (patch.tags||[]).join(',');
  if('clip' in patch)    s.dataset.clip  = patch.clip?patch.clip.map(v=>+v.toFixed(2)).join(','):'';
  if('audio' in patch)   s.dataset.audio = patch.audio==='keep'?'keep':'';
  if('solo' in patch)    s.dataset.solo  = patch.solo?'1':'';
  paintShot(s);paintSafeThumb(s);
}
function paintRotation(s){
  const rot=+(s.dataset.rot||0);
  let base=s.dataset.shape||'sq';
  if(s.dataset.safe){
    const [x1,y1,x2,y2]=s.dataset.safe.split(',').map(Number);
    let w=+s.dataset.w||1,h=+s.dataset.h||1;if(rot%180)[w,h]=[h,w];
    const ratio=((x2-x1)*w)/Math.max(.0001,(y2-y1)*h);
    base=ratio>1.15?'ls':ratio<.87?'pt':'sq';
  }
  s.classList.remove('rot90','rot180','rot270','ls','pt','sq');
  if(rot)s.classList.add('rot'+rot);
  s.classList.add(s.dataset.safe?base:(rot%180?({ls:'pt',pt:'ls'}[base]||base):base));
}
// 원래 썸네일을 캔버스에서 화면 방향으로 회전한 뒤, 필수 영역만 정확히 잘라
// 다시 썸네일에 넣는다. 원본 파일이나 기존 썸네일 파일은 수정하지 않는다.
function paintSafeThumb(s){
  const im=s.querySelector(':scope > img');
  if(!im){paintRotation(s);return;}
  if(!im.dataset.thumbSrc)im.dataset.thumbSrc=im.getAttribute('src')||'';
  const src=im.dataset.thumbSrc,safe=s.dataset.safe?s.dataset.safe.split(',').map(Number):null;
  const token=String(+(s.dataset.cropToken||0)+1);s.dataset.cropToken=token;
  s.classList.toggle('safe-thumb',!!safe);paintRotation(s);
  if(!safe){if(src&&im.getAttribute('src')!==src)im.src=src;return;}
  const source=new Image();source.onload=()=>{
    if(s.dataset.cropToken!==token||!s.dataset.safe)return;
    const w=source.naturalWidth,h=source.naturalHeight,rot=+(s.dataset.rot||0);
    if(!w||!h)return;
    const swap=rot===90||rot===270,rw=swap?h:w,rh=swap?w:h;
    const oriented=document.createElement('canvas');oriented.width=rw;oriented.height=rh;
    const oc=oriented.getContext('2d');oc.translate(rw/2,rh/2);oc.rotate(rot*Math.PI/180);
    oc.drawImage(source,-w/2,-h/2);
    const [x1,y1,x2,y2]=safe,sx=x1*rw,sy=y1*rh,sw=Math.max(1,(x2-x1)*rw),sh=Math.max(1,(y2-y1)*rh);
    const scale=Math.min(1,480/Math.max(sw,sh)),out=document.createElement('canvas');
    out.width=Math.max(1,Math.round(sw*scale));out.height=Math.max(1,Math.round(sh*scale));
    out.getContext('2d').drawImage(oriented,sx,sy,sw,sh,0,0,out.width,out.height);
    try{im.src=out.toDataURL('image/jpeg',.88);}catch(_e){/* 원래 썸네일 유지 */}
  };
  source.src=src;
}
shots.forEach(paintSafeThumb);
async function saveTag(patch,msg){
  const s=shots[cur];
  try{
    if(live) await api('/api/tag',{file:s.dataset.file,...patch});
    else stash('__tag__'+s.dataset.file,patch);
    applyTag(s,patch); renderTags();
    if(msg!==false){ const t=tagStats();
      say(`${msg||'저장'} · ${t.done}/${t.total} (꼭 ${t.must} · 제외 ${t.drop})`,'ok'); }
  }catch(e){ say('태그 저장 실패: '+e.message,'err'); }
}
function allLabels(){
  const out={};
  shots.forEach(s=>{
    const t=tagOf(s), entry={pick:t.pick,private:t.priv,rotation:t.rotation,
      focus:t.focus,safe:t.safe,face:t.face,people:t.people,short:t.short,
      solo:t.solo,tags:t.tags,clip:t.clip,audio:t.audio};
    // 서버가 빈 값은 정리하므로, 여기서는 화면 상태를 빠짐없이 보낸다.
    out[s.dataset.file]=entry;
  });
  return out;
}
async function saveAllLabels(){
  if(!live){
    Object.entries(allLabels()).forEach(([file,tag])=>stash('__tag__'+file,tag));
    say('브라우저에 레이블 전체를 저장했습니다 (수정본 내보내기 필요)','ok');
    return;
  }
  const buttons=['#saveLabelsBtn','#saveLabelsHereBtn'].map($).filter(Boolean);
  buttons.forEach(b=>{b.disabled=true;b.dataset.old=b.textContent;b.textContent='저장 중…';});
  try{
    const j=await api('/api/tags',{tags:allLabels()});
    const backup=j.backup?` · 이전 판 백업: ${j.backup}`:'';
    say(`레이블 ${j.count}개를 파일에 저장했습니다${backup}`,'ok');
  }catch(e){
    say('레이블 전체 저장 실패: '+e.message,'err');
  }finally{
    buttons.forEach(b=>{b.disabled=false;b.textContent=b.dataset.old||'💾 레이블 저장';});
  }
}
$('#saveLabelsBtn').onclick=saveAllLabels;
$('#saveLabelsHereBtn').onclick=saveAllLabels;
function renderTags(){
  const t=tagOf(shots[cur]);
  lb.classList.toggle('excluded',t.pick===0);
  $('#fPick').querySelectorAll('button').forEach(b=>b.classList.toggle('on',+b.dataset.v===t.pick));
  $('#privBtn').classList.toggle('on',t.priv);
  $('#privBtn').textContent = t.priv?'🔒 비공개 — 영상에서 뺌':'🔒 비공개';
  const box=$('#fPeople');
  box.innerHTML = roster.map((n,i)=>
      `<button data-n="${esc(n)}"${t.people.includes(n)?' class="on"':''}>${esc(n)}`
      + (i<PKEYS.length?`<i>${PKEYS[i]}</i>`:'') + `</button>`).join('')
    + `<button class="add" id="addPerson" title="목록에 사람을 추가합니다">+ 사람</button>`;
  box.querySelectorAll('button[data-n]').forEach(b=>b.onclick=()=>togglePerson(b.dataset.n));
  $('#addPerson').onclick=addPerson;
  const tb=$('#fTags');
  tb.innerHTML = milestones.map(n=>
      `<button data-t="${esc(n)}"${t.tags.includes(n)?' class="on"':''}>${esc(n)}</button>`).join('')
    + `<button class="add" id="addTag" title="목록에 항목을 추가합니다">+ 항목</button>`;
  tb.querySelectorAll('button[data-t]').forEach(b=>b.onclick=()=>toggleTag(b.dataset.t));
  $('#addTag').onclick=addMilestone;
  renderClip(t);
  if(document.activeElement!==$('#fShort')) $('#fShort').value=t.short;
  $('#focusHint').textContent = t.safe
    ? `지정됨 — 사진의 ${Math.round((t.safe[2]-t.safe[0])*100)}% × ${Math.round((t.safe[3]-t.safe[1])*100)}% 영역을 반드시 남깁니다`
    : t.focus
      ? '기존 얼굴 점이 있습니다. 사진 위를 드래그하면 필수 영역으로 바뀝니다.'
      : shots[cur].dataset.kind==='video'
        ? '아래 버튼을 누른 뒤 영상 프레임에서 빠지면 안 되는 부분을 드래그하세요'
        : '사진 위에서 빠지면 안 되는 부분을 직사각형으로 드래그하세요';
  renderSafePixels(t);
  $('#clearFocusBtn').hidden=!(t.safe||t.focus);
  $('#safeModeBtn').hidden=shots[cur].dataset.kind!=='video';
  $('#safeModeBtn').textContent=safeMode?'영역 선택 중 — 취소':'▣ 영상에서 필수 영역 선택';
  $('#rotateBox').hidden=false;
  $('#fRotate').querySelectorAll('button').forEach(b=>
    b.classList.toggle('on',b.dataset.reset==='1'&&t.rotation===0));
  renderFit(t);
  drawFocus();
}
// 이 사진을 화면에 꽉 채우면 얼마나 늘려야 하고 얼마나 잘리는지 —
// 계획(plan)이 쓰는 것과 같은 계산이라 여기서 미리 보여준다
function renderFit(t){
  const d=shots[cur].dataset;let w=+d.w||0,h=+d.h||0;
  if(t.rotation%180)[w,h]=[h,w];
  const W=CHAPS.width||1920, H=CHAPS.height||1080, MAX=CHAPS.max_upscale||1.15;
  const mode=CHAPS.group_mode||'auto';
  if(!w||!h){ $('#fitHint').textContent='크기를 알 수 없는 파일입니다';
              $('#soloBtn').hidden=true; return; }
  const s=Math.max(W/w,H/h), keep=Math.min(1,(W/s)/w)*Math.min(1,(H/s)/h);
  const cut=Math.round((1-keep)*100), up=s.toFixed(2);
  let why='';
  if(d.kind==='video') why='';
  else if(s>MAX) why=`해상도 부족 — ${up}배 늘려야 합니다`;
  else if(mode==='fill'&&keep<0.45&&t.pick!==2) why=`꽉 채우면 ${cut}% 가 잘립니다`;
  $('#fitHint').innerHTML = `원본 ${w}×${h} · 화면 ${W}×${H} 기준 `
    + (s>1 ? `<b>${up}배 확대</b>` : `확대 없음`) + ` · ${cut}% 잘림`
    + (t.solo ? ' — <b>단독 지정</b>'
      : why ? ` → <b>다른 사진과 묶어 한 화면에</b> (${why})`
            : ' — 한 화면에 단독으로 들어갑니다');
  $('#soloBtn').hidden = d.kind==='video';
  $('#soloBtn').textContent = t.solo
    ? '◻ 단독 지정 해제 — 자동 판단에 맡기기'
    : '◻ 이 사진은 묶지 말고 단독으로';
}
// 필수 영역 사각형(새 방식) 또는 예전 얼굴 점을 미디어 위에 얹는다.
function drawFocus(){
  stage.querySelectorAll('.focus,.safe-region').forEach(x=>x.remove());
  const d=shots[cur].dataset, media=stage.querySelector('img,video');
  if((!d.safe&&!d.focus)||!media) return;
  const put=()=>{
    if(!lb.classList.contains('on')||!stage.contains(media)) return;
    const r=media.getBoundingClientRect(), sr=stage.getBoundingClientRect();
    if(!r.width) return;
    const m=document.createElement('div');
    if(d.safe){
      const [x1,y1,x2,y2]=d.safe.split(',').map(Number); m.className='safe-region';
      m.style.left=(r.left-sr.left+x1*r.width)+'px';m.style.top=(r.top-sr.top+y1*r.height)+'px';
      m.style.width=((x2-x1)*r.width)+'px';m.style.height=((y2-y1)*r.height)+'px';
    }else{
      const [x,y]=d.focus.split(',').map(Number); m.className='focus';
      m.style.left=(r.left-sr.left+x*r.width)+'px';m.style.top=(r.top-sr.top+y*r.height)+'px';
    }
    stage.appendChild(m);
  };
  if(media.tagName==='IMG'&&media.complete) put();
  else if(media.tagName==='VIDEO'&&media.readyState>=1) put();
  else media.addEventListener(media.tagName==='IMG'?'load':'loadedmetadata',put,{once:true});
}
function togglePick(v){
  const t=tagOf(shots[cur]);
  saveTag({pick:t.pick===v?null:v}, t.pick===v?'선택 해제':{0:'✕ 제외',1:'· 보통',2:'★ 꼭'}[v]);
}
function togglePerson(n){
  const t=tagOf(shots[cur]);
  const people=t.people.includes(n)?t.people.filter(x=>x!==n):t.people.concat([n]);
  saveTag({people}, people.length?`인물: ${people.join(', ')}`:'인물 없음');
}
function toggleTag(n){
  const t=tagOf(shots[cur]);
  const tags=t.tags.includes(n)?t.tags.filter(x=>x!==n):t.tags.concat([n]);
  saveTag({tags}, tags.length?`마일스톤: ${tags.join(', ')}`:'마일스톤 없음');
}
async function addPerson(){
  const n=(prompt('추가할 사람 이름 (예: 고모)')||'').trim();
  if(!n) return;
  if(!roster.includes(n)){
    roster=roster.concat([n]);
    try{ if(live) await api('/api/note',{roster}); else stash('__roster__',{roster}); }
    catch(e){ say('사람 목록 저장 실패: '+e.message,'err'); }
  }
  togglePerson(n);
}
async function addMilestone(){
  const n=(prompt('추가할 마일스톤 (예: 첫 수영)')||'').trim();
  if(!n) return;
  if(!milestones.includes(n)){
    milestones=milestones.concat([n]);
    try{ if(live) await api('/api/note',{milestones}); else stash('__roster__',{milestones}); }
    catch(e){ say('마일스톤 목록 저장 실패: '+e.message,'err'); }
  }
  toggleTag(n);
}

// ── 영상 구간 ──────────────────────────────────────────
// 아기 웃음소리가 든 3초가 사진 스무 장보다 세다. 어디를 쓸지와
// 소리를 살릴지를 여기서 정한다. (영상에만 나타난다)
const vid=()=>stage.querySelector('video');
const secs=v=>`${v.toFixed(2)}초`;
function renderClip(t){
  if(!lb.classList.contains('isvideo')) return;
  const total=+(shots[cur].dataset.dur||0);
  const shown=t.clip||[0,Math.min(6,total||6)];
  $('#clipNow').innerHTML = t.clip
    ? `<b>${secs(t.clip[0])} → ${secs(t.clip[1])}</b> · 길이 ${secs(t.clip[1]-t.clip[0])}`
      + (total?` <span style="opacity:.55">/ 전체 ${secs(total)}</span>`:'')
    : `구간을 안 잡으면 <b>앞 ${secs(Math.min(6,total||6))}</b> 를 그대로 씁니다`
      + (total?` <span style="opacity:.55">(전체 ${secs(total)})</span>`:'');
  const startInput=$('#clipStartExact'),endInput=$('#clipEndExact');
  if(document.activeElement!==startInput)startInput.value=(+shown[0]).toFixed(2);
  if(document.activeElement!==endInput)endInput.value=(+shown[1]).toFixed(2);
  if(total){startInput.max=total.toFixed(2);endInput.max=total.toFixed(2)}
  else{startInput.removeAttribute('max');endInput.removeAttribute('max')}
  $('#audioBtn').textContent = t.audio==='keep'
    ? '🔊 소리 살림 — 배경음악을 이 구간만 줄입니다 (끄려면 클릭)'
    : '🔇 음소거 — 아기 목소리를 살리려면 클릭 (M)';
  paintClipRange(t.clip||[0,Math.min(6,total||6)],total||6);
}
function paintClipRange(clip,total){
  const [a,b]=clip, ap=Math.max(0,Math.min(100,a/total*100)), bp=Math.max(ap,Math.min(100,b/total*100));
  const box=$('#clipRange');
  box.querySelector('.clipfill').style.cssText=`left:${ap}%;width:${bp-ap}%`;
  box.querySelector('.cliphandle.in').style.left=ap+'%';
  box.querySelector('.cliphandle.out').style.left=bp+'%';
  box.querySelector('.cliphandle.in').dataset.label=secs(a);
  box.querySelector('.cliphandle.out').dataset.label=secs(b);
}
let clipDrag=null;
$('#clipRange').addEventListener('pointerdown',e=>{
  const v=vid(); if(!v)return;
  v.pause();
  const total=v.duration||+(shots[cur].dataset.dur||0); if(!total)return;
  let which=e.target.closest('.cliphandle')?.dataset.which;
  const r=$('#clipRange').getBoundingClientRect(), pos=Math.max(0,Math.min(total,(e.clientX-r.left)/r.width*total));
  const current=tagOf(shots[cur]).clip||[0,Math.min(6,total)];
  if(!which) which=Math.abs(pos-current[0])<=Math.abs(pos-current[1])?'in':'out';
  clipDrag={id:e.pointerId,which,total,clip:[...current]};
  $('#clipRange').setPointerCapture(e.pointerId);e.preventDefault();
});
$('#clipRange').addEventListener('pointermove',e=>{
  if(!clipDrag||e.pointerId!==clipDrag.id)return;
  const r=$('#clipRange').getBoundingClientRect();
  let pos=Math.max(0,Math.min(clipDrag.total,(e.clientX-r.left)/r.width*clipDrag.total));
  if(clipDrag.which==='in')clipDrag.clip[0]=Math.min(pos,clipDrag.clip[1]-.2);
  else clipDrag.clip[1]=Math.max(pos,clipDrag.clip[0]+.2);
  clipDrag.clip=clipDrag.clip.map(x=>+x.toFixed(2));
  paintClipRange(clipDrag.clip,clipDrag.total);
  const v=vid();if(v)v.currentTime=clipDrag.which==='in'?clipDrag.clip[0]:clipDrag.clip[1];
});
$('#clipRange').addEventListener('pointerup',e=>{
  if(!clipDrag||e.pointerId!==clipDrag.id)return;
  const clip=clipDrag.clip;clipDrag=null;
  saveTag({clip},`영상 구간 ${secs(clip[0])} → ${secs(clip[1])}`);
});
$('#clipRange').addEventListener('pointercancel',()=>{clipDrag=null;renderClip(tagOf(shots[cur]));});
function setClipPoint(which){
  const v=vid();
  if(!v) return say('영상에서만 쓸 수 있습니다','err');
  const t=+v.currentTime.toFixed(2), total=v.duration||+(shots[cur].dataset.dur||0)||t+6;
  const c=tagOf(shots[cur]).clip;
  let a,b;
  if(which==='in'){ a=t; b=(c&&c[1]>t)?c[1]:Math.min(total,t+6); }
  else            { b=t; a=(c&&c[0]<t)?c[0]:Math.max(0,t-6); }
  if(b-a<0.2) return say('구간이 너무 짧습니다 (0.2초 이상)','err');
  saveTag({clip:[a,b]}, which==='in'?`시작 ${secs(a)}`:`끝 ${secs(b)}`);
}
function applyExactClip(){
  const startInput=$('#clipStartExact'),endInput=$('#clipEndExact');
  let a=Number(startInput.value),b=Number(endInput.value);
  const v=vid(),total=(v&&Number.isFinite(v.duration)&&v.duration>0?v.duration:0)
    || +(shots[cur].dataset.dur||0);
  if(!Number.isFinite(a)||!Number.isFinite(b))return say('시작 초와 끝 초를 모두 숫자로 입력해 주세요','err');
  if(a<0)return say('시작 초는 0 이상이어야 합니다','err');
  if(b<=a)return say('끝 초는 시작 초보다 커야 합니다','err');
  if(b-a<.2)return say('구간이 너무 짧습니다 (0.2초 이상)','err');
  if(total&&b>total+.005)return say(`끝 초는 전체 영상 길이 ${secs(total)}를 넘을 수 없습니다`,'err');
  a=+a.toFixed(2);b=+Math.min(b,total||b).toFixed(2);
  startInput.value=a.toFixed(2);endInput.value=b.toFixed(2);
  saveTag({clip:[a,b]},`영상 구간 ${secs(a)} → ${secs(b)}`);
}
function playClip(){
  const v=vid(), c=tagOf(shots[cur]).clip;
  if(!v) return;
  const [a]=c||[0,Math.min(6,v.duration||6)];
  v.currentTime=a; v.play().catch(()=>{});
}
// 요약에서 자막 초안: '긴 설명 — 짧은 말' 중 짧은 쪽을 쓴다.
// 길면 단어 경계에서 자르되, 조금 넘는 정도는 그대로 둔다(말이 잘리는 게 더 나쁘다).
function shortFrom(cap){
  const parts=cap.split(/\s*[—–]\s*/).map(x=>x.trim()).filter(Boolean);
  let t=(parts.sort((a,b)=>a.length-b.length)[0]||cap).trim();
  if(t.length>18){ const cut=t.slice(0,18), sp=cut.lastIndexOf(' ');
                   t=(sp>8?cut.slice(0,sp):cut).trim(); }
  return t;
}
async function nextUntagged(){
  const i=shots.findIndex((s,k)=>k>cur&&s.dataset.pick==='');
  const j=i>=0?i:shots.findIndex(s=>s.dataset.pick==='');
  if(j<0) return say('모든 사진을 다 골랐습니다 🎉','ok');
  await go(j);
}
$('#fPick').querySelectorAll('button').forEach(b=>b.onclick=()=>togglePick(+b.dataset.v));
$('#privBtn').onclick=()=>{const t=tagOf(shots[cur]);
  saveTag({private:!t.priv}, t.priv?'비공개 해제':'🔒 비공개 — 공유·영상에서 뺍니다');};
$('#nextTagBtn').onclick=nextUntagged;
$('#clearFocusBtn').onclick=()=>saveTag({safe:null,focus:null},'필수 영역 지움');
$('#applySafePixels').onclick=()=>{const t=tagOf(shots[cur]),[w,h]=safeMediaPixels(t);if(!w||!h)return say('원본 픽셀 크기를 아직 불러오지 못했습니다','err');let x1=+$('#safeX1').value,y1=+$('#safeY1').value,x2=+$('#safeX2').value,y2=+$('#safeY2').value;if(![x1,y1,x2,y2].every(Number.isFinite))return say('픽셀 좌표를 숫자로 입력해 주세요','err');x1=Math.max(0,Math.min(w,x1));y1=Math.max(0,Math.min(h,y1));x2=Math.max(0,Math.min(w,x2));y2=Math.max(0,Math.min(h,y2));[x1,x2]=[Math.min(x1,x2),Math.max(x1,x2)];[y1,y2]=[Math.min(y1,y2),Math.max(y1,y2)];if(safeAspectLock.checked){let rw=x2-x1,rh=y2-y1,targetW=Math.max(rw,rh*16/9),targetH=targetW*9/16,scale=Math.min(1,(w-x1)/Math.max(1,targetW),(h-y1)/Math.max(1,targetH));x2=x1+targetW*scale;y2=y1+targetH*scale}if(x2-x1<2||y2-y1<2)return say('필수 영역은 가로·세로 2픽셀 이상이어야 합니다','err');const safe=[x1/w,y1/h,x2/w,y2/h].map(v=>+v.toFixed(4));saveTag({safe,focus:null},safeAspectLock.checked?'필수 영역 픽셀 좌표 적용 · 16:9':'필수 영역 픽셀 좌표 적용')};
$('#safePixels').querySelectorAll('input').forEach(input=>input.onkeydown=e=>{if(e.key==='Enter'){e.preventDefault();$('#applySafePixels').click()}});
$('#safeModeBtn').onclick=()=>{
  safeMode=!safeMode;lb.classList.toggle('safe-mode',safeMode);
  const v=vid();if(safeMode&&v)v.pause();
  renderTags();
};
const rotateBox=(box,step)=>{
  if(!box)return null;const [x1,y1,x2,y2]=box;
  return step>0?[1-y2,x1,1-y1,x2]:[y1,1-x2,y2,1-x1];
};
const rotatePoint=(p,step)=>!p?null:(step>0?[1-p[1],p[0]]:[p[1],1-p[0]]);
$('#fRotate').querySelectorAll('button').forEach(b=>b.onclick=()=>{
  const t=tagOf(shots[cur]);
  const step=b.dataset.reset==='1'?-t.rotation:+b.dataset.step;
  const rotation=b.dataset.reset==='1'?0:(t.rotation+step+360)%360;
  let safe=t.safe,focus=t.focus;
  const turns=((step%360)+360)%360/90;
  for(let i=0;i<turns;i++){safe=rotateBox(safe,90);focus=rotatePoint(focus,90);}
  const mediaName=shots[cur].dataset.kind==='video'?'영상':'사진';
  saveTag({rotation,safe,focus},rotation?`${mediaName} ${rotation}° 회전`:`${mediaName} 회전 초기화`).then(()=>{
    render();renderTags();
  });
});
$('#soloBtn').onclick=()=>{const t=tagOf(shots[cur]);
  saveTag({solo:!t.solo}, t.solo?'자동 판단':'◻ 단독으로 크게');};
$('#clipIn').onclick=()=>setClipPoint('in');
$('#clipOut').onclick=()=>setClipPoint('out');
$('#applyClipExact').onclick=applyExactClip;
[$('#clipStartExact'),$('#clipEndExact')].forEach(input=>input.onkeydown=e=>{
  if(e.key==='Enter'){e.preventDefault();applyExactClip()}
});
$('#clipPlay').onclick=playClip;
$('#clipClear').onclick=()=>saveTag({clip:null},'영상 구간 지움');
$('#audioBtn').onclick=()=>{const t=tagOf(shots[cur]);
  saveTag({audio:t.audio==='keep'?'mute':'keep'}, t.audio==='keep'?'음소거':'🔊 소리 살림');};
$('#shortFromSum').onclick=()=>{
  const cap=shots[cur].dataset.cap||'';
  if(!cap) return say('요약이 비어 있어 가져올 것이 없습니다','err');
  $('#fShort').value=shortFrom(cap); $('#fShort').focus();
};
$('#fShort').addEventListener('keydown',e=>{if(e.key==='Enter'){e.preventDefault();e.target.blur();}});
$('#fShort').addEventListener('blur',()=>{
  const v=$('#fShort').value.trim();
  if(v!==(shots[cur].dataset.short||'')) saveTag({short:v},'자막');
});
// 사진 위를 드래그해 크롭할 때 반드시 남겨야 할 직사각형을 지정한다.
let safeDrag=null;
const safePoint=(e,r)=>[Math.min(1,Math.max(0,(e.clientX-r.left)/r.width)),
                         Math.min(1,Math.max(0,(e.clientY-r.top)/r.height))];
function constrainSafe16x9(start,raw,r){const dx=(raw[0]-start[0])*r.width,dy=(raw[1]-start[1])*r.height;if(Math.abs(dx)<1&&Math.abs(dy)<1)return raw;const sx=dx<0?-1:1,sy=dy<0?-1:1;let w=Math.max(Math.abs(dx),Math.abs(dy)*16/9),h=w*9/16;const maxW=(sx>0?1-start[0]:start[0])*r.width,maxH=(sy>0?1-start[1]:start[1])*r.height,scale=Math.min(1,maxW/w,maxH/h);w*=scale;h*=scale;return [start[0]+sx*w/r.width,start[1]+sy*h/r.height]}
function paintSafeDraft(box,media){
  stage.querySelector('.safe-region.draft')?.remove();
  const [x1,y1,x2,y2]=box, r=media.getBoundingClientRect(), sr=stage.getBoundingClientRect();
  const m=document.createElement('div');m.className='safe-region draft';
  m.style.left=(r.left-sr.left+x1*r.width)+'px';m.style.top=(r.top-sr.top+y1*r.height)+'px';
  m.style.width=((x2-x1)*r.width)+'px';m.style.height=((y2-y1)*r.height)+'px';stage.appendChild(m);
}
stage.addEventListener('pointerdown',e=>{
  if((shots[cur].dataset.kind==='video'&&!safeMode)||e.button!==0)return;
  const media=e.target.closest('img,video');if(!media)return;
  const r=media.getBoundingClientRect(),p=safePoint(e,r);
  safeDrag={id:e.pointerId,media,start:p,now:p};stage.setPointerCapture(e.pointerId);e.preventDefault();
});
stage.addEventListener('pointermove',e=>{
  if(!safeDrag||e.pointerId!==safeDrag.id)return;
  const r=safeDrag.media.getBoundingClientRect(),raw=safePoint(e,r);
  safeDrag.now=safeAspectLock.checked?constrainSafe16x9(safeDrag.start,raw,r):raw;
  const [ax,ay]=safeDrag.start,[bx,by]=safeDrag.now;
  paintSafeDraft([Math.min(ax,bx),Math.min(ay,by),Math.max(ax,bx),Math.max(ay,by)],safeDrag.media);
});
stage.addEventListener('pointerup',e=>{
  if(!safeDrag||e.pointerId!==safeDrag.id)return;
  const [ax,ay]=safeDrag.start,[bx,by]=safeDrag.now;
  const box=[Math.min(ax,bx),Math.min(ay,by),Math.max(ax,bx),Math.max(ay,by)];safeDrag=null;
  stage.querySelector('.safe-region.draft')?.remove();
  if(box[2]-box[0]<.02||box[3]-box[1]<.02)return say('점이 아니라 영역을 드래그해 주세요','err');
  safeMode=false;lb.classList.remove('safe-mode');
  saveTag({safe:box,focus:null},'필수 영역 지정');
});
stage.addEventListener('pointercancel',()=>{
  safeDrag=null;stage.querySelector('.safe-region.draft')?.remove();drawFocus();
});

shots.forEach((s,i)=>s.addEventListener('click',e=>{
  // 편집 모드에서 캡션을 누른 경우엔 라이트박스를 열지 않는다
  if(document.body.classList.contains('edit') && e.target.closest('figcaption')) return;
  show(i);
}));
const requestedFile=new URLSearchParams(location.search).get('file');
if(requestedFile){const requestedIndex=shots.findIndex(s=>s.dataset.file===requestedFile);if(requestedIndex>=0)requestAnimationFrame(()=>show(requestedIndex));}

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
    if(text===(s.dataset.cap||'')){ if(!text) paintCaption(s); return; }
    try{
      if(live) await api('/api/item',{file:s.dataset.file,summary:text});
      else stash(s.dataset.file,{summary:text});
      s.dataset.cap=text; s.classList.toggle('nosum',!text);
      paintCaption(s);
      say('요약 저장','ok');
    }catch(e){ say('저장 실패: '+e.message,'err'); paintCaption(s); }
  });
});
// 모션 포토는 썸네일에 마우스를 올리면 그 자리에서 살짝 움직인다 (그때 처음 불러온다)
shots.filter(s=>s.dataset.motion).forEach(s=>{
  let v=null;
  s.addEventListener('mouseenter',()=>{
    if(v){v.play().then(()=>v.classList.add('ready')).catch(()=>{});return;}
    v=document.createElement('video');
    const still=s.querySelector('img');
    Object.assign(v,{src:s.dataset.motion,loop:true,muted:true,playsInline:true,
                     preload:'auto',poster:still?.currentSrc||still?.src||''});
    v.className='preview';
    v.addEventListener('loadeddata',()=>{
      if(!s.matches(':hover'))return;
      v.play().then(()=>v.classList.add('ready')).catch(()=>{});
    });
    v.addEventListener('error',()=>{v.remove();v=null;});
    s.appendChild(v); v.load();
  });
  s.addEventListener('mouseleave',()=>{
    if(!v)return;
    v.pause();v.classList.remove('ready');
    try{v.currentTime=0}catch(_e){}
  });
});
lb.querySelector('.close').onclick=close;
lb.querySelector('.prev').onclick=e=>{e.stopPropagation();go(cur-1)};
lb.querySelector('.next').onclick=e=>{e.stopPropagation();go(cur+1)};
lb.addEventListener('click',e=>{if(e.target===lb)close()});
document.addEventListener('keydown',e=>{
  if(!lb.classList.contains('on'))return;
  if(chap.classList.contains('on'))return;       // 챕터 창이 떠 있으면 그쪽이 먼저다
  const typing=/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName);
  // 수정 중이면 Esc 는 먼저 수정을 접는다 — 한 번 더 눌러야 닫힌다
  if(e.key==='Escape'){ if(lb.classList.contains('editing')) cancelEdit(); else close(); return; }
  if((e.metaKey||e.ctrlKey)&&e.key==='Enter'){e.preventDefault();
    if(lb.classList.contains('editing')) save(); else $('#editFieldsBtn').click();}
  if(typing)return;
  if(e.key==='ArrowLeft'){go(cur-1);return;} if(e.key==='ArrowRight'){go(cur+1);return;}
  // 영상 태그 단축키 — 130장을 훑는 작업이라 손이 키보드를 떠나지 않게
  if(e.metaKey||e.ctrlKey||e.altKey)return;
  const k=e.key.toLowerCase();
  if(k==='1'||k==='2'||k==='3'){e.preventDefault();togglePick(+k-1);return;}
  if(k==='x'){togglePick(0);return;}
  if(k==='p'){saveTag({private:!tagOf(shots[cur]).priv},'비공개 전환');return;}
  if(k==='c'){saveTag({safe:null,focus:null},'필수 영역 지움');return;}
  if(k==='n'){nextUntagged();return;}
  if(k==='i'||k==='o'){e.preventDefault();setClipPoint(k==='i'?'in':'out');return;}
  if(k==='m'){const t=tagOf(shots[cur]);
              saveTag({audio:t.audio==='keep'?'mute':'keep'},
                      t.audio==='keep'?'음소거':'🔊 소리 살림');return;}
  const pi=PKEYS.indexOf(k);
  if(pi>=0&&pi<roster.length)togglePerson(roster[pi]);
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
document.addEventListener('keydown',e=>{
  if(e.key!=='Escape')return;
  help.classList.remove('on'); $('#chap').classList.remove('on');
});

$('#editBtn').onclick=e=>{document.body.classList.toggle('edit');
  e.target.classList.toggle('on',document.body.classList.contains('edit'));
  shots.forEach(paintCaption);};
$('#nextBtn').onclick=async()=>{
  const i=shots.findIndex((s,k)=>k>cur&&s.classList.contains('nosum'));
  const j=i>=0?i:shots.findIndex(s=>s.classList.contains('nosum'));
  if(j<0)return say('요약이 비어 있는 항목이 없습니다','ok');
  if(!await leaveGuard())return;
  document.body.classList.add('edit'); $('#editBtn').classList.add('on');
  show(j); setEditing(true); setTimeout(()=>$('#fSum').focus(),60);
};
$('#tagBtn').onclick=()=>{
  const t=tagStats();
  say(`영상 태깅 ${t.done}/${t.total} — 꼭 ${t.must} · 제외 ${t.drop} · 남은 ${t.total-t.done}`,'ok');
  nextUntagged();
};
$('#untaggedBtn').onclick=e=>{
  const on=document.body.classList.toggle('onlyuntagged');
  e.target.classList.toggle('on',on);
  document.querySelectorAll('.day').forEach(d=>
    d.classList.toggle('hide', on && !d.querySelector('.shot.untagged')));
  const t=tagStats();
  say(on?`아직 안 고른 ${t.total-t.done}장만 보입니다`:'전체 보기','ok');
};
// ── 챕터 · 음악 ────────────────────────────────────────
// 영상의 뼈대. 챕터(기간·목표 길이)와 음악(BPM·후렴)이 정해지면
// [영상 계획 만들기]가 컷 리스트를 계산해 VIDEO_PLAN.md 로 내보낸다.
let CHAPS={{CHAPTERS}}, MUSIC={{MUSIC}};
const MOODS={{MOODS}};
const chap=$('#chap');

function chapRow(c,i){
  const opts=['',...MOODS].map(m=>
    `<option${m===(c.mood||'')?' selected':''}>${esc(m)}</option>`).join('');
  return `<div class="crow" data-i="${i}">
    <input class="ct" value="${esc(c.title||'')}" placeholder="챕터 제목">
    <input class="cf" value="${esc(c.from||'')}" placeholder="2025-08-09">
    <input class="cto" value="${esc(c.to||'')}" placeholder="2025-09-17">
    <input class="cs" type="number" min="1" value="${+c.sec||30}">
    <select class="cm">${opts}</select>
    <button class="del" title="이 챕터 지우기">&times;</button></div>`;
}
function renderChaps(){
  $('#chapList').innerHTML=(CHAPS.chapters||[]).map(chapRow).join('')
    || '<p class="lead">아직 챕터가 없습니다 — [초안 만들기] 를 눌러보세요.</p>';
  $('#chapTarget').value=CHAPS.target_sec||300;
  $('#chapList').querySelectorAll('.del').forEach(b=>b.onclick=()=>{
    CHAPS.chapters=readChaps().filter((_,k)=>k!==+b.closest('.crow').dataset.i);
    renderChaps();
  });
  $('#fSize').value=`${CHAPS.width||1920}x${CHAPS.height||1080}`;
  if(!$('#fSize').value) $('#fSize').value='1920x1080';
  $('#fMode').value=CHAPS.group_mode||'auto';
  $('#fUp').value=CHAPS.max_upscale||1.15;
  $('#mFile').value=MUSIC.file||''; $('#mBpm').value=MUSIC.bpm||'';
  $('#mOff').value=MUSIC.offset||'';
  $('#mChorus').value=(MUSIC.sections||[]).map(s=>`${s.from}-${s.to}`).join(', ');
}
function readScreen(){
  const [w,h]=($('#fSize').value||'1920x1080').split('x').map(Number);
  return {width:w||1920, height:h||1080, group_mode:$('#fMode').value||'auto',
          max_upscale:+$('#fUp').value||1.15};
}
function readChaps(){
  return [...$('#chapList').querySelectorAll('.crow')].map(r=>({
    title:r.querySelector('.ct').value.trim(), from:r.querySelector('.cf').value.trim(),
    to:r.querySelector('.cto').value.trim(), sec:+r.querySelector('.cs').value||30,
    mood:r.querySelector('.cm').value}));
}
function readMusic(){
  const sections=[];
  ($('#mChorus').value||'').split(/[,;]/).forEach(part=>{
    const m=part.match(/\s*([\d.]+)\s*[-~]\s*([\d.]+)\s*$/);
    if(m) sections.push({name:'chorus',from:+m[1],to:+m[2]});
  });
  return {file:$('#mFile').value.trim(), bpm:+$('#mBpm').value||0,
          offset:+$('#mOff').value||0, sections};
}
$('#chapBtn').onclick=()=>{renderChaps();chap.classList.add('on');};
chap.querySelector('.x').onclick=()=>chap.classList.remove('on');
chap.addEventListener('click',e=>{if(e.target===chap)chap.classList.remove('on')});
$('#addChap').onclick=()=>{
  const last=readChaps().slice(-1)[0];
  CHAPS.chapters=readChaps().concat([{title:'',from:last?last.to:'',to:'',sec:30,mood:''}]);
  renderChaps();
};
$('#draftChap').onclick=async()=>{
  if(!live) return say('초안 만들기는 서버로 열었을 때만 됩니다','err');
  if((readChaps().length) && !confirm('지금 챕터 목록을 초안으로 덮어쓸까요?')) return;
  try{ const j=await api('/api/chapters',{draft:true,target_sec:+$('#chapTarget').value||300});
       CHAPS.chapters=j.chapters; renderChaps(); say('초안을 만들었습니다 — 고친 뒤 [저장]','ok'); }
  catch(e){ say('실패: '+e.message,'err'); }
};
$('#saveChap').onclick=async()=>{
  const body={target_sec:+$('#chapTarget').value||300, chapters:readChaps(), ...readScreen()};
  MUSIC=readMusic();
  try{
    if(live){ await api('/api/chapters',body); await api('/api/music',MUSIC); }
    else { stash('__chapters__',body); stash('__music__',MUSIC); }
    CHAPS=body;
    if(lb.classList.contains('on')) renderFit(tagOf(shots[cur]));   // 화면 설정이 바뀌었다
    say('챕터·음악·화면 설정을 저장했습니다','ok');
  }catch(e){ say('저장 실패: '+e.message,'err'); }
};
$('#makePlan').onclick=async()=>{
  if(!live) return say('영상 계획은 서버로 열었을 때만 만들 수 있습니다','err');
  say('계획 계산 중…');
  const box=$('#planOut');
  try{
    const j=await api('/api/plan',{});
    const p=j.plan, mm=Math.floor(p.total_sec/60), ss=Math.round(p.total_sec%60);
    box.innerHTML=`<div class="big">${p.cuts}화면 · 사진·영상 ${p.photos}컷 · ${mm}분 ${ss}초 `
      +`<span style="opacity:.6">(목표 ${p.target_sec}초)</span></div>`
      +(p.grouped_cuts?`<p>${p.grouped_photos}장은 ${p.grouped_cuts}개 화면에 나눠 담았습니다 `
        +`(${p.frame.width}×${p.frame.height} · 묶기 ${p.frame.group_mode})</p>`:'')
      +`<ul>${p.chapters.map(c=>`<li>${esc(c.title)} — ${c.dur_sec.toFixed(1)}초 · `
      +`${c.cuts.length}컷${c.dropped?` <span class="w">(${c.dropped}컷 뺌)</span>`:''}</li>`).join('')}</ul>`
      +(p.warnings.length?`<p class="w">⚠︎ 확인할 것 ${p.warnings.length}건</p><ul class="w">`
        +p.warnings.slice(0,8).map(w=>`<li>${esc(w)}</li>`).join('')+`</ul>`:'')
      +`<p>VIDEO_PLAN.md · data/video_plan.json 에 저장했습니다.</p>`;
    box.innerHTML+=`<p><a href="VIDEO_PLOT.html" target="_blank">🎞 영상 플롯 HTML 열기</a></p>`;
    say('영상 계획을 만들었습니다','ok');
  }catch(e){ box.innerHTML=''; say('실패: '+e.message,'err'); }
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
