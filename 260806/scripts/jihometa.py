"""지호 사진/영상 메타데이터 추출 (표준 라이브러리만 사용).

- JPEG: EXIF APP1 세그먼트를 직접 파싱해 촬영시각 / GPS / 기기 정보를 뽑는다.
- MP4 : ISO-BMFF 박스를 훑어 moov/mvhd(생성시각·재생시간) 와
        moov/udta/(c)xyz(ISO-6709 위치)를 뽑는다.
- 위 둘이 모두 실패하면 파일명(PXL_YYYYMMDD_HHMMSSmmm, 20250809_112729 등)에서
  날짜를 추정하고, 그것도 없으면 날짜 없음으로 남긴다.

exiftool / ffprobe / Pillow 없이도 동작하도록 의도적으로 순수 파이썬으로 작성했다.
"""

from __future__ import annotations

import datetime as dt
import re
import struct
from pathlib import Path

IMAGE_EXT = {".jpg", ".jpeg", ".png", ".heic", ".heif"}
VIDEO_EXT = {".mp4", ".mov", ".m4v"}

# ---------------------------------------------------------------- EXIF (JPEG)

_TYPE_SIZE = {1: 1, 2: 1, 3: 2, 4: 4, 5: 8, 6: 1, 7: 1, 8: 2, 9: 4, 10: 8, 11: 4, 12: 8}

GPS_TAGS = {1: "lat_ref", 2: "lat", 3: "lon_ref", 4: "lon", 5: "alt_ref", 6: "alt",
            7: "gps_time", 29: "gps_datestamp"}
IFD0_TAGS = {0x010F: "make", 0x0110: "model", 0x0112: "orientation", 0x0132: "datetime"}
EXIF_TAGS = {0x9003: "datetime_original", 0x9011: "offset_original",
             0x9291: "subsec_original", 0xA002: "width", 0xA003: "height",
             0x829A: "exposure", 0x8827: "iso"}


def _read_ifd(buf: bytes, offset: int, endian: str, wanted: dict) -> tuple[dict, dict]:
    """IFD 하나를 읽어 (원하는 태그값, 서브IFD 포인터) 반환."""
    out, subs = {}, {}
    if offset + 2 > len(buf):
        return out, subs
    (count,) = struct.unpack(endian + "H", buf[offset:offset + 2])
    for i in range(count):
        e = offset + 2 + i * 12
        if e + 12 > len(buf):
            break
        tag, typ, n = struct.unpack(endian + "HHI", buf[e:e + 8])
        size = _TYPE_SIZE.get(typ, 0) * n
        if size == 0:
            continue
        if size <= 4:
            raw = buf[e + 8:e + 8 + size]
        else:
            (ptr,) = struct.unpack(endian + "I", buf[e + 8:e + 12])
            if ptr + size > len(buf):
                continue
            raw = buf[ptr:ptr + size]
        if tag in (0x8769, 0x8825):  # ExifIFD / GPSIFD 포인터
            subs["exif" if tag == 0x8769 else "gps"] = struct.unpack(endian + "I", raw[:4])[0]
            continue
        if tag not in wanted:
            continue
        out[wanted[tag]] = _decode(raw, typ, n, endian)
    return out, subs


def _decode(raw: bytes, typ: int, n: int, endian: str):
    if typ == 2:
        return raw.split(b"\x00")[0].decode("utf-8", "replace").strip()
    if typ in (1, 6, 7):
        return list(raw[:n])
    fmt = {3: "H", 4: "I", 8: "h", 9: "i"}.get(typ)
    if fmt:
        vals = struct.unpack(endian + fmt * n, raw[:_TYPE_SIZE[typ] * n])
        return vals[0] if n == 1 else list(vals)
    if typ in (5, 10):  # RATIONAL
        fmt = "II" if typ == 5 else "ii"
        vals = struct.unpack(endian + fmt * n, raw[:8 * n])
        pairs = [(vals[2 * i], vals[2 * i + 1]) for i in range(n)]
        nums = [a / b if b else 0.0 for a, b in pairs]
        return nums[0] if n == 1 else nums
    return None


def _dms_to_deg(v, ref) -> float | None:
    if not isinstance(v, list) or len(v) < 3:
        return None
    deg = v[0] + v[1] / 60.0 + v[2] / 3600.0
    if ref and str(ref).upper() in ("S", "W"):
        deg = -deg
    return round(deg, 7)


def read_exif(path: Path) -> dict:
    """JPEG에서 EXIF를 읽어 평평한 dict로 반환. 실패하면 {}."""
    try:
        data = path.read_bytes()
    except OSError:
        return {}
    if data[:2] != b"\xff\xd8":
        return {}

    app1 = None
    i = 2
    while i < len(data) - 4:
        if data[i] != 0xFF:
            i += 1
            continue
        marker = data[i + 1]
        if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
            i += 2
            continue
        if marker == 0xDA:  # 이미지 데이터 시작 — 그 뒤로는 EXIF 없음
            break
        (seglen,) = struct.unpack(">H", data[i + 2:i + 4])
        seg = data[i + 4:i + 2 + seglen]
        if marker == 0xE1 and seg[:6] == b"Exif\x00\x00":
            app1 = seg[6:]
            break
        i += 2 + seglen
    if not app1 or len(app1) < 8:
        return {}

    endian = "<" if app1[:2] == b"II" else ">" if app1[:2] == b"MM" else None
    if endian is None:
        return {}
    (ifd0_off,) = struct.unpack(endian + "I", app1[4:8])

    meta, subs = _read_ifd(app1, ifd0_off, endian, IFD0_TAGS)
    if "exif" in subs:
        sub, _ = _read_ifd(app1, subs["exif"], endian, EXIF_TAGS)
        meta.update(sub)
    if "gps" in subs:
        g, _ = _read_ifd(app1, subs["gps"], endian, GPS_TAGS)
        lat = _dms_to_deg(g.get("lat"), g.get("lat_ref"))
        lon = _dms_to_deg(g.get("lon"), g.get("lon_ref"))
        if lat is not None and lon is not None and (lat, lon) != (0.0, 0.0):
            meta["lat"], meta["lon"] = lat, lon
        alt = g.get("alt")
        if isinstance(alt, (int, float)):
            ref = g.get("alt_ref")
            below = bool(ref[0]) if isinstance(ref, list) and ref else False
            meta["alt"] = round(-alt if below else alt, 1)
    return meta


# ------------------------------------------------------------------ MP4 atoms

_MP4_EPOCH = dt.datetime(1904, 1, 1, tzinfo=dt.timezone.utc)


def _iter_boxes(f, start: int, end: int):
    pos = start
    while pos < end - 8:
        f.seek(pos)
        head = f.read(8)
        if len(head) < 8:
            return
        (size,) = struct.unpack(">I", head[:4])
        typ = head[4:8]
        body = pos + 8
        if size == 1:
            (size,) = struct.unpack(">Q", f.read(8))
            body = pos + 16
        elif size == 0:
            size = end - pos
        if size < 8:
            return
        yield typ, body, pos + size
        pos += size


def _find(f, start, end, path):
    """중첩 박스 경로(예: [b"moov", b"udta"])를 따라가 (body_start, box_end) 반환."""
    if not path:
        return start, end
    for typ, body, stop in _iter_boxes(f, start, end):
        if typ == path[0]:
            return _find(f, body, stop, path[1:])
    return None


def read_mp4(path: Path) -> dict:
    meta: dict = {}
    try:
        size = path.stat().st_size
        with path.open("rb") as f:
            mvhd = _find(f, 0, size, [b"moov", b"mvhd"])
            if mvhd:
                f.seek(mvhd[0])
                blob = f.read(min(120, mvhd[1] - mvhd[0]))
                ver = blob[0]
                if ver == 1 and len(blob) >= 32:
                    created, _, timescale, dur = struct.unpack(">QQIQ", blob[4:32])
                elif len(blob) >= 20:
                    created, _, timescale, dur = struct.unpack(">IIII", blob[4:20])
                else:
                    created = timescale = dur = 0
                if created:
                    meta["mp4_created"] = (_MP4_EPOCH + dt.timedelta(seconds=created)).strftime(
                        "%Y-%m-%d %H:%M:%S")
                if timescale:
                    meta["duration_sec"] = round(dur / timescale, 1)

            udta = _find(f, 0, size, [b"moov", b"udta"])
            if udta:
                for typ, body, stop in _iter_boxes(f, udta[0], udta[1]):
                    if typ not in (b"\xa9xyz", b"loci"):
                        continue
                    f.seek(body)
                    chunk = f.read(min(256, stop - body)).decode("utf-8", "replace")
                    m = re.search(r"([+-]\d+\.?\d*)([+-]\d+\.?\d*)", chunk)
                    if m:
                        meta["lat"] = round(float(m.group(1)), 7)
                        meta["lon"] = round(float(m.group(2)), 7)
                    break

            # 해상도: 첫 video track 의 tkhd width/height
            trak = _find(f, 0, size, [b"moov", b"trak", b"tkhd"])
            if trak:
                f.seek(trak[0])
                blob = f.read(min(92, trak[1] - trak[0]))
                if len(blob) >= 84:
                    off = 84 if blob[0] == 1 else 76
                    if len(blob) >= off + 8:
                        w, h = struct.unpack(">II", blob[off:off + 8])
                        meta["width"], meta["height"] = w >> 16, h >> 16
    except (OSError, struct.error):
        return meta
    return meta


# ------------------------------------------------------- 파일명에서 날짜 추정

_NAME_PATTERNS = [
    # PXL_20260613_090324318.jpg  (구글 픽셀 = UTC)
    (re.compile(r"PXL_(\d{8})_(\d{6})\d*"), "utc"),
    # 20250809_112729.jpg / VID_20250809_112729 (삼성 등 = 로컬)
    (re.compile(r"(?:^|[^\d])(20\d{6})_(\d{6})(?!\d)"), "local"),
    # IMG-20250809-WA0001 (카카오/왓츠앱)
    (re.compile(r"(?:^|[^\d])(20\d{6})(?![\d])"), "dateonly"),
]


def date_from_name(name: str, tz_offset_hours: float) -> tuple[str, str] | None:
    """파일명에서 (로컬 촬영시각 문자열, 근거) 추정."""
    for pat, kind in _NAME_PATTERNS:
        m = pat.search(name)
        if not m:
            continue
        try:
            if kind == "dateonly":
                d = dt.datetime.strptime(m.group(1), "%Y%m%d")
                return d.strftime("%Y-%m-%d 00:00:00"), "filename(date only)"
            d = dt.datetime.strptime(m.group(1) + m.group(2), "%Y%m%d%H%M%S")
            if kind == "utc":
                d += dt.timedelta(hours=tz_offset_hours)
                return d.strftime("%Y-%m-%d %H:%M:%S"), "filename(UTC→local)"
            return d.strftime("%Y-%m-%d %H:%M:%S"), "filename(local)"
        except ValueError:
            continue
    # 13자리 epoch 밀리초 파일명 (카카오톡 저장본 등)
    m = re.fullmatch(r"(1[5-9]\d{11})", Path(name).stem)
    if m:
        d = dt.datetime.fromtimestamp(int(m.group(1)) / 1000, dt.timezone.utc) + dt.timedelta(
            hours=tz_offset_hours)
        return d.strftime("%Y-%m-%d %H:%M:%S"), "filename(epoch ms→local)"
    return None


# ------------------------------------------- 모션 포토 (구글 포토 .MP.jpg 등)

MOTION_SUFFIX = ".motion.mp4"


def find_embedded_video(data: bytes) -> int | None:
    """JPEG 뒤에 붙어 있는 MP4 의 시작 오프셋. 없으면 None.

    구글 포토의 모션 포토(.MP.jpg / MVIMG_*.jpg)는 JPEG 끝에 MP4 를 그대로
    이어 붙여 놓는다. XMP 의 Container 정보가 없는 경우도 있어서,
    'ftyp' 박스 헤더를 직접 찾아 확인한다.
    """
    pos = 0
    while True:
        idx = data.find(b"ftyp", pos)
        if idx < 4:
            return None
        start = idx - 4
        (size,) = struct.unpack(">I", data[start:idx])
        # ftyp 박스는 보통 16~64바이트. 뒤이어 또 다른 박스가 와야 정상.
        if 12 <= size <= 128 and start + size + 8 <= len(data):
            (nxt,) = struct.unpack(">I", data[start + size:start + size + 4])
            typ = data[start + size + 4:start + size + 8]
            if typ.isalpha() or nxt in (0, 1) or 8 <= nxt <= len(data):
                return start
        pos = idx + 4


def extract_motion(path: Path, dest: Path | None = None) -> Path | None:
    """모션 포토에서 MP4 를 뽑아 `<이름>.motion.mp4` 로 저장. 이미 있으면 그대로 반환."""
    dest = dest or path.with_name(path.name.rsplit(".", 1)[0] + MOTION_SUFFIX)
    if dest.exists() and dest.stat().st_size > 0:
        return dest
    try:
        data = path.read_bytes()
    except OSError:
        return None
    off = find_embedded_video(data)
    if off is None or len(data) - off < 4096:
        return None
    dest.write_bytes(data[off:])
    return dest


# ------------------------------------------------------------------- 통합 API

def probe(path: Path, tz_offset_hours: float = 9.0) -> dict:
    """파일 하나의 메타데이터를 표준 형태로 반환."""
    ext = path.suffix.lower()
    kind = "video" if ext in VIDEO_EXT else "image" if ext in IMAGE_EXT else "other"
    info: dict = {
        "file": path.name,
        "kind": kind,
        "bytes": path.stat().st_size,
        "taken_local": None,
        "date_source": None,
        "lat": None, "lon": None,
        "make": None, "model": None,
        "width": None, "height": None,
        "duration_sec": None,
    }

    raw: dict = {}
    if kind == "image":
        raw = read_exif(path)
        stamp = raw.get("datetime_original") or raw.get("datetime")
        if stamp:
            m = re.match(r"(\d{4})[:\-](\d{2})[:\-](\d{2})[ T](\d{2}):(\d{2}):(\d{2})", stamp)
            if m:
                info["taken_local"] = "%s-%s-%s %s:%s:%s" % m.groups()
                info["date_source"] = "exif"
    elif kind == "video":
        raw = read_mp4(path)
        created = raw.get("mp4_created")
        if created:
            # mvhd 는 UTC 기준. 로컬 시각으로 옮긴다.
            d = dt.datetime.strptime(created, "%Y-%m-%d %H:%M:%S") + dt.timedelta(
                hours=tz_offset_hours)
            info["taken_local"] = d.strftime("%Y-%m-%d %H:%M:%S")
            info["date_source"] = "mp4:mvhd(UTC→local)"
        info["duration_sec"] = raw.get("duration_sec")

    if not info["taken_local"]:
        guess = date_from_name(path.name, tz_offset_hours)
        if guess:
            info["taken_local"], info["date_source"] = guess

    for key in ("lat", "lon", "make", "model", "width", "height"):
        if raw.get(key) is not None:
            info[key] = raw[key]

    if kind == "image" and (not info["width"] or not info["height"]):
        info["width"] = raw.get("width") or None
        info["height"] = raw.get("height") or None
    info["orientation"] = raw.get("orientation")
    return info
