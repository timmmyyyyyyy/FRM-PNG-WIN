#!/usr/bin/env python3
"""
FRM-PNG-WIN.py - FRM-PNG-WIN: Windows-native Fallout 1/2 FRM extractor, previewer and PNG converter.

Formats (all decoders verified against fallout1-ce / fallout2-ce source, see FORMATS.md):
    FRM, FR0-FR5   indexed sprites / tiles / animations (6 directions)
    RIX            full-screen splash images (own embedded palette)
    PAL            palettes (COLOR.PAL and special palettes) -> 16x16 swatch PNG
    FON / AAF      bitmap / antialiased fonts -> glyph atlas PNG

Usage:
    python FRM-PNG-WIN.py DUMP_DIR OUT_DIR [options]   convert an already-extracted dump
    python FRM-PNG-WIN.py                              (double-click / run.bat) archive browser: open DATs, preview, extract, convert
    python FRM-PNG-WIN.py dat list|extract|install|verify|gui ...   DAT1 (Fallout 1) / DAT2 (Fallout 2) extractor, see --help

OUTPUT = an exact copy of the dump's folders. Nothing is added to the tree:
    DUMP/art/critters/HAPOWRAA.FRM  ->  OUT/art/critters/HAPOWRAA.png
One sheet PNG per source file, same name, same relative path. A multi-frame / multi-direction FRM becomes one sheet
(one row per direction, one column per frame). Reports go to a SIBLING folder (OUT_reports), never inside OUT.
Files that yield several images (frames/directions/glyphs) also get a folder with their exact original name
holding every individual PNG:  OUT/art/critters/HAPOWRAA/HAPOWRAA_d0_f00.png ... (--no-frames to skip).
Optional extras (off by default): --sidecar-json, --previews.
"""
import argparse, csv, fnmatch, hashlib, html, json, os, re, struct, sys, time, traceback, zlib
from collections import Counter, defaultdict
from multiprocessing import Pool
from pathlib import Path

try:
    from PIL import Image
except ImportError:
    import subprocess
    print("Pillow not found for", sys.executable, "- installing it now...")
    subprocess.call([sys.executable, "-m", "pip", "install", "pillow"])
    try:
        from PIL import Image
    except ImportError:
        print("Auto-install failed. Run this exact command in cmd, then retry:")
        print(f'  "{sys.executable}" -m pip install pillow')
        input("Press Enter to close...")
        sys.exit(1)

VERSION = "4.0.0"
FRM_EXTS = {".frm", ".fr0", ".fr1", ".fr2", ".fr3", ".fr4", ".fr5"}
FORMAT_BY_EXT = {**{e: "frm" for e in FRM_EXTS}, ".rix": "rix", ".pal": "pal", ".fon": "fon", ".aaf": "aaf"}

# Palette cycling the engine applies at runtime (game/cycle.cc, fallout1-ce). Raw table values;
# the engine does `>>= 2` (6-bit) before upload. Frame 0 = table order.
CYCLE_TABLES = {
    "slime":     (229, [0, 108, 0, 11, 115, 7, 27, 123, 15, 43, 131, 27]),
    "monitors":  (233, [107, 107, 111, 99, 103, 127, 87, 107, 143, 0, 147, 163, 107, 187, 255]),
    "fire_slow": (238, [255, 0, 0, 215, 0, 0, 147, 43, 11, 255, 119, 0, 255, 59, 0]),
    "fire_fast": (243, [71, 0, 0, 123, 0, 0, 179, 0, 0, 123, 0, 0, 71, 0, 0]),
    "shoreline": (248, [83, 63, 43, 75, 59, 43, 67, 55, 39, 63, 51, 39, 55, 47, 35, 51, 43, 35]),
}
CYCLE_INDEX_RANGE = (229, 253)


class DecodeError(Exception):
    """Fatal: file is corrupt or only partially decodable. File is NOT marked converted."""


# ----------------------------------------------------------------------------- palettes
class Palette:
    """256-entry palette stored as 6-bit values (0-63) exactly like the engine's _cmap."""

    def __init__(self, name, raw6, mapped, source="", info=None):
        self.name, self.raw6, self.mapped, self.source = name, raw6, mapped, source
        self.info = info or {}

    @classmethod
    def from_bytes(cls, data, name="", source=""):
        if len(data) < 768:
            raise DecodeError(f"palette too short ({len(data)} bytes, need >= 768)")
        raw6, mapped, bad = [], [], 0
        for i in range(256):
            r, g, b = data[i * 3], data[i * 3 + 1], data[i * 3 + 2]
            ok = r <= 63 and g <= 63 and b <= 63          # engine: otherwise entry is black + unmapped
            if not ok:
                r = g = b = 0
                bad += 1
            raw6.append((r, g, b)); mapped.append(ok)
        extra = len(data) - 768
        tail = data[768 + 0x8000:768 + 0x8000 + 4] if extra >= 0x8000 else b""
        info = dict(size=len(data), unmapped_entries=bad, has_color_table=extra >= 0x8000,
                    has_newc_tables=tail in (b"NEWC", b"CWEN"), trailing_after_768=extra)
        return cls(name, raw6, mapped, source, info)

    def with_cycle(self):
        raw6 = list(self.raw6)
        for _, (base, table) in CYCLE_TABLES.items():
            for k in range(len(table) // 3):
                raw6[base + k] = tuple(v >> 2 for v in table[k * 3:k * 3 + 3])
        return Palette(self.name, raw6, self.mapped, self.source, dict(self.info, cycle_applied=True))

    def rgb(self, scale="engine"):
        if scale == "full":
            return [((r << 2) | (r >> 4), (g << 2) | (g >> 4), (b << 2) | (b >> 4)) for r, g, b in self.raw6]
        return [(r << 2, g << 2, b << 2) for r, g, b in self.raw6]   # engine: palette << 2

    def flat(self, scale="engine"):
        return [c for t in self.rgb(scale) for c in t]


def grayscale_palette():
    return Palette("grayscale", [(i >> 2,) * 3 for i in range(256)], [True] * 256, "builtin", {"fake": True})


# ----------------------------------------------------------------------------- image helpers
def indexed_to_rgba(w, h, pix, flat_pal, transparent0=True):
    im = Image.frombytes("P", (w, h), bytes(pix))
    im.putpalette(flat_pal)
    if transparent0:
        im.info["transparency"] = 0
    return im.convert("RGBA")


def pixel_stats(pix, palette):
    c = Counter(pix)
    return dict(transparent=c.get(0, 0),
                unmapped_palette_pixels=sum(n for i, n in c.items() if not palette.mapped[i]),
                cycled_palette_pixels=sum(n for i, n in c.items() if CYCLE_INDEX_RANGE[0] <= i <= CYCLE_INDEX_RANGE[1]))


# ----------------------------------------------------------------------------- FRM
HDR = 62


class FrmFrame:
    __slots__ = ("w", "h", "ox", "oy", "size", "pix", "file_offset")

    def __init__(self, w, h, ox, oy, size, pix, off):
        self.w, self.h, self.ox, self.oy, self.size, self.pix, self.file_offset = w, h, ox, oy, size, pix, off


class FrmFile:
    def __init__(self):
        self.header, self.blocks, self.dir_map, self.warnings = {}, [], [], []


def decode_frm(d):
    """Engine-faithful: directions are read SEQUENTIALLY; direction i shares data with i-1 when the
    header offsets are equal (art.cc: `index == 0 || dataOffsets[index-1] != dataOffsets[index]`)."""
    if len(d) < HDR:
        raise DecodeError(f"file smaller than 62-byte header ({len(d)} bytes)")
    f = FrmFile()
    ver, fps, act, fpd = struct.unpack(">IHHH", d[:10])
    sx, sy = struct.unpack(">6h", d[10:22]), struct.unpack(">6h", d[22:34])
    offs, dsize = struct.unpack(">6I", d[34:58]), struct.unpack(">I", d[58:62])[0]
    f.header = dict(version=ver, fps=fps, action_frame=act, frames_per_direction=fpd,
                    shift_x=list(sx), shift_y=list(sy), direction_offsets=list(offs), data_size=dsize)
    if fpd == 0:
        raise DecodeError("header says 0 frames per direction")
    if ver != 4:
        f.warnings.append(f"unexpected FRM version {ver} (normal is 4)")
    if act >= fpd:
        f.warnings.append(f"action_frame {act} >= frames_per_direction {fpd}")
    if dsize not in (0, len(d) - HDR):
        f.warnings.append(f"header data_size {dsize} != actual {len(d) - HDR}")
    pos, dir_map, block_index = HDR, [], -1
    for dr in range(6):
        if dr > 0 and offs[dr - 1] == offs[dr]:
            dir_map.append(block_index)
            continue
        if pos != HDR + offs[dr]:
            f.warnings.append(f"direction {dr}: sequential position {pos - HDR} != header offset {offs[dr]} (engine reads sequentially)")
        frames = []
        for fr in range(fpd):
            if pos + 12 > len(d):
                raise DecodeError(f"truncated: frame header missing (dir {dr}, frame {fr})")
            w, h, size, ox, oy = struct.unpack(">HHIhh", d[pos:pos + 12])
            start = pos + 12
            if size < w * h:
                raise DecodeError(f"partial pixel data: dir {dr} frame {fr} is {w}x{h} ({w*h} px) but size field = {size}")
            if start + size > len(d):
                raise DecodeError(f"truncated: dir {dr} frame {fr} needs {size} bytes, only {len(d) - start} left")
            if size > w * h:
                f.warnings.append(f"dir {dr} frame {fr}: size field {size} > w*h {w*h}; {size - w*h} extra bytes ignored")
            if w == 0 or h == 0:
                f.warnings.append(f"dir {dr} frame {fr}: empty frame ({w}x{h})")
            frames.append(FrmFrame(w, h, ox, oy, size, d[start:start + w * h], pos))
            pos = start + size
        f.blocks.append(frames)
        block_index += 1
        dir_map.append(block_index)
    f.dir_map = dir_map
    if pos < len(d):
        f.warnings.append(f"{len(d) - pos} trailing bytes after last frame")
    return f


# ----------------------------------------------------------------------------- RIX
def decode_rix(d):
    if len(d) < 10 + 768:
        raise DecodeError("RIX smaller than header+palette")
    if d[:4] != b"RIX3":
        raise DecodeError(f"bad RIX signature {d[:4]!r} (expected RIX3)")
    w, h = struct.unpack("<HH", d[4:8])
    pal_type, storage = d[8], d[9]
    if w == 0 or h == 0 or w > 32767 or h > 32767:
        raise DecodeError(f"invalid RIX size {w}x{h}")
    need = 10 + 768 + w * h
    if len(d) < need:
        raise DecodeError(f"partial pixel data: RIX {w}x{h} needs {need} bytes, file has {len(d)}")
    warns = []
    if len(d) > need:
        warns.append(f"{len(d) - need} trailing bytes")
    pal = Palette.from_bytes(d[10:778], "embedded")
    return dict(w=w, h=h, pal_type=pal_type, storage_type=storage, palette=pal, pix=d[778:778 + w * h], warnings=warns)


# ----------------------------------------------------------------------------- FON / AAF
def decode_fon(d):
    """Little-endian: u32 glyphCount, lineHeight, letterSpacing, 2 ignored ptrs; glyphs {i32 width, i32 offset}; bit data."""
    if len(d) < 20:
        raise DecodeError("FON smaller than header")
    n, line_h, spacing = struct.unpack("<III", d[:12])
    if n == 0 or n > 4096 or line_h == 0 or line_h > 512:
        raise DecodeError(f"implausible FON header (glyphs={n}, height={line_h})")
    gtab = 20 + n * 8
    if len(d) < gtab:
        raise DecodeError("truncated glyph table")
    glyphs = [struct.unpack("<ii", d[20 + i * 8:28 + i * 8]) for i in range(n)]
    data = d[gtab:]
    warns, out = [], []
    for i, (w, off) in enumerate(glyphs):
        stride = (w + 7) >> 3
        if w < 0 or w > 512 or off < 0 or off + stride * line_h > len(data):
            raise DecodeError(f"glyph {i} (width {w}, offset {off}) lies outside the data block")
        rows = [[(data[off + y * stride + (x >> 3)] >> (7 - (x & 7))) & 1 for x in range(w)] for y in range(line_h)]
        out.append(dict(code=i, width=w, offset=off, rows=rows))
    engine_size = line_h * ((glyphs[-1][0] + 7) >> 3) + glyphs[-1][1]
    if len(data) < engine_size:
        raise DecodeError("data block shorter than engine's expected size")
    if len(data) > engine_size:
        warns.append(f"{len(data) - engine_size} trailing bytes")
    return dict(glyph_count=n, line_height=line_h, letter_spacing=spacing, glyphs=out, warnings=warns)


def decode_aaf(d):
    """Big-endian: 'AAFF', u16 maxHeight, letterSpacing, wordSpacing, lineSpacing; 256 x {u16 w, u16 h, u32 off}; 1 byte/pixel."""
    if len(d) < 2060:
        raise DecodeError("AAF smaller than 2060-byte header")
    if d[:4] != b"AAFF":
        raise DecodeError(f"bad AAF signature {d[:4]!r}")
    max_h, letter, word, line = struct.unpack(">4H", d[4:12])
    data = d[2060:]
    glyphs, mx = [], 0
    for i in range(256):
        w, h, off = struct.unpack(">HHI", d[12 + i * 8:20 + i * 8])
        if w * h and off + w * h > len(data):
            raise DecodeError(f"partial pixel data: glyph {i} ({w}x{h} @ {off}) exceeds data block ({len(data)} bytes)")
        if h > max_h:
            raise DecodeError(f"glyph {i} height {h} > font max height {max_h}")
        px = data[off:off + w * h]
        if px:
            mx = max(mx, max(px))
        glyphs.append(dict(code=i, width=w, height=h, offset=off, pix=px))
    return dict(max_height=max_h, letter_spacing=letter, word_spacing=word, line_spacing=line,
                glyphs=glyphs, max_intensity=mx, warnings=[])


# ----------------------------------------------------------------------------- sheet / gif helpers
def make_sheet(images, layout="row", cols=0, pad=0, anchor="bottom-center"):
    """images: list of RGBA (or None for empty frames). Returns (sheet, cell_w, cell_h, positions)."""
    cw = max([im.width for im in images if im] + [1])
    ch = max([im.height for im in images if im] + [1])
    n = len(images)
    if layout == "column":
        cols = 1
    elif layout == "grid":
        cols = cols if cols > 0 else max(1, int(n ** 0.5 + 0.999))
    else:
        cols = n
    rows = (n + cols - 1) // cols
    sheet = Image.new("RGBA", (cols * (cw + pad) + pad, rows * (ch + pad) + pad), (0, 0, 0, 0))
    pos = []
    for i, im in enumerate(images):
        cx, cy = pad + (i % cols) * (cw + pad), pad + (i // cols) * (ch + pad)
        x, y = cx, cy
        if im is not None:
            if anchor == "bottom-center":
                x, y = cx + (cw - im.width) // 2, cy + ch - im.height
            elif anchor == "center":
                x, y = cx + (cw - im.width) // 2, cy + (ch - im.height) // 2
            sheet.paste(im, (x, y))
        pos.append([x, y])
    return sheet, cw, ch, pos


def save_gif(images, path, fps):
    cw = max(im.width for im in images if im)
    ch = max(im.height for im in images if im)
    frames = []
    for im in images:
        c = Image.new("RGBA", (cw, ch), (0, 0, 0, 0))
        if im:
            c.paste(im, ((cw - im.width) // 2, ch - im.height))
        frames.append(c)
    frames[0].save(path, save_all=True, append_images=frames[1:], duration=int(1000 / (fps or 10)),
                   loop=0, disposal=2, optimize=False)


# ----------------------------------------------------------------------------- DAT archives (Fallout 1 DAT1 / Fallout 2 DAT2)
class DatError(Exception):
    """Archive-level or entry-level problem. Entry errors are reported individually; extraction continues."""


class Cancelled(Exception):
    pass


class DatEntry:
    __slots__ = ("raw_path", "path", "size", "packed", "offset", "method", "flags", "file")

    def __init__(self, raw_path, size, packed, offset, method, flags=0, file=None):
        self.raw_path, self.size, self.packed, self.offset = raw_path, size, packed, offset
        self.method, self.flags, self.file = method, flags, file
        self.path = re.sub(r"^(\./)+", "", raw_path.replace("\\", "/"))

    @property
    def ext(self):
        return os.path.splitext(self.path)[1].lower()


def lzss_decode(src):
    """Fallout 1 LZSS block (fallout1-ce plib/db/lzss.cc): 4096-byte ring buffer pre-filled with 4078 spaces
    (write index 4078, rest zero); control byte LSB-first, bit 1 = literal, bit 0 = 2-byte match
    (offset = lo | (hi & 0xF0) << 4, absolute ring index; length = (hi & 0x0F) + 3)."""
    ring = bytearray(4096)
    ring[:4078] = b" " * 4078
    r, pos, n = 4078, 0, len(src)
    out = bytearray()
    append = out.append
    while pos < n:
        flags = src[pos]; pos += 1
        for bit in range(8):
            if pos >= n:
                break
            if flags & (1 << bit):
                b = src[pos]; pos += 1
                append(b); ring[r] = b; r = (r + 1) & 0xFFF
            else:
                if pos + 1 >= n:
                    raise DatError("truncated LZSS match token")
                lo, hi = src[pos], src[pos + 1]; pos += 2
                off = lo | ((hi & 0xF0) << 4)
                for k in range((hi & 0x0F) + 3):
                    b = ring[(off + k) & 0xFFF]
                    append(b); ring[r] = b; r = (r + 1) & 0xFFF
    return bytes(out)


def lzss_encode(data):
    """Reference encoder (used by tests / tools): produces streams lzss_decode() reads. Not optimised."""
    ring = bytearray(4096)
    ring[:4078] = b" " * 4078
    r, i, out = 4078, 0, bytearray()
    while i < len(data):
        flag, items = 0, bytearray()
        for bit in range(8):
            if i >= len(data):
                break
            best_len, best_off = 0, 0
            for off in range(4096):
                sim, rr, ln = bytearray(ring), r, 0
                while ln < 18 and i + ln < len(data):
                    b = sim[(off + ln) & 0xFFF]
                    if b != data[i + ln]:
                        break
                    sim[rr] = b; rr = (rr + 1) & 0xFFF; ln += 1
                if ln > best_len:
                    best_len, best_off = ln, off
                    if ln == 18:
                        break
            if best_len >= 3:
                items += bytes([best_off & 0xFF, ((best_off >> 4) & 0xF0) | (best_len - 3)])
                for k in range(best_len):
                    ring[r] = data[i + k]; r = (r + 1) & 0xFFF
                i += best_len
            else:
                flag |= 1 << bit
                items.append(data[i]); ring[r] = data[i]; r = (r + 1) & 0xFFF; i += 1
        out.append(flag); out += items
    return bytes(out)


WIN_RESERVED = {"con", "prn", "aux", "nul"} | {f"com{i}" for i in range(1, 10)} | {f"lpt{i}" for i in range(1, 10)}


def safe_relpath(raw):
    """Archive path -> safe relative POSIX path. Raises DatError on traversal. Returns (path, notes)."""
    notes = []
    parts = []
    s = raw.replace("\\", "/")
    if s.startswith("/") or re.match(r"^[A-Za-z]:", s):
        notes.append("absolute path made relative")
    for p in s.split("/"):
        if p in ("", "."):
            continue
        if p == "..":
            raise DatError(f"unsafe path (parent traversal): {raw!r}")
        q = re.sub(r'[\x00-\x1f<>:"|?*]', "_", p)
        q = q.rstrip(" .") or "_"
        if q.split(".")[0].lower() in WIN_RESERVED:
            q = "_" + q
        if q != p:
            notes.append(f"component {p!r} renamed to {q!r}")
        parts.append(q)
    if not parts:
        raise DatError(f"empty path: {raw!r}")
    return "/".join(parts), notes


class DatArchive:
    """One .DAT file. Entries are listed without reading any file data; data is streamed on demand."""
    kind = "archive"

    def __init__(self, path, fmt, entries, base, warnings=None):
        self.path, self.format, self.entries, self.base, self.warnings = Path(path), fmt, entries, base, warnings or []
        self.size = Path(path).stat().st_size

    @classmethod
    def open(cls, path):
        path = Path(path)
        size = path.stat().st_size
        errors = []
        with open(path, "rb") as f:
            for name, parser in (("DAT2", _parse_dat2), ("DAT1", _parse_dat1)):
                try:
                    f.seek(0)
                    entries, base, warns = parser(f, size)
                    return cls(path, name, entries, base, warns)
                except (DatError, struct.error, ValueError, OverflowError, MemoryError) as e:
                    errors.append(f"{name}: {e}")
        raise DatError(f"{path.name}: not a readable Fallout DAT1 or DAT2 archive ({'; '.join(errors)})")

    def iter_entry(self, e, chunk=1 << 20):
        """Yield the decoded bytes of an entry in chunks (raw/zlib are streamed; LZSS decodes one block at a time)."""
        if e.method == "unsupported":
            raise DatError(f"unsupported compression flags 0x{e.flags:X}")
        if e.method == "corrupt":
            raise DatError("entry offset/size lies outside the archive")
        with open(self.path, "rb") as f:
            f.seek(self.base + e.offset)
            if e.method == "raw":
                left = e.size
                while left:
                    b = f.read(min(chunk, left))
                    if not b:
                        raise DatError("archive truncated inside entry data")
                    left -= len(b); yield b
            elif e.method == "zlib":
                d, left = zlib.decompressobj(), e.packed
                while left:
                    b = f.read(min(chunk, left))
                    if not b:
                        raise DatError("archive truncated inside compressed data")
                    left -= len(b)
                    try:
                        out = d.decompress(b)
                    except zlib.error as ex:
                        raise DatError(f"zlib error: {ex}")
                    if out:
                        yield out
                try:
                    tail = d.flush()
                except zlib.error as ex:
                    raise DatError(f"zlib error: {ex}")
                if tail:
                    yield tail
                if not d.eof:
                    raise DatError("zlib stream incomplete")
            elif e.method == "lzss":
                data = f.read(e.packed)
                if len(data) != e.packed:
                    raise DatError("archive truncated inside LZSS data")
                yield lzss_decode(data)
            elif e.method == "lzss-blocks":
                produced = 0
                while produced < e.size:
                    h = f.read(2)
                    if len(h) < 2:
                        raise DatError("archive truncated at block header")
                    v = (h[0] << 8) | h[1]                      # big-endian (db.cc fread_short)
                    if v == 0:
                        raise DatError("zero-length block")
                    n = v & 0x7FFF
                    blk = f.read(n)
                    if len(blk) != n:
                        raise DatError("archive truncated inside block")
                    out = blk if v & 0x8000 else lzss_decode(blk)
                    produced += len(out)
                    yield out
            else:
                raise DatError(f"unknown method {e.method}")

    def read_entry(self, e, limit=None):
        buf = bytearray()
        for b in self.iter_entry(e):
            buf += b
            if limit and len(buf) > limit:
                raise DatError("entry larger than preview limit")
        return bytes(buf)


def _u32le(b, o):
    return struct.unpack_from("<I", b, o)[0]


def _parse_dat2(f, size):
    """Fallout 2: footer = u32 treeSize, u32 dataSize (little-endian); tree = u32 count + entries
    {u32 pathLen, path, u8 compressed, u32 unpacked, u32 packed, u32 offset}. Offsets are relative to size - dataSize."""
    if size < 12:
        raise DatError("too small")
    f.seek(size - 8)
    tree, dsz = struct.unpack("<II", f.read(8))
    if tree < 4 or tree + 8 > size or dsz > size or dsz < tree + 8:
        raise DatError("footer sizes are inconsistent")
    f.seek(size - 8 - tree)
    buf = f.read(tree)
    count = _u32le(buf, 0)
    if count * 17 > tree:
        raise DatError("entry count impossible for table size")
    base = size - dsz
    pos, entries, warns = 4, [], []
    for i in range(count):
        if pos + 4 > len(buf):
            raise DatError("file table truncated")
        plen = _u32le(buf, pos); pos += 4
        if plen == 0 or plen > 1024 or pos + plen + 13 > len(buf):
            raise DatError(f"bad path length in entry {i}")
        raw = buf[pos:pos + plen].decode("latin-1"); pos += plen
        comp = buf[pos]; unp, packed, off = struct.unpack_from("<III", buf, pos + 1); pos += 13
        method = "zlib" if comp == 1 else "raw"
        if method == "raw" and packed != unp:
            warns.append(f"{raw}: stored size {packed} != unpacked size {unp}")
        if base + off + (packed if method == "zlib" else unp) > size - 8 - tree:
            method = "corrupt"                          # reported individually at extraction time
        entries.append(DatEntry(raw, unp, packed, off, method, comp))
    if pos != len(buf):
        warns.append(f"{len(buf) - pos} unused bytes after file table")
    return entries, base, warns


def _be32(f):
    b = f.read(4)
    if len(b) != 4:
        raise DatError("unexpected end of archive")
    return struct.unpack(">i", b)[0]


def _parse_dat1(f, size):
    """Fallout 1 (fallout1-ce assoc.cc / db.cc), all integers big-endian:
    root = {i32 dirCount, max, dataSize, ptr} then per dir {u8 len, name[, dataSize bytes]};
    then per dir {i32 fileCount, max, dataSize(=16), ptr} + per file {u8 len, name, i32 flags, offset, length, packedSize}."""
    n_dirs, _mx, root_ds, _p = _be32(f), _be32(f), _be32(f), _be32(f)
    if not (0 < n_dirs <= 100000) or not (0 <= root_ds <= 1024):
        raise DatError("implausible DAT1 header")
    dirs = []
    for _ in range(n_dirs):
        ln = f.read(1)
        if not ln:
            raise DatError("directory list truncated")
        name = f.read(ln[0])
        if len(name) != ln[0]:
            raise DatError("directory name truncated")
        if root_ds:
            f.seek(root_ds, 1)
        dirs.append(name.decode("latin-1"))
    entries, warns = [], []
    for di, dname in enumerate(dirs):
        cnt, _mx, ds, _p = _be32(f), _be32(f), _be32(f), _be32(f)
        if not (0 <= cnt <= 2000000) or ds != 16:
            raise DatError(f"directory {dname!r}: bad file table header (count {cnt}, entry size {ds})")
        prefix = "" if dname in (".", "") else dname.rstrip("\\/") + "\\"
        for _ in range(cnt):
            ln = f.read(1)
            if not ln:
                raise DatError("file table truncated")
            name = f.read(ln[0])
            if len(name) != ln[0] or not name:
                raise DatError("file name truncated")
            flags, off, length, packed = _be32(f), _be32(f), _be32(f), _be32(f)
            kind = (flags or 0x10) & 0xF0                  # engine: flags == 0 behaves like 16
            method = {0x10: "lzss", 0x20: "raw", 0x40: "lzss-blocks"}.get(kind, "unsupported")
            end = off + (length if method == "raw" else packed if method == "lzss" else 0)
            if off < 0 or length < 0 or packed < 0 or off > size or end > size:
                method = "corrupt"
            entries.append(DatEntry(prefix + name.decode("latin-1"), length, packed, off, method, flags))
    tail = size - f.tell()
    if tail < 0:
        raise DatError("file table runs past the end of the archive")
    return entries, 0, warns


class LooseDir:
    """A plain folder (e.g. the game's data/ override folder) treated like an archive that never compresses."""
    kind = "folder"
    format = "FOLDER"

    def __init__(self, path):
        self.path, self.base, self.warnings, self.entries = Path(path), 0, [], []
        for p in sorted(self.path.rglob("*")):
            if p.is_file():
                rel = p.relative_to(self.path).as_posix()
                self.entries.append(DatEntry(rel, p.stat().st_size, p.stat().st_size, 0, "raw", 0, file=str(p)))
        self.size = sum(e.size for e in self.entries)

    def iter_entry(self, e, chunk=1 << 20):
        with open(e.file, "rb") as f:
            while True:
                b = f.read(chunk)
                if not b:
                    return
                yield b

    def read_entry(self, e, limit=None):
        return Path(e.file).read_bytes()


def archive_priority(path):
    """Engine load order assumption: master < critter < other .dat < patchNNN < f2_res (later overrides earlier)."""
    n = Path(path).name.lower()
    if n == "master.dat":
        return 0
    if n == "critter.dat":
        return 1
    m = re.match(r"patch(\d+)\.dat$", n)
    if m:
        return 100 + int(m.group(1))
    if n == "f2_res.dat":
        return 2000
    return 50


def discover_install(folder):
    """Workflow D: find DAT archives (and the loose data/ folder) in a Fallout installation directory."""
    folder = Path(folder)
    dats = sorted([p for p in folder.iterdir() if p.is_file() and p.suffix.lower() == ".dat"], key=lambda p: (archive_priority(p), p.name.lower()))
    loose = next((p for p in folder.iterdir() if p.is_dir() and p.name.lower() == "data"), None)
    return dats, loose


def open_archives(paths):
    """Open several archives (and folders); returns (archives sorted by priority, [(path, error)])."""
    ok, bad = [], []
    for p in paths:
        try:
            ok.append(LooseDir(p) if Path(p).is_dir() else DatArchive.open(p))
        except (DatError, OSError) as e:
            bad.append((str(p), str(e)))
    ok.sort(key=lambda a: (2999 if a.kind == "folder" else archive_priority(a.path)))
    return ok, bad


def entry_matches(e, search="", exts=None, paths=None, regex=False):
    if paths is not None and e.path not in paths:
        return False
    if exts and e.ext not in exts:
        return False
    if search:
        if regex:
            return re.search(search, e.path, re.I) is not None
        return search.lower() in e.path.lower()
    return True


def parse_exts(text):
    if not text:
        return None
    return {("." + x.strip().lower().lstrip(".")) for x in re.split(r"[,; ]+", text) if x.strip()}


SIGNATURES = {".rix": lambda h: h[:4] == b"RIX3" or "missing RIX3 signature",
              ".aaf": lambda h: h[:4] == b"AAFF" or "missing AAFF signature",
              ".frm": lambda h: (len(h) >= 62 and struct.unpack(">I", h[:4])[0] == 4) or "FRM header not version 4 / too short",
              ".pal": lambda h: len(h) >= 768 or "palette smaller than 768 bytes",
              ".mve": lambda h: h[:18] == b"Interplay MVE File" or "missing 'Interplay MVE File' signature"}


def check_signature(ext, head, size):
    fn = SIGNATURES.get(ext)
    if not fn:
        return None
    if ext == ".pal":
        r = size >= 768 or "palette smaller than 768 bytes"
    else:
        r = fn(head)
    return None if r is True else r


def extract_entries(items, out_dir, progress=None, cancel=None, conflicts="override", verify=True):
    """items: list of (archive, entry), ordered lowest -> highest priority.
    Streams every entry to <out_dir>/<safe archive path>, validates sizes, never aborts on one bad entry.
    Returns a report dict (extracted / failed / overridden / renamed / unsupported)."""
    out_dir = Path(out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    real_out = os.path.realpath(out_dir)
    sources = {os.path.realpath(a.path) for a, _ in items if a.kind == "archive"}
    rep = dict(output=str(out_dir), results=[], conflicts=conflicts)
    plan, seen = [], {}                    # seen: lowercase rel -> index in plan
    for a, e in items:
        res = dict(archive=str(a.path), format=a.format, internal_path=e.raw_path, size=e.size, method=e.method)
        try:
            rel, notes = safe_relpath(e.path)
        except DatError as ex:
            res.update(status="failed", error=str(ex)); rep["results"].append(res); continue
        if notes:
            res["notes"] = notes
        key = rel.lower()
        if key in seen:
            prev = plan[seen[key]]
            same_archive = prev[0] is a
            if same_archive or conflicts == "rename":
                n = 1
                stem, ext = os.path.splitext(rel)
                while f"{stem}__dup{n}{ext}".lower() in seen:
                    n += 1
                rel = f"{stem}__dup{n}{ext}"; key = rel.lower()
                res["status_note"] = "renamed: duplicate path" + (" inside the same archive" if same_archive else "")
            elif conflicts == "keep":
                res.update(status="skipped", error=f"kept earlier copy from {prev[0].path}"); rep["results"].append(res); continue
            else:                                   # override: higher-priority archive replaces the earlier plan entry
                prev[4]["status"] = "overridden"; prev[4]["error"] = f"overridden by {a.path}"
                prev[5] = True
        res["output_path"] = rel
        seen[key] = len(plan)
        plan.append([a, e, rel, res, res, False])
        rep["results"].append(res)
    todo = [p for p in plan if not p[5]]
    total_files, total_bytes = len(todo), sum(p[1].size for p in todo)
    done_files = done_bytes = 0
    last = [0.0]

    def tick(cur, force=False):
        if progress and (force or time.time() - last[0] > 0.1):
            last[0] = time.time()
            progress(dict(files_done=done_files, files_total=total_files, bytes_done=done_bytes, bytes_total=total_bytes, current=cur))

    for a, e, rel, res, _r, skipped in todo:
        if cancel is not None and cancel.is_set():
            res["status"] = "cancelled"; continue
        dest = out_dir / rel
        try:
            real = os.path.realpath(dest)
            if os.path.commonpath([real, real_out]) != real_out or real in sources:
                raise DatError("refusing to write outside the output folder / over a source archive")
            dest.parent.mkdir(parents=True, exist_ok=True)
            part = dest.with_name(dest.name + ".part")
            written, head = 0, b""
            with open(part, "wb") as w:
                for chunk in a.iter_entry(e):
                    if cancel is not None and cancel.is_set():
                        raise Cancelled()
                    if len(head) < 64:
                        head = (head + chunk)[:64]
                    w.write(chunk); written += len(chunk); done_bytes += len(chunk)
                    tick(rel)
            if verify and written != e.size:
                raise DatError(f"size mismatch: expected {e.size} bytes, got {written}")
            warn = check_signature(e.ext, head, written) if verify else None
            os.replace(part, dest)
            res["status"] = "extracted"; res["written"] = written
            if warn:
                res["warning"] = warn
        except Cancelled:
            res["status"] = "cancelled"
            try:
                part.unlink()
            except Exception:
                pass
            for r in rep["results"]:
                if "status" not in r:
                    r["status"] = "cancelled"
            break
        except (DatError, OSError, zlib.error) as ex:
            res["status"] = "unsupported" if e.method == "unsupported" else "failed"
            res["error"] = str(ex)
            try:
                part.unlink()
            except Exception:
                pass
        done_files += 1
        tick(rel, force=(done_files == total_files))
    c = Counter(r.get("status", "?") for r in rep["results"])
    rep["summary"] = dict(c, files=len(rep["results"]), bytes=done_bytes)
    return rep


def write_extract_report(rep, folder):
    folder = Path(folder); folder.mkdir(parents=True, exist_ok=True)
    (folder / "extraction_report.json").write_text(json.dumps(rep, indent=1), encoding="utf-8")
    with open(folder / "extraction_report.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(["archive", "internal_path", "status", "output_path", "size", "method", "note"])
        for r in rep["results"]:
            w.writerow([r.get("archive"), r.get("internal_path"), r.get("status"), r.get("output_path", ""), r.get("size"), r.get("method"),
                        r.get("error") or r.get("warning") or r.get("status_note") or "; ".join(r.get("notes", []))])


def collect_items(archives, search="", exts=None, paths=None, regex=False, always_exts=None):
    """Entries matching the filter (+ always_exts, e.g. .pal needed for colour), lowest priority first."""
    items = []
    for a in archives:
        for e in a.entries:
            if entry_matches(e, search, exts, paths, regex) or (always_exts and e.ext in always_exts):
                items.append((a, e))
    return items


# ----------------------------------------------------------------------------- worker side
CFG = {}
PAL_CACHE = {}


def init_worker(cfg):
    global CFG
    CFG = cfg


def load_pal_file(path):
    if path not in PAL_CACHE:
        PAL_CACHE[path] = Palette.from_bytes(Path(path).read_bytes(), Path(path).name, path)
    return PAL_CACHE[path]


def choose_palette(src):
    """Return (Palette, how, certainty). Order: explicit map > same-stem .pal beside file > global color.pal."""
    for pattern, palpath in CFG["palette_map"]:
        if fnmatch.fnmatch(str(src).replace("\\", "/").lower(), pattern.lower()):
            return load_pal_file(palpath), f"explicit map '{pattern}'", "explicit"
    key = (str(src.parent).lower(), src.stem.lower())
    if key in CFG["pal_index"]:
        return load_pal_file(CFG["pal_index"][key]), "same-name .pal beside file", "heuristic"
    if CFG["global_pal"]:
        return load_pal_file(CFG["global_pal"]), "global color.pal", "default"
    if CFG["allow_gray"]:
        return grayscale_palette(), "GRAYSCALE FALLBACK", "none"
    raise DecodeError("no palette available (no color.pal found and --allow-grayscale not set)")


def finalize_palette(pal):
    return pal.with_cycle() if CFG["cycle"] == "engine" else pal


def out_path(rel, filename):
    """Output is an exact copy of the dump's folder tree: <out>/<same relative folder>/<filename>."""
    p = Path(CFG["out"]) / rel / filename
    p.parent.mkdir(parents=True, exist_ok=True)
    return p


def folder_rel(rel, base):
    """Folder that holds a file's extracted images: <same relative folder>/<exact original name>/"""
    return f"{rel}/{base}" if rel else base


def relroot(p):
    return Path(p).relative_to(CFG["out"]).as_posix()


def convert_one(job):
    src, rel, base, fmt = job
    src = Path(src)
    res = dict(source=str(src), rel=rel, base=base, format=fmt, status="ok", warnings=[], error="", outputs=[], summary={})
    main = Path(CFG["out"]) / rel / f"{base}.png"
    side = Path(CFG["out"]) / rel / f"{base}.json"
    try:
        if (not CFG["force"] and main.exists() and main.stat().st_mtime >= src.stat().st_mtime
                and (not CFG["sidecar"] or side.exists())):
            res.update(status="skipped_existing", summary=dict(preview=relroot(main)), outputs=[relroot(main)])
            return res
        data = src.read_bytes()
        meta = dict(tool_version=VERSION, source_path=str(src), source_size=len(data),
                    source_sha1=hashlib.sha1(data).hexdigest(), format=fmt)
        {"frm": do_frm, "rix": do_rix, "pal": do_pal, "fon": do_fon, "aaf": do_aaf}[fmt](src, data, rel, base, res, meta)
        if res["warnings"]:
            res["status"] = "ok_with_warnings"
        if CFG["sidecar"]:
            meta.update(status=res["status"], warnings=res["warnings"])
            out_path(rel, f"{base}.json").write_text(json.dumps(meta, indent=1))
    except DecodeError as e:
        res.update(status="failed", error=str(e))
    except Exception as e:
        res.update(status="failed", error=f"internal error: {e!r}", traceback=traceback.format_exc())
    return res


def do_frm(src, data, rel, base, res, meta):
    frm = decode_frm(data)
    res["warnings"] += frm.warnings
    pal, how, certainty = choose_palette(src)
    pal = finalize_palette(pal)
    flat = pal.flat(CFG["pal_scale"])
    fps = frm.header["fps"] or 10
    ext = src.suffix.lower()
    forced = int(ext[3]) if ext.startswith(".fr") and ext[3:].isdigit() else None
    if forced is not None and len(frm.blocks) > 1:
        res["warnings"].append(f"{ext} file contains {len(frm.blocks)} direction blocks; expected 1")
        forced = None
    block_dirs = defaultdict(list)
    for d, bi in enumerate(frm.dir_map):
        block_dirs[bi].append(d)
    multi = len(frm.blocks) > 1
    tags = [forced if forced is not None else block_dirs[bi][0] for bi in range(len(frm.blocks))]
    all_imgs, tot, mblocks = [], Counter(), []
    for bi, frames in enumerate(frm.blocks):
        imgs = [indexed_to_rgba(f.w, f.h, f.pix, flat) if f.w and f.h else None for f in frames]
        st = Counter()
        for f in frames:
            st.update(pixel_stats(f.pix, pal))
        tot.update(st)
        all_imgs.append(imgs)
        mblocks.append(dict(block=bi, serves_directions=[forced] if forced is not None else block_dirs[bi], pixel_stats=dict(st)))
    fpd = frm.header["frames_per_direction"]
    flat_imgs = [im for imgs in all_imgs for im in imgs]
    # the ONE output file: <NAME>.png - the frame itself, or a sheet (one row per direction, one column per frame)
    if multi:
        sheet, cw, ch, pos = make_sheet(flat_imgs, "grid", fpd, CFG["sheet_pad"], CFG["sheet_anchor"])
    else:
        sheet, cw, ch, pos = make_sheet(flat_imgs, CFG["sheet_layout"], CFG["sheet_cols"], CFG["sheet_pad"], CFG["sheet_anchor"])
    sp = out_path(rel, f"{base}.png"); sheet.save(sp); res["outputs"].append(relroot(sp))
    # optional extras (off by default): --frames, --previews
    # every individual frame -> folder named exactly like the source (only when the file yields more than one image)
    items = [(d, frm.dir_map[d]) for d in range(6)] if multi else [(None, 0)]
    if CFG["frames"] and (len(items) * fpd > 1 or CFG["folders_always"]):
        fol = folder_rel(rel, base)
        for d, bi in items:
            for i, im in enumerate(all_imgs[bi]):
                if im is None:
                    continue
                p = out_path(fol, f"{base}_d{d}_f{i:02d}.png" if multi else f"{base}_f{i:02d}.png")
                im.save(p); res["outputs"].append(relroot(p))
    k = 0
    for bi, imgs in enumerate(all_imgs):
        if CFG["previews"] and len([x for x in imgs if x]) > 1:
            try:
                gp = out_path(rel, f"{base}_dir{tags[bi]}.gif" if multi else f"{base}.gif")
                save_gif(imgs, gp, fps); res["outputs"].append(relroot(gp))
            except Exception as e:
                res["warnings"].append(f"GIF preview failed for direction {tags[bi]}: {e}")
        mblocks[bi].update(direction_tag=tags[bi], frames=[
            dict(index=i, w=f.w, h=f.h, offset_x=f.ox, offset_y=f.oy, sheet_x=pos[k + i][0], sheet_y=pos[k + i][1])
            for i, f in enumerate(frm.blocks[bi])])
        k += len(imgs)
    if tot["unmapped_palette_pixels"]:
        res["warnings"].append(f"{tot['unmapped_palette_pixels']} pixels use palette entries that are invalid/unmapped in {pal.name} (rendered black)")
    if certainty == "heuristic":
        res["warnings"].append(f"palette chosen heuristically: {how} ({pal.source})")
    if certainty == "none":
        res["warnings"].append("GRAYSCALE fallback palette used - colours are NOT original")
    meta.update(header=frm.header, direction_map=frm.dir_map, sheet=relroot(sp), cell_w=cw, cell_h=ch,
                sheet_layout="rows=directions, columns=frames" if multi else CFG["sheet_layout"], blocks=mblocks,
                palette=dict(name=pal.name, source=pal.source, how=how, certainty=certainty, cycle=CFG["cycle"], scale=CFG["pal_scale"]),
                transparency="palette index 0")
    res["summary"] = dict(w=sheet.width, h=sheet.height, cell_w=cw, cell_h=ch, frames=fpd, directions=len(frm.blocks),
                          palette=pal.source or pal.name, palette_how=how, certainty=certainty, preview=relroot(sp), fps=fps)


def do_rix(src, data, rel, base, res, meta):
    r = decode_rix(data)
    res["warnings"] += r["warnings"]
    pal = r["palette"]
    im = indexed_to_rgba(r["w"], r["h"], r["pix"], pal.flat(CFG["pal_scale"]), transparent0=False)
    p = out_path(rel, f"{base}.png"); im.save(p); res["outputs"].append(relroot(p))
    st = pixel_stats(r["pix"], pal)
    if st["unmapped_palette_pixels"]:
        res["warnings"].append(f"{st['unmapped_palette_pixels']} pixels use unmapped embedded-palette entries")
    meta.update(width=r["w"], height=r["h"], palette_type=r["pal_type"], storage_type=r["storage_type"],
                transparency="none (opaque)", palette=dict(name="embedded", certainty="certain", scale=CFG["pal_scale"]), pixel_stats=st)
    res["summary"] = dict(w=r["w"], h=r["h"], frames=1, directions=1, palette="embedded", certainty="certain", preview=relroot(p))


def do_pal(src, data, rel, base, res, meta):
    pal = Palette.from_bytes(data, src.name, str(src))
    if pal.info["unmapped_entries"]:
        res["warnings"].append(f"{pal.info['unmapped_entries']} entries > 63 (engine treats as black/unmapped)")
    im = Image.new("RGBA", (16 * 8, 16 * 8))
    rgb = pal.rgb(CFG["pal_scale"])
    for i, c in enumerate(rgb):
        im.paste(c + (255,), ((i % 16) * 8, (i // 16) * 8, (i % 16) * 8 + 8, (i // 16) * 8 + 8))
    p = out_path(rel, f"{base}.png"); im.save(p); res["outputs"].append(relroot(p))
    meta.update(info=pal.info, entries=[dict(index=i, raw6=list(pal.raw6[i]), rgb=list(rgb[i]), mapped=pal.mapped[i]) for i in range(256)],
                note="index 0 is transparent for sprites; indices 229-253 are cycled by the engine at runtime. PNG = 16x16 swatch grid, 8px cells")
    res["summary"] = dict(w=128, h=128, frames=1, directions=1, palette=src.name, certainty="n/a", preview=relroot(p))


def font_cell_grid(n):
    return 16, (n + 15) // 16


def do_fon(src, data, rel, base, res, meta):
    f = decode_fon(data)
    res["warnings"] += f["warnings"]
    n, lh = f["glyph_count"], f["line_height"]
    cw = max([g["width"] for g in f["glyphs"]] + [1])
    cols, rows = font_cell_grid(n)
    atlas = Image.new("RGBA", (cols * cw, rows * lh), (0, 0, 0, 0))
    gl = []
    for g in f["glyphs"]:
        gx, gy = (g["code"] % cols) * cw, (g["code"] // cols) * lh
        im = Image.new("RGBA", (max(g["width"], 1), lh), (0, 0, 0, 0))
        for y, row in enumerate(g["rows"]):
            for x, bit in enumerate(row):
                if bit:
                    im.putpixel((x, y), (255, 255, 255, 255))
        atlas.paste(im, (gx, gy))
        if g["width"] and CFG["frames"]:
            p = out_path(folder_rel(rel, base), f"{base}_g{g['code']:03d}.png"); im.save(p); res["outputs"].append(relroot(p))
        gl.append(dict(code=g["code"], char=bytes([g["code"]]).decode("cp1252", "replace") if 32 <= g["code"] < 256 else "",
                       width=g["width"], height=lh, advance=g["width"] + f["letter_spacing"], x_offset=0, y_offset=0,
                       atlas_x=gx, atlas_y=gy, data_offset=g["offset"]))
    ap = out_path(rel, f"{base}.png"); atlas.save(ap); res["outputs"].append(relroot(ap))
    meta.update(font=dict(type="FON", glyph_count=n, line_height=lh, letter_spacing=f["letter_spacing"], baseline=lh,
                          cell_w=cw, cell_h=lh, atlas_columns=cols,
                          note="1-bit glyphs, white on transparent; 16 columns, glyph index = char code. advance = width + letter_spacing"), glyphs=gl)
    res["summary"] = dict(w=atlas.width, h=atlas.height, frames=n, directions=1, palette="n/a", certainty="n/a", preview=relroot(ap))


def do_aaf(src, data, rel, base, res, meta):
    f = decode_aaf(data)
    res["warnings"] += f["warnings"]
    mh, mx = f["max_height"], max(f["max_intensity"], 1)
    cw = max([g["width"] for g in f["glyphs"]] + [f["word_spacing"], 1])
    cols, rows = font_cell_grid(256)
    atlas = Image.new("RGBA", (cols * cw, rows * mh), (0, 0, 0, 0))
    gl = []
    for g in f["glyphs"]:
        gx, gy = (g["code"] % cols) * cw, (g["code"] // cols) * mh
        yoff = mh - g["height"]                       # engine skips (maxHeight - height) rows above the glyph
        if g["width"] and g["height"]:
            im = Image.new("RGBA", (g["width"], g["height"]), (255, 255, 255, 0))
            im.putdata([(255, 255, 255, min(255, round(v * 255 / mx))) for v in g["pix"]])
            atlas.paste(im, (gx, gy + yoff))
            if CFG["frames"]:
                p = out_path(folder_rel(rel, base), f"{base}_g{g['code']:03d}.png"); im.save(p); res["outputs"].append(relroot(p))
        adv = f["word_spacing"] if g["code"] == 32 else g["width"] + f["letter_spacing"]
        gl.append(dict(code=g["code"], char=bytes([g["code"]]).decode("cp1252", "replace") if 32 <= g["code"] < 256 else "",
                       width=g["width"], height=g["height"], advance=adv, x_offset=0, y_offset=yoff,
                       atlas_x=gx, atlas_y=gy, data_offset=g["offset"]))
    ap = out_path(rel, f"{base}.png"); atlas.save(ap); res["outputs"].append(relroot(ap))
    meta.update(font=dict(type="AAF", glyph_count=256, line_height=mh, max_height=mh, letter_spacing=f["letter_spacing"],
                          word_spacing=f["word_spacing"], line_spacing=f["line_spacing"], baseline=mh, cell_w=cw, cell_h=mh,
                          max_intensity=f["max_intensity"], atlas_columns=cols,
                          note="alpha = intensity / max_intensity, white RGB; 16 columns, glyph index = char code; glyph sits y_offset rows below cell top"), glyphs=gl)
    res["summary"] = dict(w=atlas.width, h=atlas.height, frames=256, directions=1, palette="n/a", certainty="n/a", preview=relroot(ap))


# ----------------------------------------------------------------------------- driver
def scan(src):
    files, pal_index, unsupported, ext_count = [], {}, [], Counter()
    for p in sorted(Path(src).rglob("*")):
        if not p.is_file():
            continue
        ext = p.suffix.lower()
        ext_count[ext] += 1
        fmt = FORMAT_BY_EXT.get(ext)
        if fmt:
            files.append((p, fmt))
            if fmt == "pal":
                pal_index[(str(p.parent).lower(), p.stem.lower())] = str(p)
        else:
            unsupported.append(p)
    return files, pal_index, unsupported, ext_count


def find_global_pal(files, forced):
    if forced:
        return forced, []
    cands = sorted([p for p, fmt in files if p.name.lower() == "color.pal"], key=lambda p: (len(p.parts), str(p)))
    return (str(cands[0]) if cands else None), [str(c) for c in cands[1:]]


def run(a):
    src = Path(a.src)
    out = Path(a.dst)
    rep_dir = Path(a.report_dir) if a.report_dir else out.parent / (out.name + "_reports")
    files, pal_index, unsupported, ext_count = scan(src)
    gpal, extra_pals = find_global_pal(files, a.pal)
    palette_map = list(json.loads(Path(a.palette_map).read_text()).items()) if a.palette_map else []
    if any(fmt == "frm" for _, fmt in files) and not gpal and not a.allow_grayscale:
        print("\nERROR: no color.pal found under", src, "\n  FRM files cannot be coloured without it. Pass --pal PATH, "
              "or --allow-grayscale to accept wrong (gray) colours.", file=sys.stderr)
        return 2
    print(f"source: {src}\n  {len(files)} convertible files, {len(unsupported)} other files ({len(ext_count)} extensions)")
    print(f"  global palette: {gpal or 'NONE'}" + (f"  (also found: {len(extra_pals)} more color.pal)" if extra_pals else ""))
    print(f"output: {out}   (exact copy of the dump's folders; reports go to {rep_dir})")

    # Output name = original file name with .png, same relative folder. Only when two sources in one folder share a
    # name (x.frm + x.pal, or NAME.FR0..FR5) is the extension appended so nothing is overwritten.
    groups = defaultdict(list)
    for p, fmt in files:
        groups[(p.parent.relative_to(src).as_posix().lower(), p.stem.lower())].append(p)
    seen, jobs, dup_events, by_stem = {}, [], [], defaultdict(list)
    for p, fmt in files:
        rel = p.parent.relative_to(src).as_posix()
        clash = len(groups[(rel.lower(), p.stem.lower())]) > 1
        rel = "" if rel == "." else rel
        ext = p.suffix.lower()
        base = f"{p.stem}_{ext[1:]}" if clash else p.stem
        if clash:
            dup_events.append(dict(source=str(p), reason="same name, different extension in one folder", output_name=base))
        key = (rel.lower(), base.lower())
        if key in seen:
            seen[key] += 1
            dup_events.append(dict(source=str(p), reason="case-insensitive name collision", output_name=f"{base}__dup{seen[key]}"))
            base = f"{base}__dup{seen[key]}"
        else:
            seen[key] = 0
        by_stem[(p.stem.lower(), ext)].append(str(p))
        jobs.append((str(p), rel, base, fmt))
    dup_names = {f"{s}{e}": v for (s, e), v in by_stem.items() if len(v) > 1}

    cfg = dict(out=str(out), force=a.force, cycle=a.cycle, pal_scale=a.pal_scale, sheet_layout=a.sheet_layout, sheet_cols=a.sheet_cols,
               sheet_pad=a.sheet_pad, sheet_anchor=a.sheet_anchor, previews=a.previews, frames=not a.no_frames, folders_always=a.folders_always, sidecar=a.sidecar_json,
               global_pal=gpal, pal_index=pal_index, palette_map=palette_map, allow_gray=a.allow_grayscale)
    out.mkdir(parents=True, exist_ok=True); rep_dir.mkdir(parents=True, exist_ok=True)

    t0, results = time.time(), []
    with Pool(a.jobs, initializer=init_worker, initargs=(cfg,)) as pool:
        for n, r in enumerate(pool.imap_unordered(convert_one, jobs, chunksize=16), 1):
            results.append(r)
            if getattr(a, "progress_cb", None):
                a.progress_cb(n, len(jobs))
            if getattr(a, "cancel", None) is not None and a.cancel.is_set():
                pool.terminate(); print("  cancelled"); break
            if n % 500 == 0 or n == len(jobs):
                bad = sum(x["status"] == "failed" for x in results)
                print(f"  {n}/{len(jobs)}  ({n / max(time.time() - t0, 1e-9):.0f}/s)  failed so far: {bad}", flush=True)
    results.sort(key=lambda r: r["source"])
    write_reports(rep_dir, out, src, results, unsupported, ext_count, dup_events, dup_names, gpal, extra_pals, cfg, time.time() - t0)
    c = Counter(r["status"] for r in results)
    fails = [r for r in results if r["status"] == "failed"]
    if fails:
        import re
        norm = lambda e: re.sub(r"\d+", "N", e)
        why = Counter(norm(r["error"]) for r in fails)
        lines = [f"{n:6d} x {msg}   e.g. {next(r['source'] for r in fails if norm(r['error']) == msg)}" for msg, n in why.most_common()]
        (rep_dir / "failure_summary.txt").write_text("\n".join(lines), encoding="utf-8")
        print("\nFAILURE REASONS (full list: failures.txt in the reports folder):")
        for ln in lines[:8]:
            print("  " + ln)
    print(f"\nDONE in {time.time() - t0:.1f}s: ok={c['ok']}  ok_with_warnings={c['ok_with_warnings']}  skipped_existing={c['skipped_existing']}  "
          f"FAILED={c['failed']}  unsupported files listed={len(unsupported)}\nReports: {rep_dir}  (open gallery_index.html)")
    return 0


def write_reports(rep, out, src, results, unsupported, ext_count, dup_events, dup_names, gpal, extra_pals, cfg, secs):
    c = Counter(r["status"] for r in results)
    fmt_count = Counter((r["format"], r["status"]) for r in results)
    unc = [r for r in results if r.get("summary", {}).get("certainty") in ("heuristic", "none")]
    summary = dict(tool_version=VERSION, source=str(src), output=str(out), seconds=round(secs, 1), totals=dict(c),
                   per_format={f"{k[0]}:{k[1]}": v for k, v in fmt_count.items()}, global_palette=gpal,
                   additional_color_pal_candidates=extra_pals, palette_cycle=cfg["cycle"], palette_scale=cfg["pal_scale"],
                   uncertain_palette_assignments=len(unc), duplicate_output_names=len(dup_events),
                   duplicate_filenames_across_dirs=len(dup_names), unsupported_files=len(unsupported),
                   unsupported_by_extension=dict(Counter(p.suffix.lower() for p in unsupported)))
    (rep / "conversion_report.json").write_text(json.dumps(dict(summary=summary, files=[{k: v for k, v in r.items() if k != "outputs"} for r in results]), indent=1))
    with open(rep / "conversion_report.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(["source", "output", "format", "status", "w", "h", "frames", "directions", "palette", "palette_how", "warnings", "error"])
        for r in results:
            s = r["summary"]
            w.writerow([r["source"], s.get("preview", ""), r["format"], r["status"], s.get("w", ""), s.get("h", ""), s.get("frames", ""),
                        s.get("directions", ""), s.get("palette", ""), s.get("palette_how", ""), " | ".join(r["warnings"]), r["error"]])
    with open(rep / "failures.txt", "w", encoding="utf-8") as f:
        for r in results:
            if r["status"] == "failed":
                f.write(f"{r['source']}\n    {r['error']}\n")
                if r.get("traceback"):
                    f.write(r["traceback"] + "\n")
    with open(rep / "unsupported.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(["path", "extension", "size"])
        for p in unsupported:
            w.writerow([str(p), p.suffix.lower(), p.stat().st_size])
    (rep / "duplicates.json").write_text(json.dumps(dict(renamed_outputs=dup_events, same_filename_in_multiple_dirs=dup_names), indent=1))
    with open(rep / "palette_assignments.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(["source", "palette", "how", "certainty"])
        for r in results:
            s = r["summary"]
            if r["format"] == "frm":
                w.writerow([r["source"], s.get("palette", ""), s.get("palette_how", ""), s.get("certainty", "")])
    write_gallery(rep, out, results)


def write_gallery(rep, out, results, per_page=400):
    pages = [results[i:i + per_page] for i in range(0, len(results), per_page)] or [[]]
    css = ("body{font:14px system-ui;background:#1b1b1b;color:#ddd;margin:16px}.g{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:10px}"
           ".c{background:#262626;border:1px solid #3a3a3a;padding:8px;border-radius:6px;overflow:hidden}.c img{max-width:100%;image-rendering:pixelated;"
           "background:repeating-conic-gradient(#333 0 25%,#444 0 50%) 0 0/16px 16px}.f{color:#fa5}.w{color:#fc6;font-size:12px}.ok{color:#7c7}a{color:#8cf}"
           ".n{word-break:break-all;font-weight:600}")

    def link(rel):
        try:
            return os.path.relpath(Path(out) / rel, rep).replace("\\", "/")
        except ValueError:
            return (Path(out) / rel).as_uri()

    for pi, chunk in enumerate(pages, 1):
        h = [f"<!doctype html><meta charset=utf-8><title>Gallery {pi}</title><style>{css}</style><p><a href=gallery_index.html>index</a> - page {pi}/{len(pages)}</p><div class=g>"]
        for r in chunk:
            s = r["summary"]
            img = f"<img loading=lazy src='{html.escape(link(s['preview']))}'>" if s.get("preview") else ""
            gif = next((o for o in r["outputs"] if o.endswith(".gif")), None)
            if gif:
                img += f"<br><small>animation:</small><br><img loading=lazy src='{html.escape(link(gif))}'>"
            st = {"ok": "ok", "skipped_existing": "ok", "ok_with_warnings": "w", "failed": "f"}[r["status"]]
            h.append(f"<div class=c><div class=n>{html.escape(Path(r['source']).name)}</div>{img}<div class={st}>{r['status']}</div>"
                     f"<div>{r['format'].upper()} {s.get('w', '?')}x{s.get('h', '?')} frames={s.get('frames', '?')} dirs={s.get('directions', '?')}</div>"
                     f"<div>palette: {html.escape(str(s.get('palette', '')))} ({html.escape(str(s.get('certainty', '')))})</div>"
                     + "".join(f"<div class=w>&#9888; {html.escape(x)}</div>" for x in r["warnings"][:6])
                     + (f"<div class=f>{html.escape(r['error'])}</div>" if r["error"] else "") + "</div>")
        h.append("</div>")
        (rep / f"gallery_{pi:04d}.html").write_text("".join(h), encoding="utf-8")
    idx = ["<!doctype html><meta charset=utf-8><title>Fallout 1 conversion gallery</title><style>" + css + "</style><h2>Gallery</h2>"]
    idx += [f"<p><a href=gallery_{i:04d}.html>page {i}</a> ({len(p)} files, first: {html.escape(Path(p[0]['source']).name) if p else ''})</p>" for i, p in enumerate(pages, 1)]
    (rep / "gallery_index.html").write_text("".join(idx), encoding="utf-8")


def pick_folders():
    try:
        import tkinter as tk
        from tkinter import filedialog
        r = tk.Tk(); r.withdraw(); r.attributes("-topmost", True)
        s = filedialog.askdirectory(title="Select your extracted Fallout 1 dump folder")
        if not s:
            sys.exit(0)
        d = filedialog.askdirectory(title="Select OUTPUT folder (it will become an exact copy of the dump's folders, with PNGs)")
        if not d:
            sys.exit(0)
        return s, d
    except Exception:
        return input("Dump folder: ").strip('" '), input("Output folder: ").strip('" ')


def build_parser():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("src"); ap.add_argument("dst")
    add_convert_options(ap)
    return ap


# ----------------------------------------------------------------------------- workflows: DAT -> extract -> convert
CONVERT_KEYS = ["pal", "palette_map", "allow_grayscale", "cycle", "pal_scale", "sheet_layout", "sheet_cols", "sheet_pad",
                "sheet_anchor", "sidecar_json", "no_frames", "folders_always", "previews", "force", "jobs", "report_dir"]


def convert_namespace(src, dst, source_args=None, **over):
    """Build the argparse namespace run() expects, from defaults + overrides (or from another parsed namespace)."""
    base = build_parser().parse_args([str(src), str(dst)])
    for k in CONVERT_KEYS:
        if source_args is not None and hasattr(source_args, k):
            setattr(base, k, getattr(source_args, k))
    for k, v in over.items():
        setattr(base, k, v)
    return base


def extract_and_convert(archives, extract_dir, png_dir=None, search="", exts=None, paths=None, regex=False, conflicts="override",
                        conv_args=None, progress=None, cancel=None, conv_progress=None):
    """Workflows A/B/C/E core. Extracts matching entries (always adding .pal files when converting, because FRMs need
    color.pal), writes the extraction report, then (optionally) feeds the extracted folder to the converter."""
    items = collect_items(archives, search, exts, paths, regex, always_exts={".pal"} if png_dir else None)
    rep = extract_entries(items, extract_dir, progress=progress, cancel=cancel, conflicts=conflicts)
    write_extract_report(rep, Path(str(extract_dir).rstrip("/\\") + "_reports"))
    code = None
    if png_dir and not (cancel is not None and cancel.is_set()):
        ns = conv_args or convert_namespace(extract_dir, png_dir)
        ns.src, ns.dst = str(extract_dir), str(png_dir)
        ns.progress_cb, ns.cancel = conv_progress, cancel
        code = run(ns)
    return rep, code


def find_color_pal(archives):
    for a in reversed(archives):                       # highest priority archive wins
        for e in a.entries:
            if e.path.lower() == "color.pal":
                try:
                    return Palette.from_bytes(a.read_entry(e, limit=1 << 20), "color.pal", f"{a.path}:{e.path}")
                except DatError:
                    pass
    return None


def render_preview(archives, archive, entry, palette=None, limit=24 << 20):
    """Decode one entry in memory for the browser. Returns (RGBA PIL image or None, description)."""
    ext = entry.ext
    if ext in FRM_EXTS:
        frm = decode_frm(archive.read_entry(entry, limit))
        pal = palette or find_color_pal(archives)
        if pal is None:
            return None, "FRM: no color.pal in the loaded archives - open master.dat too for colour preview"
        pal = finalize_cycle(pal)
        fr = frm.blocks[0][0]
        im = indexed_to_rgba(fr.w, fr.h, fr.pix, pal.flat()) if fr.w and fr.h else None
        return im, (f"FRM {fr.w}x{fr.h}, {frm.header['frames_per_direction']} frames, {len(frm.blocks)} direction block(s), "
                    f"fps {frm.header['fps']} (showing frame 0)")
    if ext == ".rix":
        r = decode_rix(archive.read_entry(entry, limit))
        return indexed_to_rgba(r["w"], r["h"], r["pix"], r["palette"].flat(), transparent0=False), f"RIX {r['w']}x{r['h']}"
    if ext == ".pal":
        pal = Palette.from_bytes(archive.read_entry(entry, limit), entry.path)
        im = Image.new("RGBA", (128, 128))
        for i, c in enumerate(pal.rgb()):
            im.paste(c + (255,), ((i % 16) * 8, (i // 16) * 8, (i % 16) * 8 + 8, (i // 16) * 8 + 8))
        return im, f"PAL, {pal.info['unmapped_entries']} unmapped entries"
    return None, f"{ext or 'file'}: no preview for this type ({entry.size} bytes)"


def finalize_cycle(pal):
    return pal.with_cycle()


class AssetModel:
    """Everything the browser needs, without any GUI toolkit (so it is unit-tested)."""

    def __init__(self):
        self.archives, self.errors, self._pal = [], [], None

    def load(self, paths):
        self.archives, self.errors = open_archives(paths)
        self._pal = None
        return self

    def items(self):
        return [(a, e) for a in self.archives for e in a.entries]

    def ext_counts(self):
        return Counter(e.ext or "(none)" for _, e in self.items())

    def filtered(self, search="", ext=None, regex=False):
        exts = {ext} if ext and ext not in ("All", "") else None
        return [(a, e) for a, e in self.items() if entry_matches(e, search, exts, None, regex)]

    def preview(self, a, e):
        if self._pal is None:
            self._pal = find_color_pal(self.archives)
        return render_preview(self.archives, a, e, self._pal)


# ----------------------------------------------------------------------------- DAT command line
def console_progress(p):
    sys.stdout.write(f"\r  extracting {p['files_done']}/{p['files_total']} files   {p['bytes_done'] / 1e6:.1f}/{p['bytes_total'] / 1e6:.1f} MB   "
                     f"{p['current'][-40:]:<40}")
    sys.stdout.flush()


def add_convert_options(ap):
    ap.add_argument("--report-dir", help="where reports/gallery go (default: <output>_reports, a sibling of the output folder)")
    ap.add_argument("--pal", help="color.pal to use (default: auto-find in dump)")
    ap.add_argument("--palette-map", help="JSON {glob: pal path} to override palette for matching source paths")
    ap.add_argument("--allow-grayscale", action="store_true", help="convert FRMs even with no palette (WRONG colours)")
    ap.add_argument("--cycle", choices=["engine", "none"], default="engine",
                    help="engine: apply the engine's runtime palette cycling (idx 229-253, frame 0). none: raw color.pal")
    ap.add_argument("--pal-scale", choices=["engine", "full"], default="engine",
                    help="engine: 6-bit<<2 exactly like the game (max 252). full: stretch to 0-255")
    ap.add_argument("--sheet-layout", choices=["row", "column", "grid"], default="row", help="single-direction sprites only")
    ap.add_argument("--sheet-cols", type=int, default=0)
    ap.add_argument("--sheet-pad", type=int, default=0)
    ap.add_argument("--sheet-anchor", choices=["bottom-center", "center", "top-left"], default="bottom-center")
    ap.add_argument("--sidecar-json", action="store_true", help="EXTRA: write NAME.json (frame grid, offsets, fps, font metrics) beside each PNG")
    ap.add_argument("--no-frames", action="store_true", help="do NOT extract individual frames/glyphs into NAME/ folders")
    ap.add_argument("--folders-always", action="store_true", help="also make a NAME/ folder for single-image files")
    ap.add_argument("--previews", action="store_true", help="EXTRA: also write animated GIF previews beside the sheet")
    ap.add_argument("--force", action="store_true", help="reconvert even if the output PNG already exists and is newer than the source")
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)


def build_dat_parser():
    ap = argparse.ArgumentParser(prog="FRM-PNG-WIN.py dat", description="FRM-PNG-WIN: Fallout DAT1/DAT2 tools - list, extract, extract+convert.")
    sub = ap.add_subparsers(dest="cmd", required=True)

    def filt(p):
        p.add_argument("--search", default="", help="only entries whose internal path contains this text")
        p.add_argument("--regex", action="store_true", help="treat --search as a regular expression")
        p.add_argument("--ext", default="", help="only these extensions, e.g. frm,fr0,rix")

    def conv(p):
        p.add_argument("--out", required=True, help="folder to extract into (exact internal folder structure is kept)")
        p.add_argument("--conflicts", choices=["override", "keep", "rename"], default="override",
                       help="same path in several archives: later/higher-priority wins (default), keep first, or keep both")
        p.add_argument("--convert", metavar="PNG_DIR", help="after extracting, convert everything supported to PNG into PNG_DIR")
        filt(p); add_convert_options(p)

    l = sub.add_parser("list", help="show the contents of one or more DATs")
    l.add_argument("archives", nargs="+"); filt(l); l.add_argument("--csv", help="also write the listing to this CSV file")
    x = sub.add_parser("extract", help="extract one or more DATs (A/B/C workflows)")
    x.add_argument("archives", nargs="+"); conv(x)
    i = sub.add_parser("install", help="Workflow D: find master.dat/critter.dat/patches (+ data/ folder) in a game folder")
    i.add_argument("folder"); conv(i)
    return ap


def dat_main(argv):
    a = build_dat_parser().parse_args(argv)
    if a.cmd == "install":
        dats, loose = discover_install(a.folder)
        paths = [str(p) for p in dats] + ([str(loose)] if loose else [])
        if not paths:
            print(f"No .dat archives found in {a.folder}", file=sys.stderr); return 2
        print("Found:", *[Path(p).name + ("/" if Path(p).is_dir() else "") for p in paths])
    else:
        paths = a.archives
    archives, bad = open_archives(paths)
    for p, err in bad:
        print(f"CANNOT OPEN {p}: {err}", file=sys.stderr)
    if not archives:
        return 2
    exts = parse_exts(a.ext)
    for ar in archives:
        print(f"{ar.path.name}: {ar.format}, {len(ar.entries)} entries" + (f"  warnings: {len(ar.warnings)}" if ar.warnings else ""))
    if a.cmd == "list":
        shown = collect_items(archives, a.search, exts, None, a.regex)
        for ar, e in shown:
            print(f"{e.size:>10} {e.packed:>10} {e.method:<12} {ar.path.name}:{e.path}")
        print(f"{len(shown)} entries shown ({sum(e.size for _, e in shown) / 1e6:.1f} MB unpacked)")
        if a.csv:
            with open(a.csv, "w", newline="", encoding="utf-8") as f:
                w = csv.writer(f); w.writerow(["archive", "path", "size", "packed", "method"])
                for ar, e in shown:
                    w.writerow([ar.path.name, e.path, e.size, e.packed, e.method])
        return 0
    rep, code = extract_and_convert(archives, a.out, a.convert, a.search, exts, None, a.regex, a.conflicts,
                                    convert_namespace(a.out, a.convert or "", a) if a.convert else None, console_progress)
    print()
    s = rep["summary"]
    rpt = str(a.out).rstrip("/\\") + "_reports"
    print(f"EXTRACTION: extracted={s.get('extracted', 0)} failed={s.get('failed', 0)} unsupported={s.get('unsupported', 0)} "
          f"overridden={s.get('overridden', 0)} skipped={s.get('skipped', 0)}  ({s.get('bytes', 0) / 1e6:.1f} MB)  report: {rpt}")
    for r in rep["results"]:
        if r.get("status") in ("failed", "unsupported"):
            print(f"  {r['status'].upper()}: {r['archive']}:{r['internal_path']}  {r.get('error', '')}")
    return code or 0


# ----------------------------------------------------------------------------- asset browser GUI (tkinter)
def launch_gui():
    """Desktop asset browser: open DATs / a Fallout folder, search + filter, preview, extract and convert."""
    import queue, threading
    import tkinter as tk
    from tkinter import filedialog, messagebox, ttk
    from PIL import ImageTk

    model = AssetModel()
    root = tk.Tk()
    root.title("FRM-PNG-WIN - Fallout DAT extractor / FRM previewer / PNG converter")
    root.geometry("1250x760")
    q, state = queue.Queue(), dict(cancel=None, shown=[], busy=False, photo=None)

    top = ttk.Frame(root); top.pack(fill="x", padx=8, pady=6)
    ttk.Button(top, text="Open DAT file(s)...", command=lambda: open_dats()).pack(side="left")
    ttk.Button(top, text="Open Fallout folder...", command=lambda: open_install()).pack(side="left", padx=6)
    ttk.Button(top, text="Convert an already-extracted folder...", command=lambda: convert_folder()).pack(side="left")
    info = ttk.Label(top, text="No archive loaded"); info.pack(side="left", padx=12)

    flt = ttk.Frame(root); flt.pack(fill="x", padx=8)
    ttk.Label(flt, text="Search path:").pack(side="left")
    search_var, ext_var, rx_var = tk.StringVar(), tk.StringVar(value="All"), tk.BooleanVar()
    ent = ttk.Entry(flt, textvariable=search_var, width=40); ent.pack(side="left", padx=4)
    ttk.Label(flt, text="Type:").pack(side="left", padx=(10, 0))
    ext_box = ttk.Combobox(flt, textvariable=ext_var, width=16, state="readonly", values=["All"]); ext_box.pack(side="left", padx=4)
    ttk.Checkbutton(flt, text="regex", variable=rx_var, command=lambda: refresh()).pack(side="left")
    count_lbl = ttk.Label(flt, text=""); count_lbl.pack(side="left", padx=12)

    mid = ttk.PanedWindow(root, orient="horizontal"); mid.pack(fill="both", expand=True, padx=8, pady=6)
    left = ttk.Frame(mid); mid.add(left, weight=4)
    cols = ("path", "size", "packed", "method", "archive")
    tree = ttk.Treeview(left, columns=cols, show="headings", selectmode="extended")
    for c, w in zip(cols, (480, 80, 80, 90, 110)):
        tree.heading(c, text=c); tree.column(c, width=w, anchor="w" if c in ("path", "archive") else "e")
    sb = ttk.Scrollbar(left, orient="vertical", command=tree.yview); tree.configure(yscrollcommand=sb.set)
    tree.pack(side="left", fill="both", expand=True); sb.pack(side="right", fill="y")
    right = ttk.Frame(mid); mid.add(right, weight=2)
    prev_lbl = ttk.Label(right, text="Select a file to preview", anchor="center"); prev_lbl.pack(fill="both", expand=True)
    prev_info = ttk.Label(right, text="", wraplength=380, justify="left"); prev_info.pack(fill="x")

    bot = ttk.Frame(root); bot.pack(fill="x", padx=8, pady=4)
    out_var, png_var = tk.StringVar(), tk.StringVar()
    r1 = ttk.Frame(bot); r1.pack(fill="x", pady=2)
    ttk.Label(r1, text="Extract to:", width=12).pack(side="left"); ttk.Entry(r1, textvariable=out_var).pack(side="left", fill="x", expand=True)
    ttk.Button(r1, text="Browse...", command=lambda: out_var.set(filedialog.askdirectory() or out_var.get())).pack(side="left", padx=4)
    r2 = ttk.Frame(bot); r2.pack(fill="x", pady=2)
    ttk.Label(r2, text="PNG output:", width=12).pack(side="left"); ttk.Entry(r2, textvariable=png_var).pack(side="left", fill="x", expand=True)
    ttk.Button(r2, text="Browse...", command=lambda: png_var.set(filedialog.askdirectory() or png_var.get())).pack(side="left", padx=4)
    r3 = ttk.Frame(bot); r3.pack(fill="x", pady=4)
    btns = []
    for text, cmd in (("Extract selected", lambda: go(False, True)), ("Extract everything shown", lambda: go(False, False)),
                      ("Extract shown + convert to PNG", lambda: go(True, False)), ("Extract selected + convert to PNG", lambda: go(True, True))):
        b = ttk.Button(r3, text=text, command=cmd); b.pack(side="left", padx=3); btns.append(b)
    cancel_btn = ttk.Button(r3, text="Cancel", command=lambda: state["cancel"] and state["cancel"].set(), state="disabled"); cancel_btn.pack(side="right")
    bar = ttk.Progressbar(root, mode="determinate"); bar.pack(fill="x", padx=8)
    status = ttk.Label(root, text="Ready."); status.pack(fill="x", padx=8, pady=(2, 8))

    def post(kind, payload=None):
        q.put((kind, payload))

    def set_busy(b):
        state["busy"] = b
        for x in btns:
            x.configure(state="disabled" if b else "normal")
        cancel_btn.configure(state="normal" if b else "disabled")

    def load(paths):
        model.load(paths)
        for p, err in model.errors:
            messagebox.showwarning("Cannot open", f"{p}\n\n{err}")
        info.configure(text=f"{len(model.archives)} source(s): " + ", ".join(f"{a.path.name} ({a.format}, {len(a.entries)})" for a in model.archives))
        counts = model.ext_counts()
        ext_box.configure(values=["All"] + [f"{e} ({n})" for e, n in sorted(counts.items())])
        ext_var.set("All")
        refresh()

    def open_dats():
        ps = filedialog.askopenfilenames(title="Select Fallout DAT file(s)", filetypes=[("Fallout DAT", "*.dat *.DAT"), ("All files", "*.*")])
        if ps:
            load(ps)

    def open_install():
        d = filedialog.askdirectory(title="Select the Fallout installation folder")
        if not d:
            return
        dats, loose = discover_install(d)
        if not dats and not loose:
            messagebox.showinfo("Nothing found", "No .dat archives or data folder in that folder."); return
        load([str(p) for p in dats] + ([str(loose)] if loose else []))

    def current_filter():
        e = ext_var.get().split(" ")[0]
        return search_var.get(), e if e != "All" else None, rx_var.get()

    def refresh(*_):
        s, e, rx = current_filter()
        try:
            state["shown"] = model.filtered(s, e, rx)
        except re.error:
            return
        tree.delete(*tree.get_children())
        shown = state["shown"]
        count_lbl.configure(text=f"{len(shown)} of {len(model.items())} entries")

        def fill(i=0):
            for k in range(i, min(i + 1500, len(shown))):
                a, en = shown[k]
                tree.insert("", "end", iid=str(k), values=(en.path, en.size, en.packed, en.method, a.path.name))
            if i + 1500 < len(shown):
                root.after(10, fill, i + 1500)
        fill()

    search_var.trace_add("write", refresh)
    ext_box.bind("<<ComboboxSelected>>", refresh)

    def on_select(_=None):
        sel = tree.selection()
        if len(sel) != 1:
            return
        a, en = state["shown"][int(sel[0])]
        try:
            im, desc = model.preview(a, en)
        except Exception as ex:
            im, desc = None, f"preview failed: {ex}"
        prev_info.configure(text=f"{a.path.name}:{en.path}\n{desc}")
        if im is None:
            prev_lbl.configure(image="", text="(no preview)"); state["photo"] = None; return
        k = max(1, min(6, 380 // max(im.width, 1), 380 // max(im.height, 1)))
        im = im.resize((im.width * k, im.height * k), Image.NEAREST) if k > 1 else im
        state["photo"] = ImageTk.PhotoImage(im)
        prev_lbl.configure(image=state["photo"], text="")
    tree.bind("<<TreeviewSelect>>", on_select)

    def go(convert, selected_only):
        if state["busy"]:
            return
        if not model.archives:
            messagebox.showinfo("Nothing loaded", "Open a DAT file or Fallout folder first."); return
        out = out_var.get().strip()
        if not out:
            out = filedialog.askdirectory(title="Choose the folder to extract into") or ""
            out_var.set(out)
        if not out:
            return
        png = None
        if convert:
            png = png_var.get().strip() or filedialog.askdirectory(title="Choose the folder for the converted PNGs") or ""
            png_var.set(png)
            if not png:
                return
        if selected_only:
            sel = tree.selection()
            if not sel:
                messagebox.showinfo("Nothing selected", "Select one or more files first (Ctrl/Shift-click)."); return
            paths = {state["shown"][int(i)][1].path for i in sel}
            s, e, rx = "", None, False
        else:
            paths = None
            s, e, rx = current_filter()
        exts = {e} if e else None
        cancel = threading.Event(); state["cancel"] = cancel; set_busy(True)

        def work():
            try:
                rep, code = extract_and_convert(model.archives, out, png, s, exts, paths, rx, "override", None,
                                                lambda p: post("progress", p), cancel, lambda n, t: post("conv", (n, t)))
                sm = rep["summary"]
                msg = (f"Extracted {sm.get('extracted', 0)} files, {sm.get('failed', 0)} failed, {sm.get('unsupported', 0)} unsupported, "
                       f"{sm.get('overridden', 0)} overridden. Report: {out}_reports")
                if png:
                    msg += "  |  conversion finished" if code == 0 else f"  |  conversion stopped (code {code})"
                post("done", ("Cancelled. " if cancel.is_set() else "") + msg)
            except Exception as ex:
                post("done", f"ERROR: {ex!r}")
        threading.Thread(target=work, daemon=True).start()

    def convert_folder():
        src = filedialog.askdirectory(title="Select an already-extracted Fallout folder")
        if not src:
            return
        dst = filedialog.askdirectory(title="Select the output folder for PNGs")
        if not dst:
            return
        cancel = threading.Event(); state["cancel"] = cancel; set_busy(True)

        def work():
            try:
                ns = convert_namespace(src, dst); ns.progress_cb = lambda n, t: post("conv", (n, t)); ns.cancel = cancel
                code = run(ns)
                post("done", f"Conversion finished (code {code}). Reports: {dst}_reports")
            except Exception as ex:
                post("done", f"ERROR: {ex!r}")
        threading.Thread(target=work, daemon=True).start()

    def poll():
        try:
            while True:
                kind, p = q.get_nowait()
                if kind == "progress":
                    bar.configure(maximum=max(p["bytes_total"], 1), value=p["bytes_done"])
                    status.configure(text=f"Extracting {p['files_done']}/{p['files_total']} files  -  {p['bytes_done'] / 1e6:.1f}/{p['bytes_total'] / 1e6:.1f} MB  -  {p['current']}")
                elif kind == "conv":
                    bar.configure(maximum=max(p[1], 1), value=p[0]); status.configure(text=f"Converting {p[0]}/{p[1]} files")
                elif kind == "done":
                    set_busy(False); status.configure(text=p); messagebox.showinfo("Finished", p)
        except queue.Empty:
            pass
        root.after(100, poll)
    poll()
    root.mainloop()
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    main.gui = False
    if argv and argv[0] == "dat":
        return dat_main(argv[1:])
    if not argv:                                   # double-click: asset browser (falls back to folder pickers)
        try:
            import tkinter  # noqa: F401
            main.gui = True
            return launch_gui()
        except ImportError:
            argv = list(pick_folders())
    return run(build_parser().parse_args(argv))


main.gui = False


if __name__ == "__main__":
    import multiprocessing
    multiprocessing.freeze_support()
    code = 1
    try:
        code = main()
    except SystemExit as e:
        code = e.code
    except Exception:
        traceback.print_exc()
    if len(sys.argv) == 1 and not main.gui:         # only when double-clicked without arguments
        input("\nFinished. Press Enter to close...")
    sys.exit(code or 0)
