"""
phonon_studio.py  -  Phonon Studio Pro

The full-featured Phonon app (Gradium Phonon-31M English, Apache 2.0, 24 kHz, CPU only):
parts list, built-in player (skip 5/10/30s, seek bar, follow-along highlighting),
paste tools, part splitter, a serious text cleaner, CPU thread control and a benchmark.

Output names:  001.Default.2026-10-19.The_morning_the_river_froze.mp3
Launch it with phonon_pro.vbs / phonon_pro.bat (the .bat installs and downloads on first run).
"""
APP_NAME = 'Phonon Studio Pro'
APP_SLUG = 'phonon_pro'
SUBTITLE = '31M  ·  CPU only  ·  parts  ·  reader  ·  serious text cleaner'
TITLE_FONT = ('Segoe UI', 20, 'bold', 'roman')
TEXT_FONT = ('Georgia', 12)

DARK = dict(
    bg='#0a1514', surface='#10211f', surface2='#17302d', border='#245049',
    fg='#e3f6f3', muted='#80aaa4', accent='#2dd4bf', accent_hover='#5eead4',
    accent_fg='#03241f', text_bg='#081110', select='#14524c', hl='#14566a',
    ok='#86efac', err='#fb7185', warn='#fbbf24',
)
LIGHT = dict(
    bg='#eff7f6', surface='#ffffff', surface2='#dfeeec', border='#bcd9d4',
    fg='#0d2422', muted='#4f716d', accent='#0f766e', accent_hover='#115e59',
    accent_fg='#ffffff', text_bg='#fafefd', select='#c3ebe5', hl='#bfe9f2',
    ok='#15803d', err='#be123c', warn='#b45309',
)

import bisect
import importlib.util
import io
import json
import math
import os
import queue
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import threading
import time
import traceback
import unicodedata
import wave
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, font as tkfont

ROOT = Path(__file__).resolve().parent
SETTINGS_FILE = ROOT / f'{APP_SLUG}_settings.json'
SESSION_FILE = ROOT / f'{APP_SLUG}_session.json'
NO_WINDOW = getattr(subprocess, 'CREATE_NO_WINDOW', 0)


def find_ffmpeg():
    local = ROOT / 'ffmpeg.exe'
    if local.exists():
        return str(local)
    return shutil.which('ffmpeg')


def fmt_time(sec):
    sec = max(0, int(sec))
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f'{h}:{m:02d}:{s:02d}' if h else f'{m:02d}:{s:02d}'


def unique_path(path):
    path = Path(path)
    if not path.exists():
        return path
    for i in range(2, 1000):
        c = path.with_name(f'{path.stem} ({i}){path.suffix}')
        if not c.exists():
            return c
    return path


def reveal_in_folder(path):
    path = Path(path)
    try:
        if sys.platform.startswith('win'):
            subprocess.Popen(['explorer', '/select,', os.path.normpath(str(path))])
        elif sys.platform == 'darwin':
            subprocess.Popen(['open', '-R', str(path)])
        else:
            subprocess.Popen(['xdg-open', str(path.parent)])
    except Exception:
        pass


# ============================================================
#  TEXT CLEANER v2
# ============================================================
LIGATURES = {'\ufb00': 'ff', '\ufb01': 'fi', '\ufb02': 'fl', '\ufb03': 'ffi',
             '\ufb04': 'ffl', '\ufb05': 'ft', '\ufb06': 'st'}

SMART = {
    '\u2018': "'", '\u2019': "'", '\u201a': "'", '\u201b': "'",
    '\u201c': '"', '\u201d': '"', '\u201e': '"', '\u201f': '"',
    '\u2032': "'", '\u2033': '"',
    '\u2013': '-', '\u2014': ' -- ', '\u2015': ' -- ', '\u2026': '...',
    '\u203c': '!!', '\u2049': '?!',
    '\u00a0': ' ', '\u2002': ' ', '\u2003': ' ', '\u2009': ' ', '\u200a': ' ',
    '\u202f': ' ', '\u3000': ' ',
    '\u200b': '', '\u200c': '', '\u2060': '', '\ufeff': '', '\u00ad': '',
    '\u00b0': ' degrees ',
    '\u2022': '. ', '\u25cf': '. ', '\u25aa': '. ', '\u00b7': ' ',
}

# Anything in these blocks is pictographic / decorative: always removed.
JUNK_RANGES = (
    (0x1F000, 0x1FAFF),   # all emoji, flags, pictographs, symbols
    (0x2190, 0x21FF),     # arrows
    (0x2300, 0x23FF),     # misc technical (watch, hourglass, play buttons...)
    (0x2600, 0x27BF),     # misc symbols + dingbats (stars, checks, hearts...)
    (0x2900, 0x297F),     # supplemental arrows
    (0x2B00, 0x2BFF),     # misc symbols and arrows (star, squares...)
    (0xFE00, 0xFE0F),     # variation selectors (emoji style)
    (0xE0000, 0xE01EF),   # tag characters + variation selectors supplement
)
JUNK_SINGLE = {0x200D, 0x20E3, 0x00A9, 0x00AE, 0x2122, 0x2139, 0x24C2,
               0x3030, 0x303D, 0x3297, 0x3299}
JUNK_CATEGORIES = {'So', 'Sk', 'Cs', 'Co', 'Cn', 'Cc', 'Cf', 'Me'}


def is_junk(ch):
    if ch in '\n\t ':
        return False
    o = ord(ch)
    if o in JUNK_SINGLE:
        return True
    for lo, hi in JUNK_RANGES:
        if lo <= o <= hi:
            return True
    return unicodedata.category(ch) in JUNK_CATEGORIES


_HR = re.compile(r'^\s*(?:[-*_=~]\s*){3,}$')
_HEAD = re.compile(r'^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$')
_QUOTE = re.compile(r'^\s*(?:>\s?)+')
_BULLET = re.compile(r'^\s*[-*+\u2022\u25cf\u25aa\u25e6\u2023\u2219\u25a0\u25ba]\s+(.*\S)\s*$')
_ENDERS = '.!?:;"\')\u201d\u2026'


def _end_sentence(s):
    s = s.strip()
    if s and s[-1] not in _ENDERS:
        s += '.'
    return s


def _strip_leading_junk(s):
    i = 0
    while i < len(s) and (is_junk(s[i]) or s[i].isspace()):
        i += 1
    return s[i:]


def _structure(text):
    """Headings / bullets / emoji-bullets become standalone sentences."""
    out = []
    for line in text.split('\n'):
        s = line.strip()
        if not s:
            out.append('')
            continue
        if _HR.match(s):
            out.append('')
            continue
        m = _HEAD.match(line)
        if m:
            out += ['', _end_sentence(_strip_leading_junk(m.group(1))), '']
            continue
        line = _QUOTE.sub('', line)
        s = line.strip()
        m = _BULLET.match(line)
        if m:
            out.append(_end_sentence(_strip_leading_junk(m.group(1))))
            continue
        if s and is_junk(s[0]):          # line starts with an emoji/symbol
            item = _strip_leading_junk(s)
            out.append(_end_sentence(item) if item else '')
            continue
        out.append(line)
    return '\n'.join(out)




CLEAN_DEFAULTS = dict(
    furniture=True,    # page numbers, "page 3/15", running headers/footers
    markdown=True,     # # headings, **bold**, bullets, links, html tags
    urls=True,         # bare links
    citations=True,    # [12] and 【4:0†source】
    caps=True,         # ALL CAPS lines -> Title Case, Chapter XII -> Chapter 12
    abbrev=True,       # e.g. -> for example, etc. -> et cetera, vs. -> versus
    ampersand=True,    # & -> and
    reflow=True,       # join hard-wrapped lines into flowing paragraphs
    paragraphs=True,   # detect paragraph/heading breaks in wrapped text
    finish=True,       # end headings/paragraphs with a full stop so the voice pauses
)
CLEAN_LABELS = [
    ('furniture', 'Remove page numbers ("page 3/15", bare numbers) and repeating headers/footers'),
    ('markdown', 'Strip markdown: # headings, **bold**, bullets, links, HTML tags'),
    ('urls', 'Remove web links'),
    ('citations', 'Remove citation marks like [12]'),
    ('caps', 'Fix ALL CAPS lines to Title Case, Chapter XII to Chapter 12'),
    ('abbrev', 'Spell out e.g.  i.e.  etc.  vs.'),
    ('ampersand', 'Read & as "and"'),
    ('reflow', 'Join broken lines into flowing paragraphs (and fix hyphenated line ends)'),
    ('paragraphs', 'Detect paragraph and heading breaks inside wrapped text'),
    ('finish', 'End headings and paragraphs with a full stop so the voice pauses'),
]

_PAGE_LINE = re.compile(r'^\s*(?:page|pg\.?|p\.)\s*\d+(?:\s*(?:/|of)\s*\d+)?\s*$', re.I)
_FRAC_LINE = re.compile(r'^\s*\d{1,4}\s*(?:/|of)\s*\d{1,4}\s*$', re.I)
_NUM_LINE = re.compile(r'^\s*[-\u2013\u2014\[(]?\s*\d{1,3}\s*[-\u2013\u2014\])]?\s*$')
_ROMAN_VALID = re.compile(r'^M{0,4}(CM|CD|D?C{0,3})(XC|XL|L?X{0,3})(IX|IV|V?I{0,3})$')
_ROMAN_LOWER = {'i', 'ii', 'iii', 'iv', 'v', 'vi', 'vii', 'viii', 'ix', 'x', 'xi', 'xii',
                'xiii', 'xiv', 'xv', 'xvi', 'xvii', 'xviii', 'xix', 'xx'}
_ROMAN_VALS = {'I': 1, 'V': 5, 'X': 10, 'L': 50, 'C': 100, 'D': 500, 'M': 1000}
_CHAPTER_WORDS = r'(?:chapter|part|book|volume|section|act|appendix)'


def roman_to_int(s):
    if not s or not _ROMAN_VALID.match(s):
        return None
    total = 0
    for i, ch in enumerate(s):
        v = _ROMAN_VALS[ch]
        total += -v if i + 1 < len(s) and _ROMAN_VALS[s[i + 1]] > v else v
    return total


def _strip_furniture(text, rep):
    removed = 0
    text, n = re.subn(r'(?i)\b(?:this is )?page\s+\d+\s*(?:/|of)\s*\d+\b[.,]?', '', text)
    removed += n
    lines = text.split('\n')
    keep = []
    for ln in lines:
        s = ln.strip()
        if s and (_PAGE_LINE.match(s) or _FRAC_LINE.match(s) or _NUM_LINE.match(s)
                  or (s.isupper() and len(s) <= 6 and roman_to_int(s) is not None)
                  or (len(s) >= 2 and s in _ROMAN_LOWER)):
            removed += 1
            continue
        keep.append(ln)
    lines = keep
    nonblank = [l.strip() for l in lines if l.strip()]
    if len(nonblank) >= 40:                       # repeating running headers / footers
        norm = lambda s: re.sub(r'\d+', '0', s.lower())
        counts = {}
        for s in nonblank:
            if 3 <= len(s) <= 80:
                counts[norm(s)] = counts.get(norm(s), 0) + 1
        drop = set()
        for s in nonblank:
            k = norm(s)
            if (counts.get(k, 0) >= 3 and 3 <= len(s) <= 80
                    and s[-1] not in '.!?,:;"\'\u201d)'
                    and (len(s.split()) >= 2 or s.isupper())):
                drop.add(k)
        if drop:
            kept = []
            for l in lines:
                if l.strip() and norm(l.strip()) in drop:
                    removed += 1
                else:
                    kept.append(l)
            lines = kept
    rep['furniture'] = rep.get('furniture', 0) + removed
    return '\n'.join(lines)


def _titlecase_line(s):
    out, prev = [], ''
    for m in re.finditer(r"[A-Za-z]+(?:'[A-Za-z]+)?|[^A-Za-z]+", s):
        tok = m.group(0)
        if tok[0].isalpha():
            if _ROMAN_VALID.match(tok) and re.fullmatch(_CHAPTER_WORDS, prev, re.I):
                out.append(tok)                       # keep, converted to digits later
            else:
                out.append(tok.capitalize())
            prev = tok
        else:
            out.append(tok)
    return ''.join(out)


def _fix_caps(text):
    lines = []
    for ln in text.split('\n'):
        letters = [c for c in ln if c.isalpha()]
        words = re.findall(r"[A-Za-z']+", ln)
        if (letters and ln.upper() == ln and ln.lower() != ln
                and (len(words) >= 2 or len(letters) >= 6)):
            ln = _titlecase_line(ln)
        lines.append(ln)
    text = '\n'.join(lines)

    def roman(m):
        n = roman_to_int(m.group(2))
        return f'{m.group(1)} {n}' if n else m.group(0)
    return re.sub(rf'(?i:\b({_CHAPTER_WORDS}))\s+([IVXLCDM]{{1,8}})\b', roman, text)


def _is_break(prev, nxt, med):
    if len(prev) >= 0.7 * med or not nxt:
        return False
    last = prev[-1]
    if last in ',;:-\u2013':
        return False
    if last in '.!?"\'\u201d)\u2026':
        return nxt[0].isupper() or nxt[0] in '"\'(['
    return len(prev) <= 70 and (nxt[0].isupper() or nxt[0].isdigit())   # heading-like


def _join_lines(lines):
    joined = ''
    for ln in lines:
        if re.search(r'[a-z]-$', joined) and ln[:1].islower():
            joined = joined[:-1] + ln                  # un-hyphenate
        else:
            joined = (joined + ' ' + ln).strip()
    return re.sub(r' {2,}', ' ', joined).strip()


def _paragraphs(text, o, finish):
    blocks = re.split(r'\n\s*\n', text)
    lens = [len(l.strip()) for b in blocks for l in b.split('\n') if len(l.strip()) > 25]
    med = statistics.median(lens) if len(lens) >= 6 else 0
    unwrapped = med > 115                              # lines are already whole paragraphs
    paras = []
    for b in blocks:
        lines = [l.strip() for l in b.split('\n') if l.strip()]
        if not lines:
            continue
        if not o['reflow']:
            paras.append('\n'.join(lines))
            continue
        cur, groups = [], []
        for ln in lines:
            if cur and o['paragraphs'] and (unwrapped or (med and _is_break(cur[-1], ln, med))):
                groups.append(cur)
                cur = []
            cur.append(ln)
        groups.append(cur)
        paras += [_join_lines(g) for g in groups]
    if finish:
        paras = [p + '.' if p and p[-1].isalnum() else p for p in paras]
    return paras


def apply_replacements(text, spec):
    for raw in (spec or '').split('\n'):
        raw = raw.strip()
        if not raw or raw.startswith('#') or '=>' not in raw:
            continue
        find, rep = (x.strip() for x in raw.split('=>', 1))
        if not find:
            continue
        pat = re.escape(find)
        if find[0].isalnum() and find[-1].isalnum():
            pat = rf'\b{pat}\b'
        text = re.sub(pat, lambda m, r=rep: r, text, flags=re.I)
    return text


def clean_text(text, opts=None, finish=True, report=None, repl=None):
    o = dict(CLEAN_DEFAULTS)
    o.update(opts or {})
    rep = report if report is not None else {}
    if not text:
        return ''
    text = unicodedata.normalize('NFC', text)
    text = text.replace('\r\n', '\n').replace('\r', '\n').replace('\t', ' ').replace('\f', '\n\n')
    for k, v in LIGATURES.items():
        text = text.replace(k, v)

    if o['furniture']:
        text = _strip_furniture(text, rep)
    if o['markdown']:
        text = _structure(text)
        text = re.sub(r'!\[[^\]]*\]\([^)]*\)', '', text)
        text = re.sub(r'\[([^\]]+)\]\([^)]*\)', r'\1', text)
        text = re.sub(r'</?[A-Za-z][^>]{0,60}>', ' ', text)
        text = re.sub(r'\*+|~~', '', text)
        text = re.sub(r'(?<![A-Za-z0-9])_+|_+(?![A-Za-z0-9])', '', text)
        text = re.sub(r'[|~]', ' ', text)
    if o['urls']:
        text, n = re.subn(r'(?:https?://|www\.)\S+', '', text)
        rep['urls'] = rep.get('urls', 0) + n
    if o['citations']:
        text = re.sub(r'\u3010[^\u3011]*\u3011', '', text)
        text = re.sub(r'\[\d{1,3}\]', '', text)

    for k, v in SMART.items():
        text = text.replace(k, v)
    if o['ampersand']:
        text = re.sub(r'\s&\s', ' and ', text)
    if o['abbrev']:
        text = re.sub(r'(?i)\be\.g\.,?', 'for example,', text)
        text = re.sub(r'(?i)\bi\.e\.,?', 'that is,', text)
        text = re.sub(r'\b(?i:etc)\.(?=\s+[A-Z"\'(]|\s*$)', 'et cetera.', text)
        text = re.sub(r'(?i)\betc\.', 'et cetera', text)
        text = re.sub(r'(?i)\bvs\.?(?=\s)', 'versus', text)

    junk = 0
    chars = []
    for ch in text:
        if is_junk(ch):
            junk += 1
            chars.append(' ')
        else:
            chars.append(ch)
    text = ''.join(chars)
    rep['symbols'] = rep.get('symbols', 0) + junk

    text = '\n'.join(re.sub(r'[ ]{2,}', ' ', l).strip() for l in text.split('\n'))

    text = re.sub(r'[ ]+([,.;:!?])', r'\1', text)
    text = re.sub(r'([,;:!?])(?=[A-Za-z])', r'\1 ', text)
    text = re.sub(r'(?<=[a-z]{2})\.(?=[A-Z][a-z])', '. ', text)
    text = re.sub(r'([.!?,])\1{3,}', r'\1\1\1', text)
    text = re.sub(r'([.!?])(?:\s+\.)+(?=\s|$)', r'\1', text)
    text = re.sub(r'\s*--\s*', ' -- ', text)
    text = re.sub(r'(?m)^ -- ', '-- ', text)

    if o['caps']:
        text = _fix_caps(text)

    paras = _paragraphs(text, o, finish and o['finish'])
    text = '\n\n'.join(paras).strip()
    if repl:
        text = apply_replacements(text, repl)
    return text


def report_text(rep):
    bits = []
    if rep.get('symbols'):
        bits.append(f"{rep['symbols']} emoji/symbols")
    if rep.get('furniture'):
        bits.append(f"{rep['furniture']} page-number/header lines")
    if rep.get('urls'):
        bits.append(f"{rep['urls']} links")
    return 'Cleaned.' + (' Removed ' + ', '.join(bits) + '.' if bits else '')


def estimate_seconds(text, wpm=160):
    return len(re.findall(r'\S+', text)) / wpm * 60


def start_slug(text, max_words=7, max_len=40):
    out = ''
    for w in re.findall(r"[^\W_]+", text[:300])[:max_words]:
        cand = f'{out}_{w}' if out else w
        if len(cand) > max_len:
            if not out:
                out = w[:max_len]
            break
        out = cand
    return out or 'untitled'


def next_number(folder):
    top = 0
    try:
        for p in Path(folder).iterdir():
            m = re.match(r'(\d+)\.', p.name)
            if m:
                top = max(top, int(m.group(1)))
    except OSError:
        pass
    return top + 1


# ============================================================
#  SENTENCE CHUNKER  (progress, ETA, cancel, follow-along map)
# ============================================================
ABBREV = {'mr', 'mrs', 'ms', 'dr', 'prof', 'sr', 'jr', 'st', 'vs', 'etc', 'inc', 'ltd', 'co',
          'no', 'fig', 'vol', 'approx', 'dept', 'est', 'mt', 'gen', 'col', 'sgt', 'capt',
          'lt', 'rev', 'hon', 'e.g', 'i.e'}


def split_sentences(par):
    """Return (start, end) spans of sentences inside one paragraph string."""
    spans, start = [], 0
    for m in re.finditer(r'[.!?\u2026]+["\')\]\u201d]*(?=\s)', par):
        end = m.end()
        nxt = par[end:].lstrip()[:1]
        if not nxt or not (nxt.isupper() or nxt.isdigit() or nxt in '"\'([\u201c'):
            continue
        tok = re.findall(r'[A-Za-z.]+$', par[:m.start()])
        if tok and '?' not in m.group(0) and '!' not in m.group(0):
            t = tok[0].strip('.').lower()
            if t in ABBREV or (len(t) == 1 and tok[0][0].isupper()):
                continue
        spans.append((start, end))
        start = end
    if start < len(par.rstrip()):
        spans.append((start, len(par.rstrip())))
    return [(a, b) for a, b in spans if par[a:b].strip()]


def _split_long(text, a, b, max_chars):
    out = []
    while b - a > max_chars:
        window = text[a:a + max_chars]
        cut = max(window.rfind(', '), window.rfind('; '), window.rfind(': '))
        if cut < max_chars * 0.4:
            cut = window.rfind(' ')
        if cut < max_chars * 0.2:
            cut = max_chars - 1
        out.append((a, a + cut + 1))
        a += cut + 1
    if b > a:
        out.append((a, b))
    return out


@dataclass
class Chunk:
    a: int
    b: int
    text: str
    para_end: bool


def chunk_text(text, max_chars=400):
    chunks = []
    for pm in re.finditer(r'(?:[^\n]|\n(?!\s*\n))+', text):
        raw = pm.group(0)
        lead = len(raw) - len(raw.lstrip())
        para = raw.strip()
        if not para:
            continue
        base = pm.start() + lead
        atoms = []
        for a, b in split_sentences(para):
            if b - a > max_chars:
                atoms += _split_long(text, base + a, base + b, max_chars)
            else:
                atoms.append((base + a, base + b))
        cur_a = cur_b = None
        para_chunks = []
        for a, b in atoms:
            if cur_a is None:
                cur_a, cur_b = a, b
            elif b - cur_a > max_chars:
                para_chunks.append((cur_a, cur_b))
                cur_a, cur_b = a, b
            else:
                cur_b = b
        if cur_a is not None:
            para_chunks.append((cur_a, cur_b))
        for i, (a, b) in enumerate(para_chunks):
            t = re.sub(r'\s+', ' ', text[a:b]).strip()
            if t:
                chunks.append(Chunk(a, b, t, i == len(para_chunks) - 1))
    return chunks


# ============================================================
#  PART SPLITTER  (long pastes -> audiobook-sized parts)
# ============================================================
CHAPTER_RE = re.compile(r'^\s*(?:chapter|part|book|section|prologue|epilogue|introduction|'
                        r'preface|appendix)\b.{0,70}$', re.I)


def _wc(s):
    return len(s.split())


def _pack(paras, max_words):
    pieces = []
    for p in paras:                                     # break oversize paragraphs
        if _wc(p) <= max_words:
            pieces.append(p)
            continue
        buf, n = [], 0
        for a, b in split_sentences(p):
            s = p[a:b].strip()
            if buf and n + _wc(s) > max_words:
                pieces.append(' '.join(buf))
                buf, n = [], 0
            buf.append(s)
            n += _wc(s)
        if buf:
            pieces.append(' '.join(buf))
    total = sum(_wc(p) for p in pieces)
    k = max(1, math.ceil(total / max_words))
    target = total / k
    out, buf, n = [], [], 0
    for p in pieces:
        w = _wc(p)
        if buf and n + w / 2 > target and len(out) < k - 1:
            out.append(buf)
            buf, n = [], 0
        buf.append(p)
        n += w
    if buf:
        out.append(buf)
    return ['\n\n'.join(g) for g in out]


def split_parts(text, max_words=1200, by_chapter=False):
    paras = [p.strip() for p in re.split(r'\n\s*\n', text.strip()) if p.strip()]
    if not paras:
        return []
    sections = [paras]
    if by_chapter:
        sections, cur = [], []
        for p in paras:
            if CHAPTER_RE.match(p) and cur:
                sections.append(cur)
                cur = []
            cur.append(p)
        if cur:
            sections.append(cur)
    out = []
    for sec in sections:
        out += _pack(sec, max_words)
    return out


# ============================================================
#  AUDIO FILE HELPERS
# ============================================================
def load_pcm_file(path, ffmpeg=None):
    """Decode wav/mp3 to (mono int16 bytes, sample_rate)."""
    path = str(path)
    if path.lower().endswith('.wav'):
        try:
            with wave.open(path, 'rb') as w:
                if w.getsampwidth() == 2 and w.getnchannels() == 1:
                    return w.readframes(w.getnframes()), w.getframerate()
        except Exception:
            pass
    try:
        import soundfile as sf
        data, sr = sf.read(path, dtype='int16', always_2d=True)
        if data.shape[1] > 1:
            data = data.mean(axis=1).astype('int16')
        else:
            data = data[:, 0]
        return data.tobytes(), int(sr)
    except Exception as e:
        err = e
    if ffmpeg:
        sr = 24000
        p = subprocess.run([ffmpeg, '-v', 'error', '-i', path, '-f', 's16le', '-ac', '1',
                            '-ar', str(sr), '-'], capture_output=True, creationflags=NO_WINDOW)
        if p.returncode == 0 and p.stdout:
            return p.stdout, sr
    raise RuntimeError(f'Could not decode {Path(path).name}: {err}')


def write_wav(path, pcm, sr):
    with wave.open(str(path), 'wb') as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(sr)
        w.writeframes(pcm)


# ============================================================
#  PLAYER  (own seek logic: works the same for mp3 and wav)
# ============================================================
class Player:
    def __init__(self):
        self.pg = None
        self.pcm = b''
        self.sr = 22050
        self.duration = 0.0
        self.state = 'stopped'          # stopped | playing | paused
        self.base = 0.0
        self._acc = 0.0
        self._t0 = 0.0
        self.volume = 0.9
        self.sound = None
        self.path = None

    def _init_mixer(self, sr):
        if self.pg is None:
            os.environ.setdefault('PYGAME_HIDE_SUPPORT_PROMPT', '1')
            import pygame
            self.pg = pygame
        m = self.pg.mixer.get_init()
        if not m or m[0] != sr or m[2] != 1:
            self.pg.mixer.quit()
            self.pg.mixer.init(frequency=sr, size=-16, channels=1, buffer=2048,
                               allowedchanges=0)

    @property
    def loaded(self):
        return bool(self.pcm)

    def load(self, pcm, sr, path):
        self.stop()
        self._init_mixer(sr)
        self.pcm, self.sr, self.path = pcm, sr, str(path)
        self.duration = len(pcm) / 2 / sr
        self.base = 0.0

    def _start(self, pos):
        pos = max(0.0, min(pos, max(0.0, self.duration - 0.05)))
        off = int(pos * self.sr) * 2
        snd = self.pg.mixer.Sound(buffer=memoryview(self.pcm)[off:])
        ch = self.pg.mixer.Channel(0)
        ch.set_volume(self.volume)
        ch.play(snd)
        self.sound = snd
        self.base, self._acc, self._t0 = pos, 0.0, time.monotonic()
        self.state = 'playing'

    def play(self, pos=None):
        if not self.loaded:
            return
        self._start(self.base if pos is None else pos)

    def pause(self):
        if self.state == 'playing':
            self.pg.mixer.Channel(0).pause()
            self._acc += time.monotonic() - self._t0
            self.state = 'paused'

    def resume(self):
        if self.state == 'paused':
            self.pg.mixer.Channel(0).unpause()
            self._t0 = time.monotonic()
            self.state = 'playing'

    def toggle(self):
        if self.state == 'playing':
            self.pause()
        elif self.state == 'paused':
            self.resume()
        else:
            self.play()

    def position(self):
        if self.state == 'playing':
            p = self.base + self._acc + (time.monotonic() - self._t0)
        else:
            p = self.base + self._acc
        return max(0.0, min(p, self.duration))

    def seek(self, pos):
        if not self.loaded:
            return
        pos = max(0.0, min(pos, self.duration))
        if self.state == 'playing':
            self._start(pos)
        elif self.state == 'paused':
            self._start(pos)
            self.pause()
        else:
            self.base, self._acc = pos, 0.0

    def skip(self, delta):
        self.seek(self.position() + delta)

    def stop(self):
        if self.pg is not None and self.pg.mixer.get_init():
            try:
                self.pg.mixer.Channel(0).stop()
            except Exception:
                pass
        self.state = 'stopped'
        self.base, self._acc = 0.0, 0.0

    def unload(self):
        self.stop()
        self.pcm, self.path, self.sound = b'', None, None
        self.duration = 0.0
        self.base = self._acc = 0.0

    def set_volume(self, v):
        self.volume = max(0.0, min(1.0, v))
        if self.pg is not None and self.pg.mixer.get_init():
            try:
                self.pg.mixer.Channel(0).set_volume(self.volume)
            except Exception:
                pass

    def poll_ended(self):
        if self.state == 'playing' and not self.pg.mixer.Channel(0).get_busy():
            self.state = 'stopped'
            self.base, self._acc = 0.0, 0.0
            return True
        return False

# ============================================================
#  THEME HELPERS
# ============================================================
def system_prefers_dark():
    try:
        import winreg
        key = winreg.OpenKey(
            winreg.HKEY_CURRENT_USER,
            r'Software\Microsoft\Windows\CurrentVersion\Themes\Personalize')
        return winreg.QueryValueEx(key, 'AppsUseLightTheme')[0] == 0
    except Exception:
        return True


# ============================================================
#  MODELS
# ============================================================
class Cancelled(Exception):
    pass


class Part:
    _n = 1

    def __init__(self, text=''):
        self.uid = f'p{Part._n}'
        Part._n += 1
        self.text = text
        self.state = 'idle'            # idle | queued | generating | done | error
        self.audio = None              # Path of generated file
        self.number = None             # running number kept when regenerating
        self.error = ''
        self.progress = 0.0
        self.eta = ''
        self.map = []                  # follow-along: (t0, t1, a, b)
        self.starts = []
        self.map_text = None
        self.duration = 0.0
        self.job = None

    @property
    def map_valid(self):
        return bool(self.map) and self.map_text == self.text


class Job:
    def __init__(self, part, text, voice, speed, mp3):
        self.part, self.text, self.voice = part, text, voice
        self.speed, self.mp3 = speed, mp3
        self.slug = start_slug(text)
        self.cancel = threading.Event()


# ============================================================
#  APP
# ============================================================
class Studio(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_NAME)
        self.geometry('1180x860')
        self.minsize(980, 700)

        self.cfg = self._load_cfg()
        self.ffmpeg = find_ffmpeg()
        self.out_dir = Path(self.cfg.get('output') or (ROOT / 'output'))
        self.parts = []
        self.sel = None
        self.player = Player()
        self.player_part = None
        self.jobs_q = queue.Queue()
        self.ui_q = queue.Queue()
        self.pending = 0
        self.active_job = None
        self._save_after = None
        self._dragging = False
        self._hl_idx = None
        self._loading_audio = False
        self._trash = []                 # last deleted batch, for Undo
        self._trash_after = None
        self._tot_after = None
        self._batch_total = 0
        self._batch_done = 0
        self._merging = False
        self._find_win = None

        theme = self.cfg.get('theme', 'light')               # light by default
        self.dark = theme == 'dark'
        self.mode = self.cfg.get('mode', 'parts')

        self._make_fonts()
        try:
            self.f_text.configure(size=int(self.cfg.get('text_size', TEXT_FONT[1])))
        except (TypeError, ValueError, tk.TclError):
            pass
        self.style = ttk.Style(self)
        self.style.theme_use('clam')
        self.backend = Backend(self)

        self.speed = tk.DoubleVar(value=float(self.cfg.get('speed', 1.0)))
        self.status = tk.StringVar(value='Starting ...')
        self.mp3 = tk.BooleanVar(value=bool(self.cfg.get('mp3', True)) and bool(self.ffmpeg))
        self.auto_clean = tk.BooleanVar(value=bool(self.cfg.get('auto_clean', True)))
        self.replace_old = tk.BooleanVar(value=bool(self.cfg.get('replace_old', True)))
        self.follow = tk.BooleanVar(value=bool(self.cfg.get('follow', True)))
        self.autonext = tk.BooleanVar(value=bool(self.cfg.get('autonext', False)))
        self.remember = tk.BooleanVar(value=bool(self.cfg.get('remember', True)))
        self.volume = tk.DoubleVar(value=float(self.cfg.get('volume', 0.9)))
        self.seek_var = tk.DoubleVar(value=0.0)
        self.menus = []

        self._build_ui()
        self._apply_theme()
        self._load_session()
        self._apply_mode()
        self.player.set_volume(self.volume.get())

        self.protocol('WM_DELETE_WINDOW', self._on_close)
        self._bind_keys()
        threading.Thread(target=self._worker, daemon=True).start()
        self.after(80, self._pump)
        self.after(200, self._tick)
        self.backend.start()
        self.set_status('Paste text, then Generate (Ctrl+Enter).')

    # ---------- settings ----------
    @staticmethod
    def _load_cfg():
        try:
            return json.loads(SETTINGS_FILE.read_text(encoding='utf-8'))
        except Exception:
            return {}

    def _save_cfg(self):
        try:
            self.cfg.update(
                theme='dark' if self.dark else 'light', mode=self.mode,
                voice=self.voice_id(), speed=round(self.speed.get(), 2),
                mp3=self.mp3.get(), auto_clean=self.auto_clean.get(),
                replace_old=self.replace_old.get(), follow=self.follow.get(),
                autonext=self.autonext.get(), remember=self.remember.get(),
                volume=round(self.volume.get(), 2), output=str(self.out_dir))
            self.backend.save_settings(self.cfg)
            SETTINGS_FILE.write_text(json.dumps(self.cfg, indent=2), encoding='utf-8')
        except Exception:
            pass

    @property
    def clean_opts(self):
        o = dict(CLEAN_DEFAULTS)
        o.update(self.cfg.get('clean', {}))
        return o

    def _on_close(self):
        if self.pending and not messagebox.askyesno(
                'Still generating',
                f'{self.pending} job(s) still running or queued.\nQuit anyway?'):
            return
        self._sync_part_text()
        self._save_cfg()
        self._save_session(force=True)
        try:
            self.player.stop()
        except Exception:
            pass
        self.destroy()

    def report_callback_exception(self, exc, val, tb):
        messagebox.showerror(f'{APP_NAME} error',
                             ''.join(traceback.format_exception(exc, val, tb))[-1500:])

    # ---------- fonts ----------
    def _make_fonts(self):
        fam = 'Segoe UI'
        for n in ('TkDefaultFont', 'TkTextFont', 'TkMenuFont', 'TkHeadingFont'):
            try:
                tkfont.nametofont(n).configure(family=fam, size=10)
            except tk.TclError:
                pass
        self.f_ui = tkfont.Font(family=fam, size=10)
        self.f_bold = tkfont.Font(family=fam, size=10, weight='bold')
        self.f_small = tkfont.Font(family=fam, size=9)
        self.f_title = tkfont.Font(family=TITLE_FONT[0], size=TITLE_FONT[1],
                                   weight=TITLE_FONT[2], slant=TITLE_FONT[3])
        self.f_text = tkfont.Font(family=TEXT_FONT[0], size=TEXT_FONT[1])
        self.f_mono = tkfont.Font(family='Consolas', size=10)

    # ---------- UI ----------
    def _build_ui(self):
        self.columnconfigure(0, weight=1)
        self.rowconfigure(2, weight=1)

        head = ttk.Frame(self, padding=(20, 12, 20, 9))
        head.grid(row=0, column=0, sticky='ew')
        head.columnconfigure(1, weight=1)
        ttk.Label(head, text=APP_NAME, style='Title.TLabel').grid(row=0, column=0, sticky='w')
        ttk.Label(head, text=SUBTITLE, style='Muted.TLabel').grid(
            row=0, column=1, sticky='w', padx=14, pady=(8, 0))
        self.mode_btn = ttk.Button(head, command=self.toggle_mode, style='Ghost.TButton')
        self.mode_btn.grid(row=0, column=2, padx=(0, 8))
        self.theme_btn = ttk.Button(head, command=self._toggle_theme, style='Ghost.TButton')
        self.theme_btn.grid(row=0, column=3, padx=(0, 8))
        self.main_menu = tk.Menu(self, tearoff=0)
        self.menus.append(self.main_menu)
        mmn = self.main_menu
        mmn.add_command(label='Open output folder', command=self._open_output)
        mmn.add_command(label='Change output folder ...', command=self._change_output)
        mmn.add_command(label='Move all audio to a folder ...', command=self.move_all_audio)
        mmn.add_command(label='Merge all audio into one file ...', command=self.merge_all_audio)
        mmn.add_separator()
        mmn.add_command(label='Find and replace ...    Ctrl+F', command=self.open_find)
        mmn.add_command(label='Bigger text    Ctrl++', command=lambda: self.zoom_text(1))
        mmn.add_command(label='Smaller text    Ctrl+-', command=lambda: self.zoom_text(-1))
        mmn.add_separator()
        mmn.add_command(label='Delete all parts ...', command=self.delete_all_parts)
        mmn.add_command(label='Undo last delete', command=self.undo_delete)
        mmn.add_separator()
        mmn.add_checkbutton(label='Remember parts between sessions',
                            variable=self.remember, command=self._save_cfg)
        mmn.add_command(label='Forget saved parts', command=self._forget_session)
        mmn.add_separator()
        mmn.add_command(label='Keyboard shortcuts', command=self._show_shortcuts)
        self.main_menu.configure(postcommand=self._refresh_menus)
        ttk.Menubutton(head, text='Menu', menu=self.main_menu, style='Ghost.TMenubutton').grid(
            row=0, column=4)

        self.accent_line = tk.Frame(self, height=3)
        self.accent_line.grid(row=1, column=0, sticky='ew')

        self.paned = tk.PanedWindow(self, orient='horizontal', sashwidth=8, bd=0,
                                    sashrelief='flat', opaqueresize=True)
        self.paned.grid(row=2, column=0, sticky='nsew', padx=16, pady=(12, 6))
        self.side = ttk.Frame(self.paned)
        self.editor = ttk.Frame(self.paned)
        self.paned.add(self.side, width=330, minsize=250, stretch='never')
        self.paned.add(self.editor, minsize=560, stretch='always')
        self._build_side()
        self._build_editor()
        self._build_player()

        bar = ttk.Frame(self, style='Status.TFrame', padding=(20, 7))
        bar.grid(row=4, column=0, sticky='ew')
        bar.columnconfigure(0, weight=1)
        ttk.Label(bar, textvariable=self.status, style='Status.TLabel').grid(
            row=0, column=0, sticky='w')
        self.undo_btn = ttk.Button(bar, text='Undo delete', style='Undo.TButton',
                                   command=self.undo_delete)
        self.undo_btn.grid(row=0, column=1, padx=(10, 10))
        self.undo_btn.grid_remove()
        self.batch_bar = ttk.Progressbar(bar, maximum=100, length=150, mode='determinate',
                                         style='Horizontal.TProgressbar')
        self.batch_bar.grid(row=0, column=2, padx=(0, 10))
        self.batch_bar.grid_remove()
        self.queue_lbl = ttk.Label(bar, style='StatusMuted.TLabel')
        self.queue_lbl.grid(row=0, column=3, sticky='e')

    def _build_side(self):
        s = self.side
        s.columnconfigure(0, weight=1)
        s.rowconfigure(1, weight=1)
        top = ttk.Frame(s)
        top.grid(row=0, column=0, sticky='ew', pady=(0, 6))
        top.columnconfigure(0, weight=1)
        ttk.Label(top, text='Parts', style='H.TLabel').grid(row=0, column=0, sticky='w')
        self.count_lbl = ttk.Label(top, style='Muted.TLabel')
        self.count_lbl.grid(row=0, column=1, sticky='e')
        self.total_lbl = ttk.Label(top, style='Muted.TLabel')
        self.total_lbl.grid(row=1, column=0, columnspan=2, sticky='w')

        box = ttk.Frame(s, style='Card.TFrame')
        box.grid(row=1, column=0, sticky='nsew')
        box.columnconfigure(0, weight=1)
        box.rowconfigure(0, weight=1)
        self.tree = ttk.Treeview(box, columns=('n', 'name', 'words', 'status'),
                                 show='headings', selectmode='extended')
        self.tree.heading('n', text='#', anchor='w')
        self.tree.heading('name', text='Starts with', anchor='w')
        self.tree.heading('words', text='Words', anchor='e')
        self.tree.heading('status', text='Status', anchor='w')
        self.tree.column('n', width=34, stretch=False, anchor='w')
        self.tree.column('name', width=104, anchor='w')
        self.tree.column('words', width=62, stretch=False, anchor='e')
        self.tree.column('status', width=92, stretch=False, anchor='w')
        self.tree.grid(row=0, column=0, sticky='nsew', padx=(1, 0), pady=1)
        sb = ttk.Scrollbar(box, orient='vertical', command=self.tree.yview)
        sb.grid(row=0, column=1, sticky='ns', padx=(0, 1), pady=1)
        self.tree.configure(yscrollcommand=sb.set)
        self.tree.bind('<<TreeviewSelect>>', self._on_tree_select)
        self.tree.bind('<Double-1>', lambda e: self.listen_selected())
        self.tree.bind('<Delete>', lambda e: (self.delete_selected(), 'break')[1])
        self.tree.bind('<Control-a>', lambda e: (self.select_all_parts(), 'break')[1])
        self.tree.bind('<Button-3>', self._tree_menu)

        # right-click menu on the parts list
        cm = self.part_ctx = tk.Menu(self, tearoff=0)
        self.menus.append(cm)
        cm.add_command(label='Listen', command=self.listen_selected)
        cm.add_command(label='Generate', command=self.generate_targets)
        cm.add_separator()
        cm.add_command(label='Duplicate', command=self.duplicate_part)
        cm.add_command(label='Merge selected (or with next)', command=self.merge_parts)
        cm.add_command(label='Move up    Alt+Up', command=lambda: self.move_parts(-1))
        cm.add_command(label='Move down    Alt+Down', command=lambda: self.move_parts(1))
        cm.add_separator()
        cm.add_command(label='Show audio in folder', command=self.reveal_selected_audio)
        cm.add_command(label='Delete audio only ...', command=self.delete_selected_audio)
        cm.add_command(label='Delete part ...    Del', command=self.delete_selected)

        # "More" menu: bulk tools
        mm = self.more_menu = tk.Menu(self, tearoff=0, postcommand=self._refresh_menus)
        self.menus.append(mm)
        mm.add_command(label='Select all parts    Ctrl+A', command=self.select_all_parts)
        mm.add_command(label='Merge selected parts', command=self.merge_parts)
        mm.add_command(label='Split part at cursor', command=self.split_at_cursor)
        mm.add_separator()
        mm.add_command(label='Generate parts without audio', command=self.generate_missing)
        mm.add_command(label='Retry failed parts', command=self.retry_failed)
        mm.add_separator()
        mm.add_command(label='Delete audio of selected parts ...', command=self.delete_selected_audio)
        mm.add_command(label='Delete finished parts ...', command=self.delete_finished)
        mm.add_command(label='Delete empty parts', command=self.delete_empty)
        mm.add_command(label='Delete all parts ...', command=self.delete_all_parts)
        mm.add_command(label='Undo last delete', command=self.undo_delete)
        mm.add_separator()
        mm.add_command(label='Move all audio to a folder ...', command=self.move_all_audio)
        mm.add_command(label='Merge all audio into one file ...', command=self.merge_all_audio)
        mm.add_command(label='Show audio in folder', command=self.reveal_selected_audio)

        btns = ttk.Frame(s)
        btns.grid(row=2, column=0, sticky='ew', pady=(8, 0))
        for c in range(3):
            btns.columnconfigure(c, weight=1, uniform='sb')

        def put(widget, r, c, span=1):
            widget.grid(row=r, column=c, columnspan=span, sticky='ew', padx=2, pady=(0, 6))
        put(ttk.Button(btns, text='Add part', command=self.add_part), 0, 0)
        put(ttk.Button(btns, text='Duplicate', command=self.duplicate_part), 0, 1)
        put(ttk.Button(btns, text='Delete', command=self.delete_selected), 0, 2)
        put(ttk.Button(btns, text='Move up', command=lambda: self.move_parts(-1)), 1, 0)
        put(ttk.Button(btns, text='Move down', command=lambda: self.move_parts(1)), 1, 1)
        put(ttk.Menubutton(btns, text='More', menu=mm), 1, 2)
        put(ttk.Button(btns, text='Generate all', command=self.generate_all,
                       style='Accent.TButton'), 2, 0, span=2)
        put(ttk.Button(btns, text='Cancel all', command=self.cancel_all), 2, 2)

    def _build_editor(self):
        e = self.editor
        e.columnconfigure(0, weight=1)
        e.rowconfigure(2, weight=1)

        card = ttk.Frame(e, style='Card.TFrame', padding=12)
        card.grid(row=0, column=0, sticky='ew', pady=(0, 8))
        card.columnconfigure(1, weight=1)
        ttk.Label(card, text='Voice', style='Card.TLabel').grid(row=0, column=0, sticky='w')
        self.voice_box = ttk.Combobox(card, state='readonly', style='Card.TCombobox',
                                      font=self.f_ui, height=16)
        self.voice_box.grid(row=0, column=1, sticky='ew', padx=(10, 22))
        self.voice_box.bind('<<ComboboxSelected>>', lambda e: (self.voice_box.selection_clear(),
                                                               self._save_cfg()))
        ttk.Label(card, text='Speed', style='Card.TLabel').grid(row=0, column=2, sticky='w')
        ttk.Scale(card, from_=0.6, to=1.6, variable=self.speed, length=150,
                  style='Card.Horizontal.TScale', command=self._on_speed).grid(
            row=0, column=3, padx=(10, 8))
        self.speed_lbl = ttk.Label(card, width=5, style='CardMuted.TLabel')
        self.speed_lbl.grid(row=0, column=4)

        extra = self.backend.build_controls(card)
        if extra is not None:
            extra.grid(row=1, column=0, columnspan=5, sticky='ew', pady=(10, 0))

        opts = ttk.Frame(card, style='CardInner.TFrame')
        opts.grid(row=2, column=0, columnspan=5, sticky='ew', pady=(10, 0))
        opts.columnconfigure(9, weight=1)
        cb = ttk.Checkbutton(opts, text='Save as MP3' if self.ffmpeg else 'WAV only (no ffmpeg)',
                             variable=self.mp3, style='Card.TCheckbutton')
        cb.grid(row=0, column=0, sticky='w')
        if not self.ffmpeg:
            cb.state(['disabled'])
        ttk.Checkbutton(opts, text='Auto-clean on paste', variable=self.auto_clean,
                        style='Card.TCheckbutton').grid(row=0, column=1, padx=(18, 0))
        ttk.Checkbutton(opts, text='Replace old audio when regenerating',
                        variable=self.replace_old, style='Card.TCheckbutton').grid(
            row=0, column=2, padx=(18, 0))

        meta = ttk.Frame(e)
        meta.grid(row=1, column=0, sticky='ew', pady=(0, 4))
        meta.columnconfigure(0, weight=1)
        self.part_lbl = ttk.Label(meta, style='H.TLabel')
        self.part_lbl.grid(row=0, column=0, sticky='w')
        self.stats_lbl = ttk.Label(meta, style='Muted.TLabel')
        self.stats_lbl.grid(row=0, column=1, sticky='e')

        self.text_border = tk.Frame(e)
        self.text_border.grid(row=2, column=0, sticky='nsew')
        self.text_inner = tk.Frame(self.text_border)
        self.text_inner.pack(fill='both', expand=True, padx=1, pady=1)
        self.text_inner.columnconfigure(0, weight=1)
        self.text_inner.rowconfigure(0, weight=1)
        self.text = tk.Text(self.text_inner, wrap='word', font=self.f_text, undo=True,
                            maxundo=200, bd=0, highlightthickness=0, padx=18, pady=14,
                            spacing1=2, spacing2=5, spacing3=6)
        self.text.grid(row=0, column=0, sticky='nsew')
        tsb = ttk.Scrollbar(self.text_inner, orient='vertical', command=self.text.yview)
        tsb.grid(row=0, column=1, sticky='ns')
        self.text.configure(yscrollcommand=tsb.set)
        self.text.tag_configure('reading')
        self.text.bind('<<Paste>>', self._on_paste)
        self.text.bind('<<Modified>>', self._on_modified)
        self.text.bind('<Control-a>', self._select_all)
        self.text.bind('<Control-Button-1>', self._ctrl_click)
        self.text.bind('<Button-3>', self._context_menu)
        self.text.bind('<Control-MouseWheel>', self._zoom_wheel)
        self.ctx = tk.Menu(self, tearoff=0)
        self.menus.append(self.ctx)
        for lab, ev in (('Cut', '<<Cut>>'), ('Copy', '<<Copy>>'), ('Paste', '<<Paste>>')):
            self.ctx.add_command(label=lab, command=lambda v=ev: self.text.event_generate(v))
        self.ctx.add_separator()
        self.ctx.add_command(label='Select all', command=self._select_all)

        act = ttk.Frame(e)
        act.grid(row=3, column=0, sticky='ew', pady=(8, 0))
        act.columnconfigure(5, weight=1)
        self.paste_menu = tk.Menu(self, tearoff=0)
        self.menus.append(self.paste_menu)
        pm = self.paste_menu
        pm.add_command(label='Paste clean at cursor    Ctrl+V', command=self.paste_cursor)
        pm.add_command(label='Replace everything with clipboard    Ctrl+Shift+V',
                       command=self.paste_replace)
        pm.add_command(label='Paste as a new part    Ctrl+N', command=self.paste_new_part)
        pm.add_command(label='Paste and split into parts ...', command=self.paste_split)
        pm.add_separator()
        pm.add_command(label='Load .txt file into this part ...', command=self.load_txt)
        pm.add_command(label='Load .txt file and split into parts ...', command=self.load_txt_split)
        ttk.Menubutton(act, text='Paste', menu=pm, width=5).grid(row=0, column=0, padx=(0, 5))
        self.clean_menu = tk.Menu(self, tearoff=0)
        self.menus.append(self.clean_menu)
        self.clean_menu.add_command(label='Clean this part now', command=self.clean_box)
        self.clean_menu.add_command(label='Cleaning options ...', command=self.open_clean_options)
        self.clean_menu.add_command(label='Pronunciation / replacements ...',
                                    command=self.open_replacements)
        ttk.Menubutton(act, text='Clean', menu=self.clean_menu, width=5).grid(row=0, column=1, padx=(0, 5))
        self.text_menu = tk.Menu(self, tearoff=0)
        self.menus.append(self.text_menu)
        tm = self.text_menu
        tm.add_command(label='Find and replace ...    Ctrl+F', command=self.open_find)
        tm.add_separator()
        tm.add_command(label='Save this part as .txt ...', command=self.save_part_txt)
        tm.add_command(label='Save all parts as one .txt ...', command=self.save_all_txt)
        tm.add_separator()
        tm.add_command(label='Bigger text    Ctrl++', command=lambda: self.zoom_text(1))
        tm.add_command(label='Smaller text    Ctrl+-', command=lambda: self.zoom_text(-1))
        tm.add_command(label='Reset text size    Ctrl+0', command=lambda: self.zoom_text(0))
        ttk.Menubutton(act, text='Text', menu=tm, width=4).grid(row=0, column=2, padx=(0, 5))
        ttk.Button(act, text='Split ...', width=7, command=self.split_current).grid(
            row=0, column=3, padx=(0, 5))
        ttk.Button(act, text='Clear', width=6, command=self._clear).grid(row=0, column=4)
        ttk.Button(act, text='Listen', width=7, command=self.listen_selected).grid(
            row=0, column=6, padx=(0, 5))
        ttk.Button(act, text='Generate', width=9, command=self.generate_selected,
                   style='Accent.TButton').grid(row=0, column=7)

        pr = ttk.Frame(e)
        pr.grid(row=4, column=0, sticky='ew', pady=(8, 0))
        pr.columnconfigure(0, weight=1)
        self.pbar = ttk.Progressbar(pr, maximum=100, mode='determinate',
                                    style='Horizontal.TProgressbar')
        self.pbar.grid(row=0, column=0, sticky='ew', padx=(0, 10))
        self.prog_lbl = ttk.Label(pr, width=34, style='Muted.TLabel')
        self.prog_lbl.grid(row=0, column=1, padx=(0, 8))
        ttk.Button(pr, text='Cancel', command=self.cancel_selected).grid(row=0, column=2)

    def _build_player(self):
        pl = ttk.Frame(self, style='Card.TFrame', padding=(14, 10))
        pl.grid(row=3, column=0, sticky='ew', padx=16, pady=(4, 8))
        pl.columnconfigure(0, weight=1)
        top = ttk.Frame(pl, style='CardInner.TFrame')
        top.grid(row=0, column=0, sticky='ew')
        top.columnconfigure(0, weight=1)
        self.now_lbl = ttk.Label(top, text='Nothing loaded', style='Card.TLabel')
        self.now_lbl.grid(row=0, column=0, sticky='w')
        ttk.Checkbutton(top, text='Follow along', variable=self.follow,
                        style='Card.TCheckbutton', command=self._save_cfg).grid(row=0, column=1)
        ttk.Checkbutton(top, text='Auto-play next part', variable=self.autonext,
                        style='Card.TCheckbutton', command=self._save_cfg).grid(
            row=0, column=2, padx=(14, 18))
        ttk.Label(top, text='Volume', style='CardMuted.TLabel').grid(row=0, column=3)
        ttk.Scale(top, from_=0, to=1, variable=self.volume, length=100,
                  style='Card.Horizontal.TScale',
                  command=lambda v: self.player.set_volume(float(v))).grid(
            row=0, column=4, padx=(8, 0))

        row = ttk.Frame(pl, style='CardInner.TFrame')
        row.grid(row=1, column=0, sticky='ew', pady=(8, 0))
        row.columnconfigure(10, weight=1)
        col = 0
        for label, delta in (('-30s', -30), ('-10s', -10), ('-5s', -5)):
            ttk.Button(row, text=label, width=4, style='Small.TButton',
                       command=lambda d=delta: self.skip(d)).grid(row=0, column=col, padx=(0, 3))
            col += 1
        self.play_btn = ttk.Button(row, text='Play', width=6, command=self.toggle_play,
                                   style='Play.TButton')
        self.play_btn.grid(row=0, column=col, padx=(6, 3))
        col += 1
        ttk.Button(row, text='Stop', width=4, style='Small.TButton',
                   command=self.stop_play).grid(row=0, column=col, padx=(0, 6))
        col += 1
        for label, delta in (('+5s', 5), ('+10s', 10), ('+30s', 30)):
            ttk.Button(row, text=label, width=4, style='Small.TButton',
                       command=lambda d=delta: self.skip(d)).grid(row=0, column=col, padx=(3, 0))
            col += 1
        self.time_lbl = ttk.Label(row, text='00:00', style='CardMuted.TLabel', width=7)
        self.time_lbl.grid(row=0, column=col, padx=(14, 2))
        self.seek = ttk.Scale(row, from_=0, to=1, variable=self.seek_var,
                              style='Card.Horizontal.TScale')
        self.seek.grid(row=0, column=10, sticky='ew', padx=4)
        self.seek.bind('<ButtonPress-1>', self._seek_press)
        self.seek.bind('<B1-Motion>', self._seek_drag)
        self.seek.bind('<ButtonRelease-1>', self._seek_release)
        self.dur_lbl = ttk.Label(row, text='00:00', style='CardMuted.TLabel', width=7)
        self.dur_lbl.grid(row=0, column=11, padx=(2, 12))
        ttk.Button(row, text='Prev part', style='Small.TButton',
                   command=lambda: self.step_part(-1)).grid(row=0, column=12, padx=(0, 4))
        ttk.Button(row, text='Next part', style='Small.TButton',
                   command=lambda: self.step_part(1)).grid(row=0, column=13)

    # ---------- theming ----------
    def _apply_theme(self):
        P = self.P = DARK if self.dark else LIGHT
        s = self.style
        self.configure(bg=P['bg'])
        s.configure('.', background=P['bg'], foreground=P['fg'], font=self.f_ui,
                    bordercolor=P['border'], lightcolor=P['bg'], darkcolor=P['bg'],
                    troughcolor=P['surface2'], focuscolor=P['bg'], insertcolor=P['fg'])
        s.configure('TFrame', background=P['bg'])
        s.configure('Card.TFrame', background=P['surface'], bordercolor=P['border'],
                    lightcolor=P['border'], darkcolor=P['border'], relief='solid', borderwidth=1)
        s.configure('CardInner.TFrame', background=P['surface'])
        s.configure('Status.TFrame', background=P['surface2'])
        s.configure('TLabel', background=P['bg'], foreground=P['fg'])
        s.configure('H.TLabel', font=self.f_bold)
        s.configure('Title.TLabel', font=self.f_title, foreground=P['accent'])
        s.configure('Muted.TLabel', foreground=P['muted'], font=self.f_small)
        s.configure('Card.TLabel', background=P['surface'])
        s.configure('CardMuted.TLabel', background=P['surface'], foreground=P['muted'])
        s.configure('Status.TLabel', background=P['surface2'])
        s.configure('StatusMuted.TLabel', background=P['surface2'], foreground=P['muted'],
                    font=self.f_small)

        def button(name, bg, fg, hover, border, font=None, pad=(12, 6), cls='TButton'):
            s.configure(name, background=bg, foreground=fg, bordercolor=border,
                        lightcolor=bg, darkcolor=bg, focusthickness=0, relief='flat',
                        borderwidth=1, padding=pad, font=font or self.f_ui, arrowcolor=fg)
            s.map(name,
                  background=[('disabled', P['surface']), ('pressed', hover), ('active', hover)],
                  lightcolor=[('pressed', hover), ('active', hover)],
                  darkcolor=[('pressed', hover), ('active', hover)],
                  bordercolor=[('active', hover)],
                  foreground=[('disabled', P['muted'])])
        button('TButton', P['surface2'], P['fg'], P['border'], P['border'])
        button('Small.TButton', P['surface2'], P['fg'], P['border'], P['border'], pad=(4, 6))
        button('Play.TButton', P['accent'], P['accent_fg'], P['accent_hover'],
               P['accent'], font=self.f_bold, pad=(10, 6))
        button('Ghost.TButton', P['bg'], P['muted'], P['surface2'], P['border'])
        button('Undo.TButton', P['accent'], P['accent_fg'], P['accent_hover'],
               P['accent'], font=self.f_bold, pad=(10, 1))
        button('Accent.TButton', P['accent'], P['accent_fg'], P['accent_hover'],
               P['accent'], font=self.f_bold, pad=(22, 7))
        button('TMenubutton', P['surface2'], P['fg'], P['border'], P['border'], pad=(12, 6))
        button('Ghost.TMenubutton', P['bg'], P['muted'], P['surface2'], P['border'], pad=(12, 6))

        for name, bg in (('TCheckbutton', P['bg']), ('Card.TCheckbutton', P['surface'])):
            s.configure(name, background=bg, foreground=P['fg'],
                        indicatorbackground=P['surface2'], indicatorforeground=P['accent_fg'],
                        bordercolor=P['border'], lightcolor=P['surface2'],
                        darkcolor=P['surface2'], focuscolor=bg, padding=(2, 2))
            s.map(name, background=[('active', bg)],
                  indicatorbackground=[('selected', P['accent']), ('active', P['border'])],
                  foreground=[('disabled', P['muted'])])

        for name in ('Card.TCombobox', 'TCombobox'):
            s.configure(name, fieldbackground=P['surface2'], background=P['surface2'],
                        foreground=P['fg'], arrowcolor=P['fg'], bordercolor=P['border'],
                        lightcolor=P['surface2'], darkcolor=P['surface2'], padding=(8, 6),
                        selectbackground=P['surface2'], selectforeground=P['fg'], arrowsize=16)
            s.map(name, fieldbackground=[('readonly', P['surface2'])],
                  background=[('active', P['border']), ('readonly', P['surface2'])],
                  foreground=[('readonly', P['fg'])],
                  selectbackground=[('readonly', P['surface2'])],
                  selectforeground=[('readonly', P['fg'])],
                  bordercolor=[('focus', P['accent'])])
        s.configure('TSpinbox', fieldbackground=P['surface2'], background=P['surface2'],
                    foreground=P['fg'], arrowcolor=P['fg'], bordercolor=P['border'],
                    lightcolor=P['surface2'], darkcolor=P['surface2'], padding=(6, 5),
                    selectbackground=P['select'], selectforeground=P['fg'], arrowsize=14)
        s.configure('TEntry', fieldbackground=P['surface2'], foreground=P['fg'],
                    insertcolor=P['accent'], bordercolor=P['border'],
                    lightcolor=P['surface2'], darkcolor=P['surface2'], padding=(6, 5),
                    selectbackground=P['select'], selectforeground=P['fg'])
        s.map('TEntry', bordercolor=[('focus', P['accent'])])
        s.configure('Card.TSpinbox', fieldbackground=P['surface2'], background=P['surface2'],
                    foreground=P['fg'], arrowcolor=P['fg'], bordercolor=P['border'],
                    lightcolor=P['surface2'], darkcolor=P['surface2'], padding=(6, 5),
                    selectbackground=P['select'], selectforeground=P['fg'], arrowsize=14)
        s.map('Card.TSpinbox', bordercolor=[('focus', P['accent'])])
        self.option_add('*TCombobox*Listbox.background', P['surface'])
        self.option_add('*TCombobox*Listbox.foreground', P['fg'])
        self.option_add('*TCombobox*Listbox.selectBackground', P['accent'])
        self.option_add('*TCombobox*Listbox.selectForeground', P['accent_fg'])
        self.option_add('*TCombobox*Listbox.font', self.f_ui)
        for box in self.backend.comboboxes(self.voice_box):
            try:
                pop = self.tk.call('ttk::combobox::PopdownWindow', str(box))
                self.tk.call(f'{pop}.f.l', 'configure', '-background', P['surface'],
                             '-foreground', P['fg'], '-selectbackground', P['accent'],
                             '-selectforeground', P['accent_fg'], '-font', self.f_ui.name,
                             '-borderwidth', 0, '-highlightthickness', 0)
            except tk.TclError:
                pass

        s.configure('Card.Horizontal.TScale', background=P['accent'], troughcolor=P['surface2'],
                    bordercolor=P['surface'], lightcolor=P['accent'], darkcolor=P['accent'])
        s.map('Card.Horizontal.TScale', background=[('active', P['accent_hover'])])
        s.configure('Horizontal.TProgressbar', background=P['accent'], troughcolor=P['surface2'],
                    bordercolor=P['border'], lightcolor=P['accent'], darkcolor=P['accent'],
                    thickness=10)
        for orient in ('Vertical', 'Horizontal'):
            n = f'{orient}.TScrollbar'
            s.configure(n, background=P['border'], troughcolor=P['surface'],
                        bordercolor=P['surface'], lightcolor=P['border'], darkcolor=P['border'],
                        arrowcolor=P['muted'], gripcount=0, arrowsize=16, relief='flat')
            s.map(n, background=[('pressed', P['accent']), ('active', P['muted'])],
                  lightcolor=[('pressed', P['accent']), ('active', P['muted'])],
                  darkcolor=[('pressed', P['accent']), ('active', P['muted'])])

        s.layout('Treeview', [('Treeview.treearea', {'sticky': 'nswe'})])
        s.configure('Treeview', background=P['surface'], fieldbackground=P['surface'],
                    foreground=P['fg'], rowheight=28, borderwidth=0, font=self.f_ui)
        s.configure('Treeview.Heading', background=P['surface2'], foreground=P['muted'],
                    relief='flat', font=self.f_small, padding=(8, 5))
        s.map('Treeview', background=[('selected', P['select'])],
              foreground=[('selected', P['fg'])])
        s.map('Treeview.Heading', background=[('active', P['border'])])
        self.tree.tag_configure('idle', foreground=P['fg'])
        self.tree.tag_configure('queued', foreground=P['muted'])
        self.tree.tag_configure('generating', foreground=P['accent'])
        self.tree.tag_configure('done', foreground=P['ok'])
        self.tree.tag_configure('error', foreground=P['err'])

        self.accent_line.configure(bg=P['accent'])
        self.paned.configure(bg=P['bg'])
        self.text_border.configure(bg=P['border'])
        self.text_inner.configure(bg=P['text_bg'])
        self.text.configure(bg=P['text_bg'], fg=P['fg'], insertbackground=P['accent'],
                            selectbackground=P['select'], selectforeground=P['fg'])
        self.text.tag_configure('reading', background=P['hl'], foreground=P['fg'])
        self.text.tag_raise('sel')
        for m in self.menus:
            m.configure(bg=P['surface'], fg=P['fg'], activebackground=P['accent'],
                        activeforeground=P['accent_fg'], bd=0, font=self.f_ui,
                        selectcolor=P['accent'])
        self.theme_btn.configure(text='Dark mode' if not self.dark else 'Light mode')
        self.backend.apply_theme(P)

    def _toggle_theme(self):
        self.dark = not self.dark
        self._apply_theme()
        self._save_cfg()

    def toggle_mode(self):
        self._sync_part_text()
        self.mode = 'single' if self.mode == 'parts' else 'parts'
        self._apply_mode()
        self._save_cfg()

    def _apply_mode(self):
        shown = str(self.side) in self.paned.panes()
        if self.mode == 'parts' and not shown:
            self.paned.add(self.side, before=self.editor, width=330, minsize=250,
                           stretch='never')
        elif self.mode == 'single' and shown:
            self.paned.forget(self.side)
        self.mode_btn.configure(text='Switch to single view' if self.mode == 'parts'
                                else 'Switch to parts view')
        self._update_counts()

    # ---------- voices / speed ----------
    def fill_voices(self, ids, labels, prefer):
        self.voice_ids = ids
        self.voice_box['values'] = labels
        cur = self.voice_id() if getattr(self, '_voices_ready', False) else prefer
        self._voices_ready = True
        idx = ids.index(cur) if cur in ids else (ids.index(prefer) if prefer in ids else 0)
        if ids:
            self.voice_box.current(idx)
        self.voice_box.selection_clear()

    def voice_id(self):
        ids = getattr(self, 'voice_ids', [])
        i = self.voice_box.current()
        if 0 <= i < len(ids):
            return ids[i]
        return self.cfg.get('voice', self.backend.default_voice)

    def _on_speed(self, *_):
        v = round(self.speed.get() / 0.05) * 0.05
        self.speed.set(round(v, 2))
        self.speed_lbl.configure(text=f'{v:.2f}x')

    # ---------- parts ----------
    def _new_part(self, text='', select=True, index=None):
        p = Part(text)
        if index is None:
            self.parts.append(p)
        else:
            self.parts.insert(index, p)
        self.tree.insert('', 'end' if index is None else index, iid=p.uid,
                         values=('', '', '', ''), tags=('idle',))
        self._renumber()
        self._refresh_row(p)
        if select:
            self.select_part(p)
        return p

    def _blank_selected(self):
        """The selected part, if it is still completely empty (nothing typed, no audio)."""
        self._sync_part_text()
        p = self.sel
        if p in self.parts and not p.text.strip() and not p.audio and p.state == 'idle':
            return p
        return None

    def add_part(self):
        if self._blank_selected():
            self.text.focus_set()
            self.set_status('This part is already empty. Type or paste into it.')
            return
        self._sync_part_text()
        i = self.parts.index(self.sel) + 1 if self.sel in self.parts else None
        self._new_part('', index=i)
        self.text.focus_set()
        self._save_session_soon()

    # ---------- selection helpers ----------
    def _target_parts(self):
        """Parts highlighted in the list (in list order), else the one in the editor."""
        uids = set(self.tree.selection())
        parts = [p for p in self.parts if p.uid in uids]
        if parts:
            return parts
        return [self.sel] if self.sel in self.parts else []

    def select_all_parts(self):
        self.tree.selection_set(tuple(p.uid for p in self.parts))

    def _tree_menu(self, event):
        row = self.tree.identify_row(event.y)
        if row and row not in self.tree.selection():
            self.tree.selection_set(row)
            self._on_tree_select()
        try:
            self.part_ctx.tk_popup(event.x_root, event.y_root)
        finally:
            self.part_ctx.grab_release()

    def step_edit(self, d):
        if not self.parts or self.sel not in self.parts:
            return
        j = self.parts.index(self.sel) + d
        if 0 <= j < len(self.parts):
            self.select_part(self.parts[j])

    def _offset(self, index):
        r = self.text.count('1.0', index, 'chars')
        if not r:
            return 0
        return int(r[0] if isinstance(r, (tuple, list)) else r)

    def _refresh_menus(self):
        st = 'normal' if self._trash else 'disabled'
        for m in (getattr(self, 'more_menu', None), getattr(self, 'main_menu', None)):
            if m is None:
                continue
            try:
                m.entryconfigure('Undo last delete', state=st)
            except tk.TclError:
                pass

    # ---------- delete / undo ----------
    def _confirm_delete(self, heading, detail, n_audio=0):
        """Returns (confirmed, also_delete_audio_files)."""
        top, body = self._dialog('Confirm delete', 460)
        top.grab_set()
        ttk.Label(body, text=heading, style='H.TLabel', wraplength=420,
                  justify='left').pack(anchor='w')
        ttk.Label(body, text=detail, style='Muted.TLabel', wraplength=420,
                  justify='left').pack(anchor='w', pady=(6, 0))
        audio = tk.BooleanVar(value=False)
        if n_audio:
            ttk.Checkbutton(
                body, variable=audio,
                text=f'Also delete the {n_audio} audio file{"s" if n_audio != 1 else ""} from disk'
            ).pack(anchor='w', pady=(12, 0))
        result = {'ok': False}

        def ok():
            result['ok'] = True
            top.destroy()
        row = ttk.Frame(body)
        row.pack(fill='x', pady=(16, 0))
        ttk.Button(row, text='Delete', command=ok, style='Accent.TButton').pack(side='right')
        cancel = ttk.Button(row, text='Cancel', command=top.destroy)
        cancel.pack(side='right', padx=8)
        cancel.focus_set()
        top.bind('<Escape>', lambda e: top.destroy())
        self.wait_window(top)
        return result['ok'], bool(audio.get()) and result['ok']

    def _unload_player(self):
        self.player.unload()
        self.player_part = None
        self._clear_reading()
        self.now_lbl.configure(text='Nothing loaded')
        self.time_lbl.configure(text='00:00')
        self.dur_lbl.configure(text='00:00')
        self.seek_var.set(0)

    def _unlink_audio(self, path):
        path = Path(path)
        if self.player.path == str(path):
            self._unload_player()
        try:
            path.unlink(missing_ok=True)
            return True
        except OSError:
            return False

    def _drop_parts(self, parts):
        """Remove parts from the list and keep the editor on something sensible."""
        parts = [p for p in self.parts if p in parts]
        if not parts:
            return
        sel_idx = self.parts.index(self.sel) if self.sel in self.parts else 0
        sel_removed = self.sel in parts
        for p in parts:
            if p.state in ('queued', 'generating'):
                self.cancel_part(p)
            if self.player_part is p:
                self._unload_player()
            self.parts.remove(p)
            if self.tree.exists(p.uid):
                self.tree.delete(p.uid)
        if not self.parts:
            self.sel = None
            self._new_part('')
        elif sel_removed:
            self.sel = None
            self.select_part(self.parts[min(sel_idx, len(self.parts) - 1)])
        self._renumber()
        self._update_part_label()
        self._save_session_soon()

    def _remove_parts(self, parts, delete_audio=False):
        """Delete parts (and optionally their audio), remembering them for Undo."""
        parts = [p for p in self.parts if p in parts]
        if not parts:
            return 0, 0
        self._sync_part_text()
        snap, failed = [], 0
        for p in parts:
            keep_audio = bool(p.audio)
            if delete_audio and p.audio:
                if p.state not in ('queued', 'generating') and self._unlink_audio(p.audio):
                    keep_audio = False
                else:
                    failed += 1
            snap.append((self.parts.index(p), p.text, str(p.audio) if keep_audio else '',
                         p.number, p.duration))
        self._drop_parts(parts)
        if any(t.strip() or a for _, t, a, _, _ in snap):
            self._trash = snap
        self._offer_undo()
        return len(parts), failed

    def _offer_undo(self):
        if self._trash_after:
            self.after_cancel(self._trash_after)
            self._trash_after = None
        if self._trash:
            self.undo_btn.grid()
            self._trash_after = self.after(180000, self._expire_undo)
        else:
            self.undo_btn.grid_remove()

    def _expire_undo(self):
        self._trash_after = None
        self._trash = []
        self.undo_btn.grid_remove()

    def undo_delete(self):
        if not self._trash:
            self.set_status('Nothing to undo.')
            return
        snap, self._trash = self._trash, []
        self._offer_undo()
        self._sync_part_text()
        if (len(self.parts) == 1 and not self.parts[0].text.strip()
                and not self.parts[0].audio):                 # blank placeholder
            ph = self.parts[0]
            self.parts.remove(ph)
            self.tree.delete(ph.uid)
            if self.sel is ph:
                self.sel = None
        first = None
        for idx, text, audio, number, duration in sorted(snap, key=lambda r: r[0]):
            p = self._new_part(text, select=False, index=min(idx, len(self.parts)))
            p.number = number
            if audio and Path(audio).exists():
                p.audio, p.state, p.duration = Path(audio), 'done', float(duration or 0)
            self._refresh_row(p)
            first = first or p
        if first:
            self.select_part(first)
        self._renumber()
        self._save_session_soon()
        n = len(snap)
        self.set_status(f'Restored {n} part{"s" if n != 1 else ""}.')

    def _report_delete(self, removed, failed, with_audio):
        msg = f'Deleted {removed} part{"s" if removed != 1 else ""}'
        msg += ' and their audio.' if with_audio and not failed else '.'
        if failed:
            msg += (f' {failed} audio file{"s" if failed != 1 else ""} could not be deleted '
                    '(open in another app?).')
        if self._trash:
            msg += '  Undo is in the status bar.'
        self.set_status(msg)

    def _audio_count(self, parts):
        return sum(1 for p in parts if p.audio and Path(p.audio).exists())

    def _delete_with_confirm(self, parts, heading, detail):
        if not parts:
            return
        ok, with_audio = self._confirm_delete(heading, detail, self._audio_count(parts))
        if ok:
            self._report_delete(*self._remove_parts(parts, with_audio), with_audio)

    def delete_selected(self):
        parts = self._target_parts()
        if not parts:
            return
        if not any(p.text.strip() or p.audio for p in parts):
            self._remove_parts(parts)                       # blank, no need to ask
            return
        n = len(parts)
        self._delete_with_confirm(
            parts, 'Delete this part?' if n == 1 else f'Delete {n} parts?',
            'The text leaves the list. Audio files stay in the output folder unless you '
            'tick the box. Undo brings the parts back right after.')

    def delete_all_parts(self):
        self._sync_part_text()
        parts = list(self.parts)
        if not any(p.text.strip() or p.audio for p in parts):
            self.set_status('Nothing to delete.')
            return
        self._delete_with_confirm(
            parts, f'Delete all {len(parts)} part{"s" if len(parts) != 1 else ""}?',
            'This clears the whole list and cancels anything still queued. Audio files stay in '
            'the output folder unless you tick the box. Undo brings the parts back (audio '
            'deleted from disk cannot come back).')

    def delete_finished(self):
        parts = [p for p in self.parts if p.state == 'done']
        if not parts:
            self.set_status('No finished parts to delete.')
            return
        n = len(parts)
        self._delete_with_confirm(
            parts, f'Delete {n} finished part{"s" if n != 1 else ""}?',
            'Only parts that already have audio. Audio files stay in the output folder '
            'unless you tick the box.')

    def delete_empty(self):
        parts = [p for p in self.parts if not p.text.strip() and not p.audio
                 and p.state not in ('queued', 'generating')]
        if not parts:
            self.set_status('No empty parts.')
            return
        n = len(parts)
        self._remove_parts(parts)
        self.set_status(f'Removed {n} empty part{"s" if n != 1 else ""}.')

    def delete_selected_audio(self):
        parts = [p for p in self._target_parts()
                 if p.audio and p.state not in ('queued', 'generating')]
        if not parts:
            self.set_status('The selected parts have no audio.')
            return
        n = len(parts)
        if not messagebox.askyesno(
                'Delete audio',
                f'Delete the audio file{"s" if n != 1 else ""} of {n} part{"s" if n != 1 else ""} '
                'from disk?\nThe text stays, so you can generate again.', parent=self):
            return
        failed = 0
        for p in parts:
            if self._unlink_audio(p.audio):
                p.audio, p.state, p.duration = None, 'idle', 0.0
                p.map, p.starts, p.map_text = [], [], None
            else:
                failed += 1
            self._refresh_row(p)
        self._update_progress_ui()
        self._update_counts()
        self._save_session_soon()
        self.set_status(f'Deleted audio of {n - failed} part{"s" if n - failed != 1 else ""}.'
                        + (f' {failed} could not be deleted (open in another app?).' if failed else ''))

    # ---------- part tools ----------
    def duplicate_part(self):
        self._sync_part_text()
        targets = self._target_parts()
        if not targets:
            return
        last = max(self.parts.index(p) for p in targets)
        first = None
        for k, p in enumerate(targets):
            c = self._new_part(p.text, select=False, index=last + 1 + k)
            first = first or c
        self._renumber()
        self.select_part(first)
        self._save_session_soon()
        self.set_status(f'Duplicated {len(targets)} part{"s" if len(targets) != 1 else ""}.')

    def merge_parts(self):
        self._sync_part_text()
        targets = self._target_parts()
        if len(targets) == 1:
            i = self.parts.index(targets[0])
            if i + 1 >= len(self.parts):
                self.set_status('Select two or more parts to merge, or a part that has one after it.')
                return
            targets = [targets[0], self.parts[i + 1]]
        if len(targets) < 2:
            return
        if any(p.state in ('queued', 'generating') for p in targets):
            self.set_status('Wait for the queue to finish before merging.')
            return
        if not messagebox.askyesno(
                'Merge parts', f'Join {len(targets)} parts into one?\n'
                'The merged part needs generating again. Old audio files stay in the output folder.',
                parent=self):
            return
        first = targets[0]
        text = '\n\n'.join(p.text.strip() for p in targets if p.text.strip())
        if self.player_part is first:
            self._unload_player()
        self._drop_parts(targets[1:])
        first.audio, first.state, first.duration = None, 'idle', 0.0
        first.map, first.starts, first.map_text = [], [], None
        if first is self.sel:
            self._set_editor_text(text)
        else:
            first.text = text
        self._refresh_row(first)
        self.select_part(first)
        self._update_counts()
        self._save_session_soon()
        self.set_status(f'Merged {len(targets)} parts.')

    def split_at_cursor(self):
        if not self.sel:
            return
        if self.sel.state in ('queued', 'generating'):
            self.set_status('Wait for this part to finish before splitting it.')
            return
        txt = self.text.get('1.0', 'end-1c')
        off = self._offset('insert')
        before, after = txt[:off].rstrip(), txt[off:].lstrip()
        if not before or not after:
            self.set_status('Click where the new part should begin, then split.')
            return
        self._set_editor_text(before)
        self._new_part(after, select=False, index=self.parts.index(self.sel) + 1)
        self._renumber()
        self.set_status('Split into two parts at the cursor.')

    def move_parts(self, d):
        targets = self._target_parts()
        if not targets:
            return
        idxs = sorted(self.parts.index(p) for p in targets)
        stuck = set()
        for i in (idxs if d < 0 else idxs[::-1]):
            j = i + d
            if not 0 <= j < len(self.parts) or j in stuck:
                stuck.add(i)
                continue
            self.parts[i], self.parts[j] = self.parts[j], self.parts[i]
            self.tree.move(self.parts[j].uid, '', j)
        self._renumber()
        self._update_part_label()
        if targets:
            self.tree.see(targets[0].uid)
        self._save_session_soon()

    def generate_targets(self):
        self._sync_part_text()
        n = sum(1 for p in self._target_parts() if self.generate_part(p, quiet=True))
        self.set_status(f'Queued {n} part{"s" if n != 1 else ""}.')

    def generate_missing(self):
        self._sync_part_text()
        n = 0
        for p in list(self.parts):
            has_audio = bool(p.audio and Path(p.audio).exists())
            if p.text.strip() and not has_audio and p.state not in ('queued', 'generating'):
                if self.generate_part(p, quiet=True):
                    n += 1
        self.set_status(f'Queued {n} part{"s" if n != 1 else ""} without audio.')

    def retry_failed(self):
        n = 0
        for p in list(self.parts):
            if p.state == 'error' and self.generate_part(p, quiet=True):
                n += 1
        self.set_status(f'Queued {n} failed part{"s" if n != 1 else ""} again.' if n
                        else 'No failed parts.')

    def reveal_selected_audio(self):
        p = next((p for p in self._target_parts()
                  if p.audio and Path(p.audio).exists()), None)
        if p:
            reveal_in_folder(p.audio)
        else:
            self.set_status('No audio file to show yet.')

    # ---------- audio library tools ----------
    def move_all_audio(self):
        parts = [p for p in self.parts if p.audio and Path(p.audio).exists()
                 and p.state not in ('queued', 'generating')]
        if not parts:
            self.set_status('No generated audio to move.')
            return
        d = filedialog.askdirectory(parent=self, title='Move all audio to ...',
                                    initialdir=str(self.out_dir))
        if not d:
            return
        dest = Path(d)
        if not messagebox.askyesno(
                'Move audio', f'Move {len(parts)} audio file{"s" if len(parts) != 1 else ""} to\n'
                f'{dest} ?', parent=self):
            return
        moved = failed = 0
        for p in parts:
            src = Path(p.audio)
            if src.parent == dest:
                continue
            target = unique_path(dest / src.name)
            try:
                dest.mkdir(parents=True, exist_ok=True)
                shutil.move(str(src), str(target))
            except OSError:
                failed += 1
                continue
            if self.player.path == str(src):
                self.player.path = str(target)
            p.audio = target
            moved += 1
        self._save_session_soon()
        self.set_status(f'Moved {moved} file{"s" if moved != 1 else ""} to {dest}.'
                        + (f' {failed} failed.' if failed else ''))

    def merge_all_audio(self):
        files = [Path(p.audio) for p in self.parts
                 if p.audio and Path(p.audio).exists() and p.state != 'generating']
        if not files:
            self.set_status('No generated audio to merge.')
            return
        if not self.ffmpeg:
            messagebox.showinfo('Merge audio', 'Merging needs ffmpeg. Put ffmpeg.exe next to '
                                'the script or add it to PATH.', parent=self)
            return
        if self._merging:
            self.set_status('A merge is already running.')
            return
        out = filedialog.asksaveasfilename(
            parent=self, title='Save merged audio', initialdir=str(self.out_dir),
            initialfile=f'audiobook.{datetime.now():%Y-%m-%d}.mp3', defaultextension='.mp3',
            filetypes=[('MP3', '*.mp3'), ('WAV', '*.wav')])
        if not out:
            return
        self._merging = True
        self.set_status(f'Merging {len(files)} files ...')

        def work():
            lst = None
            try:
                fd, lst = tempfile.mkstemp(suffix='.txt')
                with os.fdopen(fd, 'w', encoding='utf-8') as f:
                    for p in files:
                        f.write("file '" + p.resolve().as_posix().replace("'", "'\\''") + "'\n")
                codec = (['-codec:a', 'pcm_s16le'] if out.lower().endswith('.wav')
                         else ['-codec:a', 'libmp3lame', '-qscale:a', '4'])
                r = subprocess.run([self.ffmpeg, '-y', '-loglevel', 'error', '-f', 'concat',
                                    '-safe', '0', '-i', lst, '-vn'] + codec + [out],
                                   capture_output=True, text=True, creationflags=NO_WINDOW)
                if r.returncode != 0:
                    raise RuntimeError((r.stderr or 'ffmpeg failed').strip()[-600:])
                self.set_status(f'Merged {len(files)} files into {Path(out).name}')
            except Exception as e:
                err = str(e)
                self.ui(lambda: messagebox.showerror('Merge audio', err[-900:]))
                self.set_status('Merge failed.')
            finally:
                if lst:
                    try:
                        os.unlink(lst)
                    except OSError:
                        pass
                self._merging = False
        threading.Thread(target=work, daemon=True).start()

    # ---------- text files / zoom ----------
    def save_part_txt(self):
        self._sync_part_text()
        if not self.sel or not self.sel.text.strip():
            self.set_status('This part is empty.')
            return
        path = filedialog.asksaveasfilename(
            parent=self, title='Save part as text', defaultextension='.txt',
            initialfile=f'{start_slug(self.sel.text)}.txt', filetypes=[('Text', '*.txt')])
        if path:
            Path(path).write_text(self.sel.text, encoding='utf-8')
            self.set_status(f'Saved {Path(path).name}')

    def save_all_txt(self):
        self._sync_part_text()
        texts = [p.text.strip() for p in self.parts if p.text.strip()]
        if not texts:
            self.set_status('Nothing to save.')
            return
        path = filedialog.asksaveasfilename(
            parent=self, title='Save all parts as text', defaultextension='.txt',
            initialfile='all_parts.txt', filetypes=[('Text', '*.txt')])
        if path:
            Path(path).write_text('\n\n'.join(texts), encoding='utf-8')
            self.set_status(f'Saved {len(texts)} parts to {Path(path).name}')

    def zoom_text(self, d):
        size = (TEXT_FONT[1] if d == 0
                else max(9, min(32, int(self.f_text.cget('size')) + d)))
        self.f_text.configure(size=size)
        self.cfg['text_size'] = size
        self._save_cfg()
        self.set_status(f'Text size {size}.')

    def _zoom_wheel(self, e):
        self.zoom_text(1 if e.delta > 0 else -1)
        return 'break'

    # ---------- find and replace ----------
    @staticmethod
    def _find_rx(find, case, word):
        if not find:
            return None
        pat = re.escape(find)
        if word and find[0].isalnum() and find[-1].isalnum():
            pat = rf'\b{pat}\b'
        return re.compile(pat, 0 if case else re.I)

    def _goto_match(self, part, a, b):
        if part is not self.sel:
            self.select_part(part)
        self.text.tag_remove('sel', '1.0', 'end')
        self.text.tag_add('sel', f'1.0+{a}c', f'1.0+{b}c')
        self.text.mark_set('insert', f'1.0+{b}c')
        self.text.see(f'1.0+{a}c')

    def open_find(self, event=None):
        if self._find_win is not None and self._find_win.winfo_exists():
            self._find_win.lift()
            self._find_entry.focus_set()
            self._find_entry.selection_range(0, 'end')
            return
        top, body = self._dialog('Find and replace', 520)
        self._find_win = top
        pre = ''
        try:
            pre = self.text.get('sel.first', 'sel.last')
        except tk.TclError:
            pass
        if '\n' in pre or len(pre) > 80:
            pre = ''
        fv, rv = tk.StringVar(value=pre), tk.StringVar()
        case, word, allp = tk.BooleanVar(value=False), tk.BooleanVar(value=False), tk.BooleanVar(value=True)

        grid = ttk.Frame(body)
        grid.pack(fill='x')
        grid.columnconfigure(1, weight=1)
        ttk.Label(grid, text='Find').grid(row=0, column=0, sticky='w', pady=3)
        self._find_entry = ttk.Entry(grid, textvariable=fv, width=42)
        self._find_entry.grid(row=0, column=1, sticky='ew', padx=(10, 0), pady=3)
        ttk.Label(grid, text='Replace with').grid(row=1, column=0, sticky='w', pady=3)
        ttk.Entry(grid, textvariable=rv, width=42).grid(row=1, column=1, sticky='ew',
                                                        padx=(10, 0), pady=3)
        opts = ttk.Frame(body)
        opts.pack(fill='x', pady=(8, 0))
        ttk.Checkbutton(opts, text='Match case', variable=case).pack(side='left')
        ttk.Checkbutton(opts, text='Whole words', variable=word).pack(side='left', padx=14)
        ttk.Checkbutton(opts, text='All parts', variable=allp).pack(side='left')
        info = ttk.Label(body, style='Muted.TLabel')
        info.pack(anchor='w', pady=(10, 0))

        def scope():
            self._sync_part_text()
            return list(self.parts) if allp.get() else ([self.sel] if self.sel else [])

        def count(*_):
            rx = self._find_rx(fv.get(), case.get(), word.get())
            if not rx:
                info.configure(text='')
                return
            tot = hit = 0
            for p in scope():
                n = len(rx.findall(p.text))
                if n:
                    tot, hit = tot + n, hit + 1
            info.configure(text=(f'{tot} match{"es" if tot != 1 else ""} in {hit} '
                                 f'part{"s" if hit != 1 else ""}') if tot else 'No matches.')

        def find_next(*_):
            rx = self._find_rx(fv.get(), case.get(), word.get())
            if not rx or not self.sel:
                return
            self._sync_part_text()
            cur, n = self.parts.index(self.sel), len(self.parts)
            try:
                off = self._offset('sel.last')
            except tk.TclError:
                off = self._offset('insert')
            order = [(cur, off)]
            if allp.get():
                order += [((cur + k) % n, 0) for k in range(1, n)]
            order.append((cur, 0))
            for idx, start in order:
                p = self.parts[idx]
                txt = self.text.get('1.0', 'end-1c') if p is self.sel else p.text
                m = rx.search(txt, start)
                if m:
                    self._goto_match(p, m.start(), m.end())
                    count()
                    return
            info.configure(text='No matches.')

        def replace_all():
            rx = self._find_rx(fv.get(), case.get(), word.get())
            if not rx:
                return
            with_text = rv.get()
            total = changed = 0
            for p in scope():
                new, k = rx.subn(lambda m: with_text, p.text)
                if k:
                    if p is self.sel:
                        self._set_editor_text(new)
                    else:
                        p.text = new
                        self._refresh_row(p)
                    total, changed = total + k, changed + 1
            self._save_session_soon()
            self._totals_soon()
            self.set_status(f'Replaced {total} in {changed} part{"s" if changed != 1 else ""}.'
                            if total else 'No matches.')
            count()

        for v in (fv, case, word, allp):
            v.trace_add('write', count)
        self._find_entry.bind('<Return>', find_next)
        top.bind('<Escape>', lambda e: top.destroy())
        row = ttk.Frame(body)
        row.pack(fill='x', pady=(14, 0))
        ttk.Button(row, text='Replace all', command=replace_all,
                   style='Accent.TButton').pack(side='right')
        ttk.Button(row, text='Find next', command=find_next).pack(side='right', padx=8)
        ttk.Button(row, text='Close', command=top.destroy).pack(side='left')
        self._find_entry.focus_set()
        self._find_entry.selection_range(0, 'end')
        count()

    def _renumber(self):
        for i, p in enumerate(self.parts):
            self.tree.set(p.uid, 'n', str(i + 1))
        self._update_counts()

    def _update_counts(self):
        n = len(self.parts)
        done = sum(1 for p in self.parts if p.state == 'done')
        self.count_lbl.configure(text=f'{done}/{n} generated')
        if self.pending:
            total = max(1, self._batch_total)
            self.queue_lbl.configure(text=f'{self._batch_done}/{total} done')
            self.batch_bar.configure(value=100 * self._batch_done / total)
            self.batch_bar.grid()
        else:
            self.queue_lbl.configure(text='')
            self.batch_bar.grid_remove()
            self._batch_total = self._batch_done = 0
        self.mode_btn.configure(
            text=('Switch to single view' if self.mode == 'parts'
                  else f'Switch to parts view ({n})'))
        self._totals_soon()

    def _totals_soon(self):
        if self._tot_after:
            self.after_cancel(self._tot_after)
        self._tot_after = self.after(350, self._update_totals)

    def _update_totals(self):
        self._tot_after = None
        words = sum(len(p.text.split()) for p in self.parts)
        made = sum(p.duration for p in self.parts if p.state == 'done')
        self.total_lbl.configure(
            text=f'{words:,} words  \u00b7  about {fmt_time(words / 160 * 60)}  \u00b7  '
                 f'{fmt_time(made)} generated')

    def _refresh_row(self, p):
        if not self.tree.exists(p.uid):
            return
        name = re.sub(r'\s+', ' ', p.text.strip())[:40] or '(empty)'
        st = {'idle': '', 'queued': 'queued', 'error': 'failed',
              'generating': f'{int(p.progress * 100)}%',
              'done': f'done  {fmt_time(p.duration)}' if p.duration else 'done'}[p.state]
        words = len(p.text.split())
        self.tree.set(p.uid, 'name', name)
        self.tree.set(p.uid, 'words', f'{words:,}' if words else '')
        self.tree.set(p.uid, 'status', st)
        self.tree.item(p.uid, tags=(p.state,))

    def _on_tree_select(self, e=None):
        sel = self.tree.selection()
        if not sel:
            return
        if len(sel) > 1:
            self.set_status(f'{len(sel)} parts selected. Right-click the list for actions.')
            return
        part = next((p for p in self.parts if p.uid == sel[0]), None)
        if part and part is not self.sel:
            self.select_part(part)

    def select_part(self, part):
        if part is self.sel:
            return
        self._sync_part_text()
        self.sel = part
        self.text.delete('1.0', 'end')
        self.text.insert('1.0', part.text)
        self.text.edit_reset()
        self.text.edit_modified(False)
        self._hl_idx = None
        self._clear_reading()
        if self.tree.exists(part.uid) and self.tree.selection() != (part.uid,):
            self.tree.selection_set(part.uid)
            self.tree.see(part.uid)
        self._update_stats()
        self._update_part_label()
        self._update_progress_ui()

    def _update_part_label(self):
        p = self.sel
        if not p:
            return
        i = self.parts.index(p) + 1
        self.part_lbl.configure(text=f'Part {i} of {len(self.parts)}')

    # ---------- editor text ----------
    def _sync_part_text(self):
        if self.sel is None:
            return
        self.sel.text = self.text.get('1.0', 'end-1c')

    def _on_modified(self, e=None):
        if self.text.edit_modified():
            self.text.edit_modified(False)
            self._sync_part_text()
            if self.sel:
                self._refresh_row(self.sel)
            self._update_stats()
            self._save_session_soon()

    def _set_editor_text(self, txt):
        self.text.edit_separator()
        self.text.delete('1.0', 'end')
        self.text.insert('1.0', txt)
        self.text.edit_separator()
        self._sync_part_text()
        if self.sel:
            self._refresh_row(self.sel)
        self._update_stats()
        self._save_session_soon()

    def _clip(self):
        try:
            return self.clipboard_get()
        except tk.TclError:
            self.set_status('Clipboard is empty.')
            return ''

    def _clean_clip(self):
        raw = self._clip()
        if not raw:
            return ''
        if not self.auto_clean.get():
            return raw
        rep = {}
        txt = clean_text(raw, self.clean_opts, finish=False, report=rep,
                         repl=self.cfg.get('replacements', ''))
        self.set_status(report_text(rep))
        return txt

    def _on_paste(self, event=None):
        self.paste_cursor()
        return 'break'

    def paste_cursor(self):
        txt = self._clean_clip()
        if not txt:
            return
        self.text.edit_separator()
        try:
            self.text.delete('sel.first', 'sel.last')
        except tk.TclError:
            pass
        self.text.insert('insert', txt)
        self.text.edit_separator()
        self.text.see('insert')
        self._sync_part_text()
        if self.sel:
            self._refresh_row(self.sel)
        self._update_stats()
        self._save_session_soon()

    def paste_replace(self):
        txt = self._clean_clip()
        if txt:
            self._set_editor_text(txt)

    def paste_new_part(self):
        txt = self._clean_clip()
        if not txt:
            return
        if self._blank_selected():
            self._set_editor_text(txt)
        else:
            i = self.parts.index(self.sel) + 1 if self.sel in self.parts else None
            self._new_part(txt, index=i)
        self._save_session_soon()

    def paste_split(self):
        txt = self._clean_clip()
        if txt:
            self._open_split(txt, replace_current=False)

    def load_txt(self):
        txt = self._read_txt()
        if txt:
            self._set_editor_text(txt)

    def load_txt_split(self):
        txt = self._read_txt()
        if txt:
            self._open_split(txt, replace_current=False)

    def _read_txt(self):
        path = filedialog.askopenfilename(parent=self, title='Open text file',
                                          filetypes=[('Text', '*.txt *.md'), ('All', '*.*')])
        if not path:
            return ''
        raw = None
        for enc in ('utf-8-sig', 'utf-16', 'cp1252'):
            try:
                raw = Path(path).read_text(encoding=enc)
                break
            except Exception:
                continue
        if raw is None:
            messagebox.showerror('Open file', 'Could not read that file.')
            return ''
        rep = {}
        txt = clean_text(raw, self.clean_opts, finish=False, report=rep,
                         repl=self.cfg.get('replacements', ''))
        self.set_status(f'Loaded {Path(path).name}. ' + report_text(rep))
        return txt

    def _select_all(self, event=None):
        self.text.tag_add('sel', '1.0', 'end-1c')
        return 'break'

    def _context_menu(self, event):
        self.text.focus_set()
        self.ctx.tk_popup(event.x_root, event.y_root)

    def _update_stats(self):
        t = self.text.get('1.0', 'end-1c').strip()
        words = len(re.findall(r'\S+', t))
        secs = estimate_seconds(t)
        self.stats_lbl.configure(
            text=f'{len(t):,} chars   {words:,} words   about {fmt_time(secs)} of audio')
        self._totals_soon()

    def clean_box(self):
        raw = self.text.get('1.0', 'end-1c')
        if not raw.strip():
            return
        rep = {}
        txt = clean_text(raw, self.clean_opts, report=rep,
                         repl=self.cfg.get('replacements', ''))
        self._set_editor_text(txt)
        self.set_status(report_text(rep) + '  (Ctrl+Z undoes it)')

    def _clear(self):
        self._set_editor_text('')
        self.text.focus_set()

    # ---------- dialogs ----------
    def _dialog(self, title, width=560):
        top = tk.Toplevel(self)
        top.title(title)
        top.configure(bg=self.P['bg'])
        top.transient(self)
        top.resizable(False, False)
        body = ttk.Frame(top, padding=18)
        body.pack(fill='both', expand=True)
        self.update_idletasks()
        x = self.winfo_rootx() + max(20, (self.winfo_width() - width) // 2)
        top.geometry(f'+{x}+{self.winfo_rooty() + 90}')
        return top, body

    def open_clean_options(self):
        top, body = self._dialog('Cleaning options')
        ttk.Label(body, text='Emoji, symbols and pictographs are always removed.',
                  style='Muted.TLabel').pack(anchor='w', pady=(0, 10))
        vars_ = {}
        cur = self.clean_opts
        for key, label in CLEAN_LABELS:
            v = tk.BooleanVar(value=cur.get(key, True))
            vars_[key] = v
            ttk.Checkbutton(body, text=label, variable=v).pack(anchor='w', pady=2)

        def save():
            self.cfg['clean'] = {k: v.get() for k, v in vars_.items()}
            self._save_cfg()
            top.destroy()

        def reset():
            for k, v in vars_.items():
                v.set(CLEAN_DEFAULTS[k])
        row = ttk.Frame(body)
        row.pack(fill='x', pady=(14, 0))
        ttk.Button(row, text='Reset', command=reset).pack(side='left')
        ttk.Button(row, text='Save', command=save, style='Accent.TButton').pack(side='right')
        ttk.Button(row, text='Cancel', command=top.destroy).pack(side='right', padx=8)

    def open_replacements(self):
        top, body = self._dialog('Pronunciation / replacements', 520)
        ttk.Label(body, justify='left', style='Muted.TLabel', text=(
            'One per line:  word => how it should be said\n'
            'Examples:   Nairobi => Nye-robi      GPU => G P U      Mt. => Mount\n'
            'Whole words, any capitalisation. Applied every time text is cleaned.')).pack(
            anchor='w', pady=(0, 8))
        t = tk.Text(body, width=58, height=12, font=self.f_mono, bd=0, highlightthickness=1,
                    highlightbackground=self.P['border'], padx=10, pady=8, undo=True,
                    bg=self.P['text_bg'], fg=self.P['fg'], insertbackground=self.P['accent'],
                    selectbackground=self.P['select'])
        t.pack()
        t.insert('1.0', self.cfg.get('replacements', ''))

        def save():
            self.cfg['replacements'] = t.get('1.0', 'end-1c')
            self._save_cfg()
            top.destroy()
        row = ttk.Frame(body)
        row.pack(fill='x', pady=(12, 0))
        ttk.Button(row, text='Save', command=save, style='Accent.TButton').pack(side='right')
        ttk.Button(row, text='Cancel', command=top.destroy).pack(side='right', padx=8)

    def split_current(self):
        txt = self.text.get('1.0', 'end-1c').strip()
        if not txt:
            self.set_status('Nothing to split.')
            return
        self._open_split(clean_text(txt, self.clean_opts, finish=False,
                                    repl=self.cfg.get('replacements', '')), replace_current=True)

    def _open_split(self, text, replace_current):
        top, body = self._dialog('Split into parts', 520)
        total = len(text.split())
        ttk.Label(body, text=f'{total:,} words  (about {fmt_time(estimate_seconds(text))} of audio)',
                  style='H.TLabel').pack(anchor='w')
        row = ttk.Frame(body)
        row.pack(fill='x', pady=(12, 4))
        ttk.Label(row, text='Words per part').pack(side='left')
        words = tk.IntVar(value=int(self.cfg.get('split_words', 1200)))
        ttk.Spinbox(row, from_=100, to=20000, increment=100, textvariable=words,
                    width=7).pack(side='left', padx=10)
        chapters = tk.BooleanVar(value=bool(self.cfg.get('split_chapters', True)))
        ttk.Checkbutton(body, text='Start a new part at "Chapter / Part / Prologue ..." headings',
                        variable=chapters).pack(anchor='w', pady=4)
        gen_now = tk.BooleanVar(value=False)
        ttk.Checkbutton(body, text='Generate all parts right away',
                        variable=gen_now).pack(anchor='w', pady=4)
        info = ttk.Label(body, style='Muted.TLabel')
        info.pack(anchor='w', pady=(8, 0))

        def preview(*_):
            try:
                n = len(split_parts(text, max(50, words.get()), chapters.get()))
                info.configure(text=f'Will make {n} part{"s" if n != 1 else ""}.')
            except tk.TclError:
                pass
        words.trace_add('write', preview)
        chapters.trace_add('write', preview)
        preview()

        def go():
            try:
                w = max(50, int(words.get()))
            except tk.TclError:
                return
            pieces = split_parts(text, w, chapters.get())
            self.cfg['split_words'], self.cfg['split_chapters'] = w, chapters.get()
            top.destroy()
            self._apply_split(pieces, replace_current, gen_now.get())
        r2 = ttk.Frame(body)
        r2.pack(fill='x', pady=(14, 0))
        ttk.Button(r2, text='Split', command=go, style='Accent.TButton').pack(side='right')
        ttk.Button(r2, text='Cancel', command=top.destroy).pack(side='right', padx=8)

    def _apply_split(self, pieces, replace_current, gen_now):
        if not pieces:
            return
        self._sync_part_text()
        if self.mode == 'single':
            self.mode = 'parts'
            self._apply_mode()
        cur = self.sel
        created = []
        if cur is not None and (replace_current or not cur.text.strip()):
            self._set_editor_text(pieces[0])
            created.append(cur)
            rest = pieces[1:]
            at = self.parts.index(cur) + 1
        else:
            rest = pieces
            at = self.parts.index(cur) + 1 if cur in self.parts else len(self.parts)
        for k, txt in enumerate(rest):
            created.append(self._new_part(txt, select=False, index=at + k))
        self._renumber()
        self.set_status(f'Split into {len(pieces)} parts.')
        self._save_session_soon()
        if gen_now:
            for p in created:
                self.generate_part(p)

    def _show_shortcuts(self):
        messagebox.showinfo('Keyboard shortcuts', (
            'Ctrl+Enter           Generate this part\n'
            'Ctrl+Shift+Enter     Generate all parts\n'
            'Ctrl+V               Paste clean at cursor\n'
            'Ctrl+Shift+V         Replace everything with clipboard\n'
            'Ctrl+N               Paste clipboard as a new part\n'
            'Ctrl+Space           Play / pause\n'
            'Alt+Left / Right     Back / forward 5 seconds\n'
            'Alt+Shift+Left/Right Back / forward 10 seconds\n'
            'Ctrl+click in text   Jump playback to that sentence\n'
            'Ctrl+Z               Undo (also undoes Clean)\n'
            'Ctrl+F               Find and replace\n'
            'Ctrl + / - / 0       Bigger / smaller / reset text (or Ctrl+wheel)\n'
            'Alt+Up / Down        Move the selected parts up / down\n'
            'Alt+PageUp / Down    Open previous / next part\n'
            'In the parts list:   Ctrl+A select all, Del delete, right-click for more'))

    # ---------- keys ----------
    def _bind_keys(self):
        self.bind_all('<Control-Return>', lambda e: (self.generate_selected(), 'break')[1])
        self.bind_all('<Control-Shift-Return>', lambda e: (self.generate_all(), 'break')[1])
        self.bind_all('<Control-Shift-V>', lambda e: (self.paste_replace(), 'break')[1])
        self.bind_all('<Control-Shift-v>', lambda e: (self.paste_replace(), 'break')[1])
        self.bind_all('<Control-n>', lambda e: (self.paste_new_part(), 'break')[1])
        self.bind_all('<Control-space>', lambda e: (self.toggle_play(), 'break')[1])
        self.bind_all('<Alt-Left>', lambda e: (self.skip(-5), 'break')[1])
        self.bind_all('<Alt-Right>', lambda e: (self.skip(5), 'break')[1])
        self.bind_all('<Alt-Shift-Left>', lambda e: (self.skip(-10), 'break')[1])
        self.bind_all('<Alt-Shift-Right>', lambda e: (self.skip(10), 'break')[1])
        self.bind_all('<Control-f>', lambda e: (self.open_find(), 'break')[1])
        self.bind_all('<Control-equal>', lambda e: (self.zoom_text(1), 'break')[1])
        self.bind_all('<Control-plus>', lambda e: (self.zoom_text(1), 'break')[1])
        self.bind_all('<Control-minus>', lambda e: (self.zoom_text(-1), 'break')[1])
        self.bind_all('<Control-0>', lambda e: (self.zoom_text(0), 'break')[1])
        self.bind_all('<Alt-Up>', lambda e: (self.move_parts(-1), 'break')[1])
        self.bind_all('<Alt-Down>', lambda e: (self.move_parts(1), 'break')[1])
        self.bind_all('<Alt-Prior>', lambda e: (self.step_edit(-1), 'break')[1])
        self.bind_all('<Alt-Next>', lambda e: (self.step_edit(1), 'break')[1])

    # ---------- session ----------
    def _save_session_soon(self):
        if self._save_after:
            self.after_cancel(self._save_after)
        self._save_after = self.after(1500, self._save_session)

    def _save_session(self, force=False):
        self._save_after = None
        if not self.remember.get() and not force:
            return
        if not self.remember.get():
            return
        try:
            data = {'parts': [{'text': p.text, 'audio': str(p.audio) if p.audio else '',
                               'number': p.number, 'duration': p.duration}
                              for p in self.parts],
                    'selected': self.parts.index(self.sel) if self.sel in self.parts else 0}
            SESSION_FILE.write_text(json.dumps(data), encoding='utf-8')
        except Exception:
            pass

    def _load_session(self):
        data = {}
        if self.remember.get():
            try:
                data = json.loads(SESSION_FILE.read_text(encoding='utf-8'))
            except Exception:
                data = {}
        for d in data.get('parts', []):
            p = self._new_part(d.get('text', ''), select=False)
            p.number = d.get('number')
            a = d.get('audio')
            if a and Path(a).exists():
                p.audio, p.state, p.duration = Path(a), 'done', float(d.get('duration') or 0)
            self._refresh_row(p)
        if not self.parts:
            self._new_part('', select=False)
        i = min(int(data.get('selected', 0)), len(self.parts) - 1)
        self.select_part(self.parts[i])
        self._update_counts()

    def _forget_session(self):
        try:
            SESSION_FILE.unlink(missing_ok=True)
        except Exception:
            pass
        self.set_status('Saved parts forgotten (audio files are untouched).')

    # ---------- generate ----------
    def _prepare(self, text):
        return clean_text(text, self.clean_opts, repl=self.cfg.get('replacements', ''))

    def generate_selected(self):
        if self.sel:
            self.generate_part(self.sel)

    def generate_all(self):
        self._sync_part_text()
        n = 0
        for p in list(self.parts):
            if p.text.strip() and p.state not in ('queued', 'generating'):
                if self.generate_part(p, quiet=True):
                    n += 1
        self.set_status(f'Queued {n} part{"s" if n != 1 else ""}.')

    def generate_part(self, part, quiet=False):
        if part is self.sel:
            self._sync_part_text()
        if part.state in ('queued', 'generating'):
            return False
        text = self._prepare(part.text)
        if not text:
            if not quiet:
                self.set_status('Nothing to generate. Paste some text first.')
            return False
        part.text = text
        if part is self.sel:
            self._set_editor_text(text)
        job = Job(part, text, self.voice_id(), round(self.speed.get(), 2),
                  bool(self.mp3.get() and self.ffmpeg))
        part.job, part.state, part.progress, part.error = job, 'queued', 0.0, ''
        if self.pending == 0:
            self._batch_total = self._batch_done = 0
        self._batch_total += 1
        self.pending += 1
        self.jobs_q.put(job)
        self._refresh_row(part)
        self._update_progress_ui()
        self._update_counts()
        self._save_cfg()
        if not quiet:
            self.set_status('Queued.')
        if self.mode == 'single' and part is self.sel:
            self._sync_part_text()
            self._new_part('', index=self.parts.index(part) + 1)
            self.text.focus_set()
        return True

    def cancel_part(self, part):
        if part.job and part.state in ('queued', 'generating'):
            part.job.cancel.set()
            if part.state == 'queued':
                part.state = 'idle'
                self._refresh_row(part)
                self._update_progress_ui()

    def cancel_selected(self):
        if self.sel:
            self.cancel_part(self.sel)

    def cancel_all(self):
        for p in self.parts:
            self.cancel_part(p)
        self.set_status('Cancelled the queue.')

    def _update_progress_ui(self):
        p = self.sel
        if not p:
            return
        if p.state == 'generating':
            self.pbar.configure(value=p.progress * 100)
            self.prog_lbl.configure(text=f'{int(p.progress * 100)}%   {p.eta}', foreground='')
        elif p.state == 'queued':
            self.pbar.configure(value=0)
            self.prog_lbl.configure(text='Waiting in queue ...')
        elif p.state == 'done':
            self.pbar.configure(value=100)
            self.prog_lbl.configure(text=f'Done  {fmt_time(p.duration)} of audio')
        elif p.state == 'error':
            self.pbar.configure(value=0)
            self.prog_lbl.configure(text='Failed. ' + p.error.splitlines()[0][:40])
        else:
            self.pbar.configure(value=0)
            self.prog_lbl.configure(text='')
        self._update_part_label()

    # ---------- worker ----------
    def _worker(self):
        while True:
            job = self.jobs_q.get()
            part = job.part
            try:
                if job.cancel.is_set():
                    continue
                self._run_job(job)
            except Cancelled:
                part.state = 'idle'
                self.set_status('Cancelled.')
            except Exception as e:
                part.state, part.error = 'error', str(e) or repr(e)
                self.set_status('Generation failed (double-click the part for details).')
            finally:
                def fin(part=part):
                    self.pending = max(0, self.pending - 1)
                    self._batch_done += 1
                    self._refresh_row(part)
                    if part is self.sel:
                        self._update_progress_ui()
                    self._update_counts()
                self.ui(fin)

    def _pick_number(self, part):
        n = part.number
        if n:
            pref = f'{n:03d}.'
            try:
                clash = any(p.name.startswith(pref) and p != part.audio
                            for p in self.out_dir.iterdir())
            except OSError:
                clash = False
            if not clash:
                return n
        return next_number(self.out_dir)

    def _run_job(self, job):
        part = job.part
        be = self.backend
        if not be.ready.is_set():
            self.set_status('Waiting for the engine ...')
            while not be.ready.wait(0.4):
                if job.cancel.is_set():
                    raise Cancelled()
        part.state, part.progress, part.eta = 'generating', 0.0, ''
        self.ui(lambda: (self._refresh_row(part), self._update_progress_ui()))
        t0 = time.time()
        chunks = chunk_text(job.text, be.max_chars)
        if not chunks:
            raise RuntimeError('No speakable text found.')
        total = sum(len(c.text) for c in chunks)
        pcm, mp, t, sr, done = [], [], 0.0, None, 0
        for i, c in enumerate(chunks):
            if job.cancel.is_set():
                raise Cancelled()
            if not re.search(r'\w', c.text):
                done += len(c.text)
                continue
            self.set_status(f'Generating part ... sentence {i + 1} of {len(chunks)}')
            data, sr_i = be.synth(c.text, job.voice, job.speed)
            if sr is None:
                sr = sr_i
            dur = len(data) / 2 / sr
            last = i == len(chunks) - 1
            gap = 0.35 if last else (be.gap_para if c.para_end else be.gap_sentence)
            pcm.append(data)
            pcm.append(b'\x00\x00' * int(sr * gap))
            mp.append((t, t + dur + gap, c.a, c.b))
            t += dur + gap
            done += len(c.text)
            frac = done / total
            elapsed = time.time() - t0
            eta = elapsed * (1 - frac) / frac if frac > 0 else 0
            part.progress = frac
            part.eta = f'about {fmt_time(eta)} left' if frac < 1 else ''
            self.ui(lambda p=part: (self._refresh_row(p),
                                    self._update_progress_ui() if p is self.sel else None))
        if job.cancel.is_set():
            raise Cancelled()
        if sr is None:
            raise RuntimeError('No speakable text found.')
        audio = b''.join(pcm)
        self.out_dir.mkdir(parents=True, exist_ok=True)
        num = self._pick_number(part)
        stem = f'{num:03d}.{be.short(job.voice)}.{datetime.now():%Y-%m-%d}.{job.slug}'
        wav = self.out_dir / f'{stem}.wav'
        write_wav(wav, audio, sr)
        final, note = wav, ''
        if job.mp3:
            self.set_status('Encoding MP3 ...')
            mp3 = wav.with_suffix('.mp3')
            try:
                subprocess.run([self.ffmpeg, '-y', '-loglevel', 'error', '-i', str(wav),
                                '-codec:a', 'libmp3lame', '-qscale:a', '4', str(mp3)],
                               check=True, creationflags=NO_WINDOW)
                wav.unlink(missing_ok=True)
                final = mp3
            except Exception:
                note = ' (MP3 failed, kept WAV)'
        old = part.audio
        if (self.replace_old.get() and old and Path(old).exists() and Path(old) != final
                and Path(old).parent == self.out_dir):
            try:
                Path(old).unlink()
            except OSError:
                pass
        part.audio, part.number, part.duration = final, num, len(audio) / 2 / sr
        part.map, part.map_text = mp, job.text
        part.starts = [m[0] for m in mp]
        part.state, part.progress = 'done', 1.0
        self.set_status(f'Saved {final.name}{note}')

        def after():
            be.after_job()
            if self.mode == 'single' and self.player.state == 'stopped' and not self._loading_audio:
                self._play_part(part, autoplay=False)
            self._save_session_soon()
        self.ui(after)

    # ---------- player ----------
    def _play_part(self, part, start=0.0, autoplay=True):
        if not part.audio or not Path(part.audio).exists():
            self.set_status('This part has no audio yet. Generate it first.')
            return
        path = str(part.audio)
        if self.player.path == path and self.player.loaded:
            self._after_load(part, None, None, start, autoplay)
            return
        self._loading_audio = True
        self.set_status('Loading audio ...')

        def work():
            try:
                pcm, sr = load_pcm_file(path, self.ffmpeg)
                self.ui(lambda: self._after_load(part, pcm, sr, start, autoplay))
            except Exception as e:
                err = str(e)
                self._loading_audio = False
                self.ui(lambda: messagebox.showerror('Audio', err[-800:]))
        threading.Thread(target=work, daemon=True).start()

    def _after_load(self, part, pcm, sr, start, autoplay):
        self._loading_audio = False
        try:
            if pcm is not None:
                self.player.load(pcm, sr, part.audio)
            self.player_part = part
            self._hl_idx = None
            self.now_lbl.configure(text=f'Part {self.parts.index(part) + 1 if part in self.parts else "?"}'
                                        f'   {Path(part.audio).name}')
            self.dur_lbl.configure(text=fmt_time(self.player.duration))
            self.seek.configure(to=max(1.0, self.player.duration))
            if autoplay:
                self.player.play(start)
            else:
                self.player.seek(start)
            self.set_status('Playing.' if autoplay else 'Loaded. Press Play.')
        except Exception as e:
            messagebox.showerror('Audio', f'Could not start playback.\n\n{e}\n\n'
                                          'Is pygame installed in this environment?')

    def listen_selected(self):
        if not self.sel:
            return
        if self.sel.state == 'error':
            self.part_error_dialog()
        else:
            self._play_part(self.sel)

    def toggle_play(self):
        if self.player.loaded:
            self.player.toggle()
        elif self.sel:
            self._play_part(self.sel)

    def stop_play(self):
        self.player.stop()
        self._clear_reading()

    def skip(self, delta):
        if self.player.loaded:
            self.player.skip(delta)
        elif self.sel and self.sel.audio:
            self._play_part(self.sel, autoplay=False)

    def step_part(self, d):
        if not self.parts:
            return
        cur = self.player_part if self.player_part in self.parts else self.sel
        i = self.parts.index(cur)
        j = i + d
        while 0 <= j < len(self.parts):
            if self.parts[j].audio:
                self.select_part(self.parts[j])
                self._play_part(self.parts[j])
                return
            j += d
        self.set_status('No more generated parts that way.')

    def _seek_frac(self, event):
        w = max(1, self.seek.winfo_width() - 20)
        return max(0.0, min(1.0, (event.x - 10) / w))

    def _seek_press(self, event):
        self._dragging = True
        self.seek_var.set(self._seek_frac(event) * self.player.duration)
        return 'break'

    def _seek_drag(self, event):
        self.seek_var.set(self._seek_frac(event) * self.player.duration)
        self.time_lbl.configure(text=fmt_time(self.seek_var.get()))
        return 'break'

    def _seek_release(self, event):
        self._dragging = False
        if self.player.loaded:
            self.player.seek(self._seek_frac(event) * self.player.duration)
        return 'break'

    def _ctrl_click(self, event):
        part = self.sel
        if not part or not part.map_valid:
            return None
        off = self._offset(self.text.index(f'@{event.x},{event.y}'))
        k = 0
        for n, (t0, t1, a, b) in enumerate(part.map):
            if a <= off:
                k = n
        t = part.map[k][0]
        if self.player_part is part and self.player.loaded:
            self.player.seek(t)
            if self.player.state != 'playing':
                self.player.play(t)
        else:
            self._play_part(part, start=t)
        return 'break'

    def _clear_reading(self):
        self.text.tag_remove('reading', '1.0', 'end')
        self._hl_idx = None

    def _tick(self):
        pl = self.player
        try:
            if pl.loaded:
                pos = pl.position()
                if not self._dragging:
                    self.seek_var.set(pos)
                    self.time_lbl.configure(text=fmt_time(pos))
                self.play_btn.configure(text='Pause' if pl.state == 'playing' else 'Play')
                if pl.poll_ended():
                    self._on_play_end()
                self._update_reading(pos)
            else:
                self.play_btn.configure(text='Play')
        finally:
            self.after(200, self._tick)

    def _update_reading(self, pos):
        part = self.player_part
        if (not self.follow.get() or part is None or part is not self.sel
                or self.player.state == 'stopped' or not part.map_valid):
            if self._hl_idx is not None:
                self._clear_reading()
            return
        k = max(0, bisect.bisect_right(part.starts, pos) - 1)
        if k != self._hl_idx:
            self._hl_idx = k
            a, b = part.map[k][2], part.map[k][3]
            self.text.tag_remove('reading', '1.0', 'end')
            self.text.tag_add('reading', f'1.0+{a}c', f'1.0+{b}c')
            self.text.see(f'1.0+{a}c')

    def _on_play_end(self):
        self.seek_var.set(0)
        self.time_lbl.configure(text='00:00')
        self._clear_reading()
        if self.autonext.get() and self.player_part in self.parts:
            i = self.parts.index(self.player_part)
            for p in self.parts[i + 1:]:
                if p.audio:
                    self.select_part(p)
                    self._play_part(p)
                    return
        self.set_status('Finished.')

    # ---------- thread-safe helpers ----------
    def ui(self, fn):
        self.ui_q.put(fn)

    def set_status(self, msg):
        self.ui(lambda: self.status.set(msg))

    def _pump(self):
        try:
            while True:
                self.ui_q.get_nowait()()
        except queue.Empty:
            pass
        except Exception:
            traceback.print_exc()
        self.after(80, self._pump)

    # ---------- misc ----------
    def _open_output(self):
        self.out_dir.mkdir(parents=True, exist_ok=True)
        try:
            os.startfile(self.out_dir)
        except AttributeError:
            subprocess.Popen(['xdg-open', str(self.out_dir)])

    def _change_output(self):
        d = filedialog.askdirectory(parent=self, title='Output folder',
                                    initialdir=str(self.out_dir))
        if d:
            self.out_dir = Path(d)
            self._save_cfg()
            self.set_status(f'Output folder: {d}')

    def part_error_dialog(self):
        p = self.sel
        if p and p.state == 'error':
            messagebox.showerror('Generation failed', p.error[-1500:])

# ============================================================
#  PHONON BACKEND
#  Phonon-31M English (Gradium, Apache 2.0) through Hugging Face
#  Transformers + PyTorch on the CPU.  Every name below was read
#  out of the upstream sources:
#    transformers  models/gradium_phonon_tts + models/pocket_tts
#    gradium-ai/xn-ptts  (voice catalog format, duration_delta)
# ============================================================
MODEL_REPO = 'gradium/phonon-31m-en'
MIMI_REPO = 'gradium/phonon-mimi'          # the audio decoder processor_config.json points to
VOICES_REPO = 'gradium/phonon-voices'      # catalog: voices.jsonl + voices/<id>.safetensors
CACHE_DIR = ROOT / 'hf_cache'              # everything downloaded lives next to the script
READY_FLAG = CACHE_DIR / 'phonon_ready.txt'
TRANSFORMERS_ZIP = 'https://github.com/huggingface/transformers/archive/refs/heads/main.zip'

# The 31m repo also holds two GGUF files for the Rust runtime; we do not need them.
MODEL_PATTERNS = ['config.json', 'generation_config.json', 'model.safetensors',
                  'processor_config.json', 'chat_template.jinja', 'tokenizer*',
                  'default-voice.safetensors']
MIMI_PATTERNS = ['*.json', '*.safetensors', '*.jinja', '*.txt', '*.model']

MISSING_MSG = ('The Phonon model files are not downloaded yet.\n\n'
               'Close this app and double-click  phonon_pro.bat  once. It downloads them '
               'into the hf_cache folder next to this script. After that, use phonon_pro.vbs.')

# The packages the .bat installs (the app never installs anything itself).
PIP_NAMES = 'numpy soundfile pygame safetensors huggingface_hub torch'

SAMPLE_RATE_FALLBACK = 24000
PAD_MS = 150            # silence returned for text with nothing speakable
PIECE_GAP = 0.12        # seconds between the sub-pieces of one GUI chunk
BENCH_TEXT = ("The quick brown fox jumps over the lazy dog. This sentence is here to "
              "measure how fast the model can speak on this exact machine, right now.")

torch = None
np = None
load_file = None
AutoProcessor = None
PhononModel = None


def _prepare_env(offline):
    """HF reads these when it is imported, so call this before importing it."""
    os.environ['HF_HUB_CACHE'] = str(CACHE_DIR)
    os.environ['HF_HUB_DISABLE_SYMLINKS_WARNING'] = '1'
    os.environ['HF_HUB_DISABLE_TELEMETRY'] = '1'
    if offline:
        os.environ['HF_HUB_OFFLINE'] = '1'
        os.environ['TRANSFORMERS_OFFLINE'] = '1'
    else:
        os.environ.pop('HF_HUB_OFFLINE', None)
        os.environ.pop('TRANSFORMERS_OFFLINE', None)


def import_runtime():
    global torch, np, load_file, AutoProcessor, PhononModel
    if torch is None:
        import numpy as _np
        import torch as _torch
        from safetensors.torch import load_file as _load_file
        try:
            from transformers import AutoProcessor as _AP
            from transformers import GradiumPhononTTSForConditionalGeneration as _PM
        except ImportError as e:
            raise RuntimeError(
                'The installed "transformers" is too old for Phonon (it needs the GitHub main '
                'version). Double-click phonon_pro.bat to fix it.\n\n' + str(e))
        np, torch, load_file, AutoProcessor, PhononModel = _np, _torch, _load_file, _AP, _PM


# ---------------- voice catalog ----------------
def read_catalog(path):
    """voices.jsonl: one JSON object per line: name, filename and (optionally) voice_id,
    language, locale, description  (format taken from ptts/src/voice_catalog.rs)."""
    out = []
    for line in Path(path).read_text(encoding='utf-8').splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if not isinstance(d, dict):
            continue
        vid = d.get('voice_id')
        fn = d.get('filename') or (f'voices/{vid}.safetensors' if vid else None)
        name = d.get('name') or vid
        if not fn or not name:
            continue
        out.append(dict(name=str(name), filename=str(fn), voice_id=str(vid or ''),
                        language=str(d.get('language') or ''), locale=str(d.get('locale') or ''),
                        description=str(d.get('description') or '').strip()))
    return out


def english_voices(entries):
    """This checkpoint is English only. If the catalog carries no language info at all,
    keep everything rather than show an empty list."""
    en = [e for e in entries
          if e['language'].lower().startswith('en') or e['locale'].lower().startswith('en')]
    return en or entries


_LAST_ERR = ''


def _local_file(repo, filename):
    """Path of a cached file, or None. Never touches the network."""
    global _LAST_ERR
    try:
        from huggingface_hub import hf_hub_download
        return hf_hub_download(repo, filename, cache_dir=str(CACHE_DIR), local_files_only=True)
    except Exception as e:
        _LAST_ERR = f'{repo}/{filename}: {type(e).__name__}: {str(e)[:200]}'
        return None


def local_voice_table():
    """[(key, label, path)] for every English catalog voice that is on disk, plus the
    checkpoint's own default voice first."""
    rows = []
    d = _local_file(MODEL_REPO, 'default-voice.safetensors')
    if d:
        rows.append(('Default', 'Default   -   checkpoint voice', d))
    cat = _local_file(VOICES_REPO, 'voices.jsonl')
    if cat:
        used = {'Default'}
        entries = sorted(english_voices(read_catalog(cat)), key=lambda e: e['name'].lower())
        for e in entries:
            p = _local_file(VOICES_REPO, e['filename'])
            if not p:
                continue
            key = re.sub(r'[^\w\-]', '', e['name']) or e['voice_id'] or 'voice'
            if key in used:
                key = f"{key}-{(e['voice_id'] or 'x')[:4]}"
            used.add(key)
            label = f"{e['name']}   -   {e['locale'] or e['language'] or 'en'}"
            if e['description'] and len(e['description']) <= 40:
                label += f", {e['description']}"
            rows.append((key, label, p))
    return rows


def check_files():
    """(ok, reason). The reason goes into the error dialog so a failure explains itself.
    The model/decoder files themselves are checked by the real load, which reports its own errors."""
    if not READY_FLAG.exists():
        return False, f'flag file not found: {READY_FLAG}'
    try:
        cat = _local_file(VOICES_REPO, 'voices.jsonl')
        if not cat:
            return False, f'voices.jsonl not found in {CACHE_DIR}  ({_LAST_ERR})'
        n = len(english_voices(read_catalog(cat)))
        if not local_voice_table():
            return False, f'{n} English voices in the catalog, 0 found on disk  ({_LAST_ERR})'
    except Exception as e:
        return False, f'{type(e).__name__}: {e}'
    return True, ''


def files_ready():
    return check_files()[0]


def download_models():
    """python phonon_studio.py --download   (run by the .bat, needs internet)."""
    _prepare_env(offline=False)
    try:
        from huggingface_hub import snapshot_download, hf_hub_download
    except ImportError as e:
        print('[X] huggingface_hub is not installed:', e)
        return 1
    CACHE_DIR.mkdir(parents=True, exist_ok=True)
    try:
        print(f'[*] Downloading {MODEL_REPO} (about 103 MB) ...')
        snapshot_download(MODEL_REPO, cache_dir=str(CACHE_DIR), allow_patterns=MODEL_PATTERNS)
        print(f'[*] Downloading {MIMI_REPO} (audio decoder) ...')
        snapshot_download(MIMI_REPO, cache_dir=str(CACHE_DIR), allow_patterns=MIMI_PATTERNS)
        print(f'[*] Downloading the voice list from {VOICES_REPO} ...')
        cat = hf_hub_download(VOICES_REPO, 'voices.jsonl', cache_dir=str(CACHE_DIR))
        entries = english_voices(read_catalog(cat))
        ok = 0
        for i, e in enumerate(entries, 1):
            print(f'    voice {i}/{len(entries)}: {e["name"]}')
            try:
                hf_hub_download(VOICES_REPO, e['filename'], cache_dir=str(CACHE_DIR))
                ok += 1
            except Exception as ex:
                print(f'    [!] skipped {e["name"]}: {ex}')
        if ok == 0:
            print('[X] No voice could be downloaded.')
            return 1
    except Exception as e:
        print(f'[X] Download failed: {e}')
        return 1
    READY_FLAG.write_text('ok\n', encoding='ascii')
    print('[*] All model files are in:', CACHE_DIR)
    return 0


# ---------------- text prep (the model does not read numbers or symbols) ----------------
_ONES = ('zero one two three four five six seven eight nine ten eleven twelve thirteen '
         'fourteen fifteen sixteen seventeen eighteen nineteen').split()
_TENS = 'zero ten twenty thirty forty fifty sixty seventy eighty ninety'.split()
_SCALES = ((10 ** 12, 'trillion'), (10 ** 9, 'billion'), (10 ** 6, 'million'), (10 ** 3, 'thousand'))
_ORD_IRREG = {'one': 'first', 'two': 'second', 'three': 'third', 'five': 'fifth',
              'eight': 'eighth', 'nine': 'ninth', 'twelve': 'twelfth'}
_CURRENCY = {'$': ('dollar', 'dollars', 'cent', 'cents'), '€': ('euro', 'euros', 'cent', 'cents'),
             '£': ('pound', 'pounds', 'penny', 'pence')}


def _int_words(n):
    if n < 0:
        return 'minus ' + _int_words(-n)
    if n < 20:
        return _ONES[n]
    if n < 100:
        t, o = divmod(n, 10)
        return _TENS[t] + ('-' + _ONES[o] if o else '')
    if n < 1000:
        h, r = divmod(n, 100)
        return _ONES[h] + ' hundred' + (' ' + _int_words(r) if r else '')
    for val, name in _SCALES:
        if n >= val:
            q, r = divmod(n, val)
            return _int_words(q) + ' ' + name + (' ' + _int_words(r) if r else '')
    return str(n)


def _digits_words(s):
    return ' '.join(_ONES[int(c)] for c in s if c.isdigit())


def _number_words(s):
    """s: digits only (commas already removed)."""
    if len(s) > 15 or (len(s) > 1 and s.startswith('0')):
        return _digits_words(s)
    return _int_words(int(s))


def _year_words(y):
    if 2000 <= y <= 2009:
        return 'two thousand' + (' ' + _ONES[y % 100] if y % 100 else '')
    a, b = divmod(y, 100)
    if b == 0:
        return _int_words(a) + ' hundred'
    return _int_words(a) + ' ' + ('oh ' + _ONES[b] if b < 10 else _int_words(b))


def _ordinal_words(n):
    words = _int_words(n)
    head, sep, last = words.rpartition(' ')
    head2, dash, last2 = last.rpartition('-')
    base = last2
    if base in _ORD_IRREG:
        new = _ORD_IRREG[base]
    elif base.endswith('y'):
        new = base[:-1] + 'ieth'
    else:
        new = base + 'th'
    return head + sep + head2 + dash + new


_COMMA_NUM = r'\d{1,3}(?:,\d{3})+|\d+'
_RE_EMAIL = re.compile(r'\b[\w.+-]+@[\w-]+(?:\.[\w-]+)+\b')
_RE_URL = re.compile(r'\b(?:https?://)?(?:www\.)?[\w-]+(?:\.[\w-]+)*\.(?:com|org|net|io|ai|co|edu|gov|dev|app)\b(?:/[^\s]*)?',
                     re.I)
_RE_MONEY = re.compile(r'([$€£])\s?(' + _COMMA_NUM + r')(?:\.(\d{1,2}))?'
                       r'(?:\s?(thousand|million|billion|trillion)\b)?', re.I)
_RE_PERCENT = re.compile(r'(?<![\w.])(' + _COMMA_NUM + r')(?:\.(\d+))?\s?%')
_RE_ORDINAL = re.compile(r'(?<![\w.])(\d{1,12})(?:st|nd|rd|th)\b', re.I)
_RE_TIME = re.compile(r'(?<![\w:.])(\d{1,2}):(\d{2})\s?(a\.?m\.?|p\.?m\.?)?(?![\w:])', re.I)
_RE_NUMBER = re.compile(r'(?<![\w.])(-)?(' + _COMMA_NUM + r')(?:\.(\d+))?(?![\w])')
_ABBR = ((re.compile(r'\bMr\.'), 'Mister'), (re.compile(r'\bMrs\.'), 'Missus'),
         (re.compile(r'\bMs\.'), 'Miss'), (re.compile(r'\bDr\.'), 'Doctor'))


def _clean_commas(s):
    return s.replace(',', '')


def _money(m):
    sym, whole, cents, scale = m.group(1), m.group(2), m.group(3), m.group(4)
    one, many, c_one, c_many = _CURRENCY[sym]
    w = _clean_commas(whole)
    if scale:
        return f'{_number_words(w)} {scale.lower()} {many}'
    n = int(w) if len(w) <= 15 else 0
    out = f'{_number_words(w)} {one if n == 1 else many}'
    if cents:
        c = int((cents + '0')[:2])
        if c:
            out += f' and {_int_words(c)} {c_one if c == 1 else c_many}'
    return out


def _percent(m):
    out = _number_words(_clean_commas(m.group(1)))
    if m.group(2):
        out += ' point ' + _digits_words(m.group(2))
    return out + ' percent'


def _time(m):
    h, mi, ap = int(m.group(1)), int(m.group(2)), m.group(3)
    if h > 24 or mi > 59:
        return m.group(0)
    words = _int_words(h)
    if mi == 0:
        words += '' if ap else " o'clock"
    elif mi < 10:
        words += ' oh ' + _ONES[mi]
    else:
        words += ' ' + _int_words(mi)
    if ap:
        words += ' ' + ('A M' if ap.lower().startswith('a') else 'P M')
    return words


def _number(m):
    neg, whole, frac = m.group(1), m.group(2), m.group(3)
    plain = _clean_commas(whole)
    if not frac and not neg and ',' not in whole and len(plain) == 4 and 1100 <= int(plain) <= 2099:
        return _year_words(int(plain))
    out = _number_words(plain)
    if frac:
        out += ' point ' + _digits_words(frac)
    return ('minus ' + out) if neg else out


def normalize_en(text):
    """Spell out what the model cannot read: numbers, money, percents, times, ordinals,
    emails and urls, a few symbols. Everything else is left alone."""
    t = text
    for rx, rep in _ABBR:
        t = rx.sub(rep, t)
    t = _RE_EMAIL.sub(lambda m: m.group(0).replace('@', ' at ').replace('.', ' dot '), t)
    t = _RE_URL.sub(lambda m: re.sub(r'^https?://', '', m.group(0), flags=re.I)
                    .replace('.', ' dot ').replace('/', ' slash '), t)
    t = _RE_MONEY.sub(_money, t)
    t = _RE_PERCENT.sub(_percent, t)
    t = _RE_ORDINAL.sub(lambda m: _ordinal_words(int(m.group(1))), t)
    t = _RE_TIME.sub(_time, t)
    t = _RE_NUMBER.sub(_number, t)
    t = t.replace('°C', ' degrees Celsius').replace('°F', ' degrees Fahrenheit')
    t = t.replace('°', ' degrees ')
    t = re.sub(r'\s&\s', ' and ', t)
    t = re.sub(r'(?<=\w)\s?\+\s?(?=\w)', ' plus ', t)
    t = re.sub(r'(?<=\w)\s?=\s?(?=\w)', ' equals ', t)
    t = re.sub(r'#(?=\d)', 'number ', t)
    t = re.sub(r'@', ' at ', t)
    return re.sub(r'[ \t]+', ' ', t).strip()


def speed_to_delta(speed):
    """The GUI slider is 0.6x .. 1.6x. Phonon has no 'speed', it has the duration_delta
    condition: negative = faster, positive = slower, 0 = default, and small values work
    best (ptts docs). This mapping is approximate, not calibrated."""
    return max(-0.3, min(0.3, (1.0 - float(speed)) * 0.5))


def _hard_split(piece, limit=240):
    """Safety net for a piece with no punctuation at all."""
    out, cur = [], ''
    for w in piece.split(' '):
        if cur and len(cur) + 1 + len(w) > limit:
            out.append(cur)
            cur = w
        else:
            cur = f'{cur} {w}'.strip()
    if cur:
        out.append(cur)
    return out


def pcm16(audio):
    """float audio (any shape) -> mono int16 little-endian bytes, clipped."""
    a = np.nan_to_num(np.asarray(audio, dtype=np.float32).reshape(-1), nan=0.0,
                      posinf=1.0, neginf=-1.0)
    a = np.clip(a, -1.0, 1.0)
    return (a * 32767.0).astype('<i2').tobytes()


@dataclass
class BenchRow:
    threads: int
    ok: bool
    warm_s: float = 0.0
    audio_s: float = 0.0
    rtf: float = 0.0
    error: str = ''


class PhononEngine:
    def __init__(self, status=lambda m: None):
        self.status = status
        self.proc = None
        self.model = None
        self.sample_rate = SAMPLE_RATE_FALLBACK
        self.threads = 1
        self.voices = {}       # key -> (label, path)
        self._voice_cache = {}
        self._lock = threading.Lock()
        self.load_s = 0.0

    # ---- lifecycle ----
    def load(self, threads):
        t0 = time.time()
        self.set_threads(threads)
        self.status('Loading Phonon processor + decoder ...')
        self.proc = AutoProcessor.from_pretrained(MODEL_REPO)
        self.status('Loading Phonon model ...')
        try:
            model = PhononModel.from_pretrained(MODEL_REPO, dtype=torch.float32)
        except TypeError:
            model = PhononModel.from_pretrained(MODEL_REPO, torch_dtype=torch.float32)
        model.eval()
        self.model = model
        self.sample_rate = int(getattr(getattr(self.proc, 'feature_extractor', None),
                                       'sampling_rate', SAMPLE_RATE_FALLBACK)
                               or SAMPLE_RATE_FALLBACK)
        self.voices = {k: (lab, p) for k, lab, p in local_voice_table()}
        if not self.voices:
            raise FileNotFoundError(MISSING_MSG)
        self.load_s = time.time() - t0

    def set_threads(self, n):
        n = max(1, int(n))
        torch.set_num_threads(n)
        self.threads = n

    def voice_list(self):
        return [(k, lab) for k, (lab, _) in self.voices.items()]

    def _voice_tensor(self, key):
        if key not in self.voices:
            key = next(iter(self.voices))
        if key not in self._voice_cache:
            d = load_file(self.voices[key][1])
            t = d['speaker_wavs'] if 'speaker_wavs' in d else next(iter(d.values()))
            if t.ndim == 3:
                t = t[0].T                      # (1, 512, frames) -> (frames, 512), as the docs do
            elif t.ndim == 2 and t.shape[-1] != 512 and t.shape[0] == 512:
                t = t.T
            self._voice_cache[key] = t.float().contiguous()
        return self._voice_cache[key]

    # ---- synthesis ----
    def _one_piece(self, text, voice):
        conv = [{'role': 'user', 'content': [{'type': 'audio'}, {'type': 'text', 'text': text}]}]
        inputs = self.proc.apply_chat_template(
            conv, tokenize=True, return_dict=True, add_generation_prompt=True,
            processor_kwargs={'audio_prompt_latents': [voice]}).to(self.model.device)
        with torch.inference_mode():
            out = self.model.generate(**inputs)
            if isinstance(out, (list, tuple)):          # return_dict_in_generate was off
                wav = self.proc.decode(out[0])
            else:
                wav = self.proc.decode(out.audio_latents, out.audio_latents_mask)
        if isinstance(wav, (list, tuple)):
            wav = wav[0]
        a = wav.detach().float().cpu().numpy()
        if a.ndim > 1 and a.shape[0] > 1:           # stereo / multi-channel -> mono
            a = a.reshape(a.shape[0], -1).mean(axis=0)
        return a.reshape(-1)

    def synth_float(self, text, key, speed=1.0):
        """-> float32 mono numpy array at self.sample_rate. Thread-safe (one at a time)."""
        prep = normalize_en(text)
        sr = self.sample_rate
        if not re.search(r'[A-Za-z0-9]', prep):
            return np.zeros(int(sr * PAD_MS / 1000), dtype=np.float32)
        try:
            pieces = [p for p in self.proc.split_text(prep) if re.search(r'[A-Za-z0-9]', p)]
        except Exception:
            pieces = []
        pieces = pieces or [prep]
        flat = []
        for p in pieces:
            flat += _hard_split(p) if len(p) > 400 else [p]
        with self._lock:
            self.model.config.duration_delta = speed_to_delta(speed)
            voice = self._voice_tensor(key)
            parts = []
            for i, p in enumerate(flat):
                if i:
                    parts.append(np.zeros(int(sr * PIECE_GAP), dtype=np.float32))
                parts.append(self._one_piece(p, voice))
        return np.concatenate(parts) if parts else np.zeros(1, dtype=np.float32)

    def benchmark(self, key, thread_counts):
        rows = []
        saved = self.threads
        self.status('Benchmark: warm-up run ...')
        t0 = time.time()
        a = self.synth_float(BENCH_TEXT, key, 1.0)
        cold = time.time() - t0
        audio_s = len(a) / self.sample_rate
        try:
            for n in thread_counts:
                self.status(f'Benchmark: {n} thread(s) ...')
                try:
                    self.set_threads(n)
                    t0 = time.time()
                    b = self.synth_float(BENCH_TEXT, key, 1.0)
                    warm = time.time() - t0
                    dur = len(b) / self.sample_rate
                    rows.append(BenchRow(n, True, warm, dur, dur / warm if warm else 0.0))
                except Exception as e:
                    rows.append(BenchRow(n, False, error=str(e)))
        finally:
            self.set_threads(saved)
        return rows, cold, audio_s

    @staticmethod
    def format_bench(rows, load_s, cold_s):
        lines = [f'model load: {load_s:5.1f}s     first (cold) run: {cold_s:5.1f}s', '',
                 'threads     time    audio    speed']
        for r in rows:
            if r.ok:
                lines.append(f'{r.threads:<7} {r.warm_s:7.1f}s {r.audio_s:6.1f}s  '
                             f'{r.rtf:5.2f}x realtime')
            else:
                lines.append(f'{r.threads:<7} FAILED: {r.error[:80]}')
        ok = [r for r in rows if r.ok]
        if ok:
            best = max(ok, key=lambda r: r.rtf)
            lines += ['', f'Fastest: {best.threads} thread(s), {best.rtf:.2f}x realtime']
            if best.rtf < 1.0:
                lines.append('Below 1.0x: slower than the audio it makes (fine for batch).')
        return '\n'.join(lines)


class Backend:
    name = 'Phonon'
    default_voice = 'Default'
    max_chars = 200            # ~50 tokens, the chunk size the model was built around
    gap_sentence = 0.12
    gap_para = 0.50

    def __init__(self, app):
        self.app = app
        _prepare_env(offline=True)
        self.ready = threading.Event()
        self.engine = None
        self.loading = False
        self.cores = max(1, os.cpu_count() or 1)
        try:
            t = int(app.cfg.get('threads', self.cores))
        except (TypeError, ValueError):
            t = self.cores
        self.threads_var = tk.IntVar(value=max(1, min(self.cores, t)))

    @staticmethod
    def deps_missing():
        miss = [m for m in ('torch', 'transformers', 'numpy', 'safetensors',
                            'huggingface_hub', 'pygame')
                if importlib.util.find_spec(m) is None]
        return miss, PIP_NAMES + ' ' + TRANSFORMERS_ZIP

    def short(self, voice):
        return re.sub(r'[^\w\-]', '', voice)

    # ---- UI hooks ----
    def build_controls(self, card):
        eng = ttk.Frame(card, style='CardInner.TFrame')
        eng.columnconfigure(4, weight=1)
        ttk.Label(eng, text='Engine', style='Card.TLabel').grid(row=0, column=0, sticky='w')
        ttk.Label(eng, text='CPU', style='CardMuted.TLabel').grid(row=0, column=1, padx=(10, 14))
        ttk.Label(eng, text='Threads', style='Card.TLabel').grid(row=0, column=2)
        ttk.Spinbox(eng, from_=1, to=self.cores, textvariable=self.threads_var, width=3,
                    style='Card.TSpinbox', font=self.app.f_ui).grid(row=0, column=3, padx=(8, 14))
        btns = ttk.Frame(eng, style='CardInner.TFrame')
        btns.grid(row=0, column=4, sticky='w')
        self.reload_btn = ttk.Button(btns, text='Apply / reload', command=self.reload)
        self.reload_btn.grid(row=0, column=0, padx=(0, 8))
        self.bench_btn = ttk.Button(btns, text='Benchmark', command=self.run_benchmark)
        self.bench_btn.grid(row=0, column=1)
        self.engine_lbl = ttk.Label(eng, text='Engine: loading ...', style='CardMuted.TLabel')
        self.engine_lbl.grid(row=0, column=5, sticky='e')
        return eng

    def comboboxes(self, voice_box):
        return [voice_box]

    def apply_theme(self, P):
        self._paint_label()

    def save_settings(self, cfg):
        cfg['threads'] = self._threads()

    def _threads(self):
        try:
            return max(1, min(self.cores, int(self.threads_var.get())))
        except (tk.TclError, ValueError):
            return self.cores

    def _paint_label(self):
        P = self.app.P
        if not self.ready.is_set() or not self.engine:
            return
        self.engine_lbl.configure(
            text=f'Engine: CPU, {self.engine.threads} threads, fp32', foreground=P['ok'])

    # ---- engine lifecycle ----
    def start(self):
        if self.loading:
            return
        self.loading = True
        self.ready.clear()
        n = self._threads()                   # read Tk variables on the main thread only
        self.threads_var.set(n)
        self.engine_lbl.configure(text='Engine: loading ...', foreground=self.app.P['muted'])
        self.reload_btn.state(['disabled'])
        self.bench_btn.state(['disabled'])
        self.app.set_status('Loading model ...')
        threading.Thread(target=self._load, args=(n,), daemon=True).start()

    def _load(self, threads):
        app = self.app
        try:
            ok, why = check_files()
            if not ok:
                raise FileNotFoundError(MISSING_MSG + '\n\nDetails: ' + why)
            app.set_status('Importing PyTorch + Transformers (slow on a cold start) ...')
            import_runtime()
            if self.engine is None:
                self.engine = PhononEngine(status=app.set_status)
            self.engine.load(threads)
            voices = self.engine.voice_list()
            ids = [k for k, _ in voices]
            labels = [lab for _, lab in voices]

            def ready():
                app.fill_voices(ids, labels, app.cfg.get('voice', self.default_voice))
                self.ready.set()
                self._paint_label()
                app.status.set(f'Ready, {len(ids)} voices, loaded in '
                               f'{self.engine.load_s:.1f}s.')
            app.ui(ready)
        except Exception as e:
            err = str(e)

            def failed():
                self.engine_lbl.configure(text='Engine: failed', foreground=app.P['err'])
                app.status.set('Model failed to load. Fix the problem, then Apply / reload.')
                messagebox.showerror('Model error', err[-1500:])
            app.ui(failed)
        finally:
            def done():
                self.loading = False
                self.reload_btn.state(['!disabled'])
                self.bench_btn.state(['!disabled'])
            app.ui(done)

    def reload(self):
        if self.app.pending:
            messagebox.showinfo('Busy', 'Wait for the queue to finish first.')
            return
        self.app._save_cfg()
        eng = self.engine
        if eng is not None and eng.model is not None and self.ready.is_set():
            eng.set_threads(self._threads())        # no need to reload weights for this
            self._paint_label()
            self.app.set_status(f'Using {eng.threads} threads.')
            return
        self.start()

    def run_benchmark(self):
        app = self.app
        if self.engine is None or self.loading or app.pending or not self.ready.is_set():
            messagebox.showinfo('Busy', 'Engine must be loaded and idle to benchmark.')
            return
        self.bench_btn.state(['disabled'])
        self.reload_btn.state(['disabled'])
        voice = app.voice_id()
        counts = sorted({1, max(1, self.cores // 2), self.cores})

        def work():
            try:
                rows, cold, _ = self.engine.benchmark(voice, counts)
                text = PhononEngine.format_bench(rows, self.engine.load_s, cold)
                app.ui(lambda: self._show_bench(text))
                app.set_status('Benchmark done.')
            except Exception as e:
                err = str(e)
                app.ui(lambda: messagebox.showerror('Benchmark error', err[-1200:]))
            finally:
                app.ui(lambda: (self.bench_btn.state(['!disabled']),
                                self.reload_btn.state(['!disabled']), self._paint_label()))
        threading.Thread(target=work, daemon=True).start()

    def _show_bench(self, body):
        P = self.app.P
        top, frame = self.app._dialog('Benchmark', 640)
        t = tk.Text(frame, font=self.app.f_mono, bg=P['text_bg'], fg=P['fg'], bd=0,
                    highlightthickness=0, padx=16, pady=12, width=64,
                    height=body.count('\n') + 2, wrap='none')
        t.insert('1.0', body)
        t.configure(state='disabled')
        t.pack()
        ttk.Button(frame, text='Close', command=top.destroy).pack(pady=(12, 0))

    # ---- synthesis ----
    def after_job(self):
        self._paint_label()

    def synth(self, text, voice, speed):
        audio = self.engine.synth_float(text, voice, speed)
        return pcm16(audio), int(self.engine.sample_rate)


# ============================================================
#  ENTRY POINT  (any crash -> a dialog, no log files)
# ============================================================
def _fatal(msg):
    try:
        r = tk.Tk()
        r.withdraw()
        messagebox.showerror(f'{APP_NAME} crashed', msg[-1800:])
        r.destroy()
    except Exception:
        pass


def main():
    if '--download' in sys.argv:
        sys.exit(download_models())
    missing, pip_names = Backend.deps_missing()
    if missing:
        py = ROOT / '.venv' / 'Scripts' / 'python.exe'
        _fatal('Missing Python packages: ' + ', '.join(missing) + '\n\n'
               'Close this and double-click phonon_pro.bat once, it installs everything.\n\n'
               'Manual install:\n'
               f'"{py if py.exists() else "python"}" -m pip install {pip_names}')
        sys.exit(1)
    Studio().mainloop()


if __name__ == '__main__':
    try:
        main()
    except KeyboardInterrupt:
        sys.exit(0)
    except Exception:
        _fatal(traceback.format_exc())
        sys.exit(1)