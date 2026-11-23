// solve.js — a fast, dependency-free re-implementation of makefun-site 1.0.0's build.
//
// Written from the behaviour its README and reference code state; every line here is
// my own. run(input) returns the same output tree makefun-site returns for the same
// input, byte for byte: each page's index.html, the index and tag pages, the report
// and each static file.
//
// How it is faster than the reference: the reference lexes Markdown into token
// objects and then renders them, escapes HTML one character at a time, and walks a
// template node tree with a scope-chain lookup per value. This module instead
// renders Markdown in one pass over the lines with bulk escaping, caches slugs, and
// compiles each template once per case into straight-line JavaScript (a function
// built with new Function) that writes straight into an output array.

/* ------------------------------------------------------------------ text */

const byCodeUnits = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

const dirOf = (path) => (path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '');

/** `rel` (a link's path, "/"-separated) from the directory `dir` of a source, or null when it climbs out of the root. */
function resolvePath(dir, rel) {
  const parts = dir === '' ? [] : dir.split('/');
  for (const seg of rel.split('/')) {
    if (seg === '' || seg === '.') continue;
    if (seg === '..') {
      if (parts.length === 0) return null;
      parts.pop();
    } else parts.push(seg);
  }
  return parts.join('/');
}

/** The HTML escape table: & < > " ' and nothing else. */
const ESC_TEST = /[&<>"']/;
const ESC_ALL = /[&<>"']/g;
const ESC_MAP = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

function esc(text) {
  return ESC_TEST.test(text) ? text.replace(ESC_ALL, (c) => ESC_MAP[c]) : text;
}

/** Combining marks, dropped from a slug after NFKD. */
const MARK_RE = /\p{M}/gu;

/**
 * The slug of `text`: NFKD, combining marks dropped, A-Z lowered, each run of
 * characters other than a-z and 0-9 one "-", none at either end, at most 64
 * characters (a "-" left at the cut dropped), "untitled" when nothing is left.
 * `cache` is the run's own memo, so a repeated title or tag pays once.
 */
function slugify(text, cache) {
  const hit = cache.get(text);
  if (hit !== undefined) return hit;
  let plain = text;
  let ascii = true;
  for (let i = 0; i < text.length; i++) {
    if (text.charCodeAt(i) > 127) {
      ascii = false;
      break;
    }
  }
  // Plain ASCII is unchanged by NFKD and holds no combining marks.
  if (!ascii) plain = text.normalize('NFKD').replace(MARK_RE, '');
  let out = '';
  let gap = false;
  if (ascii) {
    for (let i = 0; i < plain.length; i++) {
      const ch = plain[i];
      let keep = null;
      if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
      else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
      if (keep === null) {
        gap = out.length > 0;
        continue;
      }
      if (gap) out += '-';
      gap = false;
      out += keep;
    }
  } else {
    for (const ch of plain) {
      let keep = null;
      if (ch >= 'A' && ch <= 'Z') keep = ch.toLowerCase();
      else if ((ch >= 'a' && ch <= 'z') || (ch >= '0' && ch <= '9')) keep = ch;
      if (keep === null) {
        gap = out.length > 0;
        continue;
      }
      if (gap) out += '-';
      gap = false;
      out += keep;
    }
  }
  out = out.slice(0, 64).replace(/-+$/, '');
  if (out === '') out = 'untitled';
  cache.set(text, out);
  return out;
}

/** `slug` made unique against `taken` (and added to it): the first of slug, slug-2, slug-3 ... not taken. */
function uniqueSlug(slug, taken) {
  let out = slug;
  for (let n = 2; taken.has(out); n++) out = `${slug}-${n}`;
  taken.add(out);
  return out;
}

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];

/** A YYYY-MM-DD date in words, from the string alone: "2026-11-09" is "9 November 2026". */
function longDate(date) {
  const y = date.slice(0, 4);
  const m = date.slice(5, 7);
  const d = date.slice(8, 10);
  return `${Number(d)} ${MONTHS[Number(m) - 1]} ${y}`;
}

/** The words of `lines` from `start`: the runs of characters other than whitespace, the same count as on the lines joined with "\n". Counted by hand, with no array built. */
const WS_NONASCII = new Set([0xa0, 0x1680, 0x2000, 0x2001, 0x2002, 0x2003, 0x2004, 0x2005, 0x2006, 0x2007, 0x2008, 0x2009, 0x200a, 0x2028, 0x2029, 0x202f, 0x205f, 0x3000, 0xfeff]);

function wordsInLines(lines, start) {
  let n = 0;
  for (let k = start; k < lines.length; k++) {
    const line = lines[k];
    let inWord = false;
    for (let i = 0; i < line.length; i++) {
      const c = line.charCodeAt(i);
      const ws = c < 128 ? c === 32 || c === 9 || c === 10 || c === 11 || c === 12 || c === 13 : WS_NONASCII.has(c);
      if (ws) inWord = false;
      else if (!inWord) {
        inWord = true;
        n++;
      }
    }
  }
  return n;
}

/* ------------------------------------------------------------ front matter */

const FM_LINE = /^([a-z_]+):(?: (.*))?$/;
const FM_DATE = /^(\d{4})-(\d{2})-(\d{2})$/;
const FM_NAME = /^[a-z0-9-]+$/;
const FM_SLUG = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const FM_TAG = /^[^"[\]]+$/;
const FM_KEYS = ['title', 'date', 'tags', 'draft', 'layout', 'slug', 'summary'];

/** The days of month `m` (1-12) of year `y`, by the Gregorian rule. */
function daysIn(y, m) {
  if (m === 2) return (y % 4 === 0 && y % 100 !== 0) || y % 400 === 0 ? 29 : 28;
  return m === 4 || m === 6 || m === 9 || m === 11 ? 30 : 31;
}

/** A string value: "..." with \" and \\ its only escapes, or bare, the rest of the line (never opening on " or [). */
function fmString(raw) {
  if (raw.charCodeAt(0) === 34) {
    if (raw.length < 2 || raw.charCodeAt(raw.length - 1) !== 34) return { error: 'a quoted string is not closed' };
    let out = '';
    for (let i = 1; i < raw.length - 1; i++) {
      const c = raw[i];
      if (c === '\\') {
        const n = raw[i + 1];
        if ((n !== '"' && n !== '\\') || i + 1 === raw.length - 1) return { error: 'a quoted string holds an escape other than \\" or \\\\' };
        out += n;
        i++;
      } else if (c === '"') return { error: 'a quoted string holds a stray quote' };
      else out += c;
    }
    return { value: out };
  }
  if (raw.charCodeAt(0) === 91) return { error: 'a bare string opens on [' };
  return { value: raw };
}

/** One key's value, or why it is refused. */
function fmValue(key, raw) {
  switch (key) {
    case 'title':
    case 'summary': {
      const s = fmString(raw);
      return 'error' in s ? { error: `key "${key}": ${s.error}` } : s;
    }
    case 'date': {
      const m = FM_DATE.exec(raw);
      const y = m ? Number(m[1]) : 0;
      const mo = m ? Number(m[2]) : 0;
      const d = m ? Number(m[3]) : 0;
      if (!m || y < 1970 || y > 2099 || mo < 1 || mo > 12 || d < 1 || d > daysIn(y, mo)) return { error: 'key "date": not a date from 1970-01-01 to 2099-12-31 (YYYY-MM-DD)' };
      return { value: raw };
    }
    case 'tags': {
      if (!raw.startsWith('[') || !raw.endsWith(']')) return { error: 'key "tags": not a list [a, b]' };
      const inner = raw.slice(1, -1);
      if (inner.trim() === '') return { value: [] };
      const tags = inner.split(',').map((t) => t.trim());
      if (tags.some((t) => t === '' || !FM_TAG.test(t))) return { error: 'key "tags": an empty tag, or one holding " [ or ]' };
      return { value: tags };
    }
    case 'draft':
      return raw === 'true' ? { value: true } : raw === 'false' ? { value: false } : { error: 'key "draft": true or false' };
    case 'layout':
      return FM_NAME.test(raw) ? { value: raw } : { error: 'key "layout": not a template name' };
    case 'slug':
      return FM_SLUG.test(raw) && raw.length <= 64 ? { value: raw } : { error: 'key "slug": not a slug' };
    default:
      return { error: `unknown key "${key}"` };
  }
}

/**
 * A source's front matter: { data, bodyStart } (the body's first line index), or
 * { error } with the first reason it is refused. `lines` is the source split on "\n".
 */
function parseFM(lines) {
  if (lines[0] !== '---') return { error: 'no front matter' };
  let close = -1;
  for (let i = 1; i < lines.length; i++) {
    if (lines[i] === '---') {
      close = i;
      break;
    }
  }
  if (close === -1) return { error: 'the front matter is not closed' };
  const data = {};
  for (let i = 1; i < close; i++) {
    const line = lines[i];
    if (isBlank(line) || line.charCodeAt(0) === 35) continue;
    const m = FM_LINE.exec(line);
    if (!m) return { error: `line ${i + 1} is not "key: value"` };
    const key = m[1];
    const raw = (m[2] ?? '').replace(/[ \t]+$/, '');
    if (!FM_KEYS.includes(key)) return { error: `unknown key "${key}"` };
    if (Object.hasOwn(data, key)) return { error: `key "${key}" is given twice` };
    if (raw === '') return { error: `key "${key}" has no value` };
    const v = fmValue(key, raw);
    if ('error' in v) return v;
    data[key] = v.value;
  }
  if (!Object.hasOwn(data, 'title')) return { error: 'no title' };
  return { data, bodyStart: close + 1 };
}

/* --------------------------------------------------------------- markdown */

// A line of spaces and tabs only (or empty).
function isBlank(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// A line with spaces and tabs at either end dropped.
function trimLine(line) {
  let a = 0;
  let b = line.length;
  while (a < b && (line.charCodeAt(a) === 32 || line.charCodeAt(a) === 9)) a++;
  while (b > a && (line.charCodeAt(b - 1) === 32 || line.charCodeAt(b - 1) === 9)) b--;
  return a === 0 && b === line.length ? line : line.slice(a, b);
}

// A fence opener: ``` plus an optional language, then spaces or tabs only. Returns the language, or null.
function fenceOpen(line) {
  if (!line.startsWith('```')) return null;
  let j = 3;
  while (j < line.length) {
    const c = line.charCodeAt(j);
    if ((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || (c >= 48 && c <= 57) || c === 95 || c === 43 || c === 45) j++;
    else break;
  }
  const lang = line.slice(3, j);
  for (; j < line.length; j++) {
    const c = line.charCodeAt(j);
    if (c !== 32 && c !== 9) return null;
  }
  return lang;
}

// A fence closer: ``` then spaces or tabs only.
function fenceClose(line) {
  if (!line.startsWith('```')) return false;
  for (let j = 3; j < line.length; j++) {
    const c = line.charCodeAt(j);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// A heading line's level and text, or null (a heading's text is never empty).
function headingOf(line) {
  let h = 0;
  while (h < line.length && line.charCodeAt(h) === 35) h++;
  if (h === 0 || h > 6) return null;
  if (h >= line.length) return null;
  const c = line.charCodeAt(h);
  if (c !== 32 && c !== 9) return null;
  let t = h;
  while (t < line.length) {
    const d = line.charCodeAt(t);
    if (d !== 32 && d !== 9) break;
    t++;
  }
  let end = line.length;
  while (end > t) {
    const d = line.charCodeAt(end - 1);
    if (d !== 32 && d !== 9) break;
    end--;
  }
  if (t >= end) return null;
  return { depth: h, text: line.slice(t, end) };
}

// A thematic break: --- or ***, then spaces or tabs only.
function isHr(line) {
  if (!line.startsWith('---') && !line.startsWith('***')) return false;
  for (let j = 3; j < line.length; j++) {
    const c = line.charCodeAt(j);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// A line of two or more spaces then a non-space: a list item's continuation.
function isContinued(line) {
  let sp = 0;
  while (sp < line.length && line.charCodeAt(sp) === 32) sp++;
  return sp >= 2 && sp < line.length && !/\s/.test(line[sp]);
}

// A bullet item's text, or null. An ordered item's { num, text }, or null.
function bulletItem(line) {
  const c0 = line.charCodeAt(0);
  if ((c0 === 45 || c0 === 42) && line.charCodeAt(1) === 32) return line.slice(2);
  return null;
}

function orderedItem(line) {
  let j = 0;
  while (j < line.length) {
    const c = line.charCodeAt(j);
    if (c < 48 || c > 57) break;
    j++;
  }
  if (j === 0 || j > 9) return null;
  if (line.charCodeAt(j) !== 46 || line.charCodeAt(j + 1) !== 32) return null;
  return { num: line.slice(0, j), text: line.slice(j + 2) };
}

// A list's first line, or null: { ordered, num, text }.
function listStart(line) {
  const b = bulletItem(line);
  if (b !== null) return { ordered: false, num: 1, text: b };
  const o = orderedItem(line);
  if (o !== null) return { ordered: true, num: Number(o.num), text: o.text };
  return null;
}

// Whether `line` ends a paragraph: a blank line, a fence, a heading or a thematic break.
function endsPara(line) {
  return isBlank(line) || fenceOpen(line) !== null || headingOf(line) !== null || isHr(line);
}

/** The characters a backslash escapes. */
const ESCAPABLE = new Set(['\\', '`', '*', '_', '[', ']', '(', ')', '#', '+', '-', '.', '!', '>']);

/** The first index from `from` where `s` holds `what` outside a backslash escape, or -1. */
function findUnescaped(s, what, from) {
  for (let j = from; j <= s.length - what.length; j++) {
    if (s[j] === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (s.startsWith(what, j)) return j;
  }
  return -1;
}

/** The first single * from `from` (one whose run is not **), outside an escape, or -1. */
function findSingleStar(s, from) {
  for (let j = from; j < s.length; j++) {
    const c = s[j];
    if (c === '\\' && j + 1 < s.length && ESCAPABLE.has(s[j + 1])) {
      j++;
      continue;
    }
    if (c !== '*') continue;
    if (s[j + 1] === '*') {
      j++;
      continue;
    }
    return j;
  }
  return -1;
}

const INLINE_SPECIAL = /[\\`*\[]/;
const WS_RE = /\s/;

/** `s` rendered inline; `link(target)` is a link's href. */
function inline(s, link) {
  // The common case: no markup at all, one bulk escape (or none needed).
  if (!INLINE_SPECIAL.test(s)) return ESC_TEST.test(s) ? s.replace(ESC_ALL, (c) => ESC_MAP[c]) : s;
  const out = [];
  let i = 0;
  let run = 0;
  const n = s.length;
  while (i < n) {
    // Jump to the next markup character, rather than stepping through plain text one character at a time.
    let j = n;
    let k = s.indexOf('\\', i);
    if (k !== -1 && k < j) j = k;
    k = s.indexOf('`', i);
    if (k !== -1 && k < j) j = k;
    k = s.indexOf('*', i);
    if (k !== -1 && k < j) j = k;
    k = s.indexOf('[', i);
    if (k !== -1 && k < j) j = k;
    if (j === n) break;
    const c = s[j];
    i = j;
    if (c === '\\' && i + 1 < n && ESCAPABLE.has(s[i + 1])) {
      if (run < i) out.push(esc(s.slice(run, i)));
      out.push(s[i + 1]);
      i += 2;
      run = i;
      continue;
    }
    if (c === '\\') {
      // A backslash before anything else is itself, and stays in the plain run.
      i++;
      continue;
    }
    if (c === '`') {
      const j2 = s.indexOf('`', i + 1);
      if (j2 > i + 1) {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('<code>', esc(s.slice(i + 1, j2)), '</code>');
        i = j2 + 1;
        run = i;
      } else {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('`');
        i++;
        run = i;
      }
      continue;
    }
    if (c === '*') {
      if (s[i + 1] === '*') {
        const j2 = findUnescaped(s, '**', i + 2);
        if (j2 > i + 2) {
          if (run < i) out.push(esc(s.slice(run, i)));
          out.push('<strong>', inline(s.slice(i + 2, j2), link), '</strong>');
          i = j2 + 2;
          run = i;
        } else {
          if (run < i) out.push(esc(s.slice(run, i)));
          out.push('**');
          i += 2;
          run = i;
        }
        continue;
      }
      const j2 = findSingleStar(s, i + 1);
      if (j2 > i + 1) {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('<em>', inline(s.slice(i + 1, j2), link), '</em>');
        i = j2 + 1;
        run = i;
      } else {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('*');
        i++;
        run = i;
      }
      continue;
    }
    if (c === '[') {
      const k2 = findUnescaped(s, ']', i + 1);
      const m = k2 !== -1 && s[k2 + 1] === '(' ? s.indexOf(')', k2 + 2) : -1;
      const target = m === -1 ? '' : s.slice(k2 + 2, m);
      if (target !== '' && !WS_RE.test(target)) {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('<a href="', esc(link(target)), '">', inline(s.slice(i + 1, k2), link), '</a>');
        i = m + 1;
        run = i;
      } else {
        if (run < i) out.push(esc(s.slice(run, i)));
        out.push('[');
        i++;
        run = i;
      }
      continue;
    }
  }
  if (run < n) out.push(esc(s.slice(run, n)));
  return out.join('');
}

/**
 * `lines` from `start` rendered: its HTML (each block on its own lines, a "\n"
 * after the last), its table of contents (every level 2 and 3 heading: level, id
 * and its inline HTML) and its excerpt (the first paragraph's inline HTML, or "").
 * `link(target)` is a link's href. Rendered in one pass over the lines, with no
 * token objects in between.
 */
function renderMd(lines, start, link, slugCache) {
  const ids = new Set();
  const out = [];
  const toc = [];
  let excerpt = null;
  let i = start;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (isBlank(line)) {
      i++;
      continue;
    }
    const fence = fenceOpen(line);
    if (fence !== null) {
      const body = [];
      i++;
      while (i < n && !fenceClose(lines[i])) body.push(lines[i++]);
      i++;
      const cls = fence === '' ? '' : ` class="language-${esc(fence)}"`;
      out.push(`<pre><code${cls}>`);
      for (const l of body) {
        out.push(esc(l));
        out.push('\n');
      }
      out.push('</code></pre>\n');
      continue;
    }
    const hd = headingOf(line);
    if (hd !== null) {
      const id = uniqueSlug(slugify(hd.text, slugCache), ids);
      const html = inline(hd.text, link);
      out.push(`<h${hd.depth} id="${id}">${html}</h${hd.depth}>\n`);
      if (hd.depth === 2 || hd.depth === 3) toc.push({ level: hd.depth, id, html });
      i++;
      continue;
    }
    if (isHr(line)) {
      out.push('<hr>\n');
      i++;
      continue;
    }
    if (line.charCodeAt(0) === 62) {
      const body = [];
      while (i < n && lines[i].charCodeAt(0) === 62) {
        const l = lines[i++];
        body.push(l.charCodeAt(1) === 32 ? l.slice(2) : l.slice(1));
      }
      const kept = [];
      for (const l of body) {
        const t = trimLine(l);
        if (t !== '') kept.push(t);
      }
      if (kept.length === 0) out.push('<blockquote>\n</blockquote>\n');
      else out.push(`<blockquote>\n<p>${inline(kept.join('\n'), link)}</p>\n</blockquote>\n`);
      continue;
    }
    const li = listStart(line);
    if (li !== null) {
      const ordered = li.ordered;
      const items = [];
      while (i < n) {
        const l2 = lines[i];
        const m2 = ordered ? orderedItem(l2) : bulletItem(l2);
        if (m2 !== null) {
          items.push([trimLine(ordered ? m2.text : m2)]);
          i++;
        } else if (isContinued(l2)) {
          items[items.length - 1].push(trimLine(l2));
          i++;
        } else break;
      }
      const tag = ordered ? 'ol' : 'ul';
      const open = ordered && li.num !== 1 ? `<ol start="${li.num}">` : `<${tag}>`;
      out.push(open, '\n');
      for (const it of items) out.push(`<li>${inline(it.join('\n'), link)}</li>\n`);
      out.push(`</${tag}>\n`);
      continue;
    }
    const body = [trimLine(line)];
    i++;
    while (i < n && !endsPara(lines[i])) body.push(trimLine(lines[i++]));
    const html = inline(body.join('\n'), link);
    if (excerpt === null) excerpt = html;
    out.push(`<p>${html}</p>\n`);
  }
  return { html: out.join(''), toc, excerpt: excerpt ?? '' };
}

/* --------------------------------------------------------------- templates */

// The deepest an include nests: one past it renders nothing.
const INCLUDE_DEPTH = 8;

const T_PATH = /^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const T_FOR = /^for ([A-Za-z_][A-Za-z0-9_]*) in (\S+)$/;
const T_IF = /^if (not )?(\S+)$/;
const T_INCLUDE = /^include "([a-z0-9-]+)"$/;

/** A template that does not parse: its name and why. */
class TemplateError extends Error {}

/** The path `text` names, split at its dots, or a TemplateError. */
function pathOf(name, text) {
  if (!T_PATH.test(text)) throw new TemplateError(`template "${name}": ${JSON.stringify(text)} is not a path`);
  return text.split('.');
}

/** `src`'s tokens: text, {{ }}, {{{ }}} and {% %}, a standalone tag's line taken with it. */
function tokenize(name, src) {
  const tokens = [];
  let text = '';
  let i = 0;
  while (i < src.length) {
    const open = src.indexOf('{', i);
    if (open === -1 || open === src.length - 1) {
      text += src.slice(i);
      break;
    }
    const next = src[open + 1];
    if (next !== '{' && next !== '%') {
      text += src.slice(i, open + 1);
      i = open + 1;
      continue;
    }
    text += src.slice(i, open);
    if (next === '{') {
      const raw = src[open + 2] === '{';
      const close = src.indexOf(raw ? '}}}' : '}}', open + (raw ? 3 : 2));
      if (close === -1) throw new TemplateError(`template "${name}": a ${raw ? '{{{' : '{{'} is not closed`);
      if (text !== '') tokens.push({ t: 'text', text });
      text = '';
      tokens.push({ t: raw ? 'raw' : 'var', path: pathOf(name, src.slice(open + (raw ? 3 : 2), close).trim()) });
      i = close + (raw ? 3 : 2);
      continue;
    }
    const close = src.indexOf('%}', open + 2);
    if (close === -1) throw new TemplateError(`template "${name}": a {% is not closed`);
    const end = close + 2;
    const lineStart = src.lastIndexOf('\n', open - 1) + 1;
    const nl = src.indexOf('\n', end);
    const lineEnd = nl === -1 ? src.length : nl;
    const standalone = /^[ \t]*$/.test(src.slice(lineStart, open)) && /^[ \t]*$/.test(src.slice(end, lineEnd));
    if (standalone) text = text.slice(0, text.length - (open - lineStart));
    if (text !== '') tokens.push({ t: 'text', text });
    text = '';
    tokens.push({ t: 'tag', tag: src.slice(open + 2, close).trim() });
    i = standalone ? (nl === -1 ? src.length : nl + 1) : end;
  }
  if (text !== '') tokens.push({ t: 'text', text });
  return tokens;
}

/** `src` parsed into its tree of nodes (a TemplateError when it does not parse). */
function parseTemplate(name, src) {
  const root = { kind: 'root', body: [] };
  const stack = [root];
  let body = root.body;
  for (const tok of tokenize(name, src)) {
    if (tok.t === 'text') body.push({ kind: 'text', text: tok.text });
    else if (tok.t === 'var' || tok.t === 'raw') body.push({ kind: tok.t, path: tok.path });
    else {
      const tag = tok.tag;
      const top = stack[stack.length - 1];
      let m;
      if ((m = T_FOR.exec(tag)) !== null) {
        const node = { kind: 'for', name: m[1], path: pathOf(name, m[2]), body: [] };
        body.push(node);
        stack.push(node);
        body = node.body;
      } else if ((m = T_IF.exec(tag)) !== null) {
        const node = { kind: 'if', not: m[1] !== undefined, path: pathOf(name, m[2]), then: [], else: null };
        body.push(node);
        stack.push(node);
        body = node.then;
      } else if (tag === 'else') {
        if (top.kind !== 'if' || top.else !== null) throw new TemplateError(`template "${name}": an else outside an if`);
        top.else = [];
        body = top.else;
      } else if (tag === 'endfor' || tag === 'endif') {
        if (top.kind !== (tag === 'endfor' ? 'for' : 'if')) throw new TemplateError(`template "${name}": an ${tag} with no open ${tag.slice(3)}`);
        stack.pop();
        const parent = stack[stack.length - 1];
        body = parent.kind === 'root' ? parent.body : parent.kind === 'for' ? parent.body : parent.else ?? parent.then;
      } else if ((m = T_INCLUDE.exec(tag)) !== null) body.push({ kind: 'include', name: m[1] });
      else throw new TemplateError(`template "${name}": {% ${tag} %} is not a tag`);
    }
  }
  if (stack.length > 1) throw new TemplateError(`template "${name}": a ${stack[stack.length - 1].kind} is not closed`);
  return root.body;
}

// ---------------------------------------------------------------- the compiler
//
// A parsed template becomes one JavaScript function, built once per case with
// new Function. It takes ($V, $S, $T, $D, $P, lk, g1, g2, g3, gx, txt, tru,
// esc): $V the page's values, $S the scope chain, $T the compiled templates,
// $D the include depth, $P the scope-chain link, and the small value helpers.
// It writes into a fresh array and returns the joined string.
//
// A loop's element and its `loop` object are plain locals, so a name bound by a
// loop in this template reads straight off a variable. A name bound nowhere here
// is read through the scope chain (lk), which is how an included template still
// sees the loop variable of the template that included it: a loop whose body can
// reach an include builds one chain frame per iteration, linked to the chain it
// was called with. The root values are the chain's first frame.

// The scope chain's link: a symbol, so no loop variable's name can collide with it.
const PARENT = Symbol('parent');

/** The value of name `n` in the scope chain `s`: the nearest frame holding it, else undefined. */
function lk(s, n) {
  while (s !== null && s !== undefined) {
    if (Object.hasOwn(s, n)) return s[n];
    s = s[PARENT];
  }
  return undefined;
}

/** The value at one, two or three further names of `v`, or undefined when any step is not an own property. */
function g1(v, a) {
  return v !== null && typeof v === 'object' && Object.hasOwn(v, a) ? v[a] : undefined;
}

function g2(v, a, b) {
  if (v === null || typeof v !== 'object' || !Object.hasOwn(v, a)) return undefined;
  v = v[a];
  return v !== null && typeof v === 'object' && Object.hasOwn(v, b) ? v[b] : undefined;
}

function g3(v, a, b, c) {
  if (v === null || typeof v !== 'object' || !Object.hasOwn(v, a)) return undefined;
  v = v[a];
  if (v === null || typeof v !== 'object' || !Object.hasOwn(v, b)) return undefined;
  v = v[b];
  return v !== null && typeof v === 'object' && Object.hasOwn(v, c) ? v[c] : undefined;
}

function gx(v, segs) {
  for (let k = 0; k < segs.length; k++) {
    if (v === null || typeof v !== 'object' || !Object.hasOwn(v, segs[k])) return undefined;
    v = v[segs[k]];
  }
  return v;
}

/** A value as text: a string itself, a number in JavaScript's digits, true or false, an array's items joined by ", ", else "". */
function txt(v) {
  if (typeof v === 'string') return v;
  if (typeof v === 'number') return String(v);
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  if (Array.isArray(v)) {
    let s = '';
    for (let k = 0; k < v.length; k++) {
      if (k > 0) s += ', ';
      s += txt(v[k]);
    }
    return s;
  }
  return '';
}

/** Whether a value counts as true in an if: not undefined, null, false, "", 0 or an empty array. */
function tru(v) {
  if (Array.isArray(v)) return v.length > 0;
  return v !== undefined && v !== null && v !== false && v !== '' && v !== 0;
}

/** Whether `nodes` hold an include anywhere (through for and if bodies too). */
function containsInclude(nodes) {
  for (const node of nodes) {
    if (node.kind === 'include') return true;
    if (node.kind === 'for' && containsInclude(node.body)) return true;
    if (node.kind === 'if' && (containsInclude(node.then) || (node.else !== null && containsInclude(node.else)))) return true;
  }
  return false;
}

/**
 * `nodes` with their includes spliced in: an include of a template that parses is
 * replaced by that template's own nodes, spliced the same way, while the static
 * depth stays under 8. An include past that depth renders nothing, so it is
 * dropped; an include that would cycle back to a template already being spliced
 * is kept as a runtime include, annotated with its static depth so the depth check
 * still counts from where the splice put it. `parsed` maps template names to their
 * node lists; `stack` is the chain of templates being spliced, innermost last.
 */
function spliceNodes(nodes, depth, stack, parsed) {
  const out = [];
  for (const node of nodes) {
    if (node.kind === 'include') {
      const target = parsed.get(node.name);
      if (target !== undefined && depth < INCLUDE_DEPTH && !stack.includes(node.name)) {
        out.push(...spliceNodes(target, depth + 1, [...stack, node.name], parsed));
      } else if (depth < INCLUDE_DEPTH) {
        out.push({ kind: 'include', name: node.name, depth });
      }
      // At depth 8 or more the reference renders nothing: the node is dropped.
    } else if (node.kind === 'for') {
      out.push({ ...node, body: spliceNodes(node.body, depth, stack, parsed) });
    } else if (node.kind === 'if') {
      out.push({ ...node, then: spliceNodes(node.then, depth, stack, parsed), else: node.else === null ? null : spliceNodes(node.else, depth, stack, parsed) });
    } else out.push(node);
  }
  return out;
}

/** The JavaScript expression for `path` in the code being generated. When `directRoot` is true the function is only ever
 * called at the top level, so a name no loop here binds can only come from the page's values, and reads straight off $V. */
function genPath(path, scope, scopeVar, directRoot) {
  const first = path[0];
  let expr;
  for (let s = scope.length - 1; s >= 0; s--) {
    const hit = scope[s].get(first);
    if (hit !== undefined) {
      expr = hit;
      break;
    }
  }
  if (expr === undefined) expr = directRoot ? `$V.${first}` : `lk(${scopeVar},${JSON.stringify(first)})`;
  if (path.length === 1) return expr;
  if (path.length === 2) return `g1(${expr},${JSON.stringify(path[1])})`;
  if (path.length === 3) return `g2(${expr},${JSON.stringify(path[1])},${JSON.stringify(path[2])})`;
  if (path.length === 4) return `g3(${expr},${JSON.stringify(path[1])},${JSON.stringify(path[2])},${JSON.stringify(path[3])})`;
  return `gx(${expr},${JSON.stringify(path.slice(1))})`;
}

/** `nodes` compiled into `state.parts`. `scope` is the stack of loop bindings (name -> local), `scopeVar` the chain variable in scope. */
function genNodes(nodes, scope, scopeVar, state) {
  const directRoot = state.directRoot;
  for (const node of nodes) {
    switch (node.kind) {
      case 'text':
        state.parts.push(`$o.push(${JSON.stringify(node.text)});`);
        break;
      case 'var':
        state.parts.push(`$o.push(esc(txt(${genPath(node.path, scope, scopeVar, directRoot)})));`);
        break;
      case 'raw':
        state.parts.push(`$o.push(txt(${genPath(node.path, scope, scopeVar, directRoot)}));`);
        break;
      case 'if': {
        state.parts.push(`if(tru(${genPath(node.path, scope, scopeVar, directRoot)})!==${node.not}){`);
        genNodes(node.then, scope, scopeVar, state);
        if (node.else !== null) {
          state.parts.push('}else{');
          genNodes(node.else, scope, scopeVar, state);
        }
        state.parts.push('}');
        break;
      }
      case 'for': {
        const id = state.next++;
        const xs = `$x${id}`;
        const k = `$k${id}`;
        const el = `$v${id}`;
        const lp = `$l${id}`;
        const fr = `$s${id}`;
        const hasInc = containsInclude(node.body);
        state.parts.push(`{const ${xs}=${genPath(node.path, scope, scopeVar, directRoot)};if(Array.isArray(${xs})){for(let ${k}=0;${k}<${xs}.length;${k}++){const ${el}=${xs}[${k}];const ${lp}={index:${k}+1,first:${k}===0,last:${k}===${xs}.length-1,length:${xs}.length};`);
        if (hasInc) state.parts.push(`const ${fr}={[${JSON.stringify(node.name)}]:${el},loop:${lp},[$P]:${scopeVar}};`);
        scope.push(new Map([[node.name, el], ['loop', lp]]));
        genNodes(node.body, scope, hasInc ? fr : scopeVar, state);
        scope.pop();
        state.parts.push('}}}');
        break;
      }
      case 'include': {
        const t = `$t${state.next++}`;
        const off = node.depth ?? 0;
        state.parts.push(`if($D+${off}<${INCLUDE_DEPTH}){const ${t}=$T.get(${JSON.stringify(node.name)});if(${t}!==undefined)$o.push(${t}($V,${scopeVar},$T,$D+${off}+1,$P,lk,g1,g2,g3,gx,txt,tru,esc));}`);
        break;
      }
    }
  }
}

/** A parsed template's nodes as one callable function. `directRoot` compiles for a top-level call, where a name no loop
 * binds reads straight off $V. */
function compileTemplate(nodes, directRoot = false) {
  const state = { next: 0, parts: [], directRoot };
  genNodes(nodes, [], '$S', state);
  const src = `"use strict";const $o=[];\n${state.parts.join('\n')}\nreturn $o.join("");`;
  return new Function('$V', '$S', '$T', '$D', '$P', 'lk', 'g1', 'g2', 'g3', 'gx', 'txt', 'tru', 'esc', src);
}

/* -------------------------------------------------------------------- run */

const RESERVED = ['posts', 'tags', 'page'];
const SCHEME_RE = /^[A-Za-z][A-Za-z0-9+.-]*:/;

/** One site's output tree: path -> text. */
export function run(input) {
  const slugCache = new Map();
  const report = [];
  // The parsed templates, their plain compilations (the include fallback), and
  // their compilations with includes spliced in (what a render runs).
  const parsed = new Map();
  for (const name of Object.keys(input.templates).sort(byCodeUnits)) {
    try {
      parsed.set(name, parseTemplate(name, input.templates[name]));
    } catch (err) {
      if (!(err instanceof TemplateError)) throw err;
      report.push(err.message);
    }
  }
  const general = new Map();
  for (const [name, nodes] of parsed) general.set(name, compileTemplate(nodes));
  const spliced = new Map();
  for (const [name, nodes] of parsed) spliced.set(name, compileTemplate(spliceNodes(nodes, 0, [name], parsed), true));
  const templates = general;
  const base = input.site.base_url.replace(/\/+$/, '');

  // 1. The sources, in code-unit order of their paths, line ends made "\n"; a source that is not .md is static.
  const files = [...input.files].sort((a, b) => byCodeUnits(a.path, b.path));
  const sources = [];
  const statics = [];
  for (const f of files) {
    if (f.path.endsWith('.md')) sources.push({ path: f.path, text: f.content.replace(/\r\n?/g, '\n') });
    else statics.push(f);
  }

  // 2. Each source's front matter: a refused source is reported and dropped, and so is a draft.
  const kept = [];
  for (const s of sources) {
    const lines = s.text.split('\n');
    const fm = parseFM(lines);
    if ('error' in fm) {
      report.push(`refused ${s.path}: ${fm.error}`);
      continue;
    }
    s.data = fm.data;
    s.lines = lines;
    s.bodyStart = fm.bodyStart;
    s.post = s.path.startsWith('posts/');
    const own = s.path.startsWith('tags/') ? 'tags' : s.path.startsWith('page/') ? 'page' : undefined;
    if (own !== undefined) {
      report.push(`refused ${s.path}: ${own}/ is the generator's own`);
      continue;
    }
    if (s.post && !Object.hasOwn(s.data, 'date')) {
      report.push(`refused ${s.path}: a post needs a date`);
      continue;
    }
    const layout = s.data.layout ?? (s.post ? 'post' : 'page');
    if (!templates.has(layout)) {
      report.push(`refused ${s.path}: layout "${layout}" is no template that parses`);
      continue;
    }
    s.layout = layout;
    if (s.data.draft === true) {
      report.push(`draft ${s.path}`);
      continue;
    }
    kept.push(s);
  }

  // 3. Each page's output directory and url: its slug made unique in its directory, in source order.
  const bySource = new Map();
  const taken = new Map();
  for (const s of kept) {
    const dir = s.post ? 'posts' : dirOf(s.path);
    let set = taken.get(dir);
    if (set === undefined) {
      set = new Set(dir === '' ? RESERVED : []);
      taken.set(dir, set);
    }
    const slug = uniqueSlug(s.data.slug ?? slugify(s.data.title, slugCache), set);
    s.slug = slug;
    s.outDir = dir === '' ? slug : `${dir}/${slug}`;
    s.url = `${base}/${s.outDir}/`;
    bySource.set(s.path, s);
  }

  // 4. Each body's Markdown, its links resolved to the pages and static files they name.
  const staticPaths = new Set(statics.map((f) => f.path));
  const broken = new Set();
  for (const s of kept) {
    const dir = dirOf(s.path);
    const link = (target) => {
      if (SCHEME_RE.test(target) || target.startsWith('/') || target.startsWith('#')) return target;
      const hash = target.indexOf('#');
      const rel = hash === -1 ? target : target.slice(0, hash);
      const frag = hash === -1 ? '' : target.slice(hash);
      const path = rel === '' ? null : resolvePath(dir, rel);
      if (path !== null && bySource.has(path)) return `${bySource.get(path).url}${frag}`;
      if (path !== null && staticPaths.has(path)) return `${base}/${path}${frag}`;
      broken.add(`broken-link ${s.path} -> ${target}`);
      return target;
    };
    const md = renderMd(s.lines, s.bodyStart, link, slugCache);
    s.html = md.html;
    s.toc = md.toc;
    s.excerpt = md.excerpt;
    s.words = wordsInLines(s.lines, s.bodyStart);
  }

  // 5. The posts, newest first and then by slug; each post's newer and older neighbours.
  const posts = kept.filter((s) => s.post);
  posts.sort((x, y) => byCodeUnits(y.data.date, x.data.date) || byCodeUnits(x.slug, y.slug));
  posts.forEach((p, k) => {
    p.newer = k === 0 ? null : posts[k - 1];
    p.older = k === posts.length - 1 ? null : posts[k + 1];
  });

  // 6. The tags: grouped by their slug, each named as first met in the posts' order, ordered by count and then slug.
  const bySlug = new Map();
  const ownTags = (s) => {
    const seen = new Set();
    const out = [];
    for (const name of s.data.tags ?? []) {
      const slug = slugify(name, slugCache);
      if (!seen.has(slug)) {
        seen.add(slug);
        out.push(name);
      }
    }
    return out;
  };
  for (const p of posts) {
    p.tagRefs = [];
    for (const name of ownTags(p)) {
      const slug = slugify(name, slugCache);
      let tag = bySlug.get(slug);
      if (tag === undefined) {
        tag = { name, slug, url: `${base}/tags/${slug}/`, posts: [] };
        bySlug.set(slug, tag);
      }
      tag.posts.push(p);
      p.tagRefs.push(tag);
    }
  }
  for (const s of kept) {
    if (!s.post) {
      s.tagRefs = ownTags(s).map((name) => {
        const slug = slugify(name, slugCache);
        return bySlug.get(slug) ?? { name, slug, url: '', posts: [] };
      });
    }
  }
  const tags = [...bySlug.values()].sort((x, y) => y.posts.length - x.posts.length || byCodeUnits(x.slug, y.slug));

  // A page's link record as templates read it.
  const linkOf = (s) => (s === null ? null : { title: s.data.title, url: s.url, date: s.data.date ?? '', date_long: s.data.date === undefined ? '' : longDate(s.data.date) });

  // A post's card, as lists show it.
  const cardOf = (s) => ({
    title: s.data.title,
    url: s.url,
    date: s.data.date ?? '',
    date_long: s.data.date === undefined ? '' : longDate(s.data.date),
    summary: s.data.summary ?? '',
    excerpt: s.excerpt,
    reading_minutes: Math.max(1, Math.ceil(s.words / 200)),
    tags: s.tagRefs.map((t) => ({ name: t.name, slug: t.slug, url: t.url })),
  });

  // A page as its layout reads it.
  const pageOf = (s) => ({
    ...cardOf(s),
    slug: s.slug,
    content: s.html,
    toc: s.toc.map((h) => ({ level: h.level, id: h.id, html: h.html })),
    newer: linkOf(s.newer ?? null),
    older: linkOf(s.older ?? null),
    is_post: s.post,
  });

  // A tag as templates read it (its posts as cards).
  const cards = new Map(posts.map((p) => [p, cardOf(p)]));
  const tagOf = (t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length, posts: t.posts.map((p) => cards.get(p)) });

  // 7. Every page through its layout, the index pages and the tag pages through theirs.
  const site = { title: input.site.title, base_url: base };
  const allTags = tags.map((t) => ({ name: t.name, slug: t.slug, url: t.url, count: t.posts.length }));
  const recent = posts.slice(0, input.site.recent).map((p) => cards.get(p));
  const output = {};
  const renderTpl = (name, vars) => {
    const fn = spliced.get(name);
    if (fn === undefined) return null;
    // A null prototype, so a name the page does not carry reads exactly undefined, as a scope lookup would give.
    const V = Object.create(null);
    V.site = site;
    V.tags = allTags;
    V.recent = recent;
    Object.assign(V, vars);
    V[PARENT] = null;
    return fn(V, V, general, 0, PARENT, lk, g1, g2, g3, gx, txt, tru, esc);
  };
  for (const s of kept) output[`${s.outDir}/index.html`] = renderTpl(s.layout, { page: pageOf(s) });
  const per = input.site.per_page;
  const pages = Math.max(1, Math.ceil(posts.length / per));
  const indexUrl = (k) => (k === 1 ? `${base}/` : `${base}/page/${k}/`);
  for (let k = 1; k <= pages; k++) {
    const html = renderTpl('index', {
      posts: posts.slice((k - 1) * per, k * per).map((p) => cards.get(p)),
      pager: { number: k, total: pages, url: indexUrl(k), newer_url: k === 1 ? '' : indexUrl(k - 1), older_url: k === pages ? '' : indexUrl(k + 1) },
    });
    if (html !== null) output[k === 1 ? 'index.html' : `page/${k}/index.html`] = html;
  }
  for (const t of tags) {
    const html = renderTpl('tag', { tag: tagOf(t) });
    if (html !== null) output[`tags/${t.slug}/index.html`] = html;
  }
  const tagsHtml = renderTpl('tags', {});
  if (tagsHtml !== null) output['tags/index.html'] = tagsHtml;
  for (const f of statics) {
    if (Object.hasOwn(output, f.path)) report.push(`shadowed ${f.path}: a built page has its path`);
    else output[f.path] = f.content;
  }

  // 8. The report: every refusal, draft, broken link and template that did not parse, sorted, then the counts.
  const lines = [...report, ...broken].sort(byCodeUnits);
  const pageCount = kept.filter((s) => !s.post).length;
  lines.push(`built ${pageCount} pages, ${posts.length} posts, ${tags.length} tags and ${statics.length} static files`);
  output['build-report.txt'] = `${lines.join('\n')}\n`;
  return output;
}
