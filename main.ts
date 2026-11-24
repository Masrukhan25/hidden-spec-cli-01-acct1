// mend: one patch tool for every AI edit format (SPEC.md version 1).
// Node 22, standard library only; run as `node main.ts [options] [PATCH]`.
//
// The CLI reads a patch in one of four formats (unified diff, SEARCH/REPLACE
// blocks, V4A patches, JSON tool calls), finds the lines each edit names at
// the first of three matching tiers, and changes every file or none.
// Sections 1 to 4, 9 and 10 of SPEC.md (invocation, output and exit codes,
// files/lines/paths, format detection, JSON edits, order and atomicity) are
// implemented below, together with section 5 (three-tier matching), section 6
// (unified diffs), section 7 (SEARCH/REPLACE) and section 8 (V4A).
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set,
// and this file hands over to runner.ts (the last lines below): keep that
// hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

// ---- Files as lines (SPEC section 3) ----

interface FileState {
  lines: string[];
  br: '\n' | '\r\n';
  finalBreak: boolean;
}

function parseFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', finalBreak: false };
  const nl = text.indexOf('\n');
  const br: '\n' | '\r\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const finalBreak = text.endsWith(br);
  const lines = text.split(br);
  if (finalBreak) lines.pop();
  return { lines, br, finalBreak };
}

function serializeFile(fs: FileState): string {
  if (fs.lines.length === 0) return '';
  return fs.lines.join(fs.br) + (fs.finalBreak ? fs.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

// ---- Matching lines (SPEC section 5) ----

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** All 0-based positions at or after `from` where O matches the file's lines at one tier. */
function occurrencesAt(file: string[], o: string[], tier: number, from: number): number[] {
  const out: number[] = [];
  const normO = o.map((l) => normLine(l, tier));
  for (let i = from; i + o.length <= file.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (normLine(file[i + j]!, tier) !== normO[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, then 1, then 2; only 0 with --strict) at which O occurs at least once. */
function findTierAt(
  file: string[],
  o: string[],
  strict: boolean,
  from: number,
): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrencesAt(file, o, t, from);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** First line at or after `from` equal to the anchor at the first tier with one; -1 when none. */
function findAnchorLine(file: string[], anchor: string, from: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const want = normLine(anchor, t);
    for (let i = from; i < file.length; i++) {
      if (normLine(file[i]!, t) === want) return i;
    }
  }
  return -1;
}

/**
 * One body item of a unified hunk or a V4A chunk. `bs` is a `\` line (as in
 * `\ No newline at end of file`): it refers to the body line before it and
 * carries no line of its own.
 */
type BodyItem = { kind: 'ctx' | 'del' | 'add' | 'bs'; text: string };

/**
 * The lines that replace the k matched lines at `pos`: context lines are the
 * file's own matched lines; every other line of N is written as it is, except
 * at tier 2, where a line that is not empty and not only whitespace and starts
 * with P (the leading spaces/tabs of O's first line) has that P replaced by F
 * (the leading spaces/tabs of the file's first matched line).
 */
function buildReplacement(items: BodyItem[], file: string[], pos: number, tier: number): string[] {
  let firstO = '';
  for (const it of items) {
    if (it.kind === 'ctx' || it.kind === 'del') {
      firstO = it.text;
      break;
    }
  }
  const p = leadingWs(firstO);
  const f = leadingWs(file[pos] ?? '');
  const out: string[] = [];
  let oIdx = 0;
  for (const it of items) {
    if (it.kind === 'ctx') {
      out.push(file[pos + oIdx]!);
      oIdx++;
    } else if (it.kind === 'del') {
      oIdx++;
    } else if (it.kind === 'add') {
      let line = it.text;
      if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(p)) {
        line = f + line.slice(p.length);
      }
      out.push(line);
    }
  }
  return out;
}

function oLen(items: BodyItem[]): number {
  return items.filter((it) => it.kind === 'ctx' || it.kind === 'del').length;
}
function nLen(items: BodyItem[]): number {
  return items.filter((it) => it.kind === 'ctx' || it.kind === 'add').length;
}

/** Whether a `\` line follows the body's last context or `+` line. */
function bsAfterLastCtxAdd(items: BodyItem[]): boolean {
  let last = -1;
  for (let k = items.length - 1; k >= 0; k--) {
    if (items[k]!.kind === 'ctx' || items[k]!.kind === 'add') {
      last = k;
      break;
    }
  }
  return last >= 0 && last + 1 < items.length && items[last + 1]!.kind === 'bs';
}

// ---- Detecting the format (SPEC section 4) ----

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---- JSON edits (SPEC section 9) ----

/** One JSON edit object, or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---- Unified diffs (SPEC section 6) ----

interface UniHunk {
  a: number;
  items: BodyItem[];
}

interface UniSection {
  pairOld: string | null | undefined;
  pairNew: string | null | undefined;
  hasPair: boolean;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  diffOld: string | undefined;
  diffNew: string | undefined;
  creation: boolean;
  deletion: boolean;
  hunks: UniHunk[];
}

/** The path of a `--- ` / `+++ ` line: text after the four characters, up to the first tab, trimmed; null for /dev/null. */
function uniPath(line: string): string | null {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/')) p = p.slice(2);
  else if (p.startsWith('b/')) p = p.slice(2);
  return p;
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  let i = 0;
  const n = lines.length;
  const fresh = (): UniSection => ({
    pairOld: undefined,
    pairNew: undefined,
    hasPair: false,
    renameFrom: undefined,
    renameTo: undefined,
    diffOld: undefined,
    diffNew: undefined,
    creation: false,
    deletion: false,
    hunks: [],
  });
  while (i < n) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/([^ ]+) b\/([^ ]+)\s*$/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = fresh();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseInt(m[1]!, 10);
      i++;
      const items: BodyItem[] = [];
      while (i < n) {
        const bl = lines[i]!;
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) break;
        if (bl.startsWith('@@')) break;
        if (bl === '') {
          items.push({ kind: 'ctx', text: '' });
          i++;
          continue;
        }
        const c = bl[0]!;
        if (c === ' ') {
          items.push({ kind: 'ctx', text: bl.slice(1) });
          i++;
          continue;
        }
        if (c === '-') {
          items.push({ kind: 'del', text: bl.slice(1) });
          i++;
          continue;
        }
        if (c === '+') {
          items.push({ kind: 'add', text: bl.slice(1) });
          i++;
          continue;
        }
        if (c === '\\') {
          items.push({ kind: 'bs', text: bl.slice(1) });
          i++;
          continue;
        }
        break;
      }
      while (items.length > 0) {
        const last = items[items.length - 1]!;
        if (last.kind === 'ctx' && last.text === '') items.pop();
        else break;
      }
      cur.hunks.push({ a, items });
      inHeader = false;
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('--- ')) {
        if ((lines[i + 1] ?? '').startsWith('+++ ')) {
          cur.pairOld = uniPath(line);
          cur.pairNew = uniPath(lines[i + 1]!);
          cur.hasPair = true;
          i += 2;
          continue;
        }
        throw new Exit2(`error: parse ${i + 2}`);
      }
      if (line.startsWith('rename from ')) {
        cur.renameFrom = line.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameTo = line.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.creation = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.deletion = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = fresh();
      cur.pairOld = uniPath(line);
      cur.pairNew = uniPath(lines[i + 1]!);
      cur.hasPair = true;
      sections.push(cur);
      inHeader = true;
      i += 2;
      continue;
    }
    i++;
  }
  return sections;
}

/** Apply one hunk to the file's lines, pure: returns the new file state. */
function applyUniHunk(fs: FileState, hunk: UniHunk, d: number, strict: boolean, path: string): FileState {
  const items = hunk.items;
  const oLines = items.filter((it) => it.kind === 'ctx' || it.kind === 'del').map((it) => it.text);
  const bs = bsAfterLastCtxAdd(items);
  if (oLines.length === 0) {
    let pos = hunk.a + d;
    if (pos > fs.lines.length) pos = fs.lines.length;
    if (pos < 0) pos = 0;
    const ins = items.filter((it) => it.kind === 'add').map((it) => it.text);
    const lines = [...fs.lines.slice(0, pos), ...ins, ...fs.lines.slice(pos)];
    const finalBreak = pos === fs.lines.length ? !bs : fs.finalBreak;
    return { lines, br: fs.br, finalBreak };
  }
  const found = findTierAt(fs.lines, oLines, strict, 0);
  if (!found) throw new Fail('no-match', path);
  const target = hunk.a - 1 + d;
  let best = found.occ[0]!;
  let bestDist = Math.abs(best - target);
  for (const p of found.occ) {
    const dist = Math.abs(p - target);
    if (dist < bestDist) {
      best = p;
      bestDist = dist;
    }
  }
  const rep = buildReplacement(items, fs.lines, best, found.tier);
  const lines = [...fs.lines.slice(0, best), ...rep, ...fs.lines.slice(best + oLines.length)];
  const finalBreak = best + oLines.length === fs.lines.length ? !bs : fs.finalBreak;
  return { lines, br: fs.br, finalBreak };
}

function unifiedEdits(lines: string[], strict: boolean, moves: Array<[string, string]>): Edit[] {
  const sections = parseUnified(lines);
  const edits: Edit[] = [];
  for (const s of sections) {
    const oldPath = s.hasPair ? s.pairOld! : (s.renameFrom ?? s.diffOld)!;
    const newPath = s.hasPair ? s.pairNew! : (s.renameTo ?? s.diffNew)!;
    const creation = s.creation || oldPath === null;
    const deletion = !creation && (s.deletion || newPath === null);
    edits.push((tree) => {
      if (oldPath !== null && !safe(oldPath)) throw new Fail('unsafe', oldPath);
      if (newPath !== null && !safe(newPath)) throw new Fail('unsafe', newPath);
      if (creation) {
        const np = newPath!;
        if (tree.get(np) !== null) throw new Fail('exists', np);
        const plusLines: string[] = [];
        for (const h of s.hunks) {
          for (const it of h.items) {
            if (it.kind === 'add') plusLines.push(it.text);
          }
        }
        let finalBreak = true;
        outer: for (let hi = s.hunks.length - 1; hi >= 0; hi--) {
          const items = s.hunks[hi]!.items;
          for (let k = items.length - 1; k >= 0; k--) {
            if (items[k]!.kind === 'add') {
              finalBreak = !(k + 1 < items.length && items[k + 1]!.kind === 'bs');
              break outer;
            }
          }
        }
        tree.now.set(np, plusLines.length === 0 ? '' : plusLines.join('\n') + (finalBreak ? '\n' : ''));
        return;
      }
      if (deletion) {
        const op = oldPath!;
        if (tree.get(op) === null) throw new Fail('missing', op);
        tree.now.set(op, null);
        return;
      }
      const op = oldPath!;
      const np = newPath!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      if (op !== np && tree.get(np) !== null) throw new Fail('exists', np);
      let fs = parseFile(tree.get(op)!);
      let d = 0;
      for (const h of s.hunks) {
        const o = oLen(h.items);
        const nn = nLen(h.items);
        fs = applyUniHunk(fs, h, d, strict, op);
        d += nn - o;
      }
      const out = serializeFile(fs);
      if (op === np) {
        tree.now.set(op, out);
      } else {
        tree.now.set(np, out);
        tree.now.set(op, null);
        moves.push([op, np]);
      }
    });
  }
  return edits;
}

// ---- SEARCH/REPLACE blocks (SPEC section 7) ----

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSR(lines: string[]): SRBlock[] {
  const blocks: SRBlock[] = [];
  let prevReplaceEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const s = i;
    let path: string | null = null;
    for (let j = s - 1; j > prevReplaceEnd; j--) {
      const l = lines[j]!;
      if (l.trim() === '') continue;
      if (l.trimStart().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = prevPath;
    }
    let eq = -1;
    for (let j = s + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '=======') {
        eq = j;
        break;
      }
      // A REPLACE line before any ======= means this block has no =======:
      // the block is malformed, not the start of the next block's new lines.
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') break;
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
    }
    if (eq === -1) throw new Exit2(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j++) {
      if (lines[j]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') break;
    }
    if (rep === -1) throw new Exit2(`error: parse ${s + 1}`);
    blocks.push({ path, oldLines: lines.slice(s + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevReplaceEnd = rep;
    i = rep + 1;
  }
  return blocks;
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  const blocks = parseSR(lines);
  const edits: Edit[] = [];
  for (const b of blocks) {
    edits.push((tree) => {
      const p = b.path;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (b.oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const fs = parseFile(before);
      const found = findTierAt(fs.lines, b.oldLines, strict, 0);
      if (!found) throw new Fail('no-match', p);
      if (found.occ.length > 1) throw new Fail('ambiguous', p);
      const pos = found.occ[0]!;
      const items: BodyItem[] = [
        ...b.oldLines.map((t) => ({ kind: 'del' as const, text: t })),
        ...b.newLines.map((t) => ({ kind: 'add' as const, text: t })),
      ];
      const rep = buildReplacement(items, fs.lines, pos, found.tier);
      const outLines = [...fs.lines.slice(0, pos), ...rep, ...fs.lines.slice(pos + b.oldLines.length)];
      tree.now.set(p, serializeFile({ lines: outLines, br: fs.br, finalBreak: fs.finalBreak }));
    });
  }
  return edits;
}

// ---- V4A patches (SPEC section 8) ----

interface V4AChunk {
  anchor: string | null;
  items: BodyItem[];
  eof: boolean;
}

interface V4ASection {
  kind: 'add' | 'del' | 'upd';
  path: string;
  addLines?: string[];
  moveTo?: string | null;
  chunks?: V4AChunk[];
  startLine: number;
}

function parseV4A(lines: string[]): V4ASection[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!blank(lines[i]!)) {
      first = i;
      break;
    }
  }
  if (first === -1) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!blank(lines[i]!)) {
      last = i;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4ASection[] = [];
  let i = first + 1;
  while (i < last) {
    while (i < last && blank(lines[i]!)) i++;
    if (i >= last) break;
    const line = lines[i]!;
    let kind: 'add' | 'del' | 'upd';
    let path: string;
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice(14).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'del';
      path = line.slice(17).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'upd';
      path = line.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const startLine = i + 1;
    i++;
    const spanStart = i;
    let j = i;
    while (j < last) {
      const l = lines[j]!;
      if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
      j++;
    }
    let spanEnd = j;
    while (spanEnd > spanStart && blank(lines[spanEnd - 1]!)) spanEnd--;
    const span = lines.slice(spanStart, spanEnd);
    if (kind === 'add') {
      const flines: string[] = [];
      for (let k = 0; k < span.length; k++) {
        const l = span[k]!;
        if (l === '') flines.push('');
        else if (l.startsWith('+')) flines.push(l.slice(1));
        else throw new Exit2(`error: parse ${spanStart + k + 1}`);
      }
      sections.push({ kind, path, addLines: flines, startLine });
    } else if (kind === 'del') {
      if (span.length > 0) throw new Exit2(`error: parse ${spanStart + 1}`);
      sections.push({ kind, path, startLine });
    } else {
      let moveTo: string | null = null;
      let k = 0;
      if (k < span.length && span[k]!.startsWith('*** Move to: ')) {
        moveTo = span[k]!.slice(13).trim();
        k++;
      }
      const chunks: V4AChunk[] = [];
      let cur: V4AChunk | null = null;
      const openChunk = (anchor: string | null): void => {
        cur = { anchor, items: [], eof: false };
        chunks.push(cur);
      };
      while (k < span.length) {
        const l = span[k]!;
        const lineNo = spanStart + k + 1;
        if (l.startsWith('@@')) {
          openChunk(l.slice(2).trim() === '' ? null : l.slice(2).trim());
          k++;
          continue;
        }
        if (l.trimEnd() === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${lineNo}`);
          cur.eof = true;
          cur = null;
          k++;
          continue;
        }
        if (l.startsWith('*** ')) throw new Exit2(`error: parse ${lineNo}`);
        if (cur === null) {
          if (chunks.length > 0) throw new Exit2(`error: parse ${lineNo}`);
          openChunk(null);
        }
        const c = l[0];
        if (l === '') cur.items.push({ kind: 'ctx', text: '' });
        else if (c === ' ') cur.items.push({ kind: 'ctx', text: l.slice(1) });
        else if (c === '-') cur.items.push({ kind: 'del', text: l.slice(1) });
        else if (c === '+') cur.items.push({ kind: 'add', text: l.slice(1) });
        else throw new Exit2(`error: parse ${lineNo}`);
        k++;
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${startLine}`);
      sections.push({ kind, path, moveTo, chunks, startLine });
    }
    i = j;
  }
  return sections;
}

function v4aEdits(lines: string[], strict: boolean, moves: Array<[string, string]>): Edit[] {
  const sections = parseV4A(lines);
  const edits: Edit[] = [];
  for (const sec of sections) {
    edits.push((tree) => {
      const p = sec.path;
      if (!safe(p)) throw new Fail('unsafe', p);
      if (sec.kind === 'add') {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const fl = sec.addLines!;
        tree.now.set(p, fl.length === 0 ? '' : fl.join('\n') + '\n');
        return;
      }
      if (sec.kind === 'del') {
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
        return;
      }
      if (sec.moveTo !== null && sec.moveTo !== undefined && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      if (sec.moveTo !== null && sec.moveTo !== undefined && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
      let fs = parseFile(before);
      let cursor = 0;
      for (const ch of sec.chunks!) {
        if (ch.anchor !== null) {
          const idx = findAnchorLine(fs.lines, ch.anchor, cursor, strict);
          if (idx === -1) throw new Fail('no-match', p);
          cursor = idx + 1;
        }
        const oLines = ch.items.filter((it) => it.kind === 'ctx' || it.kind === 'del').map((it) => it.text);
        if (oLines.length === 0) {
          const ins = ch.items.filter((it) => it.kind === 'add').map((it) => it.text);
          const pos = ch.eof ? fs.lines.length : cursor;
          const outLines = [...fs.lines.slice(0, pos), ...ins, ...fs.lines.slice(pos)];
          fs = { lines: outLines, br: fs.br, finalBreak: fs.finalBreak };
          cursor = pos + ins.length;
          continue;
        }
        const found = findTierAt(fs.lines, oLines, strict, cursor);
        let pos = -1;
        let tier = 0;
        if (found) {
          if (ch.eof) {
            const ok = found.occ.filter((q) => q + oLines.length === fs.lines.length);
            if (ok.length > 0) {
              pos = ok[0]!;
              tier = found.tier;
            }
          } else {
            pos = found.occ[0]!;
            tier = found.tier;
          }
        }
        if (pos === -1) throw new Fail('no-match', p);
        const rep = buildReplacement(ch.items, fs.lines, pos, tier);
        const outLines = [...fs.lines.slice(0, pos), ...rep, ...fs.lines.slice(pos + oLines.length)];
        fs = { lines: outLines, br: fs.br, finalBreak: fs.finalBreak };
        cursor = pos + rep.length;
      }
      const out = serializeFile(fs);
      if (sec.moveTo !== null && sec.moveTo !== undefined) {
        tree.now.set(sec.moveTo, out);
        tree.now.set(p, null);
        moves.push([p, sec.moveTo]);
      } else {
        tree.now.set(p, out);
      }
    });
  }
  return edits;
}

// ---- Run (SPEC sections 1, 2 and 10) ----

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const moves: Array<[string, string]> = [];
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict, moves);
    else if (kind === 'search-replace') edits = srEdits(lines, strict);
    else edits = v4aEdits(lines, strict, moves);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const movesBefore = moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      moves.length = movesBefore;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const moveSet = new Set<string>();
  const rows: { key: string; line: string }[] = [];
  for (const [o, nw] of moves) {
    if (tree.original(o) !== null && tree.get(o) === null && tree.original(nw) === null && tree.get(nw) !== null) {
      rows.push({ key: nw, line: `R ${o} -> ${nw}` });
      moveSet.add(o);
      moveSet.add(nw);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (moveSet.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows.map((r) => r.line), `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
