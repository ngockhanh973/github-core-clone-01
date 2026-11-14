// github-core-clone-01: a standalone GitHub-compatible git forge in one process.
// Node 22 standard library only. No git binary, no outside service, no UI.
//
// Surfaces: git smart HTTP (upload-pack v2, receive-pack v0), REST v3 (/api/v3),
// GraphQL v4 (/api/graphql), MCP (/mcp). All state is in-memory, deterministic:
// fixed timestamps, monotonic counters, sorted pack order. No Date.now() or
// Math.random() anywhere in a response path, so two runs agree byte for byte.
//
// Lifecycle (the harness's, not the contest's): bind an ephemeral port, POST
// {"port": N} to $MAKEFUN_ENV_URL/register, poll GET $MAKEFUN_ENV_URL/done
// until {"done": true}, exit 0. Without MAKEFUN_ENV_URL (local runs) the
// server just listens on $PORT (or an ephemeral port) and stays up.

import { createServer } from 'node:http';
import type { IncomingMessage, Server, ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { inflateSync, deflateSync } from 'node:zlib';

// ---------------------------------------------------------------- constants

const VIEWER = { id: 1000, login: 'adaiversen', name: 'ada iversen', email: 'adaiversen@example.invalid' };
const VIEWER_LOGIN = process.env.MAKEFUN_VIEWER_LOGIN ?? VIEWER.login;
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
const FIXED_EPOCH = 1700000000;
const FIXED_ISO = '2026-11-14T06:30:00Z';
const IDENT = `${VIEWER.name} <${VIEWER.email}>`;
const ZERO_OID = '0'.repeat(40);
const HEX40 = /^[0-9a-f]{40}$/;
const AGENT = 'forge/1.0';

// ---------------------------------------------------------------- small utils

function sha1(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}
function isOid(s: unknown): s is string {
  return typeof s === 'string' && HEX40.test(s);
}
function b64encode(buf: Buffer): string {
  return buf.toString('base64');
}
function b64decode(s: string): Buffer {
  return Buffer.from(s.replace(/\s+/g, ''), 'base64');
}
function esc(s: string): string {
  return s;
}

// ---------------------------------------------------------------- git objects

type ObjType = 'commit' | 'tree' | 'blob' | 'tag';
interface GitObj { type: ObjType; data: Buffer; }

function hashObject(type: ObjType, data: Buffer): string {
  const h = createHash('sha1');
  h.update(Buffer.from(`${type} ${data.length}\0`, 'utf8'));
  h.update(data);
  return h.digest('hex');
}

interface TreeEntry { mode: string; name: string; oid: string; }

function treeSortKey(e: TreeEntry): string {
  return e.mode === '40000' ? `${e.name}/` : e.name;
}
function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => (treeSortKey(a) < treeSortKey(b) ? -1 : treeSortKey(a) > treeSortKey(b) ? 1 : 0));
  const parts: Buffer[] = [];
  for (const e of sorted) {
    parts.push(Buffer.from(`${e.mode} ${e.name}\0`, 'utf8'));
    parts.push(Buffer.from(e.oid, 'hex'));
  }
  return Buffer.concat(parts);
}
function parseTree(data: Buffer): TreeEntry[] {
  const out: TreeEntry[] = [];
  let off = 0;
  while (off < data.length) {
    const sp = data.indexOf(0x20, off);
    const nul = data.indexOf(0x00, sp);
    if (sp < 0 || nul < 0 || nul + 21 > data.length) throw new Error('bad tree');
    out.push({ mode: data.subarray(off, sp).toString('utf8'), name: data.subarray(sp + 1, nul).toString('utf8'), oid: data.subarray(nul + 1, nul + 21).toString('hex') });
    off = nul + 21;
  }
  return out;
}
interface CommitView { tree: string; parents: string[]; author: string; committer: string; message: string; }
function parseCommit(data: Buffer): CommitView {
  const blank = data.indexOf('\n\n');
  const head = (blank < 0 ? data : data.subarray(0, blank)).toString('utf8');
  const message = blank < 0 ? '' : data.subarray(blank + 2).toString('utf8');
  let tree = '';
  const parents: string[] = [];
  let author = '';
  let committer = '';
  for (const line of head.split('\n')) {
    if (!line) continue;
    const sp = line.indexOf(' ');
    const k = sp < 0 ? line : line.slice(0, sp);
    const v = sp < 0 ? '' : line.slice(sp + 1);
    if (k === 'tree') tree = v;
    else if (k === 'parent') parents.push(v);
    else if (k === 'author') author = v;
    else if (k === 'committer') committer = v;
  }
  return { tree, parents, author, committer, message };
}
function buildCommit(tree: string, parents: string[], message: string, ts: number = FIXED_EPOCH): Buffer {
  const msg = message.endsWith('\n') ? message : `${message}\n`;
  const lines = [`tree ${tree}`];
  for (const p of parents) lines.push(`parent ${p}`);
  lines.push(`author ${IDENT} ${ts} +0000`, `committer ${IDENT} ${ts} +0000`, '');
  return Buffer.from(`${lines.join('\n')}\n${msg}`, 'utf8');
}
interface TagView { object: string; type: string; tag: string; tagger: string; message: string; }
function parseTag(data: Buffer): TagView {
  const blank = data.indexOf('\n\n');
  const head = (blank < 0 ? data : data.subarray(0, blank)).toString('utf8');
  const m = new Map<string, string>();
  for (const line of head.split('\n')) {
    const sp = line.indexOf(' ');
    if (sp > 0) m.set(line.slice(0, sp), line.slice(sp + 1));
  }
  return { object: m.get('object') ?? '', type: m.get('type') ?? '', tag: m.get('tag') ?? '', tagger: m.get('tagger') ?? '', message: blank < 0 ? '' : data.subarray(blank + 2).toString('utf8') };
}

// ---------------------------------------------------------------- pkt-line

const FLUSH = Buffer.from('0000', 'ascii');
const DELIM = Buffer.from('0001', 'ascii');
function pktLine(payload: string | Buffer): Buffer {
  const data = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  if (data.length > 65520 - 4) throw new Error('pkt-line too long');
  const h = Buffer.alloc(4);
  h.write(((data.length + 4).toString(16)).padStart(4, '0'), 0, 4, 'ascii');
  return Buffer.concat([h, data]);
}
function pktLines(items: Array<string | Buffer | 'flush' | 'delim'>): Buffer {
  const parts: Buffer[] = [];
  for (const it of items) {
    if (it === 'flush') parts.push(FLUSH);
    else if (it === 'delim') parts.push(DELIM);
    else parts.push(pktLine(it));
  }
  return Buffer.concat(parts);
}
type Pkt = { kind: 'data' | 'flush' | 'delim' | 'end'; payload: Buffer };
function parsePktLines(buf: Buffer): Pkt[] {
  const out: Pkt[] = [];
  let off = 0;
  while (off < buf.length) {
    if (off + 4 > buf.length) throw new Error('truncated pkt-line');
    const hex = buf.subarray(off, off + 4).toString('ascii');
    if (hex === '0000') { out.push({ kind: 'flush', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (hex === '0001') { out.push({ kind: 'delim', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (hex === '0002') { out.push({ kind: 'end', payload: Buffer.alloc(0) }); off += 4; continue; }
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error(`bad pkt-line length ${JSON.stringify(hex)}`);
    const len = parseInt(hex, 16);
    if (len < 4 || off + len > buf.length) throw new Error('bad pkt-line length');
    out.push({ kind: 'data', payload: buf.subarray(off + 4, off + len) });
    off += len;
  }
  return out;
}

// ---------------------------------------------------------------- packfile

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let off = 0;
  const readVarint = (): number => {
    let v = 0;
    let shift = 0;
    for (;;) {
      if (off >= delta.length) throw new Error('delta truncated');
      const b = delta[off++];
      v |= (b & 0x7f) << shift;
      shift += 7;
      if (!(b & 0x80)) break;
    }
    return v;
  };
  const srcSize = readVarint();
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  const tgtSize = readVarint();
  const out = Buffer.alloc(tgtSize);
  let written = 0;
  while (off < delta.length) {
    const op = delta[off++];
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      for (let i = 0; i < 4; i++) if (op & (1 << i)) cpOff |= delta[off++] << (8 * i);
      for (let i = 0; i < 3; i++) if (op & (0x10 << i)) cpSize |= delta[off++] << (8 * i);
      if (cpSize === 0) cpSize = 0x10000;
      if (cpOff + cpSize > base.length || written + cpSize > tgtSize) throw new Error('delta copy out of range');
      base.copy(out, written, cpOff, cpOff + cpSize);
      written += cpSize;
    } else if (op !== 0) {
      if (off + op > delta.length || written + op > tgtSize) throw new Error('delta insert out of range');
      delta.copy(out, written, off, off + op);
      off += op;
      written += op;
    } else throw new Error('delta opcode 0');
  }
  if (written !== tgtSize) throw new Error('delta size mismatch');
  return out;
}

interface PackEntry { oid: string; type: ObjType; data: Buffer; }
function readPack(buf: Buffer): PackEntry[] {
  if (buf.length < 12 || buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error('bad pack version');
  const count = buf.readUInt32BE(8);
  const trailerStart = buf.length - 20;
  if (trailerStart < 12) throw new Error('pack too short');
  const expect = sha1(buf.subarray(0, trailerStart));
  if (buf.subarray(trailerStart).toString('hex') !== expect) throw new Error('pack checksum mismatch');
  interface Raw { offset: number; typeCode: number; type: ObjType | null; data: Buffer; baseOffset: number | null; baseOid: string | null; }
  const raws: Raw[] = [];
  let off = 12;
  for (let i = 0; i < count; i++) {
    const start = off;
    if (off >= trailerStart) throw new Error('pack truncated');
    let b = buf[off++];
    const typeCode = (b >> 4) & 7;
    let size = b & 0x0f;
    let shift = 4;
    while (b & 0x80) {
      if (off >= trailerStart) throw new Error('pack truncated');
      b = buf[off++];
      size |= (b & 0x7f) << shift;
      shift += 7;
    }
    let baseOffset: number | null = null;
    let baseOid: string | null = null;
    if (typeCode === 6) {
      if (off >= trailerStart) throw new Error('ofs-delta truncated');
      let bb = buf[off++];
      let base = bb & 0x7f;
      while (bb & 0x80) {
        bb = buf[off++];
        base = ((base + 1) << 7) | (bb & 0x7f);
      }
      baseOffset = start - base;
    } else if (typeCode === 7) {
      if (off + 20 > trailerStart) throw new Error('ref-delta truncated');
      baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
    }
    // find consumed length: the zlib stream is self-terminating; binary-search
    // the smallest prefix that inflates to exactly `size` bytes.
    let consumed = -1;
    {
      let lo = 1;
      let hi = trailerStart - off;
      // binary search smallest prefix that inflates to `size` bytes
      while (lo <= hi) {
        const mid = (lo + hi) >> 1;
        try {
          const out = inflateSync(buf.subarray(off, off + mid));
          if (out.length === size) { consumed = mid; hi = mid - 1; }
          else if (out.length < size) lo = mid + 1;
          else hi = mid - 1;
        } catch {
          lo = mid + 1;
        }
      }
      if (consumed < 0) throw new Error('pack entry inflate failed');
    }
    const data = inflateSync(buf.subarray(off, off + consumed));
    if (data.length !== size) throw new Error('pack entry size mismatch');
    off += consumed;
    const typeMap: Record<number, ObjType | null> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag', 6: null, 7: null };
    raws.push({ offset: start, typeCode, type: typeMap[typeCode] ?? null, data, baseOffset, baseOid });
  }
  const byOffset = new Map<number, PackEntry>();
  const byOid = new Map<string, PackEntry>();
  const resolve = (raw: Raw, seen: Set<number>): PackEntry => {
    const cached = byOffset.get(raw.offset);
    if (cached) return cached;
    if (seen.has(raw.offset)) throw new Error('delta cycle');
    seen.add(raw.offset);
    let entry: PackEntry;
    if (raw.type !== null) {
      entry = { oid: hashObject(raw.type, raw.data), type: raw.type, data: raw.data };
    } else if (raw.baseOffset !== null) {
      const baseRaw = raws.find((r) => r.offset === raw.baseOffset);
      if (!baseRaw) throw new Error('ofs-delta base missing');
      const base = resolve(baseRaw, seen);
      const data = applyDelta(base.data, raw.data);
      entry = { oid: hashObject(base.type, data), type: base.type, data };
    } else {
      const base = byOid.get(raw.baseOid ?? '');
      if (!base) {
        const baseRaw = raws.find((r) => r.type !== null && hashObject(r.type, r.data) === raw.baseOid);
        if (!baseRaw) throw new Error('ref-delta base missing');
        const b = resolve(baseRaw, seen);
        const data = applyDelta(b.data, raw.data);
        entry = { oid: hashObject(b.type, data), type: b.type, data };
      } else {
        const data = applyDelta(base.data, raw.data);
        entry = { oid: hashObject(base.type, data), type: base.type, data };
      }
    }
    byOffset.set(raw.offset, entry);
    byOid.set(entry.oid, entry);
    return entry;
  };
  const out: PackEntry[] = [];
  for (const raw of raws) out.push(resolve(raw, new Set()));
  return out;
}

function writePack(entries: PackEntry[]): Buffer {
  const parts: Buffer[] = [];
  const head = Buffer.alloc(12);
  head.write('PACK', 0, 4, 'ascii');
  head.writeUInt32BE(2, 4);
  head.writeUInt32BE(entries.length, 8);
  parts.push(head);
  const code: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
  for (const e of entries) {
    const size = e.data.length;
    const headerBytes: number[] = [];
    let s = size;
    let first = (code[e.type] << 4) | (s & 0x0f);
    s >>= 4;
    if (s > 0) first |= 0x80;
    headerBytes.push(first);
    while (s > 0) {
      let b = s & 0x7f;
      s >>= 7;
      if (s > 0) b |= 0x80;
      headerBytes.push(b);
    }
    parts.push(Buffer.from(headerBytes));
    parts.push(deflateSync(e.data, { level: 1 }));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

// ---------------------------------------------------------------- store

interface Label { id: number; name: string; color: string; description: string; }
interface Comment { id: number; body: string; }
interface Issue {
  id: number; number: number; title: string; body: string;
  state: 'open' | 'closed'; labels: string[]; comments: Comment[]; seq: number;
}
interface Pull {
  id: number; number: number; title: string; body: string;
  state: 'open' | 'closed'; merged: boolean; mergedAt: string | null; mergeSha: string | null;
  headRef: string; baseRef: string; mergeBase: string; seq: number;
}
interface Repo {
  id: number; name: string; owner: string; description: string; isPrivate: boolean;
  defaultBranch: string; refs: Map<string, string>; objects: Map<string, GitObj>;
  issues: Map<number, Issue>; pulls: Map<number, Pull>; labels: Map<string, Label>;
  seq: number; createdSeq: number;
}

const repos = new Map<string, Repo>();
const reposById = new Map<number, Repo>();
let repoIdSeq = 1;
let objIdSeq = 1;
let globalSeq = 1;
let reqSeq = 1;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}
function getRepo(owner: string, name: string): Repo | undefined {
  return repos.get(repoKey(owner, name));
}
function globalId(kind: string, parts: Array<string | number>): string {
  return Buffer.from(`${kind}:${parts.join(':')}`, 'utf8').toString('base64').replace(/=+$/, '');
}
function decodeGlobalId(id: string): { kind: string; parts: string[] } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const idx = text.indexOf(':');
    if (idx < 0) return null;
    return { kind: text.slice(0, idx), parts: text.slice(idx + 1).split(':') };
  } catch {
    return null;
  }
}

function createRepoRecord(name: string, isPrivate: boolean, description: string): Repo {
  const repo: Repo = {
    id: repoIdSeq++, name, owner: VIEWER_LOGIN, description, isPrivate,
    defaultBranch: 'main', refs: new Map(), objects: new Map(),
    issues: new Map(), pulls: new Map(), labels: new Map(), seq: 0, createdSeq: globalSeq++,
  };
  repos.set(repoKey(repo.owner, name), repo);
  reposById.set(repo.id, repo);
  return repo;
}

// object helpers bound to a repo
function putObj(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) repo.objects.set(oid, { type, data });
  return oid;
}
function getObj(repo: Repo, oid: string): GitObj | undefined {
  return repo.objects.get(oid);
}
function flattenTree(repo: Repo, treeOid: string, prefix: string, out: Map<string, { mode: string; oid: string }>): void {
  const obj = getObj(repo, treeOid);
  if (!obj || obj.type !== 'tree') return;
  for (const e of parseTree(obj.data)) {
    const path = prefix === '' ? e.name : `${prefix}/${e.name}`;
    if (e.mode === '40000') flattenTree(repo, e.oid, path, out);
    else out.set(path, { mode: e.mode, oid: e.oid });
  }
}
function buildTreeFromMap(files: Map<string, { mode: string; oid: string }>): Map<string, Buffer> {
  // returns map treeOid -> tree bytes for every directory tree built (root keyed '')
  const trees = new Map<string, Buffer>();
  const buildDir = (prefix: string): string => {
    const entries: TreeEntry[] = [];
    const seen = new Set<string>();
    for (const [path, f] of files) {
      if (prefix !== '' && !path.startsWith(`${prefix}/`)) continue;
      const rest = prefix === '' ? path : path.slice(prefix.length + 1);
      const seg = rest.split('/')[0];
      if (seen.has(seg)) continue;
      seen.add(seg);
      if (rest.includes('/')) entries.push({ mode: '40000', name: seg, oid: buildDir(prefix === '' ? seg : `${prefix}/${seg}`) });
      else entries.push({ mode: f.mode, name: seg, oid: f.oid });
    }
    const bytes = buildTree(entries);
    const oid = hashObject('tree', bytes);
    trees.set(oid, bytes);
    return oid;
  };
  buildDir('');
  return trees;
}
function commitTree(repo: Repo, baseTreeOid: string | null, changes: Map<string, Buffer | null>): string {
  const files = new Map<string, { mode: string; oid: string }>();
  if (baseTreeOid) flattenTree(repo, baseTreeOid, '', files);
  for (const [path, data] of changes) {
    if (data === null) files.delete(path);
    else files.set(path, { mode: '100644', oid: putObj(repo, 'blob', data) });
  }
  const trees = buildTreeFromMap(files);
  let root = '';
  // root tree is the one built from prefix '' — recompute deterministically:
  const rootEntries: TreeEntry[] = [];
  {
    const seen = new Set<string>();
    for (const [path, f] of files) {
      const seg = path.split('/')[0];
      if (seen.has(seg)) continue;
      seen.add(seg);
      if (path.includes('/')) {
        // find the subtree oid built for this dir: rebuild via helper below
        rootEntries.push({ mode: '40000', name: seg, oid: subtreeOid(repo, files, seg) });
      } else rootEntries.push({ mode: f.mode, name: seg, oid: f.oid });
    }
  }
  const rootBytes = buildTree(rootEntries);
  root = putObj(repo, 'tree', rootBytes);
  // store all intermediate trees too
  for (const [oid, bytes] of trees) if (!repo.objects.has(oid)) repo.objects.set(oid, { type: 'tree', data: bytes });
  return root;
}
function subtreeOid(repo: Repo, files: Map<string, { mode: string; oid: string }>, prefix: string): string {
  const entries: TreeEntry[] = [];
  const seen = new Set<string>();
  for (const [path, f] of files) {
    if (!path.startsWith(`${prefix}/`)) continue;
    const rest = path.slice(prefix.length + 1);
    const seg = rest.split('/')[0];
    if (seen.has(seg)) continue;
    seen.add(seg);
    if (rest.includes('/')) entries.push({ mode: '40000', name: seg, oid: subtreeOid(repo, files, `${prefix}/${seg}`) });
    else entries.push({ mode: f.mode, name: seg, oid: f.oid });
  }
  const bytes = buildTree(entries);
  return putObj(repo, 'tree', bytes);
}
function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  return putObj(repo, 'commit', buildCommit(treeOid, parents, message));
}
function commitParents(repo: Repo, oid: string): string[] {
  const obj = getObj(repo, oid);
  if (!obj || obj.type !== 'commit') return [];
  return parseCommit(obj.data).parents;
}
function commitTreeOid(repo: Repo, oid: string): string {
  const obj = getObj(repo, oid);
  if (!obj || obj.type !== 'commit') return '';
  return parseCommit(obj.data).tree;
}
function peelToCommit(repo: Repo, oid: string): string {
  let cur = oid;
  for (let i = 0; i < 10; i++) {
    const obj = getObj(repo, cur);
    if (!obj) return cur;
    if (obj.type === 'commit') return cur;
    if (obj.type === 'tag') cur = parseTag(obj.data).object;
    else return cur;
  }
  return cur;
}
function commitClosure(repo: Repo, tips: string[]): Set<string> {
  const out = new Set<string>();
  const stack = [...tips];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = getObj(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    out.add(oid);
    for (const p of parseCommit(obj.data).parents) stack.push(p);
  }
  return out;
}
function fullClosure(repo: Repo, tips: string[]): Set<string> {
  const out = new Set<string>();
  const stack = [...tips];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = getObj(repo, oid);
    if (!obj) continue;
    out.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return out;
}
function isAncestor(repo: Repo, anc: string, desc: string): boolean {
  if (anc === desc) return true;
  const seen = new Set<string>();
  const stack = [desc];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (oid === anc) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    for (const p of commitParents(repo, oid)) stack.push(p);
  }
  return false;
}
function mergeBase(repo: Repo, a: string, b: string): string {
  const ancA = commitClosure(repo, [a]);
  const stack = [b];
  const seen = new Set<string>();
  while (stack.length) {
    const oid = stack.pop() as string;
    if (ancA.has(oid)) return oid;
    if (seen.has(oid)) continue;
    seen.add(oid);
    for (const p of commitParents(repo, oid)) stack.push(p);
  }
  return '';
}
function listCommits(repo: Repo, tip: string): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  const stack = [tip];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const obj = getObj(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    out.push(oid);
    const parents = parseCommit(obj.data).parents;
    for (let i = parents.length - 1; i >= 0; i--) stack.push(parents[i]);
  }
  return out;
}
function diffTrees(repo: Repo, baseTreeOid: string | null, headTreeOid: string | null): Array<{ path: string; status: string; additions: number; deletions: number; oldOid: string | null; newOid: string | null }> {
  const base = new Map<string, { mode: string; oid: string }>();
  const head = new Map<string, { mode: string; oid: string }>();
  if (baseTreeOid) flattenTree(repo, baseTreeOid, '', base);
  if (headTreeOid) flattenTree(repo, headTreeOid, '', head);
  const paths = new Set([...base.keys(), ...head.keys()]);
  const out: Array<{ path: string; status: string; additions: number; deletions: number; oldOid: string | null; newOid: string | null }> = [];
  const lineCount = (oid: string | null): { lines: string[]; n: number } => {
    if (!oid) return { lines: [], n: 0 };
    const obj = getObj(repo, oid);
    if (!obj || obj.type !== 'blob') return { lines: [], n: 0 };
    const text = obj.data.toString('utf8');
    const lines = text === '' ? [] : text.split('\n');
    if (lines.length && lines[lines.length - 1] === '') lines.pop();
    return { lines, n: lines.length };
  };
  for (const path of [...paths].sort()) {
    const b = base.get(path);
    const h = head.get(path);
    if (b && !h) {
      const old = lineCount(b.oid);
      out.push({ path, status: 'removed', additions: 0, deletions: old.n, oldOid: b.oid, newOid: null });
    } else if (!b && h) {
      const nw = lineCount(h.oid);
      out.push({ path, status: 'added', additions: nw.n, deletions: 0, oldOid: null, newOid: h.oid });
    } else if (b && h && b.oid !== h.oid) {
      const old = lineCount(b.oid);
      const nw = lineCount(h.oid);
      const oldSet = new Map<string, number>();
      for (const l of old.lines) oldSet.set(l, (oldSet.get(l) ?? 0) + 1);
      let additions = 0;
      for (const l of nw.lines) {
        const c = oldSet.get(l) ?? 0;
        if (c > 0) oldSet.set(l, c - 1);
        else additions++;
      }
      let deletions = 0;
      for (const c of oldSet.values()) deletions += c;
      out.push({ path, status: 'modified', additions, deletions, oldOid: b.oid, newOid: h.oid });
    }
  }
  return out;
}
function prConflict(repo: Repo, pull: Pull): boolean {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? '';
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '';
  if (!headTip || !baseTip || !pull.mergeBase) return false;
  const baseTree = commitTreeOid(repo, pull.mergeBase);
  const headTree = commitTreeOid(repo, headTip);
  const curTree = commitTreeOid(repo, baseTip);
  const headDiff = diffTrees(repo, baseTree, headTree);
  const curDiff = diffTrees(repo, baseTree, curTree);
  const curMap = new Map(curDiff.map((d) => [d.path, d]));
  for (const d of headDiff) {
    const c = curMap.get(d.path);
    if (!c) continue;
    if (c.newOid !== d.newOid) return true;
  }
  return false;
}
function squashMerge(repo: Repo, pull: Pull): { ok: boolean; sha?: string; reason?: string } {
  const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? '';
  const baseTip = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '';
  if (!headTip || !baseTip) return { ok: false, reason: 'missing branch' };
  if (prConflict(repo, pull)) return { ok: false, reason: 'conflict' };
  const headTree = commitTreeOid(repo, headTip);
  const msg = `Merge pull request #${pull.number} from ${pull.headRef}\n\n${pull.title}`;
  const sha = makeCommit(repo, headTree, [baseTip], msg);
  repo.refs.set(`refs/heads/${pull.baseRef}`, sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergedAt = FIXED_ISO;
  pull.mergeSha = sha;
  return { ok: true, sha };
}

// @@NEXT@@

// ---------------------------------------------------------------- http plumbing

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    let total = 0;
    req.on('data', (c: Buffer) => {
      total += c.length;
      if (total > 64 * 1024 * 1024) { reject(new Error('body too large')); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
function sendJson(res: ServerResponse, status: number, body: unknown, extra: Record<string, string> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  res.writeHead(status, {
    'content-type': 'application/json; charset=utf-8',
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `req-${reqSeq++}`,
    ...extra,
  });
  res.end(text);
}
function sendRaw(res: ServerResponse, status: number, buf: Buffer, contentType: string, extra: Record<string, string> = {}): void {
  res.writeHead(status, { 'content-type': contentType, 'content-length': buf.length, ...extra });
  res.end(buf);
}
function sendNoContent(res: ServerResponse, status: number): void {
  res.writeHead(status, { 'x-github-request-id': `req-${reqSeq++}` });
  res.end();
}
function pathOf(req: IncomingMessage): string {
  try {
    return new URL(req.url ?? '/', 'http://entry').pathname;
  } catch {
    return '/';
  }
}
function queryOf(req: IncomingMessage): URLSearchParams {
  try {
    return new URL(req.url ?? '/', 'http://entry').searchParams;
  } catch {
    return new URLSearchParams();
  }
}
type AuthResult = 'ok' | 'missing' | 'wrong';
function checkAuth(req: IncomingMessage): AuthResult {
  const h = req.headers.authorization ?? '';
  if (!h.startsWith('Bearer ')) return 'missing';
  const tok = h.slice('Bearer '.length);
  if (tok === '') return 'missing';
  if (TOKEN !== '' && tok !== TOKEN) return 'wrong';
  return 'ok';
}
function authFail(res: ServerResponse, result: AuthResult): void {
  void result;
  sendJson(res, 401, { message: 'Requires authentication' });
}
function parseJsonBody(buf: Buffer): { ok: true; value: unknown } | { ok: false } {
  if (buf.length === 0) return { ok: true, value: undefined };
  try {
    return { ok: true, value: JSON.parse(buf.toString('utf8')) };
  } catch {
    return { ok: false };
  }
}

// ---------------------------------------------------------------- server

function createApp(): Server {
  const server = createServer((req: IncomingMessage, res: ServerResponse) => {
    handle(req, res).catch((err: unknown) => {
      try {
        sendJson(res, 500, { message: err instanceof Error ? err.message : 'Internal Server Error' });
      } catch { /* socket gone */ }
    });
  });
  server.keepAliveTimeout = 60000;
  server.headersTimeout = 65000;
  return server;
}

async function handle(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const path = pathOf(req);
  const method = req.method ?? 'GET';

  if (method === 'GET' && path === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }
  if (method === 'GET' && (path === '/api/v3' || path === '/api/v3/')) {
    sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }
  if (method === 'GET' && path === '/api/v3/meta') {
    sendJson(res, 200, { installed_version: '1.0.0' });
    return;
  }

  if (await handleGit(req, res, path)) return;
  if (await handleRest(req, res, path)) return;
  if (await handleGraphQL(req, res, path)) return;
  if (await handleMcp(req, res, path)) return;

  sendJson(res, 404, { message: 'Not Found' });
}

// ---------------------------------------------------------------- git smart HTTP

function sortedRefs(repo: Repo): Array<{ name: string; oid: string }> {
  return [...repo.refs.entries()].map(([name, oid]) => ({ name, oid })).sort((a, b) => (a.name < b.name ? -1 : 1));
}
function refCaps(service: 'git-upload-pack' | 'git-receive-pack'): string {
  if (service === 'git-upload-pack') {
    return `symref=HEAD:refs/heads/main object-format=sha1 side-band-64k side-band thin-pack ofs-delta shallow multi_ack agent=${AGENT}`;
  }
  return `symref=HEAD:refs/heads/main report-status side-band-64k delete-refs ofs-delta agent=${AGENT}`;
}
function v0Advertisement(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const caps = refCaps(service);
  const lines: Array<string | Buffer | 'flush' | 'delim'> = [`# service=${service}\n`, 'flush'];
  const refs = sortedRefs(repo);
  const mainTip = repo.refs.get('refs/heads/main') ?? ZERO_OID;
  if (refs.length === 0) {
    lines.push(`${ZERO_OID} capabilities^{}\0${caps}\n`, 'flush');
    return pktLines(lines);
  }
  let first = true;
  const emit = (line: string): void => {
    if (first) { lines.push(`${line}\0${caps}\n`); first = false; }
    else lines.push(`${line}\n`);
  };
  emit(`${mainTip} HEAD`);
  for (const r of refs) {
    emit(`${r.oid} ${r.name}`);
    if (r.name.startsWith('refs/tags/')) {
      const obj = getObj(repo, r.oid);
      if (obj?.type === 'tag') {
        const peeled = peelToCommit(repo, r.oid);
        lines.push(`${peeled} ${r.name}^{}\n`);
      }
    }
  }
  lines.push('flush');
  return pktLines(lines);
}
function v2Advertisement(): Buffer {
  return pktLines(['# service=git-upload-pack\n', 'flush', 'version 2\n', 'ls-refs=unborn\n', 'fetch=shallow filter\n', 'object-format=sha1\n', `agent=${AGENT}\n`, 'flush']);
}

interface LsRefsArgs { peel: boolean; symrefs: boolean; unborn: boolean; prefixes: string[]; }
function parseLsRefsArgs(packets: Pkt[]): LsRefsArgs {
  const args: LsRefsArgs = { peel: false, symrefs: false, unborn: false, prefixes: [] };
  let seenDelim = false;
  for (const p of packets) {
    if (p.kind === 'delim') { seenDelim = true; continue; }
    if (p.kind !== 'data') continue;
    const line = p.payload.toString('utf8').trim();
    if (!seenDelim) continue;
    if (line === 'peel') args.peel = true;
    else if (line === 'symrefs') args.symrefs = true;
    else if (line === 'unborn') args.unborn = true;
    else if (line.startsWith('ref-prefix ')) args.prefixes.push(line.slice('ref-prefix '.length));
  }
  return args;
}
function lsRefsResponse(repo: Repo, args: LsRefsArgs): Buffer {
  const lines: string[] = [];
  const mainTip = repo.refs.get('refs/heads/main');
  if (args.prefixes.length === 0) {
    if (mainTip) lines.push(`${mainTip} HEAD${args.symrefs ? ' symref-target:refs/heads/main' : ''}\n`);
    else if (args.unborn) lines.push(`unborn HEAD symref-target:refs/heads/main\n`);
  }
  for (const r of sortedRefs(repo)) {
    if (args.prefixes.length > 0 && !args.prefixes.some((p) => r.name.startsWith(p))) continue;
    let line = `${r.oid} ${r.name}`;
    if (args.peel && r.name.startsWith('refs/tags/')) {
      const obj = getObj(repo, r.oid);
      if (obj?.type === 'tag') line += ` peeled:${peelToCommit(repo, r.oid)}`;
    }
    lines.push(`${line}\n`);
  }
  return pktLines([...lines, 'flush']);
}

interface FetchArgs { wants: string[]; haves: string[]; shallow: string[]; depth: number | null; deepenSince: number | null; deepenNot: string[]; }
function parseFetchArgs(packets: Pkt[]): FetchArgs {
  const args: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, deepenSince: null, deepenNot: [] };
  let seenDelim = false;
  for (const p of packets) {
    if (p.kind === 'delim') { seenDelim = true; continue; }
    if (p.kind !== 'data') continue;
    const line = p.payload.toString('utf8').trim();
    if (!seenDelim) continue;
    if (line.startsWith('want ')) args.wants.push(line.slice(5));
    else if (line.startsWith('have ')) args.haves.push(line.slice(5));
    else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8));
    else if (line.startsWith('deepen ')) args.depth = parseInt(line.slice(7), 10);
    else if (line.startsWith('deepen-since ')) args.deepenSince = parseInt(line.slice(13), 10);
    else if (line.startsWith('deepen-not ')) args.deepenNot.push(line.slice(11));
  }
  return args;
}
// Object closure from tips that does not cross shallow boundaries: a commit
// listed in `shallow` contributes itself and its tree, but not its parents
// (the client does not have them, so they must still be sendable).
function closureWithShallow(repo: Repo, tips: string[], shallow: Set<string>): Set<string> {
  const out = new Set<string>();
  const stack = [...tips];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = getObj(repo, oid);
    if (!obj) continue;
    out.add(oid);
    if (obj.type === 'commit') {
      const c = parseCommit(obj.data);
      stack.push(c.tree);
      if (!shallow.has(oid)) for (const p of c.parents) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return out;
}
function treeClosure(repo: Repo, treeOid: string, out: Set<string>): void {
  const stack = [treeOid];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = getObj(repo, oid);
    if (!obj) continue;
    out.add(oid);
    if (obj.type === 'tree') for (const e of parseTree(obj.data)) stack.push(e.oid);
  }
}
function selectFetch(repo: Repo, args: FetchArgs): { objects: PackEntry[]; shallow: string[]; unshallow: string[] } {
  const roots: string[] = [];
  const direct = new Set<string>();
  for (const w of args.wants) {
    const obj = getObj(repo, w);
    if (!obj) continue;
    if (obj.type === 'commit') roots.push(w);
    else if (obj.type === 'tag') { direct.add(w); roots.push(peelToCommit(repo, w)); }
    else direct.add(w);
  }
  let D: Set<string>;
  if (args.depth === null) {
    D = commitClosure(repo, roots);
  } else {
    D = new Set<string>();
    let frontier = [...roots];
    for (let d = 0; d < args.depth && frontier.length > 0; d++) {
      const next: string[] = [];
      for (const c of frontier) {
        if (D.has(c)) continue;
        const obj = getObj(repo, c);
        if (!obj || obj.type !== 'commit') continue;
        D.add(c);
        for (const p of parseCommit(obj.data).parents) next.push(p);
      }
      frontier = next;
    }
  }
  // Object set to send: depth-limited fetches take only D's own commits and
  // their trees/blobs — never ancestors. Full fetches take the whole closure.
  const wantSet = new Set<string>();
  if (args.depth === null) {
    for (const o of fullClosure(repo, [...D, ...direct])) wantSet.add(o);
  } else {
    for (const c of D) {
      wantSet.add(c);
      treeClosure(repo, commitTreeOid(repo, c), wantSet);
    }
    for (const oid of direct) {
      wantSet.add(oid);
      const obj = getObj(repo, oid);
      if (obj?.type === 'tag') {
        const target = parseTag(obj.data).object;
        if (getObj(repo, target)?.type === 'commit') { wantSet.add(target); treeClosure(repo, commitTreeOid(repo, target), wantSet); }
        else if (getObj(repo, target)?.type === 'tree') treeClosure(repo, target, wantSet);
      }
    }
  }
  const haveClosure = closureWithShallow(repo, args.haves, new Set(args.shallow));
  const haveSet = new Set(args.haves);
  const send = [...wantSet].filter((o) => !haveClosure.has(o)).sort();
  const objects: PackEntry[] = send.map((oid) => {
    const o = getObj(repo, oid) as GitObj;
    return { oid, type: o.type, data: o.data };
  });
  const shallow: string[] = [];
  const unshallow: string[] = [];
  for (const c of D) {
    const parents = commitParents(repo, c);
    if (parents.length === 0) continue;
    if (args.shallow.includes(c) && parents.every((p) => D.has(p))) { unshallow.push(c); continue; }
    if (parents.some((p) => !D.has(p) && !haveSet.has(p))) shallow.push(c);
  }
  return { objects, shallow, unshallow };
}
function sidebandPack(pack: Buffer): Buffer {
  const out: Buffer[] = [];
  for (let off = 0; off < pack.length; off += 65515) {
    const chunk = pack.subarray(off, Math.min(off + 65515, pack.length));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  if (pack.length === 0) out.push(pktLine(Buffer.from([1])));
  return Buffer.concat(out);
}
function v2FetchResponse(repo: Repo, args: FetchArgs): Buffer {
  const sel = selectFetch(repo, args);
  const parts: Buffer[] = [];
  parts.push(pktLine('acknowledgments\n'));
  const wantClosure = commitClosure(repo, args.wants.filter((w) => {
    const o = getObj(repo, w);
    return !!o && o.type === 'commit';
  }));
  const ack = args.haves.find((h) => wantClosure.has(h));
  if (ack) { parts.push(pktLine(`ACK ${ack}\n`)); parts.push(pktLine('ready\n')); }
  else parts.push(pktLine('NAK\n'));
  parts.push(FLUSH);
  if (sel.shallow.length > 0 || sel.unshallow.length > 0) {
    parts.push(pktLine('shallow-info\n'));
    for (const s of sel.shallow) parts.push(pktLine(`shallow ${s}\n`));
    for (const s of sel.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
    parts.push(FLUSH);
  }
  parts.push(pktLine('packfile\n'));
  parts.push(sidebandPack(writePack(sel.objects)));
  parts.push(FLUSH);
  return Buffer.concat(parts);
}
function v0FetchResponse(repo: Repo, body: Buffer): Buffer {
  const packets = parsePktLines(body);
  const args: FetchArgs = { wants: [], haves: [], shallow: [], depth: null, deepenSince: null, deepenNot: [] };
  let section = 0;
  for (const p of packets) {
    if (p.kind === 'flush') { section++; continue; }
    if (p.kind !== 'data') continue;
    let line = p.payload.toString('utf8').trim();
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    if (section === 0) {
      if (line.startsWith('want ')) args.wants.push(line.slice(5));
      else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8));
      else if (line.startsWith('deepen ')) args.depth = parseInt(line.slice(7), 10);
      else if (line.startsWith('deepen-since ')) args.deepenSince = parseInt(line.slice(13), 10);
      else if (line.startsWith('deepen-not ')) args.deepenNot.push(line.slice(11));
    } else if (line.startsWith('have ')) args.haves.push(line.slice(5));
  }
  const sel = selectFetch(repo, args);
  const parts: Buffer[] = [];
  const wantClosure = commitClosure(repo, args.wants.filter((w) => {
    const o = getObj(repo, w);
    return !!o && o.type === 'commit';
  }));
  const ack = args.haves.find((h) => wantClosure.has(h));
  if (ack) parts.push(pktLine(`ACK ${ack}\n`));
  else parts.push(pktLine('NAK\n'));
  for (const s of sel.shallow) parts.push(pktLine(`shallow ${s}\n`));
  for (const s of sel.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
  parts.push(sidebandPack(writePack(sel.objects)));
  parts.push(FLUSH);
  return Buffer.concat(parts);
}

interface PushCmd { oldOid: string; newOid: string; ref: string; }
function receivePackResponse(repo: Repo, body: Buffer): Buffer {
  // Scan raw pkt-lines until the first flush; everything after it is the pack.
  const cmds: PushCmd[] = [];
  let off = 0;
  let seenFlush = false;
  while (off < body.length) {
    if (off + 4 > body.length) throw new Error('truncated body');
    const hex = body.subarray(off, off + 4).toString('ascii');
    if (hex === '0000') { seenFlush = true; off += 4; break; }
    if (hex === '0001') { off += 4; continue; }
    if (!/^[0-9a-fA-F]{4}$/.test(hex)) throw new Error('bad pkt-line length');
    const len = parseInt(hex, 16);
    if (len < 4 || off + len > body.length) throw new Error('bad pkt-line length');
    let line = body.subarray(off + 4, off + len).toString('utf8');
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    const m = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)\s*$/.exec(line);
    if (!m) throw new Error('bad receive-pack command line');
    cmds.push({ oldOid: m[1], newOid: m[2], ref: m[3] });
    off += len;
  }
  if (!seenFlush) throw new Error('missing flush before pack');
  const rawPack = body.subarray(off);
  let unpackError: string | null = null;
  if (rawPack.length > 0) {
    try {
      const entries = readPack(rawPack);
      for (const e of entries) {
        if (!repo.objects.has(e.oid)) repo.objects.set(e.oid, { type: e.type, data: e.data });
      }
    } catch (err) {
      unpackError = err instanceof Error ? err.message : 'unpack failed';
    }
  }
  const lines: string[] = [];
  if (unpackError) {
    lines.push(`unpack ${unpackError}\n`);
    for (const c of cmds) lines.push(`ng ${c.ref} unpack failed\n`);
  } else {
    lines.push('unpack ok\n');
    for (const c of cmds) {
      if (!c.ref.startsWith('refs/')) { lines.push(`ng ${c.ref} invalid ref\n`); continue; }
      const current = repo.refs.get(c.ref);
      if (c.newOid === ZERO_OID) {
        if (current === undefined) lines.push(`ng ${c.ref} no such ref\n`);
        else if (current !== c.oldOid) lines.push(`ng ${c.ref} non-fast-forward\n`);
        else { repo.refs.delete(c.ref); lines.push(`ok ${c.ref}\n`); }
      } else if (c.oldOid === ZERO_OID) {
        if (current !== undefined) lines.push(`ng ${c.ref} non-fast-forward\n`);
        else { repo.refs.set(c.ref, c.newOid); lines.push(`ok ${c.ref}\n`); }
      } else {
        if (current === undefined || current !== c.oldOid) lines.push(`ng ${c.ref} non-fast-forward\n`);
        else if (isAncestor(repo, c.oldOid, c.newOid)) { repo.refs.set(c.ref, c.newOid); lines.push(`ok ${c.ref}\n`); }
        else lines.push(`ng ${c.ref} non-fast-forward\n`);
      }
    }
  }
  const inner = pktLines([...lines, 'flush']);
  const out: Buffer[] = [];
  for (let off = 0; off < inner.length; off += 65515) {
    const chunk = inner.subarray(off, Math.min(off + 65515, inner.length));
    out.push(pktLine(Buffer.concat([Buffer.from([1]), chunk])));
  }
  out.push(FLUSH);
  return Buffer.concat(out);
}

async function handleGit(req: IncomingMessage, res: ServerResponse, path: string): Promise<boolean> {
  const m = /^\/(.+?)\/(.+?)\.git\/(.*)$/.exec(path);
  if (!m) return false;
  const owner = decodeURIComponent(m[1]);
  const repoName = decodeURIComponent(m[2]);
  const tail = m[3];
  const method = req.method ?? 'GET';
  const q = queryOf(req);
  const auth = checkAuth(req);
  if (auth !== 'ok') { authFail(res, auth); return true; }
  const repo = getRepo(owner, repoName);
  if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }

  if (method === 'GET' && tail === 'info/refs') {
    const service = q.get('service') ?? '';
    if (service === 'git-upload-pack') {
      const v2 = (req.headers['git-protocol'] ?? '') === 'version=2';
      sendRaw(res, 200, v2 ? v2Advertisement() : v0Advertisement(repo, 'git-upload-pack'), 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-receive-pack') {
      sendRaw(res, 200, v0Advertisement(repo, 'git-receive-pack'), 'application/x-git-receive-pack-advertisement');
      return true;
    }
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }
  if (method === 'POST' && tail === 'git-upload-pack') {
    const body = await readBody(req);
    const v2 = (req.headers['git-protocol'] ?? '') === 'version=2';
    let packets: Pkt[];
    try {
      packets = parsePktLines(body);
    } catch {
      sendJson(res, 400, { message: 'malformed pkt-line' });
      return true;
    }
    const first = packets.find((p) => p.kind === 'data');
    const command = first ? first.payload.toString('utf8').trim().replace(/^command=/, '') : '';
    if (v2 && command === 'ls-refs') {
      sendRaw(res, 200, lsRefsResponse(repo, parseLsRefsArgs(packets)), 'application/x-git-upload-pack-result');
      return true;
    }
    if (v2 && command === 'fetch') {
      sendRaw(res, 200, v2FetchResponse(repo, parseFetchArgs(packets)), 'application/x-git-upload-pack-result');
      return true;
    }
    if (!v2) {
      sendRaw(res, 200, v0FetchResponse(repo, body), 'application/x-git-upload-pack-result');
      return true;
    }
    sendJson(res, 400, { message: 'unknown command' });
    return true;
  }
  if (method === 'POST' && tail === 'git-receive-pack') {
    const body = await readBody(req);
    let out: Buffer;
    try {
      out = receivePackResponse(repo, body);
    } catch {
      sendJson(res, 400, { message: 'malformed receive-pack' });
      return true;
    }
    sendRaw(res, 200, out, 'application/x-git-receive-pack-result');
    return true;
  }
  sendJson(res, 404, { message: 'Not Found' });
  return true;
}

// ---------------------------------------------------------------- REST v3

type J = Record<string, unknown>;
function viewerShape(): J {
  return {
    login: VIEWER_LOGIN, id: VIEWER.id, name: VIEWER.name, email: VIEWER.email, type: 'User',
    url: `/api/v3/users/${VIEWER_LOGIN}`, html_url: `https://github.com/${VIEWER_LOGIN}`,
    avatar_url: `https://avatars.githubusercontent.com/u/${VIEWER.id}?v=4`, site_admin: false,
  };
}
function openCount(repo: Repo): number {
  let n = 0;
  for (const i of repo.issues.values()) if (i.state === 'open') n++;
  for (const p of repo.pulls.values()) if (p.state === 'open') n++;
  return n;
}
function repoShape(repo: Repo): J {
  return {
    id: repo.id, name: repo.name, full_name: `${repo.owner}/${repo.name}`, owner: viewerShape(),
    private: repo.isPrivate, description: repo.description, default_branch: repo.defaultBranch,
    created_at: FIXED_ISO, updated_at: FIXED_ISO, pushed_at: FIXED_ISO,
    html_url: `https://github.com/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    clone_url: `https://github.com/${repo.owner}/${repo.name}.git`,
    git_url: `git://github.com/${repo.owner}/${repo.name}.git`,
    ssh_url: `git@github.com:${repo.owner}/${repo.name}.git`,
    homepage: null, language: null, fork: false, forks_count: 0, stargazers_count: 0,
    watchers_count: 0, open_issues_count: openCount(repo),
    has_issues: true, has_projects: true, has_wiki: true, has_pages: false,
    archived: false, disabled: false, visibility: repo.isPrivate ? 'private' : 'public',
  };
}
function labelShape(l: Label): J {
  return { id: l.id, name: l.name, color: l.color, description: l.description, default: false, url: '' };
}
function issueShape(repo: Repo, issue: Issue): J {
  return {
    id: issue.id, number: issue.number, title: issue.title, body: issue.body, state: issue.state,
    labels: issue.labels.map((name) => {
      const l = repo.labels.get(name);
      return l ? labelShape(l) : { name, color: '000000', description: '' };
    }),
    user: viewerShape(), assignee: null, assignees: [], milestone: null, locked: false,
    comments: issue.comments.length, created_at: FIXED_ISO, updated_at: FIXED_ISO, closed_at: issue.state === 'closed' ? FIXED_ISO : null,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}
function commentShape(repo: Repo, c: Comment): J {
  return {
    id: c.id, body: c.body, user: viewerShape(), created_at: FIXED_ISO, updated_at: FIXED_ISO,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${c.id}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/comments/${c.id}`,
  };
}
function pullShape(repo: Repo, pull: Pull): J {
  const headSha = repo.refs.get(`refs/heads/${pull.headRef}`) ?? '';
  const baseSha = repo.refs.get(`refs/heads/${pull.baseRef}`) ?? '';
  return {
    id: pull.id, number: pull.number, title: pull.title, body: pull.body, state: pull.state,
    merged: pull.merged, merged_at: pull.mergedAt, merge_commit_sha: pull.mergeSha,
    mergeable: !prConflict(repo, pull), draft: false, locked: false,
    head: { ref: pull.headRef, sha: headSha, label: `${repo.owner}:${pull.headRef}`, user: viewerShape() },
    base: { ref: pull.baseRef, sha: baseSha, label: `${repo.owner}:${pull.baseRef}`, user: viewerShape() },
    user: viewerShape(), assignee: null, assignees: [], requested_reviewers: [],
    created_at: FIXED_ISO, updated_at: FIXED_ISO, closed_at: pull.state === 'closed' ? FIXED_ISO : null,
    html_url: `https://github.com/${repo.owner}/${repo.name}/pull/${pull.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/pulls/${pull.number}`,
  };
}
function commitShape(repo: Repo, oid: string): J {
  const obj = getObj(repo, oid);
  const c = obj && obj.type === 'commit' ? parseCommit(obj.data) : null;
  const message = c ? c.message.replace(/\n$/, '') : '';
  return {
    sha: oid,
    commit: {
      message,
      author: { name: VIEWER.name, email: VIEWER.email, date: FIXED_ISO },
      committer: { name: VIEWER.name, email: VIEWER.email, date: FIXED_ISO },
      tree: { sha: c?.tree ?? '' },
    },
    author: viewerShape(), committer: viewerShape(),
    parents: (c?.parents ?? []).map((p) => ({ sha: p })),
    url: `/api/v3/repos/${repo.owner}/${repo.name}/commits/${oid}`,
    html_url: `https://github.com/${repo.owner}/${repo.name}/commit/${oid}`,
  };
}
function pageParams(q: URLSearchParams): { perPage: number; page: number } {
  const perPage = Math.min(100, Math.max(1, parseInt(q.get('per_page') ?? '30', 10) || 30));
  const page = Math.max(1, parseInt(q.get('page') ?? '1', 10) || 1);
  return { perPage, page };
}
function paginate<T>(items: T[], q: URLSearchParams, req: IncomingMessage): { page: T[]; link: string | null } {
  const { perPage, page } = pageParams(q);
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const total = items.length;
  const host = req.headers.host ?? '127.0.0.1';
  const base = `http://${host}${pathOf(req)}`;
  const links: string[] = [];
  const qp = new URLSearchParams(q);
  if (start + perPage < total) {
    qp.set('page', String(page + 1));
    qp.set('per_page', String(perPage));
    links.push(`<${base}?${qp.toString()}>; rel="next"`);
  }
  if (page > 1) {
    qp.set('page', String(page - 1));
    links.push(`<${base}?${qp.toString()}>; rel="prev"`);
  }
  return { page: slice, link: links.length > 0 ? links.join(', ') : null };
}
function sendPage(res: ServerResponse, items: unknown[], q: URLSearchParams, req: IncomingMessage): void {
  const { page, link } = paginate(items, q, req);
  sendJson(res, 200, page, link ? { link } : {});
}

async function handleRest(req: IncomingMessage, res: ServerResponse, path: string): Promise<boolean> {
  if (!path.startsWith('/api/v3')) return false;
  const method = req.method ?? 'GET';
  const q = queryOf(req);
  const auth = checkAuth(req);
  if (auth !== 'ok') { authFail(res, auth); return true; }

  const needsBody = method === 'POST' || method === 'PATCH' || method === 'PUT' || method === 'DELETE';
  let body: unknown;
  if (needsBody) {
    const raw = await readBody(req);
    const parsed = parseJsonBody(raw);
    if (!parsed.ok) { sendJson(res, 400, { message: 'Invalid JSON' }); return true; }
    body = parsed.value;
  }
  const b = (body ?? {}) as J;

  // GET /api/v3/user
  if (method === 'GET' && path === '/api/v3/user') {
    sendJson(res, 200, viewerShape());
    return true;
  }
  // /api/v3/user/repos
  if (path === '/api/v3/user/repos') {
    if (method === 'GET') {
      const all = [...repos.values()].filter((r) => r.owner === VIEWER_LOGIN).sort((a, b2) => a.createdSeq - b2.createdSeq);
      sendPage(res, all.map((r) => repoShape(r)), q, req);
      return true;
    }
    if (method === 'POST') {
      const name = typeof b.name === 'string' ? b.name : '';
      if (name === '' || !/^[A-Za-z0-9._-]+$/.test(name)) { sendJson(res, 422, { message: 'name is invalid' }); return true; }
      if (getRepo(VIEWER_LOGIN, name)) { sendJson(res, 422, { message: `name already exists on this account` }); return true; }
      const repo = createRepoRecord(name, b.private === true, typeof b.description === 'string' ? b.description : '');
      sendJson(res, 201, repoShape(repo));
      return true;
    }
  }

  const m = /^\/api\/v3\/repos\/([^/]+)\/([^/]+)(?:\/(.*))?$/.exec(path);
  if (!m) {
    if (path === '/api/v3/graphql') return false; // handled by the GraphQL dispatcher
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }
  const owner = decodeURIComponent(m[1]);
  const repoName = decodeURIComponent(m[2]);
  const tail = m[3] ?? '';
  const repo = getRepo(owner, repoName);
  if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }

  const resolveBranchTip = (ref: string | null): string => {
    if (ref === null) return repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? '';
    if (repo.refs.has(`refs/heads/${ref}`)) return repo.refs.get(`refs/heads/${ref}`) as string;
    const obj = getObj(repo, ref);
    return obj && obj.type === 'commit' ? ref : '';
  };
  const branchName = (ref: string | null): string => ref ?? repo.defaultBranch;

  if (tail === '' && method === 'GET') { sendJson(res, 200, repoShape(repo)); return true; }
  if (tail === '' && method === 'PATCH') {
    if (typeof b.description === 'string') repo.description = b.description;
    if (typeof b.name === 'string' && b.name !== '' && b.name !== repo.name) {
      if (getRepo(owner, b.name)) { sendJson(res, 422, { message: 'name already exists on this account' }); return true; }
      repos.delete(repoKey(repo.owner, repo.name));
      repo.name = b.name;
      repos.set(repoKey(repo.owner, repo.name), repo);
    }
    if (typeof b.default_branch === 'string' && repo.refs.has(`refs/heads/${b.default_branch}`)) repo.defaultBranch = b.default_branch;
    sendJson(res, 200, repoShape(repo));
    return true;
  }
  if (tail === '' && method === 'DELETE') {
    repos.delete(repoKey(repo.owner, repo.name));
    reposById.delete(repo.id);
    sendNoContent(res, 204);
    return true;
  }

  // branches
  if (tail === 'branches' && method === 'GET') {
    const list = sortedRefs(repo).filter((r) => r.name.startsWith('refs/heads/'))
      .map((r) => ({ name: r.name.slice('refs/heads/'.length), commit: { sha: r.oid }, protected: false }));
    sendPage(res, list, q, req);
    return true;
  }
  {
    const bm = /^branches\/([^/]+)$/.exec(tail);
    if (bm && method === 'GET') {
      const name = decodeURIComponent(bm[1]);
      const tip = repo.refs.get(`refs/heads/${name}`);
      if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      sendJson(res, 200, { name, commit: { sha: tip }, protected: false });
      return true;
    }
  }
  // git refs
  {
    const gm = /^git\/refs\/heads\/([^/]+)$/.exec(tail);
    if (gm && method === 'GET') {
      const name = decodeURIComponent(gm[1]);
      const tip = repo.refs.get(`refs/heads/${name}`);
      if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      sendJson(res, 200, { ref: `refs/heads/${name}`, object: { sha: tip, type: 'commit' } });
      return true;
    }
  }
  if (tail === 'git/refs' && method === 'POST') {
    const ref = typeof b.ref === 'string' ? b.ref : '';
    const sha = typeof b.sha === 'string' ? b.sha : '';
    if (!ref.startsWith('refs/') || !isOid(sha)) { sendJson(res, 422, { message: 'invalid ref or sha' }); return true; }
    if (repo.refs.has(ref)) { sendJson(res, 422, { message: 'Reference already exists' }); return true; }
    const obj = getObj(repo, sha);
    if (!obj || obj.type !== 'commit') { sendJson(res, 422, { message: 'Object does not exist' }); return true; }
    repo.refs.set(ref, sha);
    sendJson(res, 201, { ref, object: { sha, type: 'commit' } });
    return true;
  }
  // commits
  if (tail === 'commits' && method === 'GET') {
    const ref = q.get('sha');
    const tip = resolveBranchTip(ref);
    if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return true; }
    const list = listCommits(repo, tip).map((oid) => commitShape(repo, oid));
    sendPage(res, list, q, req);
    return true;
  }
  // contents
  if (tail.startsWith('contents/')) {
    const rawPath = tail.slice('contents/'.length);
    const cpath = rawPath.split('/').map((s) => decodeURIComponent(s)).join('/');
    const refParam = q.get('ref');
    if (method === 'GET') {
      const tip = resolveBranchTip(refParam);
      if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      const treeOid = commitTreeOid(repo, tip);
      const files = new Map<string, { mode: string; oid: string }>();
      flattenTree(repo, treeOid, '', files);
      const exact = files.get(cpath);
      if (exact) {
        const obj = getObj(repo, exact.oid);
        const data = obj && obj.type === 'blob' ? obj.data : Buffer.alloc(0);
        sendJson(res, 200, {
          type: 'file', encoding: 'base64', size: data.length, name: cpath.split('/').pop(),
          path: cpath, sha: exact.oid, content: b64encode(data),
          url: `/api/v3/repos/${owner}/${repoName}/contents/${cpath}`,
          html_url: `https://github.com/${owner}/${repoName}/blob/${branchName(refParam)}/${cpath}`,
          download_url: null, git_url: '',
        });
        return true;
      }
      // directory listing: immediate children
      const prefix = cpath === '' ? '' : `${cpath}/`;
      const children = new Map<string, { type: string; oid: string; path: string }>();
      for (const [p, f] of files) {
        if (!p.startsWith(prefix)) continue;
        const rest = p.slice(prefix.length);
        const seg = rest.split('/')[0];
        const childPath = prefix + seg;
        if (children.has(seg)) continue;
        children.set(seg, { type: rest.includes('/') ? 'dir' : 'file', oid: rest.includes('/') ? '' : f.oid, path: childPath });
      }
      if (children.size === 0) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      const entries = [...children.entries()].sort((a, b2) => (a[0] < b2[0] ? -1 : 1)).map(([name, c]) => ({
        type: c.type, size: 0, name, path: c.path, sha: c.oid,
        url: `/api/v3/repos/${owner}/${repoName}/contents/${c.path}`,
        html_url: `https://github.com/${owner}/${repoName}/tree/${branchName(refParam)}/${c.path}`,
        download_url: null, git_url: '',
      }));
      sendJson(res, 200, entries);
      return true;
    }
    if (method === 'PUT') {
      const message = typeof b.message === 'string' ? b.message : `Update ${cpath}`;
      const contentB64 = typeof b.content === 'string' ? b.content : '';
      const data = b64decode(contentB64);
      const branch = typeof b.branch === 'string' ? b.branch : repo.defaultBranch;
      let tip = repo.refs.get(`refs/heads/${branch}`);
      if (tip === undefined) {
        const defTip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
        if (defTip !== undefined) { repo.refs.set(`refs/heads/${branch}`, defTip); tip = defTip; }
      }
      const baseTree = tip ? commitTreeOid(repo, tip) : null;
      const files = new Map<string, { mode: string; oid: string }>();
      if (baseTree) flattenTree(repo, baseTree, '', files);
      const existing = files.get(cpath);
      const givenSha = typeof b.sha === 'string' ? b.sha : undefined;
      if (existing) {
        if (!givenSha) { sendJson(res, 422, { message: 'sha is required to update a file' }); return true; }
        if (givenSha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match' }); return true; }
      }
      const newTree = commitTree(repo, baseTree, new Map([[cpath, data]]));
      const newCommit = makeCommit(repo, newTree, tip ? [tip] : [], message);
      repo.refs.set(`refs/heads/${branch}`, newCommit);
      const blobOid = hashObject('blob', data);
      sendJson(res, existing ? 200 : 201, {
        content: {
          type: 'file', encoding: 'base64', size: data.length, name: cpath.split('/').pop(),
          path: cpath, sha: blobOid, content: contentB64,
          url: `/api/v3/repos/${owner}/${repoName}/contents/${cpath}`,
          html_url: `https://github.com/${owner}/${repoName}/blob/${branch}/${cpath}`,
          download_url: null, git_url: '',
        },
        commit: { sha: newCommit, message },
      });
      return true;
    }
    if (method === 'DELETE') {
      const message = typeof b.message === 'string' ? b.message : `Delete ${cpath}`;
      const givenSha = typeof b.sha === 'string' ? b.sha : '';
      const branch = typeof b.branch === 'string' ? b.branch : repo.defaultBranch;
      const tip = repo.refs.get(`refs/heads/${branch}`);
      if (!tip) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      const baseTree = commitTreeOid(repo, tip);
      const files = new Map<string, { mode: string; oid: string }>();
      flattenTree(repo, baseTree, '', files);
      const existing = files.get(cpath);
      if (!existing) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      if (givenSha !== '' && givenSha !== existing.oid) { sendJson(res, 409, { message: 'sha does not match' }); return true; }
      const newTree = commitTree(repo, baseTree, new Map([[cpath, null]]));
      const newCommit = makeCommit(repo, newTree, [tip], message);
      repo.refs.set(`refs/heads/${branch}`, newCommit);
      sendJson(res, 200, { commit: { sha: newCommit, message } });
      return true;
    }
  }
  // labels
  if (tail === 'labels') {
    if (method === 'GET') {
      sendPage(res, [...repo.labels.values()].map((l) => labelShape(l)), q, req);
      return true;
    }
    if (method === 'POST') {
      const name = typeof b.name === 'string' ? b.name : '';
      const color = typeof b.color === 'string' ? b.color.replace(/^#/, '') : '000000';
      if (name === '') { sendJson(res, 422, { message: 'name is required' }); return true; }
      if (repo.labels.has(name)) { sendJson(res, 422, { message: 'already_exists' }); return true; }
      const label: Label = { id: objIdSeq++, name, color, description: typeof b.description === 'string' ? b.description : '' };
      repo.labels.set(name, label);
      sendJson(res, 201, labelShape(label));
      return true;
    }
  }
  // issues
  if (tail === 'issues') {
    if (method === 'GET') {
      const state = q.get('state') ?? 'open';
      const sort = q.get('sort') ?? 'created';
      const direction = q.get('direction') ?? 'desc';
      let list = [...repo.issues.values()];
      if (state !== 'all') list = list.filter((i) => i.state === state);
      list.sort((a, b2) => (direction === 'asc' ? a.seq - b2.seq : b2.seq - a.seq));
      void sort;
      sendPage(res, list.map((i) => issueShape(repo, i)), q, req);
      return true;
    }
    if (method === 'POST') {
      const title = typeof b.title === 'string' ? b.title : '';
      if (title === '') { sendJson(res, 422, { message: 'title is required' }); return true; }
      const labelNames: string[] = [];
      if (Array.isArray(b.labels)) {
        for (const l of b.labels) {
          const name = typeof l === 'string' ? l : (l as J)?.name;
          if (typeof name !== 'string') continue;
          if (!repo.labels.has(name)) { sendJson(res, 422, { message: `Label '${name}' does not exist` }); return true; }
          labelNames.push(name);
        }
      }
      const number = ++repo.seq;
      const issue: Issue = {
        id: objIdSeq++, number, title, body: typeof b.body === 'string' ? b.body : '',
        state: 'open', labels: labelNames, comments: [], seq: globalSeq++,
      };
      repo.issues.set(number, issue);
      sendJson(res, 201, issueShape(repo, issue));
      return true;
    }
  }
  {
    const im = /^issues\/(\d+)(?:\/(.*))?$/.exec(tail);
    if (im) {
      const num = parseInt(im[1], 10);
      const sub = im[2] ?? '';
      const issue = repo.issues.get(num);
      if (sub === 'comments') {
        if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return true; }
        if (method === 'GET') {
          sendPage(res, issue.comments.map((c) => commentShape(repo, c)), q, req);
          return true;
        }
        if (method === 'POST') {
          const cbody = typeof b.body === 'string' ? b.body : '';
          if (cbody === '') { sendJson(res, 422, { message: 'body is required' }); return true; }
          const comment: Comment = { id: objIdSeq++, body: cbody };
          issue.comments.push(comment);
          sendJson(res, 201, commentShape(repo, comment));
          return true;
        }
      }
      if (sub === '') {
        if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return true; }
        if (method === 'GET') { sendJson(res, 200, issueShape(repo, issue)); return true; }
        if (method === 'PATCH') {
          if (typeof b.title === 'string') issue.title = b.title;
          if (typeof b.body === 'string') issue.body = b.body;
          if (b.state === 'open' || b.state === 'closed') issue.state = b.state;
          if (Array.isArray(b.labels)) {
            const names: string[] = [];
            for (const l of b.labels) {
              const name = typeof l === 'string' ? l : (l as J)?.name;
              if (typeof name === 'string' && repo.labels.has(name)) names.push(name);
            }
            issue.labels = names;
          }
          sendJson(res, 200, issueShape(repo, issue));
          return true;
        }
      }
    }
  }
  // pulls
  if (tail === 'pulls') {
    if (method === 'GET') {
      const state = q.get('state') ?? 'open';
      let list = [...repo.pulls.values()];
      if (state !== 'all') list = list.filter((p) => p.state === state);
      list.sort((a, b2) => b2.seq - a.seq);
      sendPage(res, list.map((p) => pullShape(repo, p)), q, req);
      return true;
    }
    if (method === 'POST') {
      const title = typeof b.title === 'string' ? b.title : '';
      const head = typeof b.head === 'string' ? b.head : '';
      const base = typeof b.base === 'string' ? b.base : '';
      if (title === '' || head === '' || base === '') { sendJson(res, 422, { message: 'title, head and base are required' }); return true; }
      const headTip = repo.refs.get(`refs/heads/${head}`);
      const baseTip = repo.refs.get(`refs/heads/${base}`);
      if (!headTip || !baseTip) { sendJson(res, 422, { message: 'head or base branch does not exist' }); return true; }
      for (const p of repo.pulls.values()) {
        if (p.state === 'open' && p.headRef === head && p.baseRef === base) {
          sendJson(res, 422, { message: 'A pull request already exists for this head and base' });
          return true;
        }
      }
      const number = ++repo.seq;
      const pull: Pull = {
        id: objIdSeq++, number, title, body: typeof b.body === 'string' ? b.body : '',
        state: 'open', merged: false, mergedAt: null, mergeSha: null,
        headRef: head, baseRef: base, mergeBase: mergeBase(repo, headTip, baseTip), seq: globalSeq++,
      };
      repo.pulls.set(number, pull);
      sendJson(res, 201, pullShape(repo, pull));
      return true;
    }
  }
  {
    const pm = /^pulls\/(\d+)(?:\/(.*))?$/.exec(tail);
    if (pm) {
      const num = parseInt(pm[1], 10);
      const sub = pm[2] ?? '';
      const pull = repo.pulls.get(num);
      if (!pull) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      if (sub === '' && method === 'GET') { sendJson(res, 200, pullShape(repo, pull)); return true; }
      if (sub === 'files' && method === 'GET') {
        const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? '';
        const diff = diffTrees(repo, pull.mergeBase ? commitTreeOid(repo, pull.mergeBase) : null, headTip ? commitTreeOid(repo, headTip) : null);
        const files = diff.map((d) => ({
          filename: d.path, status: d.status, additions: d.additions, deletions: d.deletions,
          changes: d.additions + d.deletions, sha: d.newOid ?? d.oldOid ?? '',
        }));
        sendPage(res, files, q, req);
        return true;
      }
      if (sub === 'merge' && method === 'PUT') {
        if (pull.merged || pull.state !== 'open') { sendJson(res, 405, { message: 'Pull request is not open' }); return true; }
        if (prConflict(repo, pull)) { sendJson(res, 405, { message: 'Merge conflict' }); return true; }
        const r = squashMerge(repo, pull);
        if (!r.ok) { sendJson(res, 405, { message: r.reason ?? 'Merge failed' }); return true; }
        sendJson(res, 200, { sha: r.sha, merged: true, message: `Merge pull request #${pull.number} from ${pull.headRef}` });
        return true;
      }
    }
  }

  sendJson(res, 404, { message: 'Not Found' });
  return true;
}

// ---------------------------------------------------------------- GraphQL

// Minimal GraphQL executor: tokenizer + recursive-descent parser + a resolver
// table. Supports operation/variables/aliases/arguments (vars, literals,
// enums, inline objects, lists, null)/inline fragments/named fragments/
// directives (parsed, ignored). Unknown fields produce an errors entry and a
// null value at HTTP 200, per the GraphQL spec.

interface GqlValue { kind: 'var' | 'int' | 'float' | 'string' | 'bool' | 'null' | 'enum' | 'list' | 'object'; name?: string; value?: unknown; items?: GqlValue[]; fields?: Array<{ name: string; value: GqlValue }>; }
interface GqlSelection { kind: 'field' | 'spread' | 'inline'; name?: string; alias?: string; args?: Array<{ name: string; value: GqlValue }>; selections?: GqlSelection[]; typeCondition?: string; }
interface GqlOperation { kind: 'query' | 'mutation' | 'subscription'; name?: string; varDefs?: Array<{ name: string }>; selections: GqlSelection[]; }
interface GqlFragment { name: string; typeCondition: string; selections: GqlSelection[]; }
interface GqlDocument { operations: GqlOperation[]; fragments: Map<string, GqlFragment>; }

function gqlTokenize(src: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < src.length) {
    const ch = src[i];
    if (ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r' || ch === ',') { i++; continue; }
    if (ch === '#') { while (i < src.length && src[i] !== '\n') i++; continue; }
    if (ch === '.' && src.slice(i, i + 3) === '...') { tokens.push('...'); i += 3; continue; }
    if ('{}():$!=@[]'.includes(ch)) { tokens.push(ch); i++; continue; }
    if (ch === '"') {
      let j = i + 1;
      let s = '';
      while (j < src.length && src[j] !== '"') {
        if (src[j] === '\\' && j + 1 < src.length) {
          const e = src[j + 1];
          s += e === 'n' ? '\n' : e === 't' ? '\t' : e === 'r' ? '\r' : e;
          j += 2;
        } else { s += src[j]; j++; }
      }
      tokens.push(JSON.stringify(s));
      i = j + 1;
      continue;
    }
    if (/[A-Za-z_]/.test(ch)) {
      let j = i;
      while (j < src.length && /[A-Za-z0-9_]/.test(src[j])) j++;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    if (/[0-9-]/.test(ch)) {
      let j = i;
      while (j < src.length && /[0-9.eE+-]/.test(src[j])) j++;
      tokens.push(src.slice(i, j));
      i = j;
      continue;
    }
    i++;
  }
  return tokens;
}

class GqlParser {
  private pos = 0;
  private tokens: string[];
  constructor(tokens: string[]) { this.tokens = tokens; }
  private peek(): string | undefined { return this.tokens[this.pos]; }
  private next(): string { return this.tokens[this.pos++]; }
  private expect(t: string): void {
    const got = this.next();
    if (got !== t) throw new Error(`expected ${t}, got ${got}`);
  }
  private isName(t: string | undefined): boolean {
    return t !== undefined && /^[A-Za-z_][A-Za-z0-9_]*$/.test(t) && !['query', 'mutation', 'subscription', 'fragment', 'on', 'true', 'false', 'null'].includes(t);
  }
  parseDocument(): GqlDocument {
    const doc: GqlDocument = { operations: [], fragments: new Map() };
    while (this.pos < this.tokens.length) {
      const t = this.peek();
      if (t === 'fragment') {
        this.next();
        const name = this.next();
        this.expect('on');
        const typeCondition = this.next();
        const selections = this.parseSelectionSet();
        doc.fragments.set(name, { name, typeCondition, selections });
      } else if (t === 'query' || t === 'mutation' || t === 'subscription') {
        const kind = this.next() as GqlOperation['kind'];
        let name: string | undefined;
        if (this.isName(this.peek())) name = this.next();
        const varDefs = this.parseVarDefs();
        this.skipDirectives();
        const selections = this.parseSelectionSet();
        doc.operations.push({ kind, name, varDefs, selections });
      } else if (t === '{') {
        const selections = this.parseSelectionSet();
        doc.operations.push({ kind: 'query', selections });
      } else {
        throw new Error(`unexpected token ${t}`);
      }
    }
    return doc;
  }
  private parseVarDefs(): Array<{ name: string }> | undefined {
    if (this.peek() !== '(') return undefined;
    this.next();
    const defs: Array<{ name: string }> = [];
    while (this.peek() !== ')') {
      this.expect('$');
      const name = this.next();
      this.expect(':');
      this.parseType();
      if (this.peek() === '=') { this.next(); this.parseValue(); }
      defs.push({ name });
    }
    this.expect(')');
    return defs;
  }
  private parseType(): void {
    if (this.peek() === '[') {
      this.next();
      this.parseType();
      this.expect(']');
    } else {
      this.next();
    }
    if (this.peek() === '!') this.next();
  }
  private skipDirectives(): void {
    while (this.peek() === '@') {
      this.next();
      this.next();
      if (this.peek() === '(') this.parseArgs();
    }
  }
  private parseArgs(): Array<{ name: string; value: GqlValue }> {
    this.expect('(');
    const args: Array<{ name: string; value: GqlValue }> = [];
    while (this.peek() !== ')') {
      const name = this.next();
      this.expect(':');
      args.push({ name, value: this.parseValue() });
    }
    this.expect(')');
    return args;
  }
  private parseSelectionSet(): GqlSelection[] {
    this.expect('{');
    const sels: GqlSelection[] = [];
    while (this.peek() !== '}') {
      sels.push(this.parseSelection());
    }
    this.expect('}');
    return sels;
  }
  private parseSelection(): GqlSelection {
    if (this.peek() === '...') {
      this.next();
      if (this.peek() === 'on') {
        this.next();
        const typeCondition = this.next();
        this.skipDirectives();
        const selections = this.parseSelectionSet();
        return { kind: 'inline', typeCondition, selections };
      }
      if (this.peek() === '{') {
        const selections = this.parseSelectionSet();
        return { kind: 'inline', selections };
      }
      const name = this.next();
      this.skipDirectives();
      return { kind: 'spread', name };
    }
    let name = this.next();
    let alias: string | undefined;
    if (this.peek() === ':') {
      this.next();
      alias = name;
      name = this.next();
    }
    let args: Array<{ name: string; value: GqlValue }> | undefined;
    if (this.peek() === '(') args = this.parseArgs();
    this.skipDirectives();
    let selections: GqlSelection[] | undefined;
    if (this.peek() === '{') selections = this.parseSelectionSet();
    return { kind: 'field', name, alias, args, selections };
  }
  private parseValue(): GqlValue {
    const t = this.peek() as string;
    if (t === '$') { this.next(); return { kind: 'var', name: this.next() }; }
    if (t === '[') {
      this.next();
      const items: GqlValue[] = [];
      while (this.peek() !== ']') items.push(this.parseValue());
      this.expect(']');
      return { kind: 'list', items };
    }
    if (t === '{') {
      this.next();
      const fields: Array<{ name: string; value: GqlValue }> = [];
      while (this.peek() !== '}') {
        const name = this.next();
        this.expect(':');
        fields.push({ name, value: this.parseValue() });
      }
      this.expect('}');
      return { kind: 'object', fields };
    }
    if (t.startsWith('"')) { this.next(); return { kind: 'string', value: JSON.parse(t) }; }
    if (t === 'true' || t === 'false') { this.next(); return { kind: 'bool', value: t === 'true' }; }
    if (t === 'null') { this.next(); return { kind: 'null', value: null }; }
    if (/^-?\d+$/.test(t)) { this.next(); return { kind: 'int', value: parseInt(t, 10) }; }
    if (/^-?[\d.]+$/.test(t)) { this.next(); return { kind: 'float', value: parseFloat(t) }; }
    this.next();
    return { kind: 'enum', value: t };
  }
}

function evalGqlValue(v: GqlValue, vars: Record<string, unknown>): unknown {
  switch (v.kind) {
    case 'var': return vars[v.name ?? ''];
    case 'list': return (v.items ?? []).map((it) => evalGqlValue(it, vars));
    case 'object': {
      const o: Record<string, unknown> = {};
      for (const f of v.fields ?? []) o[f.name] = evalGqlValue(f.value, vars);
      return o;
    }
    default: return v.value;
  }
}
function evalArgs(sel: GqlSelection, vars: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const a of sel.args ?? []) out[a.name] = evalGqlValue(a.value, vars);
  return out;
}

// -- GraphQL object model: values are plain objects carrying __typename plus
// lazily-resolved fields via the RESOLVERS table below.
type GqlObj = { __typename: string; [key: string]: unknown };
type Resolver = (parent: GqlObj, args: Record<string, unknown>, ctx: GqlCtx) => unknown;
interface GqlCtx { errors: Array<{ message: string }>; }
const RESOLVERS: Record<string, Record<string, Resolver>> = {};
function defResolver(type: string, field: string, fn: Resolver): void {
  if (!RESOLVERS[type]) RESOLVERS[type] = {};
  RESOLVERS[type][field] = fn;
}

const SCHEMA_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', '__type'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  User: ['id', 'login', 'name', 'email'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests'],
  Issue: ['id', 'number', 'title', 'state', 'body', 'labels', 'comments', 'author', 'createdAt'],
  PullRequest: ['id', 'number', 'title', 'body', 'state', 'headRefName', 'baseRefName', 'mergeable', 'merged', 'files', 'author'],
  IssueConnection: ['nodes', 'pageInfo', 'totalCount'],
  PullRequestConnection: ['nodes', 'pageInfo', 'totalCount'],
  PageInfo: ['hasNextPage', 'endCursor'],
  Label: ['id', 'name', 'color'],
  IssueComment: ['id', 'body', 'author'],
  IssueCommentEdge: ['node'],
  PullRequestFile: ['path', 'filename', 'additions', 'deletions', 'changes', 'status'],
  Ref: ['name'],
  __Type: ['name', 'kind', 'fields', 'enumValues'],
  __Field: ['name'],
  __EnumValue: ['name'],
};
const SCHEMA_ENUMS: Record<string, string[]> = {
  SearchType: ['ISSUE', 'PULL_REQUEST', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
};

function repoGql(repo: Repo): GqlObj {
  return { __typename: 'Repository', __repo: repo };
}
function issueGql(repo: Repo, issue: Issue): GqlObj {
  return { __typename: 'Issue', __repo: repo, __issue: issue };
}
function pullGql(repo: Repo, pull: Pull): GqlObj {
  return { __typename: 'PullRequest', __repo: repo, __pull: pull };
}
function commentGql(repo: Repo, issue: Issue, c: Comment): GqlObj {
  return { __typename: 'IssueComment', __repo: repo, __issue: issue, __comment: c };
}
function cursorFor(n: number): string {
  return Buffer.from(`cursor:${n}`, 'utf8').toString('base64');
}
function cursorNum(after: unknown): number {
  if (typeof after !== 'string') return 0;
  try {
    const text = Buffer.from(after, 'base64').toString('utf8');
    const m = /^cursor:(\d+)$/.exec(text);
    return m ? parseInt(m[1], 10) : 0;
  } catch {
    return 0;
  }
}
function connection<T>(nodes: T[], first: unknown, after: unknown, key: (t: T) => number, typename: string): GqlObj {
  const afterNum = cursorNum(after);
  const filtered = nodes.filter((n) => key(n) > afterNum);
  const n = typeof first === 'number' && first >= 0 ? first : filtered.length;
  const page = filtered.slice(0, n);
  const last = page.length > 0 ? key(page[page.length - 1]) : null;
  return {
    __typename: typename,
    __nodes: page,
    __pageInfo: {
      __typename: 'PageInfo',
      hasNextPage: filtered.length > page.length,
      endCursor: last === null ? null : cursorFor(last),
    },
    __totalCount: nodes.length,
  };
}

function registerGqlResolvers(): void {
  defResolver('Query', 'viewer', () => ({ __typename: 'User' }));
  defResolver('Query', 'repository', (_p, args) => {
    const repo = getRepo(String(args.owner ?? ''), String(args.name ?? ''));
    return repo ? repoGql(repo) : null;
  });
  defResolver('Query', 'node', (_p, args) => {
    const dec = decodeGlobalId(String(args.id ?? ''));
    if (!dec) return null;
    if (dec.kind === 'Repository') {
      const repo = reposById.get(Number(dec.parts[0]));
      return repo ? repoGql(repo) : null;
    }
    if (dec.kind === 'Issue') {
      const repo = reposById.get(Number(dec.parts[0]));
      const issue = repo?.issues.get(Number(dec.parts[1]));
      return repo && issue ? issueGql(repo, issue) : null;
    }
    if (dec.kind === 'PullRequest') {
      const repo = reposById.get(Number(dec.parts[0]));
      const pull = repo?.pulls.get(Number(dec.parts[1]));
      return repo && pull ? pullGql(repo, pull) : null;
    }
    return null;
  });
  defResolver('Query', '__type', (_p, args) => {
    const name = String(args.name ?? '');
    if (SCHEMA_FIELDS[name]) {
      return {
        __typename: '__Type', name, kind: 'OBJECT',
        __fields: SCHEMA_FIELDS[name].map((f) => ({ __typename: '__Field', name: f })),
        __enumValues: null,
      };
    }
    if (SCHEMA_ENUMS[name]) {
      return {
        __typename: '__Type', name, kind: 'ENUM', __fields: null,
        __enumValues: SCHEMA_ENUMS[name].map((f) => ({ __typename: '__EnumValue', name: f })),
      };
    }
    return null;
  });
  defResolver('User', 'id', () => globalId('User', [VIEWER.id]));
  defResolver('User', 'login', () => VIEWER_LOGIN);
  defResolver('User', 'name', () => VIEWER.name);
  defResolver('User', 'email', () => VIEWER.email);
  defResolver('Repository', 'id', (p) => globalId('Repository', [(p.__repo as Repo).id]));
  defResolver('Repository', 'databaseId', (p) => (p.__repo as Repo).id);
  defResolver('Repository', 'name', (p) => (p.__repo as Repo).name);
  defResolver('Repository', 'nameWithOwner', (p) => `${(p.__repo as Repo).owner}/${(p.__repo as Repo).name}`);
  defResolver('Repository', 'owner', () => ({ __typename: 'User' }));
  defResolver('Repository', 'defaultBranchRef', (p) => ({ __typename: 'Ref', name: (p.__repo as Repo).defaultBranch }));
  defResolver('Repository', 'viewerPermission', () => 'ADMIN');
  defResolver('Repository', 'hasIssuesEnabled', () => true);
  defResolver('Repository', 'issue', (p, args) => {
    const repo = p.__repo as Repo;
    const issue = repo.issues.get(Number(args.number));
    return issue ? issueGql(repo, issue) : null;
  });
  defResolver('Repository', 'issues', (p, args) => {
    const repo = p.__repo as Repo;
    let list = [...repo.issues.values()];
    const states = Array.isArray(args.states) ? (args.states as string[]) : null;
    if (states) list = list.filter((i) => states.includes(i.state === 'open' ? 'OPEN' : 'CLOSED'));
    const orderBy = args.orderBy as { field?: string; direction?: string } | undefined;
    const desc = orderBy?.direction === 'DESC';
    list.sort((a, b) => (desc ? b.number - a.number : a.number - b.number));
    const nodes = list.map((i) => issueGql(repo, i));
    return connection(nodes, args.first, args.after, (g) => (g.__issue as Issue).number, 'IssueConnection');
  });
  defResolver('Repository', 'pullRequest', (p, args) => {
    const repo = p.__repo as Repo;
    const pull = repo.pulls.get(Number(args.number));
    return pull ? pullGql(repo, pull) : null;
  });
  defResolver('Repository', 'pullRequests', (p, args) => {
    const repo = p.__repo as Repo;
    let list = [...repo.pulls.values()];
    const states = Array.isArray(args.states) ? (args.states as string[]) : null;
    if (states) {
      list = list.filter((pr) => {
        const s = pr.merged ? 'MERGED' : pr.state === 'open' ? 'OPEN' : 'CLOSED';
        return states.includes(s);
      });
    } else {
      list = list.filter((pr) => pr.state === 'open');
    }
    const orderBy = args.orderBy as { field?: string; direction?: string } | undefined;
    const desc = orderBy?.direction === 'DESC';
    list.sort((a, b) => (desc ? b.number - a.number : a.number - b.number));
    const nodes = list.map((pr) => pullGql(repo, pr));
    return connection(nodes, args.first, args.after, (g) => (g.__pull as Pull).number, 'PullRequestConnection');
  });
  defResolver('Issue', 'id', (p) => globalId('Issue', [(p.__repo as Repo).id, (p.__issue as Issue).number]));
  defResolver('Issue', 'number', (p) => (p.__issue as Issue).number);
  defResolver('Issue', 'title', (p) => (p.__issue as Issue).title);
  defResolver('Issue', 'body', (p) => (p.__issue as Issue).body);
  defResolver('Issue', 'state', (p) => ((p.__issue as Issue).state === 'open' ? 'OPEN' : 'CLOSED'));
  defResolver('Issue', 'author', () => ({ __typename: 'User' }));
  defResolver('Issue', 'createdAt', () => FIXED_ISO);
  defResolver('Issue', 'labels', (p) => {
    const repo = p.__repo as Repo;
    const issue = p.__issue as Issue;
    const nodes = issue.labels.map((name) => {
      const l = repo.labels.get(name);
      return { __typename: 'Label', name, color: l?.color ?? '000000', __labelId: l?.id ?? 0 };
    });
    return { __typename: 'LabelConnection', __nodes: nodes, __pageInfo: { __typename: 'PageInfo', hasNextPage: false, endCursor: null }, __totalCount: nodes.length };
  });
  defResolver('Issue', 'comments', (p, args) => {
    const issue = p.__issue as Issue;
    const repo = p.__repo as Repo;
    const nodes = issue.comments.map((c) => commentGql(repo, issue, c));
    return connection(nodes, args.first, args.after, (c) => (c.__comment as Comment).id, 'IssueCommentConnection');
  });
  defResolver('Label', 'id', (p) => globalId('Label', [(p as unknown as { __labelId: number }).__labelId]));
  defResolver('Label', 'name', (p) => p.name);
  defResolver('Label', 'color', (p) => p.color);
  defResolver('LabelConnection', 'nodes', (p) => p.__nodes);
  defResolver('LabelConnection', 'totalCount', (p) => p.__totalCount);
  defResolver('LabelConnection', 'pageInfo', (p) => p.__pageInfo);
  defResolver('IssueCommentConnection', 'nodes', (p) => p.__nodes);
  defResolver('IssueCommentConnection', 'totalCount', (p) => p.__totalCount);
  defResolver('IssueCommentConnection', 'pageInfo', (p) => p.__pageInfo);
  defResolver('IssueComment', 'id', (p) => globalId('IssueComment', [(p.__repo as Repo).id, (p.__issue as Issue).number, (p.__comment as Comment).id]));
  defResolver('IssueComment', 'body', (p) => (p.__comment as Comment).body);
  defResolver('IssueComment', 'author', () => ({ __typename: 'User' }));
  defResolver('IssueConnection', 'nodes', (p) => p.__nodes);
  defResolver('IssueConnection', 'totalCount', (p) => p.__totalCount);
  defResolver('IssueConnection', 'pageInfo', (p) => p.__pageInfo);
  defResolver('PullRequestConnection', 'nodes', (p) => p.__nodes);
  defResolver('PullRequestConnection', 'totalCount', (p) => p.__totalCount);
  defResolver('PullRequestConnection', 'pageInfo', (p) => p.__pageInfo);
  defResolver('PageInfo', 'hasNextPage', (p) => p.hasNextPage);
  defResolver('PageInfo', 'endCursor', (p) => p.endCursor);
  defResolver('PullRequest', 'id', (p) => globalId('PullRequest', [(p.__repo as Repo).id, (p.__pull as Pull).number]));
  defResolver('PullRequest', 'number', (p) => (p.__pull as Pull).number);
  defResolver('PullRequest', 'title', (p) => (p.__pull as Pull).title);
  defResolver('PullRequest', 'body', (p) => (p.__pull as Pull).body);
  defResolver('PullRequest', 'state', (p) => {
    const pr = p.__pull as Pull;
    return pr.merged ? 'MERGED' : pr.state === 'open' ? 'OPEN' : 'CLOSED';
  });
  defResolver('PullRequest', 'headRefName', (p) => (p.__pull as Pull).headRef);
  defResolver('PullRequest', 'baseRefName', (p) => (p.__pull as Pull).baseRef);
  defResolver('PullRequest', 'mergeable', (p) => (prConflict(p.__repo as Repo, p.__pull as Pull) ? 'CONFLICTING' : 'MERGEABLE'));
  defResolver('PullRequest', 'merged', (p) => (p.__pull as Pull).merged);
  defResolver('PullRequest', 'author', () => ({ __typename: 'User' }));
  defResolver('PullRequest', 'files', (p, args) => {
    const repo = p.__repo as Repo;
    const pull = p.__pull as Pull;
    const headTip = repo.refs.get(`refs/heads/${pull.headRef}`) ?? '';
    const diff = diffTrees(repo, pull.mergeBase ? commitTreeOid(repo, pull.mergeBase) : null, headTip ? commitTreeOid(repo, headTip) : null);
    const nodes = diff.map((d, i) => ({
      __typename: 'PullRequestFile', __idx: i + 1, path: d.path, filename: d.path,
      additions: d.additions, deletions: d.deletions, changes: d.additions + d.deletions, status: d.status,
    }));
    return connection(nodes, args.first, args.after, (n) => (n as unknown as { __idx: number }).__idx, 'PullRequestFileConnection');
  });
  defResolver('PullRequestFileConnection', 'nodes', (p) => p.__nodes);
  defResolver('PullRequestFileConnection', 'totalCount', (p) => p.__totalCount);
  defResolver('PullRequestFileConnection', 'pageInfo', (p) => p.__pageInfo);
  defResolver('PullRequestFile', 'path', (p) => p.path);
  defResolver('PullRequestFile', 'filename', (p) => p.filename);
  defResolver('PullRequestFile', 'additions', (p) => p.additions);
  defResolver('PullRequestFile', 'deletions', (p) => p.deletions);
  defResolver('PullRequestFile', 'changes', (p) => p.changes);
  defResolver('PullRequestFile', 'status', (p) => p.status);
  defResolver('Ref', 'name', (p) => p.name);
  defResolver('__Type', 'name', (p) => p.name);
  defResolver('__Type', 'kind', (p) => p.kind);
  defResolver('__Type', 'fields', (p) => p.__fields);
  defResolver('__Type', 'enumValues', (p) => p.__enumValues);
  defResolver('__Field', 'name', (p) => p.name);
  defResolver('__EnumValue', 'name', (p) => p.name);
  defResolver('IssueCommentEdge', 'node', (p) => p.__node);
  // mutations
  defResolver('Mutation', 'createIssue', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = dec?.kind === 'Repository' ? reposById.get(Number(dec.parts[0])) : undefined;
    if (!repo) { ctx.errors.push({ message: 'Repository not found' }); return { __typename: 'CreateIssuePayload', issue: null }; }
    const title = String(input.title ?? '');
    const number = ++repo.seq;
    const issue: Issue = { id: objIdSeq++, number, title, body: typeof input.body === 'string' ? input.body : '', state: 'open', labels: [], comments: [], seq: globalSeq++ };
    repo.issues.set(number, issue);
    return { __typename: 'CreateIssuePayload', issue: issueGql(repo, issue) };
  });
  defResolver('Mutation', 'closeIssue', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.issueId ?? ''));
    const repo = dec?.kind === 'Issue' ? reposById.get(Number(dec.parts[0])) : undefined;
    const issue = repo?.issues.get(Number(dec?.parts[1] ?? -1));
    if (!repo || !issue) { ctx.errors.push({ message: 'Issue not found' }); return { __typename: 'CloseIssuePayload', issue: null }; }
    issue.state = 'closed';
    return { __typename: 'CloseIssuePayload', issue: issueGql(repo, issue) };
  });
  defResolver('Mutation', 'createPullRequest', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.repositoryId ?? ''));
    const repo = dec?.kind === 'Repository' ? reposById.get(Number(dec.parts[0])) : undefined;
    if (!repo) { ctx.errors.push({ message: 'Repository not found' }); return { __typename: 'CreatePullRequestPayload', pullRequest: null }; }
    const head = String(input.headRefName ?? '');
    const base = String(input.baseRefName ?? '');
    const headTip = repo.refs.get(`refs/heads/${head}`);
    const baseTip = repo.refs.get(`refs/heads/${base}`);
    if (!headTip || !baseTip) { ctx.errors.push({ message: 'head or base branch does not exist' }); return { __typename: 'CreatePullRequestPayload', pullRequest: null }; }
    for (const pr of repo.pulls.values()) {
      if (pr.state === 'open' && pr.headRef === head && pr.baseRef === base) {
        ctx.errors.push({ message: 'A pull request already exists for this head and base' });
        return { __typename: 'CreatePullRequestPayload', pullRequest: null };
      }
    }
    const number = ++repo.seq;
    const pull: Pull = {
      id: objIdSeq++, number, title: String(input.title ?? ''), body: typeof input.body === 'string' ? input.body : '',
      state: 'open', merged: false, mergedAt: null, mergeSha: null,
      headRef: head, baseRef: base, mergeBase: mergeBase(repo, headTip, baseTip), seq: globalSeq++,
    };
    repo.pulls.set(number, pull);
    return { __typename: 'CreatePullRequestPayload', pullRequest: pullGql(repo, pull) };
  });
  defResolver('Mutation', 'mergePullRequest', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.pullRequestId ?? ''));
    const repo = dec?.kind === 'PullRequest' ? reposById.get(Number(dec.parts[0])) : undefined;
    const pull = repo?.pulls.get(Number(dec?.parts[1] ?? -1));
    if (!repo || !pull) { ctx.errors.push({ message: 'Pull request not found' }); return { __typename: 'MergePullRequestPayload', pullRequest: null }; }
    if (pull.merged || pull.state !== 'open') { ctx.errors.push({ message: 'Pull request is not open' }); return { __typename: 'MergePullRequestPayload', pullRequest: null }; }
    if (prConflict(repo, pull)) { ctx.errors.push({ message: 'Merge conflict' }); return { __typename: 'MergePullRequestPayload', pullRequest: null }; }
    const r = squashMerge(repo, pull);
    if (!r.ok) { ctx.errors.push({ message: r.reason ?? 'Merge failed' }); return { __typename: 'MergePullRequestPayload', pullRequest: null }; }
    return { __typename: 'MergePullRequestPayload', pullRequest: pullGql(repo, pull) };
  });
  defResolver('Mutation', 'addComment', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.subjectId ?? ''));
    const repo = dec?.kind === 'Issue' ? reposById.get(Number(dec.parts[0])) : undefined;
    const issue = repo?.issues.get(Number(dec?.parts[1] ?? -1));
    if (!repo || !issue) { ctx.errors.push({ message: 'Issue not found' }); return { __typename: 'AddCommentPayload', commentEdge: null }; }
    const comment: Comment = { id: objIdSeq++, body: String(input.body ?? '') };
    issue.comments.push(comment);
    return { __typename: 'AddCommentPayload', commentEdge: { __typename: 'IssueCommentEdge', __node: commentGql(repo, issue, comment) } };
  });
  // payload pass-through fields
  defResolver('CreateIssuePayload', 'issue', (p) => p.issue);
  defResolver('CloseIssuePayload', 'issue', (p) => p.issue);
  defResolver('CreatePullRequestPayload', 'pullRequest', (p) => p.pullRequest);
  defResolver('MergePullRequestPayload', 'pullRequest', (p) => p.pullRequest);
  defResolver('AddCommentPayload', 'commentEdge', (p) => p.commentEdge);
}
registerGqlResolvers();

function executeSelectionSet(sels: GqlSelection[], parent: GqlObj, vars: Record<string, unknown>, doc: GqlDocument, ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  for (const sel of sels) {
    if (sel.kind === 'spread') {
      const frag = doc.fragments.get(sel.name ?? '');
      if (frag) Object.assign(out, executeSelectionSet(frag.selections, parent, vars, doc, ctx));
      continue;
    }
    if (sel.kind === 'inline') {
      if (!sel.typeCondition || sel.typeCondition === parent.__typename) {
        Object.assign(out, executeSelectionSet(sel.selections ?? [], parent, vars, doc, ctx));
      }
      continue;
    }
    const fieldName = sel.name as string;
    const outName = sel.alias ?? fieldName;
    if (fieldName === '__typename') { out[outName] = parent.__typename; continue; }
    const typeResolvers = RESOLVERS[parent.__typename];
    const fn = typeResolvers?.[fieldName];
    if (!fn) {
      ctx.errors.push({ message: `Cannot query field "${fieldName}" on type "${parent.__typename}".` });
      out[outName] = null;
      continue;
    }
    const args = evalArgs(sel, vars);
    let value: unknown;
    try {
      value = fn(parent, args, ctx);
    } catch (err) {
      ctx.errors.push({ message: err instanceof Error ? err.message : 'resolver error' });
      out[outName] = null;
      continue;
    }
    if (value === null || value === undefined) { out[outName] = null; continue; }
    if (sel.selections && sel.selections.length > 0) {
      if (Array.isArray(value)) {
        out[outName] = value.map((v) => (v !== null && typeof v === 'object' ? executeSelectionSet(sel.selections as GqlSelection[], v as GqlObj, vars, doc, ctx) : v));
      } else if (typeof value === 'object') {
        out[outName] = executeSelectionSet(sel.selections, value as GqlObj, vars, doc, ctx);
      } else {
        out[outName] = null;
      }
    } else {
      out[outName] = value;
    }
  }
  return out;
}

function executeGqlOperation(doc: GqlDocument, op: GqlOperation, vars: Record<string, unknown>): { data: Record<string, unknown>; errors?: Array<{ message: string }> } {
  const ctx: GqlCtx = { errors: [] };
  const rootType = op.kind === 'mutation' ? 'Mutation' : 'Query';
  const root: GqlObj = { __typename: rootType };
  const data = executeSelectionSet(op.selections, root, vars, doc, ctx);
  return ctx.errors.length > 0 ? { data, errors: ctx.errors } : { data };
}

async function handleGraphQL(req: IncomingMessage, res: ServerResponse, path: string): Promise<boolean> {
  if (path !== '/api/graphql' && path !== '/api/v3/graphql') return false;
  if (req.method !== 'POST') { sendJson(res, 404, { message: 'Not Found' }); return true; }
  const auth = checkAuth(req);
  if (auth !== 'ok') { authFail(res, auth); return true; }
  const raw = await readBody(req);
  const parsed = parseJsonBody(raw);
  if (!parsed.ok) { sendJson(res, 400, { message: 'Invalid JSON' }); return true; }
  const runOne = (item: unknown): { data: Record<string, unknown>; errors?: Array<{ message: string }> } => {
    const q = item as { query?: unknown; variables?: unknown; operationName?: unknown };
    if (typeof q.query !== 'string') return { data: {}, errors: [{ message: 'query is required' }] };
    let doc: GqlDocument;
    try {
      doc = new GqlParser(gqlTokenize(q.query)).parseDocument();
    } catch (err) {
      return { data: {}, errors: [{ message: err instanceof Error ? err.message : 'syntax error' }] };
    }
    const vars = (q.variables ?? {}) as Record<string, unknown>;
    const op = typeof q.operationName === 'string'
      ? doc.operations.find((o) => o.name === q.operationName) ?? doc.operations[0]
      : doc.operations[0];
    if (!op) return { data: {}, errors: [{ message: 'no operation' }] };
    return executeGqlOperation(doc, op, vars);
  };
  if (Array.isArray(parsed.value)) {
    sendJson(res, 200, parsed.value.map((item) => runOne(item)));
    return true;
  }
  sendJson(res, 200, runOne(parsed.value));
  return true;
}

// ---------------------------------------------------------------- MCP

const MCP_SERVER_NAME = 'forge';
const MCP_SERVER_VERSION = '1.0.0';
const MCP_TOOLS: Array<{ name: string; description: string; inputSchema: { type: string; properties: Record<string, unknown>; required: string[] } }> = [
  {
    name: 'create_repo',
    description: 'Create a new repository owned by the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string', description: 'Repository description' },
        private: { type: 'boolean', description: 'Whether the repository is private' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Issue title' },
        body: { type: 'string', description: 'Issue body' },
        labels: { type: 'array', items: { type: 'string' }, description: 'Label names' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        state: { type: 'string', description: 'Issue state: open, closed or all' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        title: { type: 'string', description: 'Pull request title' },
        head: { type: 'string', description: 'Head branch name' },
        base: { type: 'string', description: 'Base branch name' },
        body: { type: 'string', description: 'Pull request body' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string', description: 'Repository owner login' },
        repo: { type: 'string', description: 'Repository name' },
        pull_number: { type: 'integer', description: 'Pull request number' },
        full_name: { type: 'string', description: 'Full repository name owner/repo' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
];

function mcpPick(args: Record<string, unknown>, names: string[]): unknown {
  for (const n of names) {
    const v = args[n];
    if (v !== undefined && v !== null && v !== '') return v;
  }
  return undefined;
}
function mcpRepoFromArgs(args: Record<string, unknown>): { owner: string; name: string } {
  const full = mcpPick(args, ['full_name', 'fullName']);
  if (typeof full === 'string' && full.includes('/')) {
    const [o, r] = full.split('/');
    return { owner: o, name: r };
  }
  const owner = String(mcpPick(args, ['owner', 'owner_login', 'org', 'login']) ?? '');
  const name = String(mcpPick(args, ['repo', 'repository', 'repo_name', 'name']) ?? '');
  return { owner, name };
}
function mcpToolResult(obj: unknown): { content: Array<{ type: string; text: string }>; structuredContent: unknown } {
  return { content: [{ type: 'text', text: JSON.stringify(obj) }], structuredContent: obj };
}
function mcpToolError(message: string): { content: Array<{ type: string; text: string }>; isError: boolean } {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function mcpCallTool(name: string, args: Record<string, unknown>): { content: Array<{ type: string; text: string }>; structuredContent?: unknown; isError?: boolean } {
  const need = (value: unknown, label: string): string | null => {
    if (value === undefined || value === null || value === '') return label;
    return null;
  };
  if (name === 'create_repo') {
    const repoName = String(mcpPick(args, ['name', 'repo', 'repository_name']) ?? '');
    const missing = need(repoName, 'name');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    if (getRepo(VIEWER_LOGIN, repoName)) return mcpToolError('name already exists on this account');
    const repo = createRepoRecord(repoName, mcpPick(args, ['private']) === true, typeof mcpPick(args, ['description']) === 'string' ? String(mcpPick(args, ['description'])) : '');
    return mcpToolResult(repoShape(repo));
  }
  if (name === 'get_repo') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const missing = need(owner, 'owner') ?? need(repoName, 'repo');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    return mcpToolResult(repoShape(repo));
  }
  if (name === 'create_issue') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const title = String(mcpPick(args, ['title', 'issue_title']) ?? '');
    const missing = need(owner, 'owner') ?? need(repoName, 'repo') ?? need(title, 'title');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    const labelNames: string[] = [];
    const labelsArg = mcpPick(args, ['labels']);
    if (Array.isArray(labelsArg)) {
      for (const l of labelsArg) {
        const n = typeof l === 'string' ? l : (l as J)?.name;
        if (typeof n !== 'string') continue;
        if (!repo.labels.has(n)) return mcpToolError(`Label '${n}' does not exist`);
        labelNames.push(n);
      }
    }
    const number = ++repo.seq;
    const issue: Issue = {
      id: objIdSeq++, number, title,
      body: typeof mcpPick(args, ['body', 'description', 'content']) === 'string' ? String(mcpPick(args, ['body', 'description', 'content'])) : '',
      state: 'open', labels: labelNames, comments: [], seq: globalSeq++,
    };
    repo.issues.set(number, issue);
    return mcpToolResult(issueShape(repo, issue));
  }
  if (name === 'list_issues') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const missing = need(owner, 'owner') ?? need(repoName, 'repo');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    const state = String(mcpPick(args, ['state']) ?? 'open');
    let list = [...repo.issues.values()];
    if (state !== 'all') list = list.filter((i) => i.state === state);
    list.sort((a, b) => b.seq - a.seq);
    const issues = list.map((i) => issueShape(repo, i));
    return mcpToolResult({ issues });
  }
  if (name === 'create_pull_request') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const title = String(mcpPick(args, ['title', 'pr_title']) ?? '');
    const head = String(mcpPick(args, ['head', 'head_ref', 'head_branch', 'source']) ?? '');
    const base = String(mcpPick(args, ['base', 'base_ref', 'target']) ?? '');
    const missing = need(owner, 'owner') ?? need(repoName, 'repo') ?? need(title, 'title') ?? need(head, 'head') ?? need(base, 'base');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    const headTip = repo.refs.get(`refs/heads/${head}`);
    const baseTip = repo.refs.get(`refs/heads/${base}`);
    if (!headTip || !baseTip) return mcpToolError('head or base branch does not exist');
    for (const p of repo.pulls.values()) {
      if (p.state === 'open' && p.headRef === head && p.baseRef === base) return mcpToolError('A pull request already exists for this head and base');
    }
    const number = ++repo.seq;
    const pull: Pull = {
      id: objIdSeq++, number, title,
      body: typeof mcpPick(args, ['body', 'description', 'content']) === 'string' ? String(mcpPick(args, ['body', 'description', 'content'])) : '',
      state: 'open', merged: false, mergedAt: null, mergeSha: null,
      headRef: head, baseRef: base, mergeBase: mergeBase(repo, headTip, baseTip), seq: globalSeq++,
    };
    repo.pulls.set(number, pull);
    return mcpToolResult(pullShape(repo, pull));
  }
  if (name === 'merge_pull_request') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const numRaw = mcpPick(args, ['pull_number', 'number', 'pr_number']);
    const missing = need(owner, 'owner') ?? need(repoName, 'repo') ?? need(numRaw, 'pull_number');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    const pull = repo.pulls.get(Number(numRaw));
    if (!pull) return mcpToolError('Not Found');
    if (pull.merged || pull.state !== 'open') return mcpToolError('Pull request is not open');
    if (prConflict(repo, pull)) return mcpToolError('Merge conflict');
    const r = squashMerge(repo, pull);
    if (!r.ok) return mcpToolError(r.reason ?? 'Merge failed');
    return mcpToolResult({ sha: r.sha, merged: true, message: `Merge pull request #${pull.number} from ${pull.headRef}` });
  }
  return mcpToolError(`unknown tool: ${name}`);
}

async function handleMcp(req: IncomingMessage, res: ServerResponse, path: string): Promise<boolean> {
  if (path !== '/mcp') return false;
  if (req.method === 'DELETE') {
    sendJson(res, 200, {});
    return true;
  }
  if (req.method !== 'POST') { sendJson(res, 404, { message: 'Not Found' }); return true; }
  const auth = checkAuth(req);
  if (auth !== 'ok') { authFail(res, auth); return true; }
  const raw = await readBody(req);
  const parsed = parseJsonBody(raw);
  if (!parsed.ok) {
    sendJson(res, 400, { jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } });
    return true;
  }
  const handleOne = (item: unknown): { jsonrpc: string; id: unknown; result?: unknown; error?: { code: number; message: string } } | null => {
    const msg = item as { jsonrpc?: unknown; id?: unknown; method?: unknown; params?: unknown };
    if (typeof msg !== 'object' || msg === null || typeof msg.method !== 'string') {
      return { jsonrpc: '2.0', id: (msg as { id?: unknown })?.id ?? null, error: { code: -32600, message: 'Invalid Request' } };
    }
    const id = msg.id;
    const isNotification = id === undefined;
    const params = (msg.params ?? {}) as Record<string, unknown>;
    let result: unknown;
    if (msg.method === 'server/discover') {
      result = {
        supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18'],
        serverInfo: { name: MCP_SERVER_NAME, version: MCP_SERVER_VERSION },
        capabilities: { tools: {} },
        _meta: { 'io.modelcontextprotocol/serverInfo': { name: MCP_SERVER_NAME, version: MCP_SERVER_VERSION } },
      };
    } else if (msg.method === 'initialize') {
      result = {
        protocolVersion: typeof params.protocolVersion === 'string' ? params.protocolVersion : '2025-06-18',
        capabilities: { tools: {} },
        serverInfo: { name: MCP_SERVER_NAME, version: MCP_SERVER_VERSION },
      };
    } else if (msg.method === 'notifications/initialized') {
      return null;
    } else if (msg.method === 'ping') {
      result = {};
    } else if (msg.method === 'tools/list') {
      result = { tools: MCP_TOOLS };
    } else if (msg.method === 'tools/call') {
      const toolName = typeof params.name === 'string' ? params.name : '';
      const toolArgs = (params.arguments ?? {}) as Record<string, unknown>;
      if (!MCP_TOOLS.some((t) => t.name === toolName)) {
        return { jsonrpc: '2.0', id, error: { code: -32602, message: `unknown tool: ${toolName}` } };
      }
      const tool = MCP_TOOLS.find((t) => t.name === toolName) as { inputSchema: { required: string[] } };
      const missing = tool.inputSchema.required.filter((r) => toolArgs[r] === undefined || toolArgs[r] === null || toolArgs[r] === '');
      if (missing.length > 0) {
        return { jsonrpc: '2.0', id, error: { code: -32602, message: `missing required argument: ${missing.join(', ')}` } };
      }
      result = mcpCallTool(toolName, toolArgs);
    } else {
      return { jsonrpc: '2.0', id, error: { code: -32601, message: `Method not found: ${msg.method}` } };
    }
    if (isNotification) return null;
    return { jsonrpc: '2.0', id, result };
  };
  if (Array.isArray(parsed.value)) {
    const out = parsed.value.map((item) => handleOne(item)).filter((r) => r !== null);
    sendJson(res, 200, out);
    return true;
  }
  const out = handleOne(parsed.value);
  if (out === null) {
    res.writeHead(202, { 'content-length': 0 });
    res.end();
    return true;
  }
  sendJson(res, 200, out);
  return true;
}

// ---------------------------------------------------------------- lifecycle

const sleep = (ms: number): Promise<void> => new Promise((resolve) => setTimeout(resolve, ms));
const ENV_URL = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');

async function register(port: number): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const r = await fetch(`${ENV_URL}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(30000),
      });
      if (r.status === 200 || r.status === 409) return;
      if (r.status === 400 || r.status === 405) throw new Error(`register answered HTTP ${r.status}`);
    } catch (err) {
      if (err instanceof Error && err.message.startsWith('register answered HTTP ')) throw err;
    }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
}
async function waitForDone(): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      const r = await fetch(`${ENV_URL}/done`, { signal: AbortSignal.timeout(30000) });
      if (r.ok) {
        const body = (await r.json()) as { done?: unknown };
        if (body.done === true) return;
      }
    } catch { /* retry */ }
    await sleep(Math.min(2000, 250 * 2 ** Math.min(attempt, 8)));
  }
}

async function main(): Promise<'local' | 'done'> {
  const server = createApp();
  if (ENV_URL === '') {
    const port = Number(process.env.PORT ?? 0);
    await new Promise<void>((resolve, reject) => {
      server.once('error', reject);
      server.listen(port, () => resolve());
    });
    const a = server.address();
    const p = a !== null && typeof a !== 'string' ? a.port : port;
    process.stdout.write(`[entry] listening on port ${p} (local mode, no MAKEFUN_ENV_URL)\n`);
    return 'local';
  }
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('the server did not bind an ephemeral TCP port');
  process.stdout.write(`[entry] listening on port ${address.port}\n`);
  await register(address.port);
  process.stdout.write('[entry] registered; waiting for the env to say done\n');
  await waitForDone();
  server.close();
  process.stdout.write('[entry] done\n');
  return 'done';
}

process.on('SIGTERM', () => process.exit(0));
try {
  const mode = await main();
  if (mode === 'done') process.exit(0);
  // local mode: stay alive — the listening server keeps the event loop going.
} catch (err) {
  process.stderr.write(`[entry] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}
