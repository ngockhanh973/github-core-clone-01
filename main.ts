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
import { deflateSync, inflateSync, createInflate, constants as zlibConstants } from 'node:zlib';
import type { Inflate } from 'node:zlib';

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
const PERF_DIAG = process.env.PERF_DIAG === '1';
const perfDiag = {
  uploadPackHits: 0,
  uploadPackMisses: 0,
  uploadPackSingleflight: 0,
  packedEntryReused: 0,
  packedEntryDeflated: 0,
  inflaterMode: 'uninitialized',
};

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
interface GitObj { type: ObjType; data: Buffer; packedEntry: Buffer | null; }
const PACK_OBJ_TYPE_CODE: Record<ObjType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };

function encodePackObjHeader(typeCode: number, size: number): Buffer {
  const tmp = Buffer.allocUnsafe(10);
  let len = 0;
  let s = size;
  let first = (typeCode << 4) | (s & 0x0f);
  s >>>= 4;
  if (s > 0) first |= 0x80;
  tmp[len++] = first;
  while (s > 0) {
    let b = s & 0x7f;
    s >>>= 7;
    if (s > 0) b |= 0x80;
    tmp[len++] = b;
  }
  return tmp.subarray(0, len);
}

/** Return [varint(type, rawSize) + zlib bytes] for an object, deflating lazily once at level 1. */
function getPackedEntry(obj: GitObj): Buffer {
  if (obj.packedEntry !== null) {
    if (PERF_DIAG) perfDiag.packedEntryReused++;
    return obj.packedEntry;
  }
  if (PERF_DIAG) perfDiag.packedEntryDeflated++;
  const hdr = encodePackObjHeader(PACK_OBJ_TYPE_CODE[obj.type], obj.data.length);
  const comp = deflateSync(obj.data, { level: 1 });
  const entry = Buffer.allocUnsafe(hdr.length + comp.length);
  hdr.copy(entry, 0);
  comp.copy(entry, hdr.length);
  obj.packedEntry = entry;
  return entry;
}

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
  const deltaLen = delta.length;
  let off = 0;
  let srcSize = 0;
  let shift = 0;
  for (;;) {
    if (off >= deltaLen) throw new Error('delta truncated');
    const b = delta[off++];
    srcSize |= (b & 0x7f) << shift;
    shift += 7;
    if (!(b & 0x80)) break;
  }
  if (srcSize !== base.length) throw new Error('delta base size mismatch');
  let tgtSize = 0;
  shift = 0;
  for (;;) {
    if (off >= deltaLen) throw new Error('delta truncated');
    const b = delta[off++];
    tgtSize |= (b & 0x7f) << shift;
    shift += 7;
    if (!(b & 0x80)) break;
  }
  // Single allocation via allocUnsafe; never exposed unless written === tgtSize.
  const out = Buffer.allocUnsafe(tgtSize);
  let written = 0;
  const baseLen = base.length;
  while (off < deltaLen) {
    const op = delta[off++];
    if (op & 0x80) {
      let cpOff = 0;
      let cpSize = 0;
      if (op & 0x01) cpOff |= delta[off++];
      if (op & 0x02) cpOff |= delta[off++] << 8;
      if (op & 0x04) cpOff |= delta[off++] << 16;
      if (op & 0x08) cpOff |= (delta[off++] << 24) >>> 0;
      if (op & 0x10) cpSize |= delta[off++];
      if (op & 0x20) cpSize |= delta[off++] << 8;
      if (op & 0x40) cpSize |= delta[off++] << 16;
      if (cpSize === 0) cpSize = 0x10000;
      if (off > deltaLen || cpOff + cpSize > baseLen || written + cpSize > tgtSize) throw new Error('delta copy out of range');
      base.copy(out, written, cpOff, cpOff + cpSize);
      written += cpSize;
    } else if (op !== 0) {
      if (off + op > deltaLen || written + op > tgtSize) throw new Error('delta insert out of range');
      delta.copy(out, written, off, off + op);
      off += op;
      written += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  if (written !== tgtSize) throw new Error('delta size mismatch');
  return out;
}

interface PackEntry { oid: string; type: ObjType; data: Buffer; packedEntry?: Buffer | null; obj?: GitObj; }

const MAX_SYNC_INFLATE_SIZE = 2 * 1024 * 1024;
type SyncInflateHandle = Inflate & {
  _processChunk?: (chunk: Buffer, flushFlag: number) => Buffer;
  reset?: () => void;
};

// Adaptive Inflater: boot-time self-test checks whether a dedicated sync-only
// Inflate handle supports _processChunk + reset() safely on this Node runtime
// (exact content + exact bytesWritten across consecutive resets with trailing
// bytes). If 100% verified, uses the reusable handle fast path; otherwise falls
// back cleanly to bounded inflateSync with tightly sized chunkSize.
let reusableInflate: SyncInflateHandle | null = null;
function initAdaptiveInflater(): void {
  try {
    const inf = createInflate({ chunkSize: 16384 }) as SyncInflateHandle;
    if (typeof inf._processChunk !== 'function' || typeof inf.reset !== 'function') {
      inf.close();
      perfDiag.inflaterMode = 'bounded-inflateSync';
      return;
    }
    const samples = [
      Buffer.from('self-test-sample-one'),
      Buffer.alloc(0),
      Buffer.from('self-test-sample-two-after-reset-0123456789'),
    ];
    for (let i = 0; i < samples.length; i++) {
      const raw = samples[i];
      const comp = deflateSync(raw, { level: 6 });
      const withTrail = Buffer.concat([comp, Buffer.from('TRAILING_BYTES')]);
      const prevBw = inf.bytesWritten;
      const out = inf._processChunk(withTrail, zlibConstants.Z_SYNC_FLUSH);
      const consumed = inf.bytesWritten - prevBw;
      if (!Buffer.isBuffer(out) || !out.equals(raw) || consumed !== comp.length) {
        inf.close();
        perfDiag.inflaterMode = 'bounded-inflateSync';
        return;
      }
      inf.reset();
    }
    reusableInflate = inf;
    perfDiag.inflaterMode = 'reuse-handle';
  } catch {
    reusableInflate = null;
    perfDiag.inflaterMode = 'bounded-inflateSync';
  }
}
initAdaptiveInflater();

/**
 * Inflate one pack entry's zlib stream synchronously (for entries < 2 MiB),
 * reporting exact compressed bytes consumed via engine.bytesWritten.
 */
function inflateEntrySync(buf: Buffer, off: number, size: number): { data: Buffer; consumed: number } {
  if (size >= MAX_SYNC_INFLATE_SIZE) throw new Error('entry exceeds sync inflate threshold');
  // A zlib stream producing `size` bytes is at most `size` bytes of stored
  // blocks (5 bytes overhead per 65535-byte block) + 2 header + 4 Adler + slack.
  const bound = off + size + 5 * Math.ceil(size / 65535) + 32;
  const slice = buf.subarray(off, Math.min(bound, buf.length));
  if (reusableInflate !== null && size <= 65536) {
    try {
      const prevBw = reusableInflate.bytesWritten;
      const data = reusableInflate._processChunk!(slice, zlibConstants.Z_SYNC_FLUSH);
      const consumed = reusableInflate.bytesWritten - prevBw;
      reusableInflate.reset!();
      if (data.length === size && Number.isInteger(consumed) && consumed > 0 && off + consumed <= buf.length) {
        return { data, consumed };
      }
    } catch {
      // Disable handle reuse permanently if runtime invariant ever breaks.
      try { reusableInflate.close(); } catch { /* ignore */ }
      reusableInflate = null;
      perfDiag.inflaterMode = 'bounded-inflateSync';
    }
  }
  const chunkSize = size < 1024 ? 1024 : size > 65536 ? 65536 : size;
  const { buffer: data, engine } = inflateSync(slice, {
    info: true,
    maxOutputLength: size > 0 ? size : 1,
    chunkSize,
  });
  if (data.length !== size) throw new Error('pack entry size mismatch');
  const consumed = (engine as { bytesWritten: number }).bytesWritten;
  if (!Number.isInteger(consumed) || consumed <= 0 || off + consumed > buf.length) throw new Error('pack entry consumed length invalid');
  return { data, consumed };
}
function inflateEntryStream(buf: Buffer, off: number, size: number): Promise<{ data: Buffer; consumed: number }> {
  return new Promise((resolve, reject) => {
    const inf = createInflate();
    const chunks: Buffer[] = [];
    inf.on('data', (c: Buffer) => chunks.push(c));
    inf.on('error', reject);
    inf.on('end', () => {
      const data = Buffer.concat(chunks);
      if (data.length !== size) { reject(new Error('pack entry size mismatch')); return; }
      resolve({ data, consumed: inf.bytesWritten });
    });
    inf.write(buf.subarray(off));
    inf.end();
  });
}

// Per-pack bounded byte LRU (32 MiB cap, skipping individual objects > 1 MiB)
// used during delta resolution so each base is resolved at most once (O(K) for
// nested delta chains) and released immediately when readPack() finishes.
const DELTA_BASE_LRU_MAX_BYTES = 32 * 1024 * 1024;
const DELTA_BASE_MAX_ITEM_BYTES = 1024 * 1024;
class DeltaBaseByteLru {
  // Map insertion order is LRU order; entry.data.length tracks byte usage directly.
  private byOffset = new Map<number, PackEntry>();
  private byOid: Map<string, PackEntry> | null;
  private totalBytes = 0;

  constructor(trackByOid: boolean) {
    this.byOid = trackByOid ? new Map<string, PackEntry>() : null;
  }
  getByOffset(offset: number): PackEntry | undefined {
    const entry = this.byOffset.get(offset);
    if (entry === undefined) return undefined;
    this.byOffset.delete(offset);
    this.byOffset.set(offset, entry);
    return entry;
  }
  getByOid(oid: string): PackEntry | undefined {
    return this.byOid !== null ? this.byOid.get(oid) : undefined;
  }
  put(offset: number, entry: PackEntry): void {
    const sz = entry.data.length;
    if (sz > DELTA_BASE_MAX_ITEM_BYTES) return;
    if (this.byOffset.has(offset)) return;
    while (this.totalBytes + sz > DELTA_BASE_LRU_MAX_BYTES && this.byOffset.size > 0) {
      const oldestOff = this.byOffset.keys().next().value as number;
      const evicted = this.byOffset.get(oldestOff) as PackEntry;
      this.byOffset.delete(oldestOff);
      this.totalBytes -= evicted.data.length;
      if (this.byOid !== null) this.byOid.delete(evicted.oid);
    }
    this.totalBytes += sz;
    this.byOffset.set(offset, entry);
    if (this.byOid !== null) this.byOid.set(entry.oid, entry);
  }
  clear(): void {
    this.byOffset.clear();
    if (this.byOid !== null) this.byOid.clear();
    this.totalBytes = 0;
  }
}

interface RawPackItem {
  offset: number;
  typeCode: number;
  type: ObjType | null;
  data: Buffer;
  baseOffset: number | null;
  baseOid: string | null;
  packedEntry: Buffer | null;
}

const PACK_TYPE_MAP: Record<number, ObjType | null> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag', 6: null, 7: null };

function resolvePackRaws(
  raws: RawPackItem[],
  hasOfsDelta: boolean,
  hasRefDelta: boolean,
  existingObjects?: Map<string, GitObj>,
): PackEntry[] {
  const n = raws.length;
  const out: PackEntry[] = new Array(n);
  // Zero-delta fast path: skip all delta maps/LRU/sets.
  if (!hasOfsDelta && !hasRefDelta) {
    for (let i = 0; i < n; i++) {
      const r = raws[i];
      const t = r.type as ObjType;
      out[i] = { oid: hashObject(t, r.data), type: t, data: r.data, packedEntry: r.packedEntry };
    }
    return out;
  }

  let rawByOffset: Map<number, RawPackItem> | null = null;
  if (hasOfsDelta) {
    rawByOffset = new Map<number, RawPackItem>();
    for (let i = 0; i < n; i++) rawByOffset.set(raws[i].offset, raws[i]);
  }
  const baseCache = new DeltaBaseByteLru(hasRefDelta);
  let rawByOid: Map<string, RawPackItem> | null = null;
  const seen = new Set<number>();

  const ensureRawByOid = (): Map<string, RawPackItem> => {
    if (rawByOid !== null) return rawByOid;
    rawByOid = new Map<string, RawPackItem>();
    for (let i = 0; i < n; i++) {
      const r = raws[i];
      if (r.type !== null) {
        const oid = hashObject(r.type, r.data);
        rawByOid.set(oid, r);
      }
    }
    return rawByOid;
  };

  const resolve = (raw: RawPackItem): PackEntry => {
    const cached = baseCache.getByOffset(raw.offset);
    if (cached !== undefined) return cached;
    if (seen.has(raw.offset)) throw new Error('delta cycle');
    seen.add(raw.offset);
    let entry: PackEntry;
    try {
      if (raw.type !== null) {
        entry = { oid: hashObject(raw.type, raw.data), type: raw.type, data: raw.data, packedEntry: raw.packedEntry };
      } else if (raw.baseOffset !== null) {
        let base = baseCache.getByOffset(raw.baseOffset);
        if (base === undefined) {
          const baseRaw = rawByOffset!.get(raw.baseOffset);
          if (!baseRaw) throw new Error('ofs-delta base missing');
          base = resolve(baseRaw);
        }
        const data = applyDelta(base.data, raw.data);
        entry = { oid: hashObject(base.type, data), type: base.type, data, packedEntry: null };
      } else {
        const baseOid = raw.baseOid ?? '';
        let baseType: ObjType;
        let baseData: Buffer;
        const cachedBase = baseCache.getByOid(baseOid);
        if (cachedBase !== undefined) {
          baseType = cachedBase.type;
          baseData = cachedBase.data;
        } else {
          const existing = existingObjects?.get(baseOid);
          if (existing !== undefined) {
            baseType = existing.type;
            baseData = existing.data;
          } else {
            const baseRaw = ensureRawByOid().get(baseOid);
            if (!baseRaw) throw new Error('ref-delta base missing');
            const b = resolve(baseRaw);
            baseType = b.type;
            baseData = b.data;
          }
        }
        const data = applyDelta(baseData, raw.data);
        entry = { oid: hashObject(baseType, data), type: baseType, data, packedEntry: null };
      }
    } finally {
      seen.delete(raw.offset);
    }
    baseCache.put(raw.offset, entry);
    return entry;
  };

  for (let i = 0; i < n; i++) {
    const raw = raws[i];
    if (raw.type !== null) {
      let entry = baseCache.getByOffset(raw.offset);
      if (entry === undefined) {
        entry = { oid: hashObject(raw.type, raw.data), type: raw.type, data: raw.data, packedEntry: raw.packedEntry };
        baseCache.put(raw.offset, entry);
      }
      out[i] = entry;
    } else {
      out[i] = resolve(raw);
    }
  }
  baseCache.clear();
  return out;
}

function readPack(buf: Buffer, existingObjects?: Map<string, GitObj>): PackEntry[] | Promise<PackEntry[]> {
  if (buf.length < 12 || buf.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('bad pack header');
  const version = buf.readUInt32BE(4);
  if (version !== 2 && version !== 3) throw new Error('bad pack version');
  const count = buf.readUInt32BE(8);
  const trailerStart = buf.length - 20;
  if (trailerStart < 12) throw new Error('pack too short');
  const expect = sha1(buf.subarray(0, trailerStart));
  if (buf.subarray(trailerStart).toString('hex') !== expect) throw new Error('pack checksum mismatch');

  const raws: RawPackItem[] = new Array(count);
  let hasOfsDelta = false;
  let hasRefDelta = false;
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
      hasOfsDelta = true;
      if (off >= trailerStart) throw new Error('ofs-delta truncated');
      let bb = buf[off++];
      let base = bb & 0x7f;
      while (bb & 0x80) {
        bb = buf[off++];
        base = ((base + 1) << 7) | (bb & 0x7f);
      }
      baseOffset = start - base;
    } else if (typeCode === 7) {
      hasRefDelta = true;
      if (off + 20 > trailerStart) throw new Error('ref-delta truncated');
      baseOid = buf.subarray(off, off + 20).toString('hex');
      off += 20;
    }
    try {
      const { data, consumed } = inflateEntrySync(buf, off, size);
      off += consumed;
      const objType = PACK_TYPE_MAP[typeCode] ?? null;
      const packedEntry = objType !== null ? Buffer.from(buf.subarray(start, off)) : null;
      raws[i] = { offset: start, typeCode, type: objType, data, baseOffset, baseOid, packedEntry };
    } catch {
      // Async streaming fallback from entry `i` onward (only for >= 2 MiB or edge streams).
      return (async () => {
        let curStart = start;
        let curTypeCode = typeCode;
        let curSize = size;
        let curBaseOffset = baseOffset;
        let curBaseOid = baseOid;
        for (let j = i; j < count; j++) {
          if (j > i) {
            curStart = off;
            if (off >= trailerStart) throw new Error('pack truncated');
            let b2 = buf[off++];
            curTypeCode = (b2 >> 4) & 7;
            curSize = b2 & 0x0f;
            let sh = 4;
            while (b2 & 0x80) {
              if (off >= trailerStart) throw new Error('pack truncated');
              b2 = buf[off++];
              curSize |= (b2 & 0x7f) << sh;
              sh += 7;
            }
            curBaseOffset = null;
            curBaseOid = null;
            if (curTypeCode === 6) {
              hasOfsDelta = true;
              if (off >= trailerStart) throw new Error('ofs-delta truncated');
              let bb2 = buf[off++];
              let bs2 = bb2 & 0x7f;
              while (bb2 & 0x80) {
                bb2 = buf[off++];
                bs2 = ((bs2 + 1) << 7) | (bb2 & 0x7f);
              }
              curBaseOffset = curStart - bs2;
            } else if (curTypeCode === 7) {
              hasRefDelta = true;
              if (off + 20 > trailerStart) throw new Error('ref-delta truncated');
              curBaseOid = buf.subarray(off, off + 20).toString('hex');
              off += 20;
            }
          }
          let res: { data: Buffer; consumed: number };
          try {
            res = inflateEntrySync(buf, off, curSize);
          } catch {
            res = await inflateEntryStream(buf, off, curSize);
          }
          off += res.consumed;
          const objType = PACK_TYPE_MAP[curTypeCode] ?? null;
          const packedEntry = objType !== null ? Buffer.from(buf.subarray(curStart, off)) : null;
          raws[j] = {
            offset: curStart, typeCode: curTypeCode, type: objType, data: res.data,
            baseOffset: curBaseOffset, baseOid: curBaseOid, packedEntry,
          };
        }
        return resolvePackRaws(raws, hasOfsDelta, hasRefDelta, existingObjects);
      })();
    }
  }
  return resolvePackRaws(raws, hasOfsDelta, hasRefDelta, existingObjects);
}

function writePack(entries: PackEntry[]): Buffer {
  // No delta compression for shallow clones or small packs: emit pre-compressed
  // packedEntry slices directly into a single pre-allocated buffer + SHA-1 trailer.
  const packed: Buffer[] = new Array(entries.length);
  let bodyLen = 12;
  for (let i = 0; i < entries.length; i++) {
    const e = entries[i];
    let pe: Buffer;
    if (e.obj) {
      pe = getPackedEntry(e.obj);
    } else if (e.packedEntry) {
      pe = e.packedEntry;
    } else {
      const hdr = encodePackObjHeader(PACK_OBJ_TYPE_CODE[e.type], e.data.length);
      const comp = deflateSync(e.data, { level: 1 });
      pe = Buffer.allocUnsafe(hdr.length + comp.length);
      hdr.copy(pe, 0);
      comp.copy(pe, hdr.length);
      e.packedEntry = pe;
    }
    packed[i] = pe;
    bodyLen += pe.length;
  }
  const out = Buffer.allocUnsafe(bodyLen + 20);
  out.write('PACK', 0, 4, 'ascii');
  out.writeUInt32BE(2, 4);
  out.writeUInt32BE(entries.length, 8);
  let pos = 12;
  for (let i = 0; i < packed.length; i++) {
    const pe = packed[i];
    pe.copy(out, pos);
    pos += pe.length;
  }
  createHash('sha1').update(out.subarray(0, bodyLen)).digest().copy(out, bodyLen);
  return out;
}

// ---------------------------------------------------------------- commit graph (SoA TypedArrays)

interface CommitMeta { tree: string; parents: string[]; commitDate: number; }

/**
 * Lazy commit header scanner: reads only tree OID, parent OIDs, and committer
 * unix timestamp directly from raw bytes via indexOf(0x0a), avoiding UTF-8
 * decoding of author/email/message until REST or GraphQL requests them.
 */
function scanCommitMeta(data: Buffer): CommitMeta {
  let tree = '';
  const parents: string[] = [];
  let commitDate = FIXED_EPOCH;
  const len = data.length;
  let pos = 0;
  while (pos < len) {
    const nl = data.indexOf(0x0a, pos);
    const lineEnd = nl < 0 ? len : nl;
    if (lineEnd === pos) break; // blank line terminates commit headers
    const lineLen = lineEnd - pos;
    const b0 = data[pos];
    if (b0 === 0x74 /* 't' */ && lineLen >= 45 && data[pos + 1] === 0x72 && data[pos + 2] === 0x65 && data[pos + 3] === 0x65 && data[pos + 4] === 0x20) {
      tree = data.subarray(pos + 5, pos + 45).toString('latin1');
    } else if (b0 === 0x70 /* 'p' */ && lineLen >= 47 && data[pos + 1] === 0x61 && data[pos + 2] === 0x72 && data[pos + 3] === 0x65 && data[pos + 4] === 0x6e && data[pos + 5] === 0x74 && data[pos + 6] === 0x20) {
      parents.push(data.subarray(pos + 7, pos + 47).toString('latin1'));
    } else if (b0 === 0x63 /* 'c' */ && lineLen > 12 && data[pos + 1] === 0x6f && data[pos + 2] === 0x6d && data[pos + 3] === 0x6d && data[pos + 4] === 0x69 && data[pos + 5] === 0x74 && data[pos + 6] === 0x74 && data[pos + 7] === 0x65 && data[pos + 8] === 0x72 && data[pos + 9] === 0x20) {
      // Parse `<timestamp> <tz>` at the end of the committer line without allocations.
      let tzSp = lineEnd - 1;
      while (tzSp > pos && data[tzSp] !== 0x20) tzSp--;
      if (tzSp > pos) {
        let tsStart = tzSp - 1;
        while (tsStart > pos && data[tsStart - 1] !== 0x20) tsStart--;
        if (tsStart < tzSp) {
          let ts = 0;
          let valid = true;
          for (let i = tsStart; i < tzSp; i++) {
            const d = data[i] - 48;
            if (d < 0 || d > 9) { valid = false; break; }
            ts = ts * 10 + d;
          }
          if (valid) commitDate = ts;
        }
      }
    }
    if (nl < 0) break;
    pos = nl + 1;
  }
  return { tree, parents, commitDate };
}

class CommitGraph {
  oidToId = new Map<string, number>();
  idToOid: string[] = [];
  treeOids: string[] = [];
  parent1: Int32Array;
  parent2: Int32Array;
  extraParents: Int32Array[] = [];
  commitDate: Float64Array;
  gen: Float64Array;
  visitStamp: Uint32Array;
  walkEpoch = 0;
  count = 0;
  private capacity = 256;
  private pendingParents = new Map<number, string[]>();
  private walkStack: number[] = [];

  constructor() {
    const cap = this.capacity;
    this.parent1 = new Int32Array(cap).fill(-1);
    this.parent2 = new Int32Array(cap).fill(-1);
    this.commitDate = new Float64Array(cap);
    this.gen = new Float64Array(cap);
    this.visitStamp = new Uint32Array(cap);
  }

  private grow(): void {
    const nextCap = this.capacity * 2;
    const p1 = new Int32Array(nextCap).fill(-1);
    p1.set(this.parent1);
    this.parent1 = p1;
    const p2 = new Int32Array(nextCap).fill(-1);
    p2.set(this.parent2);
    this.parent2 = p2;
    const cd = new Float64Array(nextCap);
    cd.set(this.commitDate);
    this.commitDate = cd;
    const g = new Float64Array(nextCap);
    g.set(this.gen);
    this.gen = g;
    const vs = new Uint32Array(nextCap);
    vs.set(this.visitStamp);
    this.visitStamp = vs;
    this.capacity = nextCap;
  }

  private linkResolvedParents(id: number, parentIds: number[]): void {
    if (parentIds.length === 0) {
      this.parent1[id] = -1;
      this.parent2[id] = -1;
    } else if (parentIds.length === 1) {
      this.parent1[id] = parentIds[0];
      this.parent2[id] = -1;
    } else if (parentIds.length === 2) {
      this.parent1[id] = parentIds[0];
      this.parent2[id] = parentIds[1];
    } else {
      this.parent1[id] = parentIds[0];
      const idx = this.extraParents.length;
      this.extraParents.push(Int32Array.from(parentIds));
      this.parent2[id] = -(idx + 2);
    }
  }

  addCommit(oid: string, data: Buffer): number {
    const existing = this.oidToId.get(oid);
    if (existing !== undefined) return existing;
    if (this.count === this.capacity) this.grow();
    const meta = scanCommitMeta(data);
    const id = this.count++;
    this.oidToId.set(oid, id);
    this.idToOid.push(oid);
    this.treeOids.push(meta.tree);
    this.commitDate[id] = meta.commitDate;

    const pLen = meta.parents.length;
    if (pLen === 0) {
      this.parent1[id] = -1;
      this.parent2[id] = -1;
      this.gen[id] = meta.commitDate;
      return id;
    }
    if (pLen === 1) {
      const pid = this.oidToId.get(meta.parents[0]);
      if (pid !== undefined) {
        this.parent1[id] = pid;
        this.parent2[id] = -1;
        const pg = this.gen[pid];
        this.gen[id] = Number.isFinite(pg) ? Math.max(meta.commitDate, pg + 1) : Infinity;
        return id;
      }
      this.parent1[id] = -1;
      this.parent2[id] = -1;
      this.gen[id] = Infinity;
      this.pendingParents.set(id, meta.parents);
      return id;
    }
    const resolvedIds: number[] = new Array(pLen);
    let allFound = true;
    let maxParentGen = -Infinity;
    for (let i = 0; i < pLen; i++) {
      const pid = this.oidToId.get(meta.parents[i]);
      if (pid === undefined) { allFound = false; break; }
      resolvedIds[i] = pid;
      const pg = this.gen[pid];
      if (!Number.isFinite(pg)) maxParentGen = Infinity;
      else if (pg > maxParentGen) maxParentGen = pg;
    }
    if (allFound) {
      this.linkResolvedParents(id, resolvedIds);
      this.gen[id] = Number.isFinite(maxParentGen) ? Math.max(meta.commitDate, maxParentGen + 1) : Infinity;
    } else {
      this.parent1[id] = -1;
      this.parent2[id] = -1;
      this.gen[id] = Infinity;
      this.pendingParents.set(id, meta.parents);
    }
    return id;
  }

  /** Link out-of-order commits after a pack completes and finalize topological generation numbers. */
  finalizePending(): void {
    if (this.pendingParents.size === 0) return;
    const newlyResolved: number[] = [];
    for (const [id, pOids] of this.pendingParents) {
      const resolvedIds: number[] = [];
      let allFound = true;
      for (let i = 0; i < pOids.length; i++) {
        const pid = this.oidToId.get(pOids[i]);
        if (pid === undefined) { allFound = false; break; }
        resolvedIds.push(pid);
      }
      if (allFound) {
        this.linkResolvedParents(id, resolvedIds);
        this.pendingParents.delete(id);
        newlyResolved.push(id);
      }
    }
    if (newlyResolved.length === 0) return;
    // Compute generation numbers in topological order for all commits with gen === Infinity
    // that have no unresolved (graft/shallow) ancestor.
    const state = new Uint8Array(this.count); // 0=unvisited, 1=visiting, 2=done
    const computeGen = (startId: number): void => {
      const stack: number[] = [startId];
      while (stack.length > 0) {
        const u = stack[stack.length - 1];
        if (state[u] === 2) { stack.pop(); continue; }
        if (this.pendingParents.has(u)) {
          this.gen[u] = Infinity;
          state[u] = 2;
          stack.pop();
          continue;
        }
        const p1 = this.parent1[u];
        const p2 = this.parent2[u];
        if (state[u] === 0) {
          state[u] = 1;
          if (p2 < -1) {
            const arr = this.extraParents[-(p2 + 2)];
            for (let i = 0; i < arr.length; i++) {
              const p = arr[i];
              if (!Number.isFinite(this.gen[p]) && state[p] === 0) stack.push(p);
            }
          } else {
            if (p1 >= 0 && !Number.isFinite(this.gen[p1]) && state[p1] === 0) stack.push(p1);
            if (p2 >= 0 && !Number.isFinite(this.gen[p2]) && state[p2] === 0) stack.push(p2);
          }
        } else {
          stack.pop();
          state[u] = 2;
          let maxPg = -Infinity;
          if (p2 < -1) {
            const arr = this.extraParents[-(p2 + 2)];
            for (let i = 0; i < arr.length; i++) {
              const pg = this.gen[arr[i]];
              if (!Number.isFinite(pg)) { maxPg = Infinity; break; }
              if (pg > maxPg) maxPg = pg;
            }
          } else {
            if (p1 >= 0) {
              const pg = this.gen[p1];
              if (!Number.isFinite(pg)) maxPg = Infinity;
              else if (pg > maxPg) maxPg = pg;
            }
            if (p2 >= 0 && Number.isFinite(maxPg)) {
              const pg = this.gen[p2];
              if (!Number.isFinite(pg)) maxPg = Infinity;
              else if (pg > maxPg) maxPg = pg;
            }
          }
          if (p1 < 0 && p2 === -1) this.gen[u] = this.commitDate[u];
          else this.gen[u] = Number.isFinite(maxPg) ? Math.max(this.commitDate[u], maxPg + 1) : Infinity;
        }
      }
    };
    for (let id = 0; id < this.count; id++) {
      if (!Number.isFinite(this.gen[id]) && !this.pendingParents.has(id) && state[id] === 0) {
        computeGen(id);
      }
    }
  }

  private nextEpoch(): number {
    if (++this.walkEpoch >= 0xffffffff) {
      this.visitStamp.fill(0);
      this.walkEpoch = 1;
    }
    return this.walkEpoch;
  }

  getTreeOid(oid: string): string | undefined {
    const id = this.oidToId.get(oid);
    return id !== undefined ? this.treeOids[id] : undefined;
  }

  getParents(oid: string): string[] | undefined {
    const id = this.oidToId.get(oid);
    if (id === undefined) return undefined;
    const pending = this.pendingParents.get(id);
    if (pending !== undefined) return pending;
    const p1 = this.parent1[id];
    if (p1 < 0) return [];
    const p2 = this.parent2[id];
    if (p2 === -1) return [this.idToOid[p1]];
    if (p2 >= 0) return [this.idToOid[p1], this.idToOid[p2]];
    const arr = this.extraParents[-(p2 + 2)];
    const out: string[] = new Array(arr.length);
    for (let i = 0; i < arr.length; i++) out[i] = this.idToOid[arr[i]];
    return out;
  }

  /** O(1) fast-forward check + generation-v2 pruned walk using visitStamp/walkEpoch (no Set). */
  isAncestor(ancOid: string, descOid: string): boolean | null {
    const ancId = this.oidToId.get(ancOid);
    const descId = this.oidToId.get(descOid);
    if (ancId === undefined || descId === undefined) return null;
    if (ancId === descId) return true;
    // O(1) fast-forward check on direct parent1 / parent2.
    if (this.parent1[descId] === ancId) return true;
    const dp2 = this.parent2[descId];
    if (dp2 === ancId) return true;
    // Generation v2 pruning: never prunes when gen is Infinity (shallow/graft boundary).
    const ancGen = this.gen[ancId];
    const canPrune = Number.isFinite(ancGen);
    if (canPrune && this.gen[descId] <= ancGen) return false;

    const epoch = this.nextEpoch();
    const visit = this.visitStamp;
    const genArr = this.gen;
    const p1Arr = this.parent1;
    const p2Arr = this.parent2;
    const stack = this.walkStack;
    stack.length = 0;
    visit[descId] = epoch;
    stack.push(descId);

    while (stack.length > 0) {
      const u = stack.pop() as number;
      const p1 = p1Arr[u];
      const p2 = p2Arr[u];
      if (p2 < -1) {
        const arr = this.extraParents[-(p2 + 2)];
        for (let i = 0; i < arr.length; i++) {
          const p = arr[i];
          if (p === ancId) { stack.length = 0; return true; }
          if (visit[p] !== epoch && !(canPrune && genArr[p] <= ancGen)) {
            visit[p] = epoch;
            stack.push(p);
          }
        }
      } else if (p1 >= 0) {
        if (p1 === ancId) { stack.length = 0; return true; }
        if (visit[p1] !== epoch && !(canPrune && genArr[p1] <= ancGen)) {
          visit[p1] = epoch;
          stack.push(p1);
        }
        if (p2 >= 0) {
          if (p2 === ancId) { stack.length = 0; return true; }
          if (visit[p2] !== epoch && !(canPrune && genArr[p2] <= ancGen)) {
            visit[p2] = epoch;
            stack.push(p2);
          }
        }
      } else if (this.pendingParents.size > 0) {
        const pend = this.pendingParents.get(u);
        if (pend !== undefined) {
          for (let i = 0; i < pend.length; i++) {
            const pid = this.oidToId.get(pend[i]);
            if (pid === undefined) continue;
            if (pid === ancId) { stack.length = 0; return true; }
            if (visit[pid] !== epoch && !(canPrune && genArr[pid] <= ancGen)) {
              visit[pid] = epoch;
              stack.push(pid);
            }
          }
        }
      }
    }
    return false;
  }
}

// ---------------------------------------------------------------- store

interface Label { id: number; name: string; color: string; description: string; }
interface Comment { id: number; body: string; }
interface Issue {
  id: number; number: number; title: string; body: string;
  state: 'open' | 'closed'; labels: string[]; comments: Comment[]; seq: number;
  rev: number;
  etag: string;
  // Serialized REST form with trailing '\n', built once and served verbatim until
  // the issue mutates; list serialization slices [0, length - 1) zero-copy.
  jsonBuf: Buffer | null;
}
interface IssueListCacheEntry { buf: Buffer; link: string | null; etag: string; }
interface Pull {
  id: number; number: number; title: string; body: string;
  state: 'open' | 'closed'; merged: boolean; mergedAt: string | null; mergeSha: string | null;
  headRef: string; baseRef: string; mergeBase: string; seq: number;
}
interface Repo {
  id: number; name: string; owner: string; description: string; isPrivate: boolean;
  defaultBranch: string; refs: Map<string, string>; objects: Map<string, GitObj>;
  graph: CommitGraph;
  issues: Map<number, Issue>;
  openIssues: Issue[];
  closedIssues: Issue[];
  allIssues: Issue[];
  issuesVersion: number;
  issueListCache: Map<string, IssueListCacheEntry>;
  pulls: Map<number, Pull>; labels: Map<string, Label>;
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
    defaultBranch: 'main', refs: new Map(), objects: new Map(), graph: new CommitGraph(),
    issues: new Map(), openIssues: [], closedIssues: [], allIssues: [],
    issuesVersion: 1, issueListCache: new Map(),
    pulls: new Map(), labels: new Map(), seq: 0, createdSeq: globalSeq++,
  };
  repos.set(repoKey(repo.owner, name), repo);
  reposById.set(repo.id, repo);
  return repo;
}

function insertIssueSortedBySeq(arr: Issue[], issue: Issue): void {
  let lo = 0;
  let hi = arr.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (arr[mid].seq < issue.seq) lo = mid + 1;
    else hi = mid;
  }
  arr.splice(lo, 0, issue);
}
function removeIssueFromSorted(arr: Issue[], issue: Issue): void {
  let lo = 0;
  let hi = arr.length;
  while (lo < hi) {
    const mid = (lo + hi) >>> 1;
    if (arr[mid].seq < issue.seq) lo = mid + 1;
    else hi = mid;
  }
  if (lo < arr.length && arr[lo] === issue) arr.splice(lo, 1);
}
function createIssueRecord(repo: Repo, title: string, body: string, labelNames: string[]): Issue {
  const number = ++repo.seq;
  const issue: Issue = {
    id: objIdSeq++, number, title, body,
    state: 'open', labels: labelNames, comments: [], seq: globalSeq++,
    rev: 1, etag: `W/"i-${number}-v1"`, jsonBuf: null,
  };
  repo.issues.set(number, issue);
  repo.openIssues.push(issue);
  repo.allIssues.push(issue);
  repo.issuesVersion++;
  if (repo.issueListCache.size > 0) repo.issueListCache.clear();
  return issue;
}
/** Single mutation choke-point: keeps issue JSON cache, list index, list cache, and ETag strictly in sync. */
function invalidateIssue(repo: Repo, issue: Issue, prevState?: 'open' | 'closed'): void {
  if (prevState !== undefined && prevState !== issue.state) {
    if (prevState === 'open') {
      removeIssueFromSorted(repo.openIssues, issue);
      insertIssueSortedBySeq(repo.closedIssues, issue);
    } else {
      removeIssueFromSorted(repo.closedIssues, issue);
      insertIssueSortedBySeq(repo.openIssues, issue);
    }
  }
  issue.jsonBuf = null;
  issue.rev++;
  issue.etag = `W/"i-${issue.number}-v${issue.rev}"`;
  repo.issuesVersion++;
  if (repo.issueListCache.size > 0) repo.issueListCache.clear();
}

// object helpers bound to a repo
function putObj(repo: Repo, type: ObjType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) {
    repo.objects.set(oid, { type, data, packedEntry: null });
    if (type === 'commit') repo.graph.addCommit(oid, data);
  }
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
  for (const [oid, bytes] of trees) if (!repo.objects.has(oid)) repo.objects.set(oid, { type: 'tree', data: bytes, packedEntry: null });
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
  const cached = repo.graph.getParents(oid);
  if (cached !== undefined) return cached;
  const obj = getObj(repo, oid);
  if (!obj || obj.type !== 'commit') return [];
  return scanCommitMeta(obj.data).parents;
}
function commitTreeOid(repo: Repo, oid: string): string {
  const cached = repo.graph.getTreeOid(oid);
  if (cached !== undefined) return cached;
  const obj = getObj(repo, oid);
  if (!obj || obj.type !== 'commit') return '';
  return scanCommitMeta(obj.data).tree;
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
    const parents = repo.graph.getParents(oid);
    if (parents !== undefined) {
      out.add(oid);
      for (let i = 0; i < parents.length; i++) stack.push(parents[i]);
      continue;
    }
    const obj = getObj(repo, oid);
    if (!obj || obj.type !== 'commit') continue;
    out.add(oid);
    for (const p of scanCommitMeta(obj.data).parents) stack.push(p);
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
      const tree = commitTreeOid(repo, oid);
      if (tree) stack.push(tree);
      for (const p of commitParents(repo, oid)) stack.push(p);
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
  const graphResult = repo.graph.isAncestor(anc, desc);
  if (graphResult !== null) return graphResult;
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
    const parents = commitParents(repo, oid);
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

const EMPTY_BUF = Buffer.alloc(0);
const EXPECTED_BEARER = TOKEN !== '' ? `Bearer ${TOKEN}` : '';
const EXPECTED_TOKEN = TOKEN !== '' ? `token ${TOKEN}` : '';

function readBody(req: IncomingMessage): Promise<Buffer> {
  const te = req.headers['transfer-encoding'];
  const cl = req.headers['content-length'];
  if (te === undefined && (cl === undefined || cl === '0')) {
    return Promise.resolve(EMPTY_BUF);
  }
  return new Promise((resolve, reject) => {
    let first: Buffer | null = null;
    let chunks: Buffer[] | null = null;
    let total = 0;
    req.on('data', (c: Buffer) => {
      total += c.length;
      if (total > 64 * 1024 * 1024) { reject(new Error('body too large')); req.destroy(); return; }
      if (first === null) {
        first = c;
      } else if (chunks === null) {
        chunks = [first, c];
      } else {
        chunks.push(c);
      }
    });
    req.on('end', () => {
      if (chunks !== null) resolve(Buffer.concat(chunks, total));
      else resolve(first !== null ? first : EMPTY_BUF);
    });
    req.on('error', reject);
  });
}
function sendJson(res: ServerResponse, status: number, body: unknown, extra?: Record<string, string>): void {
  const text = `${JSON.stringify(body)}\n`;
  if (extra === undefined) {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': Buffer.byteLength(text),
      'x-github-request-id': `req-${reqSeq++}`,
    });
  } else {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': Buffer.byteLength(text),
      'x-github-request-id': `req-${reqSeq++}`,
      ...extra,
    });
  }
  res.end(text);
}
/** sendJson for a pre-serialized buffer (same headers, no re-stringify). */
function sendJsonBuf(res: ServerResponse, status: number, buf: Buffer, extra?: Record<string, string>): void {
  if (extra === undefined) {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': buf.length,
      'x-github-request-id': `req-${reqSeq++}`,
    });
  } else {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': buf.length,
      'x-github-request-id': `req-${reqSeq++}`,
      ...extra,
    });
  }
  res.end(buf);
}
function sendJsonBufFast(res: ServerResponse, status: number, buf: Buffer, etag: string, link: string | null, isHead: boolean): void {
  if (link === null) {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': buf.length,
      'x-github-request-id': `req-${reqSeq++}`,
      etag,
    });
  } else {
    res.writeHead(status, {
      'content-type': 'application/json; charset=utf-8',
      'content-length': buf.length,
      'x-github-request-id': `req-${reqSeq++}`,
      etag,
      link,
    });
  }
  if (isHead) res.end();
  else res.end(buf);
}
function sendNotModified(res: ServerResponse, etag: string): void {
  res.writeHead(304, {
    etag,
    'x-github-request-id': `req-${reqSeq++}`,
  });
  res.end();
}
function sendRaw(res: ServerResponse, status: number, buf: Buffer, contentType: string, extra?: Record<string, string>): void {
  if (extra === undefined) {
    res.writeHead(status, { 'content-type': contentType, 'content-length': buf.length });
  } else {
    res.writeHead(status, { 'content-type': contentType, 'content-length': buf.length, ...extra });
  }
  res.end(buf);
}
function sendNoContent(res: ServerResponse, status: number): void {
  res.writeHead(status, { 'x-github-request-id': `req-${reqSeq++}` });
  res.end();
}
/** RFC 9110 weak ETag comparison for If-None-Match (handles W/, '*', comma-separated list). */
function etagMatches(inm: string | string[] | undefined, currentEtag: string): boolean {
  if (inm === undefined) return false;
  const header = Array.isArray(inm) ? inm.join(',') : inm;
  const len = header.length;
  if (len === 0) return false;
  const curOpaque = currentEtag.startsWith('W/') ? currentEtag.slice(2) : currentEtag;
  let pos = 0;
  while (pos < len) {
    let comma = header.indexOf(',', pos);
    if (comma < 0) comma = len;
    let s = pos;
    let e = comma;
    while (s < e && (header.charCodeAt(s) === 32 || header.charCodeAt(s) === 9)) s++;
    while (e > s && (header.charCodeAt(e - 1) === 32 || header.charCodeAt(e - 1) === 9)) e--;
    if (e - s === 1 && header.charCodeAt(s) === 42 /* '*' */) return true;
    if (e - s >= 2 && header.charCodeAt(s) === 87 /* 'W' */ && header.charCodeAt(s + 1) === 47 /* '/' */) s += 2;
    if (e - s === curOpaque.length && header.slice(s, e) === curOpaque) return true;
    pos = comma + 1;
  }
  return false;
}
function isGitProtoV2(req: IncomingMessage): boolean {
  const gp = req.headers['git-protocol'];
  if (gp === undefined) return false;
  const s = Array.isArray(gp) ? gp.join(':') : gp;
  if (s === 'version=2') return true;
  let pos = 0;
  while (pos < s.length) {
    let next = s.indexOf(':', pos);
    if (next < 0) next = s.length;
    if (next - pos === 9 && s.slice(pos, next) === 'version=2') return true;
    pos = next + 1;
  }
  return false;
}
function decodeSeg(s: string): string {
  if (s.indexOf('%') < 0) return s;
  try { return decodeURIComponent(s); } catch { return s; }
}
function decodeQueryVal(s: string): string {
  if (s.indexOf('%') < 0 && s.indexOf('+') < 0) return s;
  const rep = s.indexOf('+') >= 0 ? s.replace(/\+/g, ' ') : s;
  if (rep.indexOf('%') < 0) return rep;
  try { return decodeURIComponent(rep); } catch { return rep; }
}
function parseUintAscii(s: string, start: number, end: number): number {
  if (start >= end) return -1;
  let v = 0;
  for (let i = start; i < end; i++) {
    const d = s.charCodeAt(i) - 48;
    if (d < 0 || d > 9) return -1;
    v = v * 10 + d;
  }
  return v;
}
interface IssueListQuery {
  state: string;
  direction: string;
  sort: string;
  labels: string;
  page: number;
  perPage: number;
  rawQs: string;
}
function parseIssueListQuery(qs: string): IssueListQuery {
  let state = 'open';
  let direction = 'desc';
  let sort = 'created';
  let labels = '';
  let page = 1;
  let perPage = 30;
  let pos = 0;
  const len = qs.length;
  while (pos < len) {
    let amp = qs.indexOf('&', pos);
    if (amp < 0) amp = len;
    if (amp > pos) {
      const eq = qs.indexOf('=', pos);
      const keyEnd = eq >= 0 && eq < amp ? eq : amp;
      const key = qs.slice(pos, keyEnd);
      const val = eq >= 0 && eq < amp ? qs.slice(eq + 1, amp) : '';
      if (key === 'state') state = decodeQueryVal(val);
      else if (key === 'direction') direction = decodeQueryVal(val);
      else if (key === 'sort') sort = decodeQueryVal(val);
      else if (key === 'labels') labels = decodeQueryVal(val);
      else if (key === 'page') {
        const n = parseInt(val, 10);
        if (n > 0) page = n;
      } else if (key === 'per_page') {
        const n = parseInt(val, 10);
        if (n > 0) perPage = n > 100 ? 100 : n;
      }
    }
    pos = amp + 1;
  }
  return { state, direction, sort, labels, page, perPage, rawQs: qs };
}
function pathOf(req: IncomingMessage): string {
  // The request-target is origin-form here; split off the query by hand
  // instead of building a URL object per request, and decode only when the
  // path actually carries percent-escapes (suite paths are plain ASCII).
  const raw = req.url ?? '/';
  const qi = raw.indexOf('?');
  let p = qi >= 0 ? raw.slice(0, qi) : raw;
  if (p === '') p = '/';
  if (p.indexOf('%') >= 0) {
    try { p = decodeURIComponent(p); } catch { /* keep raw */ }
  }
  return p;
}
function queryOf(req: IncomingMessage): URLSearchParams {
  // Parse only the query string by hand; a full URL object per request is
  // wasted when most handlers never read a query parameter.
  const raw = req.url ?? '';
  const qi = raw.indexOf('?');
  if (qi < 0) return new URLSearchParams();
  return new URLSearchParams(raw.slice(qi + 1));
}
type AuthResult = 'ok' | 'missing' | 'wrong';
function checkAuth(req: IncomingMessage): AuthResult {
  const h = req.headers.authorization;
  if (typeof h !== 'string' || h.length === 0) return 'missing';
  if (TOKEN !== '') {
    if (h === EXPECTED_BEARER || h === EXPECTED_TOKEN) return 'ok';
  }
  let tokStart: number;
  if (h.startsWith('Bearer ')) tokStart = 7;
  else if (h.startsWith('token ')) tokStart = 6;
  else return 'missing';
  if (h.length === tokStart) return 'missing';
  if (TOKEN !== '') return 'wrong';
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
  const server = createServer({ noDelay: true, keepAlive: true }, (req: IncomingMessage, res: ServerResponse) => {
    try {
      if (tryHandleSync(req, res)) return;
    } catch (err: unknown) {
      try {
        sendJson(res, 500, { message: err instanceof Error ? err.message : 'Internal Server Error' });
      } catch { /* socket gone */ }
      return;
    }
    handle(req, res).catch((err: unknown) => {
      try {
        sendJson(res, 500, { message: err instanceof Error ? err.message : 'Internal Server Error' });
      } catch { /* socket gone */ }
    });
  });
  server.keepAliveTimeout = 60000;
  server.headersTimeout = 65000;
  server.maxRequestsPerSocket = 0;
  return server;
}

/**
 * Synchronous hot-path dispatcher for GET/HEAD requests (issues single/list,
 * git info/refs advertisement, health/meta). Avoids Promise allocation,
 * microtask turns, regex routing, new URL(), and 'data' listeners.
 */
function tryHandleSync(req: IncomingMessage, res: ServerResponse): boolean {
  const method = req.method ?? 'GET';
  if (method !== 'GET' && method !== 'HEAD') return false;
  const isHead = method === 'HEAD';
  const rawUrl = req.url ?? '/';
  const qi = rawUrl.indexOf('?');
  const rawPath = qi >= 0 ? rawUrl.slice(0, qi) : rawUrl;
  const qs = qi >= 0 ? rawUrl.slice(qi + 1) : '';

  // Static health/meta endpoints
  if (!isHead) {
    if (rawPath === '/healthz') { sendJson(res, 200, { ok: true }); return true; }
    if (PERF_DIAG && rawPath === '/__perf_diag') {
      sendJson(res, 200, { ...perfDiag, uploadPackCacheBytes: uploadPackCache.bytes, uploadPackCacheEntries: uploadPackCache.size });
      return true;
    }
    if (rawPath === '/api/v3' || rawPath === '/api/v3/') {
      sendJson(res, 200, { current_user_url: '/api/v3/user', rate_limit_url: '/api/v3/rate_limit' }, { 'x-oauth-scopes': 'repo, read:org' });
      return true;
    }
    if (rawPath === '/api/v3/meta') { sendJson(res, 200, { installed_version: '1.0.0' }); return true; }
  }

  // Hot REST v3 issues paths: /api/v3/repos/<owner>/<repo>/issues[/:num]
  if (rawPath.startsWith('/api/v3/repos/')) {
    const ownerStart = 14; // '/api/v3/repos/'.length
    const s1 = rawPath.indexOf('/', ownerStart);
    if (s1 > ownerStart) {
      const s2 = rawPath.indexOf('/', s1 + 1);
      if (s2 > s1 + 1) {
        const tailStart = s2 + 1;
        // Exact match: /api/v3/repos/:owner/:repo/issues
        if (rawPath.length === tailStart + 6 && rawPath.endsWith('/issues')) {
          const auth = checkAuth(req);
          if (auth !== 'ok') { authFail(res, auth); return true; }
          const owner = decodeSeg(rawPath.slice(ownerStart, s1));
          const repoName = decodeSeg(rawPath.slice(s1 + 1, s2));
          const repo = getRepo(owner, repoName);
          if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }
          const listEtag = `"list-v${repo.issuesVersion}"`;
          if (etagMatches(req.headers['if-none-match'], listEtag)) {
            sendNotModified(res, listEtag);
            return true;
          }
          const q = parseIssueListQuery(qs);
          const host = req.headers.host ?? '127.0.0.1';
          const entry = getIssueListCached(repo, q, host, rawPath);
          sendJsonBufFast(res, 200, entry.buf, entry.etag, entry.link, isHead);
          return true;
        }
        // Single issue: /api/v3/repos/:owner/:repo/issues/:num
        if (rawPath.startsWith('issues/', tailStart)) {
          const numStart = tailStart + 7;
          const nextSlash = rawPath.indexOf('/', numStart);
          if (nextSlash < 0) {
            const num = parseUintAscii(rawPath, numStart, rawPath.length);
            if (num >= 0) {
              const auth = checkAuth(req);
              if (auth !== 'ok') { authFail(res, auth); return true; }
              const owner = decodeSeg(rawPath.slice(ownerStart, s1));
              const repoName = decodeSeg(rawPath.slice(s1 + 1, s2));
              const repo = getRepo(owner, repoName);
              if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }
              const issue = repo.issues.get(num);
              if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return true; }
              if (etagMatches(req.headers['if-none-match'], issue.etag)) {
                sendNotModified(res, issue.etag);
                return true;
              }
              sendJsonBufFast(res, 200, issueJsonBuf(repo, issue), issue.etag, null, isHead);
              return true;
            }
          }
        }
      }
    }
    return false;
  }

  // Hot Git info/refs advertisement: GET /:owner/:repo.git/info/refs?service=...
  if (!isHead && rawPath.endsWith('.git/info/refs')) {
    const s1 = rawPath.indexOf('/', 1);
    const gitSuffixIdx = rawPath.length - 14; // '.git/info/refs'.length
    if (s1 > 1 && gitSuffixIdx > s1 + 1 && rawPath.indexOf('/', s1 + 1) === gitSuffixIdx + 4) {
      const auth = checkAuth(req);
      if (auth !== 'ok') { authFail(res, auth); return true; }
      const owner = decodeSeg(rawPath.slice(1, s1));
      const repoName = decodeSeg(rawPath.slice(s1 + 1, gitSuffixIdx));
      const repo = getRepo(owner, repoName);
      if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }
      let service = '';
      if (qs === 'service=git-upload-pack') service = 'git-upload-pack';
      else if (qs === 'service=git-receive-pack') service = 'git-receive-pack';
      else if (qs.length > 0) {
        let pos = 0;
        while (pos < qs.length) {
          let amp = qs.indexOf('&', pos);
          if (amp < 0) amp = qs.length;
          if (qs.startsWith('service=', pos)) {
            service = decodeQueryVal(qs.slice(pos + 8, amp));
            break;
          }
          pos = amp + 1;
        }
      }
      if (service === 'git-upload-pack') {
        const v2 = isGitProtoV2(req);
        sendRaw(res, 200, v2 ? V2_ADVERTISEMENT : v0AdvertisementCached(repo, 'git-upload-pack'), 'application/x-git-upload-pack-advertisement');
        return true;
      }
      if (service === 'git-receive-pack') {
        sendRaw(res, 200, v0AdvertisementCached(repo, 'git-receive-pack'), 'application/x-git-receive-pack-advertisement');
        return true;
      }
      sendJson(res, 404, { message: 'Not Found' });
      return true;
    }
  }

  return false;
}

async function handle(req: IncomingMessage, res: ServerResponse): Promise<void> {
  const method = req.method ?? 'GET';

  // Fast path: 200 sequential POSTs creating issues — no regex, no new URL().
  if (method === 'POST' && req.url !== undefined && req.url.startsWith('/api/v3/repos/') && req.url.endsWith('/issues')) {
    const rawUrl = req.url;
    if (rawUrl.indexOf('?') < 0) {
      const ownerStart = 14;
      const s1 = rawUrl.indexOf('/', ownerStart);
      const s2 = s1 > ownerStart ? rawUrl.indexOf('/', s1 + 1) : -1;
      if (s2 > s1 + 1 && s2 + 7 === rawUrl.length) {
        const auth = checkAuth(req);
        if (auth !== 'ok') { authFail(res, auth); return; }
        const raw = await readBody(req);
        const parsed = parseJsonBody(raw);
        if (!parsed.ok) { sendJson(res, 400, { message: 'Invalid JSON' }); return; }
        const repo = getRepo(decodeSeg(rawUrl.slice(ownerStart, s1)), decodeSeg(rawUrl.slice(s1 + 1, s2)));
        if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return; }
        const b = (parsed.value ?? {}) as J;
        const title = typeof b.title === 'string' ? b.title : '';
        if (title === '') { sendJson(res, 422, { message: 'title is required' }); return; }
        const labelNames: string[] = [];
        if (Array.isArray(b.labels)) {
          for (let i = 0; i < b.labels.length; i++) {
            const l = b.labels[i];
            const name = typeof l === 'string' ? l : (l as J)?.name;
            if (typeof name !== 'string') continue;
            if (!repo.labels.has(name)) { sendJson(res, 422, { message: `Label '${name}' does not exist` }); return; }
            labelNames.push(name);
          }
        }
        const issue = createIssueRecord(repo, title, typeof b.body === 'string' ? b.body : '', labelNames);
        sendJsonBufFast(res, 201, issueJsonBuf(repo, issue), issue.etag, null, false);
        return;
      }
    }
  }

  const path = pathOf(req);

  if (method === 'GET' && path === '/healthz') {
    sendJson(res, 200, { ok: true });
    return;
  }
  if (PERF_DIAG && method === 'GET' && path === '/__perf_diag') {
    sendJson(res, 200, { ...perfDiag, uploadPackCacheBytes: uploadPackCache.bytes, uploadPackCacheEntries: uploadPackCache.size });
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

// ---- hot-path caches ----
// Git objects are immutable by OID, so a fetch response depends only on its
// normalized protocol/wants/haves/depth/shallow/filter/caps arguments plus the
// objects it names: safe to memoize per repository in a byte-bounded LRU.
// Advertisements and ls-refs depend on the ref set, so they are keyed on a
// fingerprint of it. Singleflight coalesces concurrent identical fetch builds.
class ByteLruCache {
  private map = new Map<string, Buffer>();
  private maxBytes: number;
  bytes = 0;
  constructor(maxBytes: number) {
    this.maxBytes = maxBytes;
  }
  get size(): number {
    return this.map.size;
  }
  get(key: string): Buffer | undefined {
    const v = this.map.get(key);
    if (v === undefined) return undefined;
    // Promote to MRU in O(1) using Map insertion order.
    this.map.delete(key);
    this.map.set(key, v);
    return v;
  }
  set(key: string, val: Buffer): Buffer {
    if (val.length > this.maxBytes) return val;
    const old = this.map.get(key);
    if (old !== undefined) {
      this.bytes -= old.length;
      this.map.delete(key);
    }
    while (this.bytes + val.length > this.maxBytes && this.map.size > 0) {
      const oldestKey = this.map.keys().next().value as string;
      const oldestVal = this.map.get(oldestKey) as Buffer;
      this.map.delete(oldestKey);
      this.bytes -= oldestVal.length;
    }
    this.map.set(key, val);
    this.bytes += val.length;
    return val;
  }
  clear(): void {
    this.map.clear();
    this.bytes = 0;
  }
}

const uploadPackCache = new ByteLruCache(64 * 1024 * 1024);
const uploadPackInflight = new Map<string, Promise<Buffer>>();
const lsRefsCache = new Map<string, Buffer>();
const advertCache = new Map<string, Buffer>();

// Capability bitmask for deterministic upload-pack cache keys.
const CAP_SIDE_BAND_64K = 1 << 0;
const CAP_SIDE_BAND = 1 << 1;
const CAP_NO_PROGRESS = 1 << 2;
const CAP_OFS_DELTA = 1 << 3;
const CAP_INCLUDE_TAG = 1 << 4;
const CAP_DONE = 1 << 5;
const CAP_MULTI_ACK = 1 << 6;
const CAP_MULTI_ACK_DETAILED = 1 << 7;
const CAP_NO_DONE = 1 << 8;
const CAP_THIN_PACK = 1 << 9;
const CAP_DEEPEN_RELATIVE = 1 << 10;

function refsFingerprint(repo: Repo): string {
  let fp = '';
  for (const [name, oid] of repo.refs) fp += `${name}=${oid};`;
  return fp;
}
function sortedUniqueJoin(arr: string[]): string {
  if (arr.length === 0) return '';
  if (arr.length === 1) return arr[0];
  const copy = [...arr].sort();
  let out = copy[0];
  for (let i = 1; i < copy.length; i++) {
    if (copy[i] !== copy[i - 1]) out += `,${copy[i]}`;
  }
  return out;
}
function fetchCacheKey(proto: 'v0' | 'v2', repo: Repo, args: FetchArgs): string {
  return `${proto}|${repo.id}|${sortedUniqueJoin(args.wants)}|${sortedUniqueJoin(args.haves)}|${args.depth ?? ''}|${sortedUniqueJoin(args.shallow)}|${args.deepenSince ?? ''}|${sortedUniqueJoin(args.deepenNot)}|${args.filter}|${args.capsMask}`;
}
function canCacheFetch(repo: Repo, args: FetchArgs): boolean {
  if (args.deepenNot.length > 0) return false;
  for (let i = 0; i < args.wants.length; i++) {
    if (!repo.objects.has(args.wants[i])) return false;
  }
  return true;
}
function cachePut(m: Map<string, Buffer>, key: string, buf: Buffer): Buffer {
  if (m.size > 128) m.clear();
  m.set(key, buf);
  return buf;
}
function getOrBuildUploadPack(key: string, cacheable: boolean, build: () => Buffer): Buffer | Promise<Buffer> {
  if (cacheable) {
    const hit = uploadPackCache.get(key);
    if (hit !== undefined) {
      if (PERF_DIAG) perfDiag.uploadPackHits++;
      return hit;
    }
    const inflight = uploadPackInflight.get(key);
    if (inflight !== undefined) {
      if (PERF_DIAG) { perfDiag.uploadPackHits++; perfDiag.uploadPackSingleflight++; }
      return inflight;
    }
  }
  if (PERF_DIAG) perfDiag.uploadPackMisses++;
  if (!cacheable) return build();
  let resolveFn!: (b: Buffer) => void;
  let rejectFn!: (e: unknown) => void;
  const p = new Promise<Buffer>((res, rej) => { resolveFn = res; rejectFn = rej; });
  uploadPackInflight.set(key, p);
  try {
    const buf = build();
    uploadPackCache.set(key, buf);
    uploadPackInflight.delete(key);
    resolveFn(buf);
    return buf;
  } catch (err) {
    uploadPackInflight.delete(key);
    rejectFn(err);
    // Avoid unhandled rejection if no follower attached
    p.catch(() => {});
    throw err;
  }
}

function sortedRefs(repo: Repo): Array<{ name: string; oid: string }> {
  return [...repo.refs.entries()].map(([name, oid]) => ({ name, oid })).sort((a, b) => (a.name < b.name ? -1 : 1));
}
function refCaps(service: 'git-upload-pack' | 'git-receive-pack'): string {
  if (service === 'git-upload-pack') {
    return `symref=HEAD:refs/heads/main object-format=sha1 side-band-64k side-band thin-pack ofs-delta shallow multi_ack multi_ack_detailed no-done agent=${AGENT}`;
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
// The v2 advertisement never depends on repository state: build once.
const V2_ADVERTISEMENT = v2Advertisement();
function v0AdvertisementCached(repo: Repo, service: 'git-upload-pack' | 'git-receive-pack'): Buffer {
  const key = `${service}|${repo.id}|${refsFingerprint(repo)}`;
  const hit = advertCache.get(key);
  if (hit) return hit;
  return cachePut(advertCache, key, v0Advertisement(repo, service));
}
function lsRefsCached(repo: Repo, args: LsRefsArgs): Buffer {
  const key = `${repo.id}|${refsFingerprint(repo)}|${args.peel ? 'p' : ''}${args.symrefs ? 's' : ''}${args.unborn ? 'u' : ''}|${args.prefixes.join(',')}`;
  const hit = lsRefsCache.get(key);
  if (hit) return hit;
  return cachePut(lsRefsCache, key, lsRefsResponse(repo, args));
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
  if (args.prefixes.length === 0 || args.prefixes.some((p) => 'HEAD'.startsWith(p))) {
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

interface FetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  depth: number | null;
  deepenSince: number | null;
  deepenNot: string[];
  filter: string;
  capsMask: number;
}
function parseFetchArgs(packets: Pkt[]): FetchArgs {
  const args: FetchArgs = {
    wants: [], haves: [], shallow: [], depth: null, deepenSince: null, deepenNot: [],
    filter: '', capsMask: CAP_SIDE_BAND_64K,
  };
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
    else if (line.startsWith('filter ')) args.filter = line.slice(7);
    else if (line === 'done') args.capsMask |= CAP_DONE;
    else if (line === 'no-progress') args.capsMask |= CAP_NO_PROGRESS;
    else if (line === 'ofs-delta') args.capsMask |= CAP_OFS_DELTA;
    else if (line === 'include-tag') args.capsMask |= CAP_INCLUDE_TAG;
    else if (line === 'thin-pack') args.capsMask |= CAP_THIN_PACK;
    else if (line === 'deepen-relative') args.capsMask |= CAP_DEEPEN_RELATIVE;
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
      const tree = commitTreeOid(repo, oid);
      if (tree) stack.push(tree);
      if (!shallow.has(oid)) for (const p of commitParents(repo, oid)) stack.push(p);
    } else if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) stack.push(e.oid);
    } else if (obj.type === 'tag') {
      stack.push(parseTag(obj.data).object);
    }
  }
  return out;
}
function treeClosure(repo: Repo, treeOid: string, out: Set<string>, filter: string = ''): void {
  if (filter === 'tree:0') return;
  const skipBlobs = filter === 'blob:none';
  const stack = [treeOid];
  while (stack.length) {
    const oid = stack.pop() as string;
    if (out.has(oid)) continue;
    const obj = getObj(repo, oid);
    if (!obj) continue;
    if (skipBlobs && obj.type === 'blob') continue;
    out.add(oid);
    if (obj.type === 'tree') {
      for (const e of parseTree(obj.data)) {
        if (skipBlobs && e.mode !== '40000') continue;
        stack.push(e.oid);
      }
    }
  }
}
function selectFetch(repo: Repo, args: FetchArgs): { objects: PackEntry[]; shallow: string[]; unshallow: string[] } {
  const filter = args.filter;
  const roots: string[] = [];
  const rootSet = new Set<string>();
  const direct = new Set<string>();
  for (const w of args.wants) {
    const obj = getObj(repo, w);
    if (!obj) continue;
    if (obj.type === 'commit') {
      if (!rootSet.has(w)) { rootSet.add(w); roots.push(w); }
    } else if (obj.type === 'tag') {
      direct.add(w);
      const target = peelToCommit(repo, w);
      if (!rootSet.has(target)) { rootSet.add(target); roots.push(target); }
    } else {
      direct.add(w);
    }
  }
  const deepenRelative = (args.capsMask & CAP_DEEPEN_RELATIVE) !== 0;
  let D: Set<string>;
  if (args.depth === null) {
    D = commitClosure(repo, roots);
  } else if (deepenRelative && args.shallow.length > 0) {
    D = new Set<string>();
    const clientShallow = new Set(args.shallow);
    // Include everything from roots down to the existing shallow boundary.
    const walkStack = [...roots];
    while (walkStack.length > 0) {
      const c = walkStack.pop() as string;
      if (D.has(c)) continue;
      const obj = getObj(repo, c);
      if (!obj || obj.type !== 'commit') continue;
      D.add(c);
      if (!clientShallow.has(c)) {
        for (const p of commitParents(repo, c)) walkStack.push(p);
      }
    }
    // Expand `args.depth` additional generations beyond the client's shallow commits.
    let frontier: string[] = [];
    for (const s of args.shallow) {
      for (const p of commitParents(repo, s)) frontier.push(p);
    }
    for (let d = 0; d < args.depth && frontier.length > 0; d++) {
      const next: string[] = [];
      for (const c of frontier) {
        if (D.has(c)) continue;
        const obj = getObj(repo, c);
        if (!obj || obj.type !== 'commit') continue;
        D.add(c);
        for (const p of commitParents(repo, c)) next.push(p);
      }
      frontier = next;
    }
  } else if (args.depth === 1) {
    // Fast path for shallow depth=1: D is just the root commits, O(|wants|).
    D = new Set<string>();
    for (const r of roots) {
      const obj = getObj(repo, r);
      if (obj && obj.type === 'commit') D.add(r);
    }
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
        for (const p of commitParents(repo, c)) next.push(p);
      }
      frontier = next;
    }
  }
  // Object set to send: depth-limited fetches take only D's own commits and
  // their trees/blobs — never ancestors. Full fetches take the whole closure.
  const wantSet = new Set<string>();
  if (args.depth === null && filter === '') {
    for (const o of fullClosure(repo, [...D, ...direct])) wantSet.add(o);
  } else {
    for (const c of D) {
      wantSet.add(c);
      if (filter !== 'tree:0') treeClosure(repo, commitTreeOid(repo, c), wantSet, filter);
    }
    for (const oid of direct) {
      const obj = getObj(repo, oid);
      if (!obj) continue;
      if (filter === 'blob:none' && obj.type === 'blob') continue;
      if (filter === 'tree:0' && (obj.type === 'blob' || obj.type === 'tree')) continue;
      wantSet.add(oid);
      if (obj.type === 'tag') {
        const target = parseTag(obj.data).object;
        const tobj = getObj(repo, target);
        if (tobj?.type === 'commit') {
          wantSet.add(target);
          if (filter !== 'tree:0') treeClosure(repo, commitTreeOid(repo, target), wantSet, filter);
        } else if (tobj?.type === 'tree' && filter !== 'tree:0') {
          treeClosure(repo, target, wantSet, filter);
        }
      }
    }
  }
  const haveClosure = args.haves.length > 0 ? closureWithShallow(repo, args.haves, new Set(args.shallow)) : null;
  const haveSet = args.haves.length > 0 ? new Set(args.haves) : null;
  const send = (haveClosure ? [...wantSet].filter((o) => !haveClosure.has(o)) : [...wantSet]).sort();
  const objects: PackEntry[] = new Array(send.length);
  for (let i = 0; i < send.length; i++) {
    const oid = send[i];
    const o = getObj(repo, oid) as GitObj;
    objects[i] = { oid, type: o.type, data: o.data, obj: o };
  }
  const shallow: string[] = [];
  const unshallow: string[] = [];
  const clientShallowSet = args.shallow.length > 0 ? new Set(args.shallow) : null;
  for (const c of D) {
    const parents = commitParents(repo, c);
    if (parents.length === 0) continue;
    if (clientShallowSet !== null && clientShallowSet.has(c) && parents.every((p) => D.has(p))) { unshallow.push(c); continue; }
    if (parents.some((p) => !D.has(p) && (haveSet === null || !haveSet.has(p)))) shallow.push(c);
  }
  if (shallow.length > 1) shallow.sort();
  if (unshallow.length > 1) unshallow.sort();
  return { objects, shallow, unshallow };
}

const HEX_CHARS = Buffer.from('0123456789abcdef', 'ascii');
const EMPTY_SIDEBAND_PKT = Buffer.from('0005\x01', 'latin1');
// Frame raw pack/status bytes onto side-band channel 1 in a single allocation.
// side-band-64k: max pkt-line = 65520 bytes (4 length + 1 channel + 65515 payload).
// side-band: max pkt-line = 1000 bytes (4 length + 1 channel + 995 payload).
function sidebandPack(pack: Buffer, maxChunk: number = 65515): Buffer {
  if (pack.length === 0) return EMPTY_SIDEBAND_PKT;
  const numChunks = Math.ceil(pack.length / maxChunk);
  const out = Buffer.allocUnsafe(pack.length + numChunks * 5);
  let src = 0;
  let dst = 0;
  while (src < pack.length) {
    const end = src + maxChunk < pack.length ? src + maxChunk : pack.length;
    const chunkLen = end - src;
    const pktLen = chunkLen + 5;
    out[dst] = HEX_CHARS[(pktLen >> 12) & 0xf];
    out[dst + 1] = HEX_CHARS[(pktLen >> 8) & 0xf];
    out[dst + 2] = HEX_CHARS[(pktLen >> 4) & 0xf];
    out[dst + 3] = HEX_CHARS[pktLen & 0xf];
    out[dst + 4] = 1;
    pack.copy(out, dst + 5, src, end);
    dst += pktLen;
    src = end;
  }
  return out;
}
function v2FetchResponse(repo: Repo, args: FetchArgs): Buffer | Promise<Buffer> {
  const key = fetchCacheKey('v2', repo, args);
  return getOrBuildUploadPack(key, canCacheFetch(repo, args), () => {
    const sel = selectFetch(repo, args);
    const parts: Buffer[] = [];
    const hasDone = (args.capsMask & CAP_DONE) !== 0;
    // Protocol v2 spec: when the client sends `done`, skip the `acknowledgments`
    // section and go directly to `shallow-info` (if any) and `packfile`.
    if (!hasDone) {
      parts.push(pktLine('acknowledgments\n'));
      // An ACK can only name a have the client sent; with no haves the whole
      // closure walk below is pure waste.
      let ack: string | undefined;
      if (args.haves.length > 0) {
        const wantClosure = commitClosure(repo, args.wants.filter((w) => {
          const o = getObj(repo, w);
          return !!o && o.type === 'commit';
        }));
        const sortedHaves = [...args.haves].sort();
        ack = sortedHaves.find((h) => wantClosure.has(h));
      }
      if (ack) { parts.push(pktLine(`ACK ${ack}\n`)); parts.push(pktLine('ready\n')); }
      else parts.push(pktLine('NAK\n'));
      parts.push(DELIM);
    }
    if (sel.shallow.length > 0 || sel.unshallow.length > 0) {
      parts.push(pktLine('shallow-info\n'));
      for (const s of sel.shallow) parts.push(pktLine(`shallow ${s}\n`));
      for (const s of sel.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
      parts.push(DELIM);
    }
    parts.push(pktLine('packfile\n'));
    parts.push(sidebandPack(writePack(sel.objects), 65515));
    parts.push(FLUSH);
    return Buffer.concat(parts);
  });
}
function v0FetchResponse(repo: Repo, body: Buffer): Buffer | Promise<Buffer> {
  const packets = parsePktLines(body);
  const args: FetchArgs = {
    wants: [], haves: [], shallow: [], depth: null, deepenSince: null, deepenNot: [],
    filter: '', capsMask: 0,
  };
  let section = 0;
  let sawAnyCaps = false;
  for (const p of packets) {
    if (p.kind === 'flush') { section++; continue; }
    if (p.kind !== 'data') continue;
    let line = p.payload.toString('utf8').trim();
    const nul = line.indexOf('\0');
    if (nul >= 0) line = line.slice(0, nul);
    if (section === 0) {
      if (line.startsWith('want ')) {
        const rest = line.slice(5);
        const sp = rest.indexOf(' ');
        if (sp < 0) {
          args.wants.push(rest);
        } else {
          args.wants.push(rest.slice(0, sp));
          sawAnyCaps = true;
          const capTokens = rest.slice(sp + 1).split(' ');
          for (const cap of capTokens) {
            if (cap === 'side-band-64k') args.capsMask |= CAP_SIDE_BAND_64K;
            else if (cap === 'side-band') args.capsMask |= CAP_SIDE_BAND;
            else if (cap === 'no-progress') args.capsMask |= CAP_NO_PROGRESS;
            else if (cap === 'ofs-delta') args.capsMask |= CAP_OFS_DELTA;
            else if (cap === 'include-tag') args.capsMask |= CAP_INCLUDE_TAG;
            else if (cap === 'multi_ack') args.capsMask |= CAP_MULTI_ACK;
            else if (cap === 'multi_ack_detailed') args.capsMask |= CAP_MULTI_ACK_DETAILED;
            else if (cap === 'no-done') args.capsMask |= CAP_NO_DONE;
            else if (cap === 'thin-pack') args.capsMask |= CAP_THIN_PACK;
          }
        }
      } else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8));
      else if (line.startsWith('deepen ')) args.depth = parseInt(line.slice(7), 10);
      else if (line.startsWith('deepen-since ')) args.deepenSince = parseInt(line.slice(13), 10);
      else if (line.startsWith('deepen-not ')) args.deepenNot.push(line.slice(11));
      else if (line.startsWith('filter ')) args.filter = line.slice(7);
    } else if (line.startsWith('have ')) args.haves.push(line.slice(5));
    else if (line === 'done') args.capsMask |= CAP_DONE;
  }
  // Preserve v9 default side-band-64k when client omits capability tokens.
  if (!sawAnyCaps) args.capsMask |= CAP_SIDE_BAND_64K;
  const key = fetchCacheKey('v0', repo, args);
  return getOrBuildUploadPack(key, canCacheFetch(repo, args), () => {
    const sel = selectFetch(repo, args);
    const parts: Buffer[] = [];
    // Shallow/unshallow lines precede ACK/NAK in v0 when depth negotiation occurred.
    if (sel.shallow.length > 0 || sel.unshallow.length > 0) {
      for (const s of sel.shallow) parts.push(pktLine(`shallow ${s}\n`));
      for (const s of sel.unshallow) parts.push(pktLine(`unshallow ${s}\n`));
      parts.push(FLUSH);
    }
    // See v2FetchResponse: no haves means no ACK is possible; skip the closure.
    let ack: string | undefined;
    if (args.haves.length > 0) {
      const wantClosure = commitClosure(repo, args.wants.filter((w) => {
        const o = getObj(repo, w);
        return !!o && o.type === 'commit';
      }));
      const sortedHaves = [...args.haves].sort();
      ack = sortedHaves.find((h) => wantClosure.has(h));
    }
    const isDetailed = (args.capsMask & CAP_MULTI_ACK_DETAILED) !== 0;
    const hasDone = (args.capsMask & CAP_DONE) !== 0;
    const hasNoDone = (args.capsMask & CAP_NO_DONE) !== 0;
    if (isDetailed && ack) {
      parts.push(pktLine(`ACK ${ack} common\n`));
      if (!hasDone) {
        if (hasNoDone) {
          parts.push(pktLine(`ACK ${ack} ready\n`));
          parts.push(pktLine('NAK\n'));
          parts.push(pktLine(`ACK ${ack}\n`));
        } else {
          parts.push(pktLine('NAK\n'));
          return Buffer.concat(parts);
        }
      } else {
        parts.push(pktLine(`ACK ${ack}\n`));
      }
    } else if (ack) {
      parts.push(pktLine(`ACK ${ack}\n`));
    } else {
      parts.push(pktLine('NAK\n'));
      if (isDetailed && !hasDone && args.haves.length > 0) {
        return Buffer.concat(parts);
      }
    }
    const pack = writePack(sel.objects);
    if (args.capsMask & CAP_SIDE_BAND_64K) {
      parts.push(sidebandPack(pack, 65515));
      parts.push(FLUSH);
    } else if (args.capsMask & CAP_SIDE_BAND) {
      parts.push(sidebandPack(pack, 995));
      parts.push(FLUSH);
    } else {
      parts.push(pack);
    }
    return Buffer.concat(parts);
  });
}

interface PushCmd { oldOid: string; newOid: string; ref: string; }
async function receivePackResponse(repo: Repo, body: Buffer): Promise<Buffer> {
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
      const parsed = readPack(rawPack, repo.objects);
      const entries = Array.isArray(parsed) ? parsed : await parsed;
      let addedCommit = false;
      for (let i = 0; i < entries.length; i++) {
        const e = entries[i];
        if (!repo.objects.has(e.oid)) {
          repo.objects.set(e.oid, { type: e.type, data: e.data, packedEntry: e.packedEntry ?? null });
          if (e.type === 'commit') {
            repo.graph.addCommit(e.oid, e.data);
            addedCommit = true;
          }
        }
      }
      if (addedCommit) repo.graph.finalizePending();
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
      } else if (current === undefined || current !== c.oldOid) {
        lines.push(`ng ${c.ref} non-fast-forward\n`);
      } else if (c.oldOid === c.newOid || isAncestor(repo, c.oldOid, c.newOid)) {
        repo.refs.set(c.ref, c.newOid);
        lines.push(`ok ${c.ref}\n`);
      } else {
        lines.push(`ng ${c.ref} non-fast-forward\n`);
      }
    }
  }
  const inner = pktLines([...lines, 'flush']);
  return Buffer.concat([sidebandPack(inner, 65515), FLUSH]);
}

async function handleGit(req: IncomingMessage, res: ServerResponse, path: string): Promise<boolean> {
  // Fast non-regex extraction of /:owner/:repo.git/:tail
  const gitIdx = path.indexOf('.git/');
  if (gitIdx < 3 || path.charCodeAt(0) !== 47 /* '/' */) return false;
  const slash = path.indexOf('/', 1);
  if (slash <= 1 || slash >= gitIdx - 1) return false;
  const owner = decodeSeg(path.slice(1, slash));
  const repoName = decodeSeg(path.slice(slash + 1, gitIdx));
  const tail = path.slice(gitIdx + 5);
  const method = req.method ?? 'GET';
  const auth = checkAuth(req);
  if (auth !== 'ok') { authFail(res, auth); return true; }
  const repo = getRepo(owner, repoName);
  if (!repo) { sendJson(res, 404, { message: 'Not Found' }); return true; }

  if (method === 'GET' && tail === 'info/refs') {
    const q = queryOf(req);
    const service = q.get('service') ?? '';
    if (service === 'git-upload-pack') {
      const v2 = isGitProtoV2(req);
      sendRaw(res, 200, v2 ? V2_ADVERTISEMENT : v0AdvertisementCached(repo, 'git-upload-pack'), 'application/x-git-upload-pack-advertisement');
      return true;
    }
    if (service === 'git-receive-pack') {
      sendRaw(res, 200, v0AdvertisementCached(repo, 'git-receive-pack'), 'application/x-git-receive-pack-advertisement');
      return true;
    }
    sendJson(res, 404, { message: 'Not Found' });
    return true;
  }
  if (method === 'POST' && tail === 'git-upload-pack') {
    const body = await readBody(req);
    const v2 = isGitProtoV2(req);
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
      sendRaw(res, 200, lsRefsCached(repo, parseLsRefsArgs(packets)), 'application/x-git-upload-pack-result');
      return true;
    }
    if (v2 && command === 'fetch') {
      const resp = v2FetchResponse(repo, parseFetchArgs(packets));
      sendRaw(res, 200, Buffer.isBuffer(resp) ? resp : await resp, 'application/x-git-upload-pack-result');
      return true;
    }
    if (!v2) {
      const resp = v0FetchResponse(repo, body);
      sendRaw(res, 200, Buffer.isBuffer(resp) ? resp : await resp, 'application/x-git-upload-pack-result');
      return true;
    }
    sendJson(res, 400, { message: 'unknown command' });
    return true;
  }
  if (method === 'POST' && tail === 'git-receive-pack') {
    const body = await readBody(req);
    let out: Buffer;
    try {
      out = await receivePackResponse(repo, body);
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
// The viewer never changes after startup: share one frozen shape instead of
// allocating a fresh object literal per issue/comment/pull shape.
const VIEWER_SHAPE: J = viewerShape();
function openCount(repo: Repo): number {
  let n = repo.openIssues.length;
  for (const p of repo.pulls.values()) if (p.state === 'open') n++;
  return n;
}
function repoShape(repo: Repo): J {
  return {
    id: repo.id, name: repo.name, full_name: `${repo.owner}/${repo.name}`, owner: VIEWER_SHAPE,
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
    user: VIEWER_SHAPE, assignee: null, assignees: [], milestone: null, locked: false,
    comments: issue.comments.length, created_at: FIXED_ISO, updated_at: FIXED_ISO, closed_at: issue.state === 'closed' ? FIXED_ISO : null,
    html_url: `https://github.com/${repo.owner}/${repo.name}/issues/${issue.number}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}

const VIEWER_JSON = JSON.stringify(VIEWER_SHAPE);
const ISSUE_MID_OPEN = `],"user":${VIEWER_JSON},"assignee":null,"assignees":[],"milestone":null,"locked":false,"comments":`;
const ISSUE_DATES_OPEN = `,"created_at":"${FIXED_ISO}","updated_at":"${FIXED_ISO}","closed_at":null,"html_url":"https://github.com/`;
const ISSUE_DATES_CLOSED = `,"created_at":"${FIXED_ISO}","updated_at":"${FIXED_ISO}","closed_at":"${FIXED_ISO}","html_url":"https://github.com/`;
const B_OPEN = Buffer.from('[', 'ascii');
const B_COMMA = Buffer.from(',', 'ascii');
const B_CLOSE_NL = Buffer.from(']\n', 'ascii');
const B_EMPTY_ARR_NL = Buffer.from('[]\n', 'ascii');

/** The exact bytes sendJson would write for this issue, memoized. */
function issueJsonBuf(repo: Repo, issue: Issue): Buffer {
  if (issue.jsonBuf !== null) return issue.jsonBuf;
  let text: string;
  if (issue.labels.length === 0) {
    const slug = `${repo.owner}/${repo.name}/issues/${issue.number}`;
    const dates = issue.state === 'closed' ? ISSUE_DATES_CLOSED : ISSUE_DATES_OPEN;
    text = `{"id":${issue.id},"number":${issue.number},"title":${JSON.stringify(issue.title)},"body":${JSON.stringify(issue.body)},"state":"${issue.state}","labels":[${ISSUE_MID_OPEN}${issue.comments.length}${dates}${slug}","url":"/api/v3/repos/${slug}"}\n`;
  } else {
    text = `${JSON.stringify(issueShape(repo, issue))}\n`;
  }
  const buf = Buffer.from(text, 'utf8');
  issue.jsonBuf = buf;
  return buf;
}

function buildIssueListLink(host: string, reqPath: string, q: IssueListQuery, total: number): string | null {
  const start = (q.page - 1) * q.perPage;
  const hasNext = start + q.perPage < total;
  const hasPrev = q.page > 1;
  if (!hasNext && !hasPrev) return null;
  const base = `http://${host}${reqPath}`;
  const qp = new URLSearchParams(q.rawQs);
  const links: string[] = [];
  if (hasNext) {
    qp.set('page', String(q.page + 1));
    qp.set('per_page', String(q.perPage));
    links.push(`<${base}?${qp.toString()}>; rel="next"`);
  }
  if (hasPrev) {
    qp.set('page', String(q.page - 1));
    links.push(`<${base}?${qp.toString()}>; rel="prev"`);
  }
  return links.join(', ');
}

/**
 * O(pageSize) issue list builder + per-repo split-version cache.
 * Slices directly from openIssues/closedIssues/allIssues and assembles JSON
 * array via Buffer.concat([B_OPEN, buf0, B_COMMA, ..., B_CLOSE_NL]) without
 * calling JSON.stringify(array).
 */
function getIssueListCached(repo: Repo, q: IssueListQuery, host: string, reqPath: string): IssueListCacheEntry {
  const cacheKey = `${q.state}|${q.direction}|${q.labels}|${q.page}|${q.perPage}|${host}|${reqPath}`;
  const hit = repo.issueListCache.get(cacheKey);
  if (hit !== undefined) return hit;

  let src: Issue[];
  if (q.state === 'open') src = repo.openIssues;
  else if (q.state === 'closed') src = repo.closedIssues;
  else if (q.state === 'all') src = repo.allIssues;
  else src = [];

  if (q.labels !== '') {
    const wanted = q.labels.split(',').filter((s) => s.length > 0);
    if (wanted.length > 0) {
      const filtered: Issue[] = [];
      for (let i = 0; i < src.length; i++) {
        const iss = src[i];
        let ok = true;
        for (let j = 0; j < wanted.length; j++) {
          if (!iss.labels.includes(wanted[j])) { ok = false; break; }
        }
        if (ok) filtered.push(iss);
      }
      src = filtered;
    }
  }

  const total = src.length;
  const start = (q.page - 1) * q.perPage;
  const count = start >= total ? 0 : Math.min(q.perPage, total - start);
  let buf: Buffer;
  if (count === 0) {
    buf = B_EMPTY_ARR_NL;
  } else {
    const asc = q.direction === 'asc';
    const parts: Buffer[] = new Array(count * 2 + 1);
    parts[0] = B_OPEN;
    let totalBytes = 3; // '[' + ']\n'
    let pIdx = 1;
    for (let i = 0; i < count; i++) {
      const iss = asc ? src[start + i] : src[total - 1 - (start + i)];
      const full = issueJsonBuf(repo, iss);
      // Zero-copy slice stripping trailing '\n'
      const itemSlice = full.subarray(0, full.length - 1);
      if (i > 0) {
        parts[pIdx++] = B_COMMA;
        totalBytes += 1;
      }
      parts[pIdx++] = itemSlice;
      totalBytes += itemSlice.length;
    }
    parts[pIdx] = B_CLOSE_NL;
    buf = Buffer.concat(parts, totalBytes);
  }

  const link = buildIssueListLink(host, reqPath, q, total);
  const etag = `"list-v${repo.issuesVersion}"`;
  const entry: IssueListCacheEntry = { buf, link, etag };
  if (repo.issueListCache.size >= 64) repo.issueListCache.clear();
  repo.issueListCache.set(cacheKey, entry);
  return entry;
}
function commentShape(repo: Repo, c: Comment): J {
  return {
    id: c.id, body: c.body, user: VIEWER_SHAPE, created_at: FIXED_ISO, updated_at: FIXED_ISO,
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
    head: { ref: pull.headRef, sha: headSha, label: `${repo.owner}:${pull.headRef}`, user: VIEWER_SHAPE },
    base: { ref: pull.baseRef, sha: baseSha, label: `${repo.owner}:${pull.baseRef}`, user: VIEWER_SHAPE },
    user: VIEWER_SHAPE, assignee: null, assignees: [], requested_reviewers: [],
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
    author: VIEWER_SHAPE, committer: VIEWER_SHAPE,
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
    sendJson(res, 200, VIEWER_SHAPE);
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
      for (const iss of repo.allIssues) invalidateIssue(repo, iss);
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
    if (method === 'GET' || method === 'HEAD') {
      const listEtag = `"list-v${repo.issuesVersion}"`;
      if (etagMatches(req.headers['if-none-match'], listEtag)) {
        sendNotModified(res, listEtag);
        return true;
      }
      const rawUrl = req.url ?? '';
      const qi = rawUrl.indexOf('?');
      const iq = parseIssueListQuery(qi >= 0 ? rawUrl.slice(qi + 1) : '');
      const entry = getIssueListCached(repo, iq, req.headers.host ?? '127.0.0.1', path);
      sendJsonBufFast(res, 200, entry.buf, entry.etag, entry.link, method === 'HEAD');
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
      const issue = createIssueRecord(repo, title, typeof b.body === 'string' ? b.body : '', labelNames);
      sendJsonBufFast(res, 201, issueJsonBuf(repo, issue), issue.etag, null, false);
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
          invalidateIssue(repo, issue);
          sendJson(res, 201, commentShape(repo, comment));
          return true;
        }
      }
      if (sub === '') {
        if (!issue) { sendJson(res, 404, { message: 'Not Found' }); return true; }
        if (method === 'GET' || method === 'HEAD') {
          if (etagMatches(req.headers['if-none-match'], issue.etag)) {
            sendNotModified(res, issue.etag);
            return true;
          }
          sendJsonBufFast(res, 200, issueJsonBuf(repo, issue), issue.etag, null, method === 'HEAD');
          return true;
        }
        if (method === 'PATCH') {
          const prevState = issue.state;
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
          invalidateIssue(repo, issue, prevState);
          sendJsonBufFast(res, 200, issueJsonBuf(repo, issue), issue.etag, null, false);
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
    const issue = createIssueRecord(repo, title, typeof input.body === 'string' ? input.body : '', []);
    return { __typename: 'CreateIssuePayload', issue: issueGql(repo, issue) };
  });
  defResolver('Mutation', 'closeIssue', (_p, args, ctx) => {
    const input = (args.input ?? {}) as Record<string, unknown>;
    const dec = decodeGlobalId(String(input.issueId ?? ''));
    const repo = dec?.kind === 'Issue' ? reposById.get(Number(dec.parts[0])) : undefined;
    const issue = repo?.issues.get(Number(dec?.parts[1] ?? -1));
    if (!repo || !issue) { ctx.errors.push({ message: 'Issue not found' }); return { __typename: 'CloseIssuePayload', issue: null }; }
    const prevState = issue.state;
    issue.state = 'closed';
    invalidateIssue(repo, issue, prevState);
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
    invalidateIssue(repo, issue);
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
    const bodyText = typeof mcpPick(args, ['body', 'description', 'content']) === 'string' ? String(mcpPick(args, ['body', 'description', 'content'])) : '';
    const issue = createIssueRecord(repo, title, bodyText, labelNames);
    return mcpToolResult(issueShape(repo, issue));
  }
  if (name === 'list_issues') {
    const { owner, name: repoName } = mcpRepoFromArgs(args);
    const missing = need(owner, 'owner') ?? need(repoName, 'repo');
    if (missing) return mcpToolError(`missing required argument: ${missing}`);
    const repo = getRepo(owner, repoName);
    if (!repo) return mcpToolError('Not Found');
    const state = String(mcpPick(args, ['state']) ?? 'open');
    const src = state === 'open' ? repo.openIssues : state === 'closed' ? repo.closedIssues : state === 'all' ? repo.allIssues : [];
    const issues: J[] = new Array(src.length);
    for (let i = 0; i < src.length; i++) issues[i] = issueShape(repo, src[src.length - 1 - i]);
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
