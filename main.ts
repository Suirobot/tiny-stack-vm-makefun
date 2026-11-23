// Tiny stack VM for make.fun's tiny stack ISA v1: runs every program in the input set exactly as the
// reference VM does (same traps, exit codes, step and output limits) and writes stdout.bin + exit.txt.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [immediate bytes, pops, pushes] per opcode byte; -1 marks an unknown opcode.
const META: number[][] = [];
for (let i = 0; i < 256; i++) META.push([-1, 0, 0]);
const def = (b: number, imm: number, pops: number, pushes: number) => { META[b] = [imm, pops, pushes]; };
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); def(0x03, 0, 1, 0); def(0x04, 0, 1, 2);
def(0x05, 0, 2, 2); def(0x06, 0, 2, 3); def(0x07, 0, 3, 3);
def(0x10, 0, 2, 1); def(0x11, 0, 2, 1); def(0x12, 0, 2, 1); def(0x13, 0, 2, 1); def(0x14, 0, 2, 1);
def(0x15, 0, 2, 1); def(0x16, 0, 2, 1); def(0x17, 0, 1, 1); def(0x18, 0, 2, 1); def(0x19, 0, 2, 1);
def(0x1a, 0, 2, 1); def(0x1b, 0, 1, 1); def(0x1c, 0, 2, 1); def(0x1d, 0, 2, 1); def(0x1e, 0, 2, 1);
def(0x20, 0, 2, 1); def(0x21, 0, 2, 1); def(0x22, 0, 2, 1);
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0); def(0x33, 2, 0, 0); def(0x34, 0, 0, 0);
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0);
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0);

const enc = new TextEncoder();

function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; exit: number } {
  const n = prog.length;
  const D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const done = (exit: number) => ({ out: buf.slice(0, olen), exit });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const meta = META[op];
    if (meta[0] < 0) return done(5);
    const imm = meta[0];
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < meta[1]) return done(2);
    if (sp - meta[1] + meta[2] > 256) return done(3);
    pc = next;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return done(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return done(4); r = b === -1 ? 0 : a % b | 0; }
        else if (op === 0x15) { if (b === 0) return done(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return done(4); r = (a >>> 0) % (b >>> 0) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return done(7);
        C[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = C[--csp];
        break;
      case 0x40: {
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: {
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = enc.encode(String(D[sp - 1]));
        if (olen + bytes.length > 65536) return done(11);
        sp--;
        buf.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        buf[olen++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53: return done(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = readFileSync(join(I, id, 'program.bin'));
  let input: Uint8Array = new Uint8Array(0);
  try { input = readFileSync(join(I, id, 'input.bin')); } catch { /* no input file: empty input */ }
  const { out, exit } = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), String(exit) + '\n');
}
