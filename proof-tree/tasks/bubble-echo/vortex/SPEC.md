# Vortex Echo v1: the integer engine (core/ve_core.c -> core/ve_core.wasm)

Status: UNPROVED. This file describes the integer kernels; the proofs live in `proofs/` and `evidence/` (helper P).
Source of the behaviour: the Phase 1 JS prototype `web/v1/vortex.js` of the Vortex Echo v1 lane (sha256 eb65a774...,
`/Users/boxer/lanes/vortex-echo-v1-20261019/web/v1/`), ported to integer-only C with the same constants and structure.
Exact trajectories differ from the float JS (section 8 lists every difference).

## 1. Reversibility by construction

The canonical state is the header, the vortex pair (VA, VB), the rim pair (RA, RB), the jiggle ring (JQ, JP), the
corrugation ring (ZQ, ZP) and the droplet records (DI). Every export that changes canonical state is one half of a
forward/backward pair of one of these shapes (all arithmetic on 32-bit words is modulo 2^32):

| shape | forward | backward |
|---|---|---|
| Fredkin | D := F(model, B); (A, B) := (B, A + D) | D := F(model, A); (A, B) := (B - D, A) |
| kick | K := G(Q, r, ...); P := P + K | K := G(Q, r, ...); P := P - K |
| drift | Q := Q + f(P, r) | Q := Q - f(P, r) |
| LIFO births | push records (each with what it took from its parent); parent -= taken | pop records born now; parent += taken; zero them |

F and G are pure functions of their arguments; the backward half recomputes the same rounded integer from the same
inputs (the Fredkin backward reads the old B, which the forward moved into A), so each pair is an exact inverse
whatever F and G compute. F, G and f write only scratch (section 2), never the words they read.

## 2. Fixed memory layout (32 pages = 2 MiB, initial = max; byte offsets)

| region | offset | size | contents |
|---|---|---|---|
| shadow stack | 0x000000 | 16 KiB | linker stack, never used (no export touches globals) |
| HDR | 0x004000 | 256 B | canonical header (64 words, below) |
| MODEL | 0x004100 | 4 KiB | model words (host-written, constant) |
| TBL | 0x010000 | 1 MiB | speed table SPD[2048][128] int32 (host-written at or before the puncture, constant after) |
| VA, VB | 0x110000, 0x112000 | 8 KiB each | vortex pair, int32 [3N] (N <= 640), 2^23 per unit-sphere radius |
| RA, RB | 0x114000, 0x116000 | 8 KiB each | rim geodesic radius per bead, int32 [2048], 2^24 per rad |
| JQ, JP | 0x118000, 0x11A000 | 8 KiB each | jiggle displacement and rate, int32 [2048] |
| ZQ, ZP | 0x11C000, 0x11E000 | 8 KiB each | corrugation height (2^24 per bubble radius) and rate, int32 [2048] |
| DI | 0x120000 | 768 KiB | droplet records, int32 [16384][12] |
| scratch | 0x1E0000 .. 0x1F2000 | | XN 0x1E0000 int32[3N] (Q30 unit vectors), VD 0x1E2000 int32[3N], VACC 0x1E4000 int64[3N], RD 0x1E8000 int32[2048], KZ 0x1EA000 int32[2048], LAP 0x1EC000 int64[2048], KJ 0x1F0000 int32[2048] |

Canonical = every byte below 0x1E0000 (header, model, table, state); scratch is not canonical and is not compared by
the reversal checks (the native = WASM check compares all 2 MiB).

Header words (u32): 0 magic `VE1S` (0x53314556), 1 version (1), 2 tick T, 3 puncture tick P (0xFFFFFFFF = not
punctured), 4 nd (live droplet records), 5 healErr, 6-8 puncture direction popC (int32, 2^23), 9-11 C, 12-14 E1,
15-17 E2 (puncture frame, Q30), 18-23 jiggle phases JPH_i (u32 turns), 24-29 jiggle amplitudes JA_i (Q16), 30-63 zero.

Model words: 0 magic `VE1M` (0x4D314556), 1 N (1..640), 2 ZSEED (vortex.js `0x5EED + 977 seed`), 3 flags (bit 0:
jiggle ring on), 4-15 zero, 16+j circulation word CW_j = round(G4_j KV 2^20) for j < N with |CW_j| <= 2^28
(KV = 2 dt_s 2^23, dt_s = (1/60)/16; G4_j = Gamma_j / (4 pi) as vortex.js), zero for N <= j < 640, rest zero.
`ve_validate` returns 0 iff these hold.

Droplet record (12 int32): px py pz (2^20 per bubble radius), vx vy vz (per tick), birth tick, kind << 16 | parent
bead, dz, deta, 0, 0. Kinds: 0 pinch-off, 1 spray, 2 antipode burst.

Speed table: SPD[k][j] = round(2 V(k, r_j) 2^24) with V = V0 sqrt(HREF / max(HMIN, h)) the Taylor-Culick speed
(rad/tick, V0 = pi/250, HREF = 420 nm, HMIN = 140 nm) at the rim point of bead k at radius r_j = j 2^-5 rad
(j < 128), h the thickness map frozen at the puncture. The kernels read it through `spd(k, r)`: linear interpolation
on the grid in integers (index r >> 19, weight r & (2^19 - 1), rounded), clamped to the last interval and to >= 1.

## 3. Exports and their HOL-facing contracts

All exports are call-free (helpers are `always_inline`), integer-only, and use only the Hearth `wasm` profile subset
(`core/ve_wasm_check.py`). "Writes only X" lists the canonical words written; scratch writes are listed separately.
Below, n = min(N, 640), M = 2048, idx k-1 and k+1 are taken modulo M, nd' = min(nd, 16384).

- `ve_version`, `ve_hdr_ptr`, `ve_model_ptr`, `ve_table_ptr`, `ve_state_ptr` (VA), `ve_scratch_ptr`: constants.
- `ve_validate() -> u32`: model check (section 2). `ve_init() -> u32`: validate; header := (magic, 1, T = 0,
  P = none, zeros); RA .. DI := 0. VA and the model are written by the host before.
- `ve_vort_init()`: careful first step (vortex.js vortexInit): VB := VA + rsh(VK(VA), 2), then
  VB := VA + rsh(VK(VB), 1).
- `ve_vort_apply()`: for m < 3n: VB'[m] = VA[m] + VK(model, VB)[m], VA'[m] = VB[m]. Writes only VA, VB (scratch
  XN, VACC, VD). VK is a pure function of the model words (N, CW) and VB.
  `ve_vort_unapply()`: for m < 3n: VA'[m] = VB[m] - VK(model, VA)[m], VB'[m] = VA[m]. So unapply . apply = id.
  Body: phase 1 normalises the source (VB resp. VA) into XN, phase 2 accumulates the field from XN and CW into VACC
  and rounds it into VD (the same code with the same addresses in both exports), then after a compiler barrier the
  plain loop `t = B[m]; B[m] = A[m] + VD[m]; A[m] = t` (resp. `t = A[m]; A[m] = B[m] - VD[m]; B[m] = t`).
  In the shipped module the two bodies have the same 736 opcodes and differ in 15 lines only: the three source loads
  of the normalisation loop (base 0x112000 vs 0x110000) and the Fredkin loop (`core/controls/find_op.py` listings
  diffed); the field phase is opcode-identical. Likewise rim apply/unapply differ in 7 of 122 opcode lines, corr
  kick/unkick in 4 of 683 (the add/sub of the last loop), jig kick/unkick in 4 of 877, corr drift/undrift in 2 of 64.
- `ve_drop_apply()`: for i < nd': vy -= 1; px += vx; py += vy; pz += vz (in this order, so the drift uses the kicked
  vy). `ve_drop_unapply()`: for i < nd': px -= vx; py -= vy; pz -= vz; vy += 1. Writes only DI[0 .. 12 nd').
- `ve_birth_apply() -> nd`: at tick T, appends records with birth = T + 1 at slots nd', nd'+1, ... (while < 16384)
  in three passes over k = 0 .. M-1 (pinch-off, spray, antipode; section 6), subtracting (dz, deta) of each
  pinch-off record from (ZQ[k], ZP[k]) right after pushing it; writes nd. Writes only DI[12 nd' ..], ZQ, ZP, nd.
  `ve_birth_unapply() -> count`: while nd > 0 and DI[nd-1].birth = T + 1: nd -= 1; if kind = 0:
  ZQ[parent] += dz, ZP[parent] += deta; the record's 12 words := 0. Writes only DI, ZQ, ZP, nd.
  Inverse under the invariants (both hold for every state the host reaches from `ve_init`): records at slots
  >= nd are zero, and every live record has birth <= T. Then unapply . apply = id (LIFO: each pop undoes the last
  push, in reverse order, and the records born at T + 1 are exactly the ones apply pushed).
- `ve_rim_apply()`: for k < M: RB'[k] = RA[k] + RD(k, RB[k]), RA'[k] = RB[k], with RD(k, r) = 0 if r >= pi - 0.02
  else spd(k, r) (= round(2 V 2^24): the Fredkin displacement 2 dt V). Writes only RA, RB (scratch RD).
  `ve_rim_unapply()`: RA'[k] = RB[k] - RD(k, RA[k]), RB'[k] = RA[k].
- `ve_corr_kick(sub)`: for k < M: ZP'[k] = ZP[k] + KZ(ZQ, RB, table, ZSEED, T - P, sub)[k]; `ve_corr_unkick(sub)`:
  ZP'[k] = ZP[k] - the same KZ. Writes only ZP (scratch LAP, KZ). KZ reads ZQ, RB, the table, the model word ZSEED,
  header T, P and sub, never ZP.
- `ve_corr_drift()`: for k < M with RB[k] < pi - 0.02: ZQ[k] += (ZP[k] + 2) >> 2 (= round(ZP / 4), arithmetic
  shift, computed in i64); `ve_corr_undrift()`: ZQ[k] -= the same. Writes only ZQ.
- `ve_jig_kick()` / `ve_jig_unkick()`: if model flag bit 0: JP[k] +=/-= KJ(JQ, RB, table, header T, P, JPH, JA)[k].
  Writes only JP (scratch KJ). `ve_jig_drift()` / `ve_jig_undrift()`: if flag: JQ[k] +=/-= JP[k] for all k.
- `ve_puncture(cx, cy, cz) -> u32`: if P = none and the direction is nonzero: P := T; popC := (cx, cy, cz); frame
  C = norm(popC), E1 = norm(up x C) (up = (0,1,0) if |C_y| < 0.95 else (1,0,0)), E2 = C x E1 (Q30); jiggle drive
  from mulberry(cx ^ 7 cy ^ 13 cz) exactly as vortex.js (JPH_i = raw u32, JA_i = 0.6 + 0.8 rnd in Q16);
  RA[k] := r0, RB[k] := r0 + rsh(spd(k, r0), 1) (r0 = round(0.015 2^24)); JQ, JP, ZQ := 0;
  ZP[k] := round(3e-7 2^24 (hash2(k, ZSEED) - 0.5)); DI := 0; nd := 0. Returns 0 (1 if already punctured, 2 if
  zero direction). The host writes the table first.
- `ve_unpuncture() -> bad`: bad = nd + #{pop words that differ from their post-puncture value (RA, RB, JQ, JP, ZQ,
  ZP)}; healErr += bad; then P := none, header words 6-29 := 0, RA .. ZP := 0, DI := 0, nd := 0. A pop that does not
  reverse exactly therefore shows in the canonical bytes at tick 0 (vortex.js healErr).
- `ve_tick_inc()` / `ve_tick_dec()`: T := T + 1 / T - 1.

## 4. Host step order and the swirl clock

Constants: QSUB = 16 vortex substeps per swirl tick, PSUB = 1 per pop tick (the swirl clock 1/16 of vortex.js; the
vortex dt never changes), NS = 4 corrugation substeps per tick.

Forward from tick T (header T):
- swirl tick (P = none or T < P): QSUB x `ve_vort_apply`; `ve_tick_inc`; then, if not punctured and the host's
  puncture event is at the new tick: write the table, `ve_puncture(c)`.
- pop tick (T >= P): `ve_rim_apply`; `ve_jig_kick`; `ve_jig_drift`; for sub = 0 .. 3: `ve_corr_kick(sub)`,
  `ve_corr_drift`; `ve_drop_apply`; `ve_birth_apply`; PSUB x `ve_vort_apply`; `ve_tick_inc`.

Backward from tick T + 1:
- if P = T + 1: `ve_unpuncture` (the un-puncture check), then the swirl branch;
- `ve_tick_dec` (header T is now the tick of the forward step being undone);
- pop tick (T >= P): PSUB x `ve_vort_unapply`; `ve_birth_unapply`; `ve_drop_unapply`; for sub = 3 .. 0:
  `ve_corr_undrift`, `ve_corr_unkick(sub)`; `ve_jig_undrift`; `ve_jig_unkick`; `ve_rim_unapply`;
- swirl tick: QSUB x `ve_vort_unapply`.

Every forward leaf runs with header T equal to the tick being stepped, and so does its backward partner, so the
tick-dependent kicks (corrugation noise hash, jiggle drive) and the birth tick agree. The whole tick is the
composition of the pairs in this order; its inverse is the composition of the inverses in reverse order.
The vortex tracers of vortex.js (a GPU pass) are not part of this module.

## 5. Integer formulas

Rounding: rsh(a, s) = (a + 2^(s-1)) >> s (arithmetic shift, round half up = JS Math.round). Products in i64.
Every division has a denominator >= 1 by construction (clamps noted), so no export can trap on any memory content.

### 5.1 Vortex field VK (one substep, dt_s = (1/60)/16)
- XN[i] = trunc(2^30 S[i] / L_i) componentwise, L_i = max(1, isqrt(|S[i]|^2)) (isqrt: 32-round bitwise floor sqrt
  on u64), so |XN| <= 2^30 per component.
- For i != j: dot = (x_i . x_j) >> 30; den = max(D2, 2^30 + D2 - dot) with D2 = round(0.0025 2^30) = 2684355;
  w = 2^54 / den (Q24); g_j = (CW_j w) >> 20; cr = (x_j x x_i) (exact Q60) >> 36 (Q24) per component.
- VK(S)[3i+c] = rsh( sum_{j != i, j < n} ((g_j cr_c) >> 12), 36 ) as int32 (mod 2^32).
  This is round(2 dt_s 2^23 u_i) with u_i = sum_j G4_j (x_j x x_i) / (1 - x_i . x_j + delta^2), the regularised
  spherical Biot-Savart velocity of vortex.js, in fixed point. The code runs the pair loop (i < j) and computes each
  ordered term exactly as the double sum does (it negates the exact Q60 cross product before the shift), so the
  result equals the double sum bit for bit; integer sums are order independent.

### 5.2 Rim: RD(k, r) = 0 for r >= RIM_STOP = round((pi - 0.02) 2^24), else spd(k, r).

### 5.3 Droplets: gravity GD = 1 (2^-20 bubble radius per tick^2) along -y.

### 5.4 Births (tick T, birth = T + 1; all hashes are vortex.js hash2 as u32, compared against integer thresholds)
Per bead geometry from the frame: ck, sk = cos, sin(2 pi k / 2048), cr, sr = cos, sin(r) (integer sine: quadrant
fold and Taylor series to x^13 in Q30), d = ck E1 + sk E2, n = cr C + sr d (rim point), t = cr d - sr C (d n / dr),
e = ck E2 - sk E1 (along the rim); all Q30. q = spd / KQ with KQ = 2 V0 2^24 = 421657 (so V = V0 q, V in droplet
units = spd / 32 per tick, h / HREF = 1 / q^2).
1. Pinch-off (kind 0): bead k with 0.2 <= r <= pi - 0.15 (r = RB[k]), z = ZQ[k] > ZQ[k-1], z >= ZQ[k+1] and
   z >= zp(k) where zp(k) = 2^24 0.08 (0.45 + 1.6 hash2(k, ZSEED + 1)^2) / q. Drop at the ligament tip
   n (1 + tube) + (z / 2^24) (a0 + a1) / 2 with a0 = norm(n - b0 t + sp e), a1 = norm(n - b1 t + 1.6 sp e),
   sp = 0.35 (h9 - 0.5), b0 = 0.18 (0.5 + h10), b1 = 0.75 (0.6 + 0.8 h11) (h_m = hash2(k, ZSEED + m) / 2^32),
   tube = 0.0030 + 0.0055 sqrt(min(1.5, r / 1.2) min(2.5, 1 / q^2)); velocity 0.88 V t + (0.9 max(0, ZP / 2^24) +
   0.10 V) a1 + 0.14 V j1 e + 0.06 V j2 n with j1, j2 = hash2(k + 4096 birth, ZSEED + 2 / + 3) / 2^32 - 0.5;
   dz = rsh(0.3 z) (0.3 as 19661 / 2^16), deta = max(0, ZP[k]).
2. Spray (kind 1): 0.25 <= r <= pi - 0.2 and hash2(k ^ 3 ZSEED, birth) < floor(12.2231 spd) (= 0.0012 q 2^32);
   drop at n (1 + tube), velocity (0.85 + 0.15 j2) V t + (0.15 + 0.35 j2) V n + 0.25 V j1 e with
   j1 = hash2(k, birth + 77777) / 2^32 - 0.5, j2 = hash2(birth, k + 31337) / 2^32; dz = deta = 0.
3. Antipode (kind 2): RA[k] < pi - 0.10 <= RB[k] and hash2(k, ZSEED + 5) <= 2576980377 (= hash <= 0.6);
   V = max(spd(k, RB[k]), KQ / 2) / 32; drop at n, velocity (0.25 + 0.9 h6^2) V (-C) + 0.55 V ((h7 - 0.5) e +
   (h8 - 0.5) t); dz = deta = 0.
Positions are rounded to 2^20 per radius, velocities to 2^20 per radius per tick.

### 5.5 Corrugation kick KZ (substep sub; tt = T - P)
With sigma(r) = 1 / max(sin r, 0.35)^2 (Q16), on(r) = smooth(r, 0.10, 0.30) (1 - smooth(r, pi - 0.30, pi - 0.10))
(Q16 smoothstep), DQ_k = ZQ[k+1] - 2 ZQ[k] + ZQ[k-1], LAP_k = (sigma(RB[k]) DQ_k) >> 12 for every k, and for an
active bead (0.10 <= r < pi - 0.02, r = RB[k]):
- F = -(cA q on sigma) DQ_k - (cB (on / q) sigma) (LAP_{k+1} - 2 LAP_k + LAP_{k-1}) (Q16 in the code), with
  cA = (4/3) g V0^2 / (ks0 ds0^2) = 0.0853377, cB = (2/3) g V0^2 / (ks0^3 ds0^4) = 0.1030849, g = 0.8,
  ks0 = 2 pi / (0.85 1.72e-3 sqrt(420)) = 209.70, ds0 = 2 pi / 2048. (These are vortex.js ZA DS2 and ZB DS2^2 with
  the dependence on the thickness written through q: ZA = (4/3) g V0^2 q on / ks0, ZB = (2/3) g V0^2 on / (ks0^3 q).)
- a = 0.2 spd^2 / 2^24 (= g V^2 2^24, exactly, because 2^24 = SZ = SR); F := clamp(F, -0.35 a, hi) with hi = 0 if
  5 ZQ[k] > 8 zp(k) (above 1.6 zp) else 0.5 a; F += 0.002 a (hash2(k ^ ZSEED, 8 tt + sub) / 2^32 - 0.5);
- KZ_k = round(F / 4); inactive beads KZ_k = 0.

### 5.6 Jiggle kick KJ (tt = T - P), beads with RB[k] < pi - 0.02 (else 0)
KJ_k = round(-JW2 JQ_k - 0.05 (2 JQ_k - JQ_{k-1} - JQ_{k+1}) + 2.5e-6 2^24 q F_k), F_k = sum_i JA_i
sin(2 pi (JM_i k / 2048) + JW_i tt + JPH_i), JM = 23, 37, 52, 66, 81, 97, JW2 = (2 pi / 36)^2,
JW_i = sqrt(JW2 + 0.2 sin^2(pi JM_i / 2048)) (compile-time constants as u32 turns per tick).

## 6. Constants
2^24 per rad: RIM_STOP 52371634 (pi - 0.02), ON0 1677722 (0.10), OFF0 47674014 (pi - 0.30), smoothstep width
3355443 (0.2), pinch band 3355443 .. 50190596, spray band 4194304 .. 49351735, antipode 51029457 (pi - 0.10),
r0 251658 (0.015). Q-format constants: D2 2684355 (Q30), CAK 56966666 (cA / KQ, Q48), CBK8 11127432 (cB KQ, Q8),
JW2 130832186 (Q32), JKAP 214748365 (Q32), JG 427228 (2.5e-6 2^24 / KQ, Q32), seed 329853 (3e-7 2^24, Q16),
zp base 1342177 (0.08 2^24), spray 801053 (0.0012 2^32 / KQ, Q16), KQ^2 2^16 = 11651972255721782.

## 7. Build and checks

- `PY=<python with ziglang 0.17.0> core/build.sh [OUTDIR]`: zig cc wasm32-freestanding, -mcpu=mvp, -O2, -fwrapv,
  -nostdlib, -fno-builtin, 32 fixed pages, --strip-all; writes `core/SHA256SUMS`. On bluestar26 the toolchain python
  is `~/twins-lanes/wasm-sprint-20261016/B/tc-venv/bin/python` (ziglang 0.17.0 and wasmtime 49).
- `python3 core/ve_wasm_check.py core/ve_core.wasm`: the Hearth `wasm` profile subset checks of
  `core/wasm_check.py` for this export list and 32 pages.
- Native: `cc -O2 -fwrapv -o ve_run core/ve_run.c -lm` (the harness includes ve_core.c with -DVE_NATIVE).
- `core/ve_check.py`: native = WASM (whole 2 MiB memory byte for byte at several ticks, forward and backward) and the
  reversal tests (non-scratch bytes after N ticks forward and N back), native and WASM; timings.
- Negative control `core/controls/ve_core_unbirth_forget_deta.wasm` (sha256 in `core/controls/SHA256SUMS`), made by
  `core/controls/make_controls.py` from the shipped module: one byte, layout preserving. In `ve_birth_unapply` the
  give-back `ZP[parent] += deta` loads deta as record word 9 (`local.get o; i32.const 36; i32.add; i32.load`); the
  control changes the immediate 36 (0x24) to 40 (0x28), record word 10, which is always 0, so un-birth forgets the
  rate a pinch-off drop took (vortex.js `mutant=1`). It passes `ve_wasm_check.py` and FAILS the reversal
  (`ve_check.py --wasm core/controls/ve_core_unbirth_forget_deta.wasm --no-native --expect-fail`).
  `core/controls/find_op.py FILE EXPORT` lists an export's opcodes with file offsets.
- Tests: `python3 -m unittest discover -v -s tasks/bubble-echo/vortex/tests -p 'test_*.py'` from the repo root
  (with the toolchain python all 10 run; under a python without ziglang/wasmtime 4 skip).

Checks run (bluestar26, module 72fe0ba2): `ve_check.py` default (seeds 1-3, puncture at tick 30, 330 ticks, 11 dump
points) and `ve_check.py --seeds 1,2,3,4,5 --pop 540 --tend 1060 --dumps 0,540,541,800,1060` (the vortex.js demo
timeline, 9 dump points): every dump point native = WASM with 0 differing bytes of 2,097,152; every reversal 0
differing bytes of 1,966,080 and healErr 0, natively and in WASM; the control fails (healErr 4,096 end to end,
nonzero bytes mid-pop). Droplets born in the long run, seed 1: 2,748 pinch-off, 537 spray, 1,185 antipode
(vortex.js seed 1: 2,197, 542, 1,185; the antipode rule is a pure hash rule and matches exactly; pinch-off differs
with the synthetic thickness field and the integer details).

Proof target: `core/ve_core.wasm` sha256 72fe0ba28aed1a62c0cfb6912f3747c72845e09801ba3cc047a3c718f1f6ae29
(first committed in 37d1f2a4). A change to the module will be announced here with its new digest.

### Timings (module 72fe0ba2, seed 1 scene: 554 vortices)

| engine | one swirl tick (16 vortex substeps) | one vortex substep | pop tick without the substep |
|---|---|---|---|
| node 26 (V8, the browser's engine), Mac M5 Pro (`core/ve_time_node.mjs`) | 6.2 ms | 0.39 ms | 0.16 ms |
| wasmtime 49 (python), bluestar26 i7-10750H | 37 ms | 2.3 ms | 0.9 ms (incl. python call overhead) |
| native gcc -O2, bluestar26 | 40-48 ms | 2.3-3 ms | 0.6 ms |

The cost is the per-pair i64 division of the vortex field (153,181 pairs per substep): fast on Apple silicon, slow
on that Intel part. Two cheaper options, not taken because the browser target already runs a swirl tick in 6 ms and
the module is the proof target: (a) a reciprocal without division (clz normalisation plus three Newton steps in Q30)
or a 32-bit division at a coarser scale, inside phase 2 of the vortex exports only (the export shapes stay);
(b) fewer, larger substeps chosen when the model is built: e.g. 4 substeps of dt/4 per swirl tick with circulation
words built for dt_s = dt/4, and during the pop 1 substep every 4th pop tick (aligned with the tracer catch-up
stride), which keeps the 1/16 clock ratio at a quarter of the cost. The substep dt must stay fixed for the whole run
(a Fredkin pair cannot change dt), so (b) is a model choice, not a runtime switch.

## 8. Differences from vortex.js (faithfulness)

Same constants, same structure and step order; the float math inside the kicks is replaced by fixed point, so
trajectories are close to, not equal to, the JS ones.
- Vortex field: Q30 unit vectors, Q24 weights by i64 division, Q24 cross products; the JS normalises in float.
  Measured (`ve_check.py --vk-float`, test `test_vk_matches_float_formula`): on the same positions the integer VK
  equals Math.round(U KV) of the float formula except at rounding boundaries: seed 1, max |diff| 1 unit (2^-23
  radius), mean 0.010 per component, for displacements up to 7,608 units.
- Vortex init: mid and vb use VK / 4 and VK / 2 (VK = round(2 dt_s 2^23 u)) instead of rounding 0.5 dt_s 2^23 u and
  dt_s 2^23 u separately.
- Rim speed and every thickness-dependent coefficient read the table SPD (bead x radial grid of 2^-5 rad, linear
  interpolation) instead of bilinear lookups of the blurred lat-lon map at the exact rim point; the JS corrugation
  coefficients (ZA, ZB, ZAM, pinch length, ZV) are rewritten through q = V / V0 = spd / KQ (exact identities, then
  rounded).
- DS2 (1 / ds^2) is defined for every bead from its own radius; in the JS, beads outside the active band keep a stale
  DS2 from an earlier tick, which enters the bi-Laplacian of their active neighbours.
- sin/cos are an integer Taylor series (Q30); smoothstep in Q16; sqrt by the bitwise integer isqrt.
- Launch positions and velocities (births) are computed in Q30 / 2^20 integers; the constants 0.88, 0.9, ... are
  Q16. dz = round(0.3 z) uses 19661 / 2^16.
- The puncture frame is computed in integers from popC (isqrt normalisation); the jiggle frequencies are compile-time
  constants; the jiggle phases are the raw mulberry u32 outputs (the JS multiplies the float by 2 pi).
- Tracers (GPU) are out of scope.
- The table is a host input: the native harness `ve_run setup` builds it from a synthetic smooth thickness field
  (deterministic, seeded); the browser builds it from the thickness map read back at the puncture.
