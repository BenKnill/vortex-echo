/* ve_core.c: Vortex Echo v1 integer engine (tasks/bubble-echo/vortex/SPEC.md).  UNPROVED.
 *
 * Integer-only port of the Phase 1 dynamics (web/v1/vortex.js of the Vortex Echo v1 lane): the point-vortex
 * Fredkin leapfrog on the unit sphere, and the pop (Taylor-Culick rim as a Fredkin pair, Rayleigh-Taylor
 * corrugation ring and in-plane jiggle ring as kick-drift pairs, droplet kick-drift, and LIFO droplet births).
 * Every export that changes canonical state is one half of a forward/backward pair:
 *   - Fredkin pairs (vortices, rim): apply computes D = F(model, B) into scratch, then (A, B) <- (B, A + D);
 *     unapply computes D = F(model, A) into scratch, then (A, B) <- (B - D, A).
 *   - kick pairs (corrugation, jiggle): compute K from the positions (which the kick never writes) into scratch,
 *     then P += K (kick) or P -= K (unkick).
 *   - drift pairs and the droplet pair: Q += f(P) / Q -= f(P), elementwise.
 *   - births: apply pushes records (with what each took from its parent crest) on a LIFO stack; unapply pops
 *     every record born at this tick and gives the parent its (dz, deta) back.
 * The host runs the step order of SPEC.md section 4 (forward: rim, jiggle, corrugation 4 x (kick, drift),
 * droplets, births, vortex substeps; backward exactly reversed).
 *
 * Build: core/build.sh (zig 0.17.0 cc, wasm32-freestanding, -mcpu=mvp, -O2, -fwrapv, fixed 32 pages).
 * Native: -DVE_NATIVE (core/ve_run.c includes this file).  Exported bodies are call-free (helpers always_inline),
 * integer only (i64 products, divisions only by values proved nonzero), no data segment (no constant arrays).
 */
#include <stdint.h>

typedef uint32_t u32;
typedef uint64_t u64;
typedef int64_t i64;
typedef int32_t i32;

#define INL static inline __attribute__((always_inline))
#ifdef VE_NATIVE
#define EXPORT(name)
#else
#define EXPORT(name) __attribute__((export_name(name)))
#endif
/* compiler barrier (no instruction): the Fredkin / kick loops after it reload their pointers and bounds and keep
 * their plain load/compute/store form (SPEC.md section 5) */
#define BARRIER __asm__ __volatile__("" ::: "memory")

/* Mutation hook for the negative control (core/controls, tests): the operator with which ve_birth_unapply gives a
 * pinch-off parent its rate back (shipped: +; control: -). */
#ifndef VE_UNBIRTH_DE_OP
#define VE_UNBIRTH_DE_OP +
#endif

#define VE_VERSION   1u
#define VE_MAGIC_S   0x53314556u        /* "VE1S" read LE: header word 0 */
#define VE_MAGIC_M   0x4D314556u        /* "VE1M" read LE: model word 0 */
#define NV_MAX       640u               /* vortices */
#define NB           2048u              /* rim beads */
#define BMASK        2047u
#define DMAX         16384u             /* droplet slots */
#define REC          12u                /* int32 words per droplet record */
#define JR           128u               /* radial grid points per bead in the speed table */
#define JSH          19u                /* radial grid spacing 2^19 (2^-5 rad at 2^24 per rad) */
#define PNONE        0xFFFFFFFFu        /* puncture tick when not punctured */
#define GD           1u                 /* droplet gravity kick per tick (SD units) */

/* ---- fixed memory layout (byte offsets; SPEC.md section 2) ---- */
#define HDR_OFF   0x004000u             /* 256 B canonical header */
#define MODEL_OFF 0x004100u             /* 4 KiB model words (host-written, constant) */
#define TBL_OFF   0x010000u             /* 1 MiB speed table SPD[NB][JR] (host-written at/before the puncture) */
#define VA_OFF    0x110000u             /* canonical state: int32 [3 NV_MAX] each region padded to 8 KiB */
#define VB_OFF    0x112000u
#define RA_OFF    0x114000u             /* int32 [NB] rim geodesic radius, 2^24 per rad */
#define RB_OFF    0x116000u
#define JQ_OFF    0x118000u             /* int32 [NB] jiggle displacement */
#define JP_OFF    0x11A000u             /* int32 [NB] jiggle rate */
#define ZQ_OFF    0x11C000u             /* int32 [NB] corrugation height, 2^24 per bubble radius */
#define ZP_OFF    0x11E000u             /* int32 [NB] corrugation rate */
#define DI_OFF    0x120000u             /* int32 [DMAX][REC] droplet records */
#define SCR_OFF   0x1E0000u             /* scratch (not canonical) */
#define XN_OFF    0x1E0000u             /* int32 [3 NV_MAX] normalised vortex positions, Q30 */
#define VD_OFF    0x1E2000u             /* int32 [3 NV_MAX] vortex displacement D */
#define VACC_OFF  0x1E4000u             /* int64 [3 NV_MAX] field accumulators */
#define RD_OFF    0x1E8000u             /* int32 [NB] rim displacement D */
#define KZ_OFF    0x1EA000u             /* int32 [NB] corrugation kick K */
#define LAP_OFF   0x1EC000u             /* int64 [NB] sigma-weighted second differences of ZQ */
#define KJ_OFF    0x1F0000u             /* int32 [NB] jiggle kick K */
#define MEM_END   0x200000u             /* 32 pages */

#ifdef VE_NATIVE
static unsigned char ve_mem[MEM_END] __attribute__((aligned(64)));
#define MEMBASE ((uintptr_t)ve_mem)
unsigned char *ve_native_mem(void) { return ve_mem; }
#else
#define MEMBASE ((uintptr_t)0)
#endif
#define W32(off) ((u32 *)(MEMBASE + (off)))
#define W64(off) ((i64 *)(MEMBASE + (off)))
#define HDR   W32(HDR_OFF)
#define MODEL W32(MODEL_OFF)
#define TBL   W32(TBL_OFF)
#define VA    W32(VA_OFF)
#define VB    W32(VB_OFF)
#define RA    W32(RA_OFF)
#define RB    W32(RB_OFF)
#define JQ    W32(JQ_OFF)
#define JP    W32(JP_OFF)
#define ZQ    W32(ZQ_OFF)
#define ZP    W32(ZP_OFF)
#define DI    W32(DI_OFF)
#define XN    W32(XN_OFF)
#define VD    W32(VD_OFF)
#define VACC  W64(VACC_OFF)
#define RD    W32(RD_OFF)
#define KZ    W32(KZ_OFF)
#define LAP   W64(LAP_OFF)
#define KJ    W32(KJ_OFF)

/* model words */
#define M_N        MODEL[1]             /* vortex count, 1 .. 640 */
#define M_ZSEED    MODEL[2]             /* pop hash seed (vortex.js ZSEED = 0x5EED + 977 seed) */
#define M_FLAGS    MODEL[3]             /* bit 0: jiggle ring on */
#define M_CW(j)    MODEL[16u + (j)]     /* vortex j circulation word: round(G4[j] * KV * 2^20), |.| <= 2^28 */

/* header words */
#define H_T        HDR[2]               /* tick */
#define H_P        HDR[3]               /* puncture tick, PNONE before the puncture */
#define H_ND       HDR[4]               /* live droplet records */
#define H_HEAL     HDR[5]               /* un-puncture mismatch count (vortex.js healErr) */
#define H_POPC(a)  HDR[6u + (a)]        /* puncture direction, int32 2^23 */
#define H_C(a)     HDR[9u + (a)]        /* puncture frame: C, E1, E2 (Q30 unit vectors) */
#define H_E1(a)    HDR[12u + (a)]
#define H_E2(a)    HDR[15u + (a)]
#define H_JPH(i)   HDR[18u + (i)]       /* jiggle drive phases (u32 turns) */
#define H_JA(i)    HDR[24u + (i)]       /* jiggle drive amplitudes (Q16) */

/* ---- constants (radii in 2^24 per rad; see SPEC.md section 6 for the formulas) ---- */
#define ONE30     ((i64)1 << 30)
#define D2_30     2684355               /* Biot-Savart regularisation delta^2 = 0.0025, Q30 */
#define W_NUM     ((i64)1 << 54)        /* weight w = 2^54 / den (den Q30) is Q24 */
#define RIM_STOP  52371634              /* pi - 0.02 */
#define ON0       1677722               /* 0.10: corrugation on (start of the smoothstep) */
#define OFF0      47674014              /* pi - 0.30: corrugation off (start of the smoothstep) */
#define W02       3355443               /* 0.2: smoothstep width */
#define PIN0      3355443               /* 0.2 .. pi - 0.15: pinch-off band */
#define PIN1      50190596
#define SPR0      4194304               /* 0.25 .. pi - 0.2: spray band */
#define SPR1      49351735
#define ANT       51029457              /* pi - 0.10: antipode burst radius */
#define R0Q       251658                /* 0.015: rim start radius */
#define KQI       421657                /* 2 V0 2^24 (V0 = pi/250): speed-table value of q = 1 */
#define SIN035    375809638             /* 0.35 Q30 (ds floor) */
#define CAK       56966666              /* cA / KQ, Q48 per speed unit (cA = 0.0853377) */
#define CBK8      11127432              /* cB KQ, Q8 (cB = 0.1030849) */
#define JW2Q      130832186             /* (2 pi / 36)^2, Q32 */
#define JKAPQ     214748365             /* 0.05, Q32 */
#define JGQ       427228                /* JAMP 2^24 / KQ, Q32 */

INL i64 rsh(i64 a, u32 s) { return (a + ((i64)1 << (s - 1u))) >> s; }
INL i64 mul30(i64 a, i64 b) { return (a * b) >> 30; }

/* floor(sqrt(v)) for any u64, 32 fixed rounds */
INL u64 isqrt64(u64 v) {
  u64 r = 0, bit = (u64)1 << 62;
#ifdef __clang__
#pragma clang loop unroll(disable)
#endif
  for (u32 it = 0; it < 32u; it++) {
    if (v >= r + bit) { v -= r + bit; r = (r >> 1) + bit; }
    else r >>= 1;
    bit >>= 2;
  }
  return r;
}

/* vortex.js hash2(a, b) * 2^32, exactly */
INL u32 hash2(u32 a, u32 b) {
  u32 h = ((a ^ 0x9E3779B9u) * 0x85EBCA6Bu) ^ ((b + 0x632BE5ABu) * 0xC2B2AE35u);
  h ^= h >> 15;
  h *= 0x2C1B3C6Du;
  h ^= h >> 12;
  return h;
}
INL i64 hc(u32 h) { return (i64)h - 2147483648LL; }     /* (hash - 0.5) 2^32 */

/* sin of a u32 phase (turns 2^-32), Q30: quadrant fold, then the Taylor series to x^13 in Q30 (error < 2^-28) */
INL i64 isin(u32 ph) {
  u32 q = ph >> 30, f = ph & 0x3FFFFFFFu;
  if (q & 1u) f = 0x40000000u - f;
  i64 x = ((i64)f * 1686629713) >> 30;                  /* f (pi/2) in Q30 radians */
  i64 x2 = mul30(x, x);
  i64 t = ONE30 - mul30(x2, 6882960);                   /* 1/156 */
  t = ONE30 - mul30(mul30(x2, 9761289), t);             /* 1/110 */
  t = ONE30 - mul30(mul30(x2, 14913081), t);            /* 1/72 */
  t = ONE30 - mul30(mul30(x2, 25565282), t);            /* 1/42 */
  t = ONE30 - mul30(mul30(x2, 53687091), t);            /* 1/20 */
  t = ONE30 - mul30(mul30(x2, 178956971), t);           /* 1/6 */
  i64 s = mul30(x, t);
  return (q & 2u) ? -s : s;
}
INL i64 icos(u32 ph) { return isin(ph + 0x40000000u); }
INL u32 rturns(i32 r) { return (u32)(u64)(((i64)r * 2670177) >> 16); }   /* 2^24 rad -> u32 turns */

/* ======================================================================================================== */
/* vortices: VK(model, S) = round(2 dt_s 2^23 u(S)), u = regularised spherical Biot-Savart (SPEC.md 5.1)     */
/* ======================================================================================================== */
INL u32 vort_n(void) { u32 n = M_N; return n > NV_MAX ? NV_MAX : n; }

/* XN[i] = trunc(2^30 S[i] / max(1, isqrt(|S[i]|^2))) componentwise */
INL void vk_normalise(const u32 *src, u32 n) {
  u32 *xn = XN;
  for (u32 i = 0; i < n; i++) {
    i64 x = (i32)src[3u * i], y = (i32)src[3u * i + 1u], z = (i32)src[3u * i + 2u];
    u64 s = (u64)(x * x) + (u64)(y * y) + (u64)(z * z);
    i64 l = (i64)isqrt64(s);
    if (l < 1) l = 1;
    xn[3u * i] = (u32)(x * ONE30 / l);
    xn[3u * i + 1u] = (u32)(y * ONE30 / l);
    xn[3u * i + 2u] = (u32)(z * ONE30 / l);
  }
}

/* VD = VK from XN and the circulation words.  Pair loop (i < j); each ordered-pair term is computed exactly as the
 * full double sum would compute it, so the result equals
 *   VD[3i+c] = rsh( sum_{j != i} ((CW_j w_ij >> 20) * ((x_j x x_i)_c >> 36)) >> 12, 36 )
 *   w_ij = 2^54 / max(D2, 2^30 + D2 - ((x_i . x_j) >> 30)),  x = XN (Q30), products exact in i64.            */
INL void vk_field(u32 n) {
  const u32 *xn = XN;
  i64 *acc = VACC;
  for (u32 m = 0; m < 3u * n; m++) acc[m] = 0;
  for (u32 i = 0; i < n; i++) {
    i64 xi = (i32)xn[3u * i], yi = (i32)xn[3u * i + 1u], zi = (i32)xn[3u * i + 2u];
    i64 ci = (i32)M_CW(i);
    i64 ax = 0, ay = 0, az = 0;
    for (u32 j = i + 1u; j < n; j++) {
      i64 xj = (i32)xn[3u * j], yj = (i32)xn[3u * j + 1u], zj = (i32)xn[3u * j + 2u];
      i64 cj = (i32)M_CW(j);
      i64 dot = (xi * xj + yi * yj + zi * zj) >> 30;
      i64 den = ONE30 + D2_30 - dot;
      if (den < D2_30) den = D2_30;
      i64 w = W_NUM / den;
      i64 gj = (cj * w) >> 20, gi = (ci * w) >> 20;
      i64 vx = yj * zi - zj * yi, vy = zj * xi - xj * zi, vz = xj * yi - yj * xi;   /* x_j x x_i, Q60 */
      ax += (gj * (vx >> 36)) >> 12;
      ay += (gj * (vy >> 36)) >> 12;
      az += (gj * (vz >> 36)) >> 12;
      acc[3u * j] += (gi * ((-vx) >> 36)) >> 12;
      acc[3u * j + 1u] += (gi * ((-vy) >> 36)) >> 12;
      acc[3u * j + 2u] += (gi * ((-vz) >> 36)) >> 12;
    }
    acc[3u * i] += ax;
    acc[3u * i + 1u] += ay;
    acc[3u * i + 2u] += az;
  }
  u32 *d = VD;
  for (u32 m = 0; m < 3u * n; m++) d[m] = (u32)(u64)rsh(acc[m], 36);
}

/* ======================================================================================================== */
/* pop helpers                                                                                               */
/* ======================================================================================================== */
/* SPD[k](r): linear interpolation of the bead's speed-table row on the radial grid r_j = j 2^19; >= 1 */
INL i64 spd_at(u32 k, i32 r) {
  u32 rr = r < 0 ? 0u : (u32)r;
  u32 j = rr >> JSH, f = rr & ((1u << JSH) - 1u);
  if (j >= JR - 1u) { j = JR - 2u; f = 1u << JSH; }
  const u32 *s = TBL + (k & BMASK) * JR + j;
  i64 a = (i32)s[0], b = (i32)s[1];
  i64 v = a + rsh((b - a) * (i64)f, JSH);
  return v < 1 ? 1 : v;
}
/* rim displacement of the Fredkin step: 2 * speed (the table holds round(2 V 2^24)); 0 once stopped */
INL u32 rim_d(u32 k, i32 r) { return r >= RIM_STOP ? 0u : (u32)spd_at(k, r); }

/* smoothstep(r, a, a + 0.2) in Q16 */
INL i64 smooth16(i32 r, i64 a) {
  i64 t = (((i64)r - a) * 65536) / W02;
  if (t < 0) t = 0;
  if (t > 65536) t = 65536;
  return (((t * t) >> 16) * (196608 - 2 * t)) >> 16;
}
/* corrugation envelope on(r) = smooth(r, 0.10, 0.30) (1 - smooth(r, pi - 0.30, pi - 0.10)), Q16 */
INL i64 on16(i32 r) { return (smooth16(r, ON0) * (65536 - smooth16(r, OFF0))) >> 16; }
/* sigma(r) = (ds0 / ds)^2 = 1 / max(sin r, 0.35)^2, Q16 */
INL i64 sig16(i32 r) {
  i64 s = isin(rturns(r));
  if (s < SIN035) s = SIN035;
  return ((i64)1 << 46) / ((s * s) >> 30);
}
/* pinch length (2^24 per radius): SZ 0.08 (0.45 + 1.6 hash2(k, ZSEED + 1)^2) sqrt(h / HREF), sqrt(h/HREF) = KQ/spd */
INL i64 zp_of(u32 k, i64 spd) {
  u32 h = hash2(k, M_ZSEED + 1u);
  u64 h2 = ((u64)h * h) >> 32;
  i64 fac = 29491 + (i64)((104858u * h2) >> 32);
  i64 zpf = (1342177 * fac) >> 16;
  return zpf * KQI / spd;
}
INL i32 zp_seed(u32 k) { return (i32)rsh(hc(hash2(k, M_ZSEED)) * 329853, 48); }   /* round(3e-7 SZ (hash - 0.5)) */
INL u32 rb_init(u32 k) { return (u32)R0Q + (u32)rsh(spd_at(k, R0Q), 1); }        /* r0 + round(V(R0) 2^24) */

/* corrugation kick K[k] = round(F / 4) from ZQ, RB, the speed table, the tick and the substep (SPEC.md 5.5) */
INL void corr_k(u32 sub) {
  const u32 *zq = ZQ, *rb = RB;
  i64 *lap = LAP;
  u32 *kz = KZ;
  for (u32 k = 0; k < NB; k++) {
    i64 dq = (i64)(i32)zq[(k + 1u) & BMASK] - 2 * (i64)(i32)zq[k] + (i64)(i32)zq[(k - 1u) & BMASK];
    lap[k] = (sig16((i32)rb[k]) * dq) >> 12;
  }
  u32 hb = (H_T - H_P) * 8u + sub, zs = M_ZSEED;
  for (u32 k = 0; k < NB; k++) {
    i32 r = (i32)rb[k];
    i64 kk = 0;
    if (r >= ON0 && r < RIM_STOP) {
      i64 spd = spd_at(k, r), on = on16(r), sg = sig16(r);
      i64 dq = (i64)(i32)zq[(k + 1u) & BMASK] - 2 * (i64)(i32)zq[k] + (i64)(i32)zq[(k - 1u) & BMASK];
      i64 a32 = (((((spd * CAK) >> 16) * on) >> 16) * sg) >> 16;          /* cA q on sigma, Q32 */
      i64 b24 = ((CBK8 * on * sg) / spd) >> 16;                           /* cB (on / q) sigma, Q24 */
      i64 l2 = lap[(k + 1u) & BMASK] - 2 * lap[k] + lap[(k - 1u) & BMASK];
      i64 f = -((a32 * dq) >> 16) - ((b24 * l2) >> 12);                  /* Q16 */
      i64 am = (spd * spd * 13107) >> 24;                                 /* a SZ = 0.2 spd^2 / 2^24, Q16 */
      i64 lo = -((am * 22938) >> 16);                                     /* -0.35 a */
      i64 zp = zp_of(k, spd), z = (i32)zq[k];
      i64 hi = (z * 5 > zp * 8) ? 0 : (am >> 1);                          /* 0.5 a, 0 above 1.6 zp */
      if (f > hi) f = hi;
      if (f < lo) f = lo;
      f += (((am * 8589935) >> 32) * hc(hash2(k ^ zs, hb))) >> 32;        /* 0.002 a (hash - 0.5) */
      kk = (f + (1 << 17)) >> 18;
    }
    kz[k] = (u32)(u64)kk;
  }
}

/* jiggle kick K[k] = round(-JW2 q - JKAP lap + JAMP (V / V0) F 2^24) from JQ, RB, the table and the tick */
#define JTERM(i, m, wt) (ja##i * isin((u32)(m) * bk + ph##i))
INL void jig_k(void) {
  const u32 *jq = JQ, *rb = RB;
  u32 *kj = KJ;
  u32 t = H_T - H_P;
  u32 ph0 = H_JPH(0) + 119790980u * t, ph1 = H_JPH(1) + 120558376u * t, ph2 = H_JPH(2) + 121765983u * t;
  u32 ph3 = H_JPH(3) + 123240517u * t, ph4 = H_JPH(4) + 125175750u * t, ph5 = H_JPH(5) + 127622235u * t;
  i64 ja0 = (i32)H_JA(0), ja1 = (i32)H_JA(1), ja2 = (i32)H_JA(2), ja3 = (i32)H_JA(3), ja4 = (i32)H_JA(4),
      ja5 = (i32)H_JA(5);
  for (u32 k = 0; k < NB; k++) {
    i32 r = (i32)rb[k];
    i64 kk = 0;
    if (r < RIM_STOP) {
      i64 q = (i32)jq[k];
      i64 lap = 2 * q - (i64)(i32)jq[(k - 1u) & BMASK] - (i64)(i32)jq[(k + 1u) & BMASK];
      u32 bk = k << 21;
      i64 f = JTERM(0, 23, 0) + JTERM(1, 37, 0) + JTERM(2, 52, 0) + JTERM(3, 66, 0) + JTERM(4, 81, 0) +
              JTERM(5, 97, 0);                                             /* Q46 */
      i64 drv = ((f >> 16) * ((spd_at(k, r) * JGQ) >> 16)) >> 14;         /* Q32 */
      kk = rsh(-JW2Q * q - JKAPQ * lap + drv, 32);
    }
    kj[k] = (u32)(u64)kk;
  }
}

/* rim geometry at bead k, radius r: position n, d/dr t, along-rim e (Q30), from the puncture frame */
typedef struct { i64 nx, ny, nz, tx, ty, tz, ex, ey, ez; } geo_t;
INL geo_t rim_geo(u32 k, i32 r) {
  geo_t g;
  u32 pr = rturns(r), pk = k << 21;
  i64 cr = icos(pr), sr = isin(pr), ck = icos(pk), sk = isin(pk);
  i64 c0 = (i32)H_C(0), c1 = (i32)H_C(1), c2 = (i32)H_C(2);
  i64 a0 = (i32)H_E1(0), a1 = (i32)H_E1(1), a2 = (i32)H_E1(2);
  i64 b0 = (i32)H_E2(0), b1 = (i32)H_E2(1), b2 = (i32)H_E2(2);
  i64 dx = (ck * a0 + sk * b0) >> 30, dy = (ck * a1 + sk * b1) >> 30, dz = (ck * a2 + sk * b2) >> 30;
  g.nx = (cr * c0 + sr * dx) >> 30; g.ny = (cr * c1 + sr * dy) >> 30; g.nz = (cr * c2 + sr * dz) >> 30;
  g.tx = (cr * dx - sr * c0) >> 30; g.ty = (cr * dy - sr * c1) >> 30; g.tz = (cr * dz - sr * c2) >> 30;
  g.ex = (ck * b0 - sk * a0) >> 30; g.ey = (ck * b1 - sk * a1) >> 30; g.ez = (ck * b2 - sk * a2) >> 30;
  return g;
}
/* tube radius 0.0030 + 0.0055 sqrt(min(1.5, r / 1.2) min(2.5, h / HREF)), Q30; h / HREF = (KQ / spd)^2 */
INL i64 tube30(i32 r, i64 spd) {
  i64 a = ((i64)(r < 0 ? 0 : r) * 5) / 1536;
  if (a > 98304) a = 98304;
  i64 b = 11651972255721782LL / (spd * spd);
  if (b > 163840) b = 163840;
  return 3221225 + ((5905580 * (i64)isqrt64((u64)(a * b))) >> 16);
}
/* (x, y, z) <- 2^30 (x, y, z) / max(1, isqrt(|.|^2)) */
#define NRM3(x, y, z) do { u64 s_ = (u64)((x) * (x)) + (u64)((y) * (y)) + (u64)((z) * (z)); \
    i64 l_ = (i64)isqrt64(s_); if (l_ < 1) l_ = 1; \
    (x) = (x) * ONE30 / l_; (y) = (y) * ONE30 / l_; (z) = (z) * ONE30 / l_; } while (0)

INL void push_rec(u32 nd, i64 px, i64 py, i64 pz, i64 vx, i64 vy, i64 vz, u32 birth, u32 kp, i64 dz, i64 de) {
  u32 *o = DI + REC * nd;
  o[0] = (u32)px; o[1] = (u32)py; o[2] = (u32)pz;
  o[3] = (u32)vx; o[4] = (u32)vy; o[5] = (u32)vz;
  o[6] = birth; o[7] = kp; o[8] = (u32)dz; o[9] = (u32)de;
}

INL u32 drop_n(void) { u32 n = H_ND; return n > DMAX ? DMAX : n; }

/* ======================================================================================================== */
/* exports (SPEC.md section 3)                                                                               */
/* ======================================================================================================== */
EXPORT("ve_version") u32 ve_version(void) { return VE_VERSION; }
EXPORT("ve_hdr_ptr") u32 ve_hdr_ptr(void) { return HDR_OFF; }
EXPORT("ve_model_ptr") u32 ve_model_ptr(void) { return MODEL_OFF; }
EXPORT("ve_table_ptr") u32 ve_table_ptr(void) { return TBL_OFF; }
EXPORT("ve_state_ptr") u32 ve_state_ptr(void) { return VA_OFF; }
EXPORT("ve_scratch_ptr") u32 ve_scratch_ptr(void) { return SCR_OFF; }

/* model check: 0 = valid */
INL u32 model_valid(void) {
  const u32 *m = MODEL;
  if (m[0] != VE_MAGIC_M) return 1u;
  if (m[1] < 1u || m[1] > NV_MAX) return 2u;
  if (m[3] > 1u) return 3u;
  for (u32 w = 4; w < 16u; w++) if (m[w] != 0u) return 4u;
  for (u32 j = 0; j < NV_MAX; j++) {
    i64 c = (i32)m[16u + j];
    if (j >= m[1] ? c != 0 : (c > (1 << 28) || c < -(1 << 28))) return 5u;
  }
  for (u32 w = 16u + NV_MAX; w < 1024u; w++) if (m[w] != 0u) return 6u;
  return 0u;
}
EXPORT("ve_validate") u32 ve_validate(void) { return model_valid(); }

/* header reset (tick 0, not punctured) and pop state cleared; the host writes VA (and the model) before */
EXPORT("ve_init") u32 ve_init(void) {
  u32 v = model_valid();
  if (v) return v;
  u32 *h = HDR;
  for (u32 w = 0; w < 64u; w++) h[w] = 0u;
  h[0] = VE_MAGIC_S;
  h[1] = VE_VERSION;
  H_P = PNONE;
  u32 *s = RA;
  for (u32 w = 0; w < (DI_OFF + 4u * REC * DMAX - RA_OFF) / 4u; w++) s[w] = 0u;
  return 0u;
}

/* careful first step (vortex.js vortexInit): mid = VA + round(VK(VA) / 4); VB = VA + round(VK(mid) / 2) */
EXPORT("ve_vort_init") void ve_vort_init(void) {
  u32 n = vort_n();
  vk_normalise(VA, n);
  vk_field(n);
  for (u32 m = 0; m < 3u * n; m++) VB[m] = VA[m] + (u32)rsh((i32)VD[m], 2);
  vk_normalise(VB, n);
  vk_field(n);
  for (u32 m = 0; m < 3u * n; m++) VB[m] = VA[m] + (u32)rsh((i32)VD[m], 1);
}

/* one vortex Fredkin substep: VB' = VA + VK(model, VB), VA' = VB */
EXPORT("ve_vort_apply") void ve_vort_apply(void) {
  u32 n = vort_n();
  vk_normalise(VB, n);
  vk_field(n);
  BARRIER;
  u32 m3 = 3u * vort_n();
  u32 *a = VA, *b = VB;
  const u32 *d = VD;
  for (u32 m = 0; m < m3; m++) { u32 t = b[m]; b[m] = a[m] + d[m]; a[m] = t; }
}
/* its inverse: VA' = VB - VK(model, VA), VB' = VA */
EXPORT("ve_vort_unapply") void ve_vort_unapply(void) {
  u32 n = vort_n();
  vk_normalise(VA, n);
  vk_field(n);
  BARRIER;
  u32 m3 = 3u * vort_n();
  u32 *a = VA, *b = VB;
  const u32 *d = VD;
  for (u32 m = 0; m < m3; m++) { u32 t = a[m]; a[m] = b[m] - d[m]; b[m] = t; }
}

/* droplets, i < nd: vy -= g; x += v  /  x -= v; vy += g */
EXPORT("ve_drop_apply") void ve_drop_apply(void) {
  u32 n = drop_n();
  u32 *p = DI;
  for (u32 i = 0; i < n; i++) {
    u32 *o = p + REC * i;
    o[4] -= GD;
    o[0] += o[3];
    o[1] += o[4];
    o[2] += o[5];
  }
}
EXPORT("ve_drop_unapply") void ve_drop_unapply(void) {
  u32 n = drop_n();
  u32 *p = DI;
  for (u32 i = 0; i < n; i++) {
    u32 *o = p + REC * i;
    o[0] -= o[3];
    o[1] -= o[4];
    o[2] -= o[5];
    o[4] += GD;
  }
}

/* births at tick T (records carry birth = T + 1): 1. pinch-off at corrugation crests above the pinch length,
 * 2. rim spray by the integer hash rule, 3. antipode burst on the crossing of pi - 0.10.  Returns nd. */
EXPORT("ve_birth_apply") u32 ve_birth_apply(void) {
  u32 nd = drop_n(), birth = H_T + 1u, zs = M_ZSEED;
  u32 *zq = ZQ, *zp = ZP;
  const u32 *ra = RA, *rb = RB;
  /* 1. pinch-off: the crest gives (dz, deta) = (round(0.3 z), max(0, ZP)) to its drop */
  for (u32 k = 0; k < NB && nd < DMAX; k++) {
    i32 r = (i32)rb[k];
    if (r < PIN0 || r > PIN1) continue;
    i32 z = (i32)zq[k];
    if (z <= (i32)zq[(k - 1u) & BMASK] || z < (i32)zq[(k + 1u) & BMASK]) continue;
    i64 spd = spd_at(k, r);
    if ((i64)z < zp_of(k, spd)) continue;
    geo_t g = rim_geo(k, r);
    i64 tube = tube30(r, spd);
    i64 sp = (hc(hash2(k, zs + 9u)) * 22938) >> 32;                       /* tilt (h - 0.5), Q16 */
    i64 b0 = (11796 * ((i64)hash2(k, zs + 10u) + 2147483648LL)) >> 32;   /* back (0.5 + h), Q16 */
    i64 b1 = 29491 + (i64)((39322u * (u64)hash2(k, zs + 11u)) >> 32);   /* bend (0.6 + 0.8 h), Q16 */
    i64 p0 = g.nx - ((b0 * g.tx) >> 16) + ((sp * g.ex) >> 16);
    i64 p1 = g.ny - ((b0 * g.ty) >> 16) + ((sp * g.ey) >> 16);
    i64 p2 = g.nz - ((b0 * g.tz) >> 16) + ((sp * g.ez) >> 16);
    i64 q0 = g.nx - ((b1 * g.tx) >> 16) + ((sp * 8 * g.ex) / 327680);    /* 1.6 sp = 8 sp / 5 */
    i64 q1 = g.ny - ((b1 * g.ty) >> 16) + ((sp * 8 * g.ey) / 327680);
    i64 q2 = g.nz - ((b1 * g.tz) >> 16) + ((sp * 8 * g.ez) / 327680);
    NRM3(p0, p1, p2);
    NRM3(q0, q1, q2);
    i64 zz = z;
    i64 px = rsh(((g.nx * (ONE30 + tube)) >> 30) + ((zz * (p0 + q0)) >> 25), 10);
    i64 py = rsh(((g.ny * (ONE30 + tube)) >> 30) + ((zz * (p1 + q1)) >> 25), 10);
    i64 pz = rsh(((g.nz * (ONE30 + tube)) >> 30) + ((zz * (p2 + q2)) >> 25), 10);
    i64 zpk = (i32)zp[k];
    i64 vt = (spd * 57672) >> 16;                                          /* speeds in SD / 32 per tick */
    i64 vn = (((zpk > 0 ? zpk : 0) * 2 * 58982) >> 16) + ((spd * 6554) >> 16);
    i64 j1 = (((spd * 9175) >> 16) * hc(hash2(k + 4096u * birth, zs + 2u))) >> 32;
    i64 j2 = (((spd * 3932) >> 16) * hc(hash2(k + 4096u * birth, zs + 3u))) >> 32;
    i64 vx = rsh(vt * g.tx + vn * q0 + j1 * g.ex + j2 * g.nx, 35);
    i64 vy = rsh(vt * g.ty + vn * q1 + j1 * g.ey + j2 * g.ny, 35);
    i64 vz = rsh(vt * g.tz + vn * q2 + j1 * g.ez + j2 * g.nz, 35);
    i64 dz = rsh(zz * 19661, 16), de = zpk > 0 ? zpk : 0;
    push_rec(nd, px, py, pz, vx, vy, vz, birth, k, dz, de);
    nd++;
    zq[k] -= (u32)dz;
    zp[k] -= (u32)de;
  }
  /* 2. fine spray: hash2(k ^ 3 ZSEED, birth) < 0.0012 (V / V0) 2^32 */
  for (u32 k = 0; k < NB && nd < DMAX; k++) {
    i32 r = (i32)rb[k];
    if (r < SPR0 || r > SPR1) continue;
    i64 spd = spd_at(k, r);
    if ((i64)hash2(k ^ (zs * 3u), birth) >= ((spd * 801053) >> 16)) continue;
    geo_t g = rim_geo(k, r);
    i64 tube = tube30(r, spd);
    u32 h2 = hash2(birth, k + 31337u);
    i64 vt = (spd * (55706 + (i64)((9830u * (u64)h2) >> 32))) >> 16;
    i64 vn = (spd * (9830 + (i64)((22938u * (u64)h2) >> 32))) >> 16;
    i64 j1 = (((spd * 16384) >> 16) * hc(hash2(k, birth + 77777u))) >> 32;
    i64 px = rsh((g.nx * (ONE30 + tube)) >> 30, 10);
    i64 py = rsh((g.ny * (ONE30 + tube)) >> 30, 10);
    i64 pz = rsh((g.nz * (ONE30 + tube)) >> 30, 10);
    i64 vx = rsh(vt * g.tx + vn * g.nx + j1 * g.ex, 35);
    i64 vy = rsh(vt * g.ty + vn * g.ny + j1 * g.ey, 35);
    i64 vz = rsh(vt * g.tz + vn * g.nz + j1 * g.ez, 35);
    push_rec(nd, px, py, pz, vx, vy, vz, birth, (1u << 16) | k, 0, 0);
    nd++;
  }
  /* 3. antipode burst: beads crossing pi - 0.10 this tick (RA = old radius, RB = new), hash2(k, ZSEED + 5) <= 0.6 */
  for (u32 k = 0; k < NB && nd < DMAX; k++) {
    i32 ro = (i32)ra[k], rn = (i32)rb[k];
    if (!(ro < ANT && rn >= ANT)) continue;
    if (hash2(k, zs + 5u) > 2576980377u) continue;
    geo_t g = rim_geo(k, rn);
    i64 vv = spd_at(k, rn);
    if (vv < KQI / 2) vv = KQI / 2;                                        /* max(V, 0.5 V0) */
    u32 h1 = hash2(k, zs + 6u);
    u64 h1s = ((u64)h1 * h1) >> 32;
    i64 up = (vv * (16384 + (i64)((58982u * h1s) >> 32))) >> 16;           /* (0.25 + 0.9 h1^2) V */
    i64 lat = (vv * 36045) >> 16;                                          /* 0.55 V */
    i64 l2 = (lat * hc(hash2(k, zs + 7u))) >> 32, l3 = (lat * hc(hash2(k, zs + 8u))) >> 32;
    i64 c0 = (i32)H_C(0), c1 = (i32)H_C(1), c2 = (i32)H_C(2);
    i64 vx = rsh(-up * c0 + l2 * g.ex + l3 * g.tx, 35);
    i64 vy = rsh(-up * c1 + l2 * g.ey + l3 * g.ty, 35);
    i64 vz = rsh(-up * c2 + l2 * g.ez + l3 * g.tz, 35);
    push_rec(nd, rsh(g.nx, 10), rsh(g.ny, 10), rsh(g.nz, 10), vx, vy, vz, birth, (2u << 16) | k, 0, 0);
    nd++;
  }
  H_ND = nd;
  return nd;
}

/* un-birth at tick T: pop every record with birth = T + 1 (LIFO), give a pinch-off parent (dz, deta) back,
 * zero the record.  Returns the number popped. */
EXPORT("ve_birth_unapply") u32 ve_birth_unapply(void) {
  u32 n = drop_n(), b = H_T + 1u, c = 0;
  u32 *zq = ZQ, *zp = ZP, *di = DI;
  while (n > 0u && di[REC * (n - 1u) + 6u] == b) {
    n--;
    u32 *o = di + REC * n;
    u32 kp = o[7], k = kp & BMASK;
    if ((kp >> 16) == 0u) {
      zq[k] = zq[k] + o[8];
      zp[k] = zp[k] VE_UNBIRTH_DE_OP o[9];
    }
    for (u32 w = 0; w < REC; w++) o[w] = 0u;
    c++;
  }
  H_ND = n;
  return c;
}

/* rim Fredkin step: RB' = RA + D(RB), RA' = RB with D(r)[k] = 2 speed(k, r) (0 for r >= pi - 0.02) */
EXPORT("ve_rim_apply") void ve_rim_apply(void) {
  u32 *rd = RD;
  const u32 *src = RB;
  for (u32 k = 0; k < NB; k++) rd[k] = rim_d(k, (i32)src[k]);
  BARRIER;
  u32 *a = RA, *b = RB;
  const u32 *d = RD;
  for (u32 k = 0; k < NB; k++) { u32 t = b[k]; b[k] = a[k] + d[k]; a[k] = t; }
}
EXPORT("ve_rim_unapply") void ve_rim_unapply(void) {
  u32 *rd = RD;
  const u32 *src = RA;
  for (u32 k = 0; k < NB; k++) rd[k] = rim_d(k, (i32)src[k]);
  BARRIER;
  u32 *a = RA, *b = RB;
  const u32 *d = RD;
  for (u32 k = 0; k < NB; k++) { u32 t = a[k]; a[k] = b[k] - d[k]; b[k] = t; }
}

/* corrugation kick substep sub (0 .. 3): ZP += K(ZQ, RB, table, T - P, sub)  /  ZP -= the same K */
EXPORT("ve_corr_kick") void ve_corr_kick(u32 sub) {
  corr_k(sub);
  BARRIER;
  u32 *p = ZP;
  const u32 *kz = KZ;
  for (u32 k = 0; k < NB; k++) p[k] += kz[k];
}
EXPORT("ve_corr_unkick") void ve_corr_unkick(u32 sub) {
  corr_k(sub);
  BARRIER;
  u32 *p = ZP;
  const u32 *kz = KZ;
  for (u32 k = 0; k < NB; k++) p[k] -= kz[k];
}
/* corrugation drift substep: ZQ += round(ZP / 4) where RB < pi - 0.02 (stopped beads freeze)  /  ZQ -= the same */
EXPORT("ve_corr_drift") void ve_corr_drift(void) {
  u32 *q = ZQ;
  const u32 *p = ZP, *rb = RB;
  for (u32 k = 0; k < NB; k++) if ((i32)rb[k] < RIM_STOP) q[k] += (u32)(u64)(((i64)(i32)p[k] + 2) >> 2);
}
EXPORT("ve_corr_undrift") void ve_corr_undrift(void) {
  u32 *q = ZQ;
  const u32 *p = ZP, *rb = RB;
  for (u32 k = 0; k < NB; k++) if ((i32)rb[k] < RIM_STOP) q[k] -= (u32)(u64)(((i64)(i32)p[k] + 2) >> 2);
}

/* jiggle ring (model flag bit 0): JP += K(JQ, RB, table, T - P)  /  JP -= the same K;  JQ += JP  /  JQ -= JP */
EXPORT("ve_jig_kick") void ve_jig_kick(void) {
  if (!(M_FLAGS & 1u)) return;
  jig_k();
  BARRIER;
  u32 *p = JP;
  const u32 *kj = KJ;
  for (u32 k = 0; k < NB; k++) p[k] += kj[k];
}
EXPORT("ve_jig_unkick") void ve_jig_unkick(void) {
  if (!(M_FLAGS & 1u)) return;
  jig_k();
  BARRIER;
  u32 *p = JP;
  const u32 *kj = KJ;
  for (u32 k = 0; k < NB; k++) p[k] -= kj[k];
}
EXPORT("ve_jig_drift") void ve_jig_drift(void) {
  if (!(M_FLAGS & 1u)) return;
  u32 *q = JQ;
  const u32 *p = JP;
  for (u32 k = 0; k < NB; k++) q[k] += p[k];
}
EXPORT("ve_jig_undrift") void ve_jig_undrift(void) {
  if (!(M_FLAGS & 1u)) return;
  u32 *q = JQ;
  const u32 *p = JP;
  for (u32 k = 0; k < NB; k++) q[k] -= p[k];
}

/* the puncture at the current tick, direction (cx, cy, cz) (int32, 2^23): frame, jiggle drive (mulberry seeded as
 * vortex.js), rim start (careful first step), droplets cleared, corrugation seeded.  The host writes the speed table
 * first.  Returns 0, 1 if already punctured, 2 if the direction is zero. */
#define MB_NEXT(a, out) do { (a) += 0x6D2B79F5u; u32 t_ = ((a) ^ ((a) >> 15)) * (1u | (a)); \
    t_ = (t_ + ((t_ ^ (t_ >> 7)) * (61u | t_))) ^ t_; (out) = t_ ^ (t_ >> 14); } while (0)
EXPORT("ve_puncture") u32 ve_puncture(u32 cx, u32 cy, u32 cz) {
  if (H_P != PNONE) return 1u;
  i64 x = (i32)cx, y = (i32)cy, z = (i32)cz;
  if (x == 0 && y == 0 && z == 0) return 2u;
  NRM3(x, y, z);
  i64 u0, u1, u2;
  if ((y < 0 ? -y : y) < 1020054733) { u0 = z; u1 = 0; u2 = -x; }      /* up = (0,1,0): up x C */
  else { u0 = 0; u1 = -z; u2 = y; }                                       /* up = (1,0,0) */
  NRM3(u0, u1, u2);
  H_P = H_T;
  H_POPC(0) = cx; H_POPC(1) = cy; H_POPC(2) = cz;
  H_C(0) = (u32)x; H_C(1) = (u32)y; H_C(2) = (u32)z;
  H_E1(0) = (u32)u0; H_E1(1) = (u32)u1; H_E1(2) = (u32)u2;
  H_E2(0) = (u32)((y * u2 - z * u1) >> 30);
  H_E2(1) = (u32)((z * u0 - x * u2) >> 30);
  H_E2(2) = (u32)((x * u1 - y * u0) >> 30);
  u32 a = cx ^ (cy * 7u) ^ (cz * 13u);
  for (u32 i = 0; i < 6u; i++) {
    u32 v;
    MB_NEXT(a, v);
    H_JPH(i) = v;
    MB_NEXT(a, v);
    H_JA(i) = 39322u + (u32)((52429u * (u64)v) >> 32);                  /* 0.6 + 0.8 rnd, Q16 */
  }
  for (u32 k = 0; k < NB; k++) {
    RA[k] = (u32)R0Q;
    RB[k] = rb_init(k);
    JQ[k] = 0u; JP[k] = 0u; ZQ[k] = 0u;
    ZP[k] = (u32)zp_seed(k);
  }
  u32 *d = DI;
  for (u32 w = 0; w < REC * DMAX; w++) d[w] = 0u;
  H_ND = 0u;
  return 0u;
}
/* un-puncture (stepping back onto the puncture tick): count every pop word that differs from its post-puncture
 * value (and every live droplet) into the header word healErr, then clear the pop state.  Returns the count. */
EXPORT("ve_unpuncture") u32 ve_unpuncture(void) {
  if (H_P == PNONE) return 0u;
  u32 bad = H_ND;
  for (u32 k = 0; k < NB; k++) {
    bad += (RA[k] != (u32)R0Q) + (RB[k] != rb_init(k)) + (JQ[k] != 0u) + (JP[k] != 0u) + (ZQ[k] != 0u) +
           (ZP[k] != (u32)zp_seed(k));
  }
  H_HEAL += bad;
  H_P = PNONE;
  u32 *h = HDR;
  for (u32 w = 6u; w < 30u; w++) h[w] = 0u;
  for (u32 k = 0; k < NB; k++) { RA[k] = 0u; RB[k] = 0u; JQ[k] = 0u; JP[k] = 0u; ZQ[k] = 0u; ZP[k] = 0u; }
  u32 *d = DI;
  for (u32 w = 0; w < REC * DMAX; w++) d[w] = 0u;
  H_ND = 0u;
  return bad;
}

EXPORT("ve_tick_inc") void ve_tick_inc(void) { H_T += 1u; }
EXPORT("ve_tick_dec") void ve_tick_dec(void) { H_T -= 1u; }
