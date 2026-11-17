/* vortex.c: Vortex Echo, purist Wasm (lane vortex-purist-20261106, M1).
 *
 * One module, no imports.  The leaves are ve_core.c (VAB tasks/bubble-echo/vortex/core, main a1580438, the source of
 * the proved ve_core.wasm 72fe0ba2) with EXPORT turned into `static noinline` (ve_leaves.c, made by build.sh with one
 * sed line).  This file adds what the JS host used to do:
 *   - the seeded scene (ve_run.c build_vortices) and the model words, in f64 with an in-module sin/cos (no imports);
 *   - the rim speed table at the puncture (ve_run.c hfield, rewritten without atan2/asin), in f64;
 *   - the tick sequencer (vortex/SPEC.md section 4: 16 vortex substeps per swirl tick; pop tick = rim, jiggle,
 *     4 x corrugation, droplets, births, 1 vortex substep), the auto puncture, the end of the run, the un-puncture.
 * Descoped vs v5.8w2: the v5.8 pop of ve2_core.wasm (needs film tables read back from the GPU tracers) is replaced by
 * the v1 pop already in ve_core.c; the speed table comes from the synthetic thickness field of ve_run.c, not the
 * film readback; the GPU film tracers stay outside (drawing only).
 * Canonical state = bytes [0x4000, 0x1E0000) as in vortex/SPEC.md section 2; the table is zero before the puncture.
 */
#include "ve_leaves.c"

#define QSUB   16u
#define PSUB   1u
#define NS     4u
#define AFTER  520u               /* pop ticks after the puncture (vortex.js AFTER) */
#define H_AUTO HDR[32]            /* auto-puncture tick (0 = none) */
#define H_AUTOC(a) HDR[33u + (a)] /* its direction, int32 2^23 */
#define SNAP_OFF  0x200000u       /* check aid: snapshot of the canonical bytes */
#define CAN0 HDR_OFF
#define CAN1 SCR_OFF
#define F64S(off) ((double *)(MEMBASE + (off)))
#define X0_OFF 0x1F4000u          /* f64 [640][3] scene positions (scratch) */
#define G4_OFF 0x1F8000u          /* f64 [640] scene circulations (scratch) */

#define WEXPORT(name) __attribute__((export_name(name)))
typedef double f64;

/* ---- f64 helpers: only add/sub/mul/div/sqrt/floor/compare (IEEE-754 exact rounding, no host math) ---- */
#define PI_D    3.14159265358979311600e+00
#define PIO2_HI 1.57079632673412561417e+00
#define PIO2_LO 6.07710050650619224932e-11
#define TWOOPI  6.36619772367581382433e-01
INL f64 ksin(f64 x) {
  f64 z = x * x;
  return x + x * z * (-1.66666666666666324348e-01 + z * (8.33333333332248946124e-03 + z * (-1.98412698298579493134e-04 +
         z * (2.75573137070700676789e-06 + z * (-2.50507602534068634195e-08 + z * 1.58969099521155010221e-10)))));
}
INL f64 kcos(f64 x) {
  f64 z = x * x;
  return 1.0 - 0.5 * z + z * z * (4.16666666666666019037e-02 + z * (-1.38888888888741095749e-03 + z * (2.48015872894767294178e-05 +
         z * (-2.75573143513906633035e-07 + z * (2.08757232129817482790e-09 + z * -1.13596475577881948265e-11)))));
}
static __attribute__((noinline)) f64 dsin_q(f64 x, u32 shift) {   /* sin(x + shift pi/2) */
  f64 n = __builtin_floor(x * TWOOPI + 0.5);
  f64 y = (x - n * PIO2_HI) - n * PIO2_LO;
  u32 q = ((u32)(i32)(i64)n + shift) & 3u;
  return q == 0u ? ksin(y) : q == 1u ? kcos(y) : q == 2u ? -ksin(y) : -kcos(y);
}
INL f64 dsin(f64 x) { return dsin_q(x, 0u); }
INL f64 dcos(f64 x) { return dsin_q(x, 1u); }
INL f64 dsqrt(f64 x) { return __builtin_sqrt(x); }
INL i32 dround(f64 x) { return x >= 0 ? (i32)(i64)__builtin_floor(x + 0.5) : -(i32)(i64)__builtin_floor(0.5 - x); }
INL void v3norm(f64 *a) { f64 l = dsqrt(a[0] * a[0] + a[1] * a[1] + a[2] * a[2]); a[0] /= l; a[1] /= l; a[2] /= l; }
INL void v3cross(const f64 *a, const f64 *b, f64 *o) {
  f64 x = a[1] * b[2] - a[2] * b[1], y = a[2] * b[0] - a[0] * b[2], z = a[0] * b[1] - a[1] * b[0];
  o[0] = x; o[1] = y; o[2] = z;
}
INL void sph(f64 lon, f64 lat, f64 *o) {
  f64 lo = lon * PI_D / 180, la = lat * PI_D / 180;
  o[0] = dcos(la) * dsin(lo); o[1] = dsin(la); o[2] = dcos(la) * dcos(lo);
}
static __attribute__((noinline)) void frame_at(const f64 *c, f64 *e1, f64 *e2) {
  f64 up[3] = {0, 1, 0};
  f64 ay = c[1] < 0 ? -c[1] : c[1];
  if (!(ay < 0.95)) { up[0] = 1; up[1] = 0; }
  v3cross(up, c, e1); v3norm(e1); v3cross(c, e1, e2);
}

/* ---- the scene (ve_run.c build_vortices) ---- */
static u32 mb_state, nv;
static f64 rnd(void) { u32 v; MB_NEXT(mb_state, v); return v / 4294967296.0; }
static void at(const f64 *c, const f64 *e1, const f64 *e2, f64 r, f64 th) {
  f64 *x = F64S(X0_OFF) + 3u * nv;
  f64 s = dsin(r), k = dcos(r), ct = dcos(th), st = dsin(th);
  for (int a = 0; a < 3; a++) x[a] = k * c[a] + s * (ct * e1[a] + st * e2[a]);
  v3norm(x);
}
static void patch(f64 lon, f64 lat, f64 a, f64 gamma, u32 n) {
  f64 c[3], e1[3], e2[3];
  sph(lon, lat, c); frame_at(c, e1, e2);
  for (u32 i = 0; i < n; i++) {
    at(c, e1, e2, a * dsqrt((i + 0.5) / n), i * 2.39996323 + 0.2 * rnd());
    F64S(G4_OFF)[nv++] = gamma / n / (4 * PI_D);
  }
}
static void dipole(f64 lon, f64 lat, f64 d, f64 gamma, f64 a, u32 n) {
  f64 c[3], e1[3], e2[3];
  sph(lon, lat, c); frame_at(c, e1, e2);
  f64 t = dsin(d / 2) / dcos(d / 2);
  for (int s = -1; s <= 1; s += 2) {
    f64 cc[3], f1[3], f2[3];
    for (int q = 0; q < 3; q++) cc[q] = c[q] + s * t * e1[q];
    v3norm(cc); frame_at(cc, f1, f2);
    for (u32 i = 0; i < n; i++) {
      at(cc, f1, f2, a * dsqrt((i + 0.5) / n), i * 2.39996323);
      F64S(G4_OFF)[nv++] = -s * gamma / n / (4 * PI_D);
    }
  }
}
static void build_vortices(u32 seed) {
  nv = 0;
  mb_state = 20261019u + 7919u * (seed - 1u);
  patch(8, 25, 0.27, +0.85, 170);
  patch(46, 8, 0.15, +0.32, 70);
  patch(-42, -20, 0.20, -0.52, 110);
  dipole(-12, -60, 0.17, 0.11, 0.05, 8); dipole(30, -62, 0.17, 0.10, 0.05, 8);
  dipole(70, -55, 0.16, 0.09, 0.05, 8); dipole(-60, -58, 0.16, 0.09, 0.05, 8);
  for (u32 i = 0; i < 140u; i++) {
    f64 z = 2 * rnd() - 1, ph = 2 * PI_D * rnd(), s = dsqrt(1 - z * z);
    f64 *x = F64S(X0_OFF) + 3u * nv;
    x[0] = s * dcos(ph); x[1] = z; x[2] = s * dsin(ph);
    F64S(G4_OFF)[nv++] = ((i & 1u) ? 1 : -1) * (0.012 + 0.012 * rnd()) / (4 * PI_D);
  }
}

/* ve_run.c hfield without atan2/asin: lon = atan2(x, z), lat = asin(y), expanded by multiple-angle identities */
static f64 hfield(const f64 *p, u32 seed) {
  f64 y = p[1] < -1 ? -1 : p[1] > 1 ? 1 : p[1];
  f64 rho = dsqrt(p[0] * p[0] + p[2] * p[2]);
  f64 sl = rho > 1e-300 ? p[0] / rho : 0, cl = rho > 1e-300 ? p[2] / rho : 1;      /* sin lon, cos lon */
  f64 s3 = 3 * sl - 4 * sl * sl * sl, c3 = 4 * cl * cl * cl - 3 * cl;            /* 3 lon */
  f64 c2lat = 1 - 2 * y * y;
  f64 a = 0.9 * seed, b = 0.4 * seed;
  f64 t1 = (s3 * dcos(a) + c3 * dsin(a)) * c2lat;                                 /* sin(3 lon + a) cos(2 lat) */
  f64 s5 = 16 * y * y * y * y * y - 20 * y * y * y + 5 * y;                       /* sin 5 lat */
  f64 c5 = 16 * rho * rho * rho * rho * rho - 20 * rho * rho * rho + 5 * rho;     /* cos 5 lat (cos lat = rho) */
  f64 s2 = 2 * sl * cl, c2 = cl * cl - sl * sl;                                   /* 2 lon */
  f64 sa = s5 * c2 + c5 * s2, ca = c5 * c2 - s5 * s2;                             /* 5 lat + 2 lon */
  f64 t2 = sa * dcos(b) + ca * dsin(b);
  return 420 + 170 * t1 + 80 * t2 + 60 * (0.3 * p[0] + 0.8 * p[1] + 0.5 * p[2]);
}

static const f64 SEEDC[8][2] = {{-24, 27}, {-40, 12}, {-10, 40}, {-55, -5}, {15, 30}, {-30, -25}, {30, 10}, {-65, 30}};

/* the table for the puncture frame from the rounded direction (as ve_run.c do_setup) */
static void build_table(u32 cx, u32 cy, u32 cz, u32 seed) {
  f64 c[3] = {(f64)(i32)cx, (f64)(i32)cy, (f64)(i32)cz}, e1[3], e2[3];
  v3norm(c); frame_at(c, e1, e2);
  const f64 V0 = PI_D / 250, SR = 16777216.0;
  u32 *tbl = TBL;
  for (u32 k = 0; k < NB; k++) {
    f64 ang = 2 * PI_D * k / NB, ck = dcos(ang), sk = dsin(ang), d[3];
    for (int a = 0; a < 3; a++) d[a] = ck * e1[a] + sk * e2[a];
    for (u32 j = 0; j < JR; j++) {
      f64 r = j / 32.0, p[3], cr = dcos(r), sr = dsin(r);
      for (int a = 0; a < 3; a++) p[a] = cr * c[a] + sr * d[a];
      f64 h = hfield(p, seed);
      if (h < 140.0) h = 140.0;
      tbl[k * JR + j] = (u32)dround(2 * V0 * dsqrt(420.0 / h) * SR);
    }
  }
}
INL void clear_table(void) { u32 *t = TBL; for (u32 w = 0; w < NB * JR; w++) t[w] = 0u; }
INL u32 seed_of(void) { return (M_ZSEED - 0x5EEDu) / 977u; }


/* ---- M3: the vortex field in f64 inside the same Fredkin shape (build with -DVK_F64) ----
 * D_i = round( sum_{j != i} c_j (x_j x x_i) / max(d2, 1 + d2 - x_i . x_j) ),  c_j = CW_j 2^-20,  x = S / |S| in f64.
 * The same real formula as vk_field, evaluated in IEEE f64 (fixed pair order, no fma, no host math) instead of in
 * Q30/Q24 integers.  The pair (A, B) <- (B, A + D(B)) / (A, B) <- (B - D(A), A) is an exact inverse for any D that the
 * forward and backward steps compute identically, so reversal stays exact iff f64 evaluation is deterministic.
 * NaN-free by construction: |S| = 0 gives x = 0 (guarded), the denominator is >= d2 > 0, inputs are int32. */
#define XF_OFF 0x3E8000u          /* f64 [3 NV_MAX] unit vectors (scratch, above the snapshot) */
#define AF_OFF 0x3EC000u          /* f64 [3 NV_MAX] accumulators */
#define D2_F   0.0025
static __attribute__((noinline)) void vk_f64(const u32 *src, u32 n) {
  f64 *x = F64S(XF_OFF), *acc = F64S(AF_OFF);
  for (u32 i = 0; i < n; i++) {
    f64 a = (f64)(i32)src[3u * i], b = (f64)(i32)src[3u * i + 1u], c = (f64)(i32)src[3u * i + 2u];
    f64 l = dsqrt(a * a + b * b + c * c);
    if (!(l > 0.0)) l = 1.0;
    x[3u * i] = a / l; x[3u * i + 1u] = b / l; x[3u * i + 2u] = c / l;
    acc[3u * i] = 0; acc[3u * i + 1u] = 0; acc[3u * i + 2u] = 0;
  }
  for (u32 i = 0; i < n; i++) {
    f64 xi = x[3u * i], yi = x[3u * i + 1u], zi = x[3u * i + 2u];
    f64 ci = (f64)(i32)M_CW(i) * (1.0 / 1048576.0);
    f64 ax = 0, ay = 0, az = 0;
    for (u32 j = i + 1u; j < n; j++) {
      f64 xj = x[3u * j], yj = x[3u * j + 1u], zj = x[3u * j + 2u];
      f64 cj = (f64)(i32)M_CW(j) * (1.0 / 1048576.0);
      f64 den = 1.0 + D2_F - (xi * xj + yi * yj + zi * zj);
      if (den < D2_F) den = D2_F;
      f64 vx = yj * zi - zj * yi, vy = zj * xi - xj * zi, vz = xj * yi - yj * xi;   /* x_j x x_i */
      f64 gj = cj / den, gi = ci / den;
      ax += gj * vx; ay += gj * vy; az += gj * vz;
      acc[3u * j] -= gi * vx; acc[3u * j + 1u] -= gi * vy; acc[3u * j + 2u] -= gi * vz;
    }
    acc[3u * i] += ax; acc[3u * i + 1u] += ay; acc[3u * i + 2u] += az;
  }
  u32 *d = VD;
  for (u32 m = 0; m < 3u * n; m++) d[m] = (u32)dround(acc[m]);
}
static __attribute__((noinline)) void vort_apply_f64(void) {
  u32 n = vort_n();
  vk_f64(VB, n);
  u32 *a = VA, *b = VB; const u32 *d = VD;
  for (u32 m = 0; m < 3u * n; m++) { u32 t = b[m]; b[m] = a[m] + d[m]; a[m] = t; }
}
static __attribute__((noinline)) void vort_unapply_f64(void) {
  u32 n = vort_n();
  vk_f64(VA, n);
  u32 *a = VA, *b = VB; const u32 *d = VD;
  for (u32 m = 0; m < 3u * n; m++) { u32 t = a[m]; a[m] = b[m] - d[m]; b[m] = t; }
}
static void vort_init_f64(void) {   /* careful first step, as ve_vort_init */
  u32 n = vort_n();
  vk_f64(VA, n);
  for (u32 m = 0; m < 3u * n; m++) VB[m] = VA[m] + (u32)rsh((i32)VD[m], 2);
  vk_f64(VB, n);
  for (u32 m = 0; m < 3u * n; m++) VB[m] = VA[m] + (u32)rsh((i32)VD[m], 1);
}
#ifdef VK_F64
#define VORT_APPLY vort_apply_f64
#define VORT_UNAPPLY vort_unapply_f64
#define VORT_INIT vort_init_f64
#else
#define VORT_APPLY ve_vort_apply
#define VORT_UNAPPLY ve_vort_unapply
#define VORT_INIT ve_vort_init
#endif

/* ---- exports ---- */
/* init(seed, auto_tick): the seeded scene, model, ve_init, careful first step; auto puncture at auto_tick (0 = none)
 * at the seed's default point.  Returns 0 or the ve_init code. */
WEXPORT("init") u32 init(u32 seed, u32 auto_tick) {
  if (seed < 1u) seed = 1u;
  u32 *all = W32(HDR_OFF);
  for (u32 w = 0; w < (MEM_END - HDR_OFF) / 4u; w++) all[w] = 0u;
  build_vortices(seed);
  const f64 SV = 8388608.0, KV = 2 * (1.0 / 60 / 16) * SV;
  u32 *m = MODEL;
  m[0] = VE_MAGIC_M; m[1] = nv; m[2] = 0x5EEDu + 977u * seed; m[3] = 1u;
  const f64 *g4 = F64S(G4_OFF), *x0 = F64S(X0_OFF);
  for (u32 j = 0; j < nv; j++) m[16u + j] = (u32)dround(g4[j] * KV * 1048576.0);
  for (u32 i = 0; i < 3u * nv; i++) VA[i] = (u32)dround(x0[i] * SV);
  u32 v = ve_init();
  if (v) return v;
  VORT_INIT();
  if (auto_tick) {
    f64 c[3];
    sph(SEEDC[(seed - 1u) % 8u][0], SEEDC[(seed - 1u) % 8u][1], c);
    H_AUTO = auto_tick;
    for (int a = 0; a < 3; a++) H_AUTOC(a) = (u32)dround(c[a] * SV);
  }
  return 0u;
}

/* puncture now (tick >= 1, not punctured): table, then ve_puncture.  0 ok, 1 already punctured, 2 zero dir, 3 tick 0 */
WEXPORT("puncture") u32 puncture(u32 cx, u32 cy, u32 cz) {
  if (H_P != PNONE) return 1u;
  if (H_T == 0u) return 3u;
  if (cx == 0u && cy == 0u && cz == 0u) return 2u;
  build_table(cx, cy, cz, seed_of());
  return ve_puncture(cx, cy, cz);
}

/* one tick forward (SPEC.md section 4).  Returns 1, or 0 at the end of the run (AFTER pop ticks) */
WEXPORT("tick_forward") u32 tick_forward(void) {
  u32 T = H_T, P = H_P;
  if (P != PNONE && T >= P) {
    if (T >= P + AFTER) return 0u;
    ve_rim_apply();
    ve_jig_kick(); ve_jig_drift();
    for (u32 s = 0; s < NS; s++) { ve_corr_kick(s); ve_corr_drift(); }
    ve_drop_apply();
    ve_birth_apply();
    for (u32 i = 0; i < PSUB; i++) VORT_APPLY();
  } else {
    for (u32 i = 0; i < QSUB; i++) VORT_APPLY();
  }
  ve_tick_inc();
  if (H_P == PNONE && H_AUTO != 0u && H_T == H_AUTO) puncture(H_AUTOC(0), H_AUTOC(1), H_AUTOC(2));
  return 1u;
}

/* one tick backward.  Returns 1, or 0 at tick 0 */
WEXPORT("tick_backward") u32 tick_backward(void) {
  u32 T1 = H_T;
  if (T1 == 0u) return 0u;
  if (H_P != PNONE && T1 == H_P) { ve_unpuncture(); clear_table(); }
  u32 P = H_P;
  ve_tick_dec();
  if (P != PNONE && T1 > P) {
    for (u32 i = 0; i < PSUB; i++) VORT_UNAPPLY();
    ve_birth_unapply();
    ve_drop_unapply();
    for (u32 s = NS; s-- > 0;) { ve_corr_undrift(); ve_corr_unkick(s); }
    ve_jig_undrift(); ve_jig_unkick();
    ve_rim_unapply();
  } else {
    for (u32 i = 0; i < QSUB; i++) VORT_UNAPPLY();
  }
  return 1u;
}

/* views (read-only for the drawing host) */
WEXPORT("hdr_ptr") u32 hdr_ptr(void) { return HDR_OFF; }
WEXPORT("va_ptr") u32 va_ptr(void) { return VA_OFF; }
WEXPORT("vb_ptr") u32 vb_ptr(void) { return VB_OFF; }
WEXPORT("ra_ptr") u32 ra_ptr(void) { return RA_OFF; }
WEXPORT("rb_ptr") u32 rb_ptr(void) { return RB_OFF; }
WEXPORT("zq_ptr") u32 zq_ptr(void) { return ZQ_OFF; }
WEXPORT("di_ptr") u32 di_ptr(void) { return DI_OFF; }
WEXPORT("tick") u32 tick(void) { return H_T; }
WEXPORT("pop_tick") u32 pop_tick(void) { return H_P; }
WEXPORT("drops") u32 drops(void) { return H_ND; }
WEXPORT("heal_err") u32 heal_err(void) { return H_HEAL; }
WEXPORT("nvort") u32 nvort(void) { return M_N; }

/* check aids: two 32-bit word-FNV lanes over the canonical bytes (as ve2_host.js digest), and a snapshot compare */
WEXPORT("canon_hash") u64 canon_hash(void) {
  const u32 *w = W32(CAN0);
  u32 h = 0x811c9dc5u, g = 0x9747b28cu;
  for (u32 i = 0; i < (CAN1 - CAN0) / 4u; i++) { u32 x = w[i]; h = (h ^ x) * 0x01000193u; g = (g ^ x) * 0x5bd1e995u; g ^= g >> 13; }
  return ((u64)h << 32) | g;
}
WEXPORT("snap") void snap(void) {
  const u32 *s = W32(CAN0); u32 *d = W32(SNAP_OFF);
  for (u32 i = 0; i < (CAN1 - CAN0) / 4u; i++) d[i] = s[i];
}
WEXPORT("snap_diff") u32 snap_diff(void) {   /* differing bytes vs the snapshot */
  const unsigned char *s = (const unsigned char *)(MEMBASE + CAN0), *d = (const unsigned char *)(MEMBASE + SNAP_OFF);
  u32 n = 0;
  for (u32 i = 0; i < CAN1 - CAN0; i++) n += s[i] != d[i];
  return n;
}
