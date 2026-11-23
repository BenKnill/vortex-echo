// Vortex Echo v5.8w2 (2026-10-20): v5.8 with the point vortices stepped by ve_core.wasm (VAB tasks/bubble-echo/vortex,
// sha256 72fe0ba2...) and the pop's state update stepped by ve2_core.wasm (tasks/bubble-echo/vortex2), both digest-checked
// on load. The GPU tracer film and all drawing are v5.8 (06fc5b1d). Dynamics URL knobs of v5.8 have no effect here.
// Vortex Echo (prototype B of the bubble pivot study, 2026-10-19). Unverified, browser-only.
// Swirl: ~540 point vortices on the unit sphere (regularised spherical Biot-Savart), integrated in 32-bit integers
// with the Fredkin leapfrog (a,b) <- (b, a + R(2 dt f(b))). The film thickness is carried by a Lagrangian mesh of
// ~400k integer tracers (same Fredkin leapfrog, on the GPU, RGBA32I textures); its triangles carry a procedural
// initial thickness by their starting position, rasterised into a cube map each frame.
// Pop: a rim of 2048 beads in geodesic polar coordinates about the puncture (Fredkin leapfrog, speed = Taylor-Culick
// v ~ h^-1/2 from the local thickness), kinematic fingers, and droplets as integer kick-drift particles with birth
// ticks so that shedding undoes itself exactly on reversal.
'use strict';
(function () {
  const Q = new URLSearchParams(location.search);
  const DEMO = Q.get('demo') === '1', MANUAL = Q.get('clock') === 'manual';
  const MESH_N = Math.max(32, Math.min(384, +(Q.get('n') || 256)));
  const FACE = Math.max(256, Math.min(2048, +(Q.get('face') || 1024)));
  const SHEAR = true;          // tracers: one-step shear splitting (v1 drops the leapfrog option: its dt must stay fixed)
  const SEED = Math.max(1, Math.min(9999, Math.floor(+(Q.get('seed') || 1))));
  const MUTANT = Q.get('mutant') === '1';   // control: a deliberately broken un-birth
  const FIN57 = Q.get('fin') !== '56';   // v5.7 finale (fewer, larger drops, no burst); &fin=56 = v5.6's
  // swirl clock: the vortex Fredkin leapfrog always steps dt_s = DT/QSUB (so its dt never changes); a swirl tick runs QSUB
  // substeps and a pop tick runs PSUB, a fixed rational clock ratio PSUB/QSUB (default 1/16 = 6.25 %) in integer substeps
  const CLK = (Q.get('clk') || '1/16').split('/').map(v => Math.floor(+v));
  const QSUB = 16, PSUB = 1;   // purist round 2: fixed by the module (clk is ignored)
  const SV = 8388608;          // 2^23: vortex + tracer fixed point, unit sphere radius (float32 stays exact below 2^24)
  const SR = 16777216;         // 2^24: rim geodesic radius, radians
  const SD = 1048576;          // 2^20: droplet coordinates, bubble radius 1
  const DT = 1 / 60;           // swirl time per tick
  const DELTA2 = 0.0025;       // Biot-Savart regularisation (core ~ 0.07 rad)
  const NVMAX = 640;
  const M = 2048, DMAX = 16384, REC = 12, MF = 128, FS = M / MF;   // rim beads; droplet slots; ints per record; flap nodes
  const R0 = 0.015, V0 = Math.PI / 250, HREF = 420, HMIN = 140;   // rim: start radius, mean speed (rad/tick), ref thickness
  const AFTER = 520;           // ticks from puncture to end of run
  const SWIRL_MAX = 720;        // free-run auto-puncture tick (the leapfrog's computational mode grows in strain; see NOTES)
  // slow-motion factor implied by Taylor-Culick: a 4 cm bubble (R = 2 cm), gamma = 0.03 N/m, film 420 nm -> v = 12 m/s
  const SLOWMO = Math.round((1 / 60) / (V0 * 0.02 / Math.sqrt(2 * 0.03 / (1000 * HREF * 1e-9))) / 10) * 10;
  const SEEDC = [[-24, 27], [-40, 12], [-10, 40], [-55, -5], [15, 30], [-30, -25], [30, 10], [-65, 30]];
  const DEMO_POP = Math.max(60, Math.floor(+(Q.get('pop') || 540))), DEMO_C = Q.get('at') ? Q.get('at').split(',').map(Number) : SEEDC[(SEED - 1) % SEEDC.length];
  const GD = 1;                // gravity kick per tick on droplets (integer, slow-motion scale)
  const PI = Math.PI, TAU = 2 * PI, D2R = PI / 180;
  const HW = 512, HH = 256;    // lat-lon thickness map read back at the puncture (rim speed)

  const $ = id => document.getElementById(id);
  const errBox = $('err');
  const fail = m => { errBox.textContent += m + '\n'; errBox.style.display = 'block'; console.error(m); };
  window.addEventListener('error', e => fail('error: ' + e.message));

  // ---------- small vector / matrix helpers ----------
  const sph = (lon, lat) => { const lo = lon * D2R, la = lat * D2R; return [Math.cos(la) * Math.sin(lo), Math.sin(la), Math.cos(la) * Math.cos(lo)]; };
  const cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
  const dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
  const norm = a => { const l = Math.hypot(a[0], a[1], a[2]); return [a[0] / l, a[1] / l, a[2] / l]; };
  const frameAt = c => { const up = Math.abs(c[1]) < 0.95 ? [0, 1, 0] : [1, 0, 0]; const e1 = norm(cross(up, c)); return [e1, cross(c, e1)]; };
  function mulberry(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
  const hash2 = (a, b) => { let h = Math.imul(a ^ 0x9E3779B9, 0x85EBCA6B) ^ Math.imul(b + 0x632BE5AB, 0xC2B2AE35); h ^= h >>> 15; h = Math.imul(h, 0x2C1B3C6D); h ^= h >>> 12; return (h >>> 0) / 4294967296; };
  function persp(fy, asp, n, f) { const t = 1 / Math.tan(fy / 2); return [t / asp, 0, 0, 0, 0, t, 0, 0, 0, 0, (f + n) / (n - f), -1, 0, 0, 2 * f * n / (n - f), 0]; }
  function lookAt(e, c, up) { const z = norm([e[0] - c[0], e[1] - c[1], e[2] - c[2]]), x = norm(cross(up, z)), y = cross(z, x);
    return { m: [x[0], y[0], z[0], 0, x[1], y[1], z[1], 0, x[2], y[2], z[2], 0, -dot(x, e), -dot(y, e), -dot(z, e), 1], x, y, z }; }
  function mul(a, b) { const o = new Array(16); for (let c = 0; c < 4; c++) for (let r = 0; r < 4; r++) { let s = 0; for (let k = 0; k < 4; k++) s += a[k * 4 + r] * b[c * 4 + k]; o[c * 4 + r] = s; } return o; }
  function inv(m) { const a = m, o = new Array(16);
    o[0] = a[5] * a[10] * a[15] - a[5] * a[11] * a[14] - a[9] * a[6] * a[15] + a[9] * a[7] * a[14] + a[13] * a[6] * a[11] - a[13] * a[7] * a[10];
    o[4] = -a[4] * a[10] * a[15] + a[4] * a[11] * a[14] + a[8] * a[6] * a[15] - a[8] * a[7] * a[14] - a[12] * a[6] * a[11] + a[12] * a[7] * a[10];
    o[8] = a[4] * a[9] * a[15] - a[4] * a[11] * a[13] - a[8] * a[5] * a[15] + a[8] * a[7] * a[13] + a[12] * a[5] * a[11] - a[12] * a[7] * a[9];
    o[12] = -a[4] * a[9] * a[14] + a[4] * a[10] * a[13] + a[8] * a[5] * a[14] - a[8] * a[6] * a[13] - a[12] * a[5] * a[10] + a[12] * a[6] * a[9];
    o[1] = -a[1] * a[10] * a[15] + a[1] * a[11] * a[14] + a[9] * a[2] * a[15] - a[9] * a[3] * a[14] - a[13] * a[2] * a[11] + a[13] * a[3] * a[10];
    o[5] = a[0] * a[10] * a[15] - a[0] * a[11] * a[14] - a[8] * a[2] * a[15] + a[8] * a[3] * a[14] + a[12] * a[2] * a[11] - a[12] * a[3] * a[10];
    o[9] = -a[0] * a[9] * a[15] + a[0] * a[11] * a[13] + a[8] * a[1] * a[15] - a[8] * a[3] * a[13] - a[12] * a[1] * a[11] + a[12] * a[3] * a[9];
    o[13] = a[0] * a[9] * a[14] - a[0] * a[10] * a[13] - a[8] * a[1] * a[14] + a[8] * a[2] * a[13] + a[12] * a[1] * a[10] - a[12] * a[2] * a[9];
    o[2] = a[1] * a[6] * a[15] - a[1] * a[7] * a[14] - a[5] * a[2] * a[15] + a[5] * a[3] * a[14] + a[13] * a[2] * a[7] - a[13] * a[3] * a[6];
    o[6] = -a[0] * a[6] * a[15] + a[0] * a[7] * a[14] + a[4] * a[2] * a[15] - a[4] * a[3] * a[14] - a[12] * a[2] * a[7] + a[12] * a[3] * a[6];
    o[10] = a[0] * a[5] * a[15] - a[0] * a[7] * a[13] - a[4] * a[1] * a[15] + a[4] * a[3] * a[13] + a[12] * a[1] * a[7] - a[12] * a[3] * a[5];
    o[14] = -a[0] * a[5] * a[14] + a[0] * a[6] * a[13] + a[4] * a[1] * a[14] - a[4] * a[2] * a[13] - a[12] * a[1] * a[6] + a[12] * a[2] * a[5];
    o[3] = -a[1] * a[6] * a[11] + a[1] * a[7] * a[10] + a[5] * a[2] * a[11] - a[5] * a[3] * a[10] - a[9] * a[2] * a[7] + a[9] * a[3] * a[6];
    o[7] = a[0] * a[6] * a[11] - a[0] * a[7] * a[10] - a[4] * a[2] * a[11] + a[4] * a[3] * a[10] + a[8] * a[2] * a[7] - a[8] * a[3] * a[6];
    o[11] = -a[0] * a[5] * a[11] + a[0] * a[7] * a[9] + a[4] * a[1] * a[11] - a[4] * a[3] * a[9] - a[8] * a[1] * a[7] + a[8] * a[3] * a[5];
    o[15] = a[0] * a[5] * a[10] - a[0] * a[6] * a[9] - a[4] * a[1] * a[10] + a[4] * a[2] * a[9] + a[8] * a[1] * a[6] - a[8] * a[2] * a[5];
    const d = a[0] * o[0] + a[1] * o[4] + a[2] * o[8] + a[3] * o[12]; for (let i = 0; i < 16; i++) o[i] /= d; return o; }

  // ---------- vortex scene (fixed seed) ----------
  // ---------- vortex scene: built by the module (init(seed, 120)); the page reads N and the circulations back ----------
  const AUTO = 120;
  // 2026-11-17 fix batch: the digest is checked before anything calls the module (ve_load.js does not instantiate it on a
  // mismatch either); a missing or mismatched module stops the page here, before init
  const VEC = window.VE_MOD;
  if (!VEC || !VEC.e || !VEC.ok) { fail(VEC && VEC.sha ? 'vortex_a1.wasm digest ' + VEC.sha + ' is not the expected ' + VEC.want + '; not run' : 'vortex_a1.wasm not loaded'); return; }
  { const v = VEC.e.init(SEED, AUTO); if (v !== 0) fail('init refused: ' + v); }
  const NV = window.VE_MOD.e.nvort() >>> 0;
  if (NV > NVMAX) fail('too many vortices');
  const G4 = [];   // circulation per 4 pi, from the model words CW_j = round(G4_j KV 2^20) (drawing: tracer field, vortex colours)
  { const MW = new Int32Array(window.VE_MOD.e.memory.buffer, 0x4100, 1024), kv = 2 * (DT / 16) * SV * 1048576; for (let j = 0; j < NV; j++) G4.push(MW[16 + j] / kv); }

  // ---------- integer state: views into vortex_a1.wasm memory (vortex/SPEC.md section 2; fixed memory, never grown) ----------
  const vex = VEC.e, VBUF = vex.memory.buffer, HP = vex.hdr_ptr() >>> 0;
  if (HP !== 0x4000 || (vex.va_ptr() >>> 0) !== 0x110000 || (vex.ra_ptr() >>> 0) !== 0x114000 || (vex.di_ptr() >>> 0) !== 0x120000) fail('unexpected vortex_a1 layout');
  const va = new Int32Array(VBUF, vex.va_ptr() >>> 0, 3 * NV), vb = new Int32Array(VBUF, vex.vb_ptr() >>> 0, 3 * NV), U = new Float64Array(3 * NV), XN = new Float64Array(3 * NV);
  const ST = vex.ra_ptr() >>> 0;   // RA; RB, JQ, JP, ZQ, ZP follow at 8 KiB steps (the same offsets as v5.8's ve2 state)
  const ra = new Int32Array(VBUF, ST, M), rb = new Int32Array(VBUF, vex.rb_ptr() >>> 0, M), RD = new Float64Array(M);
  const JQ = new Int32Array(VBUF, ST + 0x4000, M), JP = new Int32Array(VBUF, ST + 0x6000, M);
  const DI = new Int32Array(VBUF, vex.di_ptr() >>> 0, REC * DMAX);   // droplet: px py pz vx vy vz birth kind|parent dz deta 0 0
  const ZQ = new Int32Array(VBUF, vex.zq_ptr() >>> 0, M), ZP = new Int32Array(VBUF, ST + 0xA000, M);
  // v5.8-only arrays that the v1 pop does not have: zero-filled, so the drawing reads flat flaps, no liquid, no pools
  const FQ = new Int32Array(MF), FP = new Int32Array(MF);
  const NPOOL = 32, PPP = (M / 2) / NPOOL, RV = new Int32Array(M), POOL = new Int32Array(NPOOL), VSC = 1048576, PC = new Int32Array(NPOOL);
  const H2 = new Int32Array(VBUF, HP, 64);   // header: magic, version, T, P (-1 = none), nd, healErr, popC, frame C/E1/E2 (Q30), ...
  const CANON = new Int32Array(VBUF, 0x4000, (0x1E0000 - 0x4000) / 4);   // the canonical bytes (canon_hash covers the same)
  let nd = 0, tick = 0, popTick = -1, healErr = 0, lastHeal = -1;
  const popC = new Int32Array(VBUF, HP + 24, 3);
  function sync2() { nd = H2[4]; popTick = H2[3]; healErr = H2[5]; tick = H2[2]; }
  const canonHash = () => { const h = vex.canon_hash(); return (BigInt.asUintN(64, h)).toString(16).padStart(16, '0'); };
  let event = null;   // a click at tick 0 waits for tick 1 (SPEC 4: a puncture follows a swirl tick)
  function vortexVel(src) {
    for (let i = 0; i < NV; i++) { const x = src[3 * i], y = src[3 * i + 1], z = src[3 * i + 2], L = 1 / Math.sqrt(x * x + y * y + z * z); XN[3 * i] = x * L; XN[3 * i + 1] = y * L; XN[3 * i + 2] = z * L; }
    U.fill(0);
    for (let i = 0; i < NV; i++) {
      const xi = XN[3 * i], yi = XN[3 * i + 1], zi = XN[3 * i + 2], gi = G4[i]; let ux = 0, uy = 0, uz = 0;
      for (let j = i + 1; j < NV; j++) {
        const xj = XN[3 * j], yj = XN[3 * j + 1], zj = XN[3 * j + 2];
        const w = 1 / (1 - (xi * xj + yi * yj + zi * zj) + DELTA2);
        const cx = yj * zi - zj * yi, cy = zj * xi - xj * zi, cz = xj * yi - yj * xi;   // x_j x x_i
        const gj = G4[j] * w, gw = gi * w;
        ux += gj * cx; uy += gj * cy; uz += gj * cz;
        U[3 * j] -= gw * cx; U[3 * j + 1] -= gw * cy; U[3 * j + 2] -= gw * cz;
      }
      U[3 * i] += ux; U[3 * i + 1] += uy; U[3 * i + 2] += uz;
    }
  }
  const DTS = DT / QSUB, KV = 2 * DTS * SV;
  function vortexInit() { sync2(); }   // the module's init(seed, 120) ran above: the scene, the model and the careful first step

  // ---------- WebGL setup ----------
  const canvas = $('gl');
  const gl = canvas.getContext('webgl2', { antialias: false, alpha: false, preserveDrawingBuffer: true });
  if (!gl) { fail('WebGL2 not available'); return; }
  if (!gl.getExtension('EXT_color_buffer_float')) fail('EXT_color_buffer_float missing');
  function sh(type, src) { const s = gl.createShader(type); gl.shaderSource(s, src); gl.compileShader(s); if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) { fail(gl.getShaderInfoLog(s) + '\n' + src.split('\n').map((l, i) => (i + 1) + ': ' + l).slice(0, 400).join('\n')); } return s; }
  function prog(vs, fs) { const p = gl.createProgram(); gl.attachShader(p, sh(gl.VERTEX_SHADER, vs)); gl.attachShader(p, sh(gl.FRAGMENT_SHADER, fs)); gl.linkProgram(p); if (!gl.getProgramParameter(p, gl.LINK_STATUS)) fail(gl.getProgramInfoLog(p));
    const u = {}; const n = gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS); for (let i = 0; i < n; i++) { const info = gl.getActiveUniform(p, i); u[info.name.replace(/\[0\]$/, '')] = gl.getUniformLocation(p, info.name); } return { p, u }; }
  const PRE = `#version 300 es
precision highp float; precision highp int; precision highp sampler2D; precision highp isampler2D; precision highp samplerCube;
`;
  const VS_FULL = PRE + `out vec2 vUV; void main(){ vec2 P = vec2(gl_VertexID == 1 ? 3.0 : -1.0, gl_VertexID == 2 ? 3.0 : -1.0); vUV = P * 0.5 + 0.5; gl_Position = vec4(P, 0.0, 1.0); }`;

  // tracers: Fredkin leapfrog on RGBA32I textures; one code path for f so forward and backward round identically
  const TW = 1024, NP1 = MESH_N + 1, NVERT = 6 * NP1 * NP1, TH = Math.ceil(NVERT / TW);
  const FS_TRACER = PRE + `
layout(std140) uniform Vort { vec4 vv[${NVMAX}]; };
uniform isampler2D uA, uB; uniform int uNV, uDir; uniform float uK, uDt;
out ivec4 o;
vec3 vel(vec3 p) { vec3 n = normalize(p); vec3 u = vec3(0.0);
  for (int j = 0; j < uNV; j++) { vec4 v = vv[j]; u += (v.w / (1.0 - dot(n, v.xyz) + ${DELTA2.toFixed(6)})) * cross(v.xyz, n); }
  return u; }
void main() { ivec2 tc = ivec2(gl_FragCoord.xy); ivec4 A = texelFetch(uA, tc, 0), B = texelFetch(uB, tc, 0);
  if (uDir == 0) { vec3 n = normalize(vec3(A.xyz)); vec3 m = n + 0.5 * uDt * vel(n); o = ivec4(A.xyz + ivec3(floor(vel(m) * uK * 0.5 + 0.5)), 0); return; }
  ivec4 q = uDir > 0 ? B : A;
  ivec3 d = ivec3(floor(vel(vec3(q.xyz)) * uK + 0.5));
  o = uDir > 0 ? ivec4(A.xyz + d, 0) : ivec4(B.xyz - d, 0); }`;
  const pTracer = prog(VS_FULL, FS_TRACER);
  gl.uniformBlockBinding(pTracer.p, gl.getUniformBlockIndex(pTracer.p, 'Vort'), 0);
  const ubo = gl.createBuffer(); gl.bindBuffer(gl.UNIFORM_BUFFER, ubo); gl.bufferData(gl.UNIFORM_BUFFER, NVMAX * 16, gl.DYNAMIC_DRAW); gl.bindBufferBase(gl.UNIFORM_BUFFER, 0, ubo);
  const vortF32 = new Float32Array(NVMAX * 4);
  function uploadVortices() { for (let i = 0; i < NV; i++) { const x = vb[3 * i], y = vb[3 * i + 1], z = vb[3 * i + 2], L = 1 / Math.sqrt(x * x + y * y + z * z); vortF32[4 * i] = x * L; vortF32[4 * i + 1] = y * L; vortF32[4 * i + 2] = z * L; vortF32[4 * i + 3] = G4[i]; }
    gl.bindBuffer(gl.UNIFORM_BUFFER, ubo); gl.bufferSubData(gl.UNIFORM_BUFFER, 0, vortF32); }

  function itex(data) { const t = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, t); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32I, TW, TH, 0, gl.RGBA_INTEGER, gl.INT, data);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST); const f = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, f); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, t, 0); return { t, f }; }
  // cube-sphere mesh (equal-angle), one grid per face; seam vertices are duplicated and evolve identically
  const init32 = new Int32Array(TW * TH * 4), initF = new Float32Array(TW * TH * 4);
  const idx = new Uint32Array(6 * MESH_N * MESH_N * 6);
  (function buildMesh() {
    let v = 0, q = 0;
    for (let f = 0; f < 6; f++) { const base = v;
      for (let j = 0; j < NP1; j++) for (let i = 0; i < NP1; i++) {
        const a = Math.tan(PI / 4 * (-1 + 2 * i / MESH_N)), b = Math.tan(PI / 4 * (-1 + 2 * j / MESH_N));
        const p = norm([[1, b, -a], [-1, b, a], [a, 1, -b], [a, -1, b], [a, b, 1], [-a, b, -1]][f]);
        for (let c = 0; c < 3; c++) { init32[4 * v + c] = Math.round(p[c] * SV); initF[4 * v + c] = p[c]; } v++; }
      for (let j = 0; j < MESH_N; j++) for (let i = 0; i < MESH_N; i++) { const k = base + j * NP1 + i; idx[q++] = k; idx[q++] = k + 1; idx[q++] = k + NP1 + 1; idx[q++] = k; idx[q++] = k + NP1 + 1; idx[q++] = k + NP1; } }
    for (; v < TW * TH; v++) { init32[4 * v] = SV; initF[4 * v] = 1; }
  })();
  const T = [itex(init32), itex(null), itex(null)];
  let ia = 0, ib = 1;
  const texInit = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, texInit); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, TW, TH, 0, gl.RGBA, gl.FLOAT, initF);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  const vaoEmpty = gl.createVertexArray();
  const ibo = gl.createBuffer(); gl.bindVertexArray(vaoEmpty); gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ibo); gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, idx, gl.STATIC_DRAW); gl.bindVertexArray(null);

  // One-step alternative, exactly invertible with no parasitic mode: the flow of vortex j alone is a rotation about
  // x_j whose rate depends only on x.x_j. Per vortex: rotate into a frame with x_j on +z (two plane rotations, each three
  // integer shears, plus exact half-turn flips), rotate about z by an angle that depends only on Z (three shears; Z is
  // untouched by them), then undo the frame shears exactly. Every piece is x += R(c*y); its inverse is x -= R(c*y).
  // Vortices are applied in sequence (Lie-Trotter splitting), reversed order when stepping back.
  const FS_SHEAR = PRE + `
uniform isampler2D uB; uniform sampler2D uR; uniform int uNV, uDir; uniform float uDt;
out ivec4 o;
int R(float v) { return int(floor(v + 0.5)); }
void main() { ivec2 tc = ivec2(gl_FragCoord.xy); ivec3 X = texelFetch(uB, tc, 0).xyz;
  for (int i = 0; i < uNV; i++) {
    int j = uDir > 0 ? i : uNV - 1 - i;
    vec4 c = texelFetch(uR, ivec2(2 * j, 0), 0), e = texelFetch(uR, ivec2(2 * j + 1, 0), 0);
    if (e.x > 0.5) { X.x = -X.x; X.y = -X.y; }
    X.x += R(c.x * float(X.y)); X.y += R(c.y * float(X.x)); X.x += R(c.x * float(X.y));
    if (e.y > 0.5) { X.x = -X.x; X.z = -X.z; }
    X.z += R(c.z * float(X.x)); X.x += R(c.w * float(X.z)); X.z += R(c.z * float(X.x));
    float s = float(X.z) * ${(1 / 8388608).toExponential(8)};
    float th = uDt * e.z / (1.0 - s + ${DELTA2.toFixed(6)}), h = 0.5 * th;
    float ta = -(h + h * h * h * 0.33333333), sn = th - th * th * th * 0.16666667;
    if (uDir > 0) { X.x += R(ta * float(X.y)); X.y += R(sn * float(X.x)); X.x += R(ta * float(X.y)); }
    else          { X.x -= R(ta * float(X.y)); X.y -= R(sn * float(X.x)); X.x -= R(ta * float(X.y)); }
    X.z -= R(c.z * float(X.x)); X.x -= R(c.w * float(X.z)); X.z -= R(c.z * float(X.x));
    if (e.y > 0.5) { X.x = -X.x; X.z = -X.z; }
    X.x -= R(c.x * float(X.y)); X.y -= R(c.y * float(X.x)); X.x -= R(c.x * float(X.y));
    if (e.x > 0.5) { X.x = -X.x; X.y = -X.y; }
  }
  o = ivec4(X, 0); }`;
  const pShear = prog(VS_FULL, FS_SHEAR);
  const rotTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, rotTex); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, 2 * NVMAX, 1, 0, gl.RGBA, gl.FLOAT, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  const rotF32 = new Float32Array(8 * NVMAX);
  function uploadRot() {
    for (let i = 0; i < NV; i++) {
      const x = vb[3 * i], y = vb[3 * i + 1], z = vb[3 * i + 2], L = Math.sqrt(x * x + y * y + z * z), ux = x / L, uy = y / L, uz = z / L;
      let ph = Math.atan2(uy, ux), fz = 0; if (Math.abs(ph) > PI / 2) { fz = 1; ph -= Math.sign(ph) * PI; }
      const g1 = -ph, rho = Math.hypot(ux, uy); let th = Math.atan2(rho, uz), fy = 0; if (th > PI / 2) { fy = 1; th -= PI; }
      const g2 = -th, o = 8 * i;
      rotF32[o] = -Math.tan(g1 / 2); rotF32[o + 1] = Math.sin(g1); rotF32[o + 2] = -Math.tan(g2 / 2); rotF32[o + 3] = Math.sin(g2);
      rotF32[o + 4] = fz; rotF32[o + 5] = fy; rotF32[o + 6] = G4[i]; rotF32[o + 7] = 0;
    }
    gl.bindTexture(gl.TEXTURE_2D, rotTex); gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, 2 * NVMAX, 1, gl.RGBA, gl.FLOAT, rotF32);
  }
  function shearPass(dir, dt) {
    const free = (ib + 1) % 3;
    gl.bindFramebuffer(gl.FRAMEBUFFER, T[free].f); gl.viewport(0, 0, TW, TH); gl.disable(gl.BLEND); gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pShear.p);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, T[ib].t); gl.uniform1i(pShear.u.uB, 0);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, rotTex); gl.uniform1i(pShear.u.uR, 1);
    gl.uniform1i(pShear.u.uNV, NV); gl.uniform1i(pShear.u.uDir, dir); gl.uniform1f(pShear.u.uDt, dt);
    gl.bindVertexArray(vaoEmpty); gl.drawArrays(gl.TRIANGLES, 0, 3);
    ib = free; ia = free; cubeDirty = true;
  }
  function tracerPass(dir, dt) {   // dir: +1 forward, -1 backward, 0 = careful first step (b from a); dt: swirl time of this pass
    if (SHEAR) { if (dir === 0) { ia = 0; ib = 0; cubeDirty = true; return; } uploadRot(); return shearPass(dir, dt); }
    const free = 3 - ia - ib;
    gl.bindFramebuffer(gl.FRAMEBUFFER, T[dir === 0 ? 1 : free].f); gl.viewport(0, 0, TW, TH);
    gl.disable(gl.BLEND); gl.disable(gl.DEPTH_TEST);
    gl.useProgram(pTracer.p);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, T[ia].t); gl.uniform1i(pTracer.u.uA, 0);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, dir === 0 ? T[ia].t : T[ib].t); gl.uniform1i(pTracer.u.uB, 1);
    gl.uniform1i(pTracer.u.uNV, NV); gl.uniform1i(pTracer.u.uDir, dir); gl.uniform1f(pTracer.u.uK, KV); gl.uniform1f(pTracer.u.uDt, DT);
    gl.bindVertexArray(vaoEmpty); gl.drawArrays(gl.TRIANGLES, 0, 3);
    if (dir > 0) { ia = ib; ib = free; } else if (dir < 0) { ib = ia; ia = free; }
    cubeDirty = true;
  }

  // thickness cube map from the deformed mesh: each face is a gnomonic projection (great circles -> straight lines)
  const VS_CUBE = PRE + `uniform isampler2D uA, uB; uniform sampler2D uInit; uniform int uFace;
out vec3 vI;
// draw the midpoint of the leapfrog pair (a, b): it cancels the leapfrog's odd-even (parasitic) zigzag to first order
// vertices whose pair has split far apart (leapfrog computational mode grown in strong strain) are pushed behind
void main() { ivec2 tc = ivec2(gl_VertexID % ${TW}, gl_VertexID / ${TW}); vec3 A = vec3(texelFetch(uA, tc, 0).xyz), B = vec3(texelFetch(uB, tc, 0).xyz); vec3 p = A + B; vI = texelFetch(uInit, tc, 0).xyz;
  float bad = length(B - A) > ${(0.016 * 8388608).toFixed(1)} ? 1.0 : 0.0;
  float ma, sc, tt;
  if (uFace == 0) { ma = p.x; sc = -p.z; tt = -p.y; } else if (uFace == 1) { ma = -p.x; sc = p.z; tt = -p.y; }
  else if (uFace == 2) { ma = p.y; sc = p.x; tt = p.z; } else if (uFace == 3) { ma = -p.y; sc = p.x; tt = -p.z; }
  else if (uFace == 4) { ma = p.z; sc = p.x; tt = -p.y; } else { ma = -p.z; sc = -p.x; tt = -p.y; }
  gl_Position = vec4(sc, tt, (bad * 0.6 - 0.3) * ma, ma); }`;
  const NOISE = `
float hash3(vec3 p) { p = fract(p * 0.3183099 + vec3(0.71, 0.113, 0.419)); p *= 17.0; return fract(p.x * p.y * p.z * (p.x + p.y + p.z)); }
float vnoise(vec3 x) { vec3 i = floor(x), f = fract(x); f = f * f * (3.0 - 2.0 * f);
  return mix(mix(mix(hash3(i), hash3(i + vec3(1,0,0)), f.x), mix(hash3(i + vec3(0,1,0)), hash3(i + vec3(1,1,0)), f.x), f.y),
             mix(mix(hash3(i + vec3(0,0,1)), hash3(i + vec3(1,0,1)), f.x), mix(hash3(i + vec3(0,1,1)), hash3(i + vec3(1,1,1)), f.x), f.y), f.z); }
float fbm(vec3 p) { float s = 0.0, a = 0.5; for (int k = 0; k < 5; k++) { s += a * vnoise(p); p = p * 2.03 + vec3(1.7, 9.2, 3.1); a *= 0.5; } return s; }
// initial film thickness (nm): drained (thin silver/black on top, thicker coloured bands below), streaked
float h0(vec3 p) {
  float y = p.y, t = clamp(0.5 * (1.0 - y), 0.0, 1.0);
  float warp = fbm(vec3(2.2 * p.x, 2.2 * p.y, 2.2 * p.z) + 4.0) - 0.5;
  float t2 = clamp(t + 0.10 * warp, 0.0, 1.0);
  float h = 55.0 + 780.0 * pow(t2, 1.1);
  float streak = fbm(vec3(5.0 * p.x, 24.0 * p.y, 5.0 * p.z) + 1.3) - 0.5;
  float fine = fbm(vec3(14.0 * p.x, 60.0 * p.y, 14.0 * p.z) + 7.1) - 0.5;
  h += (150.0 * streak + 55.0 * fine) * (0.25 + t);
  float cap = smoothstep(0.80, 0.90, y + 0.08 * (fbm(p * 7.0) - 0.5));
  h = mix(h, 18.0, cap);
  return clamp(h, 8.0, 1550.0); }
`;
  // the flow is area-preserving, so a triangle whose drawn area is far larger than its material area is a mesh failure
  // (its vertices straddle a separatrix and its straight edges no longer follow the curved material lines): draw it behind
  const FS_CUBE = PRE + `uniform samplerCube uH0; in vec3 vI; out vec4 o;
void main() { vec3 dx = dFdx(vI), dy = dFdy(vI); vec2 st = gl_FragCoord.xy * ${(2 / FACE).toFixed(8)} - 1.0;
  float J = length(cross(dx, dy)), J0 = ${(4 / (FACE * FACE)).toExponential(6)} / pow(1.0 + dot(st, st), 1.5), ratio = J / J0;
  gl_FragDepth = ratio < 0.3 ? 0.95 - 0.5 * clamp(ratio / 0.3, 0.0, 1.0) * 0.1 : gl_FragCoord.z;
  o = vec4(texture(uH0, vI).r, 0.0, 0.0, 1.0); }`;
  const pCube = prog(VS_CUBE, FS_CUBE);
  // the initial thickness, baked once into a static cube map (each face texel -> its direction, GL cube conventions)
  const FS_H0 = PRE + NOISE + `uniform int uFace; out vec4 o;
void main() { vec2 q = gl_FragCoord.xy * ${(2 / FACE).toFixed(8)} - 1.0; float sc = q.x, tc = q.y; vec3 d;
  if (uFace == 0) d = vec3(1.0, -tc, -sc); else if (uFace == 1) d = vec3(-1.0, -tc, sc); else if (uFace == 2) d = vec3(sc, 1.0, tc);
  else if (uFace == 3) d = vec3(sc, -1.0, -tc); else if (uFace == 4) d = vec3(sc, -tc, 1.0); else d = vec3(-sc, -tc, -1.0);
  o = vec4(h0(normalize(d)), 0.0, 0.0, 1.0); }`;
  const pH0 = prog(VS_FULL, FS_H0);
  const h0Tex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_CUBE_MAP, h0Tex);
  for (let f = 0; f < 6; f++) gl.texImage2D(gl.TEXTURE_CUBE_MAP_POSITIVE_X + f, 0, gl.R16F, FACE, FACE, 0, gl.RED, gl.HALF_FLOAT, null);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  { const fb = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, fb); gl.useProgram(pH0.p); gl.viewport(0, 0, FACE, FACE); gl.disable(gl.DEPTH_TEST); gl.disable(gl.BLEND);
    gl.bindVertexArray(gl.createVertexArray());
    for (let f = 0; f < 6; f++) { gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_CUBE_MAP_POSITIVE_X + f, h0Tex, 0); gl.uniform1i(pH0.u.uFace, f); gl.drawArrays(gl.TRIANGLES, 0, 3); }
    gl.bindVertexArray(null); }
  const cubeTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_CUBE_MAP, cubeTex);
  const cubeFB = [], cubeDepth = gl.createRenderbuffer(); gl.bindRenderbuffer(gl.RENDERBUFFER, cubeDepth); gl.renderbufferStorage(gl.RENDERBUFFER, gl.DEPTH_COMPONENT16, FACE, FACE);
  gl.bindTexture(gl.TEXTURE_CUBE_MAP, cubeTex);
  for (let f = 0; f < 6; f++) { gl.texImage2D(gl.TEXTURE_CUBE_MAP_POSITIVE_X + f, 0, gl.R16F, FACE, FACE, 0, gl.RED, gl.HALF_FLOAT, null);
    const fb = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, fb); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_CUBE_MAP_POSITIVE_X + f, cubeTex, 0);
    gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, cubeDepth); cubeFB.push(fb); }
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
  gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_CUBE_MAP, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  let cubeDirty = true;
  function renderCube() {
    gl.useProgram(pCube.p); gl.disable(gl.BLEND); gl.enable(gl.DEPTH_TEST); gl.depthFunc(gl.LESS); gl.depthMask(true); gl.disable(gl.CULL_FACE);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, T[ib].t); gl.uniform1i(pCube.u.uB, 0);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, texInit); gl.uniform1i(pCube.u.uInit, 1);
    gl.activeTexture(gl.TEXTURE2); gl.bindTexture(gl.TEXTURE_2D, T[ia].t); gl.uniform1i(pCube.u.uA, 2);
    gl.activeTexture(gl.TEXTURE3); gl.bindTexture(gl.TEXTURE_CUBE_MAP, h0Tex); gl.uniform1i(pCube.u.uH0, 3);
    gl.bindVertexArray(vaoEmpty);
    for (let f = 0; f < 6; f++) { gl.bindFramebuffer(gl.FRAMEBUFFER, cubeFB[f]); gl.viewport(0, 0, FACE, FACE); gl.clearColor(400, 0, 0, 1); gl.clearDepth(1); gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
      gl.uniform1i(pCube.u.uFace, f); gl.drawElements(gl.TRIANGLES, idx.length, gl.UNSIGNED_INT, 0); }
    gl.bindVertexArray(null); gl.disable(gl.DEPTH_TEST); cubeDirty = false;
  }

  // lat-lon thickness map, read back at the puncture: the rim kick reads it (frozen during the pop)
  const FS_HMAP = PRE + `uniform samplerCube uCube; in vec2 vUV; out vec4 o;
void main() { float lon = (vUV.x - 0.5) * 6.2831853, lat = (vUV.y - 0.5) * 3.14159265; vec3 d = vec3(cos(lat) * sin(lon), sin(lat), cos(lat) * cos(lon)); o = vec4(texture(uCube, d).r, 0.0, 0.0, 1.0); }`;
  const pHmap = prog(VS_FULL, FS_HMAP);
  const hmapTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, hmapTex); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA32F, HW, HH, 0, gl.RGBA, gl.FLOAT, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  const hmapFB = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, hmapFB); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, hmapTex, 0);
  const HMAP = new Float32Array(HW * HH), hmapRaw = new Float32Array(HW * HH * 4);
  function readHmap() {
    renderCube();
    gl.useProgram(pHmap.p); gl.bindFramebuffer(gl.FRAMEBUFFER, hmapFB); gl.viewport(0, 0, HW, HH); gl.disable(gl.BLEND); gl.disable(gl.DEPTH_TEST);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_CUBE_MAP, cubeTex); gl.uniform1i(pHmap.u.uCube, 0);
    gl.bindVertexArray(vaoEmpty); gl.drawArrays(gl.TRIANGLES, 0, 3);
    gl.readPixels(0, 0, HW, HH, gl.RGBA, gl.FLOAT, hmapRaw);
    const tmp = new Float32Array(HW * HH);
    for (let i = 0; i < HW * HH; i++) HMAP[i] = Math.round(hmapRaw[4 * i]);   // quantise to whole nm
    for (let pass = 0; pass < 2; pass++) {                                     // blur so the rim kick is smooth
      for (let j = 0; j < HH; j++) for (let i = 0; i < HW; i++) { let s = 0; for (let d = -3; d <= 3; d++) s += HMAP[j * HW + ((i + d + HW) % HW)]; tmp[j * HW + i] = s / 7; }
      for (let j = 0; j < HH; j++) for (let i = 0; i < HW; i++) { let s = 0; for (let d = -3; d <= 3; d++) s += tmp[Math.min(HH - 1, Math.max(0, j + d)) * HW + i]; HMAP[j * HW + i] = s / 7; } }
  }
  function hAt(x, y, z) {
    const lon = Math.atan2(x, z), lat = Math.asin(Math.max(-1, Math.min(1, y)));
    const u = (lon / TAU + 0.5) * HW - 0.5, v = Math.max(0, Math.min(HH - 1.001, (lat / PI + 0.5) * HH - 0.5));
    const i0 = Math.floor(u), j0 = Math.floor(v), fu = u - i0, fv = v - j0, i = (i0 + HW) % HW, i1 = (i0 + 1 + HW) % HW;
    return (HMAP[j0 * HW + i] * (1 - fu) + HMAP[j0 * HW + i1] * fu) * (1 - fv) + (HMAP[(j0 + 1) * HW + i] * (1 - fu) + HMAP[(j0 + 1) * HW + i1] * fu) * fv;
  }

  // ---------- the pop: rim beads (Fredkin), Rayleigh-Taylor corrugation ring (kick-drift), droplet births (LIFO) ----------
  // Physics (Lhuissier & Villermaux 2009/2012, "Bursting bubble aerosols", JFM 696): the hole opens at the Culick speed V;
  // the rim, following the curved cap, feels a centripetal acceleration a = V^2/R, which makes the rim Rayleigh-Taylor
  // unstable. Corrugations grow at the most unstable wavelength lambda ~ 2 pi sqrt(3 sigma/(rho a)) = 7.7 sqrt(R h); their
  // crests grow into ligaments, which pinch off drops (Rayleigh-Plateau). Here the corrugation is a ring of integer
  // oscillators (one per bead, height zeta normal to the film) with the dispersion s^2(k) = A k^2 - B k^4 tuned so that
  // the peak sits at the local RT wavenumber and growth rate. Every update is a shear (x += R(f(others))), and each drop
  // birth is pushed on a LIFO stack with what it took from its parent, so reversal un-births it exactly.
  const COS = new Float64Array(M), SIN = new Float64Array(M); for (let k = 0; k < M; k++) { COS[k] = Math.cos(TAU * k / M); SIN[k] = Math.sin(TAU * k / M); }
  let C = [0, 0, 1], E1 = [1, 0, 0], E2 = [0, 1, 0];
  const SZ = 16777216;          // 2^24: corrugation height per bubble radius
  const qp = (k, d) => +(Q.get('rt.' + k) || d);
  const RT = { ns: 4, g: qp('g', 0.8), lam: qp('lam', 0.85), cs: qp('cs', 0.5), cb: qp('cb', 0.35), noise: qp('noise', 0.002), seed0: qp('seed0', 3e-7),
    zp: qp('zp', 0.03), zsk: qp('zsk', 1.6), dz: qp('dz', 0.35), de: qp('de', 0.9), on0: 0.10, on1: 0.30, smin: 0.35, spray: qp('spray', 0.025),
    tilt: qp('tilt', 0.35), back: qp('back', 0.18), bend: qp('bend', 0.75) };
  const splayFade = re => 1 - 0.9 * smooth(re, PI / 2 - 0.1, PI / 2 + 0.35);   // v4: past the equator the torn edge stays near the sphere (births and drawing)
  // v5.5 (Ben on v5.4, 123: "these outflowering petals look cool but weren't in the reference maybe a subtler version of
  // this dynamic would be ok"): the splay of the torn edge is drawn at petal times its v2-v5.4 amplitude, on a narrower band
  // (fl.w), fading further through the crossing (reff 0.6-1.4), so the edge rolls slightly outward instead of curling into
  // petals; births leave from the same subtler edge. The flapping oscillators (integer state) are unchanged. &petal=1 = v5.4.
  const PETAL = +(Q.get('petal') ?? 0.35);
  const petalF = re => PETAL >= 1 ? 1 : PETAL * (1 - 0.6 * smooth(re, 0.6, 1.4));
  // v5.5 spray jets (Ben on v5.4, 122: "no super distinct out-jetting lines of spray"); see popStepF 2b. rate per crest and
  // tick, drops per jet n0..n1, mean elevation off the surface el (rad), speeds s0..s1 of the rim speed, liquid share 1/lq
  const JET = { rate: +(Q.get('jet') ?? 0.18), n0: 4, n1: 8, el: +(Q.get('jetel') || 0.95), s0: 0.30, s1: +(Q.get('jets1') || 1.0), lq: +(Q.get('jetlq') || 16), b0: 1.2, late: +(Q.get('jetlate') ?? 0.4) };   // (b0, late: more jets early than the spray, fewer late: refs 103/105 vs 107)
  // v5.5: spray and jets are born until the pair's gap is down to 2 fend rad (v4-v5.4: the spray stopped at 0.4 rad), so the
  // last loop keeps shedding as it shrinks (fend=0.2 = v5.4)
  const FEND = +(Q.get('fend') || 0.06);
  const f01j = k => k / M;   // (0.06: stopped pairs alternate within ~0.05 of RIM_STOP; no births there)
  const SPRAYC = +(Q.get('sprayc') || 2.5);   // v4: more mist shed as the rim gathers past the equator (v3: 1.5)
  const zpOf = (k, h) => SZ * RT.zp * (0.45 + RT.zsk * hash2(k, ZSEED + 1) ** 2) * Math.sqrt(h / HREF);   // pinch length: many short, few long
  const ZA = new Float64Array(M), ZB = new Float64Array(M), ZAM = new Float64Array(M), DS2 = new Float64Array(M), ZH = new Float64Array(M), ZV = new Float64Array(M), LAP = new Float64Array(M);
  const ZSEED = 0x5EED + 977 * SEED;
  function rimPos(r, k, out) { const s = Math.sin(r), c = Math.cos(r), dx = COS[k] * E1[0] + SIN[k] * E2[0], dy = COS[k] * E1[1] + SIN[k] * E2[1], dz = COS[k] * E1[2] + SIN[k] * E2[2];
    out[0] = c * C[0] + s * dx; out[1] = c * C[1] + s * dy; out[2] = c * C[2] + s * dz;
    out[3] = -s * C[0] + c * dx; out[4] = -s * C[1] + c * dy; out[5] = -s * C[2] + c * dz; return out; }   // position, d/dr
  const P6 = new Float64Array(6);
  const RIM_STOP = PI - 0.02;
  // v4: rays may run through the antipode. Bead k and bead k ^ HALF lie on one great circle through the puncture and
  // the antipode; the film between them along it is gone once r_k + r_opp >= 2 pi. reff = (r_k + r_opp) / 2 equals r
  // for a symmetric pop, and every 'near the end' rule reads reff, so a cap pushed off the antipode by thicker film
  // shrinks as a smooth displaced lens instead of being pinned to the antipode (v3's heart/bowtie cusp).
  const HALF = M / 2, reff = (src, k) => (src[k] + src[k ^ HALF]) / (2 * SR);
  const smooth = (x, a, b) => { const t = Math.min(1, Math.max(0, (x - a) / (b - a))); return t * t * (3 - 2 * t); };
  // v4 Huygens rim. A Taylor-Culick front moves normal to itself at the local speed V(h) ~ h^-1/2. At the puncture the
  // arrival time T(x) of that front is solved once (eikonal |grad T| = 1/V, fast marching on a lat-lon grid whose
  // equator holds the puncture and the antipode), from the thickness map frozen at the puncture. Each bead keeps its
  // ray but moves along it at the speed with which the front's level set crosses the ray, ds/dt = 1/(dT/ds), read from
  // a per-ray table. The speed is a function of the bead's own position only, so the rim stays a Fredkin pair, and the
  // drawn rim is a level set of T: a smooth cap that shrinks off the antipode into a lens, with tips where fronts meet.
  const ELON = 512, ELAT = 256, EDL = TAU / ELON, EDT = PI / ELAT, NR = 512, NSS = 1024, DSS = TAU / NSS, VMAXF = 3.0;
  const ET = new Float64Array(ELON * ELAT), EF = new Float64Array(ELON * ELAT), EDONE = new Uint8Array(ELON * ELAT), ECOS = new Float64Array(ELAT);
  for (let j = 0; j < ELAT; j++) ECOS[j] = Math.cos(-PI / 2 + (j + 0.5) * EDT);
  const VT = new Float32Array(NR * NSS);
  let HK = new Float64Array(1 << 16), HV = new Int32Array(1 << 16), hn = 0;
  function hpush(key, v) { if (hn >= HK.length) { const K2 = new Float64Array(2 * HK.length), V2 = new Int32Array(2 * HK.length); K2.set(HK); V2.set(HV); HK = K2; HV = V2; }
    let i = hn++; while (i > 0) { const pa = (i - 1) >> 1; if (HK[pa] <= key) break; HK[i] = HK[pa]; HV[i] = HV[pa]; i = pa; } HK[i] = key; HV[i] = v; }
  function hpop() { const top = HV[0], key = HK[--hn], v = HV[hn]; let i = 0;
    while (true) { let c = 2 * i + 1; if (c >= hn) break; if (c + 1 < hn && HK[c + 1] < HK[c]) c++; if (HK[c] >= key) break; HK[i] = HK[c]; HV[i] = HV[c]; i = c; }
    HK[i] = key; HV[i] = v; return top; }
  function eNode(j, i, o) { const th = -PI / 2 + (j + 0.5) * EDT, la = i * EDL, ct = Math.cos(th), st = Math.sin(th), cl = Math.cos(la), sl = Math.sin(la);
    for (let c = 0; c < 3; c++) o[c] = ct * (cl * C[c] + sl * E1[c]) + st * E2[c]; return o; }
  function eUpdate(j, i) {
    const id = j * ELON + i, F = EF[id], il = j * ELON + (i + ELON - 1) % ELON, ir = j * ELON + (i + 1) % ELON;
    let a = Infinity, b = Infinity;
    if (EDONE[il]) a = ET[il]; if (EDONE[ir] && ET[ir] < a) a = ET[ir];
    if (j > 0 && EDONE[id - ELON]) b = ET[id - ELON]; if (j < ELAT - 1 && EDONE[id + ELON] && ET[id + ELON] < b) b = ET[id + ELON];
    const hx = ECOS[j] * EDL, hy = EDT;
    if (a === Infinity) return b + F * hy; if (b === Infinity) return a + F * hx;
    const t1 = Math.min(a + F * hx, b + F * hy), wa = 1 / (hx * hx), wb = 1 / (hy * hy), S = wa * a + wb * b, W = wa + wb, disc = S * S - W * (wa * a * a + wb * b * b - F * F);
    if (disc < 0) return t1; const t = (S + Math.sqrt(disc)) / W; return t >= Math.max(a, b) ? t : t1; }
  function eT(x, y, z) {
    const pc = x * C[0] + y * C[1] + z * C[2], p1 = x * E1[0] + y * E1[1] + z * E1[2], p2 = x * E2[0] + y * E2[1] + z * E2[2];
    let u = Math.atan2(p1, pc) / EDL; if (u < 0) u += ELON; const v = Math.max(0, Math.min(ELAT - 1.000001, (Math.asin(Math.max(-1, Math.min(1, p2))) + PI / 2) / EDT - 0.5));
    const i0 = Math.floor(u), fu = u - i0, ia = i0 % ELON, ib = (i0 + 1) % ELON, j0 = Math.floor(v), fv = v - j0;
    return (ET[j0 * ELON + ia] * (1 - fu) + ET[j0 * ELON + ib] * fu) * (1 - fv) + (ET[(j0 + 1) * ELON + ia] * (1 - fu) + ET[(j0 + 1) * ELON + ib] * fu) * fv; }
  let TMAX = 0;
  // v5.4 (Ben: "in the REAL film its super super consistent speed, maybe even more consistent than in ours"): vg scales the
  // thickness dependence of the front speed, V = V0 (HREF/h)^(vg/2) (vg 1 = Culick's h^-1/2 on our map, v4-v5.3). With
  // vg < 1 the front is more uniform, so the late rim is a nearly planar circle and the last film, seen edge-on, is a thin
  // bent band (ref 108) instead of a warped loop around a broad patch. The slowness is rescaled to the same area-weighted
  // mean as vg 1, so the pace is unchanged. Read at the puncture only, like the thickness map.
  const VG = +(Q.get('vg') ?? 0.15);
  function buildArrival() {
    const P = [0, 0, 0];
    let s1 = 0, sg = 0;
    for (let j = 0; j < ELAT; j++) for (let i = 0; i < ELON; i++) { const id = j * ELON + i; eNode(j, i, P); const q = HREF / Math.max(HMIN, hAt(P[0], P[1], P[2]));
      EF[id] = 1 / (V0 * Math.pow(q, 0.5 * VG)); s1 += ECOS[j] / (V0 * Math.sqrt(q)); sg += ECOS[j] * EF[id]; }
    const fk = sg > 0 ? s1 / sg : 1, F0 = fk / (V0 * Math.pow(HREF / Math.max(HMIN, hAt(C[0], C[1], C[2])), 0.5 * VG));
    hn = 0;
    for (let j = 0; j < ELAT; j++) for (let i = 0; i < ELON; i++) { const id = j * ELON + i; eNode(j, i, P);
      EF[id] *= fk; ET[id] = Infinity; EDONE[id] = 0;
      const d = Math.acos(Math.max(-1, Math.min(1, P[0] * C[0] + P[1] * C[1] + P[2] * C[2]))); if (d < 0.04) { ET[id] = d * F0; hpush(ET[id], id); } }
    while (hn > 0) { const id = hpop(); if (EDONE[id]) continue; EDONE[id] = 1; const j = (id / ELON) | 0, i = id - j * ELON;
      const nb = [j * ELON + (i + 1) % ELON, j * ELON + (i + ELON - 1) % ELON, j > 0 ? id - ELON : -1, j < ELAT - 1 ? id + ELON : -1];
      for (const q of nb) { if (q < 0 || EDONE[q]) continue; const qj = (q / ELON) | 0, t = eUpdate(qj, q - qj * ELON); if (t < ET[q]) { ET[q] = t; hpush(t, q); } } }
    TMAX = 0; for (let i = 0; i < ET.length; i++) if (ET[i] > TMAX) TMAX = ET[i];
    const vmax = VMAXF * V0, tmp = new Float64Array(NSS);
    for (let j = 0; j < NR; j++) {
      const ph = TAU * j / NR, cp = Math.cos(ph), sp = Math.sin(ph), dx = cp * E1[0] + sp * E2[0], dy = cp * E1[1] + sp * E2[1], dz = cp * E1[2] + sp * E2[2];
      let tp = eT(C[0], C[1], C[2]);
      for (let i = 0; i < NSS; i++) { const s1 = (i + 1) * DSS, c1 = Math.cos(s1), s_ = Math.sin(s1), t = eT(c1 * C[0] + s_ * dx, c1 * C[1] + s_ * dy, c1 * C[2] + s_ * dz), dT = t - tp; tp = t;
        tmp[i] = dT * vmax > DSS ? DSS / dT : vmax; }
      for (let pass = 0; pass < 2; pass++) { let prev = tmp[0]; for (let i = 0; i < NSS; i++) { const cur = tmp[i], nx = tmp[Math.min(NSS - 1, i + 1)]; tmp[i] = 0.25 * prev + 0.5 * cur + 0.25 * nx; prev = cur; } }
      for (let i = 0; i < NSS; i++) VT[j * NSS + i] = tmp[i]; }
  }
  function rimSpeed(r, k) {
    const x = k * NR / M, j0 = Math.floor(x), fj = x - j0, ja = j0 % NR, jb = (j0 + 1) % NR;
    const u = Math.max(0, Math.min(NSS - 1.000001, r / DSS - 0.5)), i0 = Math.floor(u), fi = u - i0;
    const A = VT[ja * NSS + i0] * (1 - fi) + VT[ja * NSS + i0 + 1] * fi, B = VT[jb * NSS + i0] * (1 - fi) + VT[jb * NSS + i0 + 1] * fi;
    return A * (1 - fj) + B * fj; }
  function rimDisp(src) { for (let k = 0; k < M; k++) { const r = src[k] / SR; RD[k] = reff(src, k) >= RIM_STOP ? 0 : Math.round(2 * rimSpeed(r, k) * SR); } }
  const tubeR = (r, h) => 0.0030 + 0.0055 * Math.sqrt(Math.min(1.5, r / 1.2) * Math.min(2.5, h / HREF));
  // per-bead RT coefficients from the rim radius (the kick reads r, never writes it) and the thickness frozen at the puncture
  function corrCoef(src) {
    for (let k = 0; k < M; k++) {
      const r = src[k] / SR, re = reff(src, k); if (re >= RIM_STOP || r < RT.on0) { ZA[k] = 0; ZB[k] = 0; ZAM[k] = 0; continue; }
      rimPos(r, k, P6); const h = Math.max(HMIN, hAt(P6[0], P6[1], P6[2])), V = V0 * Math.sqrt(HREF / h), a = RT.g * V * V;
      const lam = RT.lam * 1.72e-3 * Math.sqrt(h), ks = TAU / lam, on = smooth(r, RT.on0, RT.on1) * (1 - smooth(re, PI - 0.30, PI - 0.10));
      const s2 = (2 / 3) * a * ks * on, ds = TAU * Math.max(Math.abs(Math.sin(r)), RT.smin) / M;
      ZA[k] = 2 * s2 / (ks * ks); ZB[k] = s2 / (ks * ks * ks * ks); ZAM[k] = a * SZ; DS2[k] = 1 / (ds * ds); ZH[k] = h; ZV[k] = V;
    } }
  function corrKick(sign, t, sub) {   // zeta'' = clamp(-A lap zeta - B lap^2 zeta, -cb a, cs a) + weak noise; reads zeta and r only
    for (let k = 0; k < M; k++) LAP[k] = (ZQ[(k + 1) & (M - 1)] - 2 * ZQ[k] + ZQ[(k + M - 1) & (M - 1)]) * DS2[k];
    for (let k = 0; k < M; k++) {
      if (ZAM[k] === 0) continue;
      const L2 = (LAP[(k + 1) & (M - 1)] - 2 * LAP[k] + LAP[(k + M - 1) & (M - 1)]) * DS2[k];
      let F = -ZA[k] * LAP[k] - ZB[k] * L2; const am = ZAM[k];
      F = Math.max(-RT.cb * am, Math.min((ZQ[k] > 1.6 * zpOf(k, ZH[k]) ? 0 : RT.cs) * am, F)) + RT.noise * am * (hash2(k ^ ZSEED, t * 8 + sub) - 0.5);
      ZP[k] += sign * Math.round(F / RT.ns);
    } }
  function corrDrift(src, sign) { for (let k = 0; k < M; k++) if (reff(src, k) < RIM_STOP) ZQ[k] += sign * Math.round(ZP[k] / RT.ns); }   // stopped beads freeze
  // Flapping (Lhuissier & Villermaux 2009, "Destabilization of flapping sheets"; "soap films burst like flapping flags"):
  // the film near the retracting rim flaps out of its plane and splays off the sphere. A coarse ring of MF integer
  // oscillators (one per FS beads) carries the out-of-plane displacement of the torn edge: kick-drift, kick reads only
  // (FQ, r), with a long-wave dispersion peak (lobes), a weak outward bias (the edge flares) and a cap. Stylised scale.
  const FL = { ns: 4, lam: +(Q.get('fl.lam') || 0.50), g: +(Q.get('fl.g') || 1.4), bias: +(Q.get('fl.bias') || 0.03), cap: +(Q.get('fl.cap') || 0.12),
    noise: +(Q.get('fl.noise') || 0.10), seed0: +(Q.get('fl.seed0') || 6e-5), cs: 0.8, cb: 0.5 };
  const FA = new Float64Array(MF), FB = new Float64Array(MF), FAM = new Float64Array(MF), FDS2 = new Float64Array(MF), FLAP = new Float64Array(MF);
  const FSEED = 0xF1A9 + 131 * SEED;
  function flapCoef(src) {
    for (let j = 0; j < MF; j++) {
      const k = j * FS, r = src[k] / SR, re = reff(src, k); if (re >= RIM_STOP || r < RT.on0) { FA[j] = 0; FB[j] = 0; FAM[j] = 0; continue; }
      rimPos(r, k, P6); const h = Math.max(HMIN, hAt(P6[0], P6[1], P6[2])), V = V0 * Math.sqrt(HREF / h), a = FL.g * V * V;
      const ks = TAU / FL.lam, on = smooth(r, RT.on0, RT.on1) * (1 - smooth(re, PI - 0.25, PI - 0.08));
      const s2 = (2 / 3) * a * ks * on, ds = TAU * Math.max(Math.abs(Math.sin(r)), RT.smin) / MF;
      FA[j] = 2 * s2 / (ks * ks); FB[j] = s2 / (ks * ks * ks * ks); FAM[j] = a * SZ * on; FDS2[j] = 1 / (ds * ds);
    } }
  function flapKick(sign, t, sub) {
    for (let j = 0; j < MF; j++) FLAP[j] = (FQ[(j + 1) & (MF - 1)] - 2 * FQ[j] + FQ[(j + MF - 1) & (MF - 1)]) * FDS2[j];
    for (let j = 0; j < MF; j++) {
      if (FAM[j] === 0) continue;
      const L2 = (FLAP[(j + 1) & (MF - 1)] - 2 * FLAP[j] + FLAP[(j + MF - 1) & (MF - 1)]) * FDS2[j], am = FAM[j];
      let F = -FA[j] * FLAP[j] - FB[j] * L2;
      F = Math.max(-FL.cb * am, Math.min(FL.cs * am, F)) + FL.bias * am + FL.noise * am * (hash2(j ^ FSEED, t * 8 + sub) - 0.5);
      if (FQ[j] > FL.cap * SZ) F = Math.min(F, 0);
      FP[j] += sign * Math.round(F / FL.ns);
    } }
  function flapDrift(src, sign) { for (let j = 0; j < MF; j++) if (reff(src, j * FS) < RIM_STOP) FQ[j] += sign * Math.round(FP[j] / FL.ns); }
  const flapSeed = j => Math.round(FL.seed0 * SZ * (hash2(j, FSEED) - 0.3));
  function flapAt(k) { const u = k / FS, j0 = Math.floor(u), f = u - j0, j1 = (j0 + 1) & (MF - 1), jm = (j0 + MF - 1) & (MF - 1), j2 = (j0 + 2) & (MF - 1);   // Catmull-Rom
    const p0 = FQ[jm], p1 = FQ[j0 & (MF - 1)], p2 = FQ[j1], p3 = FQ[j2];
    return (p1 + 0.5 * f * (p2 - p0 + f * (2 * p0 - 5 * p1 + 4 * p2 - p3 + f * (3 * (p1 - p2) + p3 - p0)))) / SZ; }
  // the puncture: the module builds its own rim speed table; the page reads the film back only for drawing (hAt: the
  // thickness the drawn rim and thread use) and takes the drawing frame C, E1, E2 from header words 9-17 (Q30)
  function onPunctured() {
    const q = 1 / 1073741824; C = [H2[9] * q, H2[10] * q, H2[11] * q]; E1 = [H2[12] * q, H2[13] * q, H2[14] * q]; E2 = [H2[15] * q, H2[16] * q, H2[17] * q];
    readHmap(); forceRender = true;
  }
  function applyPuncture() {
    event.fresh = false;
    const c = event.c, r = vex.puncture(c[0] >>> 0, c[1] >>> 0, c[2] >>> 0); if (r !== 0) { fail('puncture refused: ' + r); return; }
    sync2(); onPunctured();
  }
  // jiggle: in-plane rim waves (a ring of integer oscillators, kick-drift, exact), driven at a few long wavelengths with a
  // strength proportional to the local rim speed: a stylised reversible home for Culick's dissipated half of the energy
  const JIGGLE = Q.get('jiggle') !== '0', JM = [23, 37, 52, 66, 81, 97], JW = new Float64Array(6), JPH = new Float64Array(6), JA = new Float64Array(6);
  const JW2 = (TAU / 36) ** 2, JKAP = 0.05, JAMP = +(Q.get('jamp') || 2.5e-6);
  function jiggleKick(sign, t) {
    if (!JIGGLE) return;
    for (let k = 0; k < M; k++) {
      const r = rb[k] / SR; if (reff(rb, k) >= RIM_STOP) continue;
      const q = JQ[k], lap = 2 * q - JQ[(k + M - 1) % M] - JQ[(k + 1) % M], ph = TAU * k / M;
      let F = 0; for (let i = 0; i < 6; i++) F += JA[i] * Math.sin(JM[i] * ph + JW[i] * t + JPH[i]);
      JP[k] += sign * Math.round(-JW2 * q - JKAP * lap + JAMP * (rimSpeed(r, k) / V0) * F * SR);
    } }
  function jiggleDrift(sign) { if (!JIGGLE) return; for (let k = 0; k < M; k++) JQ[k] += sign * JP[k]; }
  // ligament geometry at bead k for rim radius r and crest height z (radii): base on the rim tube, leaving along the outward
  // normal and trailing backward (the rim curves away under it), bending further back towards the tip
  const LG = new Float64Array(12);
  // v4: the rim's local frame from its neighbours: position, travel direction normal to the front (in the sphere's tangent
  // plane, oriented along increasing r), FEX along the front; returns the bead spacing over its nominal spacing. Spray and
  // ligaments leave along the front normal, not along the bead's ray (rays all cross at the antipode: v3's fans there).
  const FPa = new Float64Array(6), FPb = new Float64Array(6), FEX = new Float64Array(3);
  function rimFrontR(r, rp, rm, k, out) {
    const kp = (k + 1) & (M - 1), km = (k + M - 1) & (M - 1); rimPos(rp, kp, FPa); rimPos(rm, km, FPb); rimPos(r, k, out);
    let tx = FPa[0] - FPb[0], ty = FPa[1] - FPb[1], tz = FPa[2] - FPb[2]; const tl = Math.hypot(tx, ty, tz), nom = TAU * Math.max(Math.abs(Math.sin(r)), RT.smin) / M;
    const d = tx * out[0] + ty * out[1] + tz * out[2]; tx -= d * out[0]; ty -= d * out[1]; tz -= d * out[2]; const tl2 = Math.hypot(tx, ty, tz);
    if (tl2 < 1e-12) { FEX[0] = -SIN[k] * E1[0] + COS[k] * E2[0]; FEX[1] = -SIN[k] * E1[1] + COS[k] * E2[1]; FEX[2] = -SIN[k] * E1[2] + COS[k] * E2[2]; return 0; }
    tx /= tl2; ty /= tl2; tz /= tl2;
    let nx = ty * out[2] - tz * out[1], ny = tz * out[0] - tx * out[2], nz = tx * out[1] - ty * out[0];
    if (nx * out[3] + ny * out[4] + nz * out[5] < 0) { nx = -nx; ny = -ny; nz = -nz; }
    out[3] = nx; out[4] = ny; out[5] = nz; FEX[0] = tx; FEX[1] = ty; FEX[2] = tz;
    return 0.5 * tl / nom; }
  const rimFront = (src, k, out) => rimFrontR(src[k] / SR, src[(k + 1) & (M - 1)] / SR, src[(k + M - 1) & (M - 1)] / SR, k, out);
  function ligament(k, r, z, h, out, fr) {   // fr: optional front frame [position, travel] (v4); FEX then holds the along-front direction
    if (!fr) rimPos(r, k, T6); const F = fr || T6, tube = tubeR(r, h), L = z;
    const nx = F[0], ny = F[1], nz = F[2], tx = F[3], ty = F[4], tz = F[5];
    out[0] = nx * (1 + tube); out[1] = ny * (1 + tube); out[2] = nz * (1 + tube);           // base
    const ex = fr ? FEX[0] : -SIN[k] * E1[0] + COS[k] * E2[0], ey = fr ? FEX[1] : -SIN[k] * E1[1] + COS[k] * E2[1], ez = fr ? FEX[2] : -SIN[k] * E1[2] + COS[k] * E2[2];   // along the rim
    const sp = RT.tilt * (hash2(k, ZSEED + 9) - 0.5), b0 = RT.back * (0.5 + hash2(k, ZSEED + 10)), b1 = RT.bend * (0.6 + 0.8 * hash2(k, ZSEED + 11));   // splay
    let a0 = norm([nx - b0 * tx + sp * ex, ny - b0 * ty + sp * ey, nz - b0 * tz + sp * ez]), a1 = norm([nx - b1 * tx + 1.6 * sp * ex, ny - b1 * ty + 1.6 * sp * ey, nz - b1 * tz + 1.6 * sp * ez]);
    out[3] = a0[0]; out[4] = a0[1]; out[5] = a0[2]; out[6] = a1[0]; out[7] = a1[1]; out[8] = a1[2]; out[9] = L; out[10] = tube;
    return out; }
  const ligPt = (g, u, o) => { const w0 = u - 0.5 * u * u, w1 = 0.5 * u * u; for (let c = 0; c < 3; c++) o[c] = g[c] + g[9] * (w0 * g[3 + c] + w1 * g[6 + c]); return o; };
  const T6 = new Float64Array(6), TIP = new Float64Array(3);
  function pushDrop(x, y, z, vx, vy, vz, birth, kind, parent, dz, de) {
    const o = REC * nd++;
    DI[o] = Math.round(x * SD); DI[o + 1] = Math.round(y * SD); DI[o + 2] = Math.round(z * SD);
    DI[o + 3] = Math.round(vx * SD); DI[o + 4] = Math.round(vy * SD); DI[o + 5] = Math.round(vz * SD);
    DI[o + 6] = birth; DI[o + 7] = (kind << 16) | parent; DI[o + 8] = dz; DI[o + 9] = de; }
  // the film each bead swept this tick, from (ra, rb) = (r(t), r(t+1)): a shear on RV, undone by the same amount; no sweep
  // once the pair has reached the meeting threshold (its liquid has gone to the pool)
  const MEET = PI - 0.10, DPHI = TAU / M;
  // v5.5 (Ben on v5.3/v5.4: "at the very end ... a whole circle of remaining bubble just flashes to spray/large droplets").
  // v4.1-v5.4 moved every bead's liquid into its meeting pool once its pair's gap fell under 0.2 rad (MEET). With an even
  // front the last cap is a circle, every pair crossed that line within two ticks, and 3/4 of the bubble's liquid became
  // ~170 large drops at once, around the circle. Now each bead releases at its own gap 2 (mg0 + (mg1 - mg0) u_k), u_k a
  // function of the bead fixed at the puncture (not state): mostly a zip that starts at the lowest point of the last loop
  // (gravity drains rim liquid there, so it is fattest and pinches first) and runs both ways round to the top, plus patchy
  // noise, so the last loop breaks up from one end over about a dozen ticks as it shrinks and sheds its drops where it is;
  // jets and spray drain it to the end (fend). mg0 >= 0.06 keeps the release clear of the pairs that have stopped (they
  // alternate within ~0.05 of RIM_STOP). &meet=old = v5.4.
  const MG0 = +(Q.get('mg0') || 0.06), MG1 = +(Q.get('mg1') || 0.5), ZIP = +(Q.get('zip') ?? 0.7), MEETK = new Float64Array(M).fill(MEET);
  function meetSet() {   // at the puncture: E1, E2 frame the rays; near the antipode bead k sits at -C + sin r (cos phi E1 + sin phi E2)
    if (Q.get('meet') === 'old') { MEETK.fill(MEET); return; }
    const pd = Math.atan2(-E2[1], -E1[1]);   // the ray angle whose end of the loop is lowest (gravity is -y)
    for (let k = 0; k < M; k++) { let a = (TAU * k / M - pd) % TAU; if (a < 0) a += TAU; const z = Math.abs(a - PI) / PI, nz = 0.5 + vn2(k / M * 12, 0.5, 4401 + SEED, 12);   // z: 1 at the lowest bead, 0 at the top
      const u = Math.min(1, Math.max(0, ZIP * z + (1 - ZIP) * nz)); MEETK[k] = PI - (MG0 + (MG1 - MG0) * u); } }
  // v5.7: past its let-go a bead's swept film goes straight into its pool (a shear on POOL, undone by the same amount: the
  // test reads only ra, rb, which are the same when the sweep is done and undone), so the pools fill smoothly over the last
  // ticks instead of v5.6's second hand-over of every bead at the close (~700 hand-overs and ~70 large drops in 4 ticks)
  function rimSweep(sign) {
    for (let k = 0; k < M; k++) { const qm = reffM(k); if (qm >= CLOSE) continue;   // v5.6: sweep until the pair closes (v5.5 stopped at the bead's let-go: 0.8% of the film was never booked)
      const m = 0.5 * (ra[k] + rb[k]) / SR; rimPos(m, k, P6);
      const dv = sign * Math.round(VSC * Math.max(0, hAt(P6[0], P6[1], P6[2])) * Math.abs(Math.sin(m)) * DPHI * (rb[k] - ra[k]) / SR);
      if (FIN57 && qm >= MEETK[k]) POOL[((k & (HALF - 1)) / PPP) | 0] += dv; else RV[k] += dv; } }
  const VBIG = +(Q.get('vbig') || 30) * VSC;
  // v5.6 (Ben: "a droplet size/volume limit which is making the ending discontinuous"): one large drop holds at most BIGMAX
  // (drawn radius 0.0026 cbrt(v / 0.3 VBIG) stays under its 0.008 clamp); more liquid makes more drops, never a clamp
  // v5.7 (Ben on v5.6: "allow the drops to be a bit larger and varied in shape ... a bit of a burst to too many drops ... I
  // see performance judders at the end"; refs 106-110: a few larger drops and ligament fragments among the fine mist):
  // fewer, larger drops from the same liquid. Each pool aims its next drop at a size drawn log-uniformly (seeded by the pool
  // and how many drops it has shed, so the size does not re-roll every tick and favour small drops) between bigk and
  // 20 bigk VBIG, sheds at most one drop per tick, holds at most bigcap VBIG per drop, and once its stretch of rim has closed
  // sheds what is left one drop at a time on staggered ticks (leftp per tick), so no tick spawns a burst. &fin=56 = v5.6.
  const BIGK = +(Q.get('bigk') || 0.75), LEFTP = +(Q.get('leftp') || 0.12);
  const BIGMAX = (FIN57 ? +(Q.get('bigcap') || 24) : 8) * VBIG, CLOSE = PI - FEND;
  // v5.6: a pair that reaches RIM_STOP keeps a Fredkin alternation (r(t) below, r(t+1) above; one pair even creeps on), so
  // every end-of-life rule reads the larger of the pair's two values: once either is past CLOSE the pair no longer sweeps
  // film or gives births (v5.5 read r(t+1) alone, which let such a pair sweep every other tick and book new liquid)
  const reffM = k => Math.max(reff(ra, k), reff(rb, k));   // the volume scale of the large drops (about 25 beads' liquid)
  // (v5.8 popStepF / popStepB removed: the pop runs in vortex_a1.wasm)

  // ---------- stepping ----------
  // purist round 2: vortex_a1.wasm is the only state engine. tick_forward() runs the whole tick (16 vortex substeps per
  // swirl tick; pop tick = rim, jiggle, 4 x corrugation, droplets, births, 1 vortex substep; the auto puncture at tick
  // 120); tick_backward() undoes it. The GPU film tracers are drawing: v5.8's order is kept, a tracer pass in the field of
  // the vortices at the start of the tick and then the vortex substeps (now inside tick_forward); backward the reverse.
  // During the pop the tracers catch up every TSTRIDE-th pop tick with one pass of TSTRIDE * PSUB substeps, as in v5.8.
  const TSTRIDE = Math.max(1, Math.min(16, Math.floor(+(Q.get('tstride') || 4))));
  function stepF() {
    const P = popTick, t = tick;
    if (P >= 0 && t >= P) {
      if (t >= P + AFTER) return false;
      const i = t - P, a = performance.now();
      if (i % TSTRIDE === TSTRIDE - 1) tracerPass(1, TSTRIDE * PSUB * DTS);
      const b = performance.now();
      if (!vex.tick_forward()) return false;
      TM.pop += performance.now() - b; TM.sw += b - a; TM.n++;
    } else {
      uploadVortices(); tracerPass(1, QSUB * DTS);
      if (!vex.tick_forward()) return false;
    }
    sync2();
    if (P < 0 && popTick >= 0) onPunctured();                                    // the module's auto puncture
    if (event && popTick < 0 && event.tick === tick) applyPuncture();            // a click at tick 0, applied at tick 1
    return true;
  }
  function stepB() {
    const T1 = tick, P = popTick; if (T1 <= 0) return false;
    const isPop = P >= 0 && T1 > P, h0 = healErr;
    if (!vex.tick_backward()) return false;
    sync2();
    if (isPop) { const i = T1 - 1 - P; if (i % TSTRIDE === TSTRIDE - 1) tracerPass(-1, TSTRIDE * PSUB * DTS); }
    else { uploadVortices(); tracerPass(-1, QSUB * DTS); }
    if (P >= 0 && T1 === P) lastHeal = healErr - h0;                             // the un-puncture's mismatch count
    return true;
  }
  function phase() { if (popTick < 0 || tick < popTick) return 'swirl'; let done = true; for (let k = 0; k < M; k += 8) if ((reff(ra, k) + reff(rb, k)) / 2 < PI - 0.08) { done = false; break; } return done ? 'after' : 'pop'; }

  // ---------- full-state snapshot for the reversal check ----------
  // 2026-11-17 fix batch: buf.ok records whether the read really happened (no lost context, no GL error); a failed read
  // leaves the zero-filled buffer, so diffSplit then gives no GPU tracer count at all
  function readTracers(i) { const buf = new Int32Array(TW * TH * 4); for (let k = 0; k < 16 && gl.getError() !== gl.NO_ERROR; k++);
    gl.bindFramebuffer(gl.FRAMEBUFFER, T[i].f); gl.readPixels(0, 0, TW, TH, gl.RGBA_INTEGER, gl.INT, buf);
    buf.ok = !gl.isContextLost() && gl.getError() === gl.NO_ERROR; return buf; }
  function snapshot() {
    const parts = [CANON, readTracers(ib)];
    const n = parts.reduce((s, p) => s + p.length, 0), out = new Int32Array(n); let o = 0; out.bounds = []; out.trOk = parts[1].ok; for (const p of parts) { out.set(p, o); out.bounds.push(o); o += p.length; } return out; }
  const PART_NAMES = ['module state [0x4000, 0x1E0000)', 'tracers'];
  function diffParts(a, b) { const r = []; const bd = a.bounds.concat([a.length]); for (let p = 0; p < PART_NAMES.length; p++) { if (p === 1 && !(a.trOk && b.trOk)) { r.push('tracers: not compared (a read failed)'); continue; } let d = 0, first = -1; for (let i = bd[p]; i < bd[p + 1]; i++) if (a[i] !== b[i]) { d++; if (first < 0) first = i - bd[p]; } if (d) r.push(`${PART_NAMES[p]}: ${d} words differ (first at ${first})`); } return r.join('; '); }
  // 2026-11-17 fix batch: the module snapshot and the GPU tracers are counted separately (different evidence: the module
  // snapshot is what the proofs are about; the tracers are a browser measurement of drawing state, nothing proved)
  function diffSplit(a, b) { const bd = a.bounds.concat([a.length]), r = [];
    for (let p = 0; p < 2; p++) { const A = new Uint8Array(a.buffer, 4 * bd[p], 4 * (bd[p + 1] - bd[p])), B = new Uint8Array(b.buffer, 4 * bd[p], 4 * (bd[p + 1] - bd[p])); let d = 0; for (let i = 0; i < A.length; i++) if (A[i] !== B[i]) d++; r.push({ bytes: A.length, diff: d }); }
    return { mod: r[0], tr: a.trOk && b.trOk ? r[1] : null }; }   // tr null: a tracer read failed, no GPU count
  function fnv(a) { const B = new Uint8Array(a.buffer); let h = 0x811c9dc5; for (let i = 0; i < B.length; i += 1) { h ^= B[i]; h = Math.imul(h, 0x01000193); } return (h >>> 0).toString(16).padStart(8, '0'); }

  // ---------- rendering ----------
  const FS_BG = PRE + `in vec2 vUV; uniform vec2 uRes; out vec4 o;
void main() { vec2 q = (vUV - 0.5) * vec2(uRes.x / uRes.y, 1.0); float r = length(q * vec2(0.85, 1.0));
  vec3 c = mix(vec3(0.0075, 0.0085, 0.0125), vec3(0.0018, 0.0021, 0.0032), smoothstep(0.15, 0.95, r)); o = vec4(c, 1.0); }`;
  const LOOK = Q.get('look') || 'r';   // v4.2 default 'r': the dim room of Ben's references; 'c': v1-v4.1 studio; 'b': B's
  const LOOK_C = LOOK === 'c' || LOOK === 'r';   // C's Fresnel boost (kept for the room)
  // v4.6 render-only cap palette: pal=ref shifts the thickness used for the colour lookup (palo nm, scaled by palk) so
  // the cap shows the pastel magenta/green of higher interference orders, as in Ben's 18,000 fps frames, instead of
  // first-order orange/blue. The thickness itself (and so the rim speed and every integer) is unchanged.
  const PAL = Q.get('pal') || 'film', PALO = +(Q.get('palo') || (PAL === 'ref' ? 700 : 0)), PALK = +(Q.get('palk') || (PAL === 'ref' ? 0.6 : 1));
  const HCOL = `(h * ${PALK.toFixed(4)} + ${PALO.toFixed(2)})`;
  const WBACK = +(Q.get('wback') ?? 0.5);   // v5.1: share of the window seen in the back film's reflection
  const DBACK = +(Q.get('dback') ?? 0.1);   // share of the even dome seen in the back film's reflection (v5.2: 0.5 = wback; v5.2.1: 0.2; v5.3: 0.1): low keeps the front swirl crisp
  const SIDE = +(Q.get('side') ?? 3.5), EDGEW = +(Q.get('edgew') || 1.0), EDGEP = +(Q.get('edgep') || 3.5);   // v4.7: pale film edge (side 0 = v4.6)
  const ENV = `
uniform vec3 uKey, uKeyX, uKeyY, uFill, uFillX, uFillY;
vec3 envmapB(vec3 d) {
  float y = d.y;
  vec3 c = mix(vec3(0.020, 0.020, 0.024), vec3(0.42, 0.46, 0.55), smoothstep(-0.35, 0.95, y));
  c += vec3(0.20, 0.18, 0.16) * smoothstep(-0.25, -0.02, y) * (1.0 - smoothstep(-0.02, 0.30, y));
  float kd = dot(d, uKey); if (kd > 0.0) { vec3 q = d / kd - uKey; float sx = dot(q, uKeyX), sy = dot(q, uKeyY);
    float dd = pow(pow(abs(sx) / 0.36, 4.0) + pow(abs(sy) / 0.26, 4.0), 0.25); float box = 1.0 - smoothstep(0.70, 1.25, dd); c += vec3(6.0, 5.8, 5.5) * box; }
  float fd = dot(d, uFill); if (fd > 0.0) { vec3 q = d / fd - uFill; float sx = dot(q, uFillX), sy = dot(q, uFillY);
    float strip = (1.0 - smoothstep(0.05, 0.11, abs(sx))) * (1.0 - smoothstep(0.55, 0.80, abs(sy))); c += vec3(2.4, 2.6, 3.0) * strip; }
  return c; }
// candidate C's studio: broad soft dome above, bright horizon band, softbox, strip light, warm floor bounce
vec3 envmapC(vec3 d) {
  vec3 c = vec3(0.006, 0.007, 0.009);
  c += vec3(0.62, 0.66, 0.74) * smoothstep(-0.15, 0.9, d.y);
  c += vec3(0.22, 0.2, 0.18) * exp(-12.0 * d.y * d.y);
  vec3 s = normalize(vec3(-0.55, 0.55, 0.62)); vec3 a = normalize(cross(vec3(0, 1, 0), s)), bb = cross(s, a);
  float px = dot(d, a), py = dot(d, bb), pz = dot(d, s);
  c += vec3(3.2, 3.15, 3.05) * step(0.0, pz) * (1.0 - smoothstep(0.30, 0.42, abs(px / max(pz, 1e-3)))) * (1.0 - smoothstep(0.22, 0.32, abs(py / max(pz, 1e-3))));
  c += vec3(1.2, 1.3, 1.5) * smoothstep(0.955, 0.985, dot(d, normalize(vec3(0.95, 0.2, -0.25))));
  c += vec3(0.035, 0.026, 0.018) * smoothstep(0.0, -0.6, d.y);
  float fd = dot(d, uFill); if (fd > 0.0) { vec3 q = d / fd - uFill; float sx = dot(q, uFillX), sy = dot(q, uFillY);   // B's strip light: the glassy arc
    c += vec3(1.8, 1.95, 2.25) * (1.0 - smoothstep(0.05, 0.11, abs(sx))) * (1.0 - smoothstep(0.55, 0.80, abs(sy))); }
  return c; }
// v4.2 room, matched to Ben's 18,000 fps reference frames: a dim warm-grey room. The only light bright enough to show the
// film's interference colours is a broad ceiling light overhead, so the colour sits on the cap and the rest of the film is
// nearly clear. Two soft out-of-focus light pillars stand behind the bubble, a faint window strip at the side gives the
// glassy arc, and the floor is a little lighter than the walls. ROOM(d, sharp): sharp = 0 drops the lights for the
// directly seen (out-of-focus) background.
uniform float uPilS; uniform float uCeil, uPil, uCeilBack, uCamAz, uSide, uWin, uDome; uniform vec2 uDomeW; uniform vec3 uCeilD, uVD, uWinD; uniform vec2 uCeilW, uWinW;
float gCeil = 1.0;   // per-use share of the ceiling light: 1 for the front film, uCeilBack for the back film, 0 for the backdrop
uniform mat3 uEnvR;   // v4.8: the room counter-rotated against the camera roll, so it stays upright on screen
vec3 envmapR(vec3 d) {
  d = uEnvR * d;
  vec3 c = vec3(0.0078, 0.0072, 0.0066);
  c += vec3(0.010, 0.009, 0.008) * smoothstep(-0.36, -0.52, d.y);
  // the ceiling light is above and behind the bubble: the front film's top reflects it, the back film's bottom does not
  c += vec3(1.0, 0.98, 0.95) * uCeil * gCeil * smoothstep(uCeilW.x, uCeilW.y, dot(d, uCeilD));
  // v5.1: a large soft window behind and above the camera (win; 0 = v5.0). The film's face reflects it, so its thickness
  // swirls show as interference colour over much of the bubble instead of only on the top arc; the film stays clear
  // (the reflection is added, nothing behind is hidden). Not seen directly (behind the camera; off for the backdrop).
  // v5.2: an even diffuse dome filling the hemisphere around the camera (dome; 0 = v5.1 reference). Soap-film
  // photographers reflect a large, even source off the film against a dark background: every point of the face then
  // reflects nearly the same radiance, so the colour is the thin-film reflectance itself and the swirls show everywhere,
  // with no hotspot. It fades out (domew, cosines to the view axis) before the reflected rays turn sideways, so the
  // outline is not brightened further; the room behind the bubble stays dark (off for the backdrop).
  // v5.2.1: domew -0.75,0 (v5.2: -0.1,0.65). Dome x Fresnel is flat to 70% of the face radius and fades over 75-95%,
  // where the pale side-wall edge takes over, so there is no darker ring at 80%; the back film sees the dome at dback.
  c += vec3(0.97, 0.98, 1.0) * uDome * step(0.001, gCeil) * mix(${DBACK.toFixed(3)}, 1.0, step(0.999, gCeil)) * smoothstep(uDomeW.x, uDomeW.y, dot(d, uVD));
  c += vec3(1.0, 0.99, 0.97) * uWin * step(0.001, gCeil) * mix(${WBACK.toFixed(3)}, 1.0, step(0.999, gCeil)) * smoothstep(uWinW.x, uWinW.y, dot(d, uWinD));   // the back film's (inverted) reflection at wback
  float az = atan(d.x, -d.z) - uCamAz; az = az - 6.2831853 * floor((az + 3.14159265) / 6.2831853); float up = smoothstep(-0.44, -0.12, d.y) * (1.0 - 0.35 * smoothstep(0.1, 0.6, d.y));
  c += vec3(0.046, 0.045, 0.043) * uPil * up * (exp(-pow((az / uPilS + 0.38) / 0.075, 2.0)) + 0.85 * exp(-pow((az / uPilS - 0.23) / 0.08, 2.0)));

  float fd = dot(d, uFill); if (fd > 0.0) { vec3 q = d / fd - uFill; float sx = dot(q, uFillX), sy = dot(q, uFillY);
    c += vec3(0.12, 0.13, 0.15) * (1.0 - smoothstep(0.05, 0.11, abs(sx))) * (1.0 - smoothstep(0.55, 0.80, abs(sy))); }
  return c; }
// v4.7: the side walls (directions across the view axis uVD), a lighter warm grey than the backdrop. The camera never
// sees them directly; the film reflects them only near its outline, where the reflected ray turns sideways and the
// reflection is nearly total and colourless (both faces reflect strongly at grazing): a thin pale edge all round, as in
// the refs (v4.2-v4.6 showed a dark ring there). Used only through the film's white edge term.
vec3 sideWall(vec3 d) { d = uEnvR * d; float s = 1.0 - dot(d, uVD) * dot(d, uVD); return vec3(0.034, 0.032, 0.030) * uSide * s * s * s * (0.6 + 0.4 * smoothstep(-0.6, 0.3, d.y)); }
vec3 envmap(vec3 d) { return ${LOOK === 'r' ? 'envmapR(d)' : LOOK_C ? 'envmapC(d)' : 'envmapB(d)'}; }`;
  const FS_FILM = PRE + ENV + `
uniform mat4 uInvVP, uVP; uniform vec3 uCam; uniform samplerCube uThick; uniform sampler2D uLUT, uRim; uniform int uLayer, uPop, uM;
uniform vec3 uC, uE1, uE2; uniform float uPx, uGain, uMilk;
in vec2 vUV; out vec4 o;
void main() {
  vec2 ndc = vUV * 2.0 - 1.0; vec4 pn = uInvVP * vec4(ndc, -1.0, 1.0), pf = uInvVP * vec4(ndc, 1.0, 1.0);
  vec3 ro = uCam, rd = normalize(pf.xyz / pf.w - pn.xyz / pn.w);
  float b = dot(ro, rd), c = dot(ro, ro) - 1.0, disc = b * b - c; if (disc <= 0.0) discard;
  float t = uLayer == 1 ? -b - sqrt(disc) : -b + sqrt(disc); vec3 p = ro + t * rd;
  float dperp = sqrt(max(0.0, dot(ro, ro) - b * b)); float edge = smoothstep(0.0, 1.2 * uPx * t, 1.0 - dperp);
  float hole = 1.0;
  if (uPop == 1) { float th = acos(clamp(dot(p, uC), -1.0, 1.0)); float ph = atan(dot(p, uE2), dot(p, uE1));
    float u = fract(ph / 6.2831853) * float(uM); int k0 = int(floor(u)); float f = u - float(k0);
    float r = mix(texelFetch(uRim, ivec2(k0 % uM, 0), 0).r, texelFetch(uRim, ivec2((k0 + 1) % uM, 0), 0).r, f);
    float r2 = mix(texelFetch(uRim, ivec2((k0 + uM / 2) % uM, 0), 0).r, texelFetch(uRim, ivec2((k0 + 1 + uM / 2) % uM, 0), 0).r, f);   // the opposite ray, run through the antipode
    hole = smoothstep(r - 0.5 * uPx * t, r + 1.5 * uPx * t, th) * smoothstep(r2 - 0.5 * uPx * t, r2 + 1.5 * uPx * t, 6.2831853 - th); if (hole <= 0.0) discard; }
  vec3 n = uLayer == 1 ? p : -p; gCeil = uLayer == 1 ? 1.0 : uCeilBack;
  float ci = clamp(dot(-rd, n), 0.0, 1.0);
  float h = texture(uThick, p).r;
  float st = sqrt(1.0 - ci * ci) / 1.33, ct = sqrt(1.0 - st * st);
  vec3 film = texture(uLUT, vec2(clamp(${HCOL} / 1600.0, 0.0, 1.0), clamp((ct - 0.6) / 0.4, 0.0, 1.0))).rgb;
  float fg = pow(1.0 - ci, 5.0);
${LOOK_C ? `  vec3 R = min(film * uGain * (1.0 + 5.0 * pow(1.0 - ci, 3.0)) + vec3(0.25) * pow(1.0 - ci, 6.0) * step(30.0, h), vec3(1.0));
  R = mix(R, vec3(dot(R, vec3(0.3333)) * 1.4 + 0.035 + 0.10 * pow(1.0 - ci, 2.0)), uMilk);   // v4.9: the last cap turns milky (ref 108)
  vec3 col = envmap(reflect(rd, n)) * R + sideWall(reflect(rd, n)) * ${EDGEW.toFixed(3)} * pow(1.0 - ci, ${EDGEP.toFixed(2)});
  float a = clamp(dot(R, vec3(0.3333)), 0.0, 1.0);` : `  vec3 R = mix(film * uGain, film * uGain * 2.0 + 0.10, fg);
  vec3 col = envmap(reflect(rd, n)) * R;
  float a = clamp(dot(R, vec3(0.3333)), 0.0, 1.0) * 0.6 + 0.015;`}
  float w = (uLayer == 1 ? 1.0 : 0.8) * edge * hole;
  vec4 cp = uVP * vec4(p, 1.0); gl_FragDepth = clamp(0.5 * cp.z / cp.w + 0.5, 0.0, 1.0);
  o = vec4(col * w, a * w); }`;
  const VS_PT = PRE + `in vec4 aP; in vec4 aK; uniform mat4 uVP; uniform float uFocal; out vec4 vK;
void main() { vec4 c = uVP * vec4(aP.xyz, 1.0); gl_Position = c; gl_PointSize = clamp(2.0 * aP.w * uFocal / c.w, 1.5, 60.0); vK = aK; }`;
  const FS_PT = PRE + ENV + `in vec4 vK; uniform vec3 uCX, uCY, uCZ; out vec4 o;
void main() { vec2 q = gl_PointCoord * 2.0 - 1.0; q.y = -q.y; float r2 = dot(q, q); if (r2 > 1.0) discard;
  if (vK.z > 0.5) { o = vec4((vK.z > 1.5 ? vec3(0.25, 0.55, 1.6) : vec3(1.6, 0.35, 0.25)) * (1.0 - 0.5 * r2), 1.0); return; }
  vec3 n = vec3(q, sqrt(1.0 - r2)); vec3 rv = vec3(0.0, 0.0, -1.0) + 2.0 * n.z * n; vec3 rw = rv.x * uCX + rv.y * uCY + rv.z * uCZ;
  vec3 tv = normalize(vec3(-q * 0.8, -1.0)); vec3 tw = tv.x * uCX + tv.y * uCY + tv.z * uCZ;
  float fr = 0.03 + 0.97 * pow(1.0 - n.z, 4.0);
  vec3 col = envmap(rw) * fr + envmap(tw) * 0.55 * (1.0 - fr) + vK.x * vec3(0.10, 0.11, 0.13);
  float glint = pow(max(0.0, dot(n, normalize(vec3(-0.45, 0.55, 0.7)))), 40.0) * 6.0;
  o = vec4((col + glint) * vK.y, 1.0); }`;
  const FS_TONE = PRE + `uniform sampler2D uHdr; uniform float uExp; in vec2 vUV; out vec4 o;
void main() { vec3 c = texture(uHdr, vUV).rgb * uExp; c = 1.0 - exp(-c); c = mix(12.92 * c, 1.055 * pow(c, vec3(1.0 / 2.4)) - 0.055, step(0.0031308, c)); o = vec4(c, 1.0); }`;
  const FS_BG_R = PRE + ENV + `in vec2 vUV; uniform mat4 uInvVP; out vec4 o;
void main() { vec2 ndc = vUV * 2.0 - 1.0; vec4 pn = uInvVP * vec4(ndc, -1.0, 1.0), pf = uInvVP * vec4(ndc, 1.0, 1.0);
  vec3 rd = normalize(pf.xyz / pf.w - pn.xyz / pn.w); gCeil = 0.0; o = vec4(envmapR(rd), 1.0); }`;
  const pBg = prog(VS_FULL, LOOK === 'r' ? FS_BG_R : FS_BG), pFilm = prog(VS_FULL, FS_FILM), pPt = prog(VS_PT, FS_PT), pTone = prog(VS_FULL, FS_TONE);

  // film reflectance LUT: thickness 0..1600 nm x cos(theta_t) 0.6..1, true reflectance (linear sRGB)
  const LUTW = 512, LUTH = 32, lutData = new Float32Array(LUTW * LUTH * 4);
  for (let j = 0; j < LUTH; j++) for (let i = 0; i < LUTW; i++) { const [X, Y, Z] = FilmColor.filmXYZ(i / (LUTW - 1) * 1600, 0.6 + 0.4 * j / (LUTH - 1));
    const o = 4 * (j * LUTW + i); lutData[o] = Math.max(0, 3.2406 * X - 1.5372 * Y - 0.4986 * Z); lutData[o + 1] = Math.max(0, -0.9689 * X + 1.8758 * Y + 0.0415 * Z); lutData[o + 2] = Math.max(0, 0.0557 * X - 0.2040 * Y + 1.0570 * Z); lutData[o + 3] = 1; }
  const lutTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, lutTex); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA16F, LUTW, LUTH, 0, gl.RGBA, gl.FLOAT, lutData);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
  const rimTex = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, rimTex); gl.texImage2D(gl.TEXTURE_2D, 0, gl.R32F, M, 1, 0, gl.RED, gl.FLOAT, null);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  const rimF = new Float32Array(M);

  // points (rim beads, finger ligaments, droplets)
  const PTMAX = M + 90000 + DMAX + NVMAX, ptData = new Float32Array(PTMAX * 8);
  const ptBuf = gl.createBuffer(), vaoPt = gl.createVertexArray();
  gl.bindVertexArray(vaoPt); gl.bindBuffer(gl.ARRAY_BUFFER, ptBuf); gl.bufferData(gl.ARRAY_BUFFER, ptData.byteLength, gl.DYNAMIC_DRAW);
  const locP = gl.getAttribLocation(pPt.p, 'aP'), locK = gl.getAttribLocation(pPt.p, 'aK');
  gl.enableVertexAttribArray(locP); gl.vertexAttribPointer(locP, 4, gl.FLOAT, false, 32, 0); gl.enableVertexAttribArray(locK); gl.vertexAttribPointer(locK, 4, gl.FLOAT, false, 32, 16);
  gl.bindVertexArray(null);
  // v5.7: shaped drops (the large drops and their ligament fragments). A sprite drawn as the screen outline of an ellipsoid
  // with semi-axes r s along a 3D axis and r / sqrt(s) across it (s > 1 oblong, s < 1 oblate; volume kept), shaded with
  // the normal of that ellipse. aP: centre, r; aA: axis (unit), s; aK: glow, brightness.
  const VS_SH = PRE + `in vec4 aP; in vec4 aA; in vec4 aK; uniform mat4 uVP; uniform float uFocal; uniform vec2 uRes; out vec4 vK; out vec2 vAx; out vec2 vSc;
void main() { vec4 c = uVP * vec4(aP.xyz, 1.0); gl_Position = c; float s = max(aA.w, 0.15), a = aP.w * s, b = aP.w / sqrt(s), ppu = uFocal / c.w;
  vec4 c2 = uVP * vec4(aP.xyz + aA.xyz * a, 1.0); vec2 d = (c2.xy / c2.w - c.xy / c.w) * 0.5 * uRes; float dl = length(d);
  float f = clamp(dl / max(1e-6, a * ppu), 0.0, 1.0), al = ppu * sqrt(a * a * f * f + b * b * (1.0 - f * f)), ac = ppu * b, S = clamp(2.0 * max(al, ac) + 1.0, 1.5, 120.0);
  gl_PointSize = S; vAx = dl > 1e-5 ? d / dl : vec2(1.0, 0.0); vSc = max(vec2(al, ac), vec2(0.5)) / (0.5 * S); vK = aK; }`;
  const FS_SH = PRE + ENV + `in vec4 vK; in vec2 vAx; in vec2 vSc; uniform vec3 uCX, uCY, uCZ; out vec4 o;
void main() { vec2 q = gl_PointCoord * 2.0 - 1.0; q.y = -q.y; vec2 pr = vec2(-vAx.y, vAx.x), e = vec2(dot(q, vAx), dot(q, pr)) / vSc; float r2 = dot(e, e); if (r2 > 1.0) discard;
  vec3 n = vec3(e.x * vAx + e.y * pr, sqrt(1.0 - r2)); vec3 rv = vec3(0.0, 0.0, -1.0) + 2.0 * n.z * n; vec3 rw = rv.x * uCX + rv.y * uCY + rv.z * uCZ;
  vec3 tv = normalize(vec3(-n.xy * 0.8, -1.0)); vec3 tw = tv.x * uCX + tv.y * uCY + tv.z * uCZ;
  float fr = 0.03 + 0.97 * pow(1.0 - n.z, 4.0);
  vec3 col = envmap(rw) * fr + envmap(tw) * 0.55 * (1.0 - fr) + vK.x * vec3(0.10, 0.11, 0.13);
  float glint = pow(max(0.0, dot(n, normalize(vec3(-0.45, 0.55, 0.7)))), 40.0) * 6.0;
  o = vec4((col + glint) * vK.y, 1.0); }`;
  const pSh = prog(VS_SH, FS_SH), SHMAX = 16384, shData = new Float32Array(SHMAX * 12); let nSh = 0;
  const shBuf = gl.createBuffer(), vaoSh = gl.createVertexArray();
  gl.bindVertexArray(vaoSh); gl.bindBuffer(gl.ARRAY_BUFFER, shBuf); gl.bufferData(gl.ARRAY_BUFFER, shData.byteLength, gl.DYNAMIC_DRAW);
  for (const [nm, off] of [['aP', 0], ['aA', 16], ['aK', 32]]) { const l = gl.getAttribLocation(pSh.p, nm); gl.enableVertexAttribArray(l); gl.vertexAttribPointer(l, 4, gl.FLOAT, false, 48, off); }
  gl.bindVertexArray(null);

  // HDR target
  let hdr = null, W = 0, H = 0;
  function resize() {
    const dpr = window.devicePixelRatio || 1, w = Math.round(canvas.clientWidth * dpr), h = Math.round(canvas.clientHeight * dpr);
    if (w === W && h === H && hdr) return; W = w; H = h; canvas.width = W; canvas.height = H;
    if (hdr) { gl.deleteTexture(hdr.t); gl.deleteRenderbuffer(hdr.d); gl.deleteFramebuffer(hdr.f); }
    const t = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, t); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA16F, W, H, 0, gl.RGBA, gl.HALF_FLOAT, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
    const d = gl.createRenderbuffer(); gl.bindRenderbuffer(gl.RENDERBUFFER, d); gl.renderbufferStorage(gl.RENDERBUFFER, gl.DEPTH_COMPONENT24, W, H);
    const f = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, f); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, t, 0); gl.framebufferRenderbuffer(gl.FRAMEBUFFER, gl.DEPTH_ATTACHMENT, gl.RENDERBUFFER, d);
    hdr = { t, d, f };
  }
  // v4.4: camera elevation (deg) as a knob; Ben's references are filmed nearly level
  const EL = +(Q.get('el') || 17) * D2R, AZ = +(Q.get('az') || 0) * D2R, DIST = +(Q.get('dist') || 10), EYE = [DIST * Math.cos(EL) * Math.sin(AZ), DIST * Math.sin(EL), DIST * Math.cos(EL) * Math.cos(AZ)];
  const FOVY = 2 * Math.atan(Math.tan(Math.asin(1 / DIST)) / 0.72);
  const PILS = FOVY / (2 * Math.atan(Math.tan(Math.asin(1 / 4)) / 0.72));   // v5.4: the out-of-focus pillars keep their place in the frame with the long lens
  // v5.4: dist 10 (v1-v5.3: 4). Ben's 18,000 fps frames are taken with a long lens from far away, so the perspective is
  // nearly flat; from 4 radii the late rim's plane is seen about 11 degrees from edge-on and the last film reads as a broad
  // lens, from 10 radii about 5 degrees, a thin bent band (ref 108). The bubble keeps its size on screen (FOVY).
  const key = norm([-0.55, 0.60, 0.58]), keyX = norm(cross([0, 1, 0], key)), keyY = cross(key, keyX);
  const fill = norm([0.85, 0.15, -0.35]), fillX = norm(cross([0, 1, 0], fill)), fillY = cross(fill, fillX);
  // v4.6: dimmer light pillars (pil 0.45; v4.2-v4.5: 1); v4.7: 0.2. The refs' backdrop is a nearly flat dark warm grey (columns
  // 13-18% grey across the frame), ours had pillars at 23-27%
  const ROOM = { ceil: +(Q.get('ceil') || 1.5), pil: +(Q.get('pil') || 0.2), dir: norm((Q.get('cl') || '0.12,0.62,-0.78').split(',').map(Number)), w: (Q.get('cw') || '0.78,0.96').split(',').map(Number), back: +(Q.get('cback') || 0.15) };
  { const d = ROOM.dir, c = Math.cos(AZ), sn = Math.sin(AZ); ROOM.dirW = [d[0] * c + d[2] * sn, d[1], -d[0] * sn + d[2] * c]; }   // v4.4: the room turns with the camera
  const VD = norm(EYE);   // v4.7: unit vector towards the camera (the side walls lie across it)
  // v4.8: camera roll (deg) about the view axis, with the room counter-rotated so it stays upright: a framing knob that
  // turns the bubble on screen (the state, the puncture and the dynamics are untouched; drops' tiny sag turns with it)
  const ROLL = +(Q.get('roll') || 0) * D2R;
  const rotAx = (v, a, t) => { const c = Math.cos(t), s = Math.sin(t), d = v[0] * a[0] + v[1] * a[1] + v[2] * a[2], x = cross(a, v);
    return [v[0] * c + x[0] * s + a[0] * d * (1 - c), v[1] * c + x[1] * s + a[1] * d * (1 - c), v[2] * c + x[2] * s + a[2] * d * (1 - c)]; };
  const CUP = rotAx([0, 1, 0], VD, ROLL);
  // v5.1 lighting presets (Ben 2026-10-20: "clear beats pastel. but it would be nice if the lighting could be altered to
  // make the swirls more prominent"). 'ref' = v5.0's room. 'swirl' adds the soft window (win, at wel degrees above the
  // view axis and waz to the side, soft edges ww as cosines) and widens the ceiling light (cws), so more of the film
  // catches a bright reflection and shows its swirls. Live: PROTO.light('swirl' | 'ref'); URL: &light=swirl, or the knobs.
  const WINP = { dome: +(Q.get('dome') ?? 0.28), domew: (Q.get('domew') || '-0.75,0').split(',').map(Number), ceile: +(Q.get('ceile') ?? 0.7), win: +(Q.get('win') ?? 0.55), wel: +(Q.get('wel') ?? 24), waz: +(Q.get('waz') ?? -18), ww: (Q.get('ww') || '0.62,0.95').split(',').map(Number), cws: (Q.get('cws') || '0.62,0.93').split(',').map(Number) };
  const ROOMW0 = ROOM.w.slice();
  const LIGHT = { mode: 'ref', win: 0, ww: WINP.ww, winD: [0, 1, 0], dome: 0, domew: WINP.domew };   const CEIL0 = ROOM.ceil;
  { const hx = VD[0], hz = VD[2], hl = Math.hypot(hx, hz) || 1, e = WINP.wel * D2R, a = WINP.waz * D2R, ca = Math.cos(a), sa = Math.sin(a);
    const bx = hx / hl * ca + hz / hl * sa, bz = -hx / hl * sa + hz / hl * ca; LIGHT.winD = norm([bx * Math.cos(e), Math.sin(e), bz * Math.cos(e)]); }
  function setLight(m) { LIGHT.mode = m === 'swirl' || m === 'even' ? m : 'ref'; const sw = LIGHT.mode === 'swirl', ev = LIGHT.mode === 'even';
    LIGHT.win = sw ? WINP.win : 0; ROOM.w = sw ? WINP.cws.slice() : ROOMW0.slice(); LIGHT.dome = ev ? WINP.dome : 0; ROOM.ceil = ev ? CEIL0 * WINP.ceile : CEIL0; return LIGHT.mode; }   // v5.2: 'even' = the diffuse dome (ceile scales the ceiling accent)
  setLight(Q.get('light') || 'even');   // v5.3: even diffuse is the default (Ben on v5.2: "even diffuse is a step in the right direction! onward."); light=ref = v5.0's room
  const ENVR = (() => { const ex = rotAx([1, 0, 0], VD, -ROLL), ey = rotAx([0, 1, 0], VD, -ROLL), ez = rotAx([0, 0, 1], VD, -ROLL); return new Float32Array([...ex, ...ey, ...ez]); })();   // columns
  function setEnv(p) { gl.uniform1f(p.u.uPilS, PILS); gl.uniformMatrix3fv(p.u.uEnvR, false, ENVR); gl.uniform1f(p.u.uSide, SIDE); gl.uniform3fv(p.u.uVD, VD); gl.uniform1f(p.u.uCeil, ROOM.ceil); gl.uniform1f(p.u.uPil, ROOM.pil); gl.uniform3fv(p.u.uCeilD, ROOM.dirW); gl.uniform1f(p.u.uCamAz, -AZ); gl.uniform2fv(p.u.uCeilW, ROOM.w); gl.uniform1f(p.u.uWin, LIGHT.win); gl.uniform1f(p.u.uDome, LIGHT.dome); gl.uniform2fv(p.u.uDomeW, LIGHT.domew); gl.uniform3fv(p.u.uWinD, LIGHT.winD); gl.uniform2fv(p.u.uWinW, LIGHT.ww); gl.uniform1f(p.u.uCeilBack, ROOM.back); gl.uniform3fv(p.u.uKey, key); gl.uniform3fv(p.u.uKeyX, keyX); gl.uniform3fv(p.u.uKeyY, keyY); gl.uniform3fv(p.u.uFill, fill); gl.uniform3fv(p.u.uFillX, fillX); gl.uniform3fv(p.u.uFillY, fillY); }
  let VP = null, IVP = null, CAM = null; const TM = { pop: 0, sw: 0, n: 0, bp: 0, nb: 0 };

  // ---------- v2 pop rendering: everything below is a pure function of the integer state ----------
  // crinkle: multi-scale value noise along the rim (cycles around the hole) that evolves with the rim's travel r
  function vn2(x, y, sd, per) { const i0 = Math.floor(x), j0 = Math.floor(y), fx = x - i0, fy = y - j0, ux = fx * fx * (3 - 2 * fx), uy = fy * fy * (3 - 2 * fy);
    // v5.7 (performance): the same values as v5.6 without a closure per call or modulos in the common case
    const a = i0 >= 0 && i0 < per ? i0 : ((i0 % per) + per) % per, b = a + 1 < per ? a + 1 : (a + 1) % per, ia = a * 7919 + sd, ib = b * 7919 + sd, j1 = j0 + 1013 * sd;
    return (hash2(ia, j1) * (1 - ux) + hash2(ib, j1) * ux) * (1 - uy) + (hash2(ia, j1 + 1) * (1 - ux) + hash2(ib, j1 + 1) * ux) * uy - 0.5; }
  const CR = { N: [60, 170, 430, 1000], S: [5, 12, 26, 55], A: [+(Q.get('cr.a') || 0.0080), 0.0070, 0.0050, 0.0030] };
  function crinkle(f01, r, sd) { f01 += CRW * vn2(f01 * 9, r * 2, sd + 919, 9) + 0.4 * CRW * vn2(f01 * 31, r * 4, sd + 921, 31);   // v5.6: warped (irregular spacing)
    let c = 0; for (let o = 0; o < 4; o++) c += CR.A[o] * vn2(f01 * CR.N[o], r * CR.S[o], sd + 17 * o, CR.N[o]);
    const env = 0.25 + 1.5 * Math.max(0, vn2(f01 * 11, r * 3, sd + 303, 11) + 0.25);   // patchy: some stretches crumple, others stay smooth
    return c * env; }
  const CRW = +(Q.get('crw') ?? 0.02);   // v5.6: crinkle warp (0 = v5.5)
  function rimPosPhi(th, phi, out) { const s = Math.sin(th), c = Math.cos(th), cp = Math.cos(phi), sp = Math.sin(phi);
    const dx = cp * E1[0] + sp * E2[0], dy = cp * E1[1] + sp * E2[1], dz = cp * E1[2] + sp * E2[2];
    out[0] = c * C[0] + s * dx; out[1] = c * C[1] + s * dy; out[2] = c * C[2] + s * dz; out[3] = -s * C[0] + c * dx; out[4] = -s * C[1] + c * dy; out[5] = -s * C[2] + c * dz; return out; }
  const FLAPW = +(Q.get('fl.w') || (PETAL >= 1 ? 0.14 : 0.09)), NSUB = 4, FCOL = M / 2, FROW = 9;
  const flapPos = new Float32Array(FCOL * FROW * 10);   // position, material direction, smooth normal, crease
  const RM = new Float64Array(M), REF = new Float64Array(M), RD2 = new Float64Array(M), LF = new Float64Array(M), HMk = new Float64Array(M);
  const ED = new Float64Array(6 * (M * NSUB + 1));   // the free edge, sampled: position xyz, rim radius, brightness, size
  function edgeState() {           // per bead: drawn rim radius (with in-plane jiggle), flap lift, local thickness
    for (let k = 0; k < M; k++) { const r = (ra[k] + rb[k]) / (2 * SR); RM[k] = r; RD2[k] = r + JQ[k] / SR; LF[k] = Math.max(-0.01, flapAt(k)); }
    for (let k = 0; k < M; k++) REF[k] = 0.5 * (RM[k] + RM[k ^ HALF]);
    for (let k = 0; k < M; k++) { if (REF[k] > PI - 0.06) { HMk[k] = HREF; continue; } rimPos(RD2[k], k, P6); HMk[k] = Math.max(HMIN, hAt(P6[0], P6[1], P6[2])); }
  }
  const P6b = new Float64Array(6);
  // v4: no frill. In Taylor-Culick retraction the film is swallowed into the rim as it goes, so there is no wide sheet
  // behind the rim to fold. sheetPoint(u, t) is the intact film's last strip: from the free edge (t = 0, the rim thread)
  // to where it rejoins the sphere (t = 1, bandW ahead of the rim), shaded exactly like the sphere and with no folds.
  // Past the equator the rim's circumference shrinks, and the compression shows only on the thread itself: it crinkles
  // harder and more irregularly at several scales, thickens and brightens, sheds more mist and short ligaments, and
  // lifts a little off the sphere.
  const compOf = re => (re > PI / 2 ? 1 - Math.sin(Math.min(PI, re)) : 0);   // fraction of the circumference lost since the equator (reads reff)
  const compG = rd => smooth(Math.sqrt(compOf(rd)), 0.0, 0.75);   // 0 before the equator, 1 when heavily compressed
  const bandW = re => FLAPW * (1 - 0.8 * smooth(re, PI / 2 - 0.1, PI / 2 + 0.35));   // the strip narrows as the rim gathers it
  const LACE = +(Q.get('lace') || 2.5), KNOT = +(Q.get('knot') || 0.85);   // v4.3 thread lace and beading (0 = v4.2); v4.6: more beaded (v4.3-v4.5: 0.7)
  // v4.6: the refs' rim thread is thin and beaded, a little brighter than the mist, not a bright white double line:
  // thread brightness (thb) and side-strand brightness (strb) scaled down (v4.3-v4.5: thb 1, strb 0.55, thw 1.5)
  const THB = +(Q.get('thb') || 0.7), STRB = +(Q.get('strb') || 0.3);
  const RIBW = +(Q.get('ribw') || 4.0), RIBB = +(Q.get('ribb') || 0.6), RIBM = +(Q.get('ribm') ?? 0.75), RIBH = +(Q.get('ribh') ?? 0.5);   // v4.7 late ribbon
  // v4.3: in the room look the film is nearly clear, so a thread seen through it is barely dimmed (v3-v4.2: 0.18), and the
  // thread is drawn a little thicker; spray streams out from the surface as well as trailing (the veil beyond the outline)
  const STRANDS = +(Q.get('strands') || 1);
  const BEHIND = +(Q.get('behind') || (LOOK === 'r' ? 0.7 : 0.18)), THW = +(Q.get('thw') || 1.15), NOUT = +(Q.get('nout') || 0.05);   // v4.3 thread lace and beading (0 = v4.2)
  const LIFTC = +(Q.get('lift') || 0.016), SPLAYK = +(Q.get('splay') || 1);                       // modest outward lift of the compressed thread
  const SP = { x: 0, y: 0, z: 0, mx: 0, my: 0, mz: 0, crease: 0, rd: 0, r: 0, re: 0, h: 0, cg: 0 };
  // v5.7 (performance): the thread's noise depends on (u, sd, dth) only, not on t, so it is computed once per column
  // (sheetNoise) and composed for each t (sheetAt); same arithmetic in the same order as v5.6's sheetPoint, so the drawn
  // geometry is bit-identical. buildFlap used to evaluate the ~17 noise octaves 9 times per column.
  const SN = { k0: 0, r: 0, rd: 0, lf: 0, re: 0, mat: 0, phi: 0, cg: 0, X1: 0, X2: 0, L0: 0, LP: 0, LCI: 0, LCN: 0, dth: 0 };
  function sheetNoise(u, sd, dth) {
    sd = sd || 0; dth = dth || 0;
    const k0 = Math.floor(u) % M, k1 = (k0 + 1) % M, f = u - Math.floor(u);
    const r = RM[k0] * (1 - f) + RM[k1] * f, rd = RD2[k0] * (1 - f) + RD2[k1] * f, lf = Math.max(0, LF[k0] * (1 - f) + LF[k1] * f), re = REF[k0] * (1 - f) + REF[k1] * f;
    const mat = smooth(r, 0.03, 0.30), f01 = u / M, phi = TAU * f01, cg = compG(re);
    const big = cg * (0.010 * vn2(f01 * 37, rd * 4, 611, 37) + 0.007 * vn2(f01 * 97, rd * 7, 612, 97)) * (0.4 + 1.6 * Math.max(0, vn2(f01 * 7, rd * 2, 613, 7) + 0.3));
    SN.X1 = crinkle(f01, r, 101 + sd) * (1 + 1.3 * cg) + big;
    SN.X2 = crinkle(f01, r, 202 + sd) * 1.4 * (1 + 1.0 * cg) + crinkle(f01, r, 505 + sd) * (0.3 + 1.1 * cg) + 0.8 * big;
    SN.L0 = cg * LIFTC * (0.5 + 1.2 * Math.max(0, vn2(f01 * 13, rd * 3, 614, 13) + 0.35));
    SN.LP = (0.3 + 1.5 * Math.max(0, vn2(f01 * 9, rd * 2.5, 707, 9) + 0.2));
    SN.LCI = (0.040 * vn2(f01 * 41, rd * 6, 708, 41) + 0.020 * vn2(f01 * 113, rd * 11, 709 + sd, 113));
    SN.LCN = (0.030 * vn2(f01 * 37, rd * 6, 710, 37) + 0.015 * vn2(f01 * 97, rd * 11, 711 + sd, 97));
    SN.k0 = k0; SN.r = r; SN.rd = rd; SN.lf = lf; SN.re = re; SN.mat = mat; SN.phi = phi; SN.cg = cg; SN.dth = dth; return SN; }
  function sheetAt(t) {   // sheetPoint(u, t) for the u of the last sheetNoise call
    const { k0, r, rd, lf, re, mat, phi, cg, dth } = SN, e = 1 - t;
    // the splay of the torn edge (flap ring) before the equator; past it the thread stays near the sphere
    const splay = SPLAYK * lf * e * e * splayFade(re) * petalF(re);
    // crinkle: in the film's plane (ci, along the travel) and off it (cn); compression adds amplitude and two coarser,
    // patchy, aperiodic octaves (crumpling), so there is no regular spacing anywhere
    const rib = 1 - RIBM * smooth(re, PI - 0.9, PI - 0.12);   // v4.7: at the end the crumpled thread settles into a smooth ribbon edge (refs 107, 108)
    const e4 = e * e * e * e * rib;   // the crinkle lives on the thread; the film just behind it is smooth
    const ci = SN.X1 * mat * e4;
    const cn = SN.X2 * mat * e4;
    const lift = SN.L0 * e * e;
    // v4.3 lace: the reference thread (103, 105) is a crumpled string with loops and cusps a few percent of the radius
    // across, mostly out of the film's plane, in patches; two coarse aperiodic octaves under a patchy envelope
    const lace = LACE * mat * e4 * SN.LP;   // (e4 carries the v4.7 ribbon factor)
    const lci = lace * SN.LCI + dth * mat;
    const lcn = lace * SN.LCN;
    const wf = bandW(re);
    const th = rd + ci + lci + wf * t;
    rimPosPhi(th, phi, P6b); const h = HMk[k0], rr = 1 + tubeR(rd, h) * 0.35 * e + splay + cn + lcn + lift;
    SP.x = P6b[0] * rr; SP.y = P6b[1] * rr; SP.z = P6b[2] * rr;
    rimPosPhi(rd + wf * t, phi, P6b); SP.mx = P6b[0]; SP.my = P6b[1]; SP.mz = P6b[2];   // material point (thickness)
    SP.crease = 0; SP.rd = rd; SP.r = r; SP.re = re; SP.h = h; SP.cg = cg;
    return SP; }
  function sheetPoint(u, t, sd, dth) { sheetNoise(u, sd, dth); return sheetAt(t); }   // v4.3: sd, dth (optional) give a side strand of the laced thread
  function edgePoint(u, out, o) {  // the free edge = sheetPoint(u, 0): the thin bright crinkled thread
    const q = sheetPoint(u, 0); out[o] = q.x; out[o + 1] = q.y; out[o + 2] = q.z; out[o + 3] = q.re;
    const end = smooth(q.re, PI - 0.9, PI - 0.12);   // the last liquid gathers: the edge brightens and thickens into a ribbon
    const knot = KNOT > 0 ? 1 - KNOT + KNOT * 2.2 * Math.max(0, vn2(u / M * 160, q.rd * 9, 712, 160) + 0.2) : 1;   // v4.3: beaded, uneven brightness
    // v4.7 late ribbon: in the refs (107, 108) the last rim is a soft, broad, pale band, not a crisp bright line: at the
    // end the thread widens (ribw) and its peak brightness rises less (ribb; v4.1-v4.6: 1.8 and 2.4)
    out[o + 4] = THB * (2.4 + RIBB * end) * (1 + 0.9 * q.cg) * knot; out[o + 5] = (0.0009 + 0.0004 * Math.sqrt(Math.min(2.5, q.h / HREF))) * (1 + RIBW * end) * (1 + 0.7 * q.cg); }
  function buildFlap() {           // the band of the same sheet, t from 0 (free edge) to 1 (hinge), with smooth normals
    let n = FCOL * FROW;
    for (let c = 0; c < FCOL; c++) flapLive[c] = REF[2 * c] < PI - 0.05 ? 1 : 0;   // v4: no strip where the fronts have met
    // v5.7: only columns that a live strip uses (itself or a neighbour live) are built; the noise once per column
    for (let c = 0; c < FCOL; c++) { if (!flapLive[c] && !flapLive[(c + 1) % FCOL] && !flapLive[(c + FCOL - 1) % FCOL]) continue;
      sheetNoise(2 * c);
      for (let q = 0; q < FROW; q++) { const s = sheetAt(q / (FROW - 1)), o = 10 * (c * FROW + q);
        flapPos[o] = s.x; flapPos[o + 1] = s.y; flapPos[o + 2] = s.z; flapPos[o + 3] = s.mx; flapPos[o + 4] = s.my; flapPos[o + 5] = s.mz; flapPos[o + 9] = s.crease; } }
    for (let c = 0; c < FCOL; c++) if (flapLive[c]) for (let q = 0; q < FROW; q++) {
      const i = c * FROW + q, cl = ((c + FCOL - 1) % FCOL) * FROW + q, cr = ((c + 1) % FCOL) * FROW + q, qd = c * FROW + Math.max(0, q - 1), qu = c * FROW + Math.min(FROW - 1, q + 1);
      const ux = flapPos[10 * cr] - flapPos[10 * cl], uy = flapPos[10 * cr + 1] - flapPos[10 * cl + 1], uz = flapPos[10 * cr + 2] - flapPos[10 * cl + 2];
      const vx = flapPos[10 * qu] - flapPos[10 * qd], vy = flapPos[10 * qu + 1] - flapPos[10 * qd + 1], vz = flapPos[10 * qu + 2] - flapPos[10 * qd + 2];
      let nx = uy * vz - uz * vy, ny = uz * vx - ux * vz, nz = ux * vy - uy * vx; const l = Math.hypot(nx, ny, nz) || 1;
      flapPos[10 * i + 6] = nx / l; flapPos[10 * i + 7] = ny / l; flapPos[10 * i + 8] = nz / l; }
    nFlapIdx = 0;
    for (let c = 0; c < FCOL; c++) { const c1 = (c + 1) % FCOL; if (!flapLive[c] || !flapLive[c1]) continue; flapIdxDyn.set(flapIdx.subarray(6 * (FROW - 1) * c, 6 * (FROW - 1) * (c + 1)), nFlapIdx); nFlapIdx += 6 * (FROW - 1); }
    return n; }
  // droplets: closed-form flight from the birth record, with drag (they stop within about tau ticks and hang as a cloud)
  const DROP_TAU = [40, 11, 70, 55, 1, +(Q.get('jettau') || 16)], DROP_RES = 0.012;
  const STREAK = +(Q.get('streak') || 6), PATCH = +(Q.get('patch') || 0.9);   // v4.2: spray streak length in ticks of flight (v4.1: 3), finer hair-like veil
  const PINW = +(Q.get('pinw') || 1.6), PINB = +(Q.get('pinb') || 0.06);   // v4.2: pinpoint brightness spread (0 = v4.1: all drops equally bright)
  // v4.6: no bright collar at the rim. In the refs the fringe right at the rim is a dim grey hair; the grey builds up as the
  // spray spreads. Spray haze fades in over hzin ticks of age and the crisp streaks start at hzc of their brightness
  // (v4.2-v4.5: hzin 0 = full haze and streak brightness at birth, which drew a bright white fur along the rim)
  const HZIN = +(Q.get('hzin') ?? 12), HZC = +(Q.get('hzc') || 0.35);
  // v4.6: pinpoint drops beyond pinr bubble radii from the centre fade to 15% over 0.6 radii (0 = v4.5: no fade); in the
  // refs the drops hang in and near the cloud rather than filling the frame like stars
  const PINR = +(Q.get('pinr') ?? 1.35);
  // v4.8 knob: lifetime of the crisp spray streaks in ticks (default 700 as in v4.1-v4.7; shorter values thin the old
  // spray, though the grey dome under the cap comes mostly from the haze, which Ben liked in v4.5)
  const LNT = +(Q.get('lnt') || 150);   // v5.0: 150 (v4.1-v4.9: 700)
  // v4.9: the last cap turns milky and pale as the film runs out (ref 108: a pale band of gathered film, faint colour):
  // the film reflectance is blended towards a brighter grey by milk once the film gone passes milkg (render-only)
  const MILK = +(Q.get('milk') ?? 0.7), MILKG = +(Q.get('milkg') || 0.80);
  // v5.0: drifting smoke. In the refs the old spray does not keep the shape of the sphere: by 107-110 it has drifted into
  // a ragged cloud with wisps and gaps, and no outline where the film was. Each drop, once older than dsa ticks, is carried
  // by a slow, smooth, random air flow sampled at its birth point (two octaves of value noise, frequency dsf), so
  // neighbouring drops drift together into wisps while the shell spreads and thins. Drawing only: a pure function of the
  // drop record and its age (cached per slot, checked against the record). dsp 0 = v4.9; big drops drift dsk as much.
  const DSP = +(Q.get('dsp') ?? 0.5), DSF = +(Q.get('dsf') || 4), DSA = +(Q.get('dsa') ?? 10), DSK = +(Q.get('dsk') ?? 0.35), DSO = +(Q.get('dso') || 100);   // dso: ticks over which the drift speeds up
  function vn3(x, y, z, sd) { const i0 = Math.floor(x), j0 = Math.floor(y), k0 = Math.floor(z), fx = x - i0, fy = y - j0, fz = z - k0;
    const ux = fx * fx * (3 - 2 * fx), uy = fy * fy * (3 - 2 * fy), uz = fz * fz * (3 - 2 * fz), h = (i, j, k) => hash2(i * 7919 + sd, j * 104729 + k * 1013 + 31 * sd);
    const l = k => (h(i0, j0, k) * (1 - ux) + h(i0 + 1, j0, k) * ux) * (1 - uy) + (h(i0, j0 + 1, k) * (1 - ux) + h(i0 + 1, j0 + 1, k) * ux) * uy;
    return l(k0) * (1 - uz) + l(k0 + 1) * uz - 0.5; }
  const DFV = new Float32Array(3 * DMAX), DFK = new Int32Array(4 * DMAX).fill(-2147483648);
  function drift(i, o, age, P, s) { const a = age - DSA; if (DSP <= 0 || a <= 0) return; const c = 4 * i, v = 3 * i;
    if (DFK[c] !== DI[o] || DFK[c + 1] !== DI[o + 1] || DFK[c + 2] !== DI[o + 2] || DFK[c + 3] !== DI[o + 6]) {
      const x = DI[o] / SD * DSF, y = DI[o + 1] / SD * DSF, z = DI[o + 2] / SD * DSF;
      for (let d = 0; d < 3; d++) DFV[v + d] = 2.4 * (vn3(x, y, z, 401 + 17 * d) + 0.5 * vn3(2.3 * x + 5.1, 2.3 * y, 2.3 * z, 457 + 17 * d));
      DFK[c] = DI[o]; DFK[c + 1] = DI[o + 1]; DFK[c + 2] = DI[o + 2]; DFK[c + 3] = DI[o + 6]; }
    const g = s * DSP * a * a / (100 * (a + DSO)); P[0] += g * DFV[v]; P[1] += g * DFV[v + 1]; P[2] += g * DFV[v + 2]; }
  // v5.3: the late dome's bright outline. Spray is drawn as a thin shell just outside the film (sprayOut), and a thin shell
  // seen in projection is limb-brightened: the line of sight grazes it at the outline and crosses about 1/|n.v| times as
  // much of it as at the centre. The real cloud is a thick, irregular volume and shows no outline (refs 106-108). So the
  // old spray's streaks and haze are weighted by |n.v| of the birth normal (floor limbf), ramped in over limba ticks of age:
  // the projected density becomes even, while the young veil at the rim (refs 103, 105) is untouched. Drawing only.
  const LIMBF = +(Q.get('limbf') ?? 0.08), LIMBA = (Q.get('limba') || '40,110').split(',').map(Number);
  function limbW(o, age) { if (LIMBF >= 1) return 1; const bx = DI[o], by = DI[o + 1], bz = DI[o + 2], bl = Math.hypot(bx, by, bz) || 1;
    const nv = Math.abs(bx * VD[0] + by * VD[1] + bz * VD[2]) / bl; return 1 - smooth(age, LIMBA[0], LIMBA[1]) * (1 - Math.max(LIMBF, nv)); }
  // v5.3: fewer pinpoints in the old cloud. In the refs the pinpoint drops sit mostly near the cloud's front; the old ones
  // drift off the focal plane and blur into the haze. A share pink keeps its pinpoint; the rest fade out, each at its own
  // age between pina ticks (a pure function of the record). Their haze is kept.
  // v5.5: jet drawing (str: dash length in ticks of flight; min: shortest dash; b, t: brightness and its decay in ticks; lig:
  // ligament brightness; brk: ages over which the ligament breaks into drops) and the random spray dashes turned down (dash)
  const JDR = { str: +(Q.get('jstr') || 2), min: 0.002, b: +(Q.get('jb') || 0.30), t: +(Q.get('jt') || 20), lig: +(Q.get('jlig') || 0.8), brk: (Q.get('jbrk') || '6,26').split(',').map(Number) };
  const DASH = +(Q.get('dash') ?? 0.4), BIGB = +(Q.get('bigb') || 1.3);
  // v5.8 (refs 103, 105: the fringe beyond the rim is a soft grey hair, the streaks slightly curved with grey mist between
  // them, not crisp straight needles; 106-107: the swept hole is dark, no hatching): jets bend gently off the surface
  // (each drop offset along its birth normal by jcv x (distance flown)^2, so a jet's string of drops curves, tip most), their
  // haze is stronger (jhz) and their crisp lines a little dimmer (jln); the old spray dashes fade with age (dasht ticks; the
  // haze they leave is kept). jcv=0, jhz=1, jln=1, dasht=0 = v5.7. Drawing only.
  const JCV = +(Q.get('jcv') ?? 2.5), JHZ = +(Q.get('jhz') || 1.9), JLN = +(Q.get('jln') || 0.8), DASHT = +(Q.get('dasht') ?? 28);
  function jetBend(o, age, P, c) { if (JCV <= 0) return; const vl = Math.hypot(DI[o + 3], DI[o + 4], DI[o + 5]) / SD, d = vl * ekOf(5, age), b = JCV * d * d, bl = RCV[c + 7];
    P[0] += b * DI[o] / bl; P[1] += b * DI[o + 1] / bl; P[2] += b * DI[o + 2] / bl; }   // v5.5: large drops dimmer (v4.1-v5.4: 2.2)
  const PINK = +(Q.get('pink') ?? 0.25), PINA = (Q.get('pina') || '50,220').split(',').map(Number);
  // v5.7 (performance): per-age tables of the pure functions of age (same formulas, so bit-identical), and per-record
  // constants (hashes, patch noise, the birth normal's |n.v| and length) cached per slot, keyed by the record
  const AT = 8192, EK = new Float64Array(6 * AT);
  for (let a = 0; a < AT; a++) for (let k = 0; k < 6; k++) { const tau = DROP_TAU[k]; EK[k * AT + a] = tau * (1 - Math.exp(-a / tau)) + DROP_RES * a; }
  const ekOf = (kind, age) => (age | 0) === age && age >= 0 && age < AT ? EK[kind * AT + age] : DROP_TAU[kind] * (1 - Math.exp(-age / DROP_TAU[kind])) + DROP_RES * age;
  const RCK = new Int32Array(4 * DMAX).fill(-2147483648), RCV = new Float64Array(8 * DMAX);
  function rcGet(i, o) { const k = 4 * i, c = 8 * i;
    if (RCK[k] !== DI[o] || RCK[k + 1] !== DI[o + 1] || RCK[k + 2] !== DI[o + 6] || RCK[k + 3] !== DI[o + 7]) {
      const kind = DI[o + 7] >>> 16, par = DI[o + 7] & 0xFFFF, b = DI[o + 6], bx = DI[o], by = DI[o + 1], bz = DI[o + 2], bl = Math.hypot(bx, by, bz) || 1;
      RCV[c] = hash2(par, b * 3 + kind);
      RCV[c + 1] = PATCH > 0 ? 1 - PATCH + PATCH * 2.4 * Math.max(0, vn2(par / M * 7, b * 0.03, 713, 7) + 0.18) : 1;   // v4.3: the beard comes in patches
      RCV[c + 2] = 0.4 + 1.2 * hash2(b, par + 991);   // sprayOut's hq
      RCV[c + 3] = hash2(4096 * b + par, ZSEED + 85);   // a jet's length class (hl)
      RCV[c + 4] = hash2(b + 7, par * 5 + kind); RCV[c + 5] = hash2(b + 13, par * 7 + kind);   // pinpoint q2, q3
      RCV[c + 6] = Math.abs(bx * VD[0] + by * VD[1] + bz * VD[2]) / bl; RCV[c + 7] = bl;   // limbW's nv; the birth point's length
      RCK[k] = DI[o]; RCK[k + 1] = DI[o + 1]; RCK[k + 2] = DI[o + 6]; RCK[k + 3] = DI[o + 7]; }
    return c; }
  function limbC(c, age) { if (LIMBF >= 1) return 1; return 1 - smooth(age, LIMBA[0], LIMBA[1]) * (1 - Math.max(LIMBF, RCV[c + 6])); }
  function sprayOutC(o, age, P, c) { const bl = RCV[c + 7], hq = RCV[c + 2];
    const e = NOUT * hq * (1 - Math.exp(-age / 20)); P[0] += e * DI[o] / bl; P[1] += e * DI[o + 1] / bl; P[2] += e * DI[o + 2] / bl; }
  function dropAt(o, age, out) { const kind = DI[o + 7] >>> 16, e = ekOf(kind, age);
    out[0] = (DI[o] + DI[o + 3] * e) / SD; out[1] = (DI[o + 1] + DI[o + 4] * e) / SD - 2e-7 * age * age; out[2] = (DI[o + 2] + DI[o + 5] * e) / SD; return kind; }
  // v4.3: spray drawn drifting out from the surface along its birth point's normal (a pure function of the record and age)
  function sprayOut(o, age, P) { const bx = DI[o], by = DI[o + 1], bz = DI[o + 2], bl = Math.hypot(bx, by, bz) || 1, hq = 0.4 + 1.2 * hash2(DI[o + 6], (DI[o + 7] & 0xFFFF) + 991);
    const e = NOUT * hq * (1 - Math.exp(-age / 20)); P[0] += e * bx / bl; P[1] += e * by / bl; P[2] += e * bz / bl; }
  const LMAX = 2 * (DMAX + 64 * 40), lineData = new Float32Array(LMAX * 5);
  const DP0 = new Float64Array(3), DP1 = new Float64Array(3);
  // v2: the flap band (thin-film shaded mesh, splayed off the sphere) and additive lines (mist streaks, cobwebs)
  const VS_FLAP = PRE + `in vec3 aP; in vec3 aM; in vec3 aN; in float aC; uniform mat4 uVP; out vec3 vP; out vec3 vM; out vec3 vN; out float vC; void main(){ vP = aP; vM = aM; vN = aN; vC = aC; gl_Position = uVP * vec4(aP, 1.0); }`;
  const FS_FLAP = PRE + ENV + `uniform samplerCube uThick; uniform sampler2D uLUT; uniform vec3 uCam; uniform float uGain; in vec3 vP; in vec3 vM; in vec3 vN; in float vC; out vec4 o;
void main(){ vec3 v = normalize(uCam - vP); vec3 n = normalize(vN); if (dot(n, v) < 0.0) n = -n;
  // v5.4: a stretch of the band on the far side is seen from inside, like the sphere's back film: it gets the back film's
  // share of the lights (cback, dback) and weight, and no pale side-wall edge. v5.3 lit it like the front film, so the far
  // band showed through the front film as a brighter strip whose hinge was a line running ahead of the rim (Ben, 121).
  bool inner = dot(vM, v) < 0.0; gCeil = inner ? uCeilBack : 1.0; float bw = inner ? 0.8 : 1.0;
  float ci = clamp(dot(v, n), 0.0, 1.0), h = texture(uThick, vM).r, st = sqrt(1.0 - ci * ci) / 1.33, ct = sqrt(1.0 - st * st);
  vec3 film = texture(uLUT, vec2(clamp(${HCOL} / 1600.0, 0.0, 1.0), clamp((ct - 0.6) / 0.4, 0.0, 1.0))).rgb;
  vec3 R = min(film * uGain * (1.0 + 5.0 * pow(1.0 - ci, 3.0)) + vec3(0.25) * pow(1.0 - ci, 6.0) * step(30.0, h), vec3(1.0));   // = the sphere film
  vec3 col = envmap(reflect(-v, n)) * R + vec3(0.9, 0.92, 1.0) * 0.45 * vC;   // bright creases where the sheet folds over
  if (!inner) col += sideWall(reflect(-v, n)) * ${EDGEW.toFixed(3)} * pow(1.0 - ci, ${EDGEP.toFixed(2)});   // as the sphere's front film
  o = vec4(col * bw, clamp(dot(R, vec3(0.3333)) + 0.35 * vC, 0.0, 1.0) * bw); }`;
  const VS_LN = PRE + `in vec4 aP; in float aH; uniform mat4 uVP; uniform float uLnK; out float vA; void main(){ vA = uLnK < 0.0 ? aH : aP.w * uLnK; gl_Position = uVP * vec4(aP.xyz, 1.0); }`;
  const FS_LN = PRE + `in float vA; out vec4 o; void main(){ o = vec4(vec3(0.85, 0.88, 0.95) * vA, 0.0); }`;
  const pFlap = prog(VS_FLAP, FS_FLAP), pLn = prog(VS_LN, FS_LN);
  // v4.2 mist haze. In the reference frames the spray reads as a soft grey "beard": millions of drops far below a pixel,
  // seen as a fuzzy, streaky veil, with only a few pinpoint drops. So the spray streaks, ligaments, cobwebs and drops are
  // drawn a second time into a half-resolution buffer, blurred, and added back as grey haze; the crisp streaks are drawn
  // dimmer. The haze is a pure function of the drawn geometry, itself a pure function of the integer state.
  const HZ = { k: +(Q.get('haze') || 0.2), wide: +(Q.get('hazew') || 0.8), ln: +(Q.get('lnk') || 0.34), tau: +(Q.get('hazet') || 25),   // v5.0: 25 (v4.5-v4.9: 40): the old cloud thins as it drifts (refs 107-110)
      // v4.5: the haze lasts longer: a broad grey cloud where the film was (106/107)
    // v4.6: stronger soft saturation (hazes 3, haze 0.2; v4.4-v4.5: 0.6, 0.17): the faint far cloud keeps its grey, but
    // the dense haze along the rim and at the cap's tips (the bright white fur and puffs) is held to the refs' dim grey
    tint: [0.74, 0.72, 0.70], sat: +(Q.get('hazes') || 3) };
  const FS_HZPT = PRE + `in vec4 vK; out vec4 o; void main(){ if (vK.w <= 0.0 || vK.z > 0.5) discard;   // v4.7: any point with a haze weight (drops, and the late thread's halo)
  vec2 q = gl_PointCoord * 2.0 - 1.0; float r2 = dot(q, q); if (r2 > 1.0) discard; o = vec4(vec3(vK.w * (1.0 - r2)), 0.0); }`;
  const FS_BLUR = PRE + `uniform sampler2D uT; uniform vec2 uDir; in vec2 vUV; out vec4 o;
void main(){ vec4 s = texture(uT, vUV) * 0.2270270;
  s += (texture(uT, vUV + uDir * 1.3846154) + texture(uT, vUV - uDir * 1.3846154)) * 0.3162162;
  s += (texture(uT, vUV + uDir * 3.2307692) + texture(uT, vUV - uDir * 3.2307692)) * 0.0702703; o = s; }`;
  const FS_HZADD = PRE + `uniform sampler2D uA, uB; uniform vec3 uTint; uniform float uK, uW, uSat, uAbs; in vec2 vUV; out vec4 o;
void main(){ vec3 h = texture(uA, vUV).rgb + uW * texture(uB, vUV).rgb; h = h / (1.0 + uSat * h); o = vec4(uTint * uK * h, clamp(uAbs * uSat * dot(h, vec3(0.3333)), 0.0, 1.0)); }`;
  // v5.0: the haze of a drop fades in two stages: most of it within hazet ticks (the dense fringe stays near the rim, as in
  // the refs), and a share hzf over hzt2 ticks (the faint broad cloud left where the film was, now drifting; v4.5-v4.9: one
  // stage of 40 ticks, which filled the whole swept region with a dense grey carpet)
  // v5.0: the mist also dims what is behind it (hza: the share of the backdrop hidden by the densest haze; 0 = v4.9, purely
  // additive). In refs 107-108 the old beard reads as grey smoke, darker than the lit backdrop in places, not a glowing fur.
  const HZA = +(Q.get('hza') ?? 0.6);
  const HZF = +(Q.get('hzf') ?? 0.15), HZT2 = +(Q.get('hzt2') || 150);
  const hzAge = age => (1 - HZF) * Math.exp(-age / HZ.tau) + HZF * Math.exp(-age / HZT2);
  const pHzPt = prog(VS_PT, FS_HZPT), pBlur = prog(VS_FULL, FS_BLUR), pHzAdd = prog(VS_FULL, FS_HZADD);
  let hz = null;
  function mkTarget(w, h) { const t = gl.createTexture(); gl.bindTexture(gl.TEXTURE_2D, t); gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA16F, w, h, 0, gl.RGBA, gl.HALF_FLOAT, null);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE); gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    const f = gl.createFramebuffer(); gl.bindFramebuffer(gl.FRAMEBUFFER, f); gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, t, 0); return { t, f, w, h }; }
  function blurPass(src, dst, dx, dy) { gl.bindFramebuffer(gl.FRAMEBUFFER, dst.f); gl.viewport(0, 0, dst.w, dst.h); gl.useProgram(pBlur.p);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, src.t); gl.uniform1i(pBlur.u.uT, 0); gl.uniform2f(pBlur.u.uDir, dx / src.w, dy / src.h); gl.drawArrays(gl.TRIANGLES, 0, 3); }
  function drawHaze(np, focal) {   // into hz.a (fine, half res) and hz.c (wide, quarter res); the caller composites
    const hw = Math.max(1, W >> 1), hh = Math.max(1, H >> 1);
    if (!hz || hz.a.w !== hw || hz.a.h !== hh) { if (hz) for (const x of [hz.a, hz.b, hz.c, hz.d]) { gl.deleteTexture(x.t); gl.deleteFramebuffer(x.f); }
      hz = { a: mkTarget(hw, hh), b: mkTarget(hw, hh), c: mkTarget(Math.max(1, hw >> 1), Math.max(1, hh >> 1)), d: mkTarget(Math.max(1, hw >> 1), Math.max(1, hh >> 1)) }; }
    gl.bindFramebuffer(gl.FRAMEBUFFER, hz.a.f); gl.viewport(0, 0, hw, hh); gl.clearColor(0, 0, 0, 0); gl.clear(gl.COLOR_BUFFER_BIT);
    gl.disable(gl.DEPTH_TEST); gl.depthMask(false); gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE);
    if (nLines > 0) { gl.useProgram(pLn.p); gl.uniformMatrix4fv(pLn.u.uVP, false, VP); gl.uniform1f(pLn.u.uLnK, -1.0); gl.bindVertexArray(vaoLn); gl.drawArrays(gl.LINES, 0, nLines); }
    if (np > 0) { gl.useProgram(pHzPt.p); gl.uniformMatrix4fv(pHzPt.u.uVP, false, VP); gl.uniform1f(pHzPt.u.uFocal, focal * 0.5); gl.bindVertexArray(vaoPt); gl.drawArrays(gl.POINTS, 0, np); }
    gl.disable(gl.BLEND); gl.bindVertexArray(vaoEmpty);
    blurPass(hz.a, hz.b, 1, 0); blurPass(hz.b, hz.a, 0, 1);                  // fine: sigma about 2 half-res pixels
    blurPass(hz.a, hz.c, 1, 0); blurPass(hz.c, hz.d, 0, 1);                  // wide: downsample and blur again, twice
    blurPass(hz.d, hz.c, 2, 0); blurPass(hz.c, hz.d, 0, 2);
  }
  const flapBuf = gl.createBuffer(), flapIbo = gl.createBuffer(), vaoFlap = gl.createVertexArray();
  const flapIdx = new Uint32Array(FCOL * (FROW - 1) * 6); { let q = 0; for (let c = 0; c < FCOL; c++) { const c1 = (c + 1) % FCOL; for (let r = 0; r < FROW - 1; r++) {
    const a = c * FROW + r, b = c1 * FROW + r; flapIdx[q++] = a; flapIdx[q++] = b; flapIdx[q++] = b + 1; flapIdx[q++] = a; flapIdx[q++] = b + 1; flapIdx[q++] = a + 1; } } }
  gl.bindVertexArray(vaoFlap); gl.bindBuffer(gl.ARRAY_BUFFER, flapBuf); gl.bufferData(gl.ARRAY_BUFFER, flapPos.byteLength, gl.DYNAMIC_DRAW);
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, flapIbo); gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, flapIdx, gl.DYNAMIC_DRAW);
  const flapLive = new Uint8Array(FCOL), flapIdxDyn = new Uint32Array(flapIdx.length); let nFlapIdx = 0;
  { const lp = gl.getAttribLocation(pFlap.p, 'aP'), lm = gl.getAttribLocation(pFlap.p, 'aM'), ln = gl.getAttribLocation(pFlap.p, 'aN');
    const lc = gl.getAttribLocation(pFlap.p, 'aC');
    gl.enableVertexAttribArray(lp); gl.vertexAttribPointer(lp, 3, gl.FLOAT, false, 40, 0); gl.enableVertexAttribArray(lm); gl.vertexAttribPointer(lm, 3, gl.FLOAT, false, 40, 12);
    gl.enableVertexAttribArray(ln); gl.vertexAttribPointer(ln, 3, gl.FLOAT, false, 40, 24); gl.enableVertexAttribArray(lc); gl.vertexAttribPointer(lc, 1, gl.FLOAT, false, 40, 36); }
  const lnBuf = gl.createBuffer(), vaoLn = gl.createVertexArray();
  gl.bindVertexArray(vaoLn); gl.bindBuffer(gl.ARRAY_BUFFER, lnBuf); gl.bufferData(gl.ARRAY_BUFFER, lineData.byteLength, gl.DYNAMIC_DRAW);
  { const l = gl.getAttribLocation(pLn.p, 'aP'); gl.enableVertexAttribArray(l); gl.vertexAttribPointer(l, 4, gl.FLOAT, false, 20, 0);
    const lh = gl.getAttribLocation(pLn.p, 'aH'); gl.enableVertexAttribArray(lh); gl.vertexAttribPointer(lh, 1, gl.FLOAT, false, 20, 16); }
  gl.bindVertexArray(null);

  let nLines = 0, nFlap = 0; const LF6 = new Float64Array(6);
  function behindFilm(px, py, pz) {   // is the point seen through the intact front film? (ray from the eye hits the film first)
    let dx = px - EYE[0], dy = py - EYE[1], dz = pz - EYE[2]; const L = Math.hypot(dx, dy, dz); dx /= L; dy /= L; dz /= L;
    const b = EYE[0] * dx + EYE[1] * dy + EYE[2] * dz, c = EYE[0] * EYE[0] + EYE[1] * EYE[1] + EYE[2] * EYE[2] - 1, disc = b * b - c; if (disc <= 0) return false;
    const t1 = -b - Math.sqrt(disc); if (t1 >= L - 0.01) return false;
    const x = EYE[0] + t1 * dx, y = EYE[1] + t1 * dy, z = EYE[2] + t1 * dz, th = Math.acos(Math.max(-1, Math.min(1, x * C[0] + y * C[1] + z * C[2])));
    let ph = Math.atan2(x * E2[0] + y * E2[1] + z * E2[2], x * E1[0] + y * E1[1] + z * E1[2]); if (ph < 0) ph += TAU;
    const kk = Math.floor(ph / TAU * M) % M, ko = kk ^ HALF; return th > RD2[kk] + bandW(REF[kk]) && th < TAU - RD2[ko] - bandW(REF[ko]); }
  // v5.7 (Ben on v5.6: "allow the drops to be a bit larger and varied in shape"; refs 106-110): each large drop is drawn
  // by shape class, a pure function of its record and age. All end as a blob that wobbles between oblong and oblate about
  // its direction of flight and settles (a freshly pinched drop rings in its lowest mode); some start as a ligament
  // fragment along the meeting line that beads up and contracts (refs 106-108, the lacy strings at the left) and leave a
  // satellite; a few trail a satellite on a thin neck. Sizes: bigr x cbrt(v / 0.3 VBIG) (v5.5-v5.6: 0.0026, at most
  // 0.008); in refs 107-110 the larger drops are about 1% of the bubble across. &shape=0 = v5.6's drawing.
  const SHAPE = Q.get('shape') !== '0', BIGR = +(Q.get('bigr') || 0.0036), WOB = +(Q.get('wob') ?? 1);
  const shp = (x, y, z, r, ax, ay, az, st, glow, br) => { if (nSh >= SHMAX) return; const o = 12 * nSh++; shData[o] = x; shData[o + 1] = y; shData[o + 2] = z; shData[o + 3] = r;
    shData[o + 4] = ax; shData[o + 5] = ay; shData[o + 6] = az; shData[o + 7] = st; shData[o + 8] = glow; shData[o + 9] = br; shData[o + 10] = 0; shData[o + 11] = 0; };
  const DS = new Float64Array(3);
  function shapeDrop(o, age, q, c) {   // DP0 holds the drop's position at this age
    const vr = Math.cbrt(Math.max(0, DI[o + 10]) / (0.3 * VBIG)), rad = Math.min(0.012, BIGR * vr), fade = BIGB * (0.25 + 0.75 * Math.exp(-age / 40));
    const h1 = RCV[c + 4], h2 = RCV[c + 5], h3 = hash2(DI[o + 6] + 29, (DI[o + 7] & 0xFFFF) * 11 + 3), h4 = hash2(DI[o + 6] + 31, (DI[o + 7] & 0xFFFF) * 13 + 5);
    const ed = Math.exp(-age / DROP_TAU[3]) + DROP_RES;   // direction of flight: drag-scaled launch velocity plus gravity
    let ux = DI[o + 3] / SD * ed, uy = DI[o + 4] / SD * ed - 4e-7 * age, uz = DI[o + 5] / SD * ed; const ul = Math.hypot(ux, uy, uz) || 1; ux /= ul; uy /= ul; uz /= ul;
    const wob = a => 1 + WOB * (0.45 + 0.5 * h1) * Math.exp(-a / (12 + 10 * h2)) * Math.cos(TAU * a / (7 + 5 * h3));   // stretch: oblong at pinch-off, rings, settles
    // the meeting-line direction tilted per drop (as v4.1-v5.6's ligament): the axis of a ligament fragment
    const pl = Math.hypot(DP0[0], DP0[1], DP0[2]) || 1, tilt = 1.2 * (q - 0.5);
    let gx = DI[o + 8] / SD + tilt * DP0[0] / pl, gy = DI[o + 9] / SD + tilt * DP0[1] / pl, gz = DI[o + 11] / SD + tilt * DP0[2] / pl; const gl_ = Math.hypot(gx, gy, gz) || 1; gx /= gl_; gy /= gl_; gz /= gl_;
    const L = 0.03 + 0.04 * vr;
    if (q >= 0.35 && q < 0.8) {   // ligament fragment: nb beads along g that start as one thread, bead up and draw together
      const TL = 10 + 12 * h2, nb = 2 + Math.floor(3 * h4);
      if (age < TL) { const u = age / TL, Lu = L * (0.9 - 0.65 * u), bow = 0.3 * Lu * (1 - u), vl = Math.hypot(DI[o + 3], DI[o + 4], DI[o + 5]) || 1;
        const nxr = DP0[0] / pl, nyr = DP0[1] / pl, nzr = DP0[2] / pl, curl = 0.18 * Lu * (h3 - 0.5) * 2 * (1 - 0.6 * u);   // a slight S-curl off the surface: lacy, not a rod
        const at = (w, b, out) => { const sc = curl * Math.sin(TAU * w); out[0] = DP0[0] + gx * Lu * w - DI[o + 3] / vl * b + nxr * sc; out[1] = DP0[1] + gy * Lu * w - DI[o + 4] / vl * b + nyr * sc; out[2] = DP0[2] + gz * Lu * w - DI[o + 5] / vl * b + nzr * sc; return out; };
        const thr = 1 - smooth(u, 0.25, 0.85);   // the thread between the beads thins and breaks
        if (thr > 0.02) for (let i = 0; i <= 15; i++) { const w = i / 15 - 0.5; at(w, bow * (1 - 4 * w * w), DS); shp(DS[0], DS[1], DS[2], rad * 0.26 * (1 - 0.45 * u), gx, gy, gz, 1.6, 1.3, 0.85 * fade * thr); }
        for (let i = 0; i < nb; i++) { const w = (i + 0.5) / nb - 0.5, hb = hash2(DI[o + 6] + 37 * i, (DI[o + 7] & 0xFFFF) + 17);
          const ri = rad * Math.cbrt((0.6 + 0.8 * hb) / nb) * (0.75 + 0.25 * u), seg = Lu / nb, st = Math.max(1.15, Math.pow(seg / (2 * ri), 2 / 3) * (1 - u) + 1.25 * u);   // swell out of the thread, then round up
          at(w, bow * (1 - 4 * w * w) * (0.6 + 0.8 * hb), DS); shp(DS[0], DS[1], DS[2], ri, gx, gy, gz, st, 1.3, fade); }
        return; }
      shp(DP0[0], DP0[1], DP0[2], rad * 0.96, ux, uy, uz, wob(age - TL), 1.3, fade);
      const so = (0.22 + 0.2 * h3) * L * (h4 < 0.5 ? 1 : -1); dropAt(o, age * 0.88 + 0.12 * TL, DS);
      shp(DS[0] + gx * so, DS[1] + gy * so, DS[2] + gz * so, rad * 0.36, gx, gy, gz, wob(age - TL + 3), 1.3, 0.8 * fade); return; }
    shp(DP0[0], DP0[1], DP0[2], rad, ux, uy, uz, wob(age), 1.3, fade);   // a blob
    if (q >= 0.8) {   // with a satellite trailing on a thin neck that snaps after a few ticks
      dropAt(o, age * 0.85, DS); const sx = DS[0] - ux * 0.35 * rad, sy = DS[1] - uy * 0.35 * rad, sz = DS[2] - uz * 0.35 * rad;
      shp(sx, sy, sz, rad * 0.33, ux, uy, uz, wob(age + 2), 1.3, 0.8 * fade);
      if (age < 6) { const nx = 0.5 * (DP0[0] + sx), ny = 0.5 * (DP0[1] + sy), nz = 0.5 * (DP0[2] + sz), nl = Math.hypot(DP0[0] - sx, DP0[1] - sy, DP0[2] - sz), rn = rad * 0.18;
        if (nl > 2 * rn) shp(nx, ny, nz, rn, (DP0[0] - sx) / nl, (DP0[1] - sy) / nl, (DP0[2] - sz) / nl, Math.pow(nl / (2 * rn), 2 / 3), 1.3, 0.6 * fade * (1 - age / 6)); } } }
  function buildPoints() {
    let n = 0; nLines = 0; nFlap = 0; nSh = 0;
    const put = (x, y, z, r, glow, bright, hw) => { if (n >= PTMAX) return; const o = 8 * n++; ptData[o] = x; ptData[o + 1] = y; ptData[o + 2] = z; ptData[o + 3] = r; ptData[o + 4] = glow; ptData[o + 5] = bright; ptData[o + 6] = 0; ptData[o + 7] = hw || 0; };
    const line = (x0, y0, z0, x1, y1, z1, a, hw) => { if (nLines >= LMAX - 1) return; const h = hw === undefined ? a : hw; let o = 5 * nLines++; lineData[o] = x0; lineData[o + 1] = y0; lineData[o + 2] = z0; lineData[o + 3] = a; lineData[o + 4] = h;
      o = 5 * nLines++; lineData[o] = x1; lineData[o + 1] = y1; lineData[o + 2] = z1; lineData[o + 3] = a; lineData[o + 4] = h; };
    if (popTick >= 0 && tick >= popTick) {
      edgeState();
      for (let k = 0; k < M; k++) rimF[k] = RD2[k] + bandW(REF[k]) * 0.995;   // the sphere film starts where the band hinges (same edge curve)
      nFlap = buildFlap();
      // the free edge: a thin, bright, crinkled thread
      const NE = M * NSUB;
      for (let i = 0; i < NE; i++) { const u = i / NSUB, k0 = Math.floor(u) % M, f = u - Math.floor(u), re = REF[k0] * (1 - f) + REF[(k0 + 1) % M] * f;
        if (re > PI - 0.05) { ED[6 * i + 3] = re; continue; }   // v5.7: a met point is not drawn and only its re is read
        edgePoint(u, ED, 6 * i); }
      for (let i = 0; i < NE; i++) { const o = 6 * i; if (ED[o + 3] > PI - 0.05) continue; put(ED[o], ED[o + 1], ED[o + 2], ED[o + 5] * (THW - (THW - 1) * smooth(ED[o + 3], PI / 2, PI - 0.3)), 1.0, ED[o + 4] * (behindFilm(ED[o], ED[o + 1], ED[o + 2]) ? BEHIND : 1), RIBH * smooth(ED[o + 3], PI - 0.9, PI - 0.12)); }   // v4.7: soft halo at the end
      // v4.3 lace: two side strands split off the thread in patches and rejoin it, so the rim reads as the lacy, looped
      // string of 103/105 (where the separation envelope is zero the strands lie on the thread)
      if (STRANDS > 0) for (let sgn = -1; sgn <= 1; sgn += 2) for (let i = 0; i < NE; i += 2) { const o = 6 * i; if (ED[o + 3] > PI - 0.12) continue;
        const u = i / NSUB, f01 = u / M, rd = RD2[Math.floor(u) % M], env = Math.max(0, vn2(f01 * 23, rd * 3, 720 + sgn, 23) + 0.02);
        if (env <= 0) continue; const q = sheetPoint(u, 0, 31 * sgn, sgn * STRANDS * 0.05 * env * (0.6 + 0.8 * hash2(i >> 6, 733 + sgn)) * (1 - RIBM * smooth(ED[o + 3], PI - 0.9, PI - 0.12)));
        put(q.x, q.y, q.z, ED[o + 5] * THW * 0.7, 1.0, ED[o + 4] * STRB * Math.min(1, env * 6) * (behindFilm(q.x, q.y, q.z) ? BEHIND : 1)); }
      // short ligaments: corrugation crests (the integer ZQ ring) drawn as short strands leaving the thread, more and
      // brighter as the rim gathers past the equator; irregular because the crests are (hash-seeded RT growth)
      for (let k = 0; k < M; k++) {
        const r = RM[k]; if (r < 0.2 || REF[k] > PI - 0.12) continue;
        const z = ZQ[k]; if (z <= ZQ[(k + M - 1) & (M - 1)] || z < ZQ[(k + 1) & (M - 1)]) continue;
        const cg = compG(REF[k]), zp = zpOf(k, HMk[k]); if (z < (0.6 - 0.3 * cg) * zp) continue;
        if (rimFrontR(RD2[k], RD2[(k + 1) & (M - 1)], RD2[(k + M - 1) & (M - 1)], k, LF6) < 0.35) continue;
        const g = ligament(k, RD2[k], (z / SZ) * (0.7 + 0.6 * cg), HMk[k], LG, LF6), o = 6 * k * NSUB;
        let px = ED[o], py = ED[o + 1], pz = ED[o + 2];
        const a = (0.10 + 0.28 * cg) * Math.min(1, z / zp) * (behindFilm(px, py, pz) ? 0.2 : 1), bx = px, by = py, bz = pz;
        for (let j = 1; j <= 4; j++) { const u = j / 4, w0 = u - 0.5 * u * u, w1 = 0.5 * u * u;
          const x = bx + g[9] * (w0 * g[3] + w1 * g[6]), y = by + g[9] * (w0 * g[4] + w1 * g[7]), zz = bz + g[9] * (w0 * g[5] + w1 * g[8]);
          line(px, py, pz, x, y, zz, a * (1 - 0.6 * u)); px = x; py = y; pz = zz; } }
      // droplets: pinpoints (crest pinch-off, antipode, a share of the spray) and the misty veil (dim motion streaks)
      const age0 = tick;
      for (let i = 0; i < nd; i++) { const o = REC * i, age = age0 - DI[o + 6]; if (age < 0) continue;
        if ((DI[o + 7] >>> 16) === 4) continue;   // pool moves are bookkeeping, not drops
        const c = rcGet(i, o), kind = dropAt(o, age, DP0), q = RCV[c];   // v5.7: q and the rest of the record's constants cached
        if ((kind === 1 || kind === 5) && NOUT > 0) sprayOutC(o, age, DP0, c);
        if (kind !== 3) drift(i, o, age, DP0, kind === 1 || kind === 5 ? 1 : DSK);
        if (kind === 5) {   // v5.5 jets: each drop a short dash along the jet's direction (its motion over jstr ticks), and while
          // young a ligament to the next drop of the same jet (the next record, same birth and bead): a continuous line that
          // breaks into a string of drops between ages jbrk; brightest young (near the rim), fading with age. Drawing only.
          const vx = DI[o + 3], vy = DI[o + 4], vz = DI[o + 5], vl = Math.hypot(vx, vy, vz) || 1;
          const len = Math.max(JDR.min, vl / SD * (ekOf(5, age) - ekOf(5, Math.max(0, age - JDR.str))));   // v5.7: no closure per drop per frame
          const lw = limbC(c, age), yin = HZIN > 0 ? smooth(age, 0, HZIN) : 1, hl = RCV[c + 3], aj = JDR.b * (0.25 + 2.2 * hl * hl * hl) * (0.6 + 0.4 * q) * Math.exp(-age / (JDR.t * (0.6 + 0.8 * hl))) * smooth(age, 0, 2) * lw;   // v5.6: a few long, bright, lasting jets over a soft majority
          jetBend(o, age, DP0, c);
          line(DP0[0] - vx / vl * len, DP0[1] - vy / vl * len, DP0[2] - vz / vl * len, DP0[0], DP0[1], DP0[2], JLN * aj, JHZ * lw * (0.11 + 0.26 * q) * 2.5 * hzAge(age) * yin);
          const o2 = o + REC;
          if (age < JDR.brk[1] && i + 1 < nd && DI[o2 + 6] === DI[o + 6] && DI[o2 + 7] === DI[o + 7]) {
            const c2 = rcGet(i + 1, o2); dropAt(o2, age, DP1); if (NOUT > 0) sprayOutC(o2, age, DP1, c2); drift(i + 1, o2, age, DP1, 1); jetBend(o2, age, DP1, c2);
            line(DP0[0], DP0[1], DP0[2], DP1[0], DP1[1], DP1[2], JDR.lig * aj * (1 - smooth(age, JDR.brk[0], JDR.brk[1])), 0); }
          continue; }
        if (kind === 3 && SHAPE) { shapeDrop(o, age, q, c); continue; }
        if (kind === 3) {   // v4.1: the liquid of a stretch of rim where fronts met: a thick filament along the meeting line that
          // contracts and beads up (Rayleigh-Plateau) for TP ticks, then a large drop and a satellite; bright, then like the cloud
          const vr = Math.cbrt(Math.max(0, DI[o + 10]) / (0.3 * VBIG)), rad = Math.min(0.008, 0.0026 * vr), TP = 10;   // v5.5: smaller (v4.1-v5.4: 0.0034 vr, max 0.011)
          const fade = BIGB * (0.25 + 0.75 * Math.exp(-age / 40)), fx = DI[o + 8] / SD, fy = DI[o + 9] / SD, fz = DI[o + 11] / SD, L = 0.03 + 0.04 * vr;
          if (age < TP) { const u = age / TP, Lu = L * (1 - 0.75 * u), pl = Math.hypot(DP0[0], DP0[1], DP0[2]) || 1, tilt = 1.2 * (q - 0.5);
            let dx = fx + tilt * DP0[0] / pl, dy = fy + tilt * DP0[1] / pl, dz = fz + tilt * DP0[2] / pl; const dl = Math.hypot(dx, dy, dz) || 1; dx /= dl; dy /= dl; dz /= dl;
            const vx = DI[o + 3], vy = DI[o + 4], vz = DI[o + 5], vl = Math.hypot(vx, vy, vz) || 1, bow = 0.3 * Lu * (1 - u);   // the middle lags: a stretched, bowed ligament
            for (let s = 0; s <= 18; s++) { const w = s / 18 - 0.5, bead = 1 + 0.65 * u * Math.cos(TAU * 2.5 * w + q * 6), b = bow * (1 - 4 * w * w);
              put(DP0[0] + dx * Lu * w - vx / vl * b, DP0[1] + dy * Lu * w - vy / vl * b, DP0[2] + dz * Lu * w - vz / vl * b, rad * (0.5 + 0.3 * u) * bead * (1 - 0.45 * Math.abs(w)), 1.3, fade); } }
          else { put(DP0[0], DP0[1], DP0[2], rad, 1.3, fade); const so = 0.25 * L * (q < 0.5 ? 1 : -1);
            dropAt(o, age * 0.85 + 0.15 * TP, DP1); put(DP1[0] + fx * so, DP1[1] + fy * so, DP1[2] + fz * so, rad * 0.42, 1.3, 0.8 * fade); }
          continue; }
        if (kind !== 1 || q < 0.07) { const rad = kind === 2 ? 0.0009 + 0.0012 * q : 0.0007 + 0.0009 * q, q2 = RCV[c + 4];
          const far = PINR > 0 ? 1 - 0.85 * smooth(Math.hypot(DP0[0], DP0[1], DP0[2]), PINR, PINR + 0.6) : 1;   // v4.6: the far drops fade (refs: the drops hang in the cloud)
          const q3 = RCV[c + 5], t0 = PINA[0] + (PINA[1] - PINA[0]) * q3, pf = PINK >= 1 || q3 < PINK ? 1 : 1 - smooth(age, t0, t0 + 40);
          const lw = limbC(c, age); if (pf > 0.02) put(DP0[0], DP0[1], DP0[2], rad, 1.3, pf * far * 1.25 * Math.exp(-age / 900) * (PINW > 0 ? PINB + PINW * q2 * q2 * q2 : 1), 0.25 * hzAge(age) * lw); }
        else { dropAt(o, Math.max(0, age - STREAK), DP1); if (NOUT > 0) sprayOutC(o, Math.max(0, age - STREAK), DP1, c); drift(i, o, Math.max(0, age - STREAK), DP1, 1);
          const pk = RCV[c + 1];   // v4.3: the beard comes in patches (v5.7: cached)
          const yin = HZIN > 0 ? smooth(age, 0, HZIN) : 1;   // v4.6: young spray fades in (a pure function of its age)
          const lw = limbC(c, age);   // v5.3: no limb-brightened outline on the old cloud
          line(DP1[0], DP1[1], DP1[2], DP0[0], DP0[1], DP0[2], DASH * lw * pk * (0.11 + 0.26 * q) * Math.exp(-age / LNT) * (DASHT > 0 ? Math.exp(-age / DASHT) : 1) * (HZC + (1 - HZC) * yin), lw * pk * (0.11 + 0.26 * q) * 2.5 * hzAge(age) * yin); } }
      // cobwebs (v4): lacy strands only where the fronts have met. A met bead pair sits on the meeting line; T (the arrival
      // time solved at the puncture) at that point says when they met, so strands show for WEBT ticks after a meeting and
      // fade. Strands join neighbouring meeting points with a sagging, wobbling thread and a few short side hairs.
      const tnow = tick - popTick, WEBT = +(Q.get('webt') || 60);   // v4.5: cobwebs linger in the cloud (v4.1-v4.4: 34)
      for (let k = 0; k < HALF; k += 6) {
        const k2 = k + 6; if (REF[k] < PI - 0.05 || REF[k2 % M] < PI - 0.05) continue;
        rimPos(RM[k], k, P6); const age = tnow - eT(P6[0], P6[1], P6[2]); if (age < 0 || age > WEBT) continue;
        const ax = P6[0], ay = P6[1], az = P6[2]; rimPos(RM[k2 % M], k2 % M, P6); const bx = P6[0], by = P6[1], bz = P6[2];
        const L = Math.hypot(bx - ax, by - ay, bz - az); if (L > 0.12 || L < 1e-5) continue;
        const fade = (1 - age / WEBT) * smooth(age, 0, 3), a = 0.30 * fade * (0.5 + hash2(k, ZSEED + 44)), lift = 0.004 + 0.012 * hash2(k, ZSEED + 45) + 0.0006 * age;
        let qx = ax * (1 + lift * 0.3), qy = ay * (1 + lift * 0.3), qz = az * (1 + lift * 0.3);
        for (let j = 1; j <= 8; j++) { const t = j / 8, sg = Math.sin(PI * t), wob = 0.006 * sg * Math.sin(t * 9 + k * 0.37 + tick * 0.07);
          const mx = ax + (bx - ax) * t, my = ay + (by - ay) * t, mz = az + (bz - az) * t, m = Math.hypot(mx, my, mz) || 1, rr = 1 + lift * (0.3 + 0.7 * sg);
          const x = mx / m * rr + wob * (by - ay) / L, y = my / m * rr - wob * (bx - ax) / L, z = mz / m * rr + wob * 0.5;
          line(qx, qy, qz, x, y, z, a); qx = x; qy = y; qz = z;
          if (j === 4 && hash2(k, ZSEED + 46) < 0.6) { const hl = 0.01 + 0.03 * hash2(k, tick + ZSEED), hx = x / m, hy = y / m, hz = z / m;   // a short side hair
            line(x, y, z, x + hl * (hx + 0.6 * (by - ay) / L), y + hl * (hy - 0.6 * (bx - ax) / L), z + hl * hz, 0.6 * a); } } }
    } else rimF.fill(0);
    if (view.vort) for (let i = 0; i < NV && n < PTMAX; i++) { const x = vb[3 * i] / SV, y = vb[3 * i + 1] / SV, z = vb[3 * i + 2] / SV; const o = 8 * n++; ptData[o] = x * 1.004; ptData[o + 1] = y * 1.004; ptData[o + 2] = z * 1.004; ptData[o + 3] = 0.006; ptData[o + 6] = G4[i] > 0 ? 1 : 2; }
    return n;
  }

  function render() {
    resize();
    if (cubeDirty) renderCube();
    const asp = W / H, P = persp(FOVY, asp, 0.1, 40), V = lookAt(EYE, [0, 0, 0], CUP);
    VP = mul(P, V.m); IVP = inv(VP); CAM = V;
    const pxWorld = 2 * Math.tan(FOVY / 2) / H;
    gl.bindFramebuffer(gl.FRAMEBUFFER, hdr.f); gl.viewport(0, 0, W, H);
    gl.depthMask(true); gl.clearColor(0, 0, 0, 1); gl.clearDepth(1); gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.disable(gl.DEPTH_TEST); gl.disable(gl.BLEND); gl.depthMask(false);
    gl.useProgram(pBg.p); gl.uniform2f(pBg.u.uRes, W, H); gl.uniformMatrix4fv(pBg.u.uInvVP, false, IVP); setEnv(pBg); gl.bindVertexArray(vaoEmpty); gl.drawArrays(gl.TRIANGLES, 0, 3);
    // points
    const tb0 = performance.now(); const np = buildPoints(); TM.bp += performance.now() - tb0; TM.nb++;
    gl.enable(gl.DEPTH_TEST); gl.depthFunc(gl.LEQUAL); gl.depthMask(true);
    if (np > 0) {
      gl.useProgram(pPt.p); setEnv(pPt); gl.uniformMatrix4fv(pPt.u.uVP, false, VP); gl.uniform1f(pPt.u.uFocal, H / (2 * Math.tan(FOVY / 2)));
      gl.uniform3fv(pPt.u.uCX, V.x); gl.uniform3fv(pPt.u.uCY, V.y); gl.uniform3fv(pPt.u.uCZ, V.z);
      gl.bindVertexArray(vaoPt); gl.bindBuffer(gl.ARRAY_BUFFER, ptBuf); gl.bufferData(gl.ARRAY_BUFFER, ptData.subarray(0, np * 8), gl.STREAM_DRAW); gl.drawArrays(gl.POINTS, 0, np);
    }
    if (nSh > 0) {   // v5.7: shaped drops
      gl.useProgram(pSh.p); setEnv(pSh); gl.uniformMatrix4fv(pSh.u.uVP, false, VP); gl.uniform1f(pSh.u.uFocal, H / (2 * Math.tan(FOVY / 2))); gl.uniform2f(pSh.u.uRes, W, H);
      gl.uniform3fv(pSh.u.uCX, V.x); gl.uniform3fv(pSh.u.uCY, V.y); gl.uniform3fv(pSh.u.uCZ, V.z);
      gl.bindVertexArray(vaoSh); gl.bindBuffer(gl.ARRAY_BUFFER, shBuf); gl.bufferData(gl.ARRAY_BUFFER, shData.subarray(0, nSh * 12), gl.STREAM_DRAW); gl.drawArrays(gl.POINTS, 0, nSh);
    }
    gl.depthMask(false);
    if (nLines > 0) {   // mist streaks and cobwebs, additive
      gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE); gl.useProgram(pLn.p); gl.uniformMatrix4fv(pLn.u.uVP, false, VP); gl.uniform1f(pLn.u.uLnK, HZ.ln);
      gl.bindVertexArray(vaoLn); gl.bindBuffer(gl.ARRAY_BUFFER, lnBuf); gl.bufferData(gl.ARRAY_BUFFER, lineData.subarray(0, nLines * 5), gl.STREAM_DRAW); gl.drawArrays(gl.LINES, 0, nLines);
    }
    if (nFlap > 0) {    // the splayed flap band, thin-film shaded like the sphere
      gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA); gl.useProgram(pFlap.p); setEnv(pFlap);
      gl.uniformMatrix4fv(pFlap.u.uVP, false, VP); gl.uniform3fv(pFlap.u.uCam, EYE); gl.uniform1f(pFlap.u.uGain, view.gain);
      gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_CUBE_MAP, cubeTex); gl.uniform1i(pFlap.u.uThick, 0);
      gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, lutTex); gl.uniform1i(pFlap.u.uLUT, 1);
      gl.bindVertexArray(vaoFlap); gl.bindBuffer(gl.ARRAY_BUFFER, flapBuf); gl.bufferData(gl.ARRAY_BUFFER, flapPos.subarray(0, nFlap * 10), gl.STREAM_DRAW);
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, flapIbo); if (nFlapIdx > 0) gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, flapIdxDyn.subarray(0, nFlapIdx), gl.STREAM_DRAW);
      if (nFlapIdx > 0) gl.drawElements(gl.TRIANGLES, nFlapIdx, gl.UNSIGNED_INT, 0);
    }
    const popped = popTick >= 0 && tick >= popTick;
    if (popped && HZ.k > 0 && (nLines > 0 || np > 0)) {   // v4.2: the mist haze, added before the film so the film lies over it
      drawHaze(np, H / (2 * Math.tan(FOVY / 2)));
      gl.bindFramebuffer(gl.FRAMEBUFFER, hdr.f); gl.viewport(0, 0, W, H); gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA); gl.useProgram(pHzAdd.p); gl.uniform1f(pHzAdd.u.uAbs, HZA);
      gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, hz.a.t); gl.uniform1i(pHzAdd.u.uA, 0);
      gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, hz.d.t); gl.uniform1i(pHzAdd.u.uB, 1);
      gl.uniform3fv(pHzAdd.u.uTint, HZ.tint); gl.uniform1f(pHzAdd.u.uK, HZ.k); gl.uniform1f(pHzAdd.u.uW, HZ.wide); gl.uniform1f(pHzAdd.u.uSat, HZ.sat); gl.bindVertexArray(vaoEmpty); gl.drawArrays(gl.TRIANGLES, 0, 3);
      gl.activeTexture(gl.TEXTURE0); gl.enable(gl.DEPTH_TEST); }
    // film: back layer, then front layer
    gl.bindTexture(gl.TEXTURE_2D, rimTex); gl.texSubImage2D(gl.TEXTURE_2D, 0, 0, 0, M, 1, gl.RED, gl.FLOAT, rimF);
    gl.depthMask(false); gl.enable(gl.BLEND); gl.blendFunc(gl.ONE, gl.ONE_MINUS_SRC_ALPHA);
    gl.useProgram(pFilm.p); setEnv(pFilm);
    gl.uniformMatrix4fv(pFilm.u.uInvVP, false, IVP); gl.uniformMatrix4fv(pFilm.u.uVP, false, VP); gl.uniform3fv(pFilm.u.uCam, EYE);
    gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_CUBE_MAP, cubeTex); gl.uniform1i(pFilm.u.uThick, 0);
    gl.activeTexture(gl.TEXTURE1); gl.bindTexture(gl.TEXTURE_2D, lutTex); gl.uniform1i(pFilm.u.uLUT, 1);
    gl.activeTexture(gl.TEXTURE2); gl.bindTexture(gl.TEXTURE_2D, rimTex); gl.uniform1i(pFilm.u.uRim, 2);
    gl.uniform1i(pFilm.u.uPop, popped ? 1 : 0); gl.uniform1i(pFilm.u.uM, M); gl.uniform3fv(pFilm.u.uC, C); gl.uniform3fv(pFilm.u.uE1, E1); gl.uniform3fv(pFilm.u.uE2, E2);
    gl.uniform1f(pFilm.u.uPx, pxWorld); gl.uniform1f(pFilm.u.uGain, view.gain);
    { let g = 0; if (popped) { for (let k = 0; k < M; k += 4) g += (1 - Math.cos(Math.min(PI, reff(ra, k)))) / 2; g /= M / 4; }   // fraction of the film gone (read-only)
      gl.uniform1f(pFilm.u.uMilk, MILK * smooth(g, MILKG, 0.985)); }
    gl.bindVertexArray(vaoEmpty);
    gl.uniform1i(pFilm.u.uLayer, 0); gl.drawArrays(gl.TRIANGLES, 0, 3);
    gl.uniform1i(pFilm.u.uLayer, 1); gl.drawArrays(gl.TRIANGLES, 0, 3);
    gl.disable(gl.BLEND); gl.disable(gl.DEPTH_TEST);
    // tone map to the canvas
    gl.bindFramebuffer(gl.FRAMEBUFFER, null); gl.viewport(0, 0, W, H);
    gl.useProgram(pTone.p); gl.activeTexture(gl.TEXTURE0); gl.bindTexture(gl.TEXTURE_2D, hdr.t); gl.uniform1i(pTone.u.uHdr, 0); gl.uniform1f(pTone.u.uExp, view.exposure);
    gl.drawArrays(gl.TRIANGLES, 0, 3); gl.bindVertexArray(null);
  }
  const view = { gain: +(Q.get('gain') || (LOOK_C ? 1.15 : 1.4)), exposure: +(Q.get('exp') || (LOOK_C ? 2.0 : 2.2)), vort: Q.get('vort') === '1' };

  // ---------- init ----------
  vortexInit(); uploadVortices(); tracerPass(0, 0);
  const snap0 = snapshot(), hash0 = fnv(snap0);
  let lastCheck = null, lastVerify = null;

  // ---------- UI / loop ----------
  // 2026-11-17 rework: ONE owner for every state change. The buttons, the click on the bubble and the PROTO tool hooks only
  // put commands in a queue; the frame loop (pump, below) is the only code that runs them, steps the module (stepF, stepB,
  // the puncture) or writes the controller state (running, dir, speed, the demo's hold, the check result, the playback
  // bookkeeping). Verify and Reset are exclusive jobs: while one runs, each frame advances only that job by one slice,
  // nothing else steps, and commands that arrive meanwhile wait and then run in order. A check's counts are therefore the
  // steps it ran itself, and its verdict compares the module snapshot taken when it started with the one where it ended.
  let running = !MANUAL, dir = 1, speed = 1, acc = 0, last = performance.now(), demoState = DEMO ? 'fwd' : null, holdUntil = 0;
  const fpsT = []; let fps = 0, busy = false;   // busy: the running job's progress message (false: no job)
  const queue = [], QMAX = 64;                  // pending commands { op, arg, res, rej }
  let job = null;                               // the exclusive job: { name, gen, res }
  let maxTickSeen = 0;                          // furthest tick since the state was last at tick 0 (a check's inner ticks not counted)
  let queueNoticeUntil = 0;
  let popNotice = '', popNoticeUntil = 0;       // a refused puncture request, shown in the HUD (counted from first display)
  function send(op, arg, control = false) {
    return new Promise((res, rej) => {
      if (queue.length < QMAX) { queue.push({ op, arg, res, rej }); return; }
      if (control) {
        queueNoticeUntil = Infinity;   // start counting once the HUD actually displays the refusal
        if (op === 'speed') $('speed').value = String(speed);
      }
      rej(new Error('command queue full'));
    });
  }
  function sendControl(op, arg) { send(op, arg, true).catch(() => {}); }
  function moved() { if (tick === 0) maxTickSeen = 0; else if (tick > maxTickSeen) maxTickSeen = tick; }   // after every state move
  function setBusy(msg) { busy = msg; $('reset').disabled = !!msg; $('verify').disabled = !!msg; }
  function freezeCheck(check) {
    if (check.mod) Object.freeze(check.mod);
    if (check.tr) Object.freeze(check.tr);
    return Object.freeze(check);
  }
  function checkAtZero(label, steps, src) {   // compare with the load-time state; steps: backward steps that brought us here (0: none ran)
    if (!steps) return { kind: 'none', src, ticks: 'no ticks tested: already at tick 0' };
    try { const s = snapshot(), d = diffSplit(snap0, s); return { kind: 'tested', src, ticks: label, mod: d.mod, tr: d.tr, hash: fnv(s), hash0 }; }
    catch (err) { return { kind: 'incomplete', src, ticks: `check failed (${err && err.message}) at tick 0: no reversal verdict` }; }
  }
  function setDir(d) { dir = d; $('rev').classList.toggle('on', dir < 0); }
  const setHtml = (el, h) => { if (el.__h !== h) { el.__h = h; el.innerHTML = h; } };   // v5.7: touch the DOM only on a change
  function checkHtml(check) {
    const label = check.src === 'verify' ? 'verify reversal' : 'reversal check';
    if (check.kind !== 'tested') return `${label} · <b>${check.ticks}</b>`;
    const mb = n => (n / 1e6).toFixed(2);
    return `${label} (${check.ticks}): module snapshot <b class="${check.mod.diff === 0 ? 'ok' : 'bad'}">${check.mod.diff} bytes of ${mb(check.mod.bytes)} MB differ</b>` +
      (check.tr ? ` · GPU tracers (browser measurement, not proved) <b class="${check.tr.diff === 0 ? 'ok' : 'bad'}">${check.tr.diff} bytes of ${mb(check.tr.bytes)} MB differ</b>`
        : ' · GPU tracer comparison unavailable (WebGL context lost or the read failed)');
  }
  function updateHud() {
    const ph = phase(), popped = popTick >= 0 && tick >= popTick;
    const slow = $('slow');
    if (popped) { const tphys = (tick - popTick) / 60 / SLOWMO * 1000; slow.style.display = 'block'; setHtml(slow, `slow motion &times;${SLOWMO} <span>t = ${tphys.toFixed(2)} ms after puncture &middot; Taylor-Culick rim, 4 cm bubble &middot; </span><span>swirl clock ${PSUB}/${QSUB} during the pop (stylised: in real time the swirl is frozen)</span>`); }
    else { slow.style.display = 'none'; }
    const head = `state: vortex_a1.wasm ${VEC.sha.slice(0, 8)} (digest ok)`;
    // page pass 1, round 1 follow-up: a finished check is wrapped in span.chk, which the phone layout hides (the result
    // card beside the verify button shows it); the text stays in #read, word for word, for the capture harness and suites
    // (status carries its leading " · ", inside the span for a check, so nothing dangles when the span is hidden)
    const chk = h => `<span class="chk"> · ${h}</span>`;
    let status = busy ? ` · ${busy}` : lastCheck ? chk(checkHtml(lastCheck)) : ` · state hash at tick 0: ${hash0}`;
    if (lastVerify && lastVerify !== lastCheck)
      status = chk(checkHtml(lastVerify) + '<br>') + status.replace(/^(<span class="chk">)? · /, '$1');
    const now = performance.now();
    if (queueNoticeUntil === Infinity) queueNoticeUntil = now + 3000;
    if (queueNoticeUntil > now) status += '<br><b class="bad">Control queue full. Input refused. Try again in a moment.</b>';
    if (popNoticeUntil === Infinity) popNoticeUntil = now + 3000;
    if (popNoticeUntil > now) status += `<br><b class="bad">${popNotice}</b>` +   // worded as past: it stays true after the state moves on
      (popTick >= 0 ? ` To puncture elsewhere, rewind to before tick ${popTick} or reset.` : '');   // advice only while it applies, from the current state
    setHtml($('read'), `tick ${tick} · ${ph}${dir < 0 ? ' · reversing' : ''}${MANUAL ? '' : ` · ${fps.toFixed(0)} fps`} · seed ${SEED} · ${NV} vortices · ${(NVERT / 1000).toFixed(0)}k tracers · ${nd} droplets<br>${head}${status}`);
    $('play').textContent = running ? 'pause' : 'run';
    updateStage(now);
  }
  // ---------- presentation only (page pass 1, 2026-11-21) ----------
  // Reads the controller state; never steps the module, queues a command or writes controller state. It draws: the
  // verify button's plan, the latest check result large beside it, a read-only timeline, and a caption when the auto film
  // turns back and when playback arrives back at tick 0.
  const fmtInt = n => String(n).replace(/\B(?=(\d{3})+(?!\d))/g, ',');
  const stage = { seen: null, seenTick: 0, back: false, capUntil: 0, cap: '', shown: null, vjob: null, shownFor: new WeakMap(), planFor: new WeakMap() };
  function verifyParts() {   // verifyJob's default budget N from here, and the ticks left before the end of the pop
    const N = Math.max(200, Math.min(1200, (popTick >= 0 ? popTick + AFTER : AUTO + AFTER) - tick));
    const P = popTick >= 0 ? popTick : (event && event.tick > tick && event.tick < AUTO ? event.tick : AUTO);
    return { N, cap: Math.max(0, P + AFTER - tick) };
  }
  function verifyPlan() {   // the forward ticks the button's check would run from here (verifyJob's N, capped at the end of the pop)
    const { N, cap } = verifyParts();
    return Math.min(N, cap);
  }
  // Three numbers, kept apart (round 1, finding 5; round 2, finding 3). The PREVIEW: what the button shows while idle,
  // from the state as drawn. The COMMITTED PLAN: what the job will run, from the state it starts in (commands queued
  // before Verify, such as a click on the bubble in the same frame, run first and can change it), shown on the button
  // while it runs. The ACTUAL COUNTS: what ran, in the result. The card adds a plan-change note only when the committed
  // plan differs from the preview the button showed at the click; an interrupted test is explained by its own result.
  function committedPlan() {
    const v = stage.vjob, m = /verifying: (forward|back) (\d+)\/(\d+)/.exec(busy || '');
    if (m && m[1] === 'forward') { v.N = +m[3]; v.plan = Math.min(v.N, v.cap); }   // the budget, as the job reports it
    if (m && m[1] === 'back') return +m[3];            // backward: exactly the forward ticks that ran
    return v.plan;
  }
  function checkTitle(c) { return c.src === 'verify' ? 'verify reversal' : c.src === 'reset' ? 'reset' : 'playback back at tick 0'; }
  function resultHtml(c) {
    const mb = n => (n / 1e6).toFixed(2);
    if (c.kind !== 'tested') return `<div class="t">${checkTitle(c)}</div><div class="big">${c.kind === 'none' ? 'no ticks tested' : 'no verdict'}</div><div>${c.ticks}</div>`;
    const ok = c.mod.diff === 0;
    return `<div class="t">${checkTitle(c)}: ${c.ticks}</div>` +
      `<div class="big ${ok ? 'ok' : 'bad'}">${fmtInt(c.mod.diff)} bytes differ</div>` +
      `<div>of the ${fmtInt(c.mod.bytes)} bytes (${mb(c.mod.bytes)} MB) of the module snapshot, the memory the proofs are about, compared with ${c.src === 'verify' ? 'where the test started' : 'tick 0 at load'}</div>` +
      (c.tr ? `<div>GPU tracers (browser measurement, not proved): <b class="${c.tr.diff === 0 ? 'ok' : 'bad'}">${fmtInt(c.tr.diff)} of ${mb(c.tr.bytes)} MB differ</b></div>`
        : '<div>GPU tracer comparison unavailable (WebGL context lost or the read failed)</div>') +
      '<div>A test in your browser, not a proof.</div>';
  }
  function updateStage(now) {
    // the verify button: its plan, or an honest "nothing to test" at the end of the pop (it stays clickable and then
    // reports "no ticks tested", as the controller always has)
    const n = verifyPlan(), idle = !busy && n === 0;
    $('verify').classList.toggle('idle', idle);
    // the committed plan: read in the frame the job starts (startJob has run, the job has not stepped), so from its start state
    if (job && job.name === 'verify' && (!stage.vjob || stage.vjob.job !== job)) {
      const v = verifyParts(); stage.vjob = { job, t0: tick, N: v.N, cap: v.cap, plan: Math.min(v.N, v.cap), result: null }; }
    // and, in the frame it finishes (nothing else runs in that frame), tie the plan to its result
    if (stage.vjob && !stage.vjob.result && stage.vjob.job !== job && lastVerify) { stage.vjob.result = lastVerify; stage.planFor.set(lastVerify, stage.vjob); }
    const vj = job && job.name === 'verify' ? committedPlan() : null;
    stage.shown = busy || queue.length ? null : { n: idle ? 0 : n, t: tick };
    setHtml($('vplan'), vj !== null ? `running: ${fmtInt(vj)} ticks forward from tick ${stage.vjob.t0}, ${fmtInt(vj)} back; nothing else moves until it finishes`
      : busy ? 'running: nothing else moves until it finishes' : queue.length ? 'test: the plan is set when it starts (commands waiting)'
      : idle ? 'nothing to test here: the pop has ended; reverse first'
      : `preview from tick ${tick}: ${fmtInt(n)} ticks forward, ${fmtInt(n)} back, then compare`);
    // the result card: progress while a job runs, else the latest check (and an earlier Verify the HUD still shows)
    const c = lastCheck;
    if (c !== stage.seen) {
      stage.seen = c; stage.seenTick = tick;
      if (c && c.src === 'playback' && c.kind === 'tested') {
        stage.cap = `Back at tick 0<span><b class="${c.mod.diff === 0 ? 'ok' : 'bad'}">${fmtInt(c.mod.diff)} bytes</b> of the ${(c.mod.bytes / 1e6).toFixed(2)} MB module snapshot differ from the start. A test in your browser, not a proof.</span>`;
        stage.capUntil = now + 4000; }
    }
    let h;
    if (busy) {
      const m = /(forward|back) (\d+)\/(\d+)/.exec(busy);
      const f = m ? (m[1] === 'forward' ? +m[2] / (2 * +m[3]) : 0.5 + +m[2] / (2 * +m[3])) : null;
      h = `<div class="t">${job && job.name === 'reset' ? 'reset' : vj !== null ? `verify reversal: ${fmtInt(vj)} ticks forward from tick ${stage.vjob.t0}, then back` : 'verify reversal'}</div><div class="big">${busy}</div>` +
        (f === null ? '' : `<div class="bar"><i style="width:${(100 * f).toFixed(1)}%"></i></div>`) + '<div>Only this check moves the simulation until it finishes.</div>';
    } else if (c) {
      const sh = stage.shownFor.get(c), vp = c.src === 'verify' ? stage.planFor.get(c) : undefined;
      h = resultHtml(c) + (vp && c.kind === 'incomplete' && c.forward !== undefined
        ? `<div>Planned when the test started: ${fmtInt(vp.plan)} ticks forward from tick ${vp.t0}, then back; it stopped after ${fmtInt(c.forward)} forward and ${fmtInt(c.back || 0)} back.</div>` : '')
        + (vp && sh && (sh.n !== vp.plan || sh.t !== vp.t0)
        ? `<div>The button's preview when clicked was ${fmtInt(sh.n)} ticks each way from tick ${sh.t}; a command queued before the test ran first and changed the state, so the plan committed when the test started was ${fmtInt(vp.plan)} ticks each way from tick ${vp.t0}.</div>` : '') + (lastVerify && lastVerify !== c && lastVerify.kind === 'tested'
        ? `<div>Earlier verify reversal (${lastVerify.ticks}): <b class="${lastVerify.mod.diff === 0 ? 'ok' : 'bad'}">${fmtInt(lastVerify.mod.diff)} bytes differ</b></div>` : '');
    } else h = '<div class="t">verify reversal</div><div>Runs the module forward from this tick, then back the same number of ticks, and compares its 1.95 MB module snapshot with where it started, byte for byte. A test in your browser, not a proof.</div>';
    setHtml($('vres'), h);
    $('vres').classList.toggle('old', !busy && !!c && tick !== stage.seenTick);
    // the turn of the auto film (its timing is the controller's; this only announces it)
    const back = demoState === 'rev' && dir < 0 && running;
    if (back && !stage.back) { stage.cap = 'Now backwards<span>the same module, tick_backward, one tick at a time, back toward tick 0</span>'; stage.capUntil = now + 2800; }
    stage.back = back;
    const turn = $('turn'), on = now < stage.capUntil;
    if (turn.style.display !== (on ? 'block' : 'none')) turn.style.display = on ? 'block' : 'none';
    if (on) setHtml(turn, stage.cap);
    // the timeline, read-only: 0, the puncture (planned or done), the end of the pop, the furthest tick reached, now.
    // The puncture label has its own row under the other two; near either end it starts or ends at its marker.
    const P = popTick >= 0 ? popTick : (event && event.tick < AUTO ? event.tick : AUTO), end = P + AFTER;
    const x = t => (100 * Math.max(0, Math.min(1, t / end))).toFixed(2) + '%';
    setHtml($('tl'), `<div class="track"></div><div class="seen" style="width:${x(Math.max(maxTickSeen, tick))}"></div>` +
      `<div class="mk" style="left:0%"></div><div class="mk p" style="left:${x(P)}"></div><div class="mk" style="left:100%"></div>` +
      `<div class="lb l" style="left:0%">tick 0</div><div class="lb p${P / end < 0.25 ? ' l' : P / end > 0.75 ? ' r' : ''}" style="left:${x(P)}">puncture ${popTick >= 0 ? 'at' : 'due at'} ${P}</div>` +
      `<div class="lb r" style="left:100%">end of pop ${end}</div><div class="th" style="left:${x(tick)}" title="tick ${tick}"></div>`);
  }
  function endRun() {   // playback stopped (end of the pop, tick 0, or a refused step): direction and the demo's hold
    if (dir < 0 && tick === 0) setDir(1);
    running = false; acc = 0;
    if (demoState) { demoState = 'hold'; holdUntil = performance.now() + (tick === 0 ? 2500 : 1200); }
  }
  function playStep(dtms, now) {   // playback, run by pump only when no job is running and the queue is empty
    if (!MANUAL && running) {
      acc += speed * dtms / (1000 / 60); let n = 0;
      while (acc >= 1 && n < 8) { acc -= 1; n++;
        const was = maxTickSeen, ok = dir > 0 ? stepF() : stepB();
        if (!ok) { endRun(); break; }
        moved();
        // a new result only from the playback step that itself arrives at tick 0
        if (dir < 0 && tick === 0) { lastCheck = freezeCheck(checkAtZero(`back at tick 0 from tick ${was}, the furthest reached`, 1, 'playback')); endRun(); break; } }
      if (acc > 4) acc = 0;
    }
    if (demoState === 'hold' && now > holdUntil) { if (tick > 0) { setDir(-1); demoState = 'rev'; } else { setDir(1); demoState = 'fwd'; } running = true; }
  }
  function frame(now) {
    const dtms = Math.min(100, now - last); last = now;
    fpsT.push(now); while (fpsT.length && fpsT[0] < now - 1000) fpsT.shift(); fps = fpsT.length;
    try { pump(dtms, now); } catch (err) { fail('controller: ' + (err && err.message)); }
    try { drawFrame(); } catch (err) { fail('drawing: ' + (err && err.message)); }
    updateHud();
    requestAnimationFrame(frame);
  }
  let lastSig = '', forceRender = true;
  function drawFrame(force = false) {
    // While paused or between ticks, reuse the last picture if its inputs are unchanged.
    const sig = tick + '|' + canvas.clientWidth + 'x' + canvas.clientHeight + '|' + devicePixelRatio + '|' + LIGHT.mode + '|' + popTick;
    if (force || forceRender || sig !== lastSig) { lastSig = sig; forceRender = false; render(); }
  }
  function pump(dtms, now) {
    // A job owns its completion frame too, so the HUD can show the verdict before any further movement.
    if (job) { stepJob(); return; }
    while (!job && queue.length) {
      const command = queue.shift();
      runCommand(command);
      if (command.op === 'goTo') return;   // leave the captured picture on screen for this frame
    }
    if (!job) playStep(dtms, now);
  }
  function startJob(name, gen, res, msg) { lastVerify = null; job = { name, gen, res }; setBusy(msg); }
  function stepJob() {
    let r;
    try { r = job.gen.next(); }
    catch (err) { moved(); r = { done: true, value: { kind: 'incomplete', src: job.name, ticks: `${job.name} failed (${err && err.message}) at tick ${tick}: no reversal verdict` } }; }
    if (!r.done) { setBusy(r.value); return; }
    const j = job; job = null; setBusy(false);
    lastCheck = freezeCheck(r.value);
    if (j.name === 'verify') lastVerify = lastCheck;
    j.res(lastCheck);
  }
  const SLICE = 25, SLICE_MS = 30;   // a job runs at most SLICE module steps (or SLICE_MS) per frame, then the page draws
  function* resetJob() {
    demoState = null; setDir(1); event = null; running = !MANUAL; acc = 0;
    let i = 0, t = performance.now();
    while (tick > 0 && stepB()) { i++; if (i % SLICE === 0 || performance.now() - t > SLICE_MS) { yield `playing back to tick 0: ${tick}…`; t = performance.now(); } }
    moved();
    if (tick === 0) return checkAtZero(`reset: ${i} ticks back to tick 0`, i, 'reset');
    return { kind: 'incomplete', src: 'reset', ticks: `reset stopped at tick ${tick} after ${i} ticks back: no reversal verdict` };
  }
  function* verifyJob(N) {   // N: forward tick budget; undefined = the button's (toward the end of the pop), fixed when the job starts
    if (N === undefined) N = Math.max(200, Math.min(1200, (popTick >= 0 ? popTick + AFTER : AUTO + AFTER) - tick));
    const t0 = tick; let s0, n = 0, m = 0, t = performance.now();
    const slice = () => (n + m) % SLICE === 0 || performance.now() - t > SLICE_MS;
    try {
      s0 = snapshot();
      for (let i = 0; i < N; i++) { if (!stepF()) break; n++; if (slice()) { yield `verifying: forward ${n}/${N}…`; t = performance.now(); } }
      for (let i = 0; i < n; i++) { if (!stepB()) break; m++; if (slice()) { yield `verifying: back ${m}/${n}…`; t = performance.now(); } }
    } catch (err) {
      moved(); return { kind: 'incomplete', src: 'verify', ticks: `check failed (${err && err.message}) at tick ${tick}: no reversal verdict`, forward: n, back: m };
    }
    moved();
    const atEnd = popTick >= 0 && tick >= popTick + AFTER;
    if (n === 0) return { kind: 'none', src: 'verify', ticks: atEnd ? `no ticks tested: tick ${t0} is the end of the pop, where the page stops going forward; reverse some way first, then verify` : `no ticks tested: the page could not go forward from tick ${t0}`, forward: 0, back: 0 };
    if (m !== n || tick !== t0) return { kind: 'incomplete', src: 'verify', ticks: `check incomplete (${n} forward from tick ${t0}, ${m} back, now at tick ${tick}): no reversal verdict`, forward: n, back: m };
    try { const s1 = snapshot(), d = diffSplit(s0, s1); return { kind: 'tested', src: 'verify', ticks: `${n} ticks forward from tick ${t0}, ${m} back`, forward: n, back: m, mod: d.mod, tr: d.tr, hash: fnv(s1), hash0: fnv(s0), where: diffParts(s0, s1), healErr, unpunctureWordsOff: lastHeal }; }
    catch (err) { return { kind: 'incomplete', src: 'verify', ticks: `check failed (${err && err.message}) reading the state back at tick ${tick}: no reversal verdict`, forward: n, back: m }; }
  }
  // v4.5.1: a click at tick 0 is scheduled for tick 1, right after the first swirl step, as in the engine's host order
  // (SPEC 4: a puncture follows a swirl tick, so P >= 1). v4.5 applied it at tick 0, where no backward step reaches the
  // un-puncture (stepB stops at tick 0): the pop state stayed at tick 0 (16,631 bytes off in Ben's report) and, with
  // popTick stuck at 0, every later click was refused. A click elsewhere applies at once, as before.
  // One puncture per film: a request is refused (false, and a HUD message) when the bubble is already punctured or a
  // tick-0 request is still waiting for tick 1 (event.fresh). A remembered click from before a rewind is not fresh: a
  // new click replaces it, and the remembered one replays on the way forward only if no new click came.
  function refusePop(msg) { popNotice = msg; popNoticeUntil = Infinity; return false; }
  function puncture(p) {
    if (popTick >= 0) return refusePop(`Puncture request refused: the bubble had already been punctured at tick ${popTick}.`);
    if (event && event.fresh) return refusePop('Puncture request refused: another request was already waiting for tick 1.');
    const c = norm(p).map(v => Math.round(v * SV));
    if (tick === 0) event = { tick: 1, c, fresh: true }; else { event = { tick, c }; applyPuncture(); }
    if (dir < 0) setDir(1);
    if (!MANUAL) { running = true; if (demoState) demoState = 'fwd'; }   // v4.5.1: a click starts the pop (ends the demo's hold)
    return true; }
  function goToNow(T) {
    T = Math.max(0, Math.round(T)); let n = 0;
    while (tick < T && stepF()) { if (++n % 64 === 0) gl.flush(); }
    while (tick > T && stepB()) { if (++n % 64 === 0) gl.flush(); }
    moved();
    drawFrame(true);
    gl.finish();
    if (gl.isContextLost()) throw new Error('WebGL context lost during capture');
    return info();
  }
  function benchNow() { const sync = () => { const b = new Int32Array(4); gl.bindFramebuffer(gl.FRAMEBUFFER, T[ib].f); gl.readPixels(0, 0, 1, 1, gl.RGBA_INTEGER, gl.INT, b); };
    sync(); let t = performance.now(); for (let i = 0; i < 30; i++) { uploadVortices(); tracerPass(1); } sync(); const tp = (performance.now() - t) / 30;
    for (let i = 0; i < 30; i++) { uploadVortices(); tracerPass(-1); } sync();
    t = performance.now(); for (let i = 0; i < 10; i++) renderCube(); sync(); const tc = (performance.now() - t) / 10;
    t = performance.now(); for (let i = 0; i < 30; i++) vortexVel(vb); const tv = (performance.now() - t) / 30;
    t = performance.now(); for (let i = 0; i < 10; i++) render(); sync(); const tr = (performance.now() - t) / 10;
    return `tracer ${tp.toFixed(2)} ms, cube ${tc.toFixed(2)} ms, vortexCPU ${tv.toFixed(2)} ms, render ${tr.toFixed(2)} ms @tick ${tick}`; }
  function runCommand(c) {   // called only by pump; Verify and Reset start a job, everything else runs to completion here
    try {
      switch (c.op) {
        case 'verify': if (c.arg !== undefined && !(c.arg >= 1)) { c.res(null); return; } startJob('verify', verifyJob(c.arg), c.res, 'verifying…'); return;
        case 'reset': startJob('reset', resetJob(), c.res, 'playing back to tick 0…'); return;
        case 'play': running = !running; demoState = null; break;
        case 'rev': setDir(-dir); running = true; demoState = null; break;
        case 'run': running = c.arg !== false; break;
        case 'setDir': setDir(c.arg); break;
        case 'speed': speed = c.arg; $('speed').value = String(speed); break;
        case 'pop': c.res(puncture(c.arg)); return;
        case 'goTo': c.res(goToNow(c.arg)); return;
        case 'rev0': { let n = 0; while (stepB()) n++; moved(); c.res(n); return; }
        case 'scan': { const out = []; while (tick < c.arg && stepF()) out.push([tick, +rimGone().toFixed(4)]); moved(); c.res(out); return; }
        case 'bench': c.res(benchNow()); return;
        default: throw new Error('unknown command ' + c.op);
      }
      c.res();
    } catch (err) { moved(); c.rej(err); }
  }

  // click to puncture
  canvas.addEventListener('pointerdown', ev => { forceRender = true;
    if (!VP) return; const r = canvas.getBoundingClientRect(), x = (ev.clientX - r.left) / r.width * 2 - 1, y = 1 - (ev.clientY - r.top) / r.height * 2;
    const pn = mulv(IVP, [x, y, -1, 1]), pf = mulv(IVP, [x, y, 1, 1]); const a = pn.map(v => v / pn[3]), b = pf.map(v => v / pf[3]);
    const rd = norm([b[0] - a[0], b[1] - a[1], b[2] - a[2]]), bb = dot(EYE, rd), cc = dot(EYE, EYE) - 1, disc = bb * bb - cc; if (disc <= 0) return;
    const t = -bb - Math.sqrt(disc), p = [EYE[0] + t * rd[0], EYE[1] + t * rd[1], EYE[2] + t * rd[2]];
    sendControl('pop', p);
  });
  function mulv(m, v) { const o = [0, 0, 0, 0]; for (let r = 0; r < 4; r++) for (let k = 0; k < 4; k++) o[r] += m[k * 4 + r] * v[k]; return o; }

  $('play').onclick = () => sendControl('play');
  $('rev').onclick = () => sendControl('rev');
  $('reset').onclick = () => sendControl('reset');
  $('vort').onclick = () => { view.vort = !view.vort; $('vort').classList.toggle('on', view.vort); forceRender = true; };   // drawing only (redraw even when paused)
  $('vort').classList.toggle('on', view.vort);
  $('speed').onchange = e => sendControl('speed', +e.target.value);
  $('verify').onclick = () => {   // as sendControl('verify'); the promise only lets the card name the preview the button showed
    const shown = stage.shown;
    send('verify', undefined, true).then(r => { if (r && typeof r === 'object') stage.shownFor.set(r, shown); }, () => {});
  };
  // State-changing hooks return promises and run in queue order. Queries answer synchronously.
  // timing() reads and clears drawing/step counters; light(mode) changes the lighting and requests a redraw.
  function rimGone() { if (popTick < 0 || tick < popTick) return 0; let g = 0; for (let k = 0; k < M; k++) g += (1 - Math.cos(Math.min(PI, reff(ra, k) * 1))) / 2; return g / M; }
  function info() { return { tick, phase: phase(), popTick, droplets: nd, fps, vortices: NV, tracers: NVERT, dir, running, check: lastCheck, hash0, demo: demoState, busy: job ? job.name : null, queued: queue.length, eventTick: event ? event.tick : null, seed: SEED, clk: `${PSUB}/${QSUB}`, healErr, lastHeal }; }
  function stats() { const kinds = [0, 0, 0, 0, 0, 0]; for (let i = 0; i < nd; i++) kinds[DI[REC * i + 7] >>> 16]++;
    let crests = 0, zmax = 0; for (let k = 0; k < M; k++) { const z = ZQ[k]; if (z > zmax) zmax = z; if (z >= 0.0035 * SZ && z > ZQ[(k + M - 1) & (M - 1)] && z >= ZQ[(k + 1) & (M - 1)]) crests++; }
    let rv = 0, pool = 0, dv = 0, big = 0; for (let k = 0; k < M; k++) rv += RV[k]; for (let j = 0; j < NPOOL; j++) pool += POOL[j];
    for (let i = 0; i < nd; i++) { const kd = DI[REC * i + 7] >>> 16; if (kd !== 4) dv += DI[REC * i + 10]; if (kd === 3) big++; }
    return { tick, nd, kinds, crests, zmax: zmax / SZ, liquid: { rim: rv / VSC, pools: pool / VSC, drops: dv / VSC, total: (rv + pool + dv) / VSC }, bigDrops: big }; }
  window.PROTO = {
    // v5.8w2: ve2 canonical-memory digest (host/ve2_host.js; = core/ve2_run.c's) and the thickness map read at the last puncture
    canonHash, modTick: () => vex.tick() >>> 0, popTickRaw: () => vex.pop_tick() >>> 0, heal: () => vex.heal_err() >>> 0, sha: () => VEC.sha, shaOk: () => VEC.ok, hmapB64: () => { const b = new Uint8Array(HMAP.buffer); let s = ''; for (let i = 0; i < b.length; i += 32768) s += String.fromCharCode.apply(null, b.subarray(i, i + 32768)); return btoa(s); },
    ready: Promise.resolve(true),
    goTo: T => send('goTo', T), info, verify: N => send('verify', N), reset: () => send('reset'), stats, timing() { const r = { pop: TM.pop / Math.max(1, TM.n), swirlCPU: TM.sw / Math.max(1, TM.n), buildPoints: TM.bp / Math.max(1, TM.nb) }; for (const k in TM) TM[k] = 0; return r; }, hash: () => fnv(snapshot()),
    pop(lon, lat) { return send('pop', sph(lon, lat)); },
    // v4.5.1, for tools/multicycle.mjs: rev0 = the page's reverse loop (step back until it stops), check0 = the byte
    // compare with the initial state that the page shows after a reversal, with the parts that differ
    rev0() { return send('rev0'); },   // 2026-11-17 rework: the hooks that step or change the controller state are commands (see pump)
    check0() { const s = snapshot(), d = diffSplit(snap0, s); return { tick, mod: d.mod, tr: d.tr, where: diffParts(snap0, s), hash: fnv(s), hash0 }; },   // 2026-11-17: mod and tr counted separately
    // v4.2, read-only: fraction of the film gone (mean over bead pairs of the cap area swept), for picking comparison phases
    rimGone,
    capDir() { if (popTick < 0 || tick < popTick) return null; const P = new Float64Array(6); let x = 0, y = 0, z = 0;   // read-only: centroid of the rim loop
      for (let k = 0; k < M; k++) { rimPos((ra[k] + rb[k]) / (2 * SR), k, P); x += P[0]; y += P[1]; z += P[2]; } const l = Math.hypot(x, y, z) || 1; return [x / l, y / l, z / l]; },
    // v5.0, read-only: rim bead positions (live beads only, every step-th) for fitting the last cap's plane (framing)
    rimPts(step) { if (popTick < 0 || tick < popTick) return []; const P = new Float64Array(6), out = [];
      for (let k = 0; k < M; k += step || 8) { if (reff(ra, k) > PI - 0.05) continue; rimPos((ra[k] + rb[k]) / (2 * SR), k, P); out.push([+P[0].toFixed(5), +P[1].toFixed(5), +P[2].toFixed(5)]); } return out; },
    // v5.5, read-only: births per kind at this tick, and the meeting state (bead pairs whose gap along their great circle
    // is under 0.2, 0.1 and 0.04 rad; the smallest gap), for tools that study the finale
    diag() { const b = [0, 0, 0, 0, 0, 0]; for (let i = nd - 1; i >= 0 && DI[REC * i + 6] === tick; i--) b[DI[REC * i + 7] >>> 16]++;
      let g20 = 0, g10 = 0, g04 = 0, gmin = 9; for (let k = 0; k < HALF; k++) { const g = 2 * PI - (rb[k] + rb[k ^ HALF]) / SR; if (g <= 0.2) g20++; if (g <= 0.1) g10++; if (g <= 0.04) g04++; if (g < gmin) gmin = g; }
      let pool = 0; for (let j = 0; j < NPOOL; j++) pool += POOL[j] > 0 ? 1 : 0;
      return `t ${tick} births ${b.join(',')} gap<.2 ${g20} <.1 ${g10} <.04 ${g04} min ${gmin.toFixed(3)} pools ${pool}`; },
    // v5.7, read-only: the large drops (birth tick, volume in units, pool), for tools that study the finale
    big() { const out = []; for (let i = 0; i < nd; i++) { const o = REC * i; if ((DI[o + 7] >>> 16) === 3) out.push([DI[o + 6], +(DI[o + 10] / VSC).toFixed(2), DI[o + 7] & 0xFFFF]); } return out; },
    scan(T1) { return send('scan', T1); },
    bench() { return send('bench'); },
    debug() { const A = readTracers(ia), B = readTracers(ib); const ds = []; for (let v = 0; v < NVERT; v++) { const dx = B[4*v]-A[4*v], dy = B[4*v+1]-A[4*v+1], dz = B[4*v+2]-A[4*v+2]; ds.push(Math.hypot(dx,dy,dz)/SV); }
      ds.sort((a,b)=>a-b); const vd = []; for (let i = 0; i < NV; i++) vd.push(Math.hypot(vb[3*i]-va[3*i], vb[3*i+1]-va[3*i+1], vb[3*i+2]-va[3*i+2])/SV); vd.sort((a,b)=>a-b);
      const q = (a, f) => a[Math.min(a.length-1, Math.floor(f*a.length))].toExponential(2);
      return `${tick}: ${q(ds,.99)} ${q(ds,.999)} ${q(ds,1)} V ${q(vd,1)}`; },
    light(m) { if (m !== undefined) forceRender = true; return m === undefined ? LIGHT.mode : setLight(m); },
    setDir: d => send('setDir', d), run: on => send('run', on), render: () => { render(); updateHud(); }
  };
  requestAnimationFrame(frame);
})();
