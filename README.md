# Vortex Echo: a soap bubble that runs backwards, with proofs

**[Watch it run](demo/)** (needs a browser with WebGL2) · [The result](#the-result-in-plain-words) ·
[Results table](#results) · [What is assumed](#what-is-assumed-or-left-out) · [Check it yourself](#check-it-yourself) ·
[Status](#status)

Vortex Echo is a small simulation of a soap bubble. Point vortices swirl over its film. Then the bubble is
punctured: a rim opens around the hole, the film ripples and wobbles, and droplets fly off. Then the whole film plays
**backwards**, and the bubble ends up exactly where it began: every byte of the simulation's state (the "snapshot"
defined below) comes back, under the conditions stated below. Two working areas of memory, a small stack area and a
scratch area, are not part of that state and do change.

All of the simulation's state lives in one WebAssembly module, [`vortex_a1.wasm`](module/vortex_a1.wasm) (30,548 bytes, no imports;
SHA-256 `a3cf8c821534dd1613e2c6c6251a003320c40d5eb2dfc8e16a871c59636aede6`). The page calls its exports
(`init`, `tick_forward`, `tick_backward`, `puncture`) and only reads its memory to draw. The film colours come from
tracers on the GPU, and they are drawing only: nothing here is proved about them.

The module was designed to be reversible. The vortices and the rim and ring arrays move by exactly invertible pairs
of 32-bit integer updates (for example a "Fredkin leapfrog": `(a, b) <- (b, a + f(b))` forward,
`(a, b) <- (b - f(a), a)` back, which inverts whatever `f` computes). Each droplet is logged with the tick it was born
on, so a backward tick can take back exactly the droplets that tick made. The puncture is different: it builds a speed
table in floating point, and stepping back over the puncture tick clears that table and the other puncture data
again. The proofs check that the shipped bytes really behave this way.

## The demo

[`demo/`](demo/) is the page, served as static files. On load it checks that the module's SHA-256 is the one above.
The default film swirls for 120 ticks, punctures the bubble by itself (the "auto" puncture), lets the pop run to
tick 640, and then you can reverse it. You can also click the bubble to puncture it yourself (the "click" film).
The **verify reversal** button runs forward from the current tick (up to 1,200 ticks, toward the end of the pop),
back again, and then compares the page's whole state (module memory and tracers) with where it started. That check
is a test in your browser, not a proof.

## The result in plain words

The proofs are in [HOL Light](https://github.com/jrh13/hol-light), a proof assistant with a small trusted
kernel. They use a HOL Light model of WebAssembly from the hol-hearth project, and they are about the exact bytes of
`vortex_a1.wasm`, not about the C source it was compiled from.

Call the module's simulation state the **snapshot**: the 487,424 32-bit words at bytes [16384, 1966080) of its
4 MiB memory (clock, puncture data, vortices, rim and ring arrays, droplet log and speed table). The end result has
two parts.

**1. One tick ([C8e](#results)).** For every snapshot in a stated domain (1 to 640 vortices, no clock wraparound, the clock not
before the puncture tick, a well-formed droplet log, a clean puncture state), one call of `tick_forward` leaves a snapshot that is a fixed
function of the old snapshot alone, named `va1_fwd` in the proofs. Nothing else in memory influences it.
This holds for plain swirl ticks, pop ticks (with the droplets that are born given by an explicit formula) and the
tick on which the automatic puncture happens. At the end of the pop, `tick_forward` returns 0 and changes nothing.
`tick_backward` is the inverse. On every snapshot that `tick_forward` can produce, one call of `tick_backward` leaves
`va1_bwd` of it, and `va1_bwd` undoes `va1_fwd` word for word (everywhere except the end state), and off the end
state `va1_fwd` is one-to-one.

**2. The films ([C8f](#results)).** The three ways the page plays the bubble are proved as whole call sequences,
with every intermediate snapshot named as some number of `va1_fwd` steps from the start:

- **pop window**: after a puncture, any sequence of forward and backward calls that stays in the pop's range ends in
  the snapshot fixed by the final clock, wherever the path went in between. So k forward calls followed by k
  backward calls restore the whole snapshot: the droplets that were born, the rings, and the vortex slots the
  model does not use.
- **auto film** (the page's default): from tick 0, K + n forward calls (the K-th does the automatic puncture), then
  n + K backward calls, bring every byte of the 4 MiB memory back to its start value, except a 96-byte stack area
  [16288, 16384) and a scratch area [1966080, 2039808) that the theorem leaves free. The same holds for the film run
  to the end of the pop and all the way back.
- **click film**: the same with the host calling `puncture` itself after K forward calls. The pair
  "`tick_forward`, then `puncture`" is undone by a single `tick_backward`.

Earlier steps of the chain ([C1 to C8p](#all-results)) prove the pieces these rest on: each tick, the puncture
routine, the droplet births and the speed table.

## Results

From single ticks to films to the end result. Each row links to its frozen spec, the theorems it claims, the
receipt of its official proving run, and the cold replay. The full wording of each result, with every premise and
what it does not cover, is its class sentence (the **class** link).

| step | what is proved | spec | theorems | receipt | cold replay | wording |
|---|---|---|---|---|---|---|
| tick (C1) | Swirl ticks: n forward calls then n backward calls restore the state (before any puncture) | [`chain_c1_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c1_final.spec) | [`VA1_NP_FILM_INVERSE`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c1_final.spec)<br>[`VA1_NP_SCRUB`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c1_final.spec) | [chain_c1_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c1_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c1_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C1.txt) |
| tick (C8a-tick) | A pop tick, with the droplets it gives birth to named by an explicit formula | [`c8a_r4n.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8a_r4n.spec) | [`VA1_TICK_FORWARD_POP_R5C_NU`](proof-tree/tasks/bubble-echo/vortex/proofs/c8a_r4n.spec) | [c8a_r4n](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_r4n.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_r4n.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8a-tick.txt) |
| tick (C8p-P67) | The puncture, automatic or clicked, with its speed table and header named | [`c8p_nu.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_nu.spec) | [`VA1_TICK_FORWARD_PUNCT_NU`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_nu.spec)<br>[`VA1_HCALL_PUNCTURE_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_nu.spec) | [c8p_nu_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_nu_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_nu_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8p-P67.txt) |
| film (C8f-pop) | Pop window: the state depends only on the clock; k forward then k back restores the snapshot | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [`VA1_POP_SCRUB_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec)<br>[`VA1_POP_CHAIN_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| film (C8f-auto) | Auto film (the page default): forward and back restores every byte but two named areas | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [`VA1_FILM_AUTO_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec)<br>[`VA1_FILM_AUTO_TO_END_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| film (C8f-click) | Click film: the same with the host calling puncture | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [`VA1_FILM_CLICK_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec)<br>[`VA1_FILM_CLICK_TO_END_N`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| endpoint (C8e) | On the stated domain, tick_forward is a function of the snapshot and tick_backward is its inverse | [`c8e_defs.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e_defs.spec)<br>[`c8e.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec) | [`VA1_FWD_FUNCTION`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec)<br>[`VA1_BWD_FUNCTION`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec)<br>[`VA1_BWD_FWD`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec)<br>[`VA1_FWD_INJ`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec) | [c8e_defs_probe](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_defs_probe.attest.json)<br>[c8e_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_final.attest.json) | c8e_defs_probe: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_defs_probe.cold.json)<br>c8e_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8e.txt) |
| endpoint (C8f-pair) | "tick_forward, then puncture" is undone by one tick_backward | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [`VA1_CLICK_PAIR_INV`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |

The words "spec", "receipt", "check-rung" and "cold replay" mean:

- **spec**: a file that fixes each theorem's exact statement and the definitions it uses. Each spec was reviewed
  and frozen before the proof was run, with its hash recorded ([freeze records](https://github.com/BenKnill/vortex-echo/tree/main/proof-tree/tasks/bubble-echo/vortex/chain-nov/frozen)).
- **receipt**: Hearth's record of the official proving run. It shows every theorem matched the frozen spec and 0 new
  axioms were added. What is published here is the `hearth attest` summary of each receipt (`.attest.json`) and its
  `inspect` listing.
- **check-rung**: an independent check of the receipt, the spec lock, the freeze record and planted mutants
  (C3a onward; C1 and C2 came before the tool).
- **cold replay**: Hearth's cold check, which re-runs the receipt's proofs in a fresh context against the frozen
  spec.

### All results

| row | kind | label | spec | receipts | check-rung | cold replay | wording |
|---|---|---|---|---|---|---|---|
| C1 | film | no-pop round trip: n forward then n backward tick calls restore the state (frame stated) | [`chain_c1_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c1_final.spec) | [chain_c1_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c1_final.attest.json) | - | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c1_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C1.txt) |
| C2 | film | v1 pop window: forward/backward tick calls through a pop restore the state | [`chain_c2_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c2_final.spec) | [chain_c2_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c2_final.attest.json) | - | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c2_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C2.txt) |
| C3a | tick | tick_backward at the pop tick (heal check, clear the pop state, undo the swirl tick) | [`chain_c3a_final2.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c3a_final2.spec) | [chain_c3a_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c3a_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c3a_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C3a.txt) |
| C3b | routine | f25 puncture seed, successful branch (no pop pending: word 16396 = -1, direction not all zero): finishes, returns 0, writes only the named regions; the guard branches return 1 (pop pending) and 2 (all-zero direction) | [`chain_c3b_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c3b_final.spec) | [chain_c3b_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c3b_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c3b_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C3b.txt) |
| C4 | film | click and auto-puncture films from tick 0 (puncture result by a TESTED relation) | [`chain_c4_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c4_final.spec) | [chain_c4_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c4_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c4_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C4.txt) |
| C5 | routine | puncture helpers f32/f34/f33 to f25 and the trunc guard (parts 1 and 2) | [`chain_c5_leaves.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5_leaves.spec)<br>[`chain_c5_punct.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5_punct.spec)<br>[`chain_c5_tof25.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5_tof25.spec) | [chain_c5_leaves_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_leaves_final.attest.json)<br>[chain_c5_punct_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_punct_final.attest.json)<br>[chain_c5_tof25_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_tof25_final.attest.json) | PASS | chain_c5_leaves_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_leaves_final.cold.json)<br>chain_c5_punct_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_punct_final.cold.json)<br>chain_c5_tof25_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_tof25_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C5.txt) |
| C5' | model | nested call model wasmn on the chain; wasmc results carried over; puncture call rules | [`chain_c5p.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5p.spec) | [chain_c5p_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5p_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5p_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C5p.txt) |
| C6a | routine | one host call of the export puncture (click) from P = -1, nonzero clock, arguments not all zero: its full result | [`chain_c6a_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c6a_final.spec) | [chain_c6a_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c6a_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c6a_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C6a.txt) |
| C6b | tick | tick_forward on the auto-pop branch (nested model), memory = C6a puncture result | [`chain_c6b_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c6b_final.spec) | [chain_c6b_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c6b_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c6b_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C6b.txt) |
| C7b | film | the page default pop film, auto puncture | [`chain_c7b_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c7b_final.spec) | [chain_c7b_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c7b_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c7b_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C7.txt) |
| C7a | film | the click pop film | [`chain_c7a_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/chain_c7a_final.spec) | [chain_c7a_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c7a_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c7a_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C7.txt) |
| C8b | tick | every tick form also preserves the unused vortex slots (gap G2); film forms not re-run | [`c8b_final.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8b_final.spec) | [c8b_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8b_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8b_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8b.txt) |
| C8a-births | routine | droplet birth f13 appends a named list of records (VA1_BIRTH_EQ; born probe) | [`c8a_born.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8a_born.spec)<br>[`c8a_birth.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8a_birth.spec) | [c8a_born_probe](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_born_probe.attest.json)<br>[c8a_birth_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_birth_final.attest.json) | PASS | c8a_born_probe: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_born_probe.cold.json)<br>c8a_birth_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_birth_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8a-births.txt) |
| C8a-tick | tick | pop-window forward tick with the births named (A8/A9, VA1_TICK_FORWARD_POP_R5C_NU) | [`c8a_r4n.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8a_r4n.spec) | [c8a_r4n](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_r4n.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8a_r4n.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8a-tick.txt) |
| C8p-P12 | routine | f32 and f34 return named terms (sin/cos routine of the puncture) | [`c8p_leaves2.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_leaves2.spec) | [c8p_leaves2_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_leaves2_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_leaves2_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8p-P12.txt) |
| C8p-P34 | routine | f33 reaches its call 25 with the speed table named | [`c8p_f33.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_f33.spec) | [c8p_f33_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_f33_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_f33_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8p-P34.txt) |
| C8p-P5 | routine | f25 also writes the named header words 9..29 | [`c8p_f25h2.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_f25h2.spec) | [c8p_f25h2_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_f25h2_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_f25h2_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8p-P5.txt) |
| C8p-P67 | tick | auto puncture tick and click puncture with the named speed table and header | [`c8p_nu.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8p_nu.spec) | [c8p_nu_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_nu_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8p_nu_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8p-P67.txt) |
| C8e | endpoint | tick_forward is a named function va1_fwd of the snapshot on va1_dom (returns 0 at the end state va1_kind = 3, else 1); tick_backward is va1_bwd on the image; va1_bwd inverts the forward step only off the end state (VA1_BWD_FWD needs ~(va1_kind sg = 3)) (defs probe + E1..E4) | [`c8e_defs.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e_defs.spec)<br>[`c8e.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8e.spec) | [c8e_defs_probe](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_defs_probe.attest.json)<br>[c8e_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_final.attest.json) | PASS | c8e_defs_probe: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_defs_probe.cold.json)<br>c8e_final: [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8e_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8e.txt) |
| C8f-pop | film | C2 pop window again, every snapshot named: the snapshot after any in-range call sequence is ITER e va1_fwd of the start (births, rings and unused vortex words included); k forward then k backward calls restore it; to the end state and back (wasmc) | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| C8f-auto | film | auto pop film (C7b premises, wasmn), every snapshot named ITER (K + n) va1_fwd; the backward run restores every byte below 4194304 except the shadow-stack area [16288, 16384) and the vort scratch [1966080, 2039808): C7b's unused-slot exclusion is gone | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| C8f-click | film | click pop film (C7a premises plus fs 33 = puncture, wasmc): forward snapshots named, the puncture leaves va1_clk a0 a1 a2 of the snapshot, the backward run ends in va1_film_bytes_s of the start | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |
| C8f-pair | endpoint | click pair: "tick_forward; puncture" is undone by ONE tick_backward; pure HOL va1_bwd (va1_clk a0 a1 a2 (va1_fwd sg)) = sg for clean kind-0 sg in va1_dom whose clock does not reach 0xffffffff | [`c8f.spec`](proof-tree/tasks/bubble-echo/vortex/proofs/c8f.spec) | [c8f_final](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.attest.json) | PASS | [reproduced](proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/c8f_final.cold.json) | [class](proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C8f.txt) |

## What is assumed or left out

These limits come from the reviewed class sentences. They are part of the result, not footnotes.

- **The host keeps out.** Every call is modelled with the assumption that nothing else writes the module's
  memory or globals between or during calls, and that memory does not grow. This is an assumption about the host
  running the module, not something proved here.
- **`init` is tested, not proved.** The theorems start from states of a stated shape. That `init(seed, ...)` leaves
  such a state was tested on the real bytes (8 seeds for C1; 24 header checks with 24 planted mutants, plus a matrix
  of films, for C4 and C7), but it is not proved.
- **Floating point stays opaque.** The puncture builds its speed table in 64-bit floating point. The model fixes
  the float rounding operations as functions but does not say what they compute, and every theorem holds for any
  choice of them. So the table appears in the proofs as a named term (`va1_ptbl`) and no float value is claimed.
  Comparisons and trapping conversions are exact on the bits.
- **States outside the domain.** No claim is made for clock wraparound, a clock before the puncture tick, an unclean
  puncture state, an automatic puncture at the last clock value, vortex counts outside 1 to 640, a malformed droplet
  log, refused calls or other exports.
- **Bytes outside the snapshot.** The one-tick result says these do not influence the snapshot, and nothing more. At
  the end of a film, the 96-byte stack area and the scratch area are left free (tests show they do change). The
  pop-window theorems say nothing outside the snapshot.
- **The trusted base.** The HOL Light kernel; hol-hearth's model of WebAssembly, including its rule that a nested
  call runs as one step; and the premises that the call table maps each index to the module's own functions and
  that global 0 starts at 16384. That the model agrees with real WebAssembly engines is not proved.
- **Not about the picture.** Nothing is proved about the browser page, the GPU tracers or the drawing, about what the
  numbers mean physically, or about the later "v5.8" renderer. That the page makes these call sequences was read
  from its code, not proved.

## Check it yourself

**The module.** `shasum -a 256 module/vortex_a1.wasm` should print `a3cf8c82...6aede6`, the hash every theorem names.

**The files are the proved files.** From a checkout of this repository:

```sh
python3 -I tools/check_tree.py
```

For every receipt this checks by SHA-256 that the proof source, the frozen spec, the wasm modules and every project
file the run read (its closure inventory) are the files published here. It needs only Python's standard library and
re-runs no proof. Expected output: `24 receipts, 1607 file checks, 0 problems`.

**Re-running a proof.** This needs a Linux host with [HOL Light](https://github.com/jrh13/hol-light) at `2a1cea8f`
and hol-hearth at the recorded revision (`6adb41ce`; `81c0fa6c` for C1 and C2) with its `wasm` profile.
hol-hearth is not public yet, so for now only its maintainers can do this step. The quickest is part 1 of C5, whose files need no overlay. From `proof-tree/`:

```sh
hearth prove tasks/bubble-echo/vortex/proofs/chain_c5_leaves_final.ml --profile wasm \
  --spec tasks/bubble-echo/vortex/proofs/chain_c5_leaves.spec
```

It should end with `PASSED chain_c5_leaves_final.ml: 14/14 bindings proved, 14/14 spec bindings matched, 24/24 spec
pins matched, 0 new axioms`. For the other results, copy
`tasks/bubble-echo/vortex/chain-nov/overlay/.` over the tree first. For the layered C8 runs, see the
[chain README](proof-tree/tasks/bubble-echo/vortex/chain-nov/README.md). It was written for the project's private
working repository: its step 1 (the claim generator, its tests and `tools/vab`) uses files that are not published
here, so use `tools/check_tree.py` instead. Its step 2 (the `hearth prove` commands and
`recipe/finish-c8-stages.json`) applies to `proof-tree/` as published. Those commands are written from the run
records. They have not been re-run from this repository.

## Status

Checked on 2026-11-17:

- **Proved.** 23 claim rows from 24 official receipts. Every receipt PASSED, every theorem matched its frozen spec,
  and 0 new axioms were added. C3a onward also passed check-rung.
- **Cold-replayed: all 24 receipts.** Each was re-run in a fresh context against its frozen spec and reproduced with
  0 new axioms (the C8f cold replay rebuilt all 24 of its basis layers from the root). The last six (`c8a_born_probe`,
  `c8a_birth_final`, `c8p_leaves2_final`, `c8p_f25h2_final`, `c8p_f33_final` and `c8e_defs_probe`) were cold-checked
  on 2026-11-17, after the snapshot of the project's private ledger this page was built from (VAB `a70e29d0`). That
  ledger still lists those six as not cold-replayed until a follow-up update; `claims.json` here carries the new
  status and a note saying so (`cold_status_note`).
- **Reviews.** GPT-6.1 Sol (an OpenAI model used as an adversarial reviewer) reviewed every spec before it was
  frozen, and each was frozen at a score of 9 or 10 out of 10. It also reviewed the C8f proof and class sentence
  (9, then 10), the import of the chain into the project's claim ledger (7, 8, then 9), and the C8f
  addition to that ledger (9, then 10). The same reviewer checked this page and its list of published files before publication (8, then 9, then 10).
- **Who did the work.** The proofs, specs, class sentences and this page were written by AI agents (the records
  name Anthropic's Claude Opus 5.5) working for Ben Knill, and reviewed as above.

The proofs ran on hol-hearth `6adb41ce` (C1 and C2 on `81c0fa6c`), HOL Light `2a1cea8f`, profile
`hol.s2n.wasm.v1`. Host paths inside the receipt files (`/home/bluestar/...`) record where each run happened. They
are not inputs.

## What is in this repository

| path | what |
|---|---|
| [`demo/`](demo/) | the page: `vortex_a1.wasm` plus the drawing code |
| [`module/`](https://github.com/BenKnill/vortex-echo/tree/main/module) | `vortex_a1.wasm`, its C source (`vortex.c`, `ve_core.c`), [build notes](module/BUILD.md) and `SHA256SUMS` |
| [`claims.json`](claims.json) | the claim table: one row per result, with its receipts, spec, class sentence, cold status and reviews |
| [`proof-tree/`](https://github.com/BenKnill/vortex-echo/tree/main/proof-tree) | the proof sources and specs, at the same paths as in the project's working repository |
| [`…/chain-nov/class/`](https://github.com/BenKnill/vortex-echo/tree/main/proof-tree/tasks/bubble-echo/vortex/chain-nov/class) | the reviewed class sentences |
| [`…/chain-nov/evidence/`](https://github.com/BenKnill/vortex-echo/tree/main/proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence) | receipt attests, inspect listings, cold-replay records, check-rung outputs and closure inventories |
| [`tools/check_tree.py`](tools/check_tree.py) | the hash check above |
| `MANIFEST.sha256` | the SHA-256 of every other file here |

Licence: see [LICENSE](LICENSE) and [NOTICE](NOTICE).
