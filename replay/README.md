# Re-run C5 part 1 on Linux, without hol-hearth

The claim, end to end:
[its reviewed wording (C5, part 1)](../proof-tree/tasks/bubble-echo/vortex/chain-nov/class/C5.txt) ·
[the frozen spec](../proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5_leaves.spec) ·
[the proof](../proof-tree/tasks/bubble-echo/vortex/proofs/chain_c5_leaves_final.ml) ·
[the receipt of the official run](../proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence/receipts/chain_c5_leaves_final.attest.json) ·
[the module's bytes](../module/vortex_a1.wasm).
This page re-runs that proof on your machine.

The standalone replay checks the C5 leaf theorems for functions 32 and 34 of
the published Wasm module, and the entry point and local declarations of
function 33. It starts a fresh HOL Light process, loads the bundled Wasm
model from source, and runs the proof against the original spec. All needed
sources are in this checkout or fetched by the setup script.

From the root of a checkout containing `replay/`, with Git, GNU Make,
Python 3.9 or newer, and Linux `strace` available, run the commands below.
The build needs OCaml 5.4.0, Camlp5 8.04.00, ocamlfind, Zarith and camlp-streams.
If you already have those tools on your PATH, start with `bash replay/setup.sh`.
Otherwise, in an initialized opam installation with a C toolchain and GMP
development headers, create and activate an OCaml switch.

```sh
opam switch create "$PWD/.replay-ocaml" 5.4.0
opam install --switch "$PWD/.replay-ocaml" camlp5.8.04.00 ocamlfind zarith camlp-streams
eval "$(opam env --switch "$PWD/.replay-ocaml" --set-switch)"
```

Run setup once. It fetches fixed public revisions and compiles HOL Light in
module mode. Choose a build path that does not yet exist and has no spaces.
Use the same toolchain when running the replay.

```sh
bash replay/setup.sh ../vortex-c5-build
python3 -I replay/c5.py ../vortex-c5-build
```

On an Ubuntu 26.04 arm64 guest (OrbStack on a Mac), setup took 16 and 20 seconds in
two runs with the toolchain already installed, and the replay 2 min 14 s and 2 min 59 s.
On an x86-64 Ubuntu machine (WSL2, Ubuntu packages for OCaml 5.4.0 and Camlp5 8.04.00,
and Ubuntu's strace unpacked into a user directory without root), setup took 54 seconds
and the replay 4 min 38 s.
A successful run exits with status 0 and ends with the line below.

```text
PASSED chain_c5_leaves_final.ml: 14/14 bindings proved, 14/14 spec bindings matched, 24/24 spec pins matched, 0 new axioms
```

The checker requires each named theorem to have no hypotheses and to match
its spec statement up to renaming of bound variables and consistent renaming
of type variables. It compares all 24 definition pins with HOL Light's
definition registry. It checks that ETA, choice and infinity are the only
axioms from startup through the end of the proof. The replay loads the
underlying proof sources in place of two wrappers from the original warm
run. It checks the SHA-256 of all eight source and artifact rows it replays,
the spec, the Wasm profile, and `vortex_a1.wasm` in `module/` and in the proof
tree (the copy the proof reads). The demo's own copy, `demo/vortex_a1.wasm`, is
not part of this check (`MANIFEST.sha256` lists its hash). It also audits local
file opens and reports timings and log paths.

The result is about the specified behavior in the bundled Wasm model for
module SHA-256
`a3cf8c821534dd1613e2c6c6251a003320c40d5eb2dfc8e16a871c59636aede6`.
The contracts leave the numerical return value and stored floating-point
values unspecified. Execution of the full puncture, the rendered film and
agreement between the model and browser engines are separate claims.
The replay trusts the stated toolchain and the pinned executable proof
sources. It has checks specific to the C5 spec format and receipt.
