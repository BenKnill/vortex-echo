# How vortex_a1.wasm was built

This is the build record, not a tested recipe for your machine. The module was not rebuilt for this page; the
theorems are about the bytes in this folder (SHA-256 `a3cf8c821534dd1613e2c6c6251a003320c40d5eb2dfc8e16a871c59636aede6`),
whatever produced them.

- `src/ve_core.c` is the integer engine. It is the source of an earlier proved module, `ve_core.wasm`
  (SHA-256 `72fe0ba2...`, in `proof-tree/tasks/bubble-echo/vortex/core/`), and the same toolchain first rebuilt that
  module byte for byte.
- `src/vortex.c` is the rest of the module: the seeded scene, the speed table built at the puncture, and the tick
  sequencer that the browser host used to run. It `#include`s `ve_leaves.c`, which is `ve_core.c` with one line changed so that its
  functions are emitted as separate, non-inlined functions. Run from `module/`:

```sh
sed -e 's|^#define EXPORT(name) __attribute__((export_name(name)))|#define EXPORT(name) __attribute__((export_name(name), noinline))|' \
  src/ve_core.c > src/ve_leaves.c
python -m ziglang cc --target=wasm32-freestanding -mcpu=mvp -O2 -g0 -std=c11 -fwrapv -ffp-contract=off \
  -Wall -Wextra -Werror -Wno-unused-function -nostdlib -fno-builtin \
  -Wl,--no-entry -Wl,--strip-all -Wl,-z,stack-size=16384 -Wl,--global-base=4063232 \
  -Wl,--initial-memory=4194304 -Wl,--max-memory=4194304 \
  -o tmp_a1.wasm src/vortex.c
python3 src/drop_exports.py tmp_a1.wasm vortex_a1.wasm ve_
```

The compiler was zig 0.17.0 (`ziglang` from PyPI), run on x86-64 Linux. `drop_exports.py` rewrites only the export
section, removing the 29 internal `ve_*` exports; every other section, including the code, is copied byte for byte.
The 29 function bodies were compared with those of `ve_core.wasm` and are byte-identical.
