# Wasm profile provenance

`recipe.ml` and the files under `wasm/` are byte-for-byte copies from the
hol-hearth revision `6adb41ce24fa3e62faa14013ed79bef5dd87ec26`.
The original paths are `profiles/wasm.ml` and `profiles/roots/wasm/`.
Copyright (c) 2026 Ben Knill. See [the hol-hearth MIT license](LICENSE.hol-hearth).
The replay uses the five files under `wasm/proofs/`. The original recipe and
`wasm/SOURCE.json` document where those files came from. Their digests are in
[SHA256SUMS](SHA256SUMS).

The generic load list in `wasm/proofs/base.ml` follows and adapts
`x86/proofs/base.ml` from s2n-bignum. That upstream file carries the Amazon
copyright and offers Apache-2.0, ISC or MIT-0. For that material, this package
uses the MIT-0 option, as the Vortex Echo root NOTICE does for existing proof
files. See the pinned upstream [license choices](LICENSE.s2n-bignum) and
[notice](NOTICE.s2n-bignum). Setup fetches the s2n-bignum dependency separately.
