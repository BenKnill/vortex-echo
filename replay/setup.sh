#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
    echo "Usage: bash replay/setup.sh NEW_BUILD_DIRECTORY" >&2
    exit 2
fi
if [[ $(ocamlc -version) != 5.4.0 ]] ||
   [[ $(camlp5 -v 2>&1) != *"version 8.04.00 (ocaml 5.4.0)"* ]]; then
    echo "Activate OCaml 5.4.0 and Camlp5 8.04.00 first." >&2
    exit 2
fi

started=$(date +%s)
mkdir -- "$1"
cd -- "$1"

checkout() {
    local name=$1 remote=$2 revision=$3
    git init -q "$name"
    git -C "$name" remote add origin "$remote"
    GIT_TERMINAL_PROMPT=0 git -C "$name" -c credential.helper= fetch --depth=1 origin "$revision"
    git -C "$name" checkout -q --detach FETCH_HEAD
    [[ $(git -C "$name" rev-parse HEAD) == "$revision" ]]
    printf '%s %s\n' "$name" "$revision"
}

checkout hol-light https://github.com/jrh13/hol-light.git 2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32
checkout s2n-bignum https://github.com/BenKnill/s2n-bignum.git 51d1db8f05df6855b54b08debff0e4a863708b81
cd hol-light
HOLLIGHT_USE_MODULE=1 make hol.sh hol_lib.cmo
test -s hol_lib.cmo
sha256sum ocaml-hol ./*.cmi ./*.cmo > replay-build.sha256
printf 'Setup wall time: %s s\n' "$(( $(date +%s) - started ))"
