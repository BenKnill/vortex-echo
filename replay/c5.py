#!/usr/bin/env python3
"""Cold replay of the published C5 part 1 proof on Linux."""

import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys
import tempfile
import time


REPLAY = Path(__file__).resolve().parent
SITE = REPLAY.parent
TREE = SITE / "proof-tree"
PROJECT = TREE / "tasks/bubble-echo/vortex"
PROOFS = PROJECT / "proofs"
PROFILE = REPLAY / "profile-wasm"
PROFILE_PROOFS = PROFILE / "wasm/proofs"
LEAF = PROOFS / "chain_c5_leaves_final.ml"
SPEC = PROOFS / "chain_c5_leaves.spec"
RECEIPT = PROJECT / "chain-nov/evidence/receipts/chain_c5_leaves_final.attest.json"
RECEIPT_SHA = "0727219254c248192248ec46d89a91d9168c716b48a98f5e837d7f7b5af62ec7"
SPEC_SHA = "610c0d63e26223ee017f64666986ce813dc917bc69558a2ca9a364534831f39d"
PROFILE_MANIFEST_SHA = "da4ac5e554f1546f082a8615367a1e6621a72627415b585cf56a8c0d135164e0"
WASM_SHA = "a3cf8c821534dd1613e2c6c6251a003320c40d5eb2dfc8e16a871c59636aede6"
HOL_REV = "2a1cea8f1cb7f3885a60d947ba06eabac6ec1d32"
S2N_REV = "51d1db8f05df6855b54b08debff0e4a863708b81"
WRAPPERS = {
    "03a1071c1461252762d722bfa4e9e6085289ec756906a4b28e475bf53cd8f0f1",
    "f9c27d585d1ab59808a2bdee920867fb30a957e049f4db119fb37e6936ce1abb",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked(path, digest):
    data = path.read_bytes()
    observed = sha(data)
    require(observed == digest, f"SHA-256 mismatch for {path}: {observed} != {digest}")
    return data


def manifest(path):
    for line in path.read_text().splitlines():
        digest, relative = line.split("  ", 1)
        yield path.parent / relative, digest


def verify_inputs(report=True):
    receipt = json.loads(checked(RECEIPT, RECEIPT_SHA))
    expected = {}
    wrappers = set()
    for row in receipt["closure"]["files"]:
        original = Path(row["path"])
        if original.name == "dependencies.ml":
            wrappers.add(row["sha256"])
            continue
        if row.get("resolution") == "mounted_source":
            require(row["declared_path"] == "wasm/proofs/wasm_tactics.ml",
                    "unexpected mounted receipt input")
            path = PROFILE / row["declared_path"]
        else:
            path = TREE / original.relative_to(receipt["closure"]["root"])
        expected[path] = row["sha256"]
    require(wrappers == WRAPPERS and len(expected) == 8, "unexpected receipt closure")
    for path, digest in expected.items():
        data = checked(path, digest)
        if path.suffix == ".ml":
            require(not re.search(rb"\b(new_axiom|mk_thm|CHEAT_TAC)\b", data),
                    f"axiom or cheat identifier in {path}")
    checked(SITE / "module/vortex_a1.wasm", WASM_SHA)
    checked(SPEC, SPEC_SHA)
    checked(PROFILE / "SHA256SUMS", PROFILE_MANIFEST_SHA)
    profile_sources = dict(manifest(PROFILE / "SHA256SUMS"))
    require(profile_sources[PROFILE / "recipe.ml"] == receipt["profile"]["recipe"]["sha256"],
            "recipe hash differs from the receipt")
    for path, digest in profile_sources.items():
        checked(path, digest)
    if report:
        print("SHA-256 matched: 8 receipt inputs, published module, frozen spec and pinned profile",
              flush=True)
        print("Two warm checkpoint wrappers are replaced by direct source loads.", flush=True)
    return set(expected) | {path for path in profile_sources if path.parent == PROFILE_PROOFS}


def parse_spec(text):
    entries = {"theorem": {}, "definition": {}}
    while text.strip():
        text = text.lstrip()
        if text.startswith("(*"):
            depth = 0
            for delimiter in re.finditer(r"\(\*|\*\)", text):
                depth += 1 if delimiter[0] == "(*" else -1
                if depth == 0:
                    text = text[delimiter.end():]
                    break
            else:
                raise ValueError("unterminated spec comment")
            continue
        entry = re.match(r"(theorem|definition)\s+(\w+)\s+`([^`]+)`\s*;;", text, re.ASCII)
        require(entry is not None, f"unexpected C5 spec syntax near {text[:80]!r}")
        kind, name, statement = entry.groups()
        name_pattern = r"[A-Z][A-Z0-9_]*" if kind == "theorem" else r"[a-z][a-zA-Z0-9_]*"
        require(re.fullmatch(name_pattern, name), f"invalid spec name: {name}")
        require(name not in entries[kind], f"duplicate spec name: {name}")
        entries[kind][name] = statement
        text = text[entry.end():]
    require(len(entries["theorem"]) == 14 and len(entries["definition"]) == 24,
            "C5 spec requires 14 theorem bindings and 24 definition pins")
    return entries


def ocaml(text):
    return json.dumps(os.fspath(text), ensure_ascii=False)


def driver(entries, nonce):
    script = [
        'use_file_raise_failure := true;;',
        f'loadt {ocaml(REPLAY / "check.ml")};;',
        'print_endline "\\nSTAGE bare HOL Light";;',
        f'load_path := [{ocaml(PROFILE_PROOFS)}; "."; "$"];;',
        f'needs {ocaml(PROFILE_PROOFS / "base.ml")};;',
        'replay_check_axioms "profile";;',
        'let replay_profile_foundation = replay_foundation ();;',
        'print_endline "\\nSTAGE Wasm profile";;',
        f'Sys.chdir {ocaml(PROOFS)};;',
        f'load_path := ["."; "$"; {ocaml(PROFILE)}];;',
        'needs "chain_c5_dec.ml";;',
        'replay_check_axioms "basis 1";;',
        'replay_check_delta "basis 1" replay_profile_foundation [0; 11; 11; 0];;',
        'let replay_basis1_foundation = replay_foundation ();;',
        'needs "chain_c5_tacs.ml";;',
        'needs "chain_c5_leaves.ml";;',
        'replay_check_axioms "basis 2";;',
        'replay_check_delta "basis 2" replay_basis1_foundation [0; 1; 1; 0];;',
        'let replay_basis_foundation = replay_foundation ();;',
        'let replay_parser_before = replay_parser_context ();;',
        'print_endline "\\nSTAGE C5 dependencies";;',
        f'loadt {ocaml(LEAF)};;',
        'replay_check_axioms "leaf";;',
        'replay_check_delta "leaf" replay_basis_foundation [0; 0; 0; 0];;',
        'if replay_parser_context () <> replay_parser_before then failwith "parser context changed";;',
        'print_endline "\\nSTAGE C5 leaf";;',
    ]
    script.extend(f'replay_check_binding "{name}" {name} {ocaml(term)};;'
                  for name, term in entries["theorem"].items())
    script.extend(f'replay_check_pin "{name}" {ocaml(term)};;'
                  for name, term in entries["definition"].items())
    script += [f'print_endline "\\nCOMPLETE {nonce}";;', 'exit 0;;']
    return "\n".join(script) + "\n"


def git(root, *args):
    return subprocess.check_output(["git", "-C", root, *args])


def verify_opens(trace, expected, hol, s2n):
    # strace -yy decodes the returned descriptor, so paths with ../ are resolved.
    opened = set()
    with trace.open() as log:
        for line in log:
            match = re.search(r"= \d+<(/[^>]+)>\s*$", line)
            if match and "O_DIRECTORY" not in line:
                opened.add(Path(match[1]))
    actual = {path for path in opened
              if path.is_relative_to(TREE) or path.is_relative_to(PROFILE)}
    require(actual == expected, f"source opens differ, missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}")
    print(f"Observed {len(actual)} expected project/profile files opened by HOL.", flush=True)
    digests = [(path, sha(path.read_bytes())) for path in sorted(actual)]
    for root, rev in ((hol, HOL_REV), (s2n, S2N_REV)):
        generated = dict(manifest(root / "replay-build.sha256")) if root == hol else {}
        for path in sorted(p for p in opened if p.is_relative_to(root)):
            digest = generated.get(path)
            if digest is None:
                relative = path.relative_to(root).as_posix()
                digest = sha(git(root, "show", f"{rev}:{relative}"))
            checked(path, digest)
            digests.append((path, digest))
        print(f"SHA-256 matched for opened {root.name} files.", flush=True)
    trace.with_name("opens.sha256").write_text(
        "".join(f"{digest}  {path}\n" for path, digest in digests))


def run_hol(build, entries, run_dir):
    hol = build / "hol-light"
    s2n = build / "s2n-bignum"
    for root, rev in ((hol, HOL_REV), (s2n, S2N_REV)):
        require(git(root, "rev-parse", "HEAD").decode().strip() == rev,
                f"{root.name} is not at {rev}")
    # Verify the pinned inputs before executing, and audit actual opens afterward.
    for path, digest in manifest(hol / "replay-build.sha256"):
        checked(path, digest)
    for root in (hol, s2n):
        subprocess.run(["git", "-C", root, "diff", "HEAD", "--exit-code", "--"],
                       check=True, stdout=subprocess.DEVNULL)
    nonce = secrets.token_hex(16)
    entry = run_dir / "driver.ml"
    entry.write_text(driver(entries, nonce))
    env = os.environ.copy()
    env.update(HOLLIGHT_DIR=str(hol), HOLLIGHT_USE_MODULE="1", HOLLIGHT_LOAD_PATH="")
    trace = run_dir / "opens.log"
    command = ["strace", "-f", "-yy", "-s", "4096", "-e", "trace=open,openat,openat2",
               "-o", trace, hol / "ocaml-hol", "-init", hol / "hol.ml", "-I", hol, "-noprompt"]
    started = time.monotonic()
    completion = []
    errors = []
    counts = {"BINDING": [], "PIN": []}
    with (run_dir / "hol.log").open("w") as log:
        proc = subprocess.Popen(command, cwd=s2n, env=env, stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, errors="replace")
        proc.stdin.write(f"#use {ocaml(entry)};;\n")
        proc.stdin.close()
        for line in proc.stdout:
            log.write(line)
            tag, _, payload = line.strip().partition(" ")
            if tag == "STAGE":
                print(f"{time.monotonic() - started:7.2f} s  {payload}", flush=True)
            elif tag in counts:
                counts[tag].append(payload)
            elif tag == "FOUNDATION":
                print(line.strip(), flush=True)
            elif tag == "COMPLETE":
                completion.append(payload)
            elif re.search(r"^(Error:|Exception:|Error in included file)", line):
                errors.append(line.strip())
        status = proc.wait()
    elapsed = time.monotonic() - started
    require(status == 0 and completion == [nonce] and not errors,
            f"HOL failed (exit {status}): {' | '.join(errors[-5:]) or 'completion marker missing'}")
    for tag, key in (("BINDING", "theorem"), ("PIN", "definition")):
        require(counts[tag] == list(entries[key]), f"missing or out-of-order {tag} records")
    return elapsed, trace


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 -I replay/c5.py BUILD_DIRECTORY", file=sys.stderr)
        return 2
    started = time.monotonic()
    build = Path(sys.argv[1]).resolve()
    try:
        expected = verify_inputs()
        entries = parse_spec(SPEC.read_text())
        run_dir = Path(tempfile.mkdtemp(prefix="c5-run-", dir=build))
        print(f"Run logs: {run_dir}", flush=True)
        elapsed, trace = run_hol(build, entries, run_dir)
        verify_opens(trace, expected, build / "hol-light", build / "s2n-bignum")
        verify_inputs(report=False)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"FAILED {LEAF.name}: {error}", file=sys.stderr)
        return 1
    print(f"Cold HOL process: {elapsed:.2f} s, full replay: {time.monotonic() - started:.2f} s")
    print("PASSED chain_c5_leaves_final.ml: 14/14 bindings proved, "
          "14/14 spec bindings matched, 24/24 spec pins matched, 0 new axioms")
    return 0


if __name__ == "__main__":
    sys.exit(main())
