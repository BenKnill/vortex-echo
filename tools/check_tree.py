#!/usr/bin/env python3
"""check_tree.py: check that the files in this repository are the files the receipts name.

Standard library only; run from the repository root:  python3 -I tools/check_tree.py

For every receipt of every claim row in claims.json it checks, by SHA-256:
  - the proof source and the frozen spec the receipt names;
  - the wasm modules in its closure (vortex_a1.wasm, and ve_core.wasm where read);
  - every project file in its closure inventory (proof-tree/.../chain-nov/evidence/closures/<case>.closure.json),
    found at its own path under proof-tree/ or, for the seven retargeted October files, under the overlay;
and that each closure inventory is bound to its receipt: its digest (SHA-256 of its sorted compact JSON without the
strict_sha256 key) recomputes to the closure sha256 in the receipt's attest and in the claim row, and its files are
exactly the attest's closure files. Removing an entry from an inventory therefore fails the check.
It re-runs no proof. It shows that what is published here is byte-for-byte what was proved.
"""
import hashlib, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREE = os.path.join(ROOT, 'proof-tree')
OVERLAY = os.path.join(TREE, 'tasks/bubble-echo/vortex/chain-nov/overlay')
EVID = os.path.join(TREE, 'tasks/bubble-echo/vortex/chain-nov/evidence')


def sha(path):
    try:
        with open(path, 'rb') as f:
            return hashlib.sha256(f.read()).hexdigest()
    except FileNotFoundError:
        return None


def main():
    claims = json.load(open(os.path.join(ROOT, 'claims.json')))['chain_nov']['claims']
    seen, bad, nfiles = set(), [], 0
    for row in claims:
        for rc in row['receipts']:
            case = rc['case']
            if case in seen:
                continue
            seen.add(case)
            checks = [(rc['source_file'], rc['source_sha256']), (rc['spec_file'], rc['spec_sha256'])]
            checks += [(w['file'], w['sha256']) for w in rc.get('wasm_files_in_closure', [])]
            for rel, want in checks:
                nfiles += 1
                if want not in (sha(os.path.join(TREE, rel)), sha(os.path.join(OVERLAY, rel))):
                    bad.append(f'{case}: {rel} sha256 differs from the receipt')
            clo = json.load(open(os.path.join(EVID, 'closures', case + '.closure.json')))
            att = json.load(open(os.path.join(EVID, 'receipts', case + '.attest.json'))).get('closure') or {}
            body = {k: v for k, v in clo.items() if k != 'strict_sha256'}
            dig = hashlib.sha256(json.dumps(body, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
            if not (dig == clo.get('strict_sha256') == att.get('sha256') == rc.get('closure_sha256')):
                bad.append(f'{case}: closure inventory digest does not recompute to the attest and claim-row closure sha256')
            want = [(r.get('resolved_path'), r.get('sha256')) for r in clo['records'] + clo['artifacts']]
            want.append((clo['entrypoint'].get('path'), clo['entrypoint'].get('sha256')))
            got = [(f.get('path'), f.get('sha256')) for f in att.get('files') or []]
            if sorted(want) != sorted(got) or len(set(got)) != len(got):
                bad.append(f'{case}: closure inventory files differ from the attest closure files')
            root = os.path.normpath(clo['project_root']) + '/'
            for rec in clo['records'] + clo['artifacts'] + [clo['entrypoint']]:
                p = os.path.normpath(rec.get('resolved_path') or rec.get('opened_path') or rec.get('path'))
                if not p.startswith(root):
                    continue  # profile, HOL Light or basis-layer files: not part of this repository
                rel = p[len(root):]
                nfiles += 1
                if rec['sha256'] not in (sha(os.path.join(TREE, rel)), sha(os.path.join(OVERLAY, rel))):
                    bad.append(f'{case}: closure file {rel} missing or different')
    print(f'{len(seen)} receipts, {nfiles} file checks, {len(bad)} problems')
    for b in bad:
        print('  ' + b)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
