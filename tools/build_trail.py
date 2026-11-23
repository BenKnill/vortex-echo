#!/usr/bin/env python3
"""build_trail.py: generate the proof-trail pages under trail/ from the published files.

Standard library only; run from the repository root:

    python3 -I tools/build_trail.py           # (re)write trail/
    python3 -I tools/build_trail.py --check   # regenerate in memory and compare with trail/ on disk

For each claim row of claims.json it writes trail/<row>.html, which follows the row from the sentence on the main
page to, for every theorem of every receipt of the row:
  1. the theorem's exact statement, quoted verbatim from the frozen spec the receipt names (with its line numbers);
  2. the line of the proof file where the receipt says the theorem is bound (trail/src/<file>.html#L<n>);
  3. the receipt's entry for it (binding status, spec match), the receipt's PASSED line and the cold replay;
  4. the functions of the wasm module its statement names (directly, or through definitions in its spec), each with
     its byte range in the module file and a hex view (trail/bytes/<module>.html).
Nothing in trail/ is written by hand: statements, line numbers, byte ranges and hex are all read from the published
files here. tools/check_trail.py checks the result independently.
"""
import hashlib, html, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TREE = 'proof-tree'
BUBBLE = 'proof-tree/tasks/bubble-echo'
OVERLAY = 'proof-tree/tasks/bubble-echo/vortex/chain-nov/overlay'
EVID = 'proof-tree/tasks/bubble-echo/vortex/chain-nov/evidence'
OUT = 'trail'
GH = 'https://github.com/BenKnill/vortex-echo/blob/main/'
MODULES = [  # (key, path in this repository, path as the receipts name it)
    ('vortex_a1', 'module/vortex_a1.wasm', 'tasks/bubble-echo/vortex/purist/vortex_a1.wasm'),
    ('ve_core', 'proof-tree/tasks/bubble-echo/vortex/core/ve_core.wasm', 'tasks/bubble-echo/vortex/core/ve_core.wasm'),
]
REPLAY_CASE = 'chain_c5_leaves_final'
SECTION_NAMES = {0: 'custom', 1: 'type', 2: 'import', 3: 'function', 4: 'table', 5: 'memory', 6: 'global',
                 7: 'export', 8: 'start', 9: 'element', 10: 'code', 11: 'data', 12: 'data count'}


class TrailError(Exception):
    pass


def rd(rel, mode='r'):
    with open(os.path.join(ROOT, rel), mode) as f:
        return f.read()


def sha(data):
    return hashlib.sha256(data if isinstance(data, bytes) else data.encode()).hexdigest()


def esc(s):
    return html.escape(str(s), quote=True)


def slug(claim):
    return claim.replace("'", 'p')


# ---------------------------------------------------------------- wasm

def leb(b, i):
    r = s = 0
    while True:
        x = b[i]
        i += 1
        r |= (x & 0x7f) << s
        s += 7
        if x < 0x80:
            return r, i


def wname(b, i):
    n, i = leb(b, i)
    return b[i:i + n].decode('utf-8'), i + n


def limits(b, i):
    flag = b[i]
    _, i = leb(b, i + 1)
    if flag & 1:
        _, i = leb(b, i)
    return i


def parse_wasm(b):
    """Sections, exported function names and the code-section entries (function index, entry start, body start, end)."""
    if b[:8] != b'\0asm\x01\0\0\0':
        raise TrailError('not a wasm 1.0 module')
    i, secs, nimp, exports, funcs = 8, [], 0, {}, []
    while i < len(b):
        sid = b[i]
        size, j = leb(b, i + 1)
        end = j + size
        secs.append((sid, i, j, end))
        if sid == 2:
            n, k = leb(b, j)
            for _ in range(n):
                _, k = wname(b, k)
                _, k = wname(b, k)
                kind = b[k]
                k += 1
                if kind == 0:
                    _, k = leb(b, k)
                    nimp += 1
                elif kind == 1:
                    k = limits(b, k + 1)
                elif kind == 2:
                    k = limits(b, k)
                else:
                    k += 2
        elif sid == 7:
            n, k = leb(b, j)
            for _ in range(n):
                nm, k = wname(b, k)
                kind = b[k]
                idx, k = leb(b, k + 1)
                if kind == 0:
                    exports.setdefault(idx, []).append(nm)
        elif sid == 10:
            n, k = leb(b, j)
            for idx in range(n):
                sz, k2 = leb(b, k)
                funcs.append((nimp + idx, k, k2, k2 + sz))
                k = k2 + sz
            if k != end:
                raise TrailError('code section does not parse to its end')
        i = end
    return {'sections': secs, 'imports': nimp, 'exports': exports, 'funcs': funcs}


# ---------------------------------------------------------------- spec files

def parse_spec(text):
    """{name: (kind, first line, last line)} for every `theorem NAME` / `definition NAME` block (1-based, inclusive)."""
    lines, items, i = text.split('\n'), {}, 0
    while i < len(lines):
        m = re.match(r'(theorem|definition) (\S+)\s*$', lines[i])
        if m:
            j = i
            while not lines[j].rstrip().endswith('`;;'):
                j += 1
            items[m.group(2)] = (m.group(1), i + 1, j + 1)
            i = j + 1
        else:
            i += 1
    return items


def block(lines, a, b):
    return '\n'.join(lines[a - 1:b])


def code_bytes(text):
    """The byte list of a code definition `name:byte list = [word 0x..; ...]`, or None if it is not one."""
    m = re.search(r'`\s*\w+\s*:\s*byte list\s*=\s*\[(.*)\]\s*`;;\s*$', text, re.S)
    if not m:
        return None
    out = []
    for el in m.group(1).split(';'):
        w = re.fullmatch(r'\s*word\s+(0x[0-9a-fA-F]+|\d+)\s*', el)
        if not w:
            return None
        out.append(int(w.group(1), 0))
    return bytes(out)


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


# ---------------------------------------------------------------- index.html sentences

def strip_tags(s):
    return re.sub(r'\s+', ' ', html.unescape(re.sub(r'<[^>]+>', '', s))).strip()


def page_sentences(index_html):
    """The results table of index.html (headline rows and chain rows): claim -> (row heading, sentence)."""
    out = {}
    for tbl in re.findall(r'<table>(.*?)</table>', index_html, re.S):
        rows = re.findall(r'<tr[^>]*>(.*?)</tr>', tbl, re.S)
        hdr = [strip_tags(c) for c in re.findall(r'<th>(.*?)</th>', rows[0], re.S)]
        if hdr[:2] != ['result', 'what is proved']:
            continue
        for r in rows[1:]:
            cells = [strip_tags(c) for c in re.findall(r'<td>(.*?)</td>', r, re.S)]
            m = re.fullmatch(r'([\w ]+): (\S+)', cells[0])
            out[m.group(2)] = (cells[0], cells[1])
    return out


# ---------------------------------------------------------------- model

def resolve(rel, want):
    """The published path (repository-relative) of a proof-tree file with the given sha256: its own path or the overlay."""
    for p in (os.path.join(TREE, rel), os.path.join(OVERLAY, rel)):
        if os.path.exists(os.path.join(ROOT, p)) and sha(rd(p, 'rb')) == want:
            return p
    raise TrailError(f'{rel}: no published copy with sha256 {want}')


def load():
    claims_doc = json.loads(rd('claims.json'))
    chain = claims_doc['chain_nov']
    mods = {}
    for key, path, recname in MODULES:
        b = rd(path, 'rb')
        mods[key] = {'key': key, 'path': path, 'recname': recname, 'bytes': b, 'sha': sha(b), 'wasm': parse_wasm(b)}
    if mods['vortex_a1']['sha'] != chain['module_sha256']:
        raise TrailError('module/vortex_a1.wasm sha256 differs from claims.json')
    body_index = {}
    for m in mods.values():
        for idx, e0, b0, b1 in m['wasm']['funcs']:
            body_index.setdefault(m['bytes'][b0:b1], []).append((m['key'], idx))

    specs, sources, receipts, rows = {}, {}, {}, []
    code_defs = {}   # (spec path, def name) -> {'bytes', 'line', 'matches': [(module, func index)]}
    sentences = page_sentences(rd('index.html'))

    def spec_info(path):
        if path not in specs:
            text = rd(path)
            lines = text.split('\n')
            items = parse_spec(text)
            defs = {n: v for n, v in items.items() if v[0] == 'definition'}
            deps = {}
            for n, (_, a, b) in defs.items():
                deps[n] = set(IDENT.findall(block(lines, a, b).split('`', 1)[1])) & set(defs) - {n}
            for n, (_, a, b) in defs.items():
                cb = code_bytes(block(lines, a, b))
                if cb is not None:
                    matches = body_index.get(cb, [])
                    if not matches:
                        raise TrailError(f'{path}: code definition {n} matches no function body in the modules')
                    code_defs[(path, n)] = {'bytes': cb, 'line': a, 'matches': matches}
            specs[path] = {'path': path, 'text': text, 'lines': lines, 'items': items, 'deps': deps,
                           'sha': sha(text)}
        return specs[path]

    def code_closure(sp, names):
        seen, todo = set(), [n for n in names if n in sp['deps']]
        while todo:
            n = todo.pop()
            if n in seen:
                continue
            seen.add(n)
            todo.extend(sp['deps'][n] - seen)
        return sorted(n for n in seen if (sp['path'], n) in code_defs)

    def source_page(path):
        if path not in sources:
            base = os.path.basename(path)
            name = base + '.html'
            if any(s['page'] == name for s in sources.values()):
                name = path.replace('/', '__') + '.html'
            sources[path] = {'path': path, 'page': name, 'text': rd(path), 'roles': set()}
        return sources[path]

    for row in chain['claims']:
        rrow = {'claim': row['claim'], 'slug': slug(row['claim']), 'row': row, 'receipts': [],
                'head': sentences.get(row['claim']), 'label': row['title'],
                'class_path': os.path.join(BUBBLE, row['class_sentence_file'])}
        if rrow['head'] is None:
            raise TrailError(f'{row["claim"]}: no row in the results table of index.html')
        rrow['class_text'] = rd(rrow['class_path'])
        for rc in row['receipts']:
            case = rc['case']
            if case not in receipts:
                attest_path = os.path.join(BUBBLE, rc['attest_file'])
                att = json.loads(rd(attest_path))
                ver = att['verdict']
                if ver['verdict'] != 'passed' or rc['status'] != 'PROVED':
                    raise TrailError(f'{case}: receipt did not pass')
                src_path = resolve(rc['source_file'], rc['source_sha256'])
                spec_path = resolve(rc['spec_file'], rc['spec_sha256'])
                sp = spec_info(spec_path)
                src = source_page(src_path)
                src['roles'].add(case)
                clo = json.loads(rd(os.path.join(EVID, 'closures', case + '.closure.json')))
                croot = os.path.normpath(clo['project_root']) + '/'
                loaded = []  # project .ml files the run loaded (the records do not give execution order)
                for rec in clo['records']:
                    p = os.path.normpath(rec.get('resolved_path') or '')
                    if p.startswith(croot) and p.endswith('.ml'):
                        q = resolve(p[len(croot):], rec['sha256'])
                        if q not in loaded:
                            loaded.append(q)
                src_lines = src['text'].split('\n')

                def bindings_of(name, before=None):
                    """Every `let NAME` line in the loaded files, and in the proof file above line `before`."""
                    pat = re.compile(r'\s*let\s+(rec\s+)?%s\b' % re.escape(name))
                    locs = [(q, k + 1) for q in sorted(loaded) for k, ln in enumerate(rd(q).split('\n'))
                            if pat.match(ln)]
                    if before:
                        locs += [(src_path, k + 1) for k, ln in enumerate(src_lines[:before - 1]) if pat.match(ln)]
                    for q, _ in locs:
                        source_page(q)
                    return locs
                thms = []
                for bnd in ver['bindings']:
                    name = bnd['name']
                    if name not in sp['items'] or sp['items'][name][0] != 'theorem':
                        raise TrailError(f'{case}: {name} is not a theorem of {spec_path}')
                    _, a, b = sp['items'][name]
                    stmt = block(sp['lines'], a, b)
                    also, kind = [], None
                    if bnd.get('line') is not None:
                        ln0 = bnd['line']
                        where = (src_path, ln0, 'receipt')
                        if not re.search(r'\b%s\b' % re.escape(name), src_lines[ln0 - 1]):
                            raise TrailError(f'{case}: line {ln0} of {src_path} does not name {name}')
                        j = ln0 - 1
                        while not src_lines[j].rstrip().endswith(';;'):
                            j += 1
                        if re.search(r'ACCEPT_TAC\s+%s\b' % re.escape(name), '\n'.join(src_lines[ln0 - 1:j + 1])):
                            kind, also = 'accept', bindings_of(name, ln0)
                    else:
                        where, kind, also = None, 'search', bindings_of(name)
                        if not also:
                            raise TrailError(f'{case}: {name} has no recorded line and no binding in the loaded files')
                    words = set(IDENT.findall(stmt.split('`', 1)[1]))
                    direct = sorted(n for n in words if (spec_path, n) in code_defs)
                    via = [n for n in code_closure(sp, words) if n not in direct]
                    thms.append({'name': name, 'spec_lines': (a, b), 'stmt': stmt, 'where': where, 'binding': bnd,
                                 'also': also, 'also_kind': kind,
                                 'spec_status': ver['spec']['bindings'].get(name), 'direct': direct, 'via': via})
                pins = ver['spec'].get('pins') or {}
                spec_code = sorted(n for (p, n) in code_defs if p == spec_path)
                receipts[case] = {'case': case, 'rc': rc, 'att': att, 'attest_path': attest_path, 'src': src_path,
                                  'spec': spec_path, 'thms': thms, 'pins': pins, 'spec_code': spec_code,
                                  'rows': []}
            receipts[case]['rows'].append(row['claim'])
            rrow['receipts'].append(receipts[case])
        rows.append(rrow)

    replay = None
    rtext = rd('replay/README.md')
    blocks = re.findall(r'```(\w+)\n(.*?)\n```', rtext, re.S)
    cmds = [b for k, b in blocks if k == 'sh' and 'replay/c5.py' in b]
    ok = [b for k, b in blocks if k == 'text' and b.startswith('PASSED ')]
    if len(cmds) == 1 and len(ok) == 1:
        replay = {'cmds': cmds[0], 'line': ok[0]}
    else:
        raise TrailError('replay/README.md: expected one command block and one PASSED line')
    return {'chain': chain, 'mods': mods, 'specs': specs, 'sources': sources, 'receipts': receipts,
            'rows': rows, 'code_defs': code_defs, 'replay': replay}


# ---------------------------------------------------------------- HTML

CSS = """
:root { --bg:#fbfbfa; --ink:#1d2129; --dim:#5b6372; --line:#e2e4e8; --acc:#2f5bb7; --code:#f1f2f4; --ok:#1d7a46; --hl:#fff3b8; }
@media (prefers-color-scheme: dark) { :root { --bg:#0f1116; --ink:#dde1e8; --dim:#9aa3b3; --line:#2a2f3a; --acc:#8fb0ff; --code:#1a1e27; --ok:#5fd08e; --hl:#3d3615; } }
html { background:var(--bg); color:var(--ink); }
body { margin:0 auto; max-width:980px; padding:22px 22px 80px; font:16px/1.55 -apple-system,"Segoe UI",Helvetica,Arial,sans-serif; }
h1 { font-size:26px; line-height:1.25; margin:6px 0 14px; }
h2 { font-size:20px; margin:34px 0 10px; padding-top:10px; border-top:1px solid var(--line); }
h3 { font-size:16px; margin:0 0 8px; }
a { color:var(--acc); }
code, pre { font:12.5px/1.45 ui-monospace,Menlo,Consolas,monospace; }
code { background:var(--code); padding:1px 4px; border-radius:4px; }
pre { background:var(--code); padding:10px 12px; border-radius:8px; overflow:auto; }
pre code { background:none; padding:0; }
pre.stmt { white-space:pre-wrap; word-break:break-all; max-height:28em; }
.crumbs { font-size:14px; color:var(--dim); }
.walk { display:flex; flex-wrap:wrap; gap:6px; align-items:center; font-size:14px; margin:10px 0 18px; }
.walk a, .walk span.s { border:1px solid var(--line); border-radius:999px; padding:3px 10px; text-decoration:none; background:var(--code); }
.walk .arr { color:var(--dim); }
blockquote { margin:10px 0; padding:8px 14px; border-left:4px solid var(--acc); background:var(--code); border-radius:0 8px 8px 0; }
.thm { border:1px solid var(--line); border-radius:10px; padding:14px 16px; margin:14px 0; }
.thm:target, .step:target, .fn:target { outline:3px solid var(--acc); outline-offset:2px; }
.thm, .step, .fn, .box, h2 { scroll-margin-top:70px; }
.src div { scroll-margin-top:120px; }
ol.steps { margin:6px 0 0; padding-left:22px; }
ol.steps > li { margin:10px 0; }
ol.steps > li > b { display:inline-block; min-width:5.5em; }
.ok { color:var(--ok); font-weight:600; }
.dim { color:var(--dim); font-size:14px; }
.box { border:1px solid var(--line); border-radius:10px; padding:12px 16px; margin:12px 0; background:var(--code); }
.box pre { background:var(--bg); }
.replay { border-color:var(--ok); }
table { border-collapse:collapse; font-size:13.5px; line-height:1.4; }
th, td { border:1px solid var(--line); padding:5px 8px; vertical-align:top; text-align:left; }
th { background:var(--code); }
.tw { overflow-x:auto; margin:10px 0; }
.src { font:12.5px/1.5 ui-monospace,Menlo,Consolas,monospace; background:var(--code); border-radius:8px; padding:8px 0; overflow-x:auto; }
.src { counter-reset:ln; }
.src div { white-space:pre; padding:0 12px 0 0; counter-increment:ln; }
.src div::before { content:counter(ln); display:inline-block; width:4.5em; padding-right:1em; text-align:right; color:var(--dim); user-select:none; }
.src div:target { background:var(--hl); }
pre.hex { line-height:1.5; }
.hex .o { color:var(--dim); }
"""


def page(title, crumbs, body, depth):
    up = '../' * depth
    nav = ' · '.join([f'<a href="{up}index.html">Vortex Echo</a>', f'<a href="{up}trail/index.html">Proof trail</a>']
                     + crumbs)
    return ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
            f'<title>{esc(title)}</title>\n<link rel="icon" href="data:,">\n<style>{CSS}</style>\n</head>\n<body>\n'
            f'<p class="crumbs">{nav}</p>\n{body}\n'
            '<p class="dim">Generated by <code>tools/build_trail.py</code> from the published files; checked by '
            '<code>tools/check_trail.py</code>.</p>\n</body>\n</html>\n')


def short(h):
    return h[:8] + '…' + h[-6:]


def fn_label(m, idx):
    ex = m['wasm']['exports'].get(idx)
    return f'function {idx}' + (f' (export <code>{esc(ex[0])}</code>)' if ex else '')


def func_entry(m, idx):
    for f in m['wasm']['funcs']:
        if f[0] == idx:
            return f
    raise TrailError(f'{m["key"]}: no function {idx}')


def code_ref(M, sp_path, name, depth, show_range=True):
    """Link(s) from a code definition in a spec to the function(s) whose body it equals."""
    up = '../' * depth
    out = []
    for key, idx in M['code_defs'][(sp_path, name)]['matches']:
        m = M['mods'][key]
        _, e0, b0, b1 = func_entry(m, idx)
        rng = (f' bytes <span data-def="{esc(name)}" data-spec="{esc(sp_path)}" data-module="{esc(m["path"])}" '
               f'data-start="{b0}" data-end="{b1}">[{b0}, {b1})</span>, {b1 - b0} B') if show_range else ''
        out.append(f'<a href="{up}trail/bytes/{key}.html#f{idx}"><code>{esc(name)}</code></a> = '
                   f'{os.path.basename(m["path"])} {fn_label(m, idx)}{rng}')
    return '; '.join(out)


def theorem_card(M, R, t, claimed, depth=1):
    up = '../' * depth
    name, (a, b) = t['name'], t['spec_lines']
    sp = R['spec']
    rc = R['rc']
    tid = esc(name)
    cid = esc(card_id(M, R, name))
    def plink(p, ln, how):
        return (f'<a href="src/{esc(M["sources"][p]["page"])}#L{ln}" data-src="{esc(p)}" data-line="{ln}" '
                f'data-name="{tid}" data-how="{how}" data-attest="{esc(R["attest_path"])}"><code>'
                f'{esc(os.path.basename(p))}</code> line {ln}</a> (<a href="{GH}{esc(p)}#L{ln}">on GitHub</a>)')
    also = t['also']
    many = (' (it is bound in more than one of them; the closure records do not say in which order they ran, so '
            'all are listed)') if len(also) > 1 else ''
    if t['where']:
        p, ln, how = t['where']
        proof = plink(p, ln, how) + ', the line the receipt records.'
        if t['also_kind'] == 'accept':
            proof += (f' That line restates the theorem and closes it with <code>ACCEPT_TAC {tid}</code>, the theorem '
                      f'of that name proved in a file the run loaded{many}: '
                      + '; '.join(plink(q, k, 'accept') for q, k in also) + '.')
    else:
        proof = ('The receipt records no line for this name; it was bound in a file the proof loads' + many + ': '
                 + '; '.join(plink(q, k, 'search') for q, k in also) + '.')
    bnd = t['binding']
    det = esc(bnd.get('detail') or '')
    rec = (f'<span data-attest="{esc(R["attest_path"])}" data-name="{tid}" data-status="{esc(bnd["status"])}" '
           f'data-spec-status="{esc(t["spec_status"])}"><span class="ok">{esc(bnd["status"])}</span> ({det}); '
           f'statement against the frozen spec: <span class="ok">{esc(t["spec_status"])}</span></span>. '
           f'Receipt <a href="#r-{esc(R["case"])}"><code>{esc(R["case"])}</code></a>: '
           f'{esc(rc["line"].split(":")[0])}, 0 new axioms; cold replay: '
           f'<a href="{up}{esc(os.path.join(BUBBLE, rc["cold"]["file"]))}">{esc(rc["cold"]["outcome"])}</a>.')
    if R['case'] == REPLAY_CASE:
        rec += f' You can <a href="#rerun">re-run this proof yourself</a>.'
    mod = M['mods']['vortex_a1']
    if t['direct'] or t['via']:
        parts = []
        if t['direct']:
            parts.append('names directly: ' + '; '.join(code_ref(M, sp, n, depth) for n in t['direct']))
        if t['via']:
            parts.append('through definitions in its spec: ' + ', '.join(
                f'<a href="{up}trail/bytes/{M["code_defs"][(sp, n)]["matches"][0][0]}.html#f'
                f'{M["code_defs"][(sp, n)]["matches"][0][1]}"><code>{esc(n)}</code></a>' for n in t['via']))
        byt = 'The statement ' + '. It also reaches, '.join(parts) + '.'
    else:
        byt = ('The statement names no function of the module, directly or through the definitions in its spec; '
               f'it is about the terms it names. The functions this spec fixes byte for byte are listed with '
               f'<a href="#r-{esc(R["case"])}">its receipt</a>.')
    byt += (f' Module <a href="{up}trail/bytes/vortex_a1.html"><code>vortex_a1.wasm</code></a>, SHA-256 '
            f'<code>{short(mod["sha"])}</code>.')
    badge = ' <span class="dim">claimed in this row</span>' if claimed else ''
    qual = f' <span class="dim">(receipt <code>{esc(R["case"])}</code>)</span>' if cid != tid else ''
    return (f'<article class="thm" id="{cid}">\n<h3><code>{tid}</code>{qual}{badge}</h3>\n<ol class="steps">\n'
            f'<li class="step" id="{cid}-stmt"><b>Statement</b> frozen spec '
            f'<a href="{GH}{esc(sp)}#L{a}-L{b}"><code>{esc(os.path.basename(sp))}</code> lines {a}–{b}</a> '
            f'(<a href="{up}{esc(sp)}">file</a>; SHA-256 <code>{short(M["specs"][sp]["sha"])}</code>, the hash the '
            f'receipt locks):\n<pre class="stmt" data-spec="{esc(sp)}" data-lines="{a}-{b}" data-name="{tid}">'
            f'{esc(t["stmt"])}</pre></li>\n'
            f'<li class="step" id="{cid}-proof"><b>Proof</b> {proof}</li>\n'
            f'<li class="step" id="{cid}-rcpt"><b>Receipt</b> {rec}</li>\n'
            f'<li class="step" id="{cid}-bytes"><b>Bytes</b> {byt}</li>\n</ol>\n</article>')


def pick(thms):
    """The theorem a walk starts from: one about named code (a _CORRECT contract if there is one), else the first."""
    return (next((t for t in thms if t['direct'] and '_CORRECT' in t['name']), None)
            or next((t for t in thms if t['direct']), None) or thms[0])


def walk_bar(first, rerun, fid=None):
    fid = fid or first
    steps = [('sentence', '#sentence'), ('statement', f'#{fid}-stmt'), ('proof line', f'#{fid}-proof'),
             ('receipt', f'#{fid}-rcpt'), ('bytes', f'#{fid}-bytes')]
    if rerun:
        steps.append(('re-run it yourself', '#rerun'))
    return ('<p class="walk">' + ' <span class="arr">→</span> '.join(
        f'<a href="{h}">{esc(s)}</a>' for s, h in steps) + f' <span class="dim">(for <code>{esc(first)}</code>)'
        '</span></p>')


def receipt_box(M, R, depth=1):
    up = '../' * depth
    rc, case = R['rc'], R['case']
    links = [f'<a href="{up}{esc(R["attest_path"])}">attest summary</a>',
             f'<a href="{up}{esc(os.path.join(EVID, "receipts", case + ".inspect.txt"))}">inspect listing</a>',
             f'<a href="{up}{esc(os.path.join(BUBBLE, rc["cold"]["file"]))}">cold replay record</a>',
             f'<a href="{up}{esc(os.path.join(EVID, "closures", case + ".closure.json"))}">closure inventory</a>']
    if rc['check_rung'].get('file'):
        links.append(f'<a href="{up}{esc(os.path.join(BUBBLE, rc["check_rung"]["file"]))}">check-rung output</a>')
    sp = R['spec']
    pinned = [n for n in R['spec_code'] if R['pins'].get(n) == 'pinned']
    code = ''
    if R['spec_code']:
        code = ('<p>The spec fixes the exact bytes of these functions as definitions, and the receipt checked each '
                f'definition against HOL Light\'s registry ({len(pinned)} of {len(R["spec_code"])} recorded as '
                '<span class="ok">pinned</span>):</p>\n<ul>\n' + '\n'.join(
                    f'<li><a href="{GH}{esc(sp)}#L{M["code_defs"][(sp, n)]["line"]}">line '
                    f'{M["code_defs"][(sp, n)]["line"]}</a>: {code_ref(M, sp, n, depth)}; receipt: '
                    f'<span data-attest="{esc(R["attest_path"])}" data-pin="{esc(n)}" '
                    f'data-pin-status="{esc(R["pins"].get(n))}">{esc(R["pins"].get(n) or "not listed")}</span></li>'
                    for n in R['spec_code']) + '\n</ul>')
    return (f'<div class="box" id="r-{esc(case)}">\n<p><strong>Receipt <code>{esc(case)}</code></strong> '
            f'(official run <code>{esc(rc["official_run"].split("/")[-1])}</code>)</p>\n'
            f'<pre data-attest="{esc(R["attest_path"])}" data-line="verdict">{esc(rc["line"])}</pre>\n'
            f'<p>Proof file <a href="src/{esc(M["sources"][R["src"]]["page"])}"><code>{esc(R["src"])}</code></a> '
            f'(SHA-256 <code>{short(rc["source_sha256"])}</code>), frozen spec <a href="{up}{esc(sp)}"><code>'
            f'{esc(sp)}</code></a> (SHA-256 <code>{short(rc["spec_sha256"])}</code>). Cold replay: '
            f'{esc(rc["cold"]["headline"])}. Check-rung: {esc(rc["check_rung"]["result"])}.</p>\n'
            f'<p class="dim">Freeze record: {esc(rc["spec_frozen_record"])}</p>\n'
            f'<p>{" · ".join(links)}</p>\n{code}\n</div>')


def rerun_box(M, depth=1):
    up = '../' * depth
    r = M['replay']
    return (f'<div class="box replay" id="rerun">\n<p><strong>Re-run it yourself.</strong> This receipt\'s proof '
            'can be re-run on Linux without hol-hearth: a fresh HOL Light loads the bundled WebAssembly model from '
            'source, runs the proof and checks every theorem against the same frozen spec. '
            f'<a href="{up}replay/README.md"><code>replay/README.md</code></a> lists the prerequisites (OCaml 5.4.0, '
            'Camlp5 8.04.00 and a few packages) and says what the replay checks and what it trusts. From the root of '
            f'a checkout:</p>\n<pre data-from="replay/README.md">{esc(r["cmds"])}</pre>\n'
            f'<p>A successful run exits with status 0 and ends with:</p>\n'
            f'<pre data-from="replay/README.md">{esc(r["line"])}</pre>\n</div>')


def shared_page(R):
    return f'receipt-{R["case"]}.html'


def card_id(M, R, name):
    """The id of the card of theorem NAME of receipt R: the bare name, or NAME--<case> where two receipts shown on one
    row page prove theorems of the same name (C8e and C8a-births), so that every card id on a page is unique."""
    if 'qual' not in M:
        q = set()
        for rr in M['rows']:
            seen = {}
            for R2 in rr['receipts']:
                for t in R2['thms']:
                    seen.setdefault(t['name'], set()).add(R2['case'])
            for n, cases in seen.items():
                if len(cases) > 1:
                    q.update((c, n) for c in cases)
        M['qual'] = q
    return f'{name}--{R["case"]}' if (R['case'], name) in M['qual'] else name


def card_page(M, R, name):
    """The trail page (under trail/) that holds the card of theorem NAME of receipt R."""
    by_claim = {rr['claim']: rr for rr in M['rows']}
    for c in R['rows']:
        ct = by_claim[c]['row']['claim_theorems']
        if not ct or name in ct:
            return f'{slug(c)}.html'
    return shared_page(R)


def receipt_page(M, R, rows):
    """One page with every theorem card of a receipt that backs rows naming their own claimed theorems."""
    links = ', '.join(f'<a href="{rr["slug"]}.html">{esc(rr["claim"])}</a>' for rr in rows)
    body = (f'<h1>Receipt <code>{esc(R["case"])}</code>: all {len(R["thms"])} theorems</h1>\n'
            f'<p>This receipt backs {links}. Each of those pages shows the theorems its row claims; this page has the '
            'card of every theorem the receipt proved.</p>\n'
            '<h2>The receipt</h2>\n' + receipt_box(M, R) + '\n'
            + '\n'.join(theorem_card(M, R, t, False) for t in R['thms']))
    return page(f'Proof trail, receipt {R["case"]}: Vortex Echo', [f'<code>{esc(R["case"])}</code>'], body, 1)


def row_page(M, rr):
    row = rr['row']
    claimed = set(row['claim_theorems'] or [])
    first = fid = None
    parts = []
    rerun = any(R['case'] == REPLAY_CASE for R in rr['receipts'])
    for R in rr['receipts']:
        order = ([t for t in R['thms'] if t['name'] in claimed] + [t for t in R['thms'] if t['name'] not in claimed]
                 if claimed else R['thms'])
        if first is None:
            first = pick([t for t in order if t['name'] in claimed] if claimed else order)['name']
            fid = card_id(M, R, first)
        cards = []
        for k, t in enumerate(order):
            if claimed and t['name'] not in claimed:  # the receipt's other theorems: one shared page, not one copy per row
                rest = order[k:]
                cards.append(f'<h3>Also proved by this receipt ({len(rest)} more)</h3>\n<p>Their cards are on '
                             f'<a href="{shared_page(R)}">the page of receipt <code>{esc(R["case"])}</code></a>: '
                             + ', '.join(f'<a href="{shared_page(R)}#{esc(card_id(M, R, x["name"]))}" data-receipt="{esc(R["case"])}"><code>{esc(x["name"])}</code></a>'
                                         for x in rest) + '.</p>')
                break
            cards.append(theorem_card(M, R, t, t['name'] in claimed))
        intro = ''
        if len(R['rows']) > 1:
            others = [c for c in dict.fromkeys(R['rows']) if c != rr['claim']]
            intro = ('<p class="dim">This receipt also backs ' + ', '.join(
                f'<a href="{slug(c)}.html">{esc(c)}</a>' for c in others) + '.</p>')
        parts.append(f'<h2>Receipt <code>{esc(R["case"])}</code>: {len(R["thms"])} theorems</h2>\n{intro}\n'
                     + receipt_box(M, R) + '\n' + (rerun_box(M) if R['case'] == REPLAY_CASE else '') + '\n'
                     + '\n'.join(cards))
    head = rr['head']
    sent = (f'<p>On the main page (<a href="../index.html#row-{rr["slug"]}">results table</a>, row '
            f'“{esc(head[0])}”):</p>\n<blockquote data-from="index.html">{esc(head[1])}</blockquote>\n')
    if head[1] != rr['label']:
        sent += (f'<p>Its label in the claim table, <a href="../claims.json"><code>claims.json</code></a>:</p>\n'
                 f'<blockquote data-from="claims.json" data-claim="{esc(rr["claim"])}">{esc(rr["label"])}</blockquote>\n')
    sent += (f'<details><summary>The reviewed wording of this result (its class sentence, '
             f'<code>{esc(os.path.basename(rr["class_path"]))}</code>)</summary>\n'
             f'<pre class="stmt" data-from="{esc(rr["class_path"])}">{esc(rr["class_text"].rstrip())}</pre>\n'
             f'<p><a href="../{esc(rr["class_path"])}">file</a></p></details>\n'
             '<p class="dim">These sentences are summaries. Where they and the theorem statements below differ, the '
             'frozen statements are the authority.</p>')
    thm_list = []
    for R in rr['receipts']:
        names = [t['name'] for t in R['thms'] if not claimed or t['name'] in claimed]
        thm_list.append(f'<code>{esc(R["case"])}</code>: ' + ', '.join(
            f'<a href="#{esc(card_id(M, R, n))}" data-receipt="{esc(R["case"])}"><code>{esc(n)}</code></a>' for n in names)
            + ('' if not claimed else f' <span class="dim">(claimed; {len(R["thms"]) - len(names)} more below)</span>'))
    body = (f'<h1>{esc(rr["claim"])}: {esc(rr["label"])}</h1>\n{walk_bar(first, rerun, fid)}\n'
            f'<h2 id="sentence">The sentence</h2>\n{sent}\n'
            f'<h2 id="theorems">The theorems</h2>\n<p>{"<br>".join(thm_list)}</p>\n<p class="dim">Each card below gives the '
            'statement exactly as frozen in the spec, the proof line, the receipt entry that recorded it, and the '
            'functions of <code>vortex_a1.wasm</code> it is about.</p>\n' + '\n'.join(parts))
    return page(f'Proof trail {rr["claim"]}: Vortex Echo', [esc(rr['claim'])], body, 1)


def source_html(M, s):
    lines = s['text'].split('\n')
    if lines and lines[-1] == '':
        lines = lines[:-1]
    rows = '\n'.join(f'<div id="L{k}">{esc(l)}</div>' for k, l in enumerate(lines, 1))
    used = sorted(s['roles'])
    role = ('The proof file of receipt' + ('s ' if len(used) > 1 else ' ') + ', '.join(
        f'<code>{esc(c)}</code>' for c in used) + '.') if used else 'A file loaded by a proof run.'
    body = (f'<h1><code>{esc(os.path.basename(s["path"]))}</code></h1>\n<p>{role} Published at '
            f'<a href="../../{esc(s["path"])}"><code>{esc(s["path"])}</code></a> (SHA-256 '
            f'<code>{sha(s["text"])}</code>; <a href="{GH}{esc(s["path"])}">on GitHub</a>). Line N has the '
            f'anchor <code>#LN</code>.</p>\n<div class="src" data-src="{esc(s["path"])}">\n{rows}\n</div>')
    return page(os.path.basename(s['path']) + ': Vortex Echo proof trail',
                [f'<code>{esc(os.path.basename(s["path"]))}</code>'], body, 2)


def hexdump(b, start, end):
    out = []
    for off in range(start - start % 16, end, 16):
        cells = [f'{b[i]:02x}' if start <= i < end else '  ' for i in range(off, off + 16)]
        out.append(f'<span class="o">{off:08x}</span>  ' + ' '.join(cells[:8]) + '  ' + ' '.join(cells[8:]))
    return '\n'.join(l.rstrip() for l in out)


def bytes_page(M, m):
    key = m['key']
    pinned_by, named_by = {}, {}
    for (sp, n), d in sorted(M['code_defs'].items()):
        for k2, idx in d['matches']:
            if k2 == key:
                pinned_by.setdefault(idx, []).append((sp, n, d['line']))
    for R in M['receipts'].values():
        for t in R['thms']:
            for n in t['direct']:
                for k2, idx in M['code_defs'][(R['spec'], n)]['matches']:
                    if k2 == key:
                        named_by.setdefault(idx, {})[(t['name'], R['case'])] = R
    w = m['wasm']
    secs = '\n'.join(f'<tr><td>{sid}</td><td>{SECTION_NAMES.get(sid, "?")}</td><td>[{s0}, {e})</td>'
                     f'<td>{e - s0}</td></tr>' for sid, s0, _, e in w['sections'])
    ftab, fsecs = [], []
    for idx, e0, b0, b1 in w['funcs']:
        pb = pinned_by.get(idx)
        ex = ', '.join(w['exports'].get(idx, []))
        cell = f'<a href="#f{idx}">{idx}</a>' if pb else str(idx)
        ftab.append(f'<tr><td>{cell}</td><td>{esc(ex)}</td><td>[{b0}, {b1})</td><td>{b1 - b0}</td>'
                    f'<td>{len(pb) if pb else ""}</td></tr>')
        if not pb:
            continue
        defs = sorted({n for _, n, _ in pb})
        specs_ = ', '.join(f'<a href="{GH}{esc(sp)}#L{ln}"><code>{esc(os.path.basename(sp))}</code></a>'
                           for sp, _, ln in pb)
        nb = named_by.get(idx, {})
        refs = ', '.join(f'<a href="../{card_page(M, R, t)}#{esc(card_id(M, R, t))}" data-receipt="{esc(c)}"><code>{esc(t)}</code></a>'
                         + (f' (<code>{esc(c)}</code>)' if card_id(M, R, t) != t else '')
                         for (t, c), R in sorted(nb.items()))
        fsecs.append(
            f'<section class="fn" id="f{idx}">\n<h2>{fn_label(m, idx)}</h2>\n'
            f'<p>Body: bytes <strong>[{b0}, {b1})</strong> of <code>{os.path.basename(m["path"])}</code>, {b1 - b0} '
            f'bytes (its code-section entry starts at byte {e0} with the body size, '
            f'{b0 - e0} byte{"s" if b0 - e0 > 1 else ""}). The definition{"s" if len(defs) > 1 else ""} '
            f'{", ".join(f"<code>{esc(n)}</code>" for n in defs)} in {len(pb)} frozen spec'
            f'{"s" if len(pb) > 1 else ""} ({specs_}) list exactly these bytes.</p>\n'
            + (f'<p>Theorems that name it directly: {refs}.</p>\n' if refs else '')
            + f'<pre class="hex" data-module="{esc(m["path"])}" data-start="{b0}" data-end="{b1}">'
            f'{hexdump(m["bytes"], b0, b1)}</pre>\n</section>')
    if key == 'vortex_a1':
        sums = (' The same hash is in <a href="../../module/SHA256SUMS"><code>module/SHA256SUMS</code></a> and '
                '<a href="../../claims.json"><code>claims.json</code></a>, and the demo checks it before running the '
                'module.')
    else:
        shared = sorted({idx for (sp, n), d in M['code_defs'].items() for k2, idx in d['matches'] if k2 == key})
        same = [i for i in shared
                if any(k2 == 'vortex_a1' and i2 == i for d in M['code_defs'].values() for k2, i2 in d['matches']
                       if (key, i) in d['matches'])]
        sums = (' Some receipts also read this earlier core module. The functions of it that a frozen spec fixes ('
                + ', '.join(str(i) for i in shared) + ') have exactly the same body bytes as functions '
                + ', '.join(f'<a href="vortex_a1.html#f{i}">{i}</a>' for i in same)
                + ' of <a href="vortex_a1.html"><code>vortex_a1.wasm</code></a>, so each such definition equals both.'
                if shared == same else ' Some receipts also read this earlier core module.')
    body = (f'<h1>The bytes: <code>{os.path.basename(m["path"])}</code></h1>\n'
            f'<p><a href="../../{esc(m["path"])}"><code>{esc(m["path"])}</code></a>: {len(m["bytes"]):,} bytes, '
            f'SHA-256 <code data-module="{esc(m["path"])}" data-sha256="{m["sha"]}">{m["sha"]}</code>.{sums}</p>\n'
            '<p>Offsets below are byte offsets in the file (hex in the dumps, decimal elsewhere). The functions a '
            'frozen spec fixes byte for byte have a hex view; the definitions in the specs equal these bodies '
            'exactly (from the local declarations to the final <code>end</code> byte, <code>0b</code>).</p>\n'
            f'<h2>Sections</h2>\n<div class="tw"><table><thead><tr><th>id</th><th>section</th><th>bytes</th>'
            f'<th>size</th></tr></thead><tbody>\n{secs}\n</tbody></table></div>\n'
            f'<h2>Functions</h2>\n<p>{len(w["funcs"])} function bodies, no imported functions'
            f'{"" if w["imports"] == 0 else " (" + str(w["imports"]) + " imported)"}. Linked indices have a hex '
            'view below.</p>\n<div class="tw"><table><thead><tr><th>index</th><th>export</th><th>body bytes</th>'
            f'<th>size</th><th>specs fixing it</th></tr></thead><tbody>\n{"".join(ftab)}\n</tbody></table></div>\n'
            + '\n'.join(fsecs))
    return page(os.path.basename(m['path']) + ': Vortex Echo proof trail',
                [f'<code>{os.path.basename(m["path"])}</code>'], body, 2)


def index_page(M):
    rows = []
    for rr in M['rows']:
        n = sum(len(R['thms']) for R in rr['receipts'])
        claimed = rr['row']['claim_theorems']
        rows.append(f'<tr><td><a href="{rr["slug"]}.html">{esc(rr["claim"])}</a></td><td>{esc(rr["row"]["kind"])}'
                    f'</td><td>{esc(rr["label"])}</td><td>' + '<br>'.join(
                        f'<a href="{rr["slug"]}.html#r-{esc(R["case"])}"><code>{esc(R["case"])}</code></a>'
                        for R in rr['receipts']) + f'</td><td>{len(claimed) if claimed else n}</td></tr>')
    c5 = next(rr for rr in M['rows'] if any(R['case'] == REPLAY_CASE for R in rr['receipts']))
    R5 = next(R for R in c5['receipts'] if R['case'] == REPLAY_CASE)
    t5 = pick(R5['thms'])
    mod = M['mods']['vortex_a1']
    body = (
        '<h1>The proof trail</h1>\n'
        '<p>Every result on the main page can be followed, in a click or two, from its sentence to the evidence: '
        'the theorem\'s exact statement in the frozen spec, the line of the proof file that proves it, the receipt '
        'of the official run that recorded it as proved, the cold replay, and the bytes of '
        f'<a href="bytes/vortex_a1.html"><code>vortex_a1.wasm</code></a> (SHA-256 <code>{short(mod["sha"])}</code>) '
        'it is about.</p>\n'
        '<p class="walk"><span class="s">sentence</span> <span class="arr">→</span> <span class="s">statement'
        '</span> <span class="arr">→</span> <span class="s">proof line</span> <span class="arr">→</span> '
        '<span class="s">receipt</span> <span class="arr">→</span> <span class="s">bytes</span></p>\n'
        f'<div class="box replay"><p><strong>Start here: part 1 of C5.</strong> '
        f'<a href="{c5["slug"]}.html#{esc(card_id(M, R5, t5["name"]))}" data-receipt="{esc(R5["case"])}"><code>{esc(t5["name"])}</code></a> is a theorem about the '
        f'exact bytes of one function of the module. Its card shows the statement, the proof line, the receipt '
        f'entry and the function\'s bytes, and this part of C5 can be '
        f'<a href="{c5["slug"]}.html#rerun">re-run on your own machine</a> in a few minutes.</p></div>\n'
        '<h2>All rows</h2>\n<div class="tw"><table><thead><tr><th>row</th><th>kind</th><th>label</th>'
        '<th>receipts</th><th>theorems</th></tr></thead><tbody>\n' + '\n'.join(rows) + '\n</tbody></table></div>\n'
        '<p class="dim">The theorems column counts the theorems the row claims (all theorems of its receipts '
        'unless the row names some).</p>\n'
        '<h2>The bytes</h2>\n<p><a href="bytes/vortex_a1.html"><code>vortex_a1.wasm</code></a>: its sections, its '
        'functions and a hex view of every function a frozen spec fixes. <a href="bytes/ve_core.html"><code>'
        've_core.wasm</code></a>: the earlier core module some receipts also read.</p>\n'
        '<h2>How these pages are made and checked</h2>\n'
        '<p><code>python3 -I tools/build_trail.py</code> writes these pages from the published files: the claim '
        'table, the receipts, the specs, the proof files and the modules. <code>python3 -I tools/check_trail.py</code> '
        'checks them without using the generator: every relative link in these pages resolves (links to websites, '
        'GitHub included, are not followed), every quoted statement is the spec text '
        'at the stated lines, every proof line names its theorem, every receipt entry says proved and matched, and '
        'every byte range and hex line is the module\'s bytes. The pages show what the files record; that the '
        'files are the ones the runs used is <code>tools/check_tree.py</code>\'s job, and re-running a proof is '
        'the replay\'s.</p>')
    return page('Proof trail: Vortex Echo', [], body, 1)


def render(M):
    files = {f'{OUT}/index.html': index_page(M)}
    shared = {}
    for rr in M['rows']:
        files[f'{OUT}/{rr["slug"]}.html'] = row_page(M, rr)
        if rr['row']['claim_theorems']:
            for R in rr['receipts']:
                shared.setdefault(R['case'], (R, []))[1].append(rr)
    for case, (R, rows) in shared.items():
        files[f'{OUT}/{shared_page(R)}'] = receipt_page(M, R, rows)
    for s in M['sources'].values():
        files[f'{OUT}/src/{s["page"]}'] = source_html(M, s)
    for m in M['mods'].values():
        files[f'{OUT}/bytes/{m["key"]}.html'] = bytes_page(M, m)
    return files


def main():
    check = '--check' in sys.argv[1:]
    try:
        files = render(load())
    except TrailError as e:
        print(f'build_trail: {e}')
        return 1
    on_disk = set()
    for dp, _, fns in os.walk(os.path.join(ROOT, OUT)):
        for fn in fns:
            on_disk.add(os.path.relpath(os.path.join(dp, fn), ROOT))
    if check:
        bad = [p for p, s in files.items() if p not in on_disk or rd(p) != s]
        bad += [f'{p} (not generated)' for p in sorted(on_disk - set(files))]
        print(f'build_trail --check: {len(files)} pages, {len(bad)} differ')
        for p in bad:
            print('  ' + p)
        return 1 if bad else 0
    stale = sorted(on_disk - set(files))
    if stale:
        print('build_trail: files under trail/ that this run does not write (remove them by hand):')
        for p in stale:
            print('  ' + p)
    for p, s in files.items():
        os.makedirs(os.path.dirname(os.path.join(ROOT, p)), exist_ok=True)
        with open(os.path.join(ROOT, p), 'w') as f:
            f.write(s)
    print(f'build_trail: wrote {len(files)} pages under {OUT}/')
    return 1 if stale else 0


if __name__ == '__main__':
    sys.exit(main())
