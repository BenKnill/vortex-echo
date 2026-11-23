#!/usr/bin/env python3
"""check_trail.py: check the proof-trail pages under trail/ against the published files, without the generator.

Standard library only; run from the repository root:  python3 -I tools/check_trail.py

It reads every HTML page under trail/ and index.html, and checks:
  - links: every relative link (and every README.md link into trail/) resolves to a file in this repository, and every #fragment to an id in its target;
  - statements: every quoted theorem statement is, character for character, the `theorem NAME ... ;;` block at the
    stated lines of the frozen spec, and that spec is the one the receipt names;
  - proof lines: every proof link points at a line of the proof file that names the theorem, the line the receipt
    records; where that line closes the theorem with ACCEPT_TAC NAME (or the receipt records no line), the further
    links point at `let NAME` bindings in files the run loaded (by SHA-256 against its closure inventory);
  - receipt entries: every shown binding status, spec match, definition pin and PASSED line is what the receipt says,
    and the visible receipt entry text is exactly "<status> (<detail>); statement against the frozen spec: <match>";
    each theorem card's receipt step is that entry followed by exactly "Receipt CASE: PASSED FILE, N new axioms; cold
    replay: OUTCOME." with CASE, FILE, N and the verdict from the card's attestation, OUTCOME and its link from the
    receipt's cold-replay record (which must be a reproduced replay of that receipt); every receipt box shows the
    receipt's proof file and spec (by SHA-256), its cold-replay headline and record, and its check-rung result;
  - bytes: every byte range shown for a spec's code definition is exactly a function body of the module and equals
    the definition's byte list; every hex view shows the module's bytes; every shown module hash is the file's;
    every link to a function of a byte page (bytes/<module>.html#fN) labelled with a definition goes to the function
    whose body is that definition's bytes, and the "function N" text and byte range after it are that function's;
    every byte page's function sections and function table show the parsed module's function index, body range,
    size and entry offset;
  - cards: every id on a page is unique; every theorem card has its four step ids, and its statement and receipt
    entry name the same theorem; a link to a card labelled with a theorem name goes to a card of that theorem (of
    the receipt the link names, where it names one: data-receipt), and a page with two cards of one name is only
    linked through data-receipt; a link with data-receipt goes exactly to the root of the card of its labelled
    theorem and receipt (not to a step of it, another receipt's card or step, or any other fragment);
  - quotations: sentences quoted from index.html, replay/README.md, claims.json and the class-sentence files are
    in those files;
  - the main page: every theorem or definition quoted on index.html and in README.md is the spec text (as above),
    and every clause shown in its clause-by-clause reading (pieces separated by "…") occurs in it, in order;
    index.html's links have the same labels and targets, in the same order, as README.md's Markdown links, and
    both show the same half-open intervals "[a, b)" the same number of times;
  - rendered proof files show the file's lines; every claim row has a page with every theorem of its receipts
    (for a row that names its claimed theorems, the receipt's other theorems may be on trail/receipt-<case>.html,
    linked from the row page).
It does not re-run a proof (see replay/) and does not check that the files are the ones the runs used (check_tree.py).
"""
import hashlib, html, json, os, re, sys
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUBBLE = os.path.join(ROOT, 'proof-tree/tasks/bubble-echo')
VOID = {'meta', 'link', 'img', 'br', 'hr', 'input', 'source', 'wbr'}


class Page(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.items, self.stack, self.dup_ids = set(), [], [], [], []

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if 'id' in a:
            if a['id'] in self.ids:
                self.dup_ids.append(a['id'])
            self.ids.add(a['id'])
        for k in ('href', 'src'):
            if a.get(k):
                self.links.append(a[k])
        if tag in VOID:
            return
        rec = None
        if any(k.startswith('data-') for k in a) or (tag == 'div' and re.fullmatch(r'L\d+', a.get('id', ''))):
            rec = {'tag': tag, 'a': a, 'text': []}
            self.items.append(rec)
        self.stack.append((tag, rec))

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        while self.stack:
            t, _ = self.stack.pop()
            if t == tag:
                break

    def handle_data(self, data):
        for _, rec in self.stack:
            if rec is not None:
                rec['text'].append(data)


class BoxAnchors(HTMLParser):
    """The anchors inside each <div class="box" id="r-CASE">, parsed (so whitespace or line breaks inside tags
    cannot hide a link): {case: [(href, text), ...]}."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.boxes, self.depth, self.case, self.cur = {}, 0, None, None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == 'div':
            if self.case is None and a.get('class') == 'box' and (a.get('id') or '').startswith('r-'):
                self.case, self.depth = a['id'][2:], 1
                self.boxes.setdefault(self.case, [])
            elif self.case is not None:
                self.depth += 1
        elif tag == 'a' and self.case is not None:
            self.cur = [a.get('href') or '', []]

    def handle_endtag(self, tag):
        if tag == 'a' and self.cur is not None:
            self.boxes[self.case].append((self.cur[0], ''.join(self.cur[1]).strip()))
            self.cur = None
        elif tag == 'div' and self.case is not None:
            self.depth -= 1
            if self.depth == 0:
                self.case = None

    def handle_data(self, data):
        if self.cur is not None:
            self.cur[1].append(data)


def rel(p):
    return os.path.relpath(p, ROOT)


def read(path, mode='r'):
    with open(path, mode) as f:
        return f.read()


def norm(s):
    return re.sub(r'\s+', ' ', s).strip()


def leb(b, i):
    r = s = 0
    while True:
        x = b[i]
        i += 1
        r |= (x & 0x7f) << s
        s += 7
        if x < 0x80:
            return r, i


def bodies(b):
    """Set of (start, end) of the function bodies in the code section (section id 10)."""
    i, out = 8, set()
    while i < len(b):
        sid = b[i]
        size, j = leb(b, i + 1)
        if sid == 10:
            n, k = leb(b, j)
            for _ in range(n):
                sz, k2 = leb(b, k)
                out.add((k2, k2 + sz))
                k = k2 + sz
        i = j + size
    return out


def funcs(b):
    """{function index: (entry start, body start, body end)} from the import (2) and code (10) sections."""
    i, nimp, out = 8, 0, {}
    while i < len(b):
        sid = b[i]
        size, j = leb(b, i + 1)
        if sid == 2:
            n, k = leb(b, j)
            for _ in range(n):
                for _ in range(2):
                    ln, k = leb(b, k)
                    k += ln
                kind = b[k]
                k += 1
                if kind == 0:
                    _, k = leb(b, k)
                    nimp += 1
                elif kind == 1:
                    k += 1
                    fl = b[k]
                    _, k = leb(b, k + 1)
                    if fl & 1:
                        _, k = leb(b, k)
                elif kind == 2:
                    fl = b[k]
                    _, k = leb(b, k + 1)
                    if fl & 1:
                        _, k = leb(b, k)
                elif kind == 3:
                    k += 2
                else:
                    raise ValueError(f'import kind {kind}')
        if sid == 10:
            n, k = leb(b, j)
            for f in range(n):
                sz, k2 = leb(b, k)
                out[nimp + f] = (k, k2, k2 + sz)
                k = k2 + sz
        i = j + size
    return out


def def_bytes(sl, name):
    """The byte list of `definition NAME ... = [word ..; ..]` in spec lines SL, or None."""
    k = next((i for i, l in enumerate(sl) if l.strip() == f'definition {name}'), None)
    if k is None:
        return None
    j = next(i for i in range(k, len(sl)) if sl[i].rstrip().endswith('`;;'))
    m = re.search(r'=\s*\[(.*)\]\s*`;;\s*$', '\n'.join(sl[k:j + 1]), re.S)
    if not m:
        return None
    return bytes(int(re.fullmatch(r'\s*word\s+(\S+)\s*', e).group(1), 0) for e in m.group(1).split(';'))


def main():
    bad = []
    pages = {}
    for dp, _, fns in os.walk(os.path.join(ROOT, 'trail')):
        for fn in fns:
            if fn.endswith('.html'):
                pages[os.path.join(dp, fn)] = None
    pages[os.path.join(ROOT, 'index.html')] = None
    for p in pages:
        pg = Page()
        pg.feed(read(p))
        pages[p] = pg
    id_cache = {p: pg.ids for p, pg in pages.items()}

    def ids_of(path):
        if path not in id_cache:
            pg = Page()
            pg.feed(read(path))
            id_cache[path] = pg.ids
        return id_cache[path]

    # links
    nlinks = next_ = 0
    for p, pg in pages.items():
        for href in pg.links:
            u = urlsplit(href)
            if u.scheme in ('http', 'https', 'mailto', 'data'):
                next_ += 1
                continue
            nlinks += 1
            target = p if not u.path else os.path.normpath(os.path.join(os.path.dirname(p), unquote(u.path)))
            if u.path.endswith('/') or os.path.isdir(target):
                target = os.path.join(target, 'index.html')
            if not target.startswith(ROOT + os.sep) or not os.path.isfile(target):
                bad.append(f'{rel(p)}: link {href} has no target')
                continue
            if u.fragment and target.endswith('.html') and unquote(u.fragment) not in ids_of(target):
                bad.append(f'{rel(p)}: link {href}: no id "{u.fragment}" in {rel(target)}')

    # README.md mirrors index.html: its relative links into trail/ must resolve too
    readme = os.path.join(ROOT, 'README.md')
    for href in re.findall(r'\]\(([^)\s]+)\)', read(readme)):
        u = urlsplit(href)
        if u.scheme or not u.path.startswith('trail/'):
            continue
        nlinks += 1
        target = os.path.normpath(os.path.join(ROOT, unquote(u.path)))
        if u.path.endswith('/'):
            target = os.path.join(target, 'index.html')
        if not os.path.isfile(target):
            bad.append(f'README.md: link {href} has no target')
        elif u.fragment and unquote(u.fragment) not in ids_of(target):
            bad.append(f'README.md: link {href}: no id "{u.fragment}" in {rel(target)}')

    claims = json.loads(read(os.path.join(ROOT, 'claims.json')))['chain_nov']
    att_cache, file_cache = {}, {}

    def attest(path):
        if path not in att_cache:
            att_cache[path] = json.loads(read(os.path.join(ROOT, path)))
        return att_cache[path]

    def lines(path):
        if path not in file_cache:
            file_cache[path] = read(os.path.join(ROOT, path)).split('\n')
        return file_cache[path]

    receipt_by_attest = {}
    for row in claims['claims']:
        for rc in row['receipts']:
            receipt_by_attest[rel(os.path.join(BUBBLE, rc['attest_file']))] = rc
    modules = {}
    index_text = norm(html.unescape(re.sub(r'<[^>]+>', ' ', read(os.path.join(ROOT, 'index.html')))))
    counts = dict(statements=0, proof_lines=0, receipt_entries=0, byte_ranges=0, hex_views=0, hex_bytes=0,
                  source_lines=0, quotes=0)

    def module(path):
        if path not in modules:
            b = read(os.path.join(ROOT, path), 'rb')
            modules[path] = (b, bodies(b))
        return modules[path]

    for p, pg in pages.items():
        here = rel(p)
        for it in pg.items:
            a, text, tag = it['a'], ''.join(it['text']), it['tag']
            try:
                if tag == 'pre' and 'data-spec' in a and 'data-lines' in a and a.get('data-kind') == 'definition':
                    counts['statements'] += 1
                    s0, s1 = map(int, a['data-lines'].split('-'))
                    sl = lines(a['data-spec'])
                    name = a['data-name']
                    if text != '\n'.join(sl[s0 - 1:s1]) or sl[s0 - 1].strip() != f'definition {name}':
                        bad.append(f'{here}: definition {name} differs from {a["data-spec"]} lines {s0}-{s1}')
                    ends = [k for k in range(s0, len(sl) + 1) if sl[k - 1].rstrip().endswith('`;;')]
                    if not ends or ends[0] != s1:
                        bad.append(f'{here}: {name}: the spec block does not end at line {s1}')
                    shas = {rc['spec_sha256'] for rc in receipt_by_attest.values()
                            if os.path.normpath('proof-tree/' + rc['spec_file']) == os.path.normpath(a['data-spec'])}
                    if hashlib.sha256('\n'.join(sl).encode()).hexdigest() not in shas or not shas:
                        bad.append(f'{here}: {a["data-spec"]} is not a spec a receipt locks')
                elif tag == 'pre' and 'data-spec' in a and 'data-lines' in a:
                    counts['statements'] += 1
                    s0, s1 = map(int, a['data-lines'].split('-'))
                    sl = lines(a['data-spec'])
                    name = a['data-name']
                    if text != '\n'.join(sl[s0 - 1:s1]):
                        bad.append(f'{here}: statement of {name} differs from {a["data-spec"]} lines {s0}-{s1}')
                    if sl[s0 - 1].strip() != f'theorem {name}':
                        bad.append(f'{here}: {a["data-spec"]} line {s0} does not start theorem {name}')
                    ends = [k for k in range(s0, len(sl) + 1) if sl[k - 1].rstrip().endswith('`;;')]
                    if not ends or ends[0] != s1:
                        bad.append(f'{here}: {name}: the spec block does not end at line {s1}')
                    rcs = [rc for rc in receipt_by_attest.values() if name in rc['theorems']
                           and os.path.normpath('proof-tree/' + rc['spec_file']) == os.path.normpath(a['data-spec'])]
                    if not rcs:
                        bad.append(f'{here}: no receipt proves {name} against {a["data-spec"]}')
                    elif hashlib.sha256('\n'.join(sl).encode()).hexdigest() != rcs[0]['spec_sha256']:
                        bad.append(f'{here}: {a["data-spec"]} is not the spec the receipt locks')
                elif 'data-src' in a and 'data-line' in a and tag == 'a':
                    counts['proof_lines'] += 1
                    name, ln = a['data-name'], int(a['data-line'])
                    line = lines(a['data-src'])[ln - 1]
                    if not re.search(r'\b%s\b' % re.escape(name), line):
                        bad.append(f'{here}: {a["data-src"]} line {ln} does not name {name}')
                    if not a['href'].endswith(f'#L{ln}'):
                        bad.append(f'{here}: proof link for {name} does not point at line {ln}')
                    tgt = os.path.normpath(os.path.join(os.path.dirname(p), a['href'].split('#')[0]))
                    srcs = [x['a'].get('data-src') for x in pages[tgt].items if x['tag'] == 'div' and
                            'data-src' in x['a']] if tgt in pages else []
                    if srcs != [a['data-src']]:
                        bad.append(f'{here}: proof link for {name} goes to a page that does not render {a["data-src"]}')
                    att = attest(a['data-attest'])
                    b = [x for x in att['verdict']['bindings'] if x['name'] == name]
                    rc = receipt_by_attest[a['data-attest']]
                    if not b:
                        bad.append(f'{here}: {name} is not a binding of {a["data-attest"]}')
                    elif a['data-how'] == 'receipt':
                        if b[0].get('line') != ln or os.path.normpath('proof-tree/' + rc['source_file']) != \
                                os.path.normpath(a['data-src']):
                            bad.append(f'{here}: {name}: the receipt records another line or file')
                    elif a['data-how'] in ('search', 'accept'):
                        if not re.match(r'\s*let\s+(rec\s+)?%s\b' % re.escape(name), line):
                            bad.append(f'{here}: {name}: {a["data-src"]} line {ln} is not a let binding of it')
                        if a['data-how'] == 'search' and b[0].get('line') is not None:
                            bad.append(f'{here}: {name}: the receipt records a line, so no search was needed')
                        if a['data-how'] == 'accept':
                            src = lines('proof-tree/' + rc['source_file'])
                            r0 = b[0].get('line') or 0
                            j = r0 - 1
                            while 0 <= j < len(src) and not src[j].rstrip().endswith(';;'):
                                j += 1
                            if not r0 or not re.search(r'ACCEPT_TAC\s+%s\b' % re.escape(name), '\n'.join(src[r0 - 1:j + 1])):
                                bad.append(f'{here}: {name}: the recorded proof line does not close it with ACCEPT_TAC')
                        clo = json.loads(read(os.path.join(BUBBLE, 'vortex/chain-nov/evidence/closures',
                                                           rc['case'] + '.closure.json')))
                        shas = {r['sha256'] for r in clo['records']} | {clo['entrypoint']['sha256']}
                        if hashlib.sha256('\n'.join(lines(a['data-src'])).encode()).hexdigest() not in shas:
                            bad.append(f'{here}: {name}: {a["data-src"]} is not a file the run loaded')
                    else:
                        bad.append(f'{here}: {name}: unknown data-how')
                elif tag == 'span' and 'data-attest' in a and 'data-status' in a:
                    counts['receipt_entries'] += 1
                    att, name = attest(a['data-attest']), a['data-name']
                    b = [x for x in att['verdict']['bindings'] if x['name'] == name]
                    if att['verdict']['verdict'] != 'passed' or not b or b[0]['status'] != a['data-status'] \
                            or a['data-status'] != 'proved' or \
                            att['verdict']['spec']['bindings'].get(name) != a['data-spec-status'] or \
                            a['data-spec-status'] != 'matched' or att['verdict']['new_axioms'] != 0:
                        bad.append(f'{here}: receipt entry for {name} is not what {a["data-attest"]} says')
                    want = (f'{b[0]["status"] if b else "?"} ({(b[0].get("detail") or "") if b else ""}); statement '
                            f'against the frozen spec: {att["verdict"]["spec"]["bindings"].get(name)}')
                    if text != want:
                        bad.append(f'{here}: receipt entry for {name} shows "{text[:80]}", the receipt says "{want[:80]}"')
                elif tag == 'span' and 'data-pin' in a:
                    counts['receipt_entries'] += 1
                    pins = attest(a['data-attest'])['verdict']['spec'].get('pins') or {}
                    if pins.get(a['data-pin']) != a['data-pin-status'] or text != a['data-pin-status']:
                        bad.append(f'{here}: pin status of {a["data-pin"]} is not what the receipt says')
                elif tag == 'pre' and a.get('data-line') == 'verdict':
                    counts['receipt_entries'] += 1
                    v = attest(a['data-attest'])['verdict']
                    if text != v['line'] or not text.startswith('PASSED ') or v['verdict'] != 'passed':
                        bad.append(f'{here}: PASSED line differs from {a["data-attest"]}')
                elif tag == 'span' and 'data-def' in a:
                    counts['byte_ranges'] += 1
                    b, bod = module(a['data-module'])
                    s0, s1 = int(a['data-start']), int(a['data-end'])
                    sl = lines(a['data-spec'])
                    k = next(i for i, l in enumerate(sl) if l.strip() == f'definition {a["data-def"]}')
                    j = next(i for i in range(k, len(sl)) if sl[i].rstrip().endswith('`;;'))
                    m = re.search(r'=\s*\[(.*)\]\s*`;;\s*$', '\n'.join(sl[k:j + 1]), re.S)
                    want = bytes(int(re.fullmatch(r'\s*word\s+(\S+)\s*', e).group(1), 0) for e in m.group(1).split(';'))
                    if (s0, s1) not in bod:
                        bad.append(f'{here}: [{s0}, {s1}) is not a function body of {a["data-module"]}')
                    if b[s0:s1] != want:
                        bad.append(f'{here}: {a["data-def"]} in {a["data-spec"]} differs from bytes [{s0}, {s1})')
                    if text != f'[{s0}, {s1})':
                        bad.append(f'{here}: shown range for {a["data-def"]} differs from its attributes')
                elif tag == 'pre' and 'data-module' in a and 'data-start' in a:
                    counts['hex_views'] += 1
                    b, bod = module(a['data-module'])
                    s0, s1 = int(a['data-start']), int(a['data-end'])
                    got = {}
                    for ln in text.split('\n'):
                        off = int(ln[:8], 16)
                        rest = ln[10:]
                        for c in range(16):
                            pos = 3 * c + (1 if c >= 8 else 0)
                            cell = rest[pos:pos + 2]
                            if cell.strip():
                                got[off + c] = int(cell, 16)
                    if sorted(got) != list(range(s0, s1)) or any(b[i] != v for i, v in got.items()):
                        bad.append(f'{here}: hex view [{s0}, {s1}) differs from {a["data-module"]}')
                    if (s0, s1) not in bod:
                        bad.append(f'{here}: hex view [{s0}, {s1}) is not a function body')
                    counts['hex_bytes'] += len(got)
                elif 'data-sha256' in a:
                    b, _ = module(a['data-module'])
                    h = hashlib.sha256(b).hexdigest()
                    if h != a['data-sha256'] or text != h:
                        bad.append(f'{here}: shown SHA-256 of {a["data-module"]} is wrong')
                    if a['data-module'] == 'module/vortex_a1.wasm' and h != claims['module_sha256']:
                        bad.append(f'{here}: vortex_a1.wasm is not the module claims.json names')
                elif tag == 'div' and 'data-src' in a:
                    want = lines(a['data-src'])
                    if want and want[-1] == '':
                        want = want[:-1]
                    got = [x for x in pg.items if x['tag'] == 'div' and re.fullmatch(r'L\d+', x['a'].get('id', ''))]
                    if len(got) != len(want):
                        bad.append(f'{here}: renders {len(got)} lines of {a["data-src"]}, which has {len(want)}')
                    for k, (x, w) in enumerate(zip(got, want), 1):
                        if x['a']['id'] != f'L{k}' or ''.join(x['text']) != w:
                            bad.append(f'{here}: line {k} differs from {a["data-src"]}')
                            break
                    counts['source_lines'] += len(got)
                elif 'data-from' in a:
                    counts['quotes'] += 1
                    src = a['data-from']
                    if src == 'index.html':
                        if norm(text) not in index_text:
                            bad.append(f'{here}: quoted sentence not found in index.html: {text[:60]}')
                    elif src == 'claims.json':
                        row = [r for r in claims['claims'] if r['claim'] == a.get('data-claim')]
                        if not row or text != row[0]['title']:
                            bad.append(f'{here}: quoted label is not the title of {a.get("data-claim")} in claims.json')
                    elif src == 'replay/README.md':
                        if text not in read(os.path.join(ROOT, src)):
                            bad.append(f'{here}: quoted text not found in replay/README.md')
                    elif text != read(os.path.join(ROOT, src)).rstrip():
                        bad.append(f'{here}: quotation differs from {src}')
            except Exception as e:  # malformed attribute or missing file: a problem, not a crash
                bad.append(f'{here}: {tag} {sorted(a)[:3]}: {type(e).__name__}: {e}')

    # the main page: statements quoted in README.md, and the clause-by-clause readings in both files
    def clause_problems(where, name, stmt, codes):
        out, hay = [], norm(stmt)
        if not codes:
            out.append(f'{where}: no clauses shown for {name}')
        for c in codes:
            pos = 0
            for piece in [norm(x) for x in c.split('\u2026') if norm(x)]:
                k = hay.find(piece, pos)
                if k < 0:
                    out.append(f'{where}: clause piece not in {name} (in order): {piece[:60]}')
                    break
                pos = k + len(piece)
        return out

    ih = read(os.path.join(ROOT, 'index.html'))
    for name, body in re.findall(r'<ul class="clauses" data-clauses="([^"]+)">(.*?)</ul>', ih, re.S):
        m = re.search(r'<pre class="stmt"[^>]*data-name="%s"[^>]*>(.*?)</pre>' % re.escape(name), ih, re.S)
        codes = [html.unescape(x) for x in re.findall(r'<li><code>(.*?)</code>', body, re.S)]
        counts['clauses'] = counts.get('clauses', 0) + len(codes)
        bad += clause_problems('index.html', name, html.unescape(m.group(1)) if m else '', codes) if m else \
            [f'index.html: clauses for {name}, but no statement of it on the page']
    rd_md = read(readme)
    shown = {}
    for kind, path, s0, s1, name, text in re.findall(
            r'<!-- (theorem|definition) (\S+) (\d+)-(\d+) (\S+) -->\n```\n(.*?)\n```', rd_md, re.S):
        sl = lines(path)
        shown[name] = text
        if text != '\n'.join(sl[int(s0) - 1:int(s1)]) or sl[int(s0) - 1].strip() != f'{kind} {name}':
            bad.append(f'README.md: {kind} {name} differs from {path} lines {s0}-{s1}')
    for name, body in re.findall(r'<!-- clauses (\S+) -->\n((?:(?:- |  ).*\n)+)', rd_md):
        codes = re.findall(r'^- `([^`]+)`', body, re.M)
        bad += clause_problems('README.md', name, shown.get(name, ''), codes)
    if '<ul class="clauses"' in ih and not shown:
        bad.append('README.md: no quoted statement, but index.html has one')

    # README.md and index.html: the same links (label, target) in order, and the same intervals
    def md_links(md):
        md = re.sub(r'<!--.*?-->', '', md, flags=re.S)
        code = [(m.start(), m.end()) for m in re.finditer(r'`[^`\n]+`', md)]
        incode = lambda i: any(a <= i < b for a, b in code)
        out = []
        for m in re.finditer(r'\]\(([^)\s]+)\)', md):
            if incode(m.start()):
                continue
            depth, i = 1, m.start() - 1
            while i >= 0 and depth:
                if not incode(i):
                    depth += {']': 1, '[': -1}.get(md[i], 0)
                i -= 1
            if depth or (i >= 0 and md[i] == '!') or md[i + 2:i + 3] == '!':
                continue  # an image, or the image link around it
            label = re.sub(r'`([^`]*)`', r'\1', md[i + 2:m.start()])
            out.append((norm(re.sub(r'\*+', '', label)), m.group(1)))
        return out

    def html_links(h):
        h = h.split('<body>', 1)[-1]
        return [(norm(html.unescape(re.sub(r'<[^>]+>', '', lab))), html.unescape(href))
                for attrs, href, lab in re.findall(r'<a( class="[^"]*")? href="([^"]*)">(.*?)</a>', h, re.S)
                if not attrs]

    def intervals(t):
        return sorted(re.findall(r'\[\d[\d,]*, \d[\d,]*\)', t))
    ih0 = read(os.path.join(ROOT, 'index.html'))
    ml, hl = md_links(read(readme)), html_links(ih0)
    counts['page_links'] = len(ml)
    if ml != hl:
        k = next((i for i, (x, y) in enumerate(zip(ml, hl)) if x != y), min(len(ml), len(hl)))
        bad.append(f'index.html: link {k + 1} differs from README.md: {hl[k] if k < len(hl) else None} vs '
                   f'{ml[k] if k < len(ml) else None} ({len(hl)} links vs {len(ml)})')
    mi = intervals(re.sub(r'<!--.*?-->', '', read(readme), flags=re.S))
    hi = intervals(html.unescape(re.sub(r'<[^>]+>', '', ih0.split('<body>', 1)[-1])))
    counts['intervals'] = len(mi)
    if mi != hi:
        bad.append(f'index.html shows intervals {sorted(set(hi) ^ set(mi)) or "a different number of times"} '
                   f'differently from README.md ({len(hi)} vs {len(mi)})')

    # unique ids, theorem cards and the links to them
    cards = {}  # page -> {id: (name, attest)}
    for p, pg in pages.items():
        for d in sorted(set(pg.dup_ids)):
            bad.append(f'{rel(p)}: id "{d}" is used more than once')
        raw = read(p)
        cs = {}
        for cid, body in re.findall(r'<article class="thm" id="([^"]+)">(.*?)</article>', raw, re.S):
            sn = re.findall(r'<pre class="stmt" [^>]*data-name="([^"]+)"', body)
            rn = re.findall(r'<span data-attest="([^"]+)" data-name="([^"]+)" data-status=', body)
            if len(sn) != 1 or len(rn) != 1 or sn[0] != rn[0][1]:
                bad.append(f'{rel(p)}: card {cid}: its statement and receipt entry do not name one theorem')
                continue
            for st in ('stmt', 'proof', 'rcpt', 'bytes'):
                if f'id="{cid}-{st}"' not in body:
                    bad.append(f'{rel(p)}: card {cid} has no step id {cid}-{st}')
            cs[cid] = (sn[0], rn[0][0])
        cards[p] = cs
    case_of = {a: rc['case'] for a, rc in receipt_by_attest.items()}
    nlinked = 0
    for p, pg in pages.items():
        raw = read(p)
        shaped = 0
        for m in re.finditer(r'<a href="([^"]*)"((?: data-[\w-]+="[^"]*")*)><code>([^<]+)</code></a>', raw):
            href, attrs, label = html.unescape(m.group(1)), m.group(2), html.unescape(m.group(3))
            rcv = re.search(r'data-receipt="([^"]*)"', attrs)
            shaped += 1 if rcv else 0
            u = urlsplit(href)
            if u.scheme or u.netloc:
                if rcv:
                    bad.append(f'{rel(p)}: link {href} names receipt {rcv.group(1)} but leaves the repository')
                continue
            tgt = p if not u.path else os.path.normpath(os.path.join(os.path.dirname(p), unquote(u.path)))
            cs = cards.get(tgt, {})
            frag = unquote(u.fragment)
            if rcv:
                # a receipt-qualified theorem link: exactly the root of the card of (label, receipt) on its target page
                nlinked += 1
                want = [cid for cid, (n, a) in cs.items() if n == label and case_of.get(a) == rcv.group(1)]
                if len(want) != 1 or frag != want[0]:
                    got = cs.get(frag)
                    bad.append(f'{rel(p)}: link {href} labelled {label} for receipt {rcv.group(1)} goes to '
                               + (f'a card of {got[0]} (receipt {case_of.get(got[1])})' if got else
                                  f'"#{frag}", not a card root') + f'; its card is '
                               + (f'#{want[0]}' if len(want) == 1 else f'not on {rel(tgt)} ({len(want)} found)'))
                continue
            card = frag if frag in cs else next((c for c in cs for st in ('stmt', 'proof', 'rcpt', 'bytes')
                                                 if frag == f'{c}-{st}'), None)
            if card is None:
                continue
            nlinked += 1
            name, att = cs[card]
            if name != label:
                bad.append(f'{rel(p)}: link {href} labelled {label} goes to the card of {name}')
            if sum(1 for n, _ in cs.values() if n == name) > 1:
                bad.append(f'{rel(p)}: link {href}: {rel(tgt)} has several cards of {name}, but the link names no receipt')
        if shaped != len(re.findall(r'<a\b[^>]*\bdata-receipt=', raw)):
            bad.append(f'{rel(p)}: a link with data-receipt is not of the form <a href=".." data-receipt=".."><code>NAME</code></a>')
    counts['card_links'] = nlinked

    # each card's receipt step: after the (checked) receipt entry, exactly the sentence its attestation and
    # cold-replay record give: "Receipt CASE: PASSED FILE, N new axioms; cold replay: OUTCOME." (+ the re-run link)
    cold_cache = {}

    def cold_rec(path):
        if path not in cold_cache:
            cold_cache[path] = json.loads(read(os.path.join(ROOT, path)))
        return cold_cache[path]

    cold_of = {a: rel(os.path.join(BUBBLE, rc['cold']['file'])) for a, rc in receipt_by_attest.items()}

    def cold_problems(where, att_path):
        v, rc, cp = attest(att_path)['verdict'], receipt_by_attest[att_path], cold_of[att_path]
        c = cold_rec(cp)
        if c.get('leaf') != rc['case'] or c.get('outcome') != 'reproduced' or c.get('exit') != 0 or \
                c.get('receipt') != v.get('receipt') or c.get('headline') != rc['cold']['headline'] or \
                rc['cold']['outcome'] != c.get('outcome') or rc['line'] != v.get('line'):
            return [f'{where}: {cp} is not a reproduced cold replay of the receipt {rc["case"]}, as claims.json says']
        return []

    receipt_step = re.compile(
        r'<span data-attest="([^"]+)" data-name="([^"]+)" data-status="[^"]*" data-spec-status="[^"]*"><span class="ok">'
        r'[^<]*</span> \([^<]*\); statement against the frozen spec: <span class="ok">[^<]*</span></span>(.*)', re.S)
    summary = re.compile(r'\. Receipt <a href="#r-([^"]+)"><code>([^<]+)</code></a>: (\S+) (\S+), (\d+) new axioms; '
                         r'cold replay: <a href="([^"]+)">([^<]+)</a>\.( You can <a href="#rerun">re-run this proof '
                         r'yourself</a>\.)?')
    nsum = 0
    for p, cs in cards.items():
        raw = read(p)
        for cid, (name, att) in cs.items():
            steps = re.findall(r'<li class="step" id="%s-rcpt"><b>Receipt</b> (.*?)</li>' % re.escape(cid), raw, re.S)
            m = receipt_step.fullmatch(steps[0]) if len(steps) == 1 else None
            if not m or m.group(1) != att or m.group(2) != name:
                bad.append(f'{rel(p)}: card {cid}: its receipt step is not one receipt entry followed by the receipt summary')
                continue
            s = summary.fullmatch(m.group(3))
            if not s:
                bad.append(f'{rel(p)}: card {cid}: receipt summary {norm(re.sub("<[^>]+>", "", m.group(3)))[:90]!r} '
                           'is not "Receipt CASE: PASSED FILE, N new axioms; cold replay: OUTCOME."')
                continue
            nsum += 1
            v, rc = attest(att)['verdict'], receipt_by_attest[att]
            cp = cold_of[att]
            href = os.path.normpath(os.path.join(os.path.dirname(p), unquote(html.unescape(s.group(6)))))
            want = (rc['case'], rc['case'], 'PASSED', v.get('source_name'), str(v.get('new_axioms')), 'reproduced')
            got = (s.group(1), html.unescape(s.group(2)), s.group(3), html.unescape(s.group(4)), s.group(5),
                   html.unescape(s.group(7)))
            if got != want or v.get('verdict') != 'passed' or v.get('new_axioms') != 0 or \
                    not v.get('line', '').startswith(f'PASSED {v.get("source_name")}:') or \
                    href != os.path.join(ROOT, cp) or bool(s.group(8)) != (rc['case'] == 'chain_c5_leaves_final'):
                bad.append(f'{rel(p)}: card {cid}: receipt summary shows {got} with cold link {rel(href)}; '
                           f'{att} and {cp} say {want} with cold link {cp}')
            bad += cold_problems(f'{rel(p)}: card {cid}', att)
    counts['summaries'] = nsum

    # receipt boxes: proof-file and spec hashes, the cold-replay headline and record, the check-rung result
    box_anchors = {}
    for p in pages:
        ba = BoxAnchors()
        ba.feed(read(p))
        box_anchors[p] = ba.boxes
    def short(h):
        return h[:8] + '…' + h[-6:]
    for p in pages:
        raw = read(p)
        for case, body in re.findall(r'<div class="box" id="r-([^"]+)">(.*?)</div>', raw, re.S):
            atts = [a for a, rc in receipt_by_attest.items() if rc['case'] == case]
            if len(atts) != 1:
                bad.append(f'{rel(p)}: receipt box r-{case} names no receipt of claims.json')
                continue
            att = atts[0]
            rc, cp = receipt_by_attest[att], cold_of[att]
            hrefs = re.search(r'<p>Proof file <a href="([^"]*)"><code>[^<]+</code></a> \(SHA-256 <code>[^<]+</code>\), '
                              r'frozen spec <a href="([^"]*)">', body)
            m = re.search(r'<p>Proof file <a href="[^"]*"><code>([^<]+)</code></a> \(SHA-256 <code>([^<]+)</code>\), '
                          r'frozen spec <a href="[^"]*"><code>([^<]+)</code></a> \(SHA-256 <code>([^<]+)</code>\)\. '
                          r'Cold replay: (.*?)\. Check-rung: (.*?)\.</p>', body, re.S)
            links = re.findall(r'<a href="([^"]*)">cold replay record</a>', body)
            if not m:
                bad.append(f'{rel(p)}: receipt box r-{case}: no proof-file, spec, cold-replay and check-rung line')
                continue
            anchors = box_anchors[p].get(case, [])
            ev_dir = os.path.dirname(os.path.join(ROOT, att))
            stem = os.path.basename(att)[:-len('.attest.json')]
            want_ev = {'attest summary': os.path.join(ROOT, att),
                       'inspect listing': os.path.join(ev_dir, stem + '.inspect.txt'),
                       'cold replay record': os.path.join(ROOT, cp),
                       'closure inventory': os.path.normpath(os.path.join(ev_dir, '..', 'closures', stem + '.closure.json')),
                       'check-rung output': os.path.normpath(os.path.join(ev_dir, '..', 'check-rung', stem + '.check-rung.out'))}
            want_src = os.path.normpath('proof-tree/' + rc['source_file'])
            want_spec = os.path.normpath(os.path.join(ROOT, 'proof-tree', rc['spec_file']))
            n_src = n_spec = 0
            seen_ev = {}
            for hx, text in anchors:
                u = urlsplit(hx)
                if u.scheme or u.netloc:
                    continue                                   # spec line links on GitHub; checked with the definitions
                tg = os.path.normpath(os.path.join(os.path.dirname(p), unquote(u.path))) if u.path else p
                if '/src/' in '/' + u.path:                    # a rendered proof source: the receipt's own proof file
                    n_src += 1
                    ds = [x['a'].get('data-src') for x in pages[tg].items if x['tag'] == 'div' and
                          'data-src' in x['a']] if tg in pages and pages[tg] else []
                    if u.fragment or text != want_src or [os.path.normpath(x) for x in ds] != [want_src]:
                        bad.append(f'{rel(p)}: receipt box r-{case}: link {hx} ("{text}") does not open the rendered '
                                   f'page of {want_src} under that label')
                elif tg.endswith('.spec'):                     # the frozen spec: the receipt's own spec file
                    n_spec += 1
                    if u.fragment or tg != want_spec or text != os.path.relpath(want_spec, ROOT):
                        bad.append(f'{rel(p)}: receipt box r-{case}: spec link {hx} ("{text}") does not open '
                                   f'proof-tree/{rc["spec_file"]} under that label')
                elif text in want_ev:                          # evidence links: once each, this receipt's own file
                    seen_ev[text] = seen_ev.get(text, 0) + 1
                    if u.fragment or tg != os.path.normpath(want_ev[text]) or seen_ev[text] > 1:
                        bad.append(f'{rel(p)}: receipt box r-{case}: "{text}" link {hx} is not the single link to '
                                   f'{rel(want_ev[text])}')
                elif os.path.dirname(tg) == os.path.join(ROOT, 'trail', 'bytes'):
                    continue                                   # function byte links; checked with the definitions
                else:
                    bad.append(f'{rel(p)}: receipt box r-{case}: unexpected link {hx} ("{text}")')
            if n_src != 1 or n_spec != 1:
                bad.append(f'{rel(p)}: receipt box r-{case}: {n_src} proof-file and {n_spec} frozen-spec links; '
                           f'exactly one of each is allowed')
            src, ssha, spec, specsha, cold, rung = (html.unescape(x) for x in m.groups())
            ph, sh = (html.unescape(x) for x in hrefs.groups())
            pu, su = urlsplit(ph), urlsplit(sh)
            ptgt = os.path.normpath(os.path.join(os.path.dirname(p), unquote(pu.path)))
            psrcs = [x['a'].get('data-src') for x in pages[ptgt].items if x['tag'] == 'div' and
                     'data-src' in x['a']] if ptgt in pages and pages[ptgt] else []
            if pu.scheme or pu.netloc or pu.fragment or \
                    [os.path.normpath(x) for x in psrcs] != [os.path.normpath('proof-tree/' + rc['source_file'])]:
                bad.append(f'{rel(p)}: receipt box r-{case}: proof link {ph} does not open the rendered page of '
                           f'proof-tree/{rc["source_file"]}')
            stgt = os.path.normpath(os.path.join(os.path.dirname(p), unquote(su.path)))
            if su.scheme or su.netloc or su.fragment or stgt != os.path.normpath(os.path.join(ROOT, 'proof-tree', rc['spec_file'])):
                bad.append(f'{rel(p)}: receipt box r-{case}: spec link {sh} does not open proof-tree/{rc["spec_file"]}')
            fsha = hashlib.sha256(read(os.path.join(ROOT, src), 'rb')).hexdigest() \
                if os.path.isfile(os.path.join(ROOT, src)) else ''
            psha = hashlib.sha256(read(os.path.join(ROOT, spec), 'rb')).hexdigest() \
                if os.path.isfile(os.path.join(ROOT, spec)) else ''
            if os.path.normpath(src) != os.path.normpath('proof-tree/' + rc['source_file']) or \
                    ssha != short(rc['source_sha256']) or fsha != rc['source_sha256']:
                bad.append(f'{rel(p)}: receipt box r-{case}: proof file {src} (SHA-256 {ssha}) is not the receipt\'s')
            if os.path.normpath(spec) != os.path.normpath('proof-tree/' + rc['spec_file']) or \
                    specsha != short(rc['spec_sha256']) or psha != rc['spec_sha256']:
                bad.append(f'{rel(p)}: receipt box r-{case}: frozen spec {spec} (SHA-256 {specsha}) is not the receipt\'s')
            if cold != cold_rec(cp).get('headline') or rung != rc['check_rung']['result'] or \
                    [os.path.normpath(os.path.join(os.path.dirname(p), unquote(html.unescape(x)))) for x in links] != \
                    [os.path.join(ROOT, cp)]:
                bad.append(f'{rel(p)}: receipt box r-{case}: cold replay, its record link or the check-rung result '
                           f'differs from {cp} and claims.json')
            bad += cold_problems(f'{rel(p)}: receipt box r-{case}', att)
            counts['receipt_boxes'] = counts.get('receipt_boxes', 0) + 1

    # byte pages: function sections and the function table against the parsed module
    bpage_mod = {}
    for p in pages:
        if os.path.dirname(p) != os.path.join(ROOT, 'trail', 'bytes'):
            continue
        raw = read(p)
        mm = set(re.findall(r'data-module="([^"]+)" data-sha256=', raw))
        if len(mm) != 1:
            bad.append(f'{rel(p)}: names no single module')
            continue
        mpath = mm.pop()
        bpage_mod[os.path.splitext(os.path.basename(p))[0]] = mpath
        try:
            fs = funcs(read(os.path.join(ROOT, mpath), 'rb'))
        except Exception as e:
            bad.append(f'{rel(p)}: cannot parse {mpath}: {e}')
            continue
        base = os.path.basename(mpath)
        secs = re.findall(r'<section class="fn" id="f(\d+)">\n<h2>function (\d+)(?: \(export <code>[^<]*</code>\))?</h2>\n'
                          r'<p>Body: bytes <strong>\[(\d+), (\d+)\)</strong> of <code>([^<]+)</code>, (\d+) bytes \(its '
                          r'code-section entry starts at byte (\d+) with the body size, (\d+) bytes?\)(.*?)</section>',
                          raw, re.S)
        if len(secs) != raw.count('<section class="fn"'):
            bad.append(f'{rel(p)}: a function section has an unexpected heading or body line')
        for fid, fn, s0, s1, mb, ln, e0, k, rest in secs:
            fid, fn, s0, s1, ln, e0, k = map(int, (fid, fn, s0, s1, ln, e0, k))
            counts['byte_sections'] = counts.get('byte_sections', 0) + 1
            if fid != fn or fid not in fs or fs[fid] != (e0, s0, s1) or ln != s1 - s0 or k != s0 - e0 or mb != base:
                bad.append(f'{rel(p)}: section f{fid} shows function {fn}, body [{s0}, {s1}), {ln} bytes, entry {e0}, '
                           f'which is not function {fid} of {mpath} ({fs.get(fid)})')
            hx = re.findall(r'<pre class="hex" data-module="([^"]+)" data-start="(\d+)" data-end="(\d+)">', rest)
            if hx != [(mpath, str(s0), str(s1))]:
                bad.append(f'{rel(p)}: section f{fid}: hex view is not of its body')
        for fn, s0, s1, ln in re.findall(r'<tr><td>(?:<a href="#f\d+">)?(\d+)(?:</a>)?</td><td>[^<]*</td>'
                                          r'<td>\[(\d+), (\d+)\)</td><td>(\d+)</td><td>[^<]*</td></tr>', raw):
            fn, s0, s1, ln = map(int, (fn, s0, s1, ln))
            if fs.get(fn, (0, -1, -1))[1:] != (s0, s1) or ln != s1 - s0:
                bad.append(f'{rel(p)}: function table row {fn} shows [{s0}, {s1}), not its body')
        for fn in re.findall(r'<tr><td><a href="#f(\d+)">(\d+)</a>', raw):
            if fn[0] != fn[1]:
                bad.append(f'{rel(p)}: function table row {fn[1]} links to #f{fn[0]}')

    # links to byte pages: the function is the one whose body is the labelled definition's bytes
    spec_defs = {}
    for rc in receipt_by_attest.values():
        sp = os.path.normpath('proof-tree/' + rc['spec_file'])
        if sp not in spec_defs:
            sl = lines(sp)
            spec_defs[sp] = {}
            for l in sl:
                mm = re.fullmatch(r'\s*definition\s+(\w+)\s*', l)
                if mm:
                    try:
                        bb = def_bytes(sl, mm.group(1))
                    except Exception:
                        bb = None
                    if bb is not None:
                        spec_defs[sp][mm.group(1)] = bb
    any_def = {}
    for d in spec_defs.values():
        for n, bb in d.items():
            any_def.setdefault(n, set()).add(bb)
    mod_funcs = {}
    tok = re.compile(r'<a href="([^"]*?)bytes/(\w+)\.html#f(\d+)"[^>]*><code>([^<]+)</code></a>'
                     r'|<span data-def="([^"]+)" data-spec="([^"]+)" data-module="([^"]+)" data-start="(\d+)" '
                     r'data-end="(\d+)">')
    for p in pages:
        raw = read(p)
        last = None
        for m in tok.finditer(raw):
            if m.group(2):
                key, fn, label = m.group(2), int(m.group(3)), html.unescape(m.group(4))
                mpath = bpage_mod.get(key)
                if mpath is None:
                    continue
                if mpath not in mod_funcs:
                    mod_funcs[mpath] = funcs(read(os.path.join(ROOT, mpath), 'rb'))
                f = mod_funcs[mpath].get(fn)
                body = module(mpath)[0][f[1]:f[2]] if f else None
                if label in any_def:
                    counts['def_links'] = counts.get('def_links', 0) + 1
                    if body not in any_def[label]:
                        bad.append(f'{rel(p)}: link to {key} function {fn} is labelled {label}, whose bytes are '
                                   'another function\'s')
                last = (m.end(), key, fn, label, mpath, f)
            else:
                dname, dspec, dmod, s0, s1 = m.group(5), m.group(6), m.group(7), int(m.group(8)), int(m.group(9))
                if last is None:
                    bad.append(f'{rel(p)}: byte range of {dname} has no function link before it')
                    continue
                pos, key, fn, label, mpath, f = last
                between = re.sub(r'<code>([^<]*)</code>', r'\1', raw[pos:m.start()])
                ok = re.fullmatch(r' = (\S+) function (\d+)(?: \(export [^)]*\))? bytes ', between)
                if label != dname or mpath != dmod or not f or (f[1], f[2]) != (s0, s1) or not ok or \
                        ok.group(1) != os.path.basename(dmod) or int(ok.group(2)) != fn:
                    bad.append(f'{rel(p)}: byte range [{s0}, {s1}) of {dname} follows a link to {key} function {fn} '
                               f'labelled {label} ({between.strip()[:60]!r})')
                last = None

    # coverage
    for row in claims['claims']:
        pth = os.path.join(ROOT, 'trail', row['claim'].replace("'", 'p') + '.html')
        if pth not in pages:
            bad.append(f'no trail page for {row["claim"]}')
            continue
        ids = pages[pth].ids
        for rc in row['receipts']:
            if 'r-' + rc['case'] not in ids:
                bad.append(f'{rel(pth)}: no section for receipt {rc["case"]}')
            shared = os.path.join(ROOT, 'trail', f'receipt-{rc["case"]}.html')
            att = rel(os.path.join(BUBBLE, rc['attest_file']))
            for t in rc['theorems']:
                if (t, att) in cards[pth].values():
                    continue
                # a row that names its claimed theorems may leave the receipt's others to the receipt's shared page
                shc = [cid for cid, v in cards.get(shared, {}).items() if v == (t, att)]
                links = {u for u in pages[pth].links if shc and u == f'receipt-{rc["case"]}.html#{shc[0]}'}
                if not (row.get('claim_theorems') and t not in row['claim_theorems'] and links):
                    bad.append(f'{rel(pth)}: no card with a statement for {t} of receipt {rc["case"]}')
    print(f'{len(pages)} pages, {nlinks} relative links ({next_} external, not followed), '
          f'{counts["statements"]} statements, {counts["proof_lines"]} proof lines, '
          f'{counts["receipt_entries"]} receipt entries, {counts["byte_ranges"]} byte ranges, '
          f'{counts["hex_views"]} hex views ({counts["hex_bytes"]} bytes), {counts["source_lines"]} source lines, '
          f'{counts["quotes"]} quotations, {counts.get("clauses", 0)} clauses, {counts.get("card_links", 0)} card links, '
          f'{counts.get("page_links", 0)} README/index links, {counts.get("intervals", 0)} intervals, '
          f'{counts.get("def_links", 0)} definition links, {counts.get("byte_sections", 0)} byte-page sections, '
          f'{counts.get("summaries", 0)} card receipt summaries, {counts.get("receipt_boxes", 0)} receipt boxes; '
          f'{len(bad)} problems')
    for b in bad[:200]:
        print('  ' + b)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
