#!/usr/bin/env python3
"""drop_exports.py IN.wasm OUT.wasm PREFIX: rewrite only the export section, dropping exports whose name starts with
PREFIX (the ve_* leaves); every other section, the code section included, is copied byte for byte."""
import sys
def leb(b, i):
    r = s = 0
    while True:
        x = b[i]; i += 1; r |= (x & 0x7f) << s; s += 7
        if x < 0x80: return r, i
def enc(n):
    o = bytearray()
    while True:
        x = n & 0x7f; n >>= 7
        if n: o.append(x | 0x80)
        else: o.append(x); return bytes(o)
b = open(sys.argv[1], 'rb').read(); out = bytearray(b[:8]); i = 8; pre = sys.argv[3].encode(); dropped = 0
while i < len(b):
    sid = b[i]; n, j = leb(b, i + 1); body = b[j:j + n]
    if sid == 7:
        cnt, k = leb(body, 0); keep = []
        for _ in range(cnt):
            s = k; l, k = leb(body, k); name = body[k:k + l]; k += l + 1; _, k = leb(body, k)
            if name.startswith(pre): dropped += 1
            else: keep.append(body[s:k])
        body = enc(len(keep)) + b''.join(keep)
    out += bytes([sid]) + enc(len(body)) + body; i = j + n
open(sys.argv[2], 'wb').write(out); print(f"dropped {dropped} exports")
