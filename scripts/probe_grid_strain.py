#!/usr/bin/env python3
"""Finite diagnostic for grid strain."""

def cantor(Y):
    out = []
    for n in range(Y + 1):
        m, ok = n, True
        while m:
            if m % 3 == 2: ok = False; break
            m //= 3
        if ok: out.append(n)
    return out

def triples(Aset, m):
    As = sorted(a for a in Aset if a <= m)
    out = []
    for x in As:
        for y in As:
            if y < x: continue
            if x + y > m: break
            z = m - x - y
            if z >= y and z in Aset: out.append((x, y, z))
    return out

def obligations(A, Y, N0, pred, name):
    Aset = set(A)
    cnt = 0
    hi = 0
    for n in range(N0, Y + 1):
        ts = triples(Aset, n)
        if ts and all(any(pred(u) for u in t) for t in ts):
            cnt += 1; hi = n
    return f"{name}: {cnt} obligated targets (last {hi})"

Y, N0 = 1200, 9
worlds = {
  "two-scale": set(range(0, 40)) | set(range(36, Y, 36)),
  "cantor": set(cantor(Y)),
}
for wname, A in worlds.items():
    infodd = len([a for a in A if a % 2 == 1 and a > 100])
    inf3 = len([a for a in A if a % 3 == 0 and a > 100])
    print(f"{wname} (|A|={len(A)}, odd-tail={infodd}, 3div-tail={inf3}):")
    print("  ", obligations(A, Y, N0, lambda u: u % 2 == 1, "B_odd"))
    print("  ", obligations(A, Y, N0, lambda u: u % 3 == 0, "B_0mod3"))
