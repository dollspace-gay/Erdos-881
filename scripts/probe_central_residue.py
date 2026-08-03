#!/usr/bin/env python3
"""Finite diagnostic for central residue."""

def cantor(Y):
    out = []
    for n in range(Y + 1):
        m, ok = n, True
        while m:
            if m % 3 == 2: ok = False; break
            m //= 3
        if ok: out.append(n)
    return out

A = cantor(2187)
Aset = set(A)
tot = {'pad0': 0, 'diag': 0, 'odd': 0, 'gap': 0}
per_c = []
for c in A:
    if c <= 0 or 2 * c > 2187 + 700: continue
    kinds = set()
    n = 2 * c
    for x in A:
        if x > n: break
        for y in A:
            if y < x: continue
            if x + y > n: break
            z = n - x - y
            if z < y or z not in Aset: continue
            # classify by the (x,y) slot
            if z == 0 and x == y == c:
                k = 'pad0'
            elif x == y:
                k = 'diag'
            elif (x + y) % 2 == 1:
                k = 'odd'
            else:
                k = 'gap' if (x + y) // 2 not in Aset else 'BAD'
            kinds.add(k)
            tot[k] = tot.get(k, 0) + 1
    per_c.append((c, sorted(kinds)))
print("totals:", tot)
bad = [p for p in per_c if 'BAD' in p[1]]
print("centrality violations:", bad[:3] if bad else "none (midpoint-free confirmed)")
only_pad = [c for c, k in per_c if k == ['pad0']]
print(f"doubles with ONLY the 0-pad triple: {len(only_pad)}/{len(per_c)}")
print(f"sample fragile doubles: {only_pad[:10]}")
