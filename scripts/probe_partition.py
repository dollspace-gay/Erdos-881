#!/usr/bin/env python3
"""Finite diagnostic for partition."""

def greedy_b2(Y):
    A = [0, 1]
    for n in range(2, Y + 1):
        As = set(A)
        if not any((n - a) in As for a in A if a <= n):
            A.append(n)
    return A

def cantor(Y):
    out = []
    for n in range(Y + 1):
        m, ok = n, True
        while m:
            if m % 3 == 2: ok = False; break
            m //= 3
        if ok: out.append(n)
    return out

def coverage_holes(U, N0, Y):
    Us, Uset = sorted(U), set(U)
    holes = 0
    for n in range(N0, Y + 1):
        ok = False
        for x in Us:
            if 3 * x > n: break
            for y in Us:
                if y < x: continue
                if x + y > n: break
                z = n - x - y
                if z >= y and z in Uset:
                    ok = True; break
            if ok: break
        if not ok: holes += 1
    return holes

for name, A, Y in (("greedyB2", greedy_b2(4000), 4000),
                   ("cantor", cantor(2187), 2187)):
    Apos = [a for a in A if a > 0]
    N0 = 30
    print(f"{name}: |A+|={len(Apos)}")
    for k in (2, 3, 4, 6, 8):
        # structure-aware: keep a small full base, thin only the tail
        base = [a for a in Apos if a <= 60]
        tail = [a for a in Apos if a > 60]
        U = [0] + base + [a for i, a in enumerate(tail) if i % k == 0]
        h = coverage_holes(U, N0, Y)
        print(f"  base+every {k}th tail: |U|={len(U)} "
              f"holes={h}/{Y-N0+1}")
