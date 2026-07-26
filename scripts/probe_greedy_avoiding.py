#!/usr/bin/env python3
"""Can GREEDY (density-preserving) build self-avoiding families?
T self-avoiding: every subset-sum of T (arities 1..3 tested, in
window) has a triple rep avoiding T.  Greedy: scan A ascending,
add a if property survives.  Measure density of T vs A, and
completeness (which window targets are subset sums of T)."""
from itertools import combinations

def cantor(Y):
    out = []
    for n in range(Y + 1):
        m, ok = n, True
        while m:
            if m % 3 == 2: ok = False; break
            m //= 3
        if ok: out.append(n)
    return out

def greedy_b2(Y):
    A = [0, 1]
    for n in range(2, Y + 1):
        As = set(A)
        if not any((n - a) in As for a in A if a <= n):
            A.append(n)
    return A

def has_avoiding_triple(m, Aset, As, Tset):
    for x in As:
        if x > m: break
        if x in Tset: continue
        for y in As:
            if y < x: continue
            if x + y > m: break
            if y in Tset: continue
            z = m - x - y
            if z >= y and z in Aset and z not in Tset:
                return True
    return False

def run(name, A, Y, N0):
    Aset, As = set(A), sorted(A)
    T = []
    for a in As:
        if a == 0: continue
        T2 = T + [a]
        Tset = set(T2)
        ok = True
        # subset sums of arities 1..3 that land in window
        sums = set()
        for r in (1, 2, 3):
            for comb in combinations(T2[-12:], r):  # recent tail (older sums exceed window anyway)
                s0 = sum(comb)
                if N0 <= s0 <= Y: sums.add(s0)
        for m in sums:
            if not has_avoiding_triple(m, Aset, As, Tset):
                ok = False; break
        if ok:
            T = T2
    Tset = set(T)
    # completeness check: fraction of [N0, Y] that is a subset-sum of T (arity<=4)
    ssums = set()
    for r in (1, 2, 3, 4):
        for comb in combinations(T, r):
            s0 = sum(comb)
            if s0 <= Y: ssums.add(s0)
    cover = sum(1 for m in range(N0, Y + 1) if m in ssums)
    print(f"{name}: |A+|={len([a for a in A if a>0])} |T|={len(T)} "
          f"density={len(T)/max(1,len([a for a in A if a>0])):.2f} "
          f"subset-sum coverage of window: {cover}/{Y-N0+1}")
    print(f"   T sample: {T[:15]}")

run("cantor", cantor(400), 400, 9)
run("greedyB2", greedy_b2(400), 400, 9)
