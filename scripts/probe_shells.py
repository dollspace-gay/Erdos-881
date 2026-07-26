#!/usr/bin/env python3
"""Shell stratification probe: greedily compute inclusion-maximal
rep-free sets (shells) on truncated models, iterating on the leftover
pool.  Reports shell sizes, depth profile, and the duty heights the
depth tax predicts (>= N0 + k/3 for depth-k+1 members)."""
import sys
sys.setrecursionlimit(100000)

def triples(A, m):
    As, Aset, out = sorted(A), set(A), []
    for x in As:
        if x > m: break
        for y in As:
            if x + y > m: break
            if (m - x - y) in Aset:
                out.append((x, y, m - x - y))
    return out

def free(S, tc):
    Ss = set(S)
    return all(any(Ss.isdisjoint(t) for t in ts) for ts in tc.values())

def max_free_shell(pool, tc):
    """greedy inclusion-maximal free subset of pool (ascending scan)"""
    S = []
    for b in sorted(pool):
        if free(S + [b], tc):
            S.append(b)
    return S

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

def run(name, A, Y, N0):
    Apos = [a for a in A if a > 0]
    tc = {m: t for m in range(N0, Y + 1) if (t := triples(A, m))}
    pool, shells = list(Apos), []
    while pool:
        S = max_free_shell(pool, tc)
        if not S: break
        shells.append(S)
        pool = [a for a in pool if a not in set(S)]
    sizes = [len(s) for s in shells]
    print(f"{name:>9} Y={Y:4d} |A+|={len(Apos):3d} shells={len(shells):3d} "
          f"sizes={sizes[:12]}{'...' if len(sizes)>12 else ''} leftover={len(pool)}")
    # duty height check for a few deep elements: min duty target over shell j
    if len(shells) >= 3:
        b = shells[-1][0]  # a deepest element
        heights = []
        for j, Qj in enumerate(shells[:-1]):
            QS = set(Qj) | {b}
            hs = [m for m, ts in tc.items() if all(not QS.isdisjoint(t) for t in ts)]
            heights.append(min(hs) if hs else None)
        print(f"          deepest b={b} depth={len(shells)} duty-heights(min per shell)={heights[:10]}")

for Y in (81, 162, 243):
    run("cantor", cantor(Y), Y, 9)
for Y in (80, 160, 240):
    run("greedyB2", greedy_b2(Y), Y, 9)
