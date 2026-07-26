#!/usr/bin/env python3
"""Conflict-target placement probe: for each pair of shells (j,k),
find ALL targets m in window whose every rep meets Q_j ∪ Q_k.
Question: does the MINIMUM conflict target show placement
regularity (e.g. ~ min Q_k, ~ max(Q_j∪Q_k), ~ sum of mins)?"""

def triples(A, m):
    As, Aset, out = sorted(A), set(A), []
    for x in As:
        if x > m: break
        for y in As:
            if x + y > m: break
            if (m - x - y) in Aset:
                out.append((x, y, m - x - y))
    return out

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

def free(S, tc):
    Ss = set(S)
    return all(any(Ss.isdisjoint(t) for t in ts) for ts in tc.values())

def max_free_shell(pool, tc):
    S = []
    for b in sorted(pool):
        if free(S + [b], tc):
            S.append(b)
    return S

def run(name, A, Y, N0):
    Apos = [a for a in A if a > 0]
    tc = {m: t for m in range(N0, Y + 1) if (t := triples(A, m))}
    pool, shells = list(Apos), []
    while pool:
        S = max_free_shell(pool, tc)
        if not S: break
        shells.append(S)
        pool = [a for a in pool if a not in set(S)]
    print(f"{name} Y={Y} shells={[len(s) for s in shells]}")
    for j in range(len(shells)):
        for k in range(j + 1, len(shells)):
            U = set(shells[j]) | set(shells[k])
            conf = [m for m, ts in tc.items()
                    if all(not U.isdisjoint(t) for t in ts)]
            if conf:
                lo, hi = min(conf), max(conf)
                print(f"  ({j},{k}): #conf={len(conf):3d} min={lo:4d} "
                      f"max={hi:4d}  minQk={min(shells[k])} "
                      f"maxU={max(U)} 2minQk={2*min(shells[k])}")
            else:
                print(f"  ({j},{k}): NO conflict in window")

run("cantor", cantor(243), 243, 9)
run("greedyB2", greedy_b2(160), 160, 9)
