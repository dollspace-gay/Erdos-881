#!/usr/bin/env python3
"""R(m) = max pairwise-disjoint 3-reps (greedy lower bound).
Question: is Cantor uniformly robust (R -> infinity), which would
unify its branch under the robustness mechanism?  Report min R(m)
over windows for cantor and greedy-B2."""

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

def triples(Aset, As, m):
    out = []
    for x in As:
        if x > m: break
        for y in As:
            if y < x: continue
            if x + y > m: break
            z = m - x - y
            if z >= y and z in Aset:
                out.append((x, y, z))
    return out

def greedy_disjoint(trips):
    used, cnt = set(), 0
    for t in trips:
        if used.isdisjoint(t):
            used.update(t)
            cnt += 1
    return cnt

def run(name, A, Y, N0):
    Aset, As = set(A), sorted(A)
    lo = []
    for W0 in range(N0, Y - 40, max(1, (Y - N0) // 6)):
        W = range(W0, min(W0 + 40, Y + 1))
        rs = [greedy_disjoint(triples(Aset, As, m)) for m in W]
        lo.append((W0, min(rs), sum(1 for r in rs if r <= 2)))
    print(f"{name}: (window_start, min R, #{{R<=2}} of 40): {lo}")

run("cantor", cantor(730), 730, 9)
run("greedyB2", greedy_b2(700), 700, 9)
