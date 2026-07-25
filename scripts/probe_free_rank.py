#!/usr/bin/env python3
"""Empirical rank probe: the finite-regime freeness-tree rank equals
the maximum free-set cardinality (verified: free_set_card_le_rank +
rank_ge_imp_free_set).  Compute it on truncated models and watch how
pool operations move it.

S (subset of A-positive) is REP-FREE on window [N0, Y] iff every
m in [N0, Y] has a triple x+y+z=m from A avoiding S.
Max-free-card = longest chain = truncated root rank (downward-closed).
"""
import random

def triples(A, m):
    As = sorted(A)
    Aset = set(A)
    out = []
    for x in As:
        if x > m: break
        for y in As:
            if x + y > m: break
            z = m - x - y
            if z in Aset:
                out.append((x, y, z))
    return out

def free(S, trip_cache):
    Sset = set(S)
    for m, trips in trip_cache.items():
        if not any(Sset.isdisjoint(t) for t in trips):
            return False
    return True

def max_free_card(pool, trip_cache, beam=200):
    # greedy beam search over chains (downward-closed family)
    frontier = [tuple()]
    depth = 0
    while True:
        nxt = []
        for S in frontier:
            hi = max(S) if S else 0
            for b in pool:
                if b > hi:
                    S2 = S + (b,)
                    if free(S2, trip_cache):
                        nxt.append(S2)
                        if len(nxt) >= beam * 4:
                            break
            if len(nxt) >= beam * 4:
                break
        if not nxt:
            return depth, frontier[:3]
        random.shuffle(nxt)
        frontier = nxt[:beam]
        depth += 1

def cantor(Y):
    out = []
    for n in range(Y + 1):
        m, ok = n, True
        while m:
            if m % 3 == 2:
                ok = False
                break
            m //= 3
        if ok:
            out.append(n)
    return out

def greedy_b2(Y, g=1):
    # greedy Sidon-ish basis: add n if needed for coverage
    A = [0, 1]
    for n in range(2, Y + 1):
        Aset = set(A)
        if not any((n - a) in Aset for a in A if a <= n):
            A.append(n)
    return A

def run(name, A, Y, N0):
    Apos = [a for a in A if a > 0]
    tc = {m: triples(A, m) for m in range(N0, Y + 1)}
    tc = {m: t for m, t in tc.items() if t}  # covered targets only
    r_full, wit = max_free_card(Apos, tc)
    # pool op: remove the greedy stall envelope (first maximal chain)
    env = set(wit[0]) if wit else set()
    pool2 = [a for a in Apos if a not in env]
    r_sub, _ = max_free_card(pool2, tc)
    # pool op: keep only upper half
    pool3 = [a for a in Apos if a > Y // 2]
    r_hi, _ = max_free_card(pool3, tc)
    print(f"{name:>10} Y={Y:4d} |A|={len(A):4d} rank={r_full:3d} "
          f"rank(-env)={r_sub:3d} rank(upper half)={r_hi:3d}")

random.seed(881)
for Y in (60, 120, 200):
    run("cantor", cantor(Y), Y, 9)
for Y in (60, 120, 200):
    run("greedyB2", greedy_b2(Y), Y, 9)
