#!/usr/bin/env python3
"""Finite diagnostic for subsequence."""

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

def triples(A, m):
    As, Aset, out = sorted(A), set(A), []
    for x in As:
        if x > m: break
        for y in As:
            if x + y > m: break
            if y < x: continue
            z = m - x - y
            if z >= y and z in Aset: out.append((x, y, z))
    return out

def shells_of(A, Y, N0):
    tc = {m: t for m in range(N0, Y + 1) if (t := triples(A, m))}
    def free(S):
        Ss = set(S)
        return all(any(Ss.isdisjoint(t) for t in ts)
                   for ts in tc.values())
    pool, out = sorted(a for a in A if a > 0), []
    while pool:
        S = []
        for b in pool:
            if free(S + [b]): S.append(b)
        if not S: break
        out.append(sorted(S))
        pool = [a for a in pool if a not in set(S)]
    return out

def higman_embeds(l1, l2):
    # pointwise-<= sublist embedding, greedy check
    i = 0
    for v in l2:
        if i < len(l1) and l1[i] <= v: i += 1
    return i == len(l1)

def spine(shells):
    # greedy chain: keep rank layers that embed forward consecutively
    chain = [0]
    for j in range(1, len(shells)):
        if higman_embeds(shells[chain[-1]], shells[j]):
            chain.append(j)
    # lineage: thread first element
    lin = [shells[chain[0]][0]]
    for a, b in zip(chain, chain[1:]):
        l1, l2 = shells[a], shells[b]
        # match lin[-1]'s position greedily
        v = lin[-1]
        w = next((u for u in l2 if u > v), None)
        if w is None: break
        lin.append(w)
    return chain, lin

for name, A, Y in (("cantor", cantor(729), 729),
                   ("greedyB2", greedy_b2(500), 500)):
    sh = shells_of(A, Y, 9)
    ch, lin = spine(sh)
    print(f"{name}: shells={[len(s) for s in sh]}")
    print(f"  chain indices: {ch}")
    print(f"  LINEAGE: {lin}")
    print(f"  shell heads: {[s[:4] for s in sh[:4]]}")
