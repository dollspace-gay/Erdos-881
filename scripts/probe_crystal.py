#!/usr/bin/env python3
"""CRYSTAL HUNT (d=1): search for A ⊆ [0,Y] with 0 ∈ A, covering
[N0,Y] by pairs, such that every pair {b,b'} of tail elements is a
FULL HUB at some target m (every 3-rep of m meets {b,b'}).
Verified theory: every finite-rank counterexample pool contains such
a world.  If even tiny crystals refuse to exist, the mixed-regime
enemy loses its finite-rank room; if they exist, study them.
Method: greedy + annealing over the tail structure; score = fraction
of tail-pairs that are full hubs somewhere in window."""
import random
random.seed(881)

def triples(Aset, m):
    out = []
    As = sorted(a for a in Aset if a <= m)
    for x in As:
        for y in As:
            if x + y > m: break
            if y < x: continue
            z = m - x - y
            if z >= y and z in Aset:
                out.append((x, y, z))
    return out

def covers(Aset, N0, Y):
    As = sorted(Aset)
    for m in range(N0, Y + 1):
        if not any((m - a) in Aset for a in As if a <= m):
            return False
    return True

def pair_hub_exists(Aset, b1, b2, N0, Y, cache):
    # is there m with every rep meeting {b1,b2}?
    for m in range(N0, Y + 1):
        ts = cache.get(m)
        if ts is None:
            ts = triples(Aset, m)
            cache[m] = ts
        if ts and all(b1 in t or b2 in t for t in ts):
            return m
    return None

def score(A, N0, Y, T0):
    Aset = set(A)
    if not covers(Aset, N0, Y):
        return -1, 0, 0
    tail = [a for a in A if a >= T0]
    if len(tail) < 4:
        return -1, 0, 0
    cache = {}
    good = tot = 0
    for i in range(len(tail)):
        for j in range(i + 1, len(tail)):
            tot += 1
            if pair_hub_exists(Aset, tail[i], tail[j], N0, Y, cache) is not None:
                good += 1
    return good / tot, good, tot

Y, N0, T0 = 400, 9, 60
# start from a Sidon-ish covering base plus structured tail
base = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
body = list(range(10, T0, 3))
tail = [T0 + 5 * k for k in range(8)]
A = sorted(set(base + body + tail + [Y - 1, Y]))
best, bg, bt = score(A, N0, Y, T0)
print(f"seed score={best:.3f} ({bg}/{bt}) |A|={len(A)}")
cur = A[:]
curscore = best
for it in range(60):
    cand = set(cur)
    op = random.random()
    x = random.randrange(10, Y)
    if op < 0.45 and x in cand and x not in range(0, 10):
        cand.discard(x)
    else:
        cand.add(x)
    sc, g, t = score(sorted(cand), N0, Y, T0)
    if sc >= curscore:
        cur, curscore = sorted(cand), sc
        if sc > best:
            best = sc
            print(f"  it={it} score={sc:.3f} ({g}/{t}) |A|={len(cand)}")
print(f"final best={best:.3f}")
