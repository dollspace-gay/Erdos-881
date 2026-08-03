#!/usr/bin/env python3
"""Finite diagnostic for sequence world."""

import sys
Y, N0 = int(sys.argv[1]), 9
Q = [3, 7]          # fixed envelope
qstar = 3
n = 20              # mirror point
L = int(sys.argv[2])
D = [50 * (k + 1) + 7 * k * k for k in range(L)]  # 20 rungs, spreading
D = [d for d in D if n + d <= Y - 10]

A = set(Q) | {0, 1, 2}
streets = [n + d for d in D]
streetset = set(streets)

def violates_street(x, Aset):
    # adding x must not create a non-Q pair of any target sequence
    for s in streets:
        y = s - x
        if 0 <= y and (y in Aset or y == x):
            if x not in Q and y not in Q:
                return True
    return False

# rungs first (forced members)
ok_rungs = 0
for d in D:
    v = n + d - qstar
    if not violates_street(v, A):
        A.add(v); ok_rungs += 1
# b-pairs per d
ok_pairs = 0
for d in D:
    for b in range(30, Y - d):
        if b in A and b + d in A:
            ok_pairs += 1; break
        cand = []
        if b not in A and not violates_street(b, A):
            A2 = A | {b}
            if (b + d) in A2 or not violates_street(b + d, A2):
                A.add(b); A.add(b + d); ok_pairs += 1
                break
# covering filler (greedy)
holes0 = 0
for m in range(N0, Y + 1):
    if any((m - a) in A for a in A if a <= m):
        continue
    # try to add one element x <= m/2 covering m
    added = False
    for x in range(m // 2 + 1):
        y = m - x
        if x in A and y in A:
            added = True; break
        if x in A or y in A:
            z = y if x in A else x
            if not violates_street(z, A):
                A.add(z); added = True; break
    if not added:
        for x in range(1, m // 2 + 1):
            y = m - x
            if not violates_street(x, A):
                A2 = A | {x}
                if not violates_street(y, A2):
                    A.add(x); A.add(y); added = True; break
    if not added:
        holes0 += 1

# verify everything
def is_street(s, Aset):
    for x in Aset:
        if x > s: continue
        y = s - x
        if y in Aset and x not in Q and y not in Q:
            return False
    return True

good_streets = sum(1 for s in streets if is_street(s, A))
rungs_in = sum(1 for d in D if (n + d - qstar) in A)
holes = sum(1 for m in range(N0, Y + 1)
            if not any((m - a) in A for a in A if a <= m))
print(f"|A|={len(A)} rungs={rungs_in}/{len(D)} "
      f"streets={good_streets}/{len(streets)} "
      f"bpairs={ok_pairs}/{len(D)} holes={holes}")
