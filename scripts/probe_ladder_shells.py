#!/usr/bin/env python3
"""Cross-audit: shell profile of the R4 ladder world.  Enemy-like
sets need infinitely deep thin shells; honest sets stall
shallow-and-fat.  Where does the ladder world sit?"""
Y, N0 = 4000, 9
Q = [3, 7]; qstar = 3; n = 20
D = [50 * (k + 1) + 7 * k * k for k in range(20)]
D = [d for d in D if n + d <= Y - 10]
A = set(Q) | {0, 1, 2}
streets = [n + d for d in D]

def violates_street(x, Aset):
    for s in streets:
        y = s - x
        if 0 <= y and (y in Aset or y == x):
            if x not in Q and y not in Q:
                return True
    return False

for d in D:
    v = n + d - qstar
    if not violates_street(v, A): A.add(v)
for d in D:
    for b in range(30, Y - d):
        if b in A and b + d in A: break
        if b not in A and not violates_street(b, A):
            A2 = A | {b}
            if (b + d) in A2 or not violates_street(b + d, A2):
                A.add(b); A.add(b + d); break
for m in range(N0, Y + 1):
    if any((m - a) in A for a in A if a <= m): continue
    added = False
    for x in range(m // 2 + 1):
        y = m - x
        if x in A and y in A: added = True; break
        if x in A or y in A:
            z = y if x in A else x
            if not violates_street(z, A): A.add(z); added = True; break
    if not added:
        for x in range(1, m // 2 + 1):
            y = m - x
            if not violates_street(x, A):
                A2 = A | {x}
                if not violates_street(y, A2):
                    A.add(x); A.add(y); break

# shell profile (window-truncated, targets to Y)
def triples(m):
    out = []
    As = sorted(a for a in A if a <= m)
    Aset = A
    for x in As:
        for y in As:
            if y < x: continue
            if x + y > m: break
            z = m - x - y
            if z >= y and z in Aset: out.append((x, y, z))
    return out
tc = {m: t for m in range(N0, Y + 1) if (t := triples(m))}
def free(S):
    Ss = set(S)
    return all(any(Ss.isdisjoint(t) for t in ts) for ts in tc.values())
pool = sorted(a for a in A if a > 0)
shells = []
while pool:
    S = []
    for b in pool:
        if free(S + [b]): S.append(b)
    if not S: break
    shells.append(S)
    pool = [a for a in pool if a not in set(S)]
print(f"|A|={len(A)} shells={len(shells)} sizes={[len(s) for s in shells][:10]}")
print(f"rung-shell placement: ", end="")
rungs = {n + d - qstar for d in D}
for i, s in enumerate(shells):
    k = len(rungs & set(s))
    if k: print(f"shell{i}:{k}", end=" ")
print()
