#!/usr/bin/env python3
"""CRYSTAL HUNT v2 — engineered.  Base: greedy B2[g]-style covering
set.  Tail: sparse geometric-ish elements.  For each tail pair
(t_i, t_j), TRY to make some target m a full hub by hole-punching:
remove base elements that enable pair-avoiding reps of m, while
keeping coverage.  Measure: how many pairs can be simultaneously
sealed, and what breaks."""

def covers_all(Aset, N0, Y):
    bad = []
    for m in range(N0, Y + 1):
        if not any((m - a) in Aset for a in Aset if a <= m):
            bad.append(m)
    return bad

def triples_avoiding(Aset, m, avoid):
    out = []
    As = sorted(a for a in Aset if a <= m)
    for x in As:
        if x in avoid: continue
        for y in As:
            if y < x or x + y > m: break_ = False
            if y < x: continue
            if x + y > m: break
            if y in avoid: continue
            z = m - x - y
            if z >= y and z in Aset and z not in avoid:
                out.append((x, y, z))
    return out

Y, N0 = 600, 9
# near-Sidon covering base (greedy: add n iff not covered)
A = {0, 1}
for n in range(2, Y + 1):
    if not any((n - a) in A for a in A if a <= n):
        A.add(n)
base = set(A)
tail = sorted(a for a in A if a > 150)
print(f"|A|={len(A)} tail={len(tail)} sample={tail[:8]}")

sealed, failed = 0, 0
protected = set()   # elements needed for coverage, cannot remove
for i in range(len(tail)):
    for j in range(i + 1, min(i + 4, len(tail))):  # nearby pairs only
        b1, b2 = tail[i], tail[j]
        ok = False
        # candidate targets: b1 + b2 + w for small w in A
        for w in sorted(a for a in A if a <= 40):
            m = b1 + b2 + w
            bad = triples_avoiding(A, m, {b1, b2})
            if not bad:
                ok = True
                break
            # try hole-punching: remove one part from each bad rep
            # (only elements not protected, not tail, not tiny)
            removable = set()
            deadend = False
            for t in bad:
                cands = [u for u in t if u > 9 and u not in protected
                         and u != b1 and u != b2]
                if not cands:
                    deadend = True
                    break
                removable.add(max(cands))
            if deadend or len(removable) > 6:
                continue
            A2 = A - removable
            if covers_all(A2, N0, Y):
                continue
            still = triples_avoiding(A2, m, {b1, b2})
            if not still:
                A = A2
                ok = True
                break
        if ok:
            sealed += 1
            protected.update({b1, b2})
        else:
            failed += 1
print(f"sealed={sealed} failed={failed} |A|now={len(A)}")
rem = covers_all(A, N0, Y)
print(f"coverage holes: {rem[:5]}")
