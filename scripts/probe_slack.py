#!/usr/bin/env python3
"""Finite diagnostic for slack."""
import random, math
random.seed(881)

Y, N0 = 320, 9

def covers_all(Aset):
    for m in range(N0, Y + 1):
        if not any((m - a) in Aset for a in Aset if a <= m):
            return False
    return True

def triples_avoiding(Aset, m, avoid):
    out = []
    As = sorted(a for a in Aset if a <= m)
    for x in As:
        if x in avoid: continue
        for y in As:
            if y < x: continue
            if x + y > m: break
            if y in avoid: continue
            z = m - x - y
            if z >= y and z in Aset and z not in avoid:
                out.append((x, y, z))
    return out

def greedy_disjoint(trips):
    used, cnt = set(), 0
    for t in trips:
        if used.isdisjoint(t):
            used.update(t); cnt += 1
    return cnt

def try_seal(A, b1, b2):
    for w in sorted(a for a in A if a <= 30)[:4]:
        m = b1 + b2 + w
        if m > Y: continue
        bad = triples_avoiding(A, m, {b1, b2})
        if not bad:
            return True, A
        removable = set()
        dead = False
        for t in bad:
            cands = [u for u in t if u > 9 and u != b1 and u != b2]
            if not cands: dead = True; break
            removable.add(max(cands))
        if dead or len(removable) > 6: continue
        A2 = A - removable
        if covers_all(A2) and not triples_avoiding(A2, m, {b1, b2}):
            return True, A2
    return False, A

def run(extra_frac):
    A = {0, 1}
    for n in range(2, Y + 1):
        if not any((n - a) in A for a in A if a <= n):
            A.add(n)
    ngreedy = len(A)
    extra = int(extra_frac * ngreedy)
    slots = [x for x in range(10, Y) if x not in A]
    random.shuffle(slots)
    for x in slots[:extra]:
        A.add(x)
    slack = len(A) - math.sqrt(2 * Y)
    # robustness: min R in mid window
    rs = [greedy_disjoint(triples_avoiding(A, m, set()))
          for m in range(150, 175)]
    tail = sorted(a for a in A if a > 100)
    pairs = [(tail[i], tail[i+1]) for i in
             random.sample(range(len(tail) - 1), min(16, len(tail)-1))]
    sealed = 0
    for b1, b2 in pairs:
        ok, A = try_seal(A, b1, b2)
        sealed += ok
    print(f"extra={extra_frac:.1f} |A|={len(A):4d} slack={slack:6.1f} "
          f"minR={min(rs)} medR={sorted(rs)[len(rs)//2]} "
          f"sealed={sealed}/{len(pairs)}")

for f in (0.0, 0.3, 0.7, 1.5):
    run(f)
