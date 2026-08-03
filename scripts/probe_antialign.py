#!/usr/bin/env python3
"""Finite diagnostic for antialign."""
import random
random.seed(881)
Y, N0 = 1500, 9

def covers(A):
    As = sorted(A)
    for n in range(N0, Y + 1):
        if not any((n - a) in A for a in As if 2 * a <= n or a <= n):
            return False
    return True

def repair(A):
    As = sorted(A)
    for n in range(N0, Y + 1):
        if not any((n - a) in A for a in A if a <= n):
            A.add(n - As[1] if n - As[1] > 0 and As[1] < n else n)
    return A

def greedy_unused(A):
    """Finite diagnostic for greedy unused."""
    Aset = set(A)
    U = {0}
    As = sorted(a for a in A if a > 0)
    for n in range(N0, Y + 1):
        Us = sorted(U)
        cov = False
        for x in Us:
            if 3 * x > n + 2: break
            for y in Us:
                if y < x: continue
                if x + y > n: break
                if (n - x - y) >= y and (n - x - y) in U:
                    cov = True; break
            if cov: break
        if cov: continue
        done = False
        # add one element completing a U-pair
        for x in Us:
            if x > n: break
            for y in Us:
                if y < x: continue
                if x + y > n: break
                z = n - x - y
                if z >= y and z in Aset:
                    U.add(z); done = True; break
            if done: break
        if not done:
            # add two elements alongside one U-element
            for x in Us:
                if x > n: break
                for a in As:
                    if x + 2 * a > n: break
                    b = n - x - a
                    if b >= a and b in Aset:
                        U.add(a); U.add(b); done = True; break
                if done: break
        if not done:
            for a in As:
                if 3 * a > n: break
                for b in As:
                    if b < a: continue
                    if a + b > n: break
                    c = n - a - b
                    if c >= b and c in Aset:
                        U.add(a); U.add(b); U.add(c)
                        done = True; break
                if done: break
    return len([a for a in As if a not in U]), len(U)

# start: LEAN two-scale covering set |A| ~ 2 sqrt(Y)
import math
m = int(math.isqrt(Y)) + 1
A = set(range(0, m + 1)) | set(range(m, Y + 1, m))
un0, u0 = greedy_unused(A)
print(f"start |A|={len(A)} unused={un0} |U|={u0}")
best = un0
cur = set(A)
for it in range(300):
    cand = set(cur)
    op = random.random()
    x = random.randrange(10, Y)
    if op < 0.5 and x in cand:
        cand.discard(x)
    else:
        cand.add(x)
    # keep covering
    ok = True
    for n in range(N0, Y + 1):
        if not any((n - a) in cand for a in cand if a <= n):
            ok = False; break
    if not ok: continue
    un, uu = greedy_unused(cand)
    # candidate counterexample objective: minimize unused, keep A lean-ish
    score = un + max(0, len(cand) - 3 * int(Y ** 0.5)) * 2
    curscore = best + max(0, len(cur) - 3 * int(Y ** 0.5)) * 2
    if score <= curscore:
        cur, best = cand, un
        if it % 60 == 0:
            print(f"  it={it} |A|={len(cur)} unused={best}")
print(f"final |A|={len(cur)} unused={best} "
      f"(floor vs sqrt(Y)={int(Y**0.5)})")
