#!/usr/bin/env python3
"""hanchor audit: for each g in a sample, does there exist c in A,
c>0, c!=g, with w+w' = 2c, w,w' in A, w != c, w != g, w' != g?
If anchors fail on reasonable worlds, all hanchor-conditioned
theorems (shell arc, depth tax, stratification) silently exclude
those worlds."""

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

def check(name, A):
    Aset = set(A)
    fails = []
    for g in [0, 1, 3, 9, 13, 27, 40, 81]:
        found = None
        for c in A:
            if c <= 0 or c == g: continue
            for w in A:
                if w > 2 * c: break
                wp = 2 * c - w
                if wp in Aset and w != c and w != g and wp != g:
                    found = (c, w, wp); break
            if found: break
        if not found:
            fails.append(g)
    print(f"{name}: anchor fails for g in {fails if fails else 'NONE - hanchor OK'}")
    # central-only double fraction
    co = sum(1 for c in A if c > 0 and not any(
        w in Aset and (2*c - w) in Aset and w != c
        for w in A if w < 2*c))
    print(f"   central-only doubles: {co}/{len([a for a in A if a>0])}")

check("cantor", cantor(729))
check("greedyB2", greedy_b2(600))
