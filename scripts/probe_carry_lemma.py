#!/usr/bin/env python3
"""Finite diagnostic for carry lemma."""
import itertools, random

def two_cover_holes(A, S, T):
    Aset = set(A)
    return [n for n in range(S, T+1)
            if not any((n - x) in Aset and n - x >= x for x in A if x <= n)]

def three_cover_holes(A, S, T):
    Aset = set(A)
    A2 = sorted(Aset)
    pair = set()
    for i, x in enumerate(A2):
        for y in A2[i:]:
            s = x + y
            if s > T: break
            pair.add(s)
    holes = []
    for n in range(S, T+1):
        if not any((n - x) in pair for x in A2 if x <= n):
            holes.append(n)
    return holes

def destroyed_targets(A, u, v, S, T):
    Aset = set(A)
    out = []
    for m in range(S, T+1):
        reps = [(x, m-x) for x in A if x <= m-x and (m-x) in Aset]
        if not reps: continue
        hu = any(u in p for p in reps); hv = any(v in p for p in reps)
        others = [p for p in reps if u not in p and v not in p]
        if hu and hv and not others:
            out.append(m)
    return out

def build_structures(rng, T):
    S = []
    # pure Cantor
    K = 1
    while 3**K <= T: K += 1
    pows = [3**i for i in range(K)]
    C = sorted({sum(c) for r in range(K+1) for c in itertools.combinations(pows, r) if sum(c) <= T})
    S.append(("cantor", C))
    # Cantor + noise
    for t in range(3):
        C2 = set(C)
        for _ in range(6):
            C2.add(rng.randrange(T))
        S.append((f"cantor+noise{t}", sorted(C2)))
    # Cantor with digit blocks shifted (base 3 digits {0,2}? {0,2}: sums {0,2,4}: covering fails; skip)
    # greedy destruction-first: start from pair (u,v), targets 2^k-ish, fill coverage greedily
    for t in range(4):
        u = rng.choice([1,2,3,4]); v = u + rng.choice([1,2,3,9])
        A = {0, u, v}
        targets = []
        q = 16
        while q < T:
            targets.append(q); q = int(q*2.7)+1
        for m in targets:
            A.add(m - u); A.add(m - v)
        # fill 2-coverage greedily avoiding new reps for targets
        for n in range(2, T+1):
            Aset = A
            if any((n-x) in Aset for x in list(A) if x <= n):
                continue
            if any(n - u == m - v or n in targets for m in targets):
                pass
            # add n-1? add a pair (a, n-a) chosen to avoid hitting targets' rep-sets
            added = False
            cands = list(range(1, n//2+1)); rng.shuffle(cands)
            for a in cands[:30]:
                b = n - a
                bad = False
                for m in targets:
                    if m < n: continue
                    for w in (a, b):
                        if (m - w) in A or 2*w == m:
                            bad = True; break
                    if bad: break
                if not bad:
                    A.add(a); A.add(b); added = True; break
            if not added:
                A.add(n)  # give up on protecting targets for n
        S.append((f"greedy{t}(u={u},v={v})", sorted(x for x in A if 0 <= x <= T)))
    return S

def thin_deletions(rng, A, dest, u, v, count=60):
    A = list(A)
    n = len(A)
    Bs = []
    # corep markers: rep partners of destroyed targets
    Bs.append(("coreps-u", [m - u for m in dest]))
    Bs.append(("coreps-v", [m - v for m in dest]))
    Bs.append(("coreps-both", [m - u for m in dest] + [m - v for m in dest]))
    # top slice, geometric slice
    Bs.append(("geometric", [a for a in A if a > 4 and abs((a & -a)) >= 0 and any(abs(a - 3**j) <= 0 for j in range(1, 12))]))
    srt = sorted(A)
    Bs.append(("every8th", srt[::8]))
    Bs.append(("every5th-off", srt[3::5]))
    for t in range(count):
        k = max(3, n // rng.choice([6, 8, 10, 12]))
        B = rng.sample(A, min(k, n))
        B = [b for b in B if b not in (0, u, v)]
        Bs.append((f"rand{t}", B))
    return Bs

def main():
    rng = random.Random(881881)
    T = 2500
    results = []
    for name, A in build_structures(rng, T):
        h2 = two_cover_holes(A, 40, T)
        if len(h2) > 0:
            results.append((name, "no-2-cover", len(h2), None)); continue
        found = None
        for u in [a for a in A if 0 < a <= 13][:6]:
            for v in [b for b in A if u < b <= u + 30][:8]:
                D = destroyed_targets(A, u, v, 50, T)
                if len(D) >= 3:
                    found = (u, v, D); break
            if found: break
        if not found:
            results.append((name, "no-destruction", 0, None)); continue
        u, v, D = found
        resists = True
        surviving_B = None
        for bname, B in thin_deletions(rng, A, D, u, v):
            Bset = set(B)
            if len(Bset) < 3: continue
            A2 = [a for a in A if a not in Bset]
            h3 = three_cover_holes(A2, 60, T)
            if not h3:
                resists = False; surviving_B = (bname, len(Bset)); break
        results.append((name, f"pair({u},{v}) dest={len(D)}",
                        "RESISTS" if resists else "killed",
                        surviving_B))
    for r in results:
        print(r)

if __name__ == "__main__":
    main()
