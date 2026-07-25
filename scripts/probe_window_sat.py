#!/usr/bin/env python3
"""Single-window satisfiability of the tight-pair enemy (Erdős 881).

Demands on A ∩ [0, T] (team S = {u, v}, d = v - u):
  D1 covering: every n in [N0, T] has a 2-rep
  D2 for EVERY b in A ∩ [W, 2W] (marker window): exists q with
     b+q, b+q-d <= T and r2(b+q) = 1 via (b, q) and
     r2(b+q-d) = 1 via (b, q-d)   [the aligned private pair]
  D3 cofinal pair-destroyed targets for (u, v) inside the window
     (all 2-reps through u or v, both used)

Search: randomized local search over A-membership on [0, T]; count
best simultaneous satisfaction. If D2 coverage stalls far below
100%, the window demand is unsatisfiable in practice; if it
saturates, examine the structure found.
"""
import random

def r2_fiber(A, Aset, n, T):
    return [(x, n - x) for x in A if x <= n - x and (n - x) in Aset]

def evaluate(A, u, v, N0, W, T):
    Aset = set(A)
    d = v - u
    holes = 0
    for n in range(N0, T + 1):
        if not any((n - x) in Aset for x in A if x <= n):
            holes += 1
    markers = [b for b in A if W <= b <= 2 * W]
    served = 0
    for b in markers:
        ok = False
        for q in A:
            s1, s2 = b + q, b + q - d
            if s2 < N0 or s1 > T or q < d:
                continue
            if (q - d) not in Aset:
                continue
            f1 = r2_fiber(A, Aset, s1, T)
            f2 = r2_fiber(A, Aset, s2, T)
            if len(f1) == 1 and len(f2) == 1:
                p1, p2 = f1[0], f2[0]
                if b in p1 and b in p2:
                    ok = True
                    break
        if ok:
            served += 1
    return holes, served, len(markers)

def local_search(T, u, v, N0, W, rng, iters=3000):
    A = {0, u, v} | {n for n in range(T + 1) if rng.random() < 0.08}
    best = None
    for it in range(iters):
        holes, served, nm = evaluate(sorted(A), u, v, N0, W, T)
        score = -holes * 10 + served
        if best is None or score > best[0]:
            best = (score, holes, served, nm, set(A))
        # mutate: fix a hole or try to serve a marker by pruning fibers
        Aset = set(A)
        if holes and rng.random() < 0.6:
            for n in range(N0, T + 1):
                if not any((n - x) in Aset for x in A if x <= n):
                    a = rng.randrange(1, n)
                    A.add(a)
                    A.add(n - a)
                    break
        else:
            # prune: remove a random element that appears in many fibers
            cands = [a for a in A if a not in (0, u, v) and a > 2]
            if cands:
                A.discard(rng.choice(cands))
    return best

def main():
    rng = random.Random(881)
    for (T, W) in [(300, 40), (600, 80)]:
        u, v, N0 = 1, 4, 10
        best = local_search(T, u, v, N0, W, rng)
        score, holes, served, nm, A = best
        print(f"T={T} W={W}: best holes={holes} served={served}/{nm} |A|={len(A)}")
    # also evaluate the Cantor window directly
    import itertools
    K = 5
    pows = [3**i for i in range(K + 1)]
    C = sorted({sum(c) for r in range(K + 2)
                for c in itertools.combinations(pows, r)})
    T = 2 * 3**K
    holes, served, nm = evaluate([x for x in C if x <= T], 1, 4, 10, 3**4, T)
    print(f"cantor T={T}: holes={holes} served={served}/{nm}")

if __name__ == "__main__":
    main()
