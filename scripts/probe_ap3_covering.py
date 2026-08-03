#!/usr/bin/env python3
"""Finite diagnostic for ap3 covering."""
import random, sys

def ap3_free(B):
    S = set(B)
    Bs = sorted(S)
    for i, w in enumerate(Bs):
        for x in Bs:
            y = 2*w - x
            if y in S and x != w and y >= x:
                return False
    return True

def sumset_covers(B, lo, hi):
    P = set()
    Bs = sorted(B)
    for i, a in enumerate(Bs):
        for b in Bs[i:]:
            s = a + b
            if lo <= s <= hi:
                P.add(s)
    return all(n in P for n in range(lo, hi+1)), P

def exact_search(m):
    """Finite diagnostic for exact search."""
    best = [None]
    target = set(range(m, 2*m+1))
    def dfs(i, B, S):
        if best[0]: return
        if i > m:
            ok, _ = sumset_covers(B, m, 2*m)
            if ok: best[0] = list(B)
            return
        # prune: remaining elements [i..m]; coverage feasibility skipped (cheap version)
        # try adding i if AP3-free stays
        addable = True
        for x in B:
            if 2*x - i in S and 2*x-i != x: addable = False; break  # i,?,x AP with mid x... wait
        # full check
        if addable:
            for x in B:
                for y in B:
                    if x + y == 2*i and x != i: addable = False; break
                if not addable: break
                if i + x == 2*y and i != y: addable = False; break
        if addable:
            B.append(i); S.add(i)
            dfs(i+1, B, S)
            B.pop(); S.discard(i)
        if best[0]: return
        dfs(i+1, B, S)
    dfs(0, [], set())
    return best[0]

def greedy_repair(m, rng, iters=4000):
    """Finite diagnostic for greedy repair."""
    B = set()
    def viol(c):  # does adding c break AP3-freeness?
        for x in B:
            if (2*x - c) in B and 2*x - c != x: return True
            if (x + c) % 2 == 0 and (x + c)//2 in B and (x+c)//2 != x and (x+c)//2 != c: return True
            if 2*c - x in B and x != c: return True
        return False
    order = list(range(m+1)); rng.shuffle(order)
    for c in order:
        if not viol(c): B.add(c)
    ok, P = sumset_covers(B, m, 2*m)
    missing = [n for n in range(m, 2*m+1) if n not in P]
    for _ in range(iters):
        if not missing: break
        n = rng.choice(missing)
        # try to add a pair (a, n-a) enabling n: remove blockers
        cands = [(a, n-a) for a in range(max(0, n-m), n//2+1) if n-a <= m]
        rng.shuffle(cands)
        done = False
        for a, b in cands[:40]:
            trial = set(B); trial.add(a); trial.add(b)
            # remove elements violating AP3 with a,b (except a,b)
            bad = set()
            T = sorted(trial)
            Ts = trial
            for w in T:
                for x in T:
                    y = 2*w - x
                    if y in Ts and x != w and y > x or (y == x and x != w and y in Ts):
                        pass
            # simpler: recompute violations triple-wise (m small)
            def triples(S):
                S2 = sorted(S); Sset = set(S2); out = []
                for w in S2:
                    for x in S2:
                        y = 2*w - x
                        if x < y and y in Sset and x != w:
                            out.append((x, w, y))
                return out
            tr = triples(trial)
            # greedily delete non-{a,b} elements to clear triples
            okk = True
            for (x, w, y) in tr:
                opts = [t for t in (x, w, y) if t not in (a, b) and t in trial]
                if not opts: okk = False; break
                trial.discard(rng.choice(opts))
            if not okk: continue
            tr = triples(trial)
            if tr: continue
            okc, PP = sumset_covers(trial, m, 2*m)
            newmissing = [q for q in range(m, 2*m+1) if q not in PP]
            if len(newmissing) < len(missing):
                B = trial; missing = newmissing; done = True; break
        if not done:
            # random restart perturbation
            if rng.random() < 0.05 and missing:
                drop = rng.sample(sorted(B), min(3, len(B)))
                for dcp in drop: B.discard(dcp)
    return B, missing

def main():
    rng = random.Random(881)
    print("P1 exact, small m:")
    for m in range(4, 15):
        r = exact_search(m)
        print(f"  m={m}: {'FOUND ' + str(r) if r else 'IMPOSSIBLE'}")
    print("P2 greedy+repair, larger m (best missing counts):")
    for m in (20, 30, 40, 60, 80):
        best = None
        for t in range(6):
            B, miss = greedy_repair(m, rng)
            if best is None or len(miss) < len(best[1]): best = (B, miss)
        B, miss = best
        assert ap3_free(B), "violation!"
        print(f"  m={m}: |B|={len(B)} missing {len(miss)}/{m+1}"
              f"{' ← COVERS!' if not miss else ''} miss[:8]={sorted(miss)[:8]}")

if __name__ == "__main__":
    main()
