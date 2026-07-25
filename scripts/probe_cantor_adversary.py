#!/usr/bin/env python3
"""END-TO-END Cantor adversary test (Erdős 881 recurring-pair leaf).

Candidate counterexample-seed: A = subset-sums of {1,3,9,...,3^K}
(base-3 digits {0,1}) + small patches.  Fixed pair (u,v) ⊆ A.
Checks against ALL verified kill-constraints:
  C1 covering: A+A ⊇ [N₀, top]
  C2 cofinal fixed-pair destroyed targets m: every 2-rep of m uses
     u or v; both channels genuinely needed (u-rep AND v-rep exist)
  C3 not-all-v escape (V6): some cofinal u-channel realizations
     must exist -- check which forks are FORCED (single-channel)
  C4 THE MATCHING: realized fork image at each destroyed m --
     does EVERY admissible realization avoid (x,y,w realized with
     x+y=2w+e, y≠w) AND (pair with difference e)?  e ∈ {0,d}.
"""
import itertools, sys

K = 9
POW = [3**i for i in range(K+1)]
C = {sum(s) for r in range(K+2) for s in itertools.combinations(POW, r)}
TOP = sum(POW)
A = sorted(C)
Aset = set(A)

def reps(m):
    return [(x, m-x) for x in A if x <= m - x and (m - x) in Aset]

# C1: covering
holes = [n for n in range(0, 2*TOP+1) if not reps(n)]
print(f"C1 covering [0,{2*TOP}]: holes={len(holes)} {holes[:6]}")

# C2: fixed-pair destroyed targets for pair candidates
def destroyed(m, u, v):
    R = reps(m)
    if not R: return False
    has_u = any(u in p for p in R)
    has_v = any(v in p for p in R)
    others = [p for p in R if u not in p and v not in p]
    return has_u and has_v and not others

pairs = []
for u in A[1:10]:
    for v in A:
        if v > u:
            D = [m for m in range(1, 2*TOP+1) if destroyed(m, u, v)]
            if len(D) >= 3:
                pairs.append((u, v, D))
for u, v, D in pairs[:10]:
    print(f"C2 pair ({u},{v}): destroyed targets {D[:8]}{'...' if len(D)>8 else ''} (n={len(D)})")
if not pairs:
    print("C2: NO fixed pair has ≥3 destroyed targets — Cantor adversary FAILS at destruction")
    # try patched variants: A ∪ small extras or A minus some digits
    sys.exit(0)

# C3/C4 for the best pair: fork analysis at each destroyed m
u, v, D = max(pairs, key=lambda t: len(t[2]))
d = v - u
print(f"\nAnalysis pair ({u},{v}), d={d}, targets {D}")
for m in D:
    L = m - v   # level coordinate
    # forks: for z in A with constraints, channels: m-u-z ∈ A, m-v-z ∈ A
    forced_u, forced_v, free = [], [], []
    for z in A:
        if z == 0 or z >= m - v: continue
        cu = (m - u - z) in Aset
        cv = (m - v - z) in Aset
        if cu and cv: free.append(z)
        elif cu: forced_u.append(z)
        elif cv: forced_v.append(z)
    img_forced = [z + 0 for z in forced_v] + [z - d + 0 for z in forced_u]
    # realized value α(z) in level coords: v-chan -> z, u-chan -> z-d?? recompute:
    # v-channel open: m-v-z ∈ A: repair partner p = m-v-z: 'drop' σ=0: α := z
    # u-channel: p = m-u-z: α := z - d ... (level-normalized)
    print(f"  m={m}: forced_u={len(forced_u)} forced_v={len(forced_v)} free={len(free)}")
    imgF = sorted(set([z for z in forced_v] + [z - d for z in forced_u]))
    # V9 pattern in FORCED image alone (adversary can't dodge these):
    S = set(imgF)
    kill_e0 = any(x + y == 2*w and y != w
                  for w in S for x in S for y in S)
    kill_ed = any(x + d == y for x in S for y in S)
    print(f"    forced image (lvl coords) n={len(imgF)} sample={imgF[:10]}")
    print(f"    KILL e=0 (midpoint triple in forced): {kill_e0}; "
          f"e=d pair in forced: {kill_ed}")
