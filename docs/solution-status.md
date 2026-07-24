# Erdős 881 (k = 2): solution status

*2026-07-24. Chain of custody for every link in the endgame program.
VERIFIED = machine-checked in Lean, zero sorries. LAB = exhaustively or
extensively machine-tested, not yet formalized. OPEN = neither.*

## The proof skeleton (positive direction)

A counterexample is an ℵ₀-minimal exact order-2 basis A (0 ∈ A) such
that A∖B is not an exact order-3 basis for any infinite B ⊆ A.

1. **Funnels.** Every destroyed target's support family is hit by the
   deleted set; the funnel is a minimal transversal. Funnels of sizes
   1, 2, 3 all occur cofinally in the wild (digit bases; census parts
   5–8). Reduction of general counterexamples to *bounded* funnel size
   via free-set/sunflower thinning: **OPEN** (Phase 3b; interface
   `HasCofinalPairFunnels` in `TeamGraphRamsey.lean`; size-3 analog
   would use `infinite_tripleRamsey_nat`).
2. **Ramsey dichotomy** (`infinite_teamClique_or_cofinal_privatePairs`,
   `TeamGraphRamsey.lean`): **VERIFIED.** Cofinal pair funnels force an
   infinite team-graph clique or an infinite stream of singleton
   private pairs.
3. **Singleton stream is dead-ended:**
   - big guardians can't recur (`no_big_guardian_stacking`): **VERIFIED**
     (consequence known: Erdős–Graham 1980 + Cassaigne–Plagne S(2)=3);
   - big-above-team / big-above-small (`no_big_guardian_above_team`,
     `no_big_guardian_above_small_guardian`): **VERIFIED**;
   - small-above-small, team-above-anything: **LAB** (zero stacks across
     all sweeps; formal proofs open — lab says the blocker is coverage
     flooding, so the sparse-window route is the template);
   - a cofinal small-guardian stream forces cofinal defective mirror
     levels: **LAB + hand derivation** (`small_desert`, `mirror_of_ne`
     VERIFIED; the defective-level spare-keys extension is **OPEN** —
     the non-defective version is VERIFIED, see 5).
4. **Infinite team clique is dead-ended:** team rigidity
   (desert/bimirror/upper mirror/forced translate): **VERIFIED.**
   Cross-scale triangle impossibility (`no_separated_triangle`):
   **OPEN** — supporting LAB evidence: team graphs of all natural bases
   are trees (zero triangles ever observed); edge-creation cost grows
   geometrically (≈×3/scale); random thin bases carry no teams at all;
   greedy triangle-purchase experiment: purchases
   at scales 0-4 all break covering, and at scale 0 EXHAUSTIVELY (all
   22 hitting sets of any composition fail) — the closing edge is
   unbuyable at any price in the even/odd scaffold.
5. **Mirror endgame** — cofinal reflection levels that are elements, at
   ANY spacing, admit a surviving infinite deletion
   (`surviving_deletion_of_cofinal_reflectionLevels`, plus periodic,
   geometric, and bounded-gap forms, and repo-vocabulary corollaries
   through `GuardianBridge`): **VERIFIED.** These are, per the
   literature check, the first positive partial cases of 881 (k=2).

## The single load-bearing open chain

Counterexample ⇒ (1: OPEN thinning) bounded funnels ⇒ (2: VERIFIED)
clique or singleton stream ⇒ (3/4: the two dead-ends, partially
VERIFIED, remainder LAB) ⇒ structures feeding (5: VERIFIED) ⇒
contradiction. The minimal formal statement whose proof would close the
positive direction, given the current verified stock:

> **Open Link A (funnel thinning).** Every counterexample admits an
> infinite thinning on which cofinally many destroyed targets have
> funnels of size ≤ K for some absolute K. — Attack with
> `BoundedPairFreeSet` + `InfiniteSunflower` (audit-rated reusable).
>
> **Open Link B (no separated cliques).** No order-2 covering set has a
> team-graph triangle whose three guards lie at pairwise separated
> scales (and inductively, no infinite clique). — Attack with
> `TeamGuardianRigidity` + the coverage-flooding mechanism the lab
> identified; the geometric edge-cost measurements say why it should be
> true.

Everything else in the skeleton is machine-verified today.

## Negative direction (gate 2b)

The disputed forum claim (NO for k ≥ 2 via thin sets) would need a
construction whose team hypergraph has no infinite dodgeable set. All
measurements point against feasibility: tree-structured protection,
geometric interlock costs, no generic protection. The triangle-purchase
experiment tested constructibility directly on the even/odd scaffold:
every purchase at five scales broke covering, exhaustively so at the
base scale. Gate 2b does not trigger.

## Priority hygiene

Before claiming novelty for any rigidity statement, read
Cassaigne–Plagne, Proc. AMS 132 (2004) 2833–2840 (unobtained; AMS PDF
Cloudflare-blocked from this environment).
