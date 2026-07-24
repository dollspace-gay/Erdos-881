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

## The assembly is now formal: `master_reduction`

`TeamGraphRamsey.lean` proves (VERIFIED): if `HasCofinalPairFunnels A`
(Open Link A's interface) and `TeamCliqueFree A` (Open Link B, now a
formal Lean definition), then a counterexample reduces to an infinite
stream of singleton private guardians.  The stream's big-guardian branch
is then formally dead (`no_cofinal_big_privatePairs`, VERIFIED: two
stream members at separation ratio 3 violate `no_big_guardian_stacking`,
with separation supplied by `guardian_le`).  The small-guardian branch
feeds the defective-mirror endgame (LAB + partially VERIFIED).

**The single remaining open statement, formally in Lean:** discharge the
hypothesis pair of `master_reduction` —

> **Link A** (`HasCofinalPairFunnels`, defined in `TeamGraphRamsey.lean`):
> every counterexample admits a thinning with cofinal size-≤2 funnels.
> Attack: `BoundedPairFreeSet` + `InfiniteSunflower`; size-3 layer via
> `infinite_tripleRamsey_nat`.
>
> **Link B** (`TeamCliqueFree`, defined in `TeamGraphRamsey.lean`): the
> team graph has no infinite clique.  Attack: `TeamGuardianRigidity` +
> the coverage-conflict mechanism; base case exhaustively verified in
> the lab (all 22 hitting sets fail), team graphs of natural bases are
> trees, edge costs grow geometrically.  Caveat: with only cofinal
> lower-bound control over edge targets, window-alignment attacks fail —
> the proof must use the covering conflict, not target placement.

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
