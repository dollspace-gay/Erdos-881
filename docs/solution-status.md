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
> team graph has no infinite clique.  The pigeonhole reduction is
> VERIFIED (`infinite_teamClique_has_separated_triple`): any infinite
> clique yields triples at arbitrarily prescribed separations, so the
> open content is exactly `no_separated_triangle` for one triple.  Attack: `TeamGuardianRigidity` +
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

## Priority hygiene — DONE

Cassaigne–Plagne (Proc. AMS 132 (2004) 2833–2840) obtained and read
(2026-07-24; see `docs/literature-erdos881.md`). Confirmed: S(2)=3 and
the two-destroyer clash are known (different proof mechanism); the
mirror/desert rigidity theory and the surviving-deletion theorems are
not in the paper. **Imported for Link B:** their Lemma-4 double count
gives Σ δ(a) ≤ h, and the pair version bounds team-edge densities by
C(h,2) — the team graph of any exact basis is density-degenerate. This
is the recommended quantitative route to `TeamCliqueFree`.

## The attack on no_separated_triangle (derived 2026-07-24, end of session)

Cassaigne–Plagne's Theorem-1 engine transplants to teams, with one new
phenomenon. Their engine: for a private target c of guard b, the numbers
c − b and c − b − b' are forced ELEMENTS (our corep/mirror), and the
identity (c − b − b') + b' = (c − b) turns a forced pair-sum into a
2-representation that violates the other guard's privacy (their Lemma 3).

Team transplant: for edge {v,w} at target m₃, corep forks (m₃−v ∈ A or
m₃−w ∈ A) and bimirror at z := u forks likewise. Each of the four
(d, e)-combinations makes some number d + u carry a 2-rep avoiding a
{u,·}-team. The team Lemma-3 analog is NOT a flat contradiction but a
**pinning lemma** (provable — the u-branch case yields an immediate
3-rep of c' avoiding the team): if a + u has a team-avoiding 2-rep,
then the {u,v}-bimirror at z := a is pinned to its v-channel cofinally.

So the triangle generates PINNED FORKS — binary clauses — and the proof
should close by exhibiting a contradiction cycle among the ≈8 branch
assignments of the three edges' forks at the three mutual guards. This
is exactly what the repo's 2-SAT/implication-SCC machinery (audit
cluster c) was built to process.

NEXT SESSION, concretely:
1. Lab: enumerate the 8 branch assignments on real team triples
   (single-scale 3-cliques from probe_team_guardians.py — they exist!)
   and check each assignment dies; extract the dying cycle.
2. Formalize the pinning lemma (short — same style as bimirror).
3. Formalize the cycle case analysis ⇒ `no_separated_triangle`,
   then `infinite_teamClique_has_separated_triple` converts it to
   `TeamCliqueFree`, and `master_reduction` fires.
