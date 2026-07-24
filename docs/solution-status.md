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

## The pinned-mirror arc (2026-07-24, executed): Link B restructured

The pinned-fork attack was executed and the lab returned a verdict that
*redirects* Link B.

**The pinning lemma is real and VERIFIED** (`PinnedMirror.lean`,
numerically pre-validated on 25 824 channel instances with zero
violations, `scripts/probe_pinned_forks.py`): if `u + x` has a
two-term representation avoiding both guards of a destroyed target,
the `u`-channel of `x`'s bimirror is dead (`IsPairDestroyer.pinned`),
so the fork must realize the other channel
(`IsPairDestroyer.pinned_mirror`), and an element with both cross-sums
avoidably represented cannot exist below the target at all
(`IsPairDestroyer.double_pin_desert`).

**But the dying cycle does not close at one triple**: separated team
triangles EXIST inside full covering sets.  `SeparatedTriangle.lean`
(VERIFIED) exhibits `[0,9] ∪ [18,26] ∪ {53,62} ∪ [89,∞)` — pair-covers
from 12, contains 0, guards 9 / 53 / 62 at ratio > 5 pairwise destroy
79 / 88 / 81.  So `no_separated_triangle` by guard separation alone is
FALSE and the one-triple reduction is a dead end.  (Lab addendum: the
counterexample is knife-edge — no triangle survives any filler block
wider than its base block, and doubling ladders kill even single
separated edges.  Growth-separated triangles remain unconstructed.)
Note also: an infinite singleton-private stream is itself an infinite
`TeamEdge`-clique (degenerate edges), so `TeamCliqueFree` as literally
defined overlaps the stream branch; the effective content of Link B is
killing *genuine* infinite cliques.

**The replacement, VERIFIED today** (`PinnedMirror.lean`): per clique
edge `{u, v}` (`u < v`), with `TwoRedundant` / `TwoRedundantPair`
denoting single/joint deletability at order 2:

1. `hugging_of_pairRedundant`: a jointly 2-redundant pair only
   destroys targets `m < 4v + N₀ + 4`.  Contrapositive: **a clear
   target certifies that deleting the two guards breaks
   pair-covering.**
2. `pinned_level`: a clear target (`3v ≤ m`) of an edge whose low
   guard is 2-redundant forces an *element* mirror level
   `m − v ∈ A`, with the whole window below `v − u` reflecting into
   `A` — the raw material of the VERIFIED mirror endgame.
3. `cofinal_pinned_levels`: an infinite clique with one 2-redundant
   vertex and clear targets manufactures these levels cofinally.
4. `pinned_translation`: two such levels compose to a forward
   translation by the level gap — the windowed analog of
   `IsReflectionLevel.translation`.

**Link B is now three sharper open sub-links:**

> **B1 (scarcity of essentials).**  All but finitely many elements are
> 2-redundant (Erdős–Graham 1980 / Grekos — literature-known, not yet
> formalized), and genuinely pair-essential pairs have summable
> density (Cassaigne–Plagne Lemma-4 double count: a target 2-destroyed
> by a genuine pair has ≤ 2 disjoint representations, so ≤ 4 covering
> pairs; lab `probe_pinned_mirror.py` V3: density sum 0.217 ≤ 2).
>
> **B2 (the hugging regime).**  Edges whose targets all hug — and the
> hug is now VERIFIED tight: `sharp_hugging_of_pairRedundant` stacks
> three dyadic covering windows inside the double-pin desert (three
> disjoint windows, two guards) to force `m < 2v + 20(N₀ + N₂ + 2)`
> for every jointly 2-redundant pair.  Open content: extract a
> contradiction or mirror structure from cofinally many edges whose
> targets sit within `O(1)` of `2v`; `IsPairDestroyer.desert` gives
> empty windows of length `u − N₀` just below each such target.
>
> **B3 (windowed endgame splice).**  Upgrade the verified full-mirror
> extraction (`surviving_deletion_of_cofinal_reflectionLevels`) to
> the one-directional windowed mirrors of `pinned_level`, using
> `pinned_translation` for the composition step.

Chain: B1 gives a 2-redundant clique vertex; its edges either go clear
(→ B3 via pinned levels) or hug (→ B2).  Any resolution of the three
kills the genuine-clique branch; `master_reduction` then leaves the
singleton stream, whose big-guardian half is already dead.
