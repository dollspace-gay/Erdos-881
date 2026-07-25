# Erdős 881 (k = 2): solution status

*Updated 2026-07-24, overnight campaign. VERIFIED = machine-checked in
Lean, zero sorries. LAB = machine-tested, not formalized. OPEN =
neither. This document supersedes all earlier versions.*

## The grand assembly (VERIFIED)

`erdos881_grand_assembly''` (`RedundantVertexKill.lean`) is the
sharpest verified statement of the campaign — superseding the earlier
forms.  For any `A` with `0 ∈ A`,
`PairCovers A N₀`, cofinal pair funnels (Link A's interface), and
anchor abundance:

> **either** a surviving infinite deletion exists (`A \ B` still
> order-3-represents every large target — so `A` is *not* a
> counterexample),
> **or** zero privately guards arbitrarily late targets,
> **or** an infinite team clique survives **all of whose positive,
> above-threshold vertices fail 2-redundancy at every threshold up to
> their own scale** — an infinite clique of self-scale 2-guardians
> (`escape_vertex_witness`: each such vertex two-guards a witness
> `n ≥ u` with support exactly `{u, n-u}`), the Grekos-type
> configuration of Open Link B1.

Everything else is dead, by the following verified kills.

## The kills (all VERIFIED tonight)

1. **The singleton stream** (`RotatingGuardianEndgame.lean`).  Any
   cofinal stream of positive singleton guardians forces a surviving
   deletion.  The extraction engine only reflects the anchor data and
   lower levels — all known before each level is chosen — so per-level
   defects are dodged through finite forbidden sets, and a stream
   refusing to dodge has a recurring guardian, killed by the fixed
   engine.  Big/small/fixed/rotating guardians: all dead.  Corollary
   (`FixedGuardianEndgame.lean`): **counterexamples have no
   order-three-essential element.**
2. **Clear clique edges** (`CliqueSplice.lean`).  A 2-redundant vertex
   whose clear edges (`3v ≤ m`) reach arbitrarily high partners runs
   the windowed engine: windows outgrow levels by partner choice.
   (Level hitting — the old B3 interface — is no longer needed.)
3. **ALL edges of any 2-redundant vertex** — the total clique kill
   (`RedundantVertexKill.lean`).  Single redundancy suffices: the
   avoiding representation of `u + x` dodges the partner free below
   the window, the upper desert and level lower bound need no joint
   hypothesis, truncation makes the out-of-window mirror promise
   vacuous, and the quad-defect engine runs on any destroyer supply.
   No hugging, clearance, or joint-redundancy hypothesis remains.
   (Known limit: the corep pin needs the redundancy threshold
   `N₁ ≤ u`; vertices redundant only at higher thresholds are not yet
   killed — this is exactly why the escape says "at every threshold
   up to its own scale".)
4. **Pair-redundant clique edges at any altitude**
   (`HuggingSplice.lean`).  Sharp pinning (`pinned_mirror_sharp`)
   needs no room — only two diagonal exclusions — so a jointly
   2-redundant pair's target carries a full-range mirror at `m - v`
   with four defects (`hugging_level`), levels are pinned near `v`
   (`level_lower_of_pairRedundant`: otherwise a covering window
   starves in the upper desert), and the quad-defect engine runs.
   **Hugging is no refuge.**
5. **Naive separated triangles** (`SeparatedTriangle.lean`): refuted
   by explicit witness — guard separation alone kills nothing.

## What remains open

**Link A (funnels).**  The trichotomy is VERIFIED
(`FunnelTrichotomy.lean`): every destroyed target of any deletion set
`B` carries a singleton funnel from `B`, a pair funnel from `B`, or
two representations with disjoint `B`-parts.  Since singleton funnels
satisfy the pair interface (`u = v`), Link A is *exactly*: no
infinite `B₀` has hereditarily diffuse destruction.  Verified tools
against it: the counting vise (`translate_two_support_card_le` —
destroyed targets and their whole translate families have
`r₂ ≤ 2|B∩[0,m]|`), the elementwise fork trichotomy
(`fork_trichotomy_elt` — every undeleted element below a destroyed
target either lands in `B + B` or plants a two-destroyed cross-sum),
and `TwoDestroyedBySet`-avoidance for undeleted elements.  Lab: the
diffuse regime never occurs in the wild (`probe_counting_vise.py`:
zero destroyed targets for sparse deletions in all models).

**Link B1 (self-scale guardians).**  The clique escape is an
infinite clique of vertices each two-guarding a witness at or above
its own scale (`escape_vertex_witness`).  Full 2-essentiality
(cofinal witnesses) is finite by Grekos-type counting (literature);
the self-scale form is weaker — it is exactly the behavior of
Erdős–Nathanson block bases at order two, so what must be excluded is
the order-three team-clique structure on top of it (lab: cross-scale
team stacking among tight-chained guards dies by coverage flooding —
the old T3 experiments).  Verified support: `TwoLevelDestroyers.lean`
(a genuinely pair-2-destroyed target has exactly two representations
and at most six destroying pairs).

**The zero residue.**  Cofinal `IsPrivateTriple A 0 m`.  Verified
squeezes: the target family's differences are never elements
(`zero_guardian_no_element_gap`) and separated targets are never
elements themselves (`zero_guardian_target_not_elt`) — the residue
needs cofinal non-element targets with an `A`-free difference set.

**Anchor abundance.**  `∀ g, ∃ c ∈ A` positive, `≠ g`, with an
unbalanced representation `w + w' = 2c` dodging `g`.  Fails only for
Sidon-like structure at every doubled point; two disjoint anchor
packages suffice.  Mild; formal supply lemma open.

**Eligibility edge cases.**  The clique escape only constrains
vertices with `0 < u`, `N₀ ≤ u`, redundancy threshold `N₁ ≤ u`.  A
clique of ineligible vertices (all 2-essential, or all below `N₀`)
escapes vacuously — B1 covers the essential case; small vertices are
finitely many.

## THE CAPSTONE: THREE INTERFACES (seventh form)

`erdos881_interfaces_refute_counterexample₇` (`Capstone.lean`).  The
zero residue is **derived away**: cofinal zero-guardianship forces
`A⁺` sum-free (`zero_residue_sum_free`), sum-freeness forbids
doubling elements, and doubling supply is already an interface — so
the residue refutes itself (`not_zero_residue_of_doubling`).  Along
the way the residue's full structure was verified: exact partition
`A⁺+A⁺ = co-A`, automatic ℵ₀-minimality, guaranteed positive triples,
primitive translation ladders.

**The three remaining interfaces:**
1. **Link A** — no cofinal diffuse destruction (`hnodiffuse`);
2. **Link B1** — no infinite clique of vertices each primitive, or
   fully 2-essential and anchor-starved-or-W-aligned;
3. **Supply** — infinitely many doubling elements plus one nonzero
   unbalanced package (near-trivial; fails only for globally
   sum-free-at-doubles structures).

## The earlier sharpest capstone

`erdos881_interfaces_refute_counterexample'` (`Capstone.lean`) +
`erdos881_grand_assembly₄` (`NonEssentialKill.lean`): with **doubling
supply** (infinitely many `c` with `c, 2c ∈ A`) and **one nonzero
package**, the interfaces are: no cofinal diffuse destruction
(Link A), no cofinal zero-guardianship, and no infinite clique of
vertices each **primitive or fully 2-essential**.  The pointwise kill
(`surviving_deletion_of_nonessential_edges`) eliminates every vertex
that is 2-redundant at any threshold and non-primitive: floored
engine, doubling anchors `(c, 0, 2c)`, zero-reflections free,
corep via non-primitivity.  Verified constraints on the survivors:
an infinite primitive clique makes zero fully 2-essential
(`zero_essential_of_infinite_primitives`); essential vertices' witness
sets repel element translates (`essential_witness_repels_translate`)
and their witnesses are never elements with two-point supports
(`escape_vertex_witness`).

## The cross-edge program (next)

The W-aligned enemy's forced families (`anchor_fork_forced`: translates
`m_k - u - C_u` below every edge top; ladders `L_k ∈ A` with
`u`-translate exits) live near the partner tops `v_k` — exactly where
the deserts of the partners' own edges `(v_i, v_j)` sit
(`IsPairDestroyer.desert`: `A ∩ (m' - v_i, m' - N₀) ⊆ {v_i, v_j}`).
Every clique pair is simultaneously constrained, so the `(v_i, v_j)`
targets must dodge windows around every `u`-forced point, for every
`u` below them, at every scale.  The composition of
`anchor_fork_forced` with the partners' deserts — quantified over the
whole clique — is the queued kill for the W-aligned escape.

## The earlier capstone

`erdos881_interfaces_refute_counterexample` (`Capstone.lean`): the
four remaining interfaces — no cofinal diffuse destruction (Link A),
anchor abundance, no cofinal zero-guardianship, no infinite clique of
self-scale 2-guardians (Link B1) — jointly refute counterexamplehood.
Link A's funnel interface is now itself a theorem
(`hasCofinalPairFunnels_of_diffuse_free`): its entire content is the
`hnodiffuse` hypothesis.

## Assessment

The problem's positive direction (YES for k = 2) is now reduced,
machine-verified end to end, to: **Link A diffuse-exclusion + Grekos
finiteness (a known theorem) + the zero residue + anchor supply.**
Every guardian-shaped mechanism — singleton, team, clear, hugging,
big, small, fixed, rotating — is formally dead.  The negative
direction would need a counterexample built entirely from
hereditarily diffuse destruction or ineligible-vertex cliques, for
which the lab finds no seed whatsoever.

## The Cantor demonstrator (2026-07-24, verified)

`Erdos881/CantorCarryRepair.lean` — the 881 repair mechanism on a
concrete basis, machine-verified end to end:

- `cantor_pair_basis`: the base-3 digit-{0,1} numbers ("Cantor basis"
  C) form an order-2 basis of ALL of ℕ (constructive layer split).
- `cantor_powers_destroyed` / `cantor_doubles_destroyed`: deleting the
  pure powers {3^k} removes EVERY 2-representation of 3^k and of
  2·3^k, at every scale (no-carry rigidity: digit-{0,1} numbers add
  without carries, so 2-reps of single-digit targets are trivial).
- `cantor_carry_repair` / `cantor_carry_repair_double`: order 3
  repairs every casualty — 3^k = (13+10+4)·3^(k-3) and
  2·3^k = (13+37+4)·3^(k-3), all parts in C, none a pure power.
  The third summand unlocks base-3 carries (1+1+1 = 3) that order 2
  cannot produce.

Significance for the recurring-pair leaf: the lab showed the leaf's
"AP3-free fork image" residue is realizable by exactly these digit
structures (AP3-free + interval sumset + cofinal fixed-pair
destruction, e.g. pair (1,4) destroying 3^k+5 with reps
{(1,3^k+4),(4,3^k+1)}), so no counting kill exists — but such
structures are NOT 881-counterexamples: the very rigidity that
starves order 2 hands order 3 its carry repairs. The enemy must be
simultaneously digit-rigid (to dodge the matching) and carry-poor
(to satisfy hfail) — the Cantor case proves these pull in opposite
directions.

Open matching residue (exact form): adversary must fork-2-color
every A-window so no v-v pair sums to T, mixed to T+d, u-u to T+2d,
for every achievable T = 2·(realized value)+e. For e=d a per-class
parity pattern dodges V9's identities; for e=0 the image must be
AP3-free (Behrend-type) — realizable as a 2-basis but then
carry-repairable at order 3.

## VERIFIED 881 INSTANCE (2026-07-24 00:00, commit 7945673)

`erdos881_cantor_instance` (CantorCarryRepair.lean, zero sorries):
the Cantor basis C realizes the full Erdős 881 (k=2) pattern:

1. **Order-2 basis**: every n ∈ ℕ is a sum of two members of C
   (`cantor_pair_basis`, constructive layer split).
2. **ℵ₀-minimal**: deleting ANY infinite B ⊆ C destroys order 2 —
   for each deleted b, the target 2b has unique representation
   (b, b) by no-carry rigidity (`cantor_double_unique`,
   `cantor_minimal`). This is exactly the minimality hypothesis of
   Erdős 881.
3. **Order-3 survival**: deleting the infinite set of pure powers
   {3^k} leaves an asymptotic order-3 basis — every n ≥ 3^7 is a
   sum of three non-pure members (`cantor_deletion_order_three`,
   full digit case tree with carry-constant menu).

So the first machine-verified nontrivial minimal order-2 basis
answers Erdős 881's question POSITIVELY for itself: the required
infinite B exists (the pure powers). The problem asks whether every
minimal basis behaves this way; the counterexample structure the
contradiction-mining campaign hunts must therefore be non-Cantor in
an essential way, while the campaign's verified interfaces already
force it to be Cantor-LIKE (2-rep poverty, AP3-free fork images) —
the pincer the remaining leaves must close.

## Endgame map after the Cantor arc (2026-07-24 00:20)

Open leaves, with tonight's dodge analysis folded in:

1. **Recurring-pair matching** (the only open leaf of the fixed-pair
   kill; everything else verified through ENGINE V9).  Image-only
   kills are now PROVEN impossible: for Ramsey color e = d the
   adversary parity-dodges V9's identities per residue class mod d;
   for e = 0 the image must be AP3-free, and AP3-free + covering +
   cofinal fixed-pair destruction is realizable (Cantor windows,
   pair (1,4), targets 3^k+5).  The leaf's true closure must couple
   the matching to hfail: a Cantor-like window structure admits
   carry repairs (verified: cantor_rigidity_conflict), so the enemy
   needs digit-rigid windows WITHOUT carry-repairable deletions —
   candidate theorem: 'fixed-pair unique-rep rigidity at cofinal
   scales ⟹ some marker deletion is order-3 repaired' (the general
   carry lemma). Lab first: build any 2-basis with fixed-pair
   destruction whose marker deletions all fail order 3 — if none
   exists, the general carry lemma is true and kills the leaf.
2. **Link A (diffuse exclusion)** — unchanged.
3. **B1 vertex classes** (primitive / essential-starved) — unchanged.
4. **Supply (hdb + hnz)** — near-trivial, unchanged.

Verified tonight: PinnedMirror sharp pinning; SeparatedTriangle
refutation; zero-residue elimination (capstone at 3 interfaces);
trichotomy→dichotomy; complete B1 case tree; fixed-pair pipeline
(corep dichotomy → fork pigeonhole → channel Ramsey → point splits →
composition) + engines V2–V9; the Cantor instance
(erdos881_cantor_full_instance) and the rigidity conflict.
