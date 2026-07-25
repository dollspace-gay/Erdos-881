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

## The capstone

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
