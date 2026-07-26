# The Flood Structure Theorem for Erdős 881 Counterexamples

_All results below are machine-verified in Lean 4 (zero sorries,
axioms: propext, Classical.choice, Quot.sound), 2026-07-25, in
`Erdos881/DisjointRepEngine.lean`.  Notation: A ⊆ ℕ, r₂(n) :=
#{x ≤ n : x ∈ A, n−x ∈ A}.  Standing hypotheses: 0 ∈ A and A
2-covers beyond N₀ (`PairCovers`).  "hfail" denotes the Erdős-881
counterexample condition at k = 2: for every infinite B ⊆ A, A∖B is
not an exact asymptotic basis of order 3.  "hmin" denotes
ℵ₀-minimality at order 2.  "anchors" is the mild anchor-supply
interface._

## 1. The dodge principle (the method)

Call a finite set P **rep-free** if every m ≥ N₀ has a
3-representation avoiding P, and **pair-free** if every m ≥ N₀ has a
2-representation avoiding P.  Freeness is the recorded non-vacuity:
fat "junk" envelopes are never free, which is exactly what the
earlier trap formulations were missing (see the vacuity certificates
`trap_conclusion_trivial`, `tower_branch_trivial`).

**Dodge Lemma.** Hub-ness is up-monotone, so a recursive pick
sequence maintaining freeness either runs forever — producing an
infinite deletion under which every late target retains a surviving
representation (all parts sit below the target, hence inside the
stalled prefix's shadow), refuting hfail (or hmin at order 2) — or
stalls at a finite free envelope.

## 2. The floods (all unconditional)

**Theorem (rep flood; `rep_flood_of_hfail`).** hfail ⟹ there is a
finite rep-free P and X such that every b ∈ A with b ≥ X carries a
personal target m ≥ b with: every 3-representation of m meets
P ∪ {b}.

**Theorem (pair flood from hfail; `pair_flood_of_hfail`).** Same
statement at order 2 (every 2-representation of m ≥ b meets
P ∪ {b}), via 0-padding.

**Theorem (pair flood from minimality; `pair_flood_of_minimality`).**
hmin alone (no counterexample hypothesis) gives the order-2 flood:
a structure theorem for EVERY ℵ₀-minimal order-2 covering set.

**Theorem (double flood; `double_flood_of_counterexample`).** In a
counterexample both floods align on the same guardian: beyond one
threshold every basis element simultaneously pair-guards and
rep-guards personal targets.

**Pool relativization (`rep_flood_pool`, `pair_flood_pool`).** The
dodge restricted to any unbounded 0-free pool yields an envelope
made of pool elements.  Consequences: cascade (envelopes of
guardians, `pair_flood_cascade`) and positivity of cores (positive
pool ⟹ 0-free envelope).

## 3. Canonical form

**Theorem (canonical flood; `canonical_flood_pos_of_hfail`).**
hfail + anchors ⟹ there is ONE nonempty finite core S* ⊆ A∖{0}
and cofinally many rotating guardians b ∉ S* whose minimal order-3
hubs are EXACTLY S* ∪ {b}.  (Rotator necessity comes from envelope
freeness; nonemptiness from the private-stream kill; positivity from
the positive-pool run.)

**Theorem (routing dichotomy; `routing_dichotomy_of_hfail`).**
Cofinally, one of:
(L) some fixed s₀ ∈ S* has coreps at canonical targets (n − s₀ ∈ A)
    beyond every bound; or
(R) the rotating guardian owns its target's entire order-2 life
    (every 2-representation of n uses a), with corep n − a ∈ A.

**Sharer laws (`two_guardians_per_pair_target`,
`three_guardians_per_rep_target`).** One envelope-avoiding
representation of a target pins all its guardians to its parts: the
guardian→target maps are ≤2-to-1 (order 2) and ≤3-to-1 (order 3).

**Team supply (`guardian_team_hubs_of_deletion`).** For every 0-free
infinite deletion B, cofinally many failing targets carry minimal
hubs of cardinality ≥ 2 made of B-elements.

## 4. The r₂ oscillation

**Sidon streets (`constant_sidon_of_hfail`,
`constant_sidon_of_minimality`).** Both hfail and hmin force
cofinal streams of targets with r₂ ≤ 2(|P|+1) — one constant.
(Pair shadow: a 0-free hub is a transversal of the order-2
representations via (x, n−x, 0); components lie in H ∪ (n−H).)

**Log wall (`log_sidon_of_hfail`).** A geometric deletion inside A
forces cofinally many targets with r₂(n) ≤ 2(log₃ n + 1).

**Fan and blowup (`pairHub_of_translate`, `hub_fan_blowup`,
`covering_sqrt_lower`).** An order-3 hub H at n is an order-2 hub at
every translate n − w (w ∈ A∖H): the fan is essentially Sidon.
Pigeonholing the ≥ |A ∩ [0,n]| − |H| fan routes over |H| members
hands some h ∈ H at least (|A∩[0,n−N₀]|−|H|)/|H| pair
representations of n − h, and |A ∩ [0,n]| ≥ √(n−2N₀+1).

**Theorem (Sidon door closed; `r2_unbounded_of_hfail`).**
hfail ⟹ r₂ is unbounded.  Erdős–Turán holds for Erdős-881
counterexamples.  Hence the counterexample's r₂ oscillates between
a fixed constant and ∞ forever.

**Offset dichotomy (`blowup_offset_dichotomy`).** The blown
translates sit either at ONE fixed envelope offset s₀ beyond every
bound, or at the rotating corep m − b.

**Reflection desert (`pair_owner_reflection_desert`).** A pair-owner
forces n − z ∉ A for every element z with z, n−z ≠ owner.

## 5. The portrait

**Theorem (`counterexample_portrait`).** A counterexample is,
simultaneously and forever: centrally administered (canonical
nonempty positive core), fully employed (every large element guards
at both orders), Sidon on its guarded streets, and infinitely blown
elsewhere.

## 6. What remains

All the above is mutually consistent locally — near-Sidon minimal
bases realize the order-2 half, and the oscillation is not yet a
contradiction.  The remaining routes: (a) geometry of the fixed
blowup offset (shift-desert accumulation); (b) hereditary team
analysis inside one geometric ground stream (transversal barriers,
ordinal rank); (c) coupling the two personal targets of one
guardian.  The problem's difficulty is now concentrated in a small,
fully-verified configuration space.

## 7. Addendum (evening block): the rank framework and the trichotomy

All verified in `Erdos881/FreeRank.lean` and
`Erdos881/InfiniteRamsey.lean`:

**Infinite Ramsey, every arity** (`infinite_ramsey_tuples`): every
two-colouring of the strictly monotone (r+1)-tuples of ℕ admits an
infinite homogeneous subsequence.  (Pairs/triples/quadruples also
available standalone.)

**The freeness tree**: nodes are finite rep-free sets of positive
basis elements; steps insert one larger element.  Verified:
well-foundedness (`freeStep_wf`), ordinal rank with strict decrease
(`exists_strict_rank`), the leaf law (boundary = hubs,
`freeNode_extension_iff`), hereditary shallow stalled zones
(`Stalled.of_step`, `stalled_chain_bound`), existence of stalled
nodes from the flood (`stalled_exists_of_hfail`), pool trees as
subrelations (`poolFreeStep_wf`), rank monotonicity
(`rank_le_of_subrel`, `pool_rank_mono`), rank positivity
(`pool_rank_pos`), size↔rank in the finite regime
(`free_set_card_le_rank`, `rank_ge_imp_free_set`), and ladder
certificates (`escalation_rank_certificate`).

**THE REDUCTION** (`no_pool_rank_descent`): no pool sequence has
strictly descending root ranks; hence any verified pool operation
strictly dropping the root rank along its iterates refutes the
counterexample and solves Erdős 881 (k = 2) positively.

**THE TRICHOTOMY** (`rank_lt_omega_perfect_clique` +
`clique_descent`): a pool of finite root rank contains a PERFECT
CLIQUE WORLD — an infinite subsequence and a level d ≥ 1 with every
d-subset free and every (d+1)-subset a full hub; its hub hypergraph
is exactly (d+1)-uniform (`perfect_world_small_sets_free`).  Thus
every counterexample pool is infinite-rank or contains a perfect
clique world.

**Status of the two rooms**: perfect worlds are hfail-self-serving
(their own pair-hubs pay every within-world deletion) and resist
counting via sparsification; infinite-rank pools are wide-not-tall
free families.  The compressed open question remains the
rank-dropping operation.

## 8. THE CHARACTERIZATION (18:20)

**Theorem (`hfail_iff_no_hereditarily_free`).**  For covering `A`
with `0 ∈ A`: the counterexample condition holds iff `A` has NO
infinite hereditarily rep-free subset (a set all of whose finite
subsets are rep-free — equivalently, a surviving deletion).

**Erdős 881 (k = 2), equivalent form:** does every ℵ₀-minimal
exact order-2 basis contain an infinite hereditarily rep-free set?

The whole campaign now organizes around this sentence: the floods
are the stalled certificates of hereditary-freeness attempts, the
crystals are its local obstructions, the rank measures how far
freeness extends, and the adaptive toolkit (immunity, location)
describes where obstructions can and cannot sit.

**Addendum to §8 (`hfail_iff_freeStep_wf`, `endgame_triangle`).**
The equivalence extends to a triangle: counterexample-hood ⟺ no
hereditarily free set ⟺ well-foundedness of the freeness tree
(the last leg purely combinatorial).  The rank framework is thus
not a model of the problem — it IS the problem.

## 9. THE FINAL FORM (18:30)

**`counterexample_iff_rep_tree_wf` / `endgame_final_form`.**  The
two characterizations collapse: minimality is a subtree consequence
(the pair tree embeds in the rep tree), so the FULL counterexample
condition — minimality and universal order-3 failure together — is
equivalent to well-foundedness of one relation:

  Erdős 881 (k = 2) ⟺ no 2-covering set containing 0 has a
  well-founded rep-freeness tree
  ⟺ every such set contains an infinite hereditarily rep-free
  subset (an infinite branch).

Everything the campaign verified is now literally a study of this
one tree: its stalls (floods), its finite-rank pockets (crystals),
its boundary (ω-nodes), its immune zones, and its Cantor branch.

## 10. THE ABSOLUTE FLOOD (18:55–19:01)

The tree-flood quantified over LARGE extensions.  Inclusion kills
that restriction (`freeSup_wf`, `pairSup_wf`): an infinite
ascending inclusion-chain of free sets — insertions anywhere, not
just at the top — would union into an infinite hereditarily free
set, i.e. a branch.  Hence:

**Theorem (`exists_absolute_leaf`).**  Under hfail, every free
node extends to an INCLUSION-MAXIMAL free envelope Q: every
positive basis element outside Q — small or large — completes a
hub over Q.  One canonical finite envelope, total guardianship.
The enemy in one line: ∃ finite free Q with A⁺ ∖ Q ⊆ Guardians(Q).

**Theorem (`exists_absolute_pair_leaf`).**  The order-2 version
needs only elementwise minimality — a standalone structure theorem
for EVERY ℵ₀-minimal exact order-2 basis: maximal pair-free
envelopes exist and are totally pair-guarded.

**Personal targets (`absolute_leaf_personal_target`).**  Freeness
of Q forces the guardian into every Q-avoiding representation of
its target: b ≤ m_b and m_b = b + y + z with y, z ∈ A ∖ Q.  So the
sharer laws make b ↦ m_b ≤3-to-1 on ALL of A⁺ ∖ Q, and every
target is Sidon over the one envelope (pair shadow).

## 11. THE SHELL ENDGAME (19:13)

Iterating pool absolute leaves (`exists_absolute_leaf_pool`)
stratifies the counterexample (`absolute_shell_stratification`,
`shell_endgame` / `endgame_shells`): infinitely many pairwise
disjoint NONEMPTY free shells Q₀, Q₁, …, each inclusion-maximal in
the pool its predecessors leave, so every positive element outside
shells 0..k guards shell k.  A shell-(k+1) member guards shells
0..k; an eternal survivor guards every level.

**The rotation cap (`four_disjoint_hubs_singleton`).**  A rep has
three parts: one target cannot carry hubs through four disjoint
b-free envelopes unless b owns it outright (every rep uses b).
Hypothesis-free pigeonhole.

**The survivor dichotomy (`eternal_survivor_dichotomy`).**
Each eternal survivor has unbounded personal targets, or owns one
target as a private singleton.

**The corner dies (`shell_survivors_unbounded_targets`).**  Owners
own at their own scale, so unboundedly large owners would form a
cofinal private-triple stream — killed by the rotating-guardian
endgame.  Hence beyond one threshold every eternal survivor is
INFINITELY EMPLOYED: it guards at unboundedly large targets over
the disjoint shell family.

**Two enemy shapes remain.**  Either eternal survivors are finite
— the shells tile A⁺ up to a finite set (perfect stratification:
the fractal/Cantor-like picture) — or infinitely many survivors
each guard at unbounded scales across infinitely many disjoint
free envelopes.

## 12. THE CAP SUITE AND THE CONFLICT LAW (19:29)

All hypothesis-free pigeonhole, hence true in every world:

**Rotation caps.**  One target, one guardian: four disjoint
b-free envelopes force singleton ownership
(`four_disjoint_hubs_singleton`); three suffice at order 2
(`three_disjoint_pair_hubs_singleton`).

**The six-level cap (`seven_level_hub_impossible`).**  One
target, seven DISTINCT guardians over seven disjoint envelopes:
impossible outright — a rep part covers at most one envelope
plus one guardian-identity, 3×2 = 6 < 7.  No ownership escape.

**The 18-level absolute cap (`eighteen_level_cap`).**  Nineteen
envelope-hubs at one target, any guardians: some guardian owns
the target.  So absent ownership one target serves ≤ 18 levels.

**The conflict law (`shell_pairs_conflict`,
`five_shell_conflict_impossible`,
`four_shell_pair_conflict_impossible`).**  Every pair of shells
owns a conflict target (later members guard earlier shells; hubs
up-monotone `IsRepHub.mono`).  Per target the conflict graph has
max degree ≤ 3 and vertex-cover ≤ 3, hence ≤ 9 shell-pairs per
target (degree ≤ 2 at order 2).  The complete graph on shell
indices must therefore spread over infinitely many conflict
targets — each a guardian-free pure envelope hub, Sidon-bounded
by the union size.

Status: the caps quantify REUSE exhaustively; placement remains
enemy-free (target liberty).  The ledger is complete; the missing
piece is unchanged — one verified upper-bound device on target
placement.

## 13. THE REFLECTION LEDGER (20:19)

**Seal cost (`seal_cost_of_disjoint_avoiding`).**  Sealing an
envelope at a target by deletion costs one deleted element per
pairwise disjoint envelope-avoiding representation (deletion form
of the matching–cover duality).

**Common-reflection supply (`two_hubs_common_reflection`).**  Two
hub targets fan-route any shared window through their envelopes;
pigeonholing the envelope pair (h, h') hands one pair a
proportional sub-window V with m − h − a ∈ A AND m' − h' − a ∈ A
for every a ∈ V.

**Double-reflection supply (`double_reflection_supply_of_hfail`).**
Composing with the rep flood and the covering √-window: at EVERY
size K a counterexample carries two reflection points u, u' and K
elements a ∈ A with u − a ∈ A and u' − a ∈ A simultaneously.
Distinct points: K-fold difference multiplicity at the fixed
offset u' − u.  Equal points: K-fold sum concentration through a
shared window.  The reflection points are located: u ∈ (m − P) ∪
{m − b}, u' ∈ (m' − P) ∪ {m' − b'} — the rotator-corep option is
the AFFINE CORNER (m_b = b + n schedules), which the T-street
joint pigeonhole turns into: difference blowup at some offset OR
an affine flood m_b = b + n with all difference-translates
n + (b − b') being constant-Sidon streets.  Formalizing the
T-street classification is queued for the next session.

## 14. THE STREET DICHOTOMY (20:26)

**`street_dichotomy_of_hfail` / `difference_blowup_or_affine_corners`.**
Three flood streets and two passes of the reflection engine
yield, at every K and beyond every size S:

  (Diff) K-fold difference multiplicity: a fixed offset δ ≥ 1
  with K elements x ∈ A, x + δ ∈ A; or

  (Affine) all reflection points coincide at a K-fold blown point
  n, size-forcing makes the flood affine there (m₂ = n + b₂,
  m₃ = n + b₃), and the difference translate n + b₃ − b₂ is a
  pair street through the third rotator.

Split over all K: either difference multiplicity is UNBOUNDED —
so B₂[g]-difference enemies die; Erdős–Turán closed the sum door,
this closes the difference door — or the counterexample produces
affine corners (blown point + affine flood + coupled street at
the basis-difference translate) beyond every threshold.  The
affine corner is the enemy's last reflection refuge; it couples a
blown point, two basis elements, and a Sidon street in one linear
equation s + b₂ = n + b₃, which no previously known theorem
forced.

## 15. THE FOUR ROOMS (20:36)

**`counterexample_four_rooms` / `endgame_four_rooms`.**  The full
composition of the dichotomy night.  Every counterexample lives
in one of four terminal rooms (rooms 3–4 share one flood
envelope):

  **R1 — the translation room**: one fixed offset δ with
  unbounded difference multiplicity (A ∩ (A − δ) infinite).
  **R2 — the scattering room**: difference pairs at arbitrarily
  large offsets, at every multiplicity.
  **R3 — the scattered halls**: arbitrarily large blown mirror
  points, each an affine corner beyond every size.
  **R4 — the street ladder**: one mirror point n whose
  difference translates n + d are pair streets for unboundedly
  large realized d.

R4 pins street POSITIONS to a one-parameter family — the first
crack in target liberty.  R1 is near-translation-invariance, the
most rigid configuration yet.  Next-session attacks: R1 via
translation/periodicity machinery (MirrorPeriodicity), R4 via
ladder-street interactions with blown targets, R2/R3 via energy
accounting over the scattered scales.

## 16. MINING THE STREET LADDER (20:42)

**`street_ladder_pure`.**  Beyond the mirror point the rotator
sits above its own street and drops out of every pair: the ladder
streets n + d are PURE-Q pair hubs (fixed finite envelope), each
in the shadow Q + A, each alongside a basis pair at difference d.

**`ladder_shadow_concentrates`.**  One shadow element q* serves
unboundedly many rungs: {n + d − q*} is an infinite subset of A —
an arithmetic copy of the realized-difference family living
inside the basis.

**`ladder_difference_desert`.**  A rung reflection crossed with a
higher rung's street forces q* + (d' − d) out of A (up to Q): the
ladder digs deserts at its own translated difference set, so the
rung family is invisible to all higher streets' pair-life.

Room R4 is now the most constrained object in the program:
explicit street positions, one fixed envelope, an arithmetic rung
family inside A, and self-dug deserts — four simultaneous laws on
one one-parameter family.

## 17. THE CLASSICAL-MINIMALITY INTERFACE (20:57)

Erdős 881 states A is a MINIMAL basis — every element essential —
and until tonight the campaign only ever used the weaker
ℵ₀-minimality that hfail forces.  The classical hypothesis now
has its own verified interface:

**`essential_private_pair_stream`.**  An essential element owns a
cofinal stream of unique-decomposition targets m = b + c: every
pair of m is exactly {b, c}.

**`shared_private_target_is_sum`.**  Two essentials share a
private target only at their mutual sum — the streams are almost
disjoint.

**`unique_pair_graph_infinite_degree` /
`disjoint_unique_pairs_of_essential`.**  The unique-sum graph
(edges = unique-decomposition sums) has all degrees infinite and
carries K pairwise disjoint edges for every K, by height-forced
fresh choice.

The true 881 configuration therefore carries a canonical infinite
graph of maximally fragile targets (r₂ = 1), almost-disjoint
streams, and arbitrarily large matchings — supply the deletion
game can consume.  Connecting this graph to the order-3 machinery
(what happens at matched targets under matched deletions) is a
fresh program that no earlier arc touched.

## 18. THE UNIQUE-SUM RAMSEY DICHOTOMY (21:05)

**`unique_sum_ramsey`** (any covering set, no minimality): an
infinite ascending subsequence exists whose pairwise sums are ALL
unique-decomposition targets or NONE are.  All-unique side
(`all_unique_pair_hubs`, `all_unique_is_sidon`): an infinite
Sidon configuration whose sums form a 2-PARAMETER family of
two-element pair hubs — denser fragile supply than the street
ladder.  None-unique side: every pairwise sum is 2-robust at
order 2.  Combined with the classical-minimality graph
(§17) and the team supply (`matched_deletion_teams`), the true
881 configuration now has three interlocking combinatorial
objects: the unique-sum marriage network, the homogeneous
Ramsey subsequences, and the guardian teams that matched
deletions must field.

**Addendum (`clique_or_independent_teams`, 21:08).**  Composed
with the team supply: the counterexample contains an infinite
no-unique-sums sequence, or an infinite Sidon clique whose
deletion is defended by teams drawn from INSIDE the clique.  In
the clique branch the fan blowup cannot land on the clique square
(r₂ = 1 there): either blown translates dodge S + S or teams have
size ≥ √n/2 — the dodge is enemy-controlled (liberty), so this is
a location law, not a kill.

## 19. THE CUBE DICHOTOMY (21:14)

**`cube_avoidance_ramsey`** — the problem in miniature, order 3:
every covering set carries an ascending positive sequence T
inside a family R with either every triple sum T i + T j + T k
representable AVOIDING R (the T-deletion leaves its own
3-parameter sum cube alive; failing targets must dodge the cube —
the order-3 negative placement law), or every representation of
every triple sum routed through R (the enemy's dream realized on
one sequence).  The full Ramsey cascade now stands:
`unique_sum_ramsey` → `ramsey_trichotomy_of_covering` (order 2) →
`cube_avoidance_ramsey` (order 3), all pure combinatorics.

**The ω-diagonal (designed, next session).**  Self-avoidance at
arity r is inherited by subsequences, and `infinite_ramsey_tuples`
covers every arity: nesting the dichotomy over r = 2, 3, 4, …
and diagonalizing yields either one sequence self-avoiding at ALL
arities simultaneously (its every sumset survives its own
deletion) or a sequence routed at some fixed arity.  The distance
from the all-arities survivor to a full surviving deletion — its
sumsets versus all late targets — is the cleanest remaining
statement of the whole problem.

## 20. THE ω-AVOIDANCE DICHOTOMY (21:22)

**`omega_avoidance_dichotomy`** — nested Ramsey at EVERY arity
against one fixed base range, diagonal extraction: every covering
set contains an ascending positive sequence T (inside a positive
family R) whose entire tail subset-sum semigroup either SURVIVES
T's own deletion — every tail subset-sum of every arity keeps a
triple representation avoiding R ⊇ T, so failing targets dodge
the whole semigroup — or is ROUTED at some fixed arity.  With
`survival_of_complete_avoiding`, Erdős 881 (k = 2) is now pinched
between two verified statements:

  the ω-diagonal gives self-avoidance at all arities but loses
  density; completeness would finish the problem but Ramsey
  thinning destroys it.

DENSITY VERSUS HOMOGENEITY, as one pair of Lean theorems.

## 21. NASH-WILLIAMS: THE DOOR AND THE SPINE (21:50)

**`shell_higman_chain`.**  The enemy's shells, read as sorted
lists, live in Higman's well-quasi-order (Mathlib's
Nash-Williams machinery): an infinite subsequence of shells is
an embedding-CHAIN — each shell pointwise-dominated inside every
later one.  The antichain of freedoms carries a canonical
ascending spine.

**`spine_lineage`.**  Consecutive embeddings compose into
element lineages, and shell disjointness makes every step
strict: a canonical strictly increasing sequence x with
x t ∈ Q (σ t) — an infinite ascending skeleton threading the
enemy's own free material, extracted with zero choices beyond
the machinery's own.

The chaining program is no longer a plan: the raw spine exists.
Next: the spine's own stall (free_prefixes_die applied to x
yields a hub of lineage elements), and the adaptive game on
canonical material — lineage extension versus stall hubs.  This
is where the next session begins.

## 22. RANK OR LOCKSTEP (21:56)

**`spine_rank_or_lockstep`.**  Spine shell sizes are
non-decreasing along the Higman chain, so:

  either the counterexample contains FREE SETS OF EVERY SIZE —
  by size ≤ rank the root rank is infinite, and the finite-rank
  room (perfect clique worlds at the root) closes for good;

  or the sizes stabilize at some s ≥ 1, equal-length sublist
  embeddings become FULL pointwise dominations, and beyond some
  point the spine shells march in lockstep: s parallel strictly
  increasing columns, the enemy's freedom supply reduced to an
  s-lane highway.

Next session's first moves: (i) the mechanical corollary that
branch 1 forces infinite root rank (free_set_card_le_rank);
(ii) extract the s parallel lineage columns in the lockstep
branch (per-coordinate spine_lineage); (iii) confront the s-lane
highway with the cap suite — s is a FIXED finite constant
carrying the entire freedom supply of the enemy beyond the
stabilization point, and every duty, conflict, and tax law now
applies to a bounded-width object.

**Addendum (`lockstep_columns`, 22:01).**  The lockstep branch
is now a function: s strictly increasing columns whose values
tile every late spine shell exactly.  Every later column value
guards every earlier shell (hierarchical guardianship), so the
s-lane highway carries a duty ledger of uniform width s + 1 —
uniformly fragile targets, ≤ 3 sharers per shell-target, ≤ 18
shells per target, tax-line heights.  The highway versus the
ledger is next session's lockstep endgame; the ω-rank branch is
its sibling.

## 23. THE ANCHOR AUDIT (22:16) — honesty and rescue

**Audit (probe_anchor.py).**  The Cantor world has NO anchors:
carry-freeness makes every double 2c central-only (all 64
positives in-window), so `hanchor` fails for every g.  Every
anchor-conditioned theorem — the rotating-guardian kill,
cofinite free singletons, the shell stratification, the depth
tax, the spine arc, `the_encirclement`'s pillars (1) and (3) —
silently excludes carry-free worlds.  (Anchor-free theorems are
unaffected: the four rooms, the ω-pinch, r₂-unbounded, the cap
suite, the floods.)

**Rescue (`anchor_dichotomy`, `no_anchor_doubles_thin`).**  The
failure mode is itself a weapon: either anchors exist and the
whole machinery applies, or a single g₀ routes every noncentral
double-decomposition — every double 2c is a two-element pair
hub {c, g₀}, giving r₂ ≤ 3 at the EXPLICIT one-parameter family
2·A, and (with anchor-free r₂-unboundedness) blown targets avoid
the doubled basis entirely.  No counterexample escapes both
branches: anchored enemies face the shells and the spine;
anchor-free enemies carry a universal pinned crystal family at
their own doubles.  Next session: mine the g₀-branch (the
universal double-hub family against the conflict law and the
caps — g₀ is ONE element serving every double, the strongest
concentration the campaign has ever forced).

**Addendum (22:19): the anchor trichotomy completed.**
`no_anchor_central_or_member` + `central_branch_singleton_hubs`:
the no-anchor branch splits again — the router g₀ is a basis
element, or doubles are PURELY CENTRAL and every element
pair-owns its double ({c} a singleton pair hub at 2c).  In the
central branch every deletion B fails at order 2 exactly on 2·B:
the campaign's first TOTAL placement law — zero order-2 target
liberty.  The full anchor trichotomy: anchored (shells + spine
apply) / g₀-routed (universal two-element double-hubs through
one basis element) / central (total pinning; carry-free worlds).
The carry-free enemy's only remaining freedom is nonzero triples
over pinned pair-ruins — next session's sharpest anchor-side
question: can order-3 nonzero-triple liberty alone sustain hfail
when order-2 life is totally pinned?

**Addendum (`central_branch_no_three_AP`, 22:23).**  Centrality
is exactly midpoint-freeness: the central enemy contains no
nontrivial 3-term arithmetic progression with positive
non-router middle.  The carry-free counterexample candidate is
thus a Salem–Spencer-type object — progression-free yet
covering, exactly the window Behrend's construction leaves open
(AP3-free density ≫ √n).  The anchor trichotomy's central
branch now reads: total order-2 pinning + automatic minimality +
progression-freeness; its order-3 residue (nonzero triples of
doubles: diagonals, or pairs with odd sum or non-basis midpoint)
is the entire remaining freedom of that world.

## 24. THE CANONICAL GRID (22:31)

**`canonical_deletion_obligation`.**  Every infinite slice of
the basis (any property P) generates an enemy-independent
obligation: cofinal targets whose every representation uses a
P-element.  The residue grid {r mod m} is the canonical opening
book.

**`grid_cap_three_classes`.**  At most three residue obligations
per modulus fire at one target (a rep has three parts, each with
one residue).  Since late coverage forces A's residue support
mod m to have width ≳ √m, the enemy's schedule against the
m-row must spread over ≳ √m/3 distinct cofinal target streams —
for every m simultaneously.  The obligation grid is the
alignment battle line weaponized: the enemy's failure schedule
against all congruence slices is itself a congruence-indexed
object of unbounded width.
