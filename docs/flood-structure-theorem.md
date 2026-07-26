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
