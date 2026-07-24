import Erdos881.TeamGuardianRigidity
import Erdos881.InfinitePairRamsey

/-!
# The team graph and the Ramsey dichotomy

Phase 1 of the endgame program (`docs/thin-basis-campaign.md`).  The
*team graph* of `A` has an edge between `u ≠ v` when the pair jointly
destroys some target at or above both (`TeamEdge`).  The dodge argument
is packaged as a trichotomy: if every infinite subset of `A` funnels
some arbitrarily-late destroyed target through two of its own elements
(`HasCofinalPairFunnels` — the interface that the funnel-thinning phase
must eventually discharge), then `A` carries

* an infinite clique of mutual team-guardianship, or
* an infinite set whose members own arbitrarily late *singleton*
  private targets.

The first branch is the object the interlock experiments show to be
geometrically expensive (`scripts/probe_team_interlock.py`,
`scripts/probe_triangle_construction.py`); the second feeds the
guardian-rigidity and no-stacking machinery.  Either way a
bounded-funnel counterexample is forced into killed or measurable
territory.
-/

namespace Erdos881

/-- `{u, v}` jointly destroy `m`: a representation exists and every
exact three-term representation meets the pair. -/
def IsPairDestroyer (A : Set ℕ) (u v m : ℕ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x = u ∨ y = u ∨ z = u ∨ x = v ∨ y = v ∨ z = v

theorem IsPairDestroyer.symm {A : Set ℕ} {u v m : ℕ}
    (h : IsPairDestroyer A u v m) : IsPairDestroyer A v u m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' | h' | h' | h' <;> tauto

/-- A pair destroyer collapses to a singleton private pair when the two
guards coincide. -/
theorem IsPairDestroyer.privateTriple_of_eq {A : Set ℕ} {u m : ℕ}
    (h : IsPairDestroyer A u u m) : IsPrivateTriple A u m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' | h' | h' | h' <;> tauto

/-- A pair destroyer whose first guard lies above the target collapses
to the second guard alone: elements above `m` appear in no
representation of `m`. -/
theorem IsPairDestroyer.privateTriple_of_lt_left {A : Set ℕ} {u v m : ℕ}
    (h : IsPairDestroyer A u v m) (hm : m < u) : IsPrivateTriple A v m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' | h' | h' | h' <;> omega

/-- The team graph: `u` and `v` are joined when they are distinct and
jointly destroy some target at or above both of them. -/
def TeamEdge (A : Set ℕ) (u v : ℕ) : Prop :=
  u ≠ v ∧ ∃ m, u ≤ m ∧ v ≤ m ∧ IsPairDestroyer A u v m

theorem TeamEdge.symm' {A : Set ℕ} : Symmetric (TeamEdge A) := by
  rintro u v ⟨hne, m, hum, hvm, hdes⟩
  exact ⟨hne.symm, m, hvm, hum, hdes.symm⟩

/-- The bounded-funnel interface (to be discharged by the sunflower
thinning phase): every infinite subset of `A` funnels an
arbitrarily-late destroyed target through two of its own elements. -/
def HasCofinalPairFunnels (A : Set ℕ) : Prop :=
  ∀ B, B ⊆ A → B.Infinite → ∀ N, ∃ m, N ≤ m ∧
    ∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m

/-- **Phase-1 dichotomy.**  A set with cofinal pair funnels carries an
infinite team-graph clique or an infinite set of elements owning
arbitrarily late singleton private targets. -/
theorem infinite_teamClique_or_cofinal_privatePairs
    {A : Set ℕ} (hA : A.Infinite)
    (hfunnel : HasCofinalPairFunnels A) :
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A)) ∨
      (∃ L, L ⊆ A ∧ L.Infinite ∧
        ∀ N, ∃ v ∈ L, ∃ m, N ≤ m ∧ IsPrivateTriple A v m) := by
  rcases infinite_pairRamsey_nat hA (TeamEdge A) TeamEdge.symm' with
    ⟨L, hLA, hLinf, hLcl⟩ | ⟨L, hLA, hLinf, hLind⟩
  · exact Or.inl ⟨L, hLA, hLinf, hLcl⟩
  · refine Or.inr ⟨L, hLA, hLinf, ?_⟩
    intro N
    obtain ⟨m, hm, u, hu, v, hv, hdes⟩ := hfunnel L hLA hLinf N
    rcases eq_or_ne u v with rfl | hne
    · exact ⟨u, hu, m, hm, hdes.privateTriple_of_eq⟩
    · rcases Nat.lt_or_ge m u with hmu | hmu
      · exact ⟨v, hv, m, hm, hdes.privateTriple_of_lt_left hmu⟩
      rcases Nat.lt_or_ge m v with hmv | hmv
      · exact ⟨u, hu, m, hm, hdes.symm.privateTriple_of_lt_left hmv⟩
      · exact absurd ⟨hne, m, hmu, hmv, hdes⟩ (hLind hu hv hne)

/-- **Open Link B, stated formally:** the team graph of `A` carries no
infinite clique of mutual guardianship.  Lab evidence: team graphs of
all natural bases are trees; closing edges are exhaustively unbuyable
at the base scale (`docs/thin-basis-campaign.md`). -/
def TeamCliqueFree (A : Set ℕ) : Prop :=
  ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A)

/-- **Master reduction (Phase-4 assembly, conditional form).**  Modulo
the two open links — cofinal pair funnels (Link A, to come from
sunflower thinning) and team-clique-freeness (Link B) — a counterexample
is reduced to an infinite stream of singleton private guardians, the
object the guardian-rigidity machinery kills. -/
theorem master_reduction {A : Set ℕ} (hA : A.Infinite)
    (hfunnel : HasCofinalPairFunnels A)
    (hclique : TeamCliqueFree A) :
    ∃ L, L ⊆ A ∧ L.Infinite ∧
      ∀ N, ∃ v ∈ L, ∃ m, N ≤ m ∧ IsPrivateTriple A v m := by
  rcases infinite_teamClique_or_cofinal_privatePairs hA hfunnel with h | h
  · exact absurd ⟨h.choose, h.choose_spec⟩ hclique
  · exact h

/-- **Pigeonhole half of Phase 2c.**  An infinite team clique contains
triples with arbitrarily prescribed scale separations, all three edges
included.  What remains open is `no_separated_triangle` itself: that
such a triple is contradictory.  Once that is proved, this theorem
converts it into `TeamCliqueFree`. -/
theorem infinite_teamClique_has_separated_triple
    {A : Set ℕ} {L : Set ℕ} (hL : L.Infinite)
    (hcl : L.Pairwise (TeamEdge A)) (sep : ℕ → ℕ) :
    ∃ u ∈ L, ∃ v ∈ L, ∃ w ∈ L,
      sep 0 < u ∧ sep u < v ∧ sep v < w ∧ u < v ∧ v < w ∧
      TeamEdge A u v ∧ TeamEdge A u w ∧ TeamEdge A v w := by
  obtain ⟨u, huL, hu⟩ := hL.exists_gt (sep 0)
  obtain ⟨v, hvL, hv⟩ := hL.exists_gt (max u (sep u))
  obtain ⟨w, hwL, hw⟩ := hL.exists_gt (max v (sep v))
  have h1 : u < v := lt_of_le_of_lt (le_max_left _ _) hv
  have h2 : sep u < v := lt_of_le_of_lt (le_max_right _ _) hv
  have h3 : v < w := lt_of_le_of_lt (le_max_left _ _) hw
  have h4 : sep v < w := lt_of_le_of_lt (le_max_right _ _) hw
  exact ⟨u, huL, v, hvL, w, hwL, hu, h2, h4, h1, h3,
    hcl huL hvL (by omega), hcl huL hwL (by omega), hcl hvL hwL (by omega)⟩

/-- **The big-guardian stream self-destructs.**  A stream of private
pairs with big guardians at arbitrarily late targets is contradictory:
two members at separation ratio 3 violate `no_big_guardian_stacking`,
with the separation supplied by the boundary theorem `guardian_le`. -/
theorem no_cofinal_big_privatePairs {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hstream : ∀ N, ∃ a m, N ≤ m ∧ IsPrivateTriple A a m ∧
      m < 2 * a ∧ N₀ + a ≤ m ∧ N₀ + 3 ≤ a) :
    False := by
  obtain ⟨a₁, m₁, _, h1, hbig1, hN1, hsize⟩ := hstream N₀
  obtain ⟨a₂, m₂, hm₂, h2, hbig2, hN2, _⟩ := hstream (3 * m₁ + 1)
  have hle := h2.guardian_le h0 hcov hbig2 hN2
  exact no_big_guardian_stacking h0 hcov h1 h2 hbig1 hN1 hbig2 hN2
    hsize (by omega)

end Erdos881
