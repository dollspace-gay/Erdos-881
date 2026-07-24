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

end Erdos881
