import Erdos881.TeamGuardianRigidity
import Erdos881.InfinitePairRamsey

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
required elements coincide. -/
theorem IsPairDestroyer.privateTriple_of_eq {A : Set ℕ} {u m : ℕ}
    (h : IsPairDestroyer A u u m) : IsPrivateTriple A u m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' | h' | h' | h' <;> tauto

/-- A pair destroyer whose first required element lies above the target collapses
to the second required element alone: elements above `m` appear in no
representation of `m`. -/
theorem IsPairDestroyer.privateTriple_of_lt_left {A : Set ℕ} {u v m : ℕ}
    (h : IsPairDestroyer A u v m) (hm : m < u) : IsPrivateTriple A v m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' | h' | h' | h' <;> omega

/-- The pair transversal graph: `u` and `v` are joined when they are distinct and
jointly destroy some target at or above both of them. -/
def PairTransversalEdge (A : Set ℕ) (u v : ℕ) : Prop :=
  u ≠ v ∧ ∃ m, u ≤ m ∧ v ≤ m ∧ IsPairDestroyer A u v m

theorem PairTransversalEdge.symm' {A : Set ℕ} : Symmetric (PairTransversalEdge A) := by
  rintro u v ⟨hne, m, hum, hvm, hdes⟩
  exact ⟨hne.symm, m, hvm, hum, hdes.symm⟩

def HasCofinalPairTransversalFamilies (A : Set ℕ) : Prop :=
  ∀ B, B ⊆ A → B.Infinite → ∀ N, ∃ m, N ≤ m ∧
    ∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m

theorem infinite_pairTransversalClique_or_cofinal_privatePairs
    {A : Set ℕ} (hA : A.Infinite)
    (hfunnel : HasCofinalPairTransversalFamilies A) :
    (∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A)) ∨
      (∃ L, L ⊆ A ∧ L.Infinite ∧
        ∀ N, ∃ v ∈ L, ∃ m, N ≤ m ∧ IsPrivateTriple A v m) := by
  rcases infinite_pairRamsey_nat hA (PairTransversalEdge A) PairTransversalEdge.symm' with
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

def PairTransversalCliqueFree (A : Set ℕ) : Prop :=
  ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A)

theorem combined_reduction {A : Set ℕ} (hA : A.Infinite)
    (hfunnel : HasCofinalPairTransversalFamilies A)
    (hclique : PairTransversalCliqueFree A) :
    ∃ L, L ⊆ A ∧ L.Infinite ∧
      ∀ N, ∃ v ∈ L, ∃ m, N ≤ m ∧ IsPrivateTriple A v m := by
  rcases infinite_pairTransversalClique_or_cofinal_privatePairs hA hfunnel with h | h
  · exact absurd ⟨h.choose, h.choose_spec⟩ hclique
  · exact h

theorem infinite_pairTransversalClique_has_separated_triple
    {A : Set ℕ} {L : Set ℕ} (hL : L.Infinite)
    (hcl : L.Pairwise (PairTransversalEdge A)) (sep : ℕ → ℕ) :
    ∃ u ∈ L, ∃ v ∈ L, ∃ w ∈ L,
      sep 0 < u ∧ sep u < v ∧ sep v < w ∧ u < v ∧ v < w ∧
      PairTransversalEdge A u v ∧ PairTransversalEdge A u w ∧ PairTransversalEdge A v w := by
  obtain ⟨u, huL, hu⟩ := hL.exists_gt (sep 0)
  obtain ⟨v, hvL, hv⟩ := hL.exists_gt (max u (sep u))
  obtain ⟨w, hwL, hw⟩ := hL.exists_gt (max v (sep v))
  have h1 : u < v := lt_of_le_of_lt (le_max_left _ _) hv
  have h2 : sep u < v := lt_of_le_of_lt (le_max_right _ _) hv
  have h3 : v < w := lt_of_le_of_lt (le_max_left _ _) hw
  have h4 : sep v < w := lt_of_le_of_lt (le_max_right _ _) hw
  exact ⟨u, huL, v, hvL, w, hwL, hu, h2, h4, h1, h3,
    hcl huL hvL (by omega), hcl huL hwL (by omega), hcl hvL hwL (by omega)⟩

theorem no_cofinal_big_privatePairs {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hstream : ∀ N, ∃ a m, N ≤ m ∧ IsPrivateTriple A a m ∧
      m < 2 * a ∧ N₀ + a ≤ m ∧ N₀ + 3 ≤ a) :
    False := by
  obtain ⟨a₁, m₁, _, h1, hbig1, hN1, hsize⟩ := hstream N₀
  obtain ⟨a₂, m₂, hm₂, h2, hbig2, hN2, _⟩ := hstream (3 * m₁ + 1)
  have hle := h2.required_element_le h0 hcov hbig2 hN2
  exact no_big_required_element_stacking h0 hcov h1 h2 hbig1 hN1 hbig2 hN2
    hsize (by omega)

end Erdos881
