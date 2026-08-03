import Erdos881.RedundantVertexKill
import Erdos881.NonEssentialKill
import Erdos881.FunnelTrichotomy

namespace Erdos881

theorem erdos881_interfaces_refute_counterexample
    {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)))
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hzero : ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        ¬ TwoRedundant A u N₁) :
    False := by
  have hfunnel :=
    hasCofinalPairTransversalFamilies_of_diffuse_free h0 hcov hfail hnodiffuse
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    erdos881_positive_conditional hA h0 hcov hfunnel hanchor hzero hB1
  exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)

theorem erdos881_interfaces_refute_counterexample'
    {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)))
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w')
    (hzero : ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ N₁, ¬ TwoRedundant A u N₁)) :
    False := by
  have hfunnel :=
    hasCofinalPairTransversalFamilies_of_diffuse_free h0 hcov hfail hnodiffuse
  rcases erdos881_combined_criterion₄ hA h0 hcov hfunnel hdb hnz with
    h | h | h
  · obtain ⟨B, hBA, hBinf, hsurv⟩ := h
    exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)
  · exact absurd h hzero
  · exact absurd h hB1

theorem erdos881_interfaces_refute_counterexample''
    {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)))
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w')
    (hzero : ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ c, c ∈ A → 2 * c ∈ A → u < c →
          (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
          (¬ ∃ s ∈ A, ∃ t ∈ A,
            s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
        (∃ K, ∀ v m, K < v → u < v → v ≤ m →
          IsPairDestroyer A u v m →
          m - v ≤ K ∨
          ¬ ∃ s ∈ A, ∃ t ∈ A,
            s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)) :
    False := by
  have hfunnel :=
    hasCofinalPairTransversalFamilies_of_diffuse_free h0 hcov hfail hnodiffuse
  rcases erdos881_combined_criterion₅ hA h0 hcov hfunnel hdb hnz with
    h | h | h
  · obtain ⟨B, hBA, hBinf, hsurv⟩ := h
    exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)
  · exact absurd h hzero
  · exact absurd h hB1

theorem erdos881_interfaces_refute_counterexample₆
    {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)))
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w')
    (hzero : ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        ((∀ N₁, ¬ TwoRedundant A u N₁) ∧
          ((∀ c, c ∈ A → 2 * c ∈ A → u < c →
            (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
            (¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
          (∃ K, ∀ v m, K < v → u < v → v ≤ m →
            IsPairDestroyer A u v m →
            m - v ≤ K ∨
            ¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)))) :
    False := by
  have hfunnel :=
    hasCofinalPairTransversalFamilies_of_diffuse_free h0 hcov hfail hnodiffuse
  rcases erdos881_combined_criterion₆ hA h0 hcov hfunnel hdb hnz with
    h | h | h
  · obtain ⟨B, hBA, hBinf, hsurv⟩ := h
    exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)
  · exact absurd h hzero
  · exact absurd h hB1

theorem erdos881_interfaces_refute_counterexample₇
    {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)))
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w')
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (PairTransversalEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        ((∀ N₁, ¬ TwoRedundant A u N₁) ∧
          ((∀ c, c ∈ A → 2 * c ∈ A → u < c →
            (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u + c ∧ s ≠ u ∧ t ≠ u) ∨
            (¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + 2 * c ∧ s ≠ u ∧ t ≠ u)) ∨
          (∃ K, ∀ v m, K < v → u < v → v ≤ m →
            IsPairDestroyer A u v m →
            m - v ≤ K ∨
            ¬ ∃ s ∈ A, ∃ t ∈ A,
              s + t = u + (m - v) ∧ s ≠ u ∧ t ≠ u)))) :
    False :=
  erdos881_interfaces_refute_counterexample₆ hA h0 hcov hfail
    hnodiffuse hdb hnz (not_zero_residue_of_doubling hcov hdb) hB1

end Erdos881
