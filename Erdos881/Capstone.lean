import Erdos881.RedundantVertexKill
import Erdos881.NonEssentialKill
import Erdos881.FunnelTrichotomy

/-!
# Capstone: the interfaces refute counterexamplehood

The verified campaign in one theorem.  A counterexample to Erdős 881
(k = 2) — an infinite covering set with zero, every infinite deletion
of which breaks the exact order-three basis property — cannot satisfy
the four remaining interfaces:

* **no cofinal diffuse destruction** (Link A, `hnodiffuse`),
* **anchor abundance** (`hanchor`),
* **no cofinal zero-guardianship** (`hzero`),
* **no infinite clique of self-scale 2-guardians** (Link B1, `hB1`).

Under those, the machinery manufactures a surviving infinite deletion,
contradicting counterexamplehood directly.  All open content of the
problem's positive direction now lives in the four named hypotheses.
-/

namespace Erdos881

/-- **The capstone.**  The four interfaces refute the counterexample
property outright. -/
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
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A) ∧
      ∀ u ∈ L, 0 < u → N₀ ≤ u → ∀ N₁, N₁ ≤ u →
        ¬ TwoRedundant A u N₁) :
    False := by
  have hfunnel :=
    hasCofinalPairFunnels_of_diffuse_free h0 hcov hfail hnodiffuse
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    erdos881_positive_conditional hA h0 hcov hfunnel hanchor hzero hB1
  exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)

/-- **The capstone, sharpest form.**  With doubling supply and one
nonzero package, the interfaces shrink to: no cofinal diffuse
destruction (Link A), no cofinal zero-guardianship, and no infinite
clique of vertices that are each primitive or fully 2-essential
(Link B1, the Grekos class plus primitives). -/
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
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A) ∧
      ∀ u ∈ L, 0 < u →
        (¬ ∃ s ∈ A, ∃ t ∈ A, s + t = u ∧ s ≠ u ∧ t ≠ u) ∨
        (∀ N₁, ¬ TwoRedundant A u N₁)) :
    False := by
  have hfunnel :=
    hasCofinalPairFunnels_of_diffuse_free h0 hcov hfail hnodiffuse
  rcases erdos881_grand_assembly₄ hA h0 hcov hfunnel hdb hnz with
    h | h | h
  · obtain ⟨B, hBA, hBinf, hsurv⟩ := h
    exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)
  · exact absurd h hzero
  · exact absurd h hB1

/-- **The capstone, fifth form**: the W-alignment interfaces refute
counterexamplehood.  No redundancy hypothesis appears anywhere. -/
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
    (hB1 : ¬ ∃ L, L ⊆ A ∧ L.Infinite ∧ L.Pairwise (TeamEdge A) ∧
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
    hasCofinalPairFunnels_of_diffuse_free h0 hcov hfail hnodiffuse
  rcases erdos881_grand_assembly₅ hA h0 hcov hfunnel hdb hnz with
    h | h | h
  · obtain ⟨B, hBA, hBinf, hsurv⟩ := h
    exact hfail B hBA hBinf (exactTupleBasis_diff_of_survival hsurv)
  · exact absurd h hzero
  · exact absurd h hB1

end Erdos881
