import Erdos881.RedundantVertexKill
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

end Erdos881
