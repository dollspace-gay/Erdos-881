/-
# The Cantor instance in the campaign's vocabulary

`erdos881_cantor_full_instance` restates the verified Cantor world in
the repository's own basis language (`IsExactTupleAsymptoticBasis`):

* the Cantor set is an exact asymptotic basis of order 2;
* it is ℵ₀-minimal — every infinite deletion destroys order 2;
* the pure powers are an infinite subset whose deletion leaves an
  exact asymptotic basis of order 3.

This is the conclusion pattern of Erdős 881 (k = 2), machine-verified
end to end on a concrete minimal basis, in the exact predicate the
main contradiction-mining development uses for its counterexample
interfaces.
-/

import Erdos881.CantorCarryRepair
import Erdos881.AdditiveSupports

namespace Erdos881Cantor

open Erdos881

/-- The Cantor basis as a set. -/
def CantorSet : Set ℕ := {n | IsCantor n}

/-- The deleted scale markers. -/
def PurePowers : Set ℕ := {n | ∃ k, n = 3 ^ k}

lemma purePowers_subset : PurePowers ⊆ CantorSet := by
  rintro x ⟨k, rfl⟩
  exact isCantor_pow k

lemma purePowers_infinite : PurePowers.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => 3 ^ k) (Nat.pow_right_injective (by norm_num))
  intro k
  exact ⟨k, rfl⟩

/-- Order-2: the Cantor set is an exact asymptotic basis of order 2
(indeed with threshold 0). -/
theorem cantorSet_basis_two :
    IsExactTupleAsymptoticBasis CantorSet 2 := by
  refine ⟨0, fun n _ => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := cantor_pair_basis n
  refine ⟨![a, b], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · simpa [Fin.sum_univ_two] using hab

/-- Minimality: deleting any infinite subset of the Cantor set
destroys the order-2 basis property — each deleted element's double
loses its unique representation. -/
theorem cantorSet_minimal_two {B : Set ℕ} (hBsub : B ⊆ CantorSet)
    (hBinf : B.Infinite) :
    ¬IsExactTupleAsymptoticBasis (CantorSet \ B) 2 := by
  rintro ⟨N, hN⟩
  obtain ⟨b, hbB, hbN⟩ := hBinf.exists_gt N
  have hb2 : N ≤ 2 * b := by omega
  obtain ⟨v, hv, hsum⟩ := hN (2 * b) hb2
  have h0 := hv 0
  have h1 := hv 1
  obtain ⟨hc0, hnB0⟩ := h0
  obtain ⟨hc1, hnB1⟩ := h1
  have hs : v 0 + v 1 = 2 * b := by
    simpa [Fin.sum_univ_two] using hsum
  obtain ⟨he0, _⟩ := cantor_double_unique (hBsub hbB) hc0 hc1 hs
  exact hnB0 (he0 ▸ hbB)

/-- Order-3 survival: deleting the pure powers leaves an exact
asymptotic basis of order 3. -/
theorem cantorSet_deletion_basis_three :
    IsExactTupleAsymptoticBasis (CantorSet \ PurePowers) 3 := by
  refine ⟨3 ^ 7, fun n hn => ?_⟩
  obtain ⟨x, y, z, hx, hy, hz, hpx, hpy, hpz, hs⟩ :=
    cantor_deletion_order_three n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hx, fun ⟨j, hj⟩ => hpx j hj⟩
    · exact ⟨hy, fun ⟨j, hj⟩ => hpy j hj⟩
    · exact ⟨hz, fun ⟨j, hj⟩ => hpz j hj⟩
  · simpa [Fin.sum_univ_three] using hs

/-- **The full Erdős 881 pattern on the Cantor basis**, in the
repository's basis vocabulary: an ℵ₀-minimal exact order-2 basis
with an infinite deletion that survives at order 3. -/
theorem erdos881_cantor_full_instance :
    IsExactTupleAsymptoticBasis CantorSet 2 ∧
    (∀ B ⊆ CantorSet, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (CantorSet \ B) 2) ∧
    PurePowers ⊆ CantorSet ∧ PurePowers.Infinite ∧
    IsExactTupleAsymptoticBasis (CantorSet \ PurePowers) 3 :=
  ⟨cantorSet_basis_two, fun _ hsub hinf => cantorSet_minimal_two hsub hinf,
    purePowers_subset, purePowers_infinite, cantorSet_deletion_basis_three⟩

end Erdos881Cantor
