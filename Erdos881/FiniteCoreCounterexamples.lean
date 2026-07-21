import Erdos881.AdditiveSupports

/-!
# Finite fixed-order obstructions need not be essential

This file records a small periodic sanity check for finite-core absorption.
Removing a finite set can destroy one prescribed additive order while the
remaining set is still an asymptotic basis of a larger order.  Thus a
fixed-order obstruction cannot be fed directly into the finiteness theorem
for essential subsets (which concerns failure at every order).
-/

namespace Erdos881

private def residueZeroOrOneModFive : Set ℕ :=
  {n | n % 5 = 0 ∨ n % 5 = 1}

private def residueBasisWithTwoDigits : Set ℕ :=
  residueZeroOrOneModFive ∪ ({2, 3} : Set ℕ)

private def twoDigits : Finset ℕ := {2, 3}

private theorem residueBasisWithTwoDigits_orderTwo :
    IsExactTupleAsymptoticBasis residueBasisWithTwoDigits 2 := by
  refine ⟨4, ?_⟩
  intro n hn
  have hmod : n % 5 < 5 := Nat.mod_lt n (by omega)
  have hdecomp := Nat.mod_add_div n 5
  interval_cases h : n % 5
  · refine ⟨![0, n], ?_, by simp⟩
    intro i
    fin_cases i <;> simp [residueBasisWithTwoDigits,
      residueZeroOrOneModFive, h]
  · refine ⟨![0, n], ?_, by simp⟩
    intro i
    fin_cases i <;> simp [residueBasisWithTwoDigits,
      residueZeroOrOneModFive, h]
  · have hsub : (n - 1) % 5 = 1 := by omega
    refine ⟨![1, n - 1], ?_, by simp; omega⟩
    intro i
    fin_cases i <;> simp [residueBasisWithTwoDigits,
      residueZeroOrOneModFive, hsub]
  · have hsub : (n - 2) % 5 = 1 := by omega
    refine ⟨![2, n - 2], ?_, by simp; omega⟩
    intro i
    fin_cases i <;> simp [residueBasisWithTwoDigits,
      residueZeroOrOneModFive, hsub]
  · have hsub : (n - 3) % 5 = 1 := by omega
    refine ⟨![3, n - 3], ?_, by simp; omega⟩
    intro i
    fin_cases i <;> simp [residueBasisWithTwoDigits,
      residueZeroOrOneModFive, hsub]

private theorem residueZeroOrOneModFive_orderFour :
    IsExactTupleAsymptoticBasis residueZeroOrOneModFive 4 := by
  refine ⟨4, ?_⟩
  intro n hn
  have hmod : n % 5 < 5 := Nat.mod_lt n (by omega)
  have hdecomp := Nat.mod_add_div n 5
  interval_cases h : n % 5
  · refine ⟨![n, 0, 0, 0], ?_, by simp [Fin.sum_univ_succ]⟩
    intro i
    fin_cases i <;> simp [residueZeroOrOneModFive, h]
  · refine ⟨![n, 0, 0, 0], ?_, by simp [Fin.sum_univ_succ]⟩
    intro i
    fin_cases i <;> simp [residueZeroOrOneModFive, h]
  · have hsub : (n - 1) % 5 = 1 := by omega
    refine ⟨![n - 1, 1, 0, 0], ?_, by
      simp [Fin.sum_univ_succ]
      omega⟩
    intro i
    fin_cases i <;> simp [residueZeroOrOneModFive, hsub]
  · have hsub : (n - 2) % 5 = 1 := by omega
    refine ⟨![n - 2, 1, 1, 0], ?_, by
      simp [Fin.sum_univ_succ]
      omega⟩
    intro i
    fin_cases i <;> simp [residueZeroOrOneModFive, hsub]
  · have hsub : (n - 3) % 5 = 1 := by omega
    refine ⟨![n - 3, 1, 1, 1], ?_, by
      simp [Fin.sum_univ_succ]
      omega⟩
    intro i
    fin_cases i <;> simp [residueZeroOrOneModFive, hsub]

private theorem residueZeroOrOneModFive_not_orderThree :
    ¬ IsExactTupleAsymptoticBasis residueZeroOrOneModFive 3 := by
  rintro ⟨N, hN⟩
  let n := 5 * N + 4
  obtain ⟨v, hv, hvsum⟩ := hN n (by dsimp [n]; omega)
  have h0 := hv (0 : Fin 3)
  have h1 := hv (1 : Fin 3)
  have h2 := hv (2 : Fin 3)
  simp only [residueZeroOrOneModFive, Set.mem_setOf_eq] at h0 h1 h2
  have hvsum' : v 0 + (v 1 + v 2) = n := by
    simpa [Fin.sum_univ_succ] using hvsum
  rcases h0 with h0 | h0 <;>
    rcases h1 with h1 | h1 <;>
      rcases h2 with h2 | h2 <;>
        dsimp [n] at hvsum' <;> omega

private theorem diff_twoDigits_eq_residueZeroOrOneModFive :
    residueBasisWithTwoDigits \ (twoDigits : Set ℕ) =
      residueZeroOrOneModFive := by
  ext n
  simp only [residueBasisWithTwoDigits, twoDigits, Set.mem_diff,
    Set.mem_union, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn | hn, hnot⟩
    · exact hn
    · exact (hnot hn).elim
  · intro hn
    refine ⟨Or.inl hn, ?_⟩
    rintro (rfl | rfl) <;>
      simp [residueZeroOrOneModFive] at hn

/-- A basis of order two with a two-point deletion which destroys exact
order three but leaves a basis of order four.  In particular the deleted
finite set is a fixed-order obstruction, not an essential subset. -/
theorem finite_orderObstruction_not_essential_counterexample :
    ∃ A : Set ℕ, ∃ D : Finset ℕ,
      IsExactTupleAsymptoticBasis A 2 ∧
      ¬ IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) 3 ∧
      IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) 4 := by
  refine ⟨residueBasisWithTwoDigits, twoDigits,
    residueBasisWithTwoDigits_orderTwo, ?_, ?_⟩
  · rw [diff_twoDigits_eq_residueZeroOrOneModFive]
    exact residueZeroOrOneModFive_not_orderThree
  · rw [diff_twoDigits_eq_residueZeroOrOneModFive]
    exact residueZeroOrOneModFive_orderFour

end Erdos881
