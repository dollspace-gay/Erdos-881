import Erdos881.FreeRank

namespace Erdos881

/-! ## Order monotonicity -/

/-- Exact asymptotic bases are monotone in the order: pad a representation
with repeated copies of one fixed basis element. -/
theorem IsExactTupleAsymptoticBasis.of_le {A : Set ℕ} {h h' : ℕ}
    (hle : h ≤ h') (hA : IsExactTupleAsymptoticBasis A h) :
    IsExactTupleAsymptoticBasis A h' := by
  induction h', hle using Nat.le_induction with
  | base => exact hA
  | succ m _ ih => exact ih.succ

/-! ## The order-two engine without a zero hypothesis -/

/-- The order-two engine of `FreeRank`, stated for an arbitrary exact
order-two basis: the `0 ∈ A` hypothesis is discharged by translating `A`
down by its minimum. -/
theorem exists_infiniteDeletion_threeBasis_of_basisTwo
    {A : Set ℕ} (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hAne : A.Nonempty := hbasis.infinite.nonempty
  set a := sInf A with ha
  have haA : a ∈ A := Nat.sInf_mem hAne
  have halower : ∀ x ∈ A, a ≤ x := fun x hx => Nat.sInf_le hx
  have hnorm : IsExactTupleAsymptoticBasis (normalizeNatSet a A) 2 :=
    exactTupleBasis_normalizeNatSet halower hbasis
  obtain ⟨N₀, hcov⟩ := pairCovers_of_exactTupleBasis hnorm
  obtain ⟨C, hCsub, hCinf, hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_pairCovers
      (zero_mem_normalizeNatSet haA) hcov
  refine ⟨translateNatSet a C, translateNatSet_subset hCsub,
    translateNatSet_infinite hCinf, ?_⟩
  rw [← normalizeNatSet_diff_translateNatSet (a := a) (A := A) (C := C)]
    at hthree
  exact exactTupleBasis_of_normalizeNatSet hthree

theorem exists_infiniteDeletion_succBasis_of_basisTwo
    {A : Set ℕ} {k : ℕ} (hk : 2 ≤ k)
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hBinf, hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_basisTwo hbasis
  exact ⟨B, hBA, hBinf, hthree.of_le (by omega)⟩

/-! ## The general-order statement -/

/-- Erdős 881 at order `k`: every strongly minimal exact order-`k` basis has
an infinite subset whose deletion leaves an exact order-`(k+1)` basis. -/
def Erdos881At (k : ℕ) : Prop :=
  ∀ A : Set ℕ, IsStronglyMinimalExactBasis A k →
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1)

/-- Order `0` is vacuous: no set is an exact order-zero asymptotic basis,
since the empty sum is `0`. -/
theorem erdos881_at_zero : Erdos881At 0 := by
  intro A hmin
  obtain ⟨N, hN⟩ := hmin.1
  obtain ⟨v, -, hsum⟩ := hN (N + 1) (by omega)
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  omega

theorem exists_infiniteDeletion_twoBasis_of_basisOne
    {A : Set ℕ} (hbasis : IsExactTupleAsymptoticBasis A 1) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 2 := by
  obtain ⟨N, hN⟩ := hbasis
  have hmem : ∀ n, N ≤ n → n ∈ A := by
    intro n hn
    obtain ⟨v, hv, hsum⟩ := hN n hn
    have hv0 : v 0 = n := by rw [← hsum, Fin.sum_univ_one]
    exact hv0 ▸ hv 0
  refine ⟨Set.range (fun i : ℕ => N + 4 + 2 * i), ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    refine hmem _ ?_
    show N ≤ N + 4 + 2 * i
    omega
  · apply Set.infinite_range_of_injective
    intro i j hij
    have hij' : N + 4 + 2 * i = N + 4 + 2 * j := hij
    omega
  · refine ⟨2 * N + 8, fun n hn => ?_⟩
    by_cases hcase : (n - N) ∈ Set.range (fun i : ℕ => N + 4 + 2 * i)
    · obtain ⟨i₀, hi₀⟩ := hcase
      have hi₀' : N + 4 + 2 * i₀ = n - N := hi₀
      have hx : N + 1 ∈ A \ Set.range (fun i : ℕ => N + 4 + 2 * i) := by
        refine ⟨hmem _ (by omega), ?_⟩
        rintro ⟨j, hj⟩
        have hj' : N + 4 + 2 * j = N + 1 := hj
        omega
      have hy : n - N - 1 ∈ A \ Set.range (fun i : ℕ => N + 4 + 2 * i) := by
        refine ⟨hmem _ (by omega), ?_⟩
        rintro ⟨j, hj⟩
        have hj' : N + 4 + 2 * j = n - N - 1 := hj
        omega
      refine ⟨![N + 1, n - N - 1], ?_, ?_⟩
      · intro i
        fin_cases i <;> assumption
      · rw [Fin.sum_univ_two]
        show N + 1 + (n - N - 1) = n
        omega
    · have hx : N ∈ A \ Set.range (fun i : ℕ => N + 4 + 2 * i) := by
        refine ⟨hmem _ le_rfl, ?_⟩
        rintro ⟨j, hj⟩
        have hj' : N + 4 + 2 * j = N := hj
        omega
      have hy : n - N ∈ A \ Set.range (fun i : ℕ => N + 4 + 2 * i) :=
        ⟨hmem _ (by omega), hcase⟩
      refine ⟨![N, n - N], ?_, ?_⟩
      · intro i
        fin_cases i <;> assumption
      · rw [Fin.sum_univ_two]
        show N + (n - N) = n
        omega

/-- Order `1`. -/
theorem erdos881_at_one : Erdos881At 1 :=
  fun _ hmin => exists_infiniteDeletion_twoBasis_of_basisOne hmin.1

/-- Order `2`: the main theorem of the repository. -/
theorem erdos881_at_two : Erdos881At 2 := erdos881

/-- At order `k ≥ 2` the problem reduces to sets which are not themselves
exact order-two bases. -/
theorem erdos881_at_of_hardCase {k : ℕ} (hk : 2 ≤ k)
    (hhard : ∀ A : Set ℕ, IsStronglyMinimalExactBasis A k →
      ¬ IsExactTupleAsymptoticBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    Erdos881At k := by
  intro A hmin
  by_cases h2 : IsExactTupleAsymptoticBasis A 2
  · exact exists_infiniteDeletion_succBasis_of_basisTwo hk h2
  · exact hhard A hmin h2

theorem erdos881_general_of_hardCase
    (hhard : ∀ k, 3 ≤ k → ∀ A : Set ℕ, IsStronglyMinimalExactBasis A k →
      ¬ IsExactTupleAsymptoticBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) (k + 1)) :
    ∀ k, Erdos881At k := by
  intro k
  match k with
  | 0 => exact erdos881_at_zero
  | 1 => exact erdos881_at_one
  | 2 => exact erdos881_at_two
  | (n + 3) =>
      exact erdos881_at_of_hardCase (by omega) (hhard (n + 3) (by omega))

theorem erdos881_settled_cases :
    Erdos881At 0 ∧ Erdos881At 1 ∧ Erdos881At 2 ∧
      ∀ k, 2 ≤ k → ∀ A : Set ℕ, IsExactTupleAsymptoticBasis A 2 →
        ∃ B, B ⊆ A ∧ B.Infinite ∧
          IsExactTupleAsymptoticBasis (A \ B) (k + 1) :=
  ⟨erdos881_at_zero, erdos881_at_one, erdos881_at_two,
    fun _ hk _ h2 => exists_infiniteDeletion_succBasis_of_basisTwo hk h2⟩

end Erdos881
