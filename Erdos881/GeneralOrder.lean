/-
# Erdős 881 at general order

`Erdos881/FreeRank.lean` settles the problem at order two.  The published
problem (erdosproblems.com/881) quantifies over *every* order `k`:

> Let `A ⊆ ℕ` be an additive basis of order `k` which is minimal, in the
> sense that if `B ⊆ A` is any infinite set then `A ∖ B` is not a basis of
> order `k`.  Must there exist an infinite `B ⊆ A` such that `A ∖ B` is a
> basis of order `k + 1`?

This module supplies the layer that is uniform in `k`:

* order monotonicity of exact asymptotic bases
  (`IsExactTupleAsymptoticBasis.of_le`), iterating the existing padding
  lemma `IsExactTupleAsymptoticBasis.succ`;
* the degenerate order `k = 0` (vacuous) and the order `k = 1` case;
* the full conclusion at **every** `k ≥ 2` for those `A` which happen to be
  exact order-two bases, by transporting the order-two engine upward;
* the resulting reduction (`erdos881_general_of_hardCase`): the only case of
  Erdős 881 still open is `k ≥ 3` with `A` *not* an exact order-two basis.
-/
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

/-- **Erdős 881 at every order `k ≥ 2`, for exact order-two bases.**  The
order-two deletion survives at order three, hence at every order `≥ 3`. -/
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

/-- **Order one, unconditionally.**  An exact order-one asymptotic basis
contains every sufficiently large integer.  Deleting the progression
`N + 4 + 2ℕ` leaves an exact order-two basis: that progression contains no
two consecutive integers, so of the two splittings `n = N + (n-N)` and
`n = (N+1) + (n-N-1)` at least one has both parts surviving.

As at order two, the minimality hypothesis is not needed. -/
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

/-- **The precise remaining gap in Erdős 881.**

Orders `0`, `1`, `2` are settled outright, and at every order the exact
order-two bases are settled.  Consequently the whole problem follows from
the single remaining family of cases: order `k ≥ 3` with `A` not an exact
order-two basis. -/
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

/-- **State of Erdős 881 after this development.**

Orders `0`, `1` and `2` are settled outright; and at *every* order `k ≥ 2`
the problem is settled for all `A` which are exact order-two bases.  In each
settled case the minimality hypothesis is never used: the conclusion holds
for every exact basis of the relevant order. -/
theorem erdos881_settled_cases :
    Erdos881At 0 ∧ Erdos881At 1 ∧ Erdos881At 2 ∧
      ∀ k, 2 ≤ k → ∀ A : Set ℕ, IsExactTupleAsymptoticBasis A 2 →
        ∃ B, B ⊆ A ∧ B.Infinite ∧
          IsExactTupleAsymptoticBasis (A \ B) (k + 1) :=
  ⟨erdos881_at_zero, erdos881_at_one, erdos881_at_two,
    fun _ hk _ h2 => exists_infiniteDeletion_succBasis_of_basisTwo hk h2⟩

end Erdos881
