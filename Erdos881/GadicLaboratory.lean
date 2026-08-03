import Erdos881.SuccessorEssentialCore

open scoped BigOperators

namespace Erdos881

/-- A two-term canonical representation lifts to three retained terms when
at most one canonical summand is deleted and every deleted summand can be
split into two retained summands. -/
theorem exactThreeBasis_of_canonicalPairs_and_splittableDeletion
    {A B : Set ℕ}
    (hzero : 0 ∈ A \ B)
    (hcanonical : ∀ n, ∃ x y,
      x ∈ A ∧ y ∈ A ∧ x + y = n ∧ ¬ (x ∈ B ∧ y ∈ B))
    (hsplit : ∀ b ∈ A, b ∈ B →
      ∃ u v, u ∈ A \ B ∧ v ∈ A \ B ∧ u + v = b) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨0, ?_⟩
  intro n _hn
  obtain ⟨x, y, hxA, hyA, hxy, hnotBoth⟩ := hcanonical n
  by_cases hxB : x ∈ B
  · have hyB : y ∉ B := by
      intro hyB
      exact hnotBoth ⟨hxB, hyB⟩
    obtain ⟨u, v, hu, hv, huv⟩ := hsplit x hxA hxB
    refine ⟨![u, v, y], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [hu, hv, hyA, hyB]
    · simp [Fin.sum_univ_succ]
      omega
  · by_cases hyB : y ∈ B
    · obtain ⟨u, v, hu, hv, huv⟩ := hsplit y hyA hyB
      refine ⟨![x, u, v], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hxA, hxB, hu, hv]
      · simp [Fin.sum_univ_succ]
        omega
    · refine ⟨![0, x, y], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hzero, hxA, hxB, hyA, hyB]
      · simp [Fin.sum_univ_succ]
        omega

/-! ## Canonical binary parity parts -/

/-- The part of `n` supported on even binary positions, written recursively
in base four. -/
def evenBitPart : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + 4 * evenBitPart ((n + 1) / 4)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_succ n) (by omega)

/-- The part of `n` supported on odd binary positions. -/
def oddBitPart : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * (((n + 1) / 2) % 2) +
      4 * oddBitPart ((n + 1) / 4)
termination_by n => n
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_succ n) (by omega)

/-- Splitting binary digits by parity is an exact additive decomposition. -/
theorem evenBitPart_add_oddBitPart (n : ℕ) :
    evenBitPart n + oddBitPart n = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [evenBitPart, oddBitPart]
      | succ n =>
          rw [evenBitPart, oddBitPart]
          have hrec := ih ((n + 1) / 4)
            (Nat.div_lt_self (Nat.zero_lt_succ n) (by omega))
          omega

/-- Multiplication by four shifts both parity parts by two binary places. -/
@[simp] theorem evenBitPart_four_mul (n : ℕ) :
    evenBitPart (4 * n) = 4 * evenBitPart n := by
  cases n with
  | zero => simp [evenBitPart]
  | succ n =>
      rw [show 4 * (n + 1) = (4 * n + 3) + 1 by omega,
        evenBitPart]
      have hdiv : (4 * n + 3 + 1) / 4 = n + 1 := by omega
      have hmod : (4 * n + 3 + 1) % 2 = 0 := by omega
      rw [hdiv, hmod]
      omega

@[simp] theorem oddBitPart_four_mul (n : ℕ) :
    oddBitPart (4 * n) = 4 * oddBitPart n := by
  cases n with
  | zero => simp [oddBitPart]
  | succ n =>
      rw [show 4 * (n + 1) = (4 * n + 3) + 1 by omega,
        oddBitPart]
      have hdiv : (4 * n + 3 + 1) / 4 = n + 1 := by omega
      have hlow : ((4 * n + 3 + 1) / 2) % 2 = 0 := by omega
      rw [hdiv, hlow]
      omega

@[simp] theorem evenBitPart_one : evenBitPart 1 = 1 := by
  simp [evenBitPart]

@[simp] theorem oddBitPart_two : oddBitPart 2 = 2 := by
  simp [oddBitPart]

@[simp] theorem evenBitPart_four_pow (j : ℕ) :
    evenBitPart (4 ^ j) = 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, Nat.mul_comm, evenBitPart_four_mul, ih]

@[simp] theorem oddBitPart_two_mul_four_pow (j : ℕ) :
    oddBitPart (2 * 4 ^ j) = 2 * 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have heq : 2 * (4 ^ j * 4) = 4 * (2 * 4 ^ j) := by ring
      rw [heq, oddBitPart_four_mul, ih]

@[simp] theorem oddBitPart_mod_two (n : ℕ) :
    oddBitPart n % 2 = 0 := by
  cases n with
  | zero => simp [oddBitPart]
  | succ n =>
      rw [oddBitPart]
      omega

theorem oddBitPart_div_four (n : ℕ) :
    oddBitPart n / 4 = oddBitPart (n / 4) := by
  cases n with
  | zero => simp [oddBitPart]
  | succ n =>
      rw [oddBitPart]
      have hlow : 2 * (((n + 1) / 2) % 2) < 4 := by omega
      omega

/-- An odd-position binary digit part is never a pure even-position power. -/
theorem oddBitPart_ne_four_pow (n j : ℕ) :
    oddBitPart n ≠ 4 ^ j := by
  induction j generalizing n with
  | zero =>
      intro h
      have hmod := oddBitPart_mod_two n
      simp at h
      omega
  | succ j ih =>
      intro h
      have hdiv := congrArg (fun z : ℕ => z / 4) h
      change oddBitPart n / 4 = 4 ^ (j + 1) / 4 at hdiv
      rw [oddBitPart_div_four] at hdiv
      have hpdiv : 4 ^ (j + 1) / 4 = 4 ^ j := by
        rw [pow_succ]
        omega
      rw [hpdiv] at hdiv
      exact ih (n / 4) hdiv

/-- The completed binary g-adic basis: all even-position digit parts and all
odd-position digit parts, including `0`. -/
def completedBinaryGadicBasis : Set ℕ :=
  Set.range evenBitPart ∪ Set.range oddBitPart

/-- Delete the positive pure powers in the even binary positions, retaining
`1` so that the bottom of the recursion has no exceptional case. -/
def positiveEvenPowerDeletion : Set ℕ :=
  {b | ∃ j, b = 4 ^ (j + 1)}

theorem positiveEvenPowerDeletion_infinite :
    positiveEvenPowerDeletion.Infinite := by
  have hrange : Set.range (fun j : ℕ => 4 ^ (j + 1)) =
      positiveEvenPowerDeletion := by
    ext b
    simp [positiveEvenPowerDeletion, eq_comm]
  rw [← hrange]
  apply Set.infinite_range_of_injective
  intro i j hij
  exact Nat.succ.inj <| Nat.pow_right_injective (by omega) hij

theorem positiveEvenPowerDeletion_subset_basis :
    positiveEvenPowerDeletion ⊆ completedBinaryGadicBasis := by
  intro b hb
  obtain ⟨j, rfl⟩ := hb
  left
  exact ⟨4 ^ (j + 1), by simp⟩

theorem oddBitPart_not_mem_positiveEvenPowerDeletion (n : ℕ) :
    oddBitPart n ∉ positiveEvenPowerDeletion := by
  rintro ⟨j, hj⟩
  exact oddBitPart_ne_four_pow n (j + 1) hj

theorem positiveEvenPowerDeletion_splits_in_complement
    (b : ℕ) (hbA : b ∈ completedBinaryGadicBasis)
    (hbB : b ∈ positiveEvenPowerDeletion) :
    ∃ u v,
      u ∈ completedBinaryGadicBasis \ positiveEvenPowerDeletion ∧
      v ∈ completedBinaryGadicBasis \ positiveEvenPowerDeletion ∧
      u + v = b := by
  obtain ⟨j, rfl⟩ := hbB
  let u := 2 * 4 ^ j
  refine ⟨u, u, ?_, ?_, ?_⟩
  · constructor
    · right
      exact ⟨u, by simp [u]⟩
    · simpa [u] using oddBitPart_not_mem_positiveEvenPowerDeletion u
  · constructor
    · right
      exact ⟨u, by simp [u]⟩
    · simpa [u] using oddBitPart_not_mem_positiveEvenPowerDeletion u
  · dsimp only [u]
    rw [pow_succ]
    ring

theorem completedBinaryGadicBasis_exactOrderTwo :
    IsExactTupleAsymptoticBasis completedBinaryGadicBasis 2 := by
  refine ⟨0, ?_⟩
  intro n _hn
  refine ⟨![evenBitPart n, oddBitPart n], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inl ⟨n, rfl⟩
    · exact Or.inr ⟨n, rfl⟩
  · simpa [Fin.sum_univ_two] using evenBitPart_add_oddBitPart n

theorem completedBinaryGadicBasis_diff_positiveEvenPowers_exactOrderThree :
    IsExactTupleAsymptoticBasis
      (completedBinaryGadicBasis \ positiveEvenPowerDeletion) 3 := by
  apply exactThreeBasis_of_canonicalPairs_and_splittableDeletion
  · constructor
    · left
      exact ⟨0, by simp [evenBitPart]⟩
    · rintro ⟨j, hj⟩
      have hpos : 0 < 4 ^ (j + 1) := pow_pos (by omega) _
      omega
  · intro n
    refine ⟨evenBitPart n, oddBitPart n, ?_, ?_,
      evenBitPart_add_oddBitPart n, ?_⟩
    · left
      exact ⟨n, rfl⟩
    · right
      exact ⟨n, rfl⟩
    · intro hboth
      exact oddBitPart_not_mem_positiveEvenPowerDeletion n hboth.2
  · exact positiveEvenPowerDeletion_splits_in_complement

theorem exists_binaryGadic_infiniteDeletion_exactTwo_to_exactThree :
    ∃ A B : Set ℕ,
      IsExactTupleAsymptoticBasis A 2 ∧
      B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  exact ⟨completedBinaryGadicBasis, positiveEvenPowerDeletion,
    completedBinaryGadicBasis_exactOrderTwo,
    positiveEvenPowerDeletion_subset_basis,
    positiveEvenPowerDeletion_infinite,
    completedBinaryGadicBasis_diff_positiveEvenPowers_exactOrderThree⟩

end Erdos881
