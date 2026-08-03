import Erdos881.TeamGraphRamsey

namespace Erdos881

/-- Geometric growth gives strict monotonicity. -/
lemma geometric_strictMono {M : ℕ → ℕ}
    (hgrow : ∀ k, 2 * M k < M (k + 1)) (h0 : 0 < M 0) :
    StrictMono M := by
  have hpos : ∀ k, 0 < M k := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      have := hgrow k
      omega
  have hstep : ∀ k, M k < M (k + 1) := by
    intro k
    have h1 := hgrow k
    have h2 := hpos k
    omega
  exact strictMono_nat_of_lt_succ hstep

/-- Cross-scale separation: a lower scale sits strictly below the next
scale minus any bounded offset. -/
lemma geometric_separation {M : ℕ → ℕ} {c : ℕ}
    (hgrow : ∀ k, 2 * M k < M (k + 1)) (hbig : c < M 0) :
    ∀ j k, j < k → M j + c < M k := by
  intro j k hjk
  have hmono : StrictMono M :=
    geometric_strictMono hgrow (by omega)
  have h1 : 2 * M j < M (j + 1) := hgrow j
  have h2 : M (j + 1) ≤ M k := hmono.monotone hjk
  have h3 : M 0 ≤ M j := hmono.monotone (Nat.zero_le j)
  omega

theorem marker_repair_distinct {u v : ℕ}
    (hu0 : 0 < u) (huv : u < v)
    (M : ℕ → ℕ) (hgrow : ∀ k, 2 * M k < M (k + 1))
    (hbig : 4 * v < M 0) :
    ∀ j k, M j - u ≠ M k - 2 * u ∧ M j - u ≠ M k - u - v ∧
      M j - u ≠ M k - v := by
  intro j k
  have hmono : StrictMono M := geometric_strictMono hgrow (by omega)
  have hMj : 4 * v < M j := by
    have := hmono.monotone (Nat.zero_le j); omega
  have hMk : 4 * v < M k := by
    have := hmono.monotone (Nat.zero_le k); omega
  rcases Nat.lt_trichotomy j k with h | h | h
  · have hsep : M j + 4 * v < M k :=
      geometric_separation hgrow (by omega) j k h
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · subst h
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · have hsep : M k + 4 * v < M j :=
      geometric_separation hgrow (by omega) k j h
    refine ⟨?_, ?_, ?_⟩ <;> omega

theorem marker_deletion_v_survival {A : Set ℕ} {u v : ℕ}
    (hu0 : 0 < u) (huv : u < v)
    (h0 : 0 ∈ A) (hvA : v ∈ A)
    (M : ℕ → ℕ) (hgrow : ∀ k, 2 * M k < M (k + 1))
    (hbig : 4 * v < M 0)
    (hcorep : ∀ k, M k - v ∈ A) :
    ∀ k, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ Set.range (fun j => M j - u) ∧
      y ∉ Set.range (fun j => M j - u) ∧
      z ∉ Set.range (fun j => M j - u) ∧
      x + y + z = M k := by
  intro k
  have hmono : StrictMono M := geometric_strictMono hgrow (by omega)
  have hM0 : ∀ i, 4 * v < M i := by
    intro i
    have := hmono.monotone (Nat.zero_le i); omega
  refine ⟨v, hvA, M k - v, hcorep k, 0, h0, ?_, ?_, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    have hj' : M j - u = v := hj
    have := hM0 j
    omega
  · rintro ⟨j, hj⟩
    have hj' : M j - u = M k - v := hj
    exact (marker_repair_distinct hu0 huv M hgrow hbig j k).2.2 hj'
  · rintro ⟨j, hj⟩
    have hj' : M j - u = 0 := hj
    have := hM0 j
    omega
  · have := hM0 k
    omega

theorem marker_deletion_targets_survive {A : Set ℕ} {u v : ℕ}
    (hu0 : 0 < u) (huv : u < v)
    (h0 : 0 ∈ A) (hvA : v ∈ A)
    (M : ℕ → ℕ) (hgrow : ∀ k, 2 * M k < M (k + 1))
    (hbig : 4 * v < M 0)
    (hcorep_u : ∀ k, M k - u ∈ A)
    (hcorep_v : ∀ k, M k - v ∈ A) :
    Set.range (fun j => M j - u) ⊆ A ∧
    (Set.range (fun j => M j - u)).Infinite ∧
    ∀ k, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ Set.range (fun j => M j - u) ∧
      y ∉ Set.range (fun j => M j - u) ∧
      z ∉ Set.range (fun j => M j - u) ∧
      x + y + z = M k := by
  have hmono : StrictMono M := geometric_strictMono hgrow (by omega)
  have hM0 : ∀ i, 4 * v < M i := by
    intro i
    have := hmono.monotone (Nat.zero_le i); omega
  refine ⟨?_, ?_, marker_deletion_v_survival hu0 huv h0 hvA M hgrow hbig
    hcorep_v⟩
  · rintro x ⟨j, rfl⟩
    exact hcorep_u j
  · apply Set.infinite_of_injective_forall_mem
      (f := fun j : ℕ => M j - u)
    · intro i j hij
      have hij' : M i - u = M j - u := hij
      have := hM0 i
      have := hM0 j
      rcases Nat.lt_trichotomy i j with h | h | h
      · have := geometric_separation hgrow (c := 4 * v) (by omega) i j h
        omega
      · exact h
      · have := geometric_separation hgrow (c := 4 * v) (by omega) j i h
        omega
    · intro j
      exact ⟨j, rfl⟩

end Erdos881
