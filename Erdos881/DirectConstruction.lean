import Erdos881.GeneralOrder

namespace Erdos881

/-- `b` is redundant relative to `F` above `b`: every `n ≥ b` has an
order-`h` representation in `A \ (F ∪ {b})`. -/
def CleanlyRedundantAbove (A : Set ℕ) (h : ℕ)
    (F : Finset ℕ) (b : ℕ) : Prop :=
  ∀ n, b ≤ n → ∃ v : Fin h → ℕ,
    (∀ i, v i ∈ A ∧ v i ∉ F ∧ v i ≠ b) ∧
    ∑ i, v i = n

/-- Every finite excluded set has arbitrarily large redundant extensions. -/
def HasCleanSupply (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ F : Finset ℕ, ∀ M, ∃ b, b ∈ A ∧ M ≤ b ∧
    CleanlyRedundantAbove A h F b

/-- Recursively accumulate selected elements and the next lower bound. -/
private noncomputable def cleanSelection
    (pick : Finset ℕ → ℕ → ℕ) : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | j + 1 =>
    (insert (pick (cleanSelection pick j).1
        (cleanSelection pick j).2)
      (cleanSelection pick j).1,
     pick (cleanSelection pick j).1
        (cleanSelection pick j).2 + 1)

theorem exists_infiniteDeletion_of_cleanSupply
    {A : Set ℕ} {h : ℕ} (hsupply : HasCleanSupply A h) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) h := by
  classical
  choose pick hpickA hpickge hpickred using hsupply
  set S : ℕ → Finset ℕ × ℕ := cleanSelection pick with hS
  set b : ℕ → ℕ := fun j => pick (S j).1 (S j).2
    with hbdef
  have hSsucc : ∀ j, S (j + 1) =
      (insert (b j) (S j).1, b j + 1) := fun j => rfl
  have hmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h1 : (S (j + 1)).2 ≤ b (j + 1) :=
      hpickge (S (j + 1)).1 (S (j + 1)).2
    rw [hSsucc j] at h1
    exact lt_of_lt_of_le (by omega) h1
  have hstack : ∀ j x, x ∈ (S j).1 ↔
      ∃ i, i < j ∧ b i = x := by
    intro j
    induction j with
    | zero =>
      intro x
      constructor
      · intro hx
        exact absurd hx (Finset.notMem_empty x)
      · rintro ⟨i, hi, -⟩
        omega
    | succ j ih =>
      intro x
      rw [hSsucc j, Finset.mem_insert]
      constructor
      · rintro (rfl | hx)
        · exact ⟨j, by omega, rfl⟩
        · obtain ⟨i, hi, hbi⟩ := (ih x).mp hx
          exact ⟨i, by omega, hbi⟩
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_or_ge i j with h' | h'
        · exact Or.inr ((ih (b i)).mpr ⟨i, h', rfl⟩)
        · have : i = j := by omega
          exact Or.inl (by rw [this])
  refine ⟨Set.range b, ?_, ?_, ?_⟩
  · rintro x ⟨j, rfl⟩
    exact hpickA (S j).1 (S j).2
  · exact Set.infinite_range_of_injective
      hmono.injective
  · refine ⟨b 0, fun n hn => ?_⟩
    set j := Nat.findGreatest (fun j => b j ≤ n) n
      with hj
    have hbj : b j ≤ n :=
      Nat.findGreatest_spec
        (P := fun j => b j ≤ n) (m := 0)
        (by omega) hn
    have hlater : ∀ l, j < l → n < b l := by
      intro l hl
      rcases Nat.lt_or_ge n l with h' | h'
      · have h1 : l ≤ b l := hmono.le_apply
        omega
      · have := Nat.findGreatest_is_greatest
          (P := fun j => b j ≤ n) hl h'
        omega
    obtain ⟨v, hv, hvsum⟩ :=
      hpickred (S j).1 (S j).2 n hbj
    refine ⟨v, ?_, hvsum⟩
    intro i
    obtain ⟨hvA, hvF, hvb⟩ := hv i
    refine ⟨hvA, ?_⟩
    rintro ⟨l, hl⟩
    have hvin : v i ≤ n := by
      rw [← hvsum]
      exact Finset.single_le_sum
        (f := v) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rcases Nat.lt_trichotomy l j with h' | rfl | h'
    · exact hvF ((hstack j (v i)).mpr ⟨l, h', hl⟩)
    · exact hvb hl.symm
    · have := hlater l h'
      omega

theorem erdos881_of_cleanSupply
    (hsup : ∀ k, 3 ≤ k → ∀ A : Set ℕ,
      IsStronglyMinimalExactBasis A k →
      ¬ IsExactTupleAsymptoticBasis A 2 →
      HasCleanSupply A (k + 1)) :
    ∀ k, Erdos881At k := by
  refine erdos881_general_of_hardCase ?_
  intro k hk A hmin h2
  exact exists_infiniteDeletion_of_cleanSupply
    (hsup k hk A hmin h2)

end Erdos881
