/-
# The direct construction: clean redundancy chains

Strategy shift.  The contradiction campaign describes a
hypothetical enemy; this file instead BUILDS the deletion.  The
load-bearing observation is prefix locality: a summand of `n` is
at most `n`, so an infinite deletion `B` hurts the target `n` only
through the finite prefix `B ∩ [0, n]`.  Consequently an infinite
surviving deletion exists as soon as one step can always be taken:

  after deleting any finite stack, some arbitrarily large element
  `b` is CLEANLY REDUNDANT — every target from `b` on keeps a
  representation avoiding both the stack and `b`.

Chaining such elements `b₀ < b₁ < …` gives `B` outright: a target
`n` in the window `[bⱼ, bⱼ₊₁)` is covered by stage `j`'s
redundancy, and every later `bₗ` exceeds `n`, so it cannot occur
as a summand.  No minimality, no contradiction, every lemma keeps
its value.

`erdos881_of_cleanSupply` records the payoff: the clean-redundancy
supply at the hard cases decides ALL of Erdős 881.  The frontier
is now one positive ∀∃-statement about bases — a target to build
toward, not an enemy to portrait.
-/

import Erdos881.GeneralOrder

namespace Erdos881

/-- `b` is cleanly redundant at order `h` over the finite stack
`F`: every target from `b` on keeps an order-`h` representation
avoiding `F` and `b`. -/
def CleanlyRedundantAbove (A : Set ℕ) (h : ℕ)
    (F : Finset ℕ) (b : ℕ) : Prop :=
  ∀ n, b ≤ n → ∃ v : Fin h → ℕ,
    (∀ i, v i ∈ A ∧ v i ∉ F ∧ v i ≠ b) ∧
    ∑ i, v i = n

/-- The clean-redundancy supply: after every finite stack, some
element above every bound is cleanly redundant. -/
def HasCleanSupply (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ F : Finset ℕ, ∀ M, ∃ b, b ∈ A ∧ M ≤ b ∧
    CleanlyRedundantAbove A h F b

/-- The stack iterator: at each step, record the picked element
and raise the floor above it. -/
private noncomputable def cleanStack
    (pick : Finset ℕ → ℕ → ℕ) : ℕ → Finset ℕ × ℕ
  | 0 => (∅, 0)
  | j + 1 =>
    (insert (pick (cleanStack pick j).1
        (cleanStack pick j).2)
      (cleanStack pick j).1,
     pick (cleanStack pick j).1
        (cleanStack pick j).2 + 1)

/-- **The chain theorem.**  A clean-redundancy supply yields an
infinite surviving deletion — the direct construction, at every
order, with no minimality hypothesis. -/
theorem exists_infiniteDeletion_of_cleanSupply
    {A : Set ℕ} {h : ℕ} (hsupply : HasCleanSupply A h) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) h := by
  classical
  choose pick hpickA hpickge hpickred using hsupply
  set S : ℕ → Finset ℕ × ℕ := cleanStack pick with hS
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

/-- **The reduction of Erdős 881.**  If every hard case carries a
clean-redundancy supply at the next order, the whole problem —
every order `k` — follows.  The open frontier is exactly this
positive supply statement. -/
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
