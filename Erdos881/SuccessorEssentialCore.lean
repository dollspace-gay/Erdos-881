import Erdos881.AlternatingRepairs

/-!
# The successor-essential core of an order-two basis

An element is placed in the successor-essential core when deleting that one
element destroys the exact order-three basis property.  Private-target
rigidity forces this core to be Sidon off the diagonal, and hence
quantitatively sparse.
-/

open scoped BigOperators

namespace Erdos881

/-- Elements individually essential for the successor-order basis property. -/
def successorEssentialCore (A : Set ℕ) : Set ℕ :=
  {a | a ∈ A ∧
    ¬ IsExactTupleAsymptoticBasis (A \ ({a} : Set ℕ)) 3}

theorem mem_successorEssentialCore_iff
    {A : Set ℕ} {a : ℕ} :
    a ∈ successorEssentialCore A ↔
      a ∈ A ∧
        ¬ IsExactTupleAsymptoticBasis (A \ ({a} : Set ℕ)) 3 := by
  rfl

/-- Essentiality is equivalent to arbitrarily late singleton destruction. -/
theorem successorEssentialCore_has_late_singletonDestruction
    {A : Set ℕ} {a : ℕ}
    (ha : a ∈ successorEssentialCore A) :
    ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({a} : Set ℕ) n := by
  have hlate :=
    (not_exactTupleAsymptoticBasis_diff_finset_iff
      (A := A) (h := 3) (D := ({a} : Finset ℕ))).mp
        (by simpa using ha.2)
  intro N
  obtain ⟨n, hn, hdestroy⟩ := hlate N
  exact ⟨n, hn, by simpa using hdestroy⟩

/-- The sum of two distinct successor-essential elements has no genuinely
different two-term representation in the ambient order-two basis. -/
theorem successorEssentialCore_pairSum_rigid
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    {a b : ℕ}
    (ha : a ∈ successorEssentialCore A)
    (hb : b ∈ successorEssentialCore A)
    (hab : a ≠ b)
    (v : Fin 2 → ℕ) (hvA : ∀ i, v i ∈ A)
    (hvsum : ∑ i, v i = a + b) :
    (∃ i, v i = a) ∧ (∃ i, v i = b) := by
  constructor
  · exact orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis hb.1 hab
      (successorEssentialCore_has_late_singletonDestruction ha)
      v hvA hvsum
  · exact orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis ha.1 hab.symm
      (successorEssentialCore_has_late_singletonDestruction hb)
      v hvA (by omega)

/-- Off the diagonal, pair sums in the successor-essential core are unique
up to exchanging the two summands. -/
theorem successorEssentialCore_isSidonOffDiagonal
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    {a b c d : ℕ}
    (ha : a ∈ successorEssentialCore A)
    (hb : b ∈ successorEssentialCore A)
    (hc : c ∈ successorEssentialCore A)
    (hd : d ∈ successorEssentialCore A)
    (hab : a ≠ b)
    (hsum : a + b = c + d) :
    ({a, b} : Finset ℕ) = {c, d} := by
  let v : Fin 2 → ℕ := ![c, d]
  have hvA : ∀ i, v i ∈ A := by
    intro i
    fin_cases i <;> simp [v, hc.1, hd.1]
  have hvsum : ∑ i, v i = a + b := by
    simpa [v, Fin.sum_univ_two] using hsum.symm
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ :=
    successorEssentialCore_pairSum_rigid
      hbasis ha hb hab v hvA hvsum
  fin_cases i <;> fin_cases j
  · have : a = b := by simpa [v] using hi.symm.trans hj
    exact (hab this).elim
  · have hca : c = a := by simpa [v] using hi
    have hdb : d = b := by simpa [v] using hj
    simp [hca, hdb]
  · have hda : d = a := by simpa [v] using hi
    have hcb : c = b := by simpa [v] using hj
    simp [hda, hcb, Finset.pair_comm]
  · have : a = b := by simpa [v] using hi.symm.trans hj
    exact (hab this).elim

/-- Quantitative sparsity of every bounded finite piece of the essential
core.  Distinct unordered pairs have distinct sums, and all those sums lie
between `0` and `2 * M`. -/
theorem successorEssentialCore_chooseTwo_le_twice_bound
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (S : Finset ℕ) (M : ℕ)
    (hcore : ∀ a ∈ S, a ∈ successorEssentialCore A)
    (hbound : ∀ a ∈ S, a ≤ M) :
    Nat.choose S.card 2 ≤ 2 * M + 1 := by
  classical
  let P := S.powersetCard 2
  let pairSum : Finset ℕ → ℕ := fun E => E.sum id
  have hinj : Set.InjOn pairSum (P : Set (Finset ℕ)) := by
    intro E hEP E' hE'P heq
    obtain ⟨hES, hEcard⟩ := Finset.mem_powersetCard.mp hEP
    obtain ⟨hE'S, hE'card⟩ := Finset.mem_powersetCard.mp hE'P
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hEcard
    obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hE'card
    have haS : a ∈ S := hES (by simp)
    have hbS : b ∈ S := hES (by simp)
    have hcS : c ∈ S := hE'S (by simp)
    have hdS : d ∈ S := hE'S (by simp)
    apply successorEssentialCore_isSidonOffDiagonal
      hbasis (hcore a haS) (hcore b hbS)
        (hcore c hcS) (hcore d hdS) hab
    simpa [pairSum, hab, hcd, Nat.add_comm] using heq
  have himage : P.image pairSum ⊆ Finset.range (2 * M + 1) := by
    intro y hy
    obtain ⟨E, hEP, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hES, hEcard⟩ := Finset.mem_powersetCard.mp hEP
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hEcard
    have haS : a ∈ S := hES (by simp)
    have hbS : b ∈ S := hES (by simp)
    apply Finset.mem_range.mpr
    simp only [pairSum]
    simp [hab]
    have haM := hbound a haS
    have hbM := hbound b hbS
    omega
  calc
    Nat.choose S.card 2 = P.card := by
      simp [P]
    _ = (P.image pairSum).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (2 * M + 1)).card :=
      Finset.card_le_card himage
    _ = 2 * M + 1 := by simp

noncomputable def successorEssentialCoreBelow
    (A : Set ℕ) (M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (M + 1)).filter fun a =>
    a ∈ successorEssentialCore A

/-- Direct counting-function form: among `0, ..., M`, the number of
successor-essential elements has at most `2 * M + 1` unordered pairs. -/
theorem successorEssentialCoreBelow_chooseTwo_bound
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (M : ℕ) :
    Nat.choose (successorEssentialCoreBelow A M).card 2 ≤
      2 * M + 1 := by
  classical
  apply successorEssentialCore_chooseTwo_le_twice_bound hbasis
  · intro a ha
    exact (Finset.mem_filter.mp ha).2
  · intro a ha
    have harange := (Finset.mem_filter.mp ha).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp harange)

end Erdos881
