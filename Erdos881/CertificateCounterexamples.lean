import Erdos881.AdditiveSupports

/-!
# Counterchecks for stronger certificate localization

A cardinal-minimal selector certificate supplies one target-private selector
for each target.  It does not, even when every block has two vertices, imply
that those private selectors can be chosen pairwise disjoint.  The explicit
two-target support family below records the obstruction.
-/

namespace Erdos881

private def overlapPairBlocks (i : ℕ) : Finset ℕ :=
  {2 * i, 2 * i + 1}

private theorem overlapPairBlocks_partition :
    IsFiniteBlockPartition (Set.univ : Set ℕ) overlapPairBlocks := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨2 * i, by simp [overlapPairBlocks]⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [overlapPairBlocks, Finset.mem_insert,
      Finset.mem_singleton] at hxi hxj
    rcases hxi with hxi | hxi <;>
      rcases hxj with hxj | hxj <;> omega
  · intro x
    constructor
    · intro _hx
      refine ⟨x / 2, ?_⟩
      simp only [overlapPairBlocks, Finset.mem_insert,
        Finset.mem_singleton]
      have hdecomp := Nat.mod_add_div x 2
      rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
      · left
        omega
      · right
        omega
    · intro _hx
      exact Set.mem_univ x

/- Target zero has the single support `{0,2}`; target one has the single
support `{0,3}`.  Other targets are irrelevant. -/
private def overlappingPrivateSupportFamily : SupportFamily
  | 0 => {{0, 2}}
  | 1 => {{0, 3}}
  | _ => ∅

private theorem destroys_overlap_zero_iff (B : Set ℕ) :
    DestroysAt overlappingPrivateSupportFamily B 0 ↔
      0 ∈ B ∨ 2 ∈ B := by
  simp [DestroysAt, overlappingPrivateSupportFamily,
    Set.not_disjoint_iff]

private theorem destroys_overlap_one_iff (B : Set ℕ) :
    DestroysAt overlappingPrivateSupportFamily B 1 ↔
      0 ∈ B ∨ 3 ∈ B := by
  simp [DestroysAt, overlappingPrivateSupportFamily,
    Set.not_disjoint_iff]

private def overlapPrivateZeroSelector :
    BlockSelector overlapPairBlocks := fun i =>
  if hi : i = 0 then
    ⟨1, by subst i; simp [overlapPairBlocks]⟩
  else
    ⟨2 * i, by simp [overlapPairBlocks]⟩

private def overlapPrivateOneSelector :
    BlockSelector overlapPairBlocks := fun i =>
  if hi : i = 0 then
    ⟨1, by subst i; simp [overlapPairBlocks]⟩
  else if hj : i = 1 then
    ⟨3, by subst i; simp [overlapPairBlocks]⟩
  else
    ⟨2 * i, by simp [overlapPairBlocks]⟩

private theorem overlapPrivateZeroSelector_value
    (i : ℕ) :
    (overlapPrivateZeroSelector i).1 =
      if i = 0 then 1 else 2 * i := by
  by_cases hi : i = 0
  · subst i
    rfl
  · simp [overlapPrivateZeroSelector, hi]

private theorem overlapPrivateOneSelector_value
    (i : ℕ) :
    (overlapPrivateOneSelector i).1 =
      if i = 0 then 1 else if i = 1 then 3 else 2 * i := by
  by_cases hi : i = 0
  · subst i
    rfl
  · by_cases hj : i = 1
    · subst i
      rfl
    · simp [overlapPrivateOneSelector, hi, hj]

private theorem overlapPrivateZeroSelector_avoids_zero_three :
    0 ∉ selectedSet overlapPrivateZeroSelector ∧
      3 ∉ selectedSet overlapPrivateZeroSelector := by
  constructor
  · rintro ⟨i, hi⟩
    change (overlapPrivateZeroSelector i).1 = 0 at hi
    rw [overlapPrivateZeroSelector_value] at hi
    split at hi <;> omega
  · rintro ⟨i, hi⟩
    change (overlapPrivateZeroSelector i).1 = 3 at hi
    rw [overlapPrivateZeroSelector_value] at hi
    split at hi <;> omega

private theorem overlapPrivateOneSelector_avoids_zero_two :
    0 ∉ selectedSet overlapPrivateOneSelector ∧
      2 ∉ selectedSet overlapPrivateOneSelector := by
  constructor
  · rintro ⟨i, hi⟩
    change (overlapPrivateOneSelector i).1 = 0 at hi
    rw [overlapPrivateOneSelector_value] at hi
    by_cases h0 : i = 0
    · simp [h0] at hi
    · by_cases h1 : i = 1
      · simp [h1] at hi
      · simp [h0, h1] at hi
  · rintro ⟨i, hi⟩
    change (overlapPrivateOneSelector i).1 = 2 at hi
    rw [overlapPrivateOneSelector_value] at hi
    by_cases h0 : i = 0
    · simp [h0] at hi
    · by_cases h1 : i = 1
      · simp [h1] at hi
      · simp [h0, h1] at hi

private theorem every_overlap_selector_certified
    (s : BlockSelector overlapPairBlocks) :
    ∃ q ∈ ({0, 1} : Finset ℕ),
      DestroysAt overlappingPrivateSupportFamily (selectedSet s) q := by
  have hs0 := (s 0).2
  have hs1 := (s 1).2
  simp only [overlapPairBlocks, Nat.mul_zero, zero_add,
    Finset.mem_insert, Finset.mem_singleton] at hs0
  simp only [overlapPairBlocks, Finset.mem_insert,
    Finset.mem_singleton] at hs1
  norm_num at hs1
  rcases hs0 with hs0 | hs0
  · refine ⟨0, by simp, (destroys_overlap_zero_iff _).mpr (Or.inl ?_)⟩
    exact ⟨0, hs0⟩
  · rcases hs1 with hs1 | hs1
    · refine ⟨0, by simp, (destroys_overlap_zero_iff _).mpr (Or.inr ?_)⟩
      exact ⟨1, hs1⟩
    · refine ⟨1, by simp, (destroys_overlap_one_iff _).mpr (Or.inr ?_)⟩
      exact ⟨1, hs1⟩

private theorem overlap_certificate_targetLocalized :
    ∀ q ∈ ({0, 1} : Finset ℕ),
      ∃ base : BlockSelector overlapPairBlocks,
        DestroysAt overlappingPrivateSupportFamily
          (selectedSet base) q ∧
        ∀ q' ∈ ({0, 1} : Finset ℕ), q' ≠ q →
          ¬ DestroysAt overlappingPrivateSupportFamily
            (selectedSet base) q' := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · refine ⟨overlapPrivateZeroSelector, ?_, ?_⟩
    · apply (destroys_overlap_zero_iff _).mpr
      exact Or.inr ⟨1, by simp [overlapPrivateZeroSelector]⟩
    · intro q' hq' hq'ne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      rcases hq' with rfl | rfl
      · exact (hq'ne rfl).elim
      · rw [destroys_overlap_one_iff]
        exact not_or_intro
          overlapPrivateZeroSelector_avoids_zero_three.1
          overlapPrivateZeroSelector_avoids_zero_three.2
  · refine ⟨overlapPrivateOneSelector, ?_, ?_⟩
    · apply (destroys_overlap_one_iff _).mpr
      exact Or.inr ⟨1, by simp [overlapPrivateOneSelector]⟩
    · intro q' hq' hq'ne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
      rcases hq' with rfl | rfl
      · rw [destroys_overlap_zero_iff]
        exact not_or_intro
          overlapPrivateOneSelector_avoids_zero_two.1
          overlapPrivateOneSelector_avoids_zero_two.2
      · exact (hq'ne rfl).elim

private theorem private_zero_selector_contains_one
    (s : BlockSelector overlapPairBlocks)
    (hprivate :
      DestroysAt overlappingPrivateSupportFamily (selectedSet s) 0 ∧
      ¬ DestroysAt overlappingPrivateSupportFamily (selectedSet s) 1) :
    1 ∈ selectedSet s := by
  have hzero : 0 ∉ selectedSet s := by
    intro h0
    exact hprivate.2 ((destroys_overlap_one_iff _).mpr (Or.inl h0))
  have hs0 := (s 0).2
  simp only [overlapPairBlocks, Nat.mul_zero, zero_add,
    Finset.mem_insert, Finset.mem_singleton] at hs0
  rcases hs0 with hs0 | hs0
  · exact (hzero ⟨0, hs0⟩).elim
  · exact ⟨0, hs0⟩

private theorem private_one_selector_contains_one
    (s : BlockSelector overlapPairBlocks)
    (hprivate :
      DestroysAt overlappingPrivateSupportFamily (selectedSet s) 1 ∧
      ¬ DestroysAt overlappingPrivateSupportFamily (selectedSet s) 0) :
    1 ∈ selectedSet s := by
  have hzero : 0 ∉ selectedSet s := by
    intro h0
    exact hprivate.2 ((destroys_overlap_zero_iff _).mpr (Or.inl h0))
  have hs0 := (s 0).2
  simp only [overlapPairBlocks, Nat.mul_zero, zero_add,
    Finset.mem_insert, Finset.mem_singleton] at hs0
  rcases hs0 with hs0 | hs0
  · exact (hzero ⟨0, hs0⟩).elim
  · exact ⟨0, hs0⟩

/-- A two-target minimal certificate on two-point blocks whose target-private
selectors necessarily intersect.  Hence minimal target localization alone
cannot be strengthened to pairwise-disjoint localized selectors. -/
theorem targetLocalized_certificateSelectors_need_not_be_disjoint :
    ∃ F : ℕ → Finset ℕ, ∃ R : SupportFamily, ∃ Q : Finset ℕ,
      IsFiniteBlockPartition (Set.univ : Set ℕ) F ∧
      Q.card = 2 ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt R (selectedSet s) q) ∧
      (∀ q ∈ Q, ∃ base : BlockSelector F,
        DestroysAt R (selectedSet base) q ∧
        ∀ q' ∈ Q, q' ≠ q →
          ¬ DestroysAt R (selectedSet base) q') ∧
      ∀ s₀ s₁ : BlockSelector F,
        (DestroysAt R (selectedSet s₀) 0 ∧
          ¬ DestroysAt R (selectedSet s₀) 1) →
        (DestroysAt R (selectedSet s₁) 1 ∧
          ¬ DestroysAt R (selectedSet s₁) 0) →
        ¬ Disjoint (selectedSet s₀) (selectedSet s₁) := by
  refine ⟨overlapPairBlocks, overlappingPrivateSupportFamily,
    {0, 1}, overlapPairBlocks_partition, by simp,
    every_overlap_selector_certified,
    overlap_certificate_targetLocalized, ?_⟩
  intro s₀ s₁ hs₀ hs₁ hdisjoint
  exact Set.disjoint_left.mp hdisjoint
    (private_zero_selector_contains_one s₀ hs₀)
    (private_one_selector_contains_one s₁ hs₁)

/-! ## The same obstruction inside an additive basis -/

private def additiveOverlapBasis : Set ℕ :=
  {x | x = 0 ∨ x = 2 ∨ x = 3 ∨ 10 ≤ x}

private def additiveOverlapBlocks : ℕ → Finset ℕ
  | 0 => {0, 10}
  | 1 => {2, 3}
  | i + 2 => {i + 11}

private theorem additiveOverlapBlocks_partition :
    IsFiniteBlockPartition additiveOverlapBasis additiveOverlapBlocks := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rcases i with _ | i
    · exact ⟨0, by simp [additiveOverlapBlocks]⟩
    · rcases i with _ | i
      · exact ⟨2, by simp [additiveOverlapBlocks]⟩
      · exact ⟨i + 11, by simp [additiveOverlapBlocks]⟩
  · intro i j hij
    rcases i with _ | i
    · rcases j with _ | j
      · exact (hij rfl).elim
      · rcases j with _ | j
        · simp [additiveOverlapBlocks]
        · simp [additiveOverlapBlocks]
    · rcases i with _ | i
      · rcases j with _ | j
        · simp [additiveOverlapBlocks]
        · rcases j with _ | j
          · exact (hij rfl).elim
          · simp [additiveOverlapBlocks]
      · rcases j with _ | j
        · simp [additiveOverlapBlocks]
        · rcases j with _ | j
          · simp [additiveOverlapBlocks]
          · simp [additiveOverlapBlocks]
            intro hEq
            apply hij
            omega
  · intro x
    constructor
    · intro hx
      rcases hx with rfl | rfl | rfl | hx
      · exact ⟨0, by simp [additiveOverlapBlocks]⟩
      · exact ⟨1, by simp [additiveOverlapBlocks]⟩
      · exact ⟨1, by simp [additiveOverlapBlocks]⟩
      · by_cases hx10 : x = 10
        · subst x
          exact ⟨0, by simp [additiveOverlapBlocks]⟩
        · refine ⟨Nat.succ (Nat.succ (x - 11)), ?_⟩
          simp only [additiveOverlapBlocks, Finset.mem_singleton]
          omega
    · rintro ⟨i, hxi⟩
      rcases i with _ | i
      · simp [additiveOverlapBlocks] at hxi
        rcases hxi with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr (by omega)))
      · rcases i with _ | i
        · simp [additiveOverlapBlocks] at hxi
          rcases hxi with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
        · simp [additiveOverlapBlocks] at hxi
          subst x
          exact Or.inr (Or.inr (Or.inr (by omega)))

private theorem additiveOverlapBasis_isExactOrderTwoBasis :
    IsExactTupleAsymptoticBasis additiveOverlapBasis 2 := by
  refine ⟨20, ?_⟩
  intro n hn
  let v : Fin 2 → ℕ := ![10, n - 10]
  refine ⟨v, ?_, ?_⟩
  · intro i
    fin_cases i
    · change 10 ∈ additiveOverlapBasis
      exact Or.inr (Or.inr (Or.inr (by omega)))
    · change n - 10 ∈ additiveOverlapBasis
      exact Or.inr (Or.inr (Or.inr (by omega)))
  · simp [v]
    omega

private theorem additiveOverlap_supportFamily_two :
    additiveSupportFamily additiveOverlapBasis 2 2 = {{0, 2}} := by
  classical
  ext E
  constructor
  · intro hER
    obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have h0 := hvA 0
    have h1 := hvA 1
    have hsum : (v 0).1 + (v 1).1 = 2 := by simpa using hvsum
    have hforms :
        ((v 0).1 = 0 ∧ (v 1).1 = 2) ∨
          ((v 0).1 = 2 ∧ (v 1).1 = 0) := by
      rcases h0 with h0 | h0 | h0 | h0 <;>
        rcases h1 with h1 | h1 | h1 | h1 <;> omega
    rw [Finset.mem_singleton]
    rcases hforms with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · ext x
      simp [tupleSupport, h0, h1]
      aesop
    · ext x
      simp [tupleSupport, h0, h1]
      aesop
  · intro hE
    have hEeq : E = {0, 2} := by simpa using hE
    subst E
    have hpair := pairSupport_mem_additiveSupportFamily
      (A := additiveOverlapBasis) (n := 2) (a := 0)
      (by omega) (Or.inl rfl) (Or.inr (Or.inl rfl))
    simpa [pairSupport] using hpair

private theorem additiveOverlap_supportFamily_three :
    additiveSupportFamily additiveOverlapBasis 2 3 = {{0, 3}} := by
  classical
  ext E
  constructor
  · intro hER
    obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have h0 := hvA 0
    have h1 := hvA 1
    have hsum : (v 0).1 + (v 1).1 = 3 := by simpa using hvsum
    have hforms :
        ((v 0).1 = 0 ∧ (v 1).1 = 3) ∨
          ((v 0).1 = 3 ∧ (v 1).1 = 0) := by
      rcases h0 with h0 | h0 | h0 | h0 <;>
        rcases h1 with h1 | h1 | h1 | h1 <;> omega
    rw [Finset.mem_singleton]
    rcases hforms with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · ext x
      simp [tupleSupport, h0, h1]
      aesop
    · ext x
      simp [tupleSupport, h0, h1]
      aesop
  · intro hE
    have hEeq : E = {0, 3} := by simpa using hE
    subst E
    have hpair := pairSupport_mem_additiveSupportFamily
      (A := additiveOverlapBasis) (n := 3) (a := 0)
      (by omega) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    simpa [pairSupport] using hpair

private theorem additiveOverlap_destroys_two_iff (B : Set ℕ) :
    DestroysAt
        (additiveSupportFamily additiveOverlapBasis 2) B 2 ↔
      0 ∈ B ∨ 2 ∈ B := by
  rw [DestroysAt, additiveOverlap_supportFamily_two]
  simp [Set.not_disjoint_iff]

private theorem additiveOverlap_destroys_three_iff (B : Set ℕ) :
    DestroysAt
        (additiveSupportFamily additiveOverlapBasis 2) B 3 ↔
      0 ∈ B ∨ 3 ∈ B := by
  rw [DestroysAt, additiveOverlap_supportFamily_three]
  simp [Set.not_disjoint_iff]

private def additiveOverlapPrivateTwoSelector :
    BlockSelector additiveOverlapBlocks
  | 0 => ⟨10, by simp [additiveOverlapBlocks]⟩
  | 1 => ⟨2, by simp [additiveOverlapBlocks]⟩
  | i + 2 => ⟨i + 11, by simp [additiveOverlapBlocks]⟩

private def additiveOverlapPrivateThreeSelector :
    BlockSelector additiveOverlapBlocks
  | 0 => ⟨10, by simp [additiveOverlapBlocks]⟩
  | 1 => ⟨3, by simp [additiveOverlapBlocks]⟩
  | i + 2 => ⟨i + 11, by simp [additiveOverlapBlocks]⟩

private theorem additiveOverlapPrivateTwo_data :
    2 ∈ selectedSet additiveOverlapPrivateTwoSelector ∧
      0 ∉ selectedSet additiveOverlapPrivateTwoSelector ∧
      3 ∉ selectedSet additiveOverlapPrivateTwoSelector := by
  refine ⟨⟨1, rfl⟩, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    change (additiveOverlapPrivateTwoSelector i).1 = 0 at hi
    rcases i with _ | i
    · simp [additiveOverlapPrivateTwoSelector] at hi
    · rcases i with _ | i <;>
        simp [additiveOverlapPrivateTwoSelector] at hi
  · rintro ⟨i, hi⟩
    change (additiveOverlapPrivateTwoSelector i).1 = 3 at hi
    rcases i with _ | i
    · simp [additiveOverlapPrivateTwoSelector] at hi
    · rcases i with _ | i <;>
        simp [additiveOverlapPrivateTwoSelector] at hi

private theorem additiveOverlapPrivateThree_data :
    3 ∈ selectedSet additiveOverlapPrivateThreeSelector ∧
      0 ∉ selectedSet additiveOverlapPrivateThreeSelector ∧
      2 ∉ selectedSet additiveOverlapPrivateThreeSelector := by
  refine ⟨⟨1, rfl⟩, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    change (additiveOverlapPrivateThreeSelector i).1 = 0 at hi
    rcases i with _ | i
    · simp [additiveOverlapPrivateThreeSelector] at hi
    · rcases i with _ | i <;>
        simp [additiveOverlapPrivateThreeSelector] at hi
  · rintro ⟨i, hi⟩
    change (additiveOverlapPrivateThreeSelector i).1 = 2 at hi
    rcases i with _ | i
    · simp [additiveOverlapPrivateThreeSelector] at hi
    · rcases i with _ | i <;>
        simp [additiveOverlapPrivateThreeSelector] at hi

private theorem every_additiveOverlap_selector_certified
    (s : BlockSelector additiveOverlapBlocks) :
    ∃ q ∈ ({2, 3} : Finset ℕ),
      DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
        (selectedSet s) q := by
  have hs0 := (s 0).2
  have hs1 := (s 1).2
  simp only [additiveOverlapBlocks, Finset.mem_insert,
    Finset.mem_singleton] at hs0 hs1
  rcases hs0 with hs0 | hs0
  · refine ⟨2, by simp,
      (additiveOverlap_destroys_two_iff _).mpr (Or.inl ⟨0, hs0⟩)⟩
  · rcases hs1 with hs1 | hs1
    · refine ⟨2, by simp,
        (additiveOverlap_destroys_two_iff _).mpr (Or.inr ⟨1, hs1⟩)⟩
    · refine ⟨3, by simp,
        (additiveOverlap_destroys_three_iff _).mpr (Or.inr ⟨1, hs1⟩)⟩

private theorem additiveOverlap_certificate_targetLocalized :
    ∀ q ∈ ({2, 3} : Finset ℕ),
      ∃ base : BlockSelector additiveOverlapBlocks,
        DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
          (selectedSet base) q ∧
        ∀ q' ∈ ({2, 3} : Finset ℕ), q' ≠ q →
          ¬ DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
            (selectedSet base) q' := by
  intro q hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl
  · refine ⟨additiveOverlapPrivateTwoSelector,
      (additiveOverlap_destroys_two_iff _).mpr
        (Or.inr additiveOverlapPrivateTwo_data.1), ?_⟩
    intro q' hq' hq'ne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
    rcases hq' with rfl | rfl
    · exact (hq'ne rfl).elim
    · rw [additiveOverlap_destroys_three_iff]
      exact not_or_intro additiveOverlapPrivateTwo_data.2.1
        additiveOverlapPrivateTwo_data.2.2
  · refine ⟨additiveOverlapPrivateThreeSelector,
      (additiveOverlap_destroys_three_iff _).mpr
        (Or.inr additiveOverlapPrivateThree_data.1), ?_⟩
    intro q' hq' hq'ne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq'
    rcases hq' with rfl | rfl
    · rw [additiveOverlap_destroys_two_iff]
      exact not_or_intro additiveOverlapPrivateThree_data.2.1
        additiveOverlapPrivateThree_data.2.2
    · exact (hq'ne rfl).elim

private theorem additiveOverlap_privateTwo_contains_ten
    (s : BlockSelector additiveOverlapBlocks)
    (hprivate :
      DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
          (selectedSet s) 2 ∧
        ¬ DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
          (selectedSet s) 3) :
    10 ∈ selectedSet s := by
  have hzero : 0 ∉ selectedSet s := by
    intro h0
    exact hprivate.2
      ((additiveOverlap_destroys_three_iff _).mpr (Or.inl h0))
  have hs0 := (s 0).2
  simp only [additiveOverlapBlocks, Finset.mem_insert,
    Finset.mem_singleton] at hs0
  rcases hs0 with hs0 | hs0
  · exact (hzero ⟨0, hs0⟩).elim
  · exact ⟨0, hs0⟩

private theorem additiveOverlap_privateThree_contains_ten
    (s : BlockSelector additiveOverlapBlocks)
    (hprivate :
      DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
          (selectedSet s) 3 ∧
        ¬ DestroysAt (additiveSupportFamily additiveOverlapBasis 2)
          (selectedSet s) 2) :
    10 ∈ selectedSet s := by
  have hzero : 0 ∉ selectedSet s := by
    intro h0
    exact hprivate.2
      ((additiveOverlap_destroys_two_iff _).mpr (Or.inl h0))
  have hs0 := (s 0).2
  simp only [additiveOverlapBlocks, Finset.mem_insert,
    Finset.mem_singleton] at hs0
  rcases hs0 with hs0 | hs0
  · exact (hzero ⟨0, hs0⟩).elim
  · exact ⟨0, hs0⟩

/-- The selector-overlap obstruction is genuinely additive: it occurs for
an exact order-two asymptotic basis and its actual pair-representation
support family, not merely for an abstract hypergraph. -/
theorem additive_targetLocalized_certificateSelectors_need_not_be_disjoint :
    ∃ A : Set ℕ, ∃ F : ℕ → Finset ℕ, ∃ Q : Finset ℕ,
      IsExactTupleAsymptoticBasis A 2 ∧
      IsFiniteBlockPartition A F ∧ Q.card = 2 ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2) (selectedSet s) q) ∧
      (∀ q ∈ Q, ∃ base : BlockSelector F,
        DestroysAt (additiveSupportFamily A 2) (selectedSet base) q ∧
        ∀ q' ∈ Q, q' ≠ q →
          ¬ DestroysAt
            (additiveSupportFamily A 2) (selectedSet base) q') ∧
      ∀ s₂ s₃ : BlockSelector F,
        (DestroysAt (additiveSupportFamily A 2) (selectedSet s₂) 2 ∧
          ¬ DestroysAt
            (additiveSupportFamily A 2) (selectedSet s₂) 3) →
        (DestroysAt (additiveSupportFamily A 2) (selectedSet s₃) 3 ∧
          ¬ DestroysAt
            (additiveSupportFamily A 2) (selectedSet s₃) 2) →
        ¬ Disjoint (selectedSet s₂) (selectedSet s₃) := by
  refine ⟨additiveOverlapBasis, additiveOverlapBlocks, {2, 3},
    additiveOverlapBasis_isExactOrderTwoBasis,
    additiveOverlapBlocks_partition, by simp,
    every_additiveOverlap_selector_certified,
    additiveOverlap_certificate_targetLocalized, ?_⟩
  intro s₂ s₃ hs₂ hs₃ hdisjoint
  exact Set.disjoint_left.mp hdisjoint
    (additiveOverlap_privateTwo_contains_ten s₂ hs₂)
    (additiveOverlap_privateThree_contains_ten s₃ hs₃)

end Erdos881
