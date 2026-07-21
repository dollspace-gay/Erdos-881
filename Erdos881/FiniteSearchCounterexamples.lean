import Erdos881.GadicLaboratory

/-!
# Additive counterexamples discovered by finite search

The search in `scripts/search_additive_repair_obstructions.py` found the
support pattern `{0,1}`, `{0,2}` at target `2`.  Translating it by `L` and
placing a cofinite tail above the target embeds the pattern at arbitrarily
late targets of a genuine exact order-two basis.
-/

namespace Erdos881

/-- The shifted four-point gadget, followed by a tail strictly above its
distinguished order-three target `3 * L + 2`. -/
def shiftedRepairBasis (L : ℕ) : Set ℕ :=
  {x | x = L ∨ x = L + 1 ∨ x = L + 2 ∨ x = L + 3 ∨
    3 * L + 3 ≤ x}

def shiftedRepairDestroyer (L : ℕ) : Finset ℕ :=
  {L + 1, L + 2}

private theorem tupleSupport_fin_three
    {n : ℕ} (v : Fin 3 → Fin (n + 1)) :
    tupleSupport v = {(v 0).1, (v 1).1, (v 2).1} := by
  ext x
  simp only [mem_tupleSupport_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr hi.symm)
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

theorem shiftedRepairBasis_exactOrderTwo (L : ℕ) :
    IsExactTupleAsymptoticBasis (shiftedRepairBasis L) 2 := by
  let H := 3 * L + 3
  refine ⟨2 * H, ?_⟩
  intro n hn
  refine ⟨![H, n - H], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [H]))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (by dsimp [H]; omega))))
  · simp
    omega

private theorem shiftedRepair_supportFamily (L : ℕ) :
    additiveSupportFamily (shiftedRepairBasis L) 3 (3 * L + 2) =
      {{L, L + 1}, {L, L + 2}} := by
  classical
  ext E
  constructor
  · intro hER
    obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have hsum : (v 0).1 + ((v 1).1 + (v 2).1) = 3 * L + 2 := by
      simpa [Fin.sum_univ_succ] using hvsum
    have hvle : ∀ i : Fin 3, (v i).1 ≤ 3 * L + 2 := by
      intro i
      exact Nat.le_of_lt_succ (v i).2
    have hvform : ∀ i : Fin 3,
        (v i).1 = L ∨ (v i).1 = L + 1 ∨
          (v i).1 = L + 2 ∨ (v i).1 = L + 3 := by
      intro i
      rcases hvA i with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · have := hvle i
        omega
    have hforms :
        ((v 0).1 = L ∧ (v 1).1 = L ∧ (v 2).1 = L + 2) ∨
        ((v 0).1 = L ∧ (v 1).1 = L + 2 ∧ (v 2).1 = L) ∨
        ((v 0).1 = L + 2 ∧ (v 1).1 = L ∧ (v 2).1 = L) ∨
        ((v 0).1 = L ∧ (v 1).1 = L + 1 ∧ (v 2).1 = L + 1) ∨
        ((v 0).1 = L + 1 ∧ (v 1).1 = L ∧ (v 2).1 = L + 1) ∨
        ((v 0).1 = L + 1 ∧ (v 1).1 = L + 1 ∧ (v 2).1 = L) := by
      rcases hvform 0 with h0 | h0 | h0 | h0 <;>
        rcases hvform 1 with h1 | h1 | h1 | h1 <;>
          rcases hvform 2 with h2 | h2 | h2 | h2 <;> omega
    rw [tupleSupport_fin_three]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hforms with h | h | h | h | h | h
    · right; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
    · right; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
    · right; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
    · left; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
    · left; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
    · left; simp [h.1, h.2.1, h.2.2, Finset.pair_comm]
  · intro hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · let v : Fin 3 → Fin (3 * L + 2 + 1) :=
        ![⟨L, by omega⟩, ⟨L + 1, by omega⟩, ⟨L + 1, by omega⟩]
      apply mem_additiveSupportFamily_iff.mpr
      refine ⟨v, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [v, shiftedRepairBasis]
      · simp [v, Fin.sum_univ_succ]
        omega
      · rw [tupleSupport_fin_three]
        simp [v]
    · let v : Fin 3 → Fin (3 * L + 2 + 1) :=
        ![⟨L, by omega⟩, ⟨L, by omega⟩, ⟨L + 2, by omega⟩]
      apply mem_additiveSupportFamily_iff.mpr
      refine ⟨v, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [v, shiftedRepairBasis]
      · simp [v, Fin.sum_univ_succ]
        omega
      · rw [tupleSupport_fin_three]
        simp [v]

theorem shiftedRepairDestroyer_minimal (L : ℕ) :
    IsInclusionMinimalDestroyer
      (additiveSupportFamily (shiftedRepairBasis L) 3)
      (shiftedRepairDestroyer L) (3 * L + 2) := by
  rw [IsInclusionMinimalDestroyer]
  constructor
  · intro E hE
    rw [shiftedRepair_supportFamily] at hE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact Set.not_disjoint_iff.mpr
        ⟨L + 1, by simp, by simp [shiftedRepairDestroyer]⟩
    · exact Set.not_disjoint_iff.mpr
        ⟨L + 2, by simp, by simp [shiftedRepairDestroyer]⟩
  · intro x hx
    simp only [shiftedRepairDestroyer, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · apply not_destroysAt_iff.mpr
      refine ⟨{L, L + 1}, ?_, ?_⟩
      · rw [shiftedRepair_supportFamily]
        simp
      · simp [shiftedRepairDestroyer]
    · apply not_destroysAt_iff.mpr
      refine ⟨{L, L + 2}, ?_, ?_⟩
      · rw [shiftedRepair_supportFamily]
        simp
      · simp [shiftedRepairDestroyer]

/-- Two unique-hit repairs belonging to distinct destroyer vertices. -/
def HasTwoDisjointUniqueHitRepairs
    (R : SupportFamily) (D : Finset ℕ) (n : ℕ) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧
    ∃ E ∈ R n, ∃ F ∈ R n,
      E ∩ D = {x} ∧ F ∩ D = {y} ∧
        Disjoint (E \ D) (F \ D)

/-- The searched additive gadget has no two-repair augmentation: both
unique-hit repairs use the same outside vertex `L`. -/
theorem shiftedRepairDestroyer_noTwoDisjointUniqueHitRepairs (L : ℕ) :
    ¬ HasTwoDisjointUniqueHitRepairs
      (additiveSupportFamily (shiftedRepairBasis L) 3)
      (shiftedRepairDestroyer L) (3 * L + 2) := by
  rintro ⟨x, hxD, y, hyD, hxy, E, hER, F, hFR,
    hEhit, hFhit, hdisj⟩
  rw [shiftedRepair_supportFamily] at hER hFR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hER hFR
  have hdiff1 :
      ({L, L + 1} : Finset ℕ) \ shiftedRepairDestroyer L = {L} := by
    ext z
    simp [shiftedRepairDestroyer]
    omega
  have hdiff2 :
      ({L, L + 2} : Finset ℕ) \ shiftedRepairDestroyer L = {L} := by
    ext z
    simp [shiftedRepairDestroyer]
    omega
  rcases hER with rfl | rfl <;> rcases hFR with rfl | rfl
  all_goals
    simp only [hdiff1, hdiff2] at hdisj
    exact (Finset.not_disjoint_iff.mpr ⟨L, by simp, by simp⟩) hdisj

/-- Therefore the naive additive augmentation claim fails at arbitrarily
late targets, even while the ambient set is an exact order-two basis. -/
theorem arbitrarilyLate_additiveMinimalDestroyer_without_twoRepairs :
    ∀ N, ∃ A : Set ℕ, ∃ n D,
      N ≤ n ∧ IsExactTupleAsymptoticBasis A 2 ∧
      IsInclusionMinimalDestroyer (additiveSupportFamily A 3) D n ∧
      ¬ HasTwoDisjointUniqueHitRepairs
          (additiveSupportFamily A 3) D n := by
  intro N
  exact ⟨shiftedRepairBasis N, 3 * N + 2, shiftedRepairDestroyer N,
    by omega, shiftedRepairBasis_exactOrderTwo N,
    shiftedRepairDestroyer_minimal N,
    shiftedRepairDestroyer_noTwoDisjointUniqueHitRepairs N⟩

end Erdos881
