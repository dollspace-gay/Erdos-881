import Erdos881.FreeSetTripleRepairs

namespace Erdos881

/-- Outside a finite exception, every point destroys the support family at
the target equal to that point. -/
def HasCofiniteSelfDestructionAtOwnTargets
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
    DestroysAt R ({a} : Set ℕ) a

/-- Cofinite self-destruction at the own targets implies strong infinite
deletion, because every infinite deletion contains arbitrarily large
nonexceptional points. -/
theorem strongInfiniteDeletion_of_cofiniteSelfDestructionAtOwnTargets
    {R : SupportFamily} {A : Set ℕ}
    (hatom : HasCofiniteSelfDestructionAtOwnTargets R A) :
    StrongInfiniteDeletion R A := by
  obtain ⟨F, hF⟩ := hatom
  intro B hBA hB N
  let D : Set ℕ := (F : Set ℕ) ∪ Set.Iio N
  have hDfinite : D.Finite := F.finite_toSet.union (Set.finite_Iio N)
  have hBoutside : (B \ D).Infinite := hB.diff hDfinite
  obtain ⟨a, haB, haD⟩ := hBoutside.nonempty
  have haF : a ∉ F := by
    intro haF
    exact haD (Or.inl haF)
  have haN : N ≤ a := by
    apply Nat.le_of_not_gt
    intro haSmall
    exact haD (Or.inr haSmall)
  have hsingleton : ({a} : Set ℕ) ⊆ B := by
    intro x hx
    simpa only [Set.mem_singleton_iff] using hx ▸ haB
  exact ⟨a, haN, (hF a (hBA haB) haF).mono hsingleton⟩

/-- Every support at a canonical atom contains the atom, so its singleton
deletion destroys the own target. -/
theorem destroysOwnTarget_of_canonicalAtom
    {A : Set ℕ} {k a : ℕ}
    (hnormal : ∀ E ∈ additiveSupportFamily A k a, E = {a, 0}) :
    DestroysAt (additiveSupportFamily A k) ({a} : Set ℕ) a := by
  intro E hER
  rw [Set.not_disjoint_iff]
  refine ⟨a, ?_, by simp⟩
  rw [hnormal E hER]
  simp

/-- Cofinitely many canonical order-`k` atoms force strong deletion at that
order. -/
theorem strongInfiniteDeletion_of_cofiniteCanonicalAtoms
    {A : Set ℕ} {k : ℕ}
    (hatom : ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
      ∀ E ∈ additiveSupportFamily A k a, E = {a, 0}) :
    StrongInfiniteDeletion (additiveSupportFamily A k) A := by
  apply strongInfiniteDeletion_of_cofiniteSelfDestructionAtOwnTargets
  obtain ⟨F, hF⟩ := hatom
  exact ⟨F, fun a haA haF =>
    destroysOwnTarget_of_canonicalAtom (hF a haA haF)⟩

/-- Strong order-`k` deletion excludes an exact order-`k` basis after every
infinite deletion. -/
theorem noInfiniteDeletionBasis_of_strongInfiniteDeletion
    {A : Set ℕ} {k : ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A k) A) :
    ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) k := by
  intro B hBA hB hbasis
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_additive_iff.mpr hbasis
  obtain ⟨n, hn, hdestroy⟩ := hstrong B hBA hB N
  obtain ⟨E, hER, hEB⟩ := hN n hn
  exact (hdestroy E hER) hEB

/-- Exact negative-answer criterion at order two.  An exact order-two basis
with cofinitely many canonical atoms at both orders two and three is strongly
minimal under infinite order-two deletions, while no infinite deletion leaves
an exact order-three basis. -/
theorem counterexample_of_cofiniteCanonicalAtoms_two_three
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hatomTwo : ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
      ∀ E ∈ additiveSupportFamily A 2 a, E = {a, 0})
    (hatomThree : ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
      ∀ G ∈ additiveSupportFamily A 3 a, G = {a, 0}) :
    IsExactTupleAsymptoticBasis A 2 ∧
      StrongInfiniteDeletion (additiveSupportFamily A 2) A ∧
      ∀ B, B ⊆ A → B.Infinite →
        ¬ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hstrongTwo :=
    strongInfiniteDeletion_of_cofiniteCanonicalAtoms hatomTwo
  have hstrongThree :=
    strongInfiniteDeletion_of_cofiniteCanonicalAtoms hatomThree
  exact ⟨hbasis, hstrongTwo,
    noInfiniteDeletionBasis_of_strongInfiniteDeletion hstrongThree⟩

end Erdos881
