import Erdos881.ReflectionDefects

/-!
# Alternating repairs for finite destroyers

This file isolates the valid local exchange step behind an alternating
repair-tree approach.  It also records the basic hypergraph obstruction:
one-step repairs can cycle without combining into a support which avoids the
whole destroyer.  Any successful additive argument must use arithmetic
structure beyond this local exchange axiom.
-/

namespace Erdos881

/-- A finite destroyer is inclusion-minimal when erasing any one of its
vertices makes the target survivable. -/
def IsInclusionMinimalDestroyer
    (R : SupportFamily) (D : Finset ℕ) (n : ℕ) : Prop :=
  DestroysAt R (D : Set ℕ) n ∧
    ∀ x ∈ D, ¬ DestroysAt R ((D.erase x : Finset ℕ) : Set ℕ) n

/-- Every vertex of an inclusion-minimal destroyer has a private repair
support: that support meets the destroyer at exactly that vertex. -/
theorem IsInclusionMinimalDestroyer.exists_uniqueHitSupport
    {R : SupportFamily} {D : Finset ℕ} {n x : ℕ}
    (hminimal : IsInclusionMinimalDestroyer R D n)
    (hxD : x ∈ D) :
    ∃ E ∈ R n, E ∩ D = {x} := by
  obtain ⟨E, hER, hEeraseSet⟩ :=
    not_destroysAt_iff.mp (hminimal.2 x hxD)
  have hEerase : Disjoint E (D.erase x) := by
    rw [Finset.disjoint_left]
    intro y hyE hyDerase
    exact Set.disjoint_left.mp hEeraseSet
      (Finset.mem_coe.mpr hyE) (Finset.mem_coe.mpr hyDerase)
  obtain ⟨y, hyE, hyD⟩ :=
    Finset.not_disjoint_iff.mp <| by
      intro hED
      exact hminimal.1 E hER (by simpa using hED)
  have hyx : y = x := by
    by_contra hyx
    exact Finset.disjoint_left.mp hEerase hyE
      (Finset.mem_erase.mpr ⟨hyx, hyD⟩)
  subst y
  refine ⟨E, hER, ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨hzE, hzD⟩ := Finset.mem_inter.mp hz
    have hzx : z = x := by
      by_contra hzx
      exact Finset.disjoint_left.mp hEerase hzE
        (Finset.mem_erase.mpr ⟨hzx, hzD⟩)
    simp [hzx]
  · intro hz
    have hzx : z = x := by simpa using hz
    subst z
    exact Finset.mem_inter.mpr ⟨hyE, hxD⟩

/-- The private repair support remains alive after swapping out its unique
hit `x`, provided all newly deleted vertices avoid that support. -/
theorem IsInclusionMinimalDestroyer.exists_swapRepair
    {R : SupportFamily} {D F : Finset ℕ} {n x : ℕ}
    (hminimal : IsInclusionMinimalDestroyer R D n)
    (hxD : x ∈ D) (hF : ∀ E ∈ R n, E ∩ D = {x} → Disjoint E F) :
    ¬ DestroysAt R
      (((D.erase x ∪ F : Finset ℕ) : Set ℕ)) n := by
  obtain ⟨E, hER, hEunique⟩ :=
    hminimal.exists_uniqueHitSupport hxD
  apply not_destroysAt_iff.mpr
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro y hyE hyUnion
  obtain hyErase | hyF := Finset.mem_union.mp (Finset.mem_coe.mp hyUnion)
  · have hyD : y ∈ D := (Finset.mem_erase.mp hyErase).2
    have hyInter : y ∈ E ∩ D := Finset.mem_inter.mpr
      ⟨Finset.mem_coe.mp hyE, hyD⟩
    have hyx : y = x := by simpa [hEunique] using hyInter
    exact (Finset.mem_erase.mp hyErase).1 hyx
  · exact Finset.disjoint_left.mp (hF E hER hEunique)
      (Finset.mem_coe.mp hyE) hyF

/-! ## A local cycling obstruction -/

private noncomputable def triangleRepairSupportFamily : SupportFamily :=
  fun n => if n = 0 then {{0, 1}, {1, 2}, {0, 2}} else ∅

private def triangleDestroyer : Finset ℕ := {0, 1, 2}

private theorem triangleRepair_supports :
    triangleRepairSupportFamily 0 = {{0, 1}, {1, 2}, {0, 2}} := by
  simp [triangleRepairSupportFamily]

private theorem triangleRepair_destroyed :
    DestroysAt triangleRepairSupportFamily
      (triangleDestroyer : Set ℕ) 0 := by
  intro E hE
  rw [triangleRepair_supports] at hE
  simp only [Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with rfl | rfl | rfl
  · exact Set.not_disjoint_iff.mpr
      ⟨0, by simp, by simp [triangleDestroyer]⟩
  · exact Set.not_disjoint_iff.mpr
      ⟨1, by simp, by simp [triangleDestroyer]⟩
  · exact Set.not_disjoint_iff.mpr
      ⟨0, by simp, by simp [triangleDestroyer]⟩

private theorem triangleRepair_eachSingletonSurvives :
    ∀ x ∈ triangleDestroyer,
      ¬ DestroysAt triangleRepairSupportFamily ({x} : Set ℕ) 0 := by
  intro x hx
  simp only [triangleDestroyer, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · apply not_destroysAt_iff.mpr
    refine ⟨{1, 2}, by simp [triangleRepairSupportFamily], ?_⟩
    simp
  · apply not_destroysAt_iff.mpr
    refine ⟨{0, 2}, by simp [triangleRepairSupportFamily], ?_⟩
    simp
  · apply not_destroysAt_iff.mpr
    refine ⟨{0, 1}, by simp [triangleRepairSupportFamily], ?_⟩
    simp

private theorem triangleRepair_noOutsideSupport :
    ¬ ∃ E ∈ triangleRepairSupportFamily 0,
      Disjoint E triangleDestroyer := by
  rintro ⟨E, hE, hdisj⟩
  exact triangleRepair_destroyed E hE (by simpa using hdisj)

/-- Individually survivable singleton deletions have no abstract
augmentation theorem.  The triangle's three repairs cycle, while their
combined deletion still destroys the target.

This does not refute an additive alternating-tree argument; it proves that
such an argument must use a genuinely additive invariant (for example,
monotone target motion or complementary-pair arithmetic). -/
theorem alternating_singletonRepairs_can_cycle :
    DestroysAt triangleRepairSupportFamily
        (triangleDestroyer : Set ℕ) 0 ∧
      (∀ x ∈ triangleDestroyer,
        ¬ DestroysAt triangleRepairSupportFamily ({x} : Set ℕ) 0) ∧
      ¬ ∃ E ∈ triangleRepairSupportFamily 0,
        Disjoint E triangleDestroyer := by
  exact ⟨triangleRepair_destroyed,
    triangleRepair_eachSingletonSurvives,
    triangleRepair_noOutsideSupport⟩

end Erdos881
