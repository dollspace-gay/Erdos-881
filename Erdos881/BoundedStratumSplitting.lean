import Erdos881.BoundedPairFreeSet
import Erdos881.SplittableIndependentDeletion

/-!
# Splitting an infinite bounded-representation stratum

The recurrent bounded-representation residual supplies an infinite set of
targets which themselves belong to the order-two basis.  This file records a
first structural dichotomy on any such infinite reservoir.

An element is `PairSplittableAwayFromSelf` when it has an order-two support
which does not use the element itself.  On an infinite set of such elements,
the bounded point-map free-set theorem chooses an infinite deletion `B` for
which the selected support of every `b ∈ B` avoids all of `B`.  Thus every
deleted point splits into two points of `A \ B`.

If no infinite splittable subreservoir exists, there is instead an infinite
tail of zero-atoms: every order-two support of `a` is exactly `{a, 0}`.  This
is the rigid branch which remains for a fixed-translate/certificate attack.
-/

namespace Erdos881

/-- The target `a` has a two-term representation whose support does not use
`a` itself. -/
def PairSplittableAwayFromSelf (A : Set ℕ) (a : ℕ) : Prop :=
  ∃ E ∈ additiveSupportFamily A 2 a, a ∉ E

/-- Failure of `PairSplittableAwayFromSelf` forces every pair support to be
the canonical support `{a, 0}`. -/
theorem pairSupport_eq_self_zero_of_not_pairSplittableAwayFromSelf
    {A : Set ℕ} {a : ℕ}
    (hatom : ¬ PairSplittableAwayFromSelf A a)
    {E : Finset ℕ} (hER : E ∈ additiveSupportFamily A 2 a) :
    E = {a, 0} := by
  have haE : a ∈ E := by
    by_contra haE
    exact hatom ⟨E, hER, haE⟩
  have hpair :=
    additiveSupportFamily_two_eq_pairSupport_of_mem hER haE
  simpa [pairSupport] using hpair

/-- Point-map free-set thinning makes every chosen deleted point split into
two retained points. -/
theorem exists_infiniteDeletion_splittingDeletedPoints
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hsplit : ∀ a ∈ K, PairSplittableAwayFromSelf A a) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      DeletionSplitsIntoComplement A B := by
  classical
  let chooseSupport (a : ℕ) : Finset ℕ :=
    if h : PairSplittableAwayFromSelf A a then Classical.choose h else ∅
  have hchoose : ∀ a ∈ K,
      chooseSupport a ∈ additiveSupportFamily A 2 a ∧
        a ∉ chooseSupport a := by
    intro a haK
    have ha : PairSplittableAwayFromSelf A a := hsplit a haK
    simp only [chooseSupport, dif_pos ha]
    exact Classical.choose_spec ha
  have hcard : ∀ a ∈ K, (chooseSupport a).card ≤ 2 := by
    intro a haK
    exact additiveSupportFamily_cardAtMost A 2 a
      (chooseSupport a) (hchoose a haK).1
  have hself : ∀ a ∈ K, a ∉ chooseSupport a := by
    intro a haK
    exact (hchoose a haK).2
  obtain ⟨B, hBK, hB, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK chooseSupport 2 hcard hself
  refine ⟨B, hBK, hB, ?_⟩
  intro b hbB
  have hbK : b ∈ K := hBK hbB
  have hsupport := (hchoose b hbK).1
  obtain ⟨v, hvA, hvsum, hsupportEq⟩ :=
    mem_additiveSupportFamily_iff.mp hsupport
  have hdisj : Disjoint (tupleSupport v : Set ℕ) B := by
    rw [hsupportEq]
    exact hfree b hbB
  refine ⟨(v 0).1, (v 1).1, ?_, ?_, ?_⟩
  · refine ⟨hvA 0, ?_⟩
    intro hvB
    exact Set.disjoint_left.mp hdisj
      (mem_tupleSupport_iff.mpr ⟨0, rfl⟩) hvB
  · refine ⟨hvA 1, ?_⟩
    intro hvB
    exact Set.disjoint_left.mp hdisj
      (mem_tupleSupport_iff.mpr ⟨1, rfl⟩) hvB
  · simpa [Fin.sum_univ_two] using hvsum

/-- If zero is retained, deleted-point splitting already implies the full
relative self-basis property along `A`: deleted targets use their chosen
split, while retained targets use the tautological representation `0 + a`. -/
theorem exactTwoBasisAlong_self_of_zero_and_deletedSplits
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hsplit : DeletionSplitsIntoComplement A B) :
    IsExactTupleAsymptoticBasisAlong (A \ B) 2 A := by
  refine ⟨0, ?_⟩
  intro a _haNonnegative haA
  by_cases haB : a ∈ B
  · obtain ⟨u, v, huC, hvC, huv⟩ := hsplit a haB
    refine ⟨![u, v], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [huC, hvC]
    · simpa [Fin.sum_univ_two] using huv
  · refine ⟨![0, a], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [hzeroA, hzeroB, haA, haB]
    · simp [Fin.sum_univ_two]

/-- Shrinking a deletion preserves the property that all of its deleted
points split in the complement. -/
theorem DeletionSplitsIntoComplement.mono
    {A B B' : Set ℕ}
    (hsplit : DeletionSplitsIntoComplement A B)
    (hB'B : B' ⊆ B) :
    DeletionSplitsIntoComplement A B' := by
  intro b hbB'
  obtain ⟨u, v, hu, hv, huv⟩ := hsplit b (hB'B hbB')
  exact ⟨u, v,
    ⟨hu.1, fun huB' => hu.2 (hB'B huB')⟩,
    ⟨hv.1, fun hvB' => hv.2 (hB'B hvB')⟩,
    huv⟩

/-- Every infinite reservoir has either an infinite self-avoiding splittable
part or an infinite part on which every point is pair-atomic. -/
theorem infinite_pairSplittable_or_pairAtomic
    {A K : Set ℕ} (hK : K.Infinite) :
    {a | a ∈ K ∧ PairSplittableAwayFromSelf A a}.Infinite ∨
      {a | a ∈ K ∧ ¬ PairSplittableAwayFromSelf A a}.Infinite := by
  let S : Set ℕ :=
    {a | a ∈ K ∧ PairSplittableAwayFromSelf A a}
  let T : Set ℕ :=
    {a | a ∈ K ∧ ¬ PairSplittableAwayFromSelf A a}
  by_cases hS : S.Infinite
  · exact Or.inl hS
  · right
    by_contra hT
    have hfinite : (S ∪ T).Finite :=
      (Set.not_infinite.mp hS).union (Set.not_infinite.mp hT)
    apply hK
    apply hfinite.subset
    intro a haK
    by_cases ha : PairSplittableAwayFromSelf A a
    · exact Or.inl ⟨haK, ha⟩
    · exact Or.inr ⟨haK, ha⟩

/-- On a sufficiently late pair-atomic reservoir, the order-two basis
property forces `0 ∈ A`, and every support is exactly `{a, 0}`. -/
theorem infinite_zeroAtoms_of_infinite_pairAtomic
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite)
    (hatom : ∀ a ∈ K, ¬ PairSplittableAwayFromSelf A a) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧ 0 ∈ A ∧
      ∀ a ∈ L, ∀ E ∈ additiveSupportFamily A 2 a,
        E = {a, 0} := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  let L : Set ℕ := K \ Set.Iio N
  have hLK : L ⊆ K := Set.diff_subset
  have hL : L.Infinite := hK.diff (Set.finite_Iio N)
  obtain ⟨a, haL⟩ := hL.nonempty
  have haN : N ≤ a := Nat.le_of_not_gt haL.2
  obtain ⟨E, hER, _hEempty⟩ := hN a haN
  have hEEq : E = {a, 0} :=
    pairSupport_eq_self_zero_of_not_pairSplittableAwayFromSelf
      (hatom a (hLK haL)) hER
  have hzeroSupport : 0 ∈ E := by
    rw [hEEq]
    simp
  have hzeroA : 0 ∈ A :=
    additiveSupportFamily_supportsIn A 2 a E hER 0 hzeroSupport
  refine ⟨L, hLK, hL, hzeroA, ?_⟩
  intro b hbL E hER
  exact pairSupport_eq_self_zero_of_not_pairSplittableAwayFromSelf
    (hatom b (hLK hbL)) hER

/-- Structural dichotomy tailored to the deletion problem.  Either an
infinite subset of the reservoir already has the deleted-point splitting
property, or an infinite tail is in the explicit zero-atomic normal form. -/
theorem infiniteDeletionSplits_or_infiniteZeroAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite) :
    (∃ B, B ⊆ K ∧ B.Infinite ∧
      DeletionSplitsIntoComplement A B) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧ 0 ∈ A ∧
        ∀ a ∈ L, ∀ E ∈ additiveSupportFamily A 2 a,
          E = {a, 0} := by
  obtain hsplittable | hatomic :=
    infinite_pairSplittable_or_pairAtomic (A := A) hK
  · left
    let S : Set ℕ :=
      {a | a ∈ K ∧ PairSplittableAwayFromSelf A a}
    have hSK : S ⊆ K := fun a ha => ha.1
    obtain ⟨B, hBS, hB, hsplitB⟩ :=
      exists_infiniteDeletion_splittingDeletedPoints
        (K := S) hsplittable (fun a ha => ha.2)
    exact ⟨B, hBS.trans hSK, hB, hsplitB⟩
  · right
    let T : Set ℕ :=
      {a | a ∈ K ∧ ¬ PairSplittableAwayFromSelf A a}
    have hTK : T ⊆ K := fun a ha => ha.1
    obtain ⟨L, hLT, hL, hzero, hnormal⟩ :=
      infinite_zeroAtoms_of_infinite_pairAtomic hbasis hatomic
        (fun a ha => ha.2)
    exact ⟨L, hLT.trans hTK, hL, hzero, hnormal⟩

end Erdos881
