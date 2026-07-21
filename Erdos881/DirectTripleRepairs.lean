import Erdos881.RigidDestroyerRepairs

/-!
# Direct order-three repairs for red-red pair sums

The splittable-independent bridge only fails when a late order-two
representation has both entries in the deletion.  This file permits that
case provided the corresponding target already has a surviving order-three
support.  It then gives a finite-injury recursion which arranges such a
support for every sum of two selected deletion points.
-/

open scoped BigOperators

namespace Erdos881

/-- Every sufficiently large target either has an order-two representation
which is not wholly deleted, or already has an order-three support disjoint
from the deletion. -/
def IsEventuallyPairIndependentOrBlueTriple
    (A B : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    (∃ x y, x ∈ A ∧ y ∈ A ∧ x + y = n ∧
      ¬ (x ∈ B ∧ y ∈ B)) ∨
    ∃ E ∈ additiveSupportFamily A 3 n,
      Disjoint (E : Set ℕ) B

/-- The mixed version of the splittable-independent bridge.  The ordinary
pair branch is handled exactly as before; the new branch is already the
required surviving order-three representation. -/
theorem exactThreeBasis_of_splittableIndependentOrBlueTriple
    {A B : Set ℕ}
    (hmixed : IsEventuallyPairIndependentOrBlueTriple A B)
    (hsplitB : DeletionSplitsIntoComplement A B)
    (hsplitC : ComplementEventuallySelfSplits A B) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨N, hN⟩ := hmixed
  obtain ⟨L, hL⟩ := hsplitC
  refine ⟨max N (2 * L), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N (2 * L)) hn
  have hnL : 2 * L ≤ n := le_trans (le_max_right N (2 * L)) hn
  obtain hpair | ⟨E, hER, hEB⟩ := hN n hnN
  · obtain ⟨x, y, hxA, hyA, hxy, hnotBoth⟩ := hpair
    by_cases hxB : x ∈ B
    · have hyB : y ∉ B := by
        intro hyB
        exact hnotBoth ⟨hxB, hyB⟩
      obtain ⟨u, v, huC, hvC, huv⟩ := hsplitB x hxB
      refine ⟨![u, v, y], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [huC, hvC, hyA, hyB]
      · simp [Fin.sum_univ_succ]
        omega
    · by_cases hyB : y ∈ B
      · obtain ⟨u, v, huC, hvC, huv⟩ := hsplitB y hyB
        refine ⟨![x, u, v], ?_, ?_⟩
        · intro i
          fin_cases i <;> simp [hxA, hxB, huC, hvC]
        · simp [Fin.sum_univ_succ]
          omega
      · have hxC : x ∈ A \ B := ⟨hxA, hxB⟩
        have hyC : y ∈ A \ B := ⟨hyA, hyB⟩
        by_cases hLx : L ≤ x
        · obtain ⟨u, v, huC, hvC, huv⟩ := hL x hxC hLx
          refine ⟨![u, v, y], ?_, ?_⟩
          · intro i
            fin_cases i <;> simp [huC, hvC, hyC]
          · simp [Fin.sum_univ_succ]
            omega
        · have hLy : L ≤ y := by omega
          obtain ⟨u, v, huC, hvC, huv⟩ := hL y hyC hLy
          refine ⟨![x, u, v], ?_, ?_⟩
          · intro i
            fin_cases i <;> simp [hxC, huC, hvC]
          · simp [Fin.sum_univ_succ]
            omega
  · obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    refine ⟨fun i => (v i).1, ?_, hvsum⟩
    intro i
    refine ⟨hvA i, ?_⟩
    intro hviB
    exact Set.disjoint_left.mp hEB
      (mem_tupleSupport_iff.mpr ⟨i, rfl⟩) hviB

/-- Every sum of two deleted points has a direct surviving order-three
support.  Unlike an alternative order-two support, the whole support is
required to be blue. -/
def HasDirectTripleRepairsForDeletedPairs
    (A B : Set ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B,
    ∃ E ∈ additiveSupportFamily A 3 (x + y),
      Disjoint (E : Set ℕ) B

/-- Direct repairs of red-red sums supply the mixed bridge from any
order-two basis. -/
theorem eventuallyPairIndependentOrBlueTriple_of_directRepairs
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hrepair : HasDirectTripleRepairsForDeletedPairs A B) :
    IsEventuallyPairIndependentOrBlueTriple A B := by
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨v, hvA, hvsum⟩ := hN n hn
  have hsum : v 0 + v 1 = n := by
    simpa [Fin.sum_univ_two] using hvsum
  by_cases hboth : v 0 ∈ B ∧ v 1 ∈ B
  · right
    obtain ⟨E, hER, hEB⟩ :=
      hrepair (v 0) hboth.1 (v 1) hboth.2
    rw [hsum] at hER
    exact ⟨E, hER, hEB⟩
  · left
    exact ⟨v 0, v 1, hvA 0, hvA 1, hsum, hboth⟩

/-- Direct triple repairs are preserved when the deletion is thinned. -/
theorem HasDirectTripleRepairsForDeletedPairs.mono
    {A B B' : Set ℕ}
    (h : HasDirectTripleRepairsForDeletedPairs A B)
    (hB'B : B' ⊆ B) :
    HasDirectTripleRepairsForDeletedPairs A B' := by
  intro x hx y hy
  obtain ⟨E, hER, hEB⟩ := h x (hB'B hx) y (hB'B hy)
  exact ⟨E, hER, hEB.mono_right hB'B⟩

/-- The splitting part of the tail reduction does not use pair
independence.  It can therefore be reused by the direct-repair bridge. -/
theorem exists_tail_with_splitting_of_selfBasis
    {A B : Set ℕ}
    (hBA : B ⊆ A) (hB : B.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A) :
    ∃ B' ⊆ B, B'.Infinite ∧
      DeletionSplitsIntoComplement A B' ∧
      ComplementEventuallySelfSplits A B' := by
  obtain ⟨L, hL⟩ := hself
  let B' : Set ℕ := B \ Set.Iio L
  have hB'B : B' ⊆ B := Set.diff_subset
  have hB'infinite : B'.Infinite := hB.diff (Set.finite_Iio L)
  have promote_split
      {a : ℕ} (haA : a ∈ A) (hLa : L ≤ a) :
      SplitsIntoTwo (A \ B') a := by
    obtain ⟨v, hvC, hvsum⟩ := hL a hLa haA
    refine ⟨v 0, v 1, ?_, ?_, ?_⟩
    · exact ⟨(hvC 0).1, fun hvB' => (hvC 0).2 hvB'.1⟩
    · exact ⟨(hvC 1).1, fun hvB' => (hvC 1).2 hvB'.1⟩
    · simpa [Fin.sum_univ_two] using hvsum
  refine ⟨B', hB'B, hB'infinite, ?_, ?_⟩
  · intro b hbB'
    exact promote_split (hBA hbB'.1) (Nat.le_of_not_gt hbB'.2)
  · refine ⟨L, ?_⟩
    intro c hc hLc
    exact promote_split hc.1 hLc

/-- A self-basis reservoir plus direct repairs already yields the desired
infinite deletion after discarding a finite initial segment. -/
theorem exists_infiniteDeletion_threeBasis_of_directTripleRepairs
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hBA : B ⊆ A) (hB : B.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A)
    (hrepair : HasDirectTripleRepairsForDeletedPairs A B) :
    ∃ B', B' ⊆ B ∧ B'.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B') 3 := by
  obtain ⟨B', hB'B, hB', hsplitB', hsplitC'⟩ :=
    exists_tail_with_splitting_of_selfBasis hBA hB hself
  have hrepair' := hrepair.mono hB'B
  have hmixed :=
    eventuallyPairIndependentOrBlueTriple_of_directRepairs hbasis hrepair'
  exact ⟨B', hB'B, hB',
    exactThreeBasis_of_splittableIndependentOrBlueTriple
      hmixed hsplitB' hsplitC'⟩

/-! ## What a strong-deletion certificate must encode -/

/-- At a late target, if deleted and retained summands can both be split as
in the mixed bridge, an order-three destroyer forces every chosen order-two
representation to be wholly deleted. -/
theorem pair_mem_deletion_of_orderThree_destroyer
    {A B : Set ℕ} {L n x y : ℕ}
    (hsplitB : DeletionSplitsIntoComplement A B)
    (hsplitC : ∀ c, c ∈ A \ B → L ≤ c →
      SplitsIntoTwo (A \ B) c)
    (hnL : 2 * L ≤ n)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) B n)
    (hxA : x ∈ A) (hyA : y ∈ A) (hxy : x + y = n) :
    x ∈ B ∧ y ∈ B := by
  have hnotuple :=
    destroysAt_additiveSupportFamily_iff.mp hdestroy
  by_cases hxB : x ∈ B
  · refine ⟨hxB, ?_⟩
    by_contra hyB
    obtain ⟨u, v, huC, hvC, huv⟩ := hsplitB x hxB
    apply hnotuple
    refine ⟨![u, v, y], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [huC, hvC, hyA, hyB]
    · simp [Fin.sum_univ_succ]
      omega
  · exfalso
    by_cases hyB : y ∈ B
    · obtain ⟨u, v, huC, hvC, huv⟩ := hsplitB y hyB
      apply hnotuple
      refine ⟨![x, u, v], ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hxA, hxB, huC, hvC]
      · simp [Fin.sum_univ_succ]
        omega
    ·
      have hxC : x ∈ A \ B := ⟨hxA, hxB⟩
      have hyC : y ∈ A \ B := ⟨hyA, hyB⟩
      by_cases hLx : L ≤ x
      · obtain ⟨u, v, huC, hvC, huv⟩ := hsplitC x hxC hLx
        apply hnotuple
        refine ⟨![u, v, y], ?_, ?_⟩
        · intro i
          fin_cases i <;> simp [huC, hvC, hyC]
        · simp [Fin.sum_univ_succ]
          omega
      · have hLy : L ≤ y := by omega
        obtain ⟨u, v, huC, hvC, huv⟩ := hsplitC y hyC hLy
        apply hnotuple
        refine ⟨![x, u, v], ?_, ?_⟩
        · intro i
          fin_cases i <;> simp [hxC, huC, hvC]
        · simp [Fin.sum_univ_succ]
          omega

/-- Under the same hypotheses, not merely one chosen pair but every
order-two support of the destroyed target is contained in the deletion. -/
theorem orderTwoSupport_subset_deletion_of_orderThree_destroyer
    {A B : Set ℕ} {L n : ℕ}
    (hsplitB : DeletionSplitsIntoComplement A B)
    (hsplitC : ∀ c, c ∈ A \ B → L ≤ c →
      SplitsIntoTwo (A \ B) c)
    (hnL : 2 * L ≤ n)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) B n) :
    ∀ E ∈ additiveSupportFamily A 2 n,
      (E : Set ℕ) ⊆ B := by
  intro E hER
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have hsum : (v 0).1 + (v 1).1 = n := by
    simpa [Fin.sum_univ_two] using hvsum
  have hboth := pair_mem_deletion_of_orderThree_destroyer
    hsplitB hsplitC hnL hdestroy
      (hvA 0) (hvA 1) hsum
  intro z hz
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hz
  fin_cases i
  · exact hi ▸ hboth.1
  · exact hi ▸ hboth.2

/-- Pairwise rigidity without rigid doubles forces every diagonal target to
have an order-two support escaping the rigid reservoir. -/
theorem exists_orderTwoSupport_not_subset_of_pairwiseRigid_noDoubles
    {A K : Set ℕ}
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K)
    {x : ℕ} (hxK : x ∈ K) :
    ∃ E ∈ additiveSupportFamily A 2 (x + x),
      ¬ (E : Set ℕ) ⊆ K := by
  classical
  have hnotRigid := hdouble x hxK
  simp only [IsRigidPairSum] at hnotRigid
  push Not at hnotRigid
  obtain ⟨E, hER, hEne⟩ := hnotRigid
  refine ⟨E, hER, ?_⟩
  intro hEsub
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have hsum : (v 0).1 + (v 1).1 = x + x := by
    simpa [Fin.sum_univ_two] using hvsum
  have hv0K : (v 0).1 ∈ K := hEsub
    (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
  have hv1K : (v 1).1 ∈ K := hEsub
    (mem_tupleSupport_iff.mpr ⟨1, rfl⟩)
  have hcanon : pairSupport (x + x) x ∈
      additiveSupportFamily A 2 (x + x) := by
    apply pairSupport_mem_additiveSupportFamily (by omega) (hKA hxK)
    have hsub : x + x - x = x := by omega
    rw [hsub]
    exact hKA hxK
  by_cases heq : (v 0).1 = (v 1).1
  · have hvx : (v 0).1 = x := by omega
    apply hEne
    have hpair := additiveSupportFamily_two_eq_pairSupport_of_mem
      (A := A) (n := x + x)
      (E := tupleSupport v) hER
      (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
    simpa [hvx] using hpair
  · have hrigidPair := hrigid (v 0).1 hv0K (v 1).1 hv1K heq
    have hER' : tupleSupport v ∈
        additiveSupportFamily A 2 ((v 0).1 + (v 1).1) := by
      rw [hsum]
      exact hER
    have hcanon' : pairSupport (x + x) x ∈
        additiveSupportFamily A 2 ((v 0).1 + (v 1).1) := by
      rw [hsum]
      exact hcanon
    exact hEne ((hrigidPair _ hER').trans
      (hrigidPair _ hcanon').symm)

/-- Combining the compact certificate `Q` with the splitting bridge: on a
tail of any self-basis reservoir, strong order-three deletion produces a
finite set `Q` such that every block selector contains both vertices of an
order-two representation of some `q ∈ Q`. -/
theorem strongDeletion_selfBasisTail_finitePairSumCertificate
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A) :
    ∃ M, ∃ K' ⊆ K, K'.Infinite ∧
      ∀ (F : ℕ → Finset ℕ)
        (_P : IsFiniteBlockPartition K' F),
        ∃ Q : Finset ℕ,
          (∀ q ∈ Q, M ≤ q) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          ∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q ∧
            (∀ E ∈ additiveSupportFamily A 2 q,
              (E : Set ℕ) ⊆ selectedSet s) ∧
            ∃ x ∈ selectedSet s, ∃ y ∈ selectedSet s,
              x + y = q := by
  obtain ⟨N, hN⟩ := hbasis
  obtain ⟨L, hL⟩ := hself
  let M := max N (2 * L)
  let K' : Set ℕ := K \ Set.Iio L
  have hK'K : K' ⊆ K := Set.diff_subset
  have hK' : K'.Infinite := hK.diff (Set.finite_Iio L)
  refine ⟨M, K', hK'K, hK', ?_⟩
  intro F _P
  have hK'A : K' ⊆ A :=
    fun x hx => hB₀A (hKB₀ (hK'K hx))
  obtain ⟨Q, hQM, hcert⟩ :=
    finiteBlockCertificates_on_subset_of_strongInfiniteDeletion
      hstrong hK'A F _P M
  refine ⟨Q, hQM, hcert, ?_⟩
  intro s
  obtain ⟨q, hqQ, hqdestroy⟩ := hcert s
  have hqM : M ≤ q := hQM q hqQ
  have hqN : N ≤ q := le_trans (le_max_left _ _) hqM
  have hqL : 2 * L ≤ q := le_trans (le_max_right _ _) hqM
  obtain ⟨v, hvA, hvsum⟩ := hN q hqN
  have hsum : v 0 + v 1 = q := by
    simpa [Fin.sum_univ_two] using hvsum
  have hsK' : selectedSet s ⊆ K' := _P.selectedSet_subset s
  have hsB₀ : selectedSet s ⊆ B₀ :=
    fun x hx => hKB₀ (hK'K (hsK' hx))
  have hsplitB : DeletionSplitsIntoComplement A (selectedSet s) := by
    intro b hbS
    have hbK' := hsK' hbS
    have hbL : L ≤ b := Nat.le_of_not_gt hbK'.2
    obtain ⟨w, hwC, hwsum⟩ := hL b hbL (hK'A hbK')
    refine ⟨w 0, w 1, ?_, ?_, ?_⟩
    · exact ⟨(hwC 0).1, fun hwS => (hwC 0).2 (hsB₀ hwS)⟩
    · exact ⟨(hwC 1).1, fun hwS => (hwC 1).2 (hsB₀ hwS)⟩
    · simpa [Fin.sum_univ_two] using hwsum
  have hsplitC : ∀ c, c ∈ A \ selectedSet s → L ≤ c →
      SplitsIntoTwo (A \ selectedSet s) c := by
    intro c hc hLc
    obtain ⟨w, hwC, hwsum⟩ := hL c hLc hc.1
    refine ⟨w 0, w 1, ?_, ?_, ?_⟩
    · exact ⟨(hwC 0).1, fun hwS => (hwC 0).2 (hsB₀ hwS)⟩
    · exact ⟨(hwC 1).1, fun hwS => (hwC 1).2 (hsB₀ hwS)⟩
    · simpa [Fin.sum_univ_two] using hwsum
  have hboth := pair_mem_deletion_of_orderThree_destroyer
    hsplitB hsplitC hqL hqdestroy
      (hvA 0) (hvA 1) hsum
  have hallPairs :=
    orderTwoSupport_subset_deletion_of_orderThree_destroyer
      hsplitB hsplitC hqL hqdestroy
  exact ⟨q, hqQ, hqdestroy, hallPairs,
    v 0, hboth.1, v 1, hboth.2, hsum⟩

/-- On the rigid Ramsey branch with no rigid doubles, the finite certificate
is a genuine loop-free finite edge certificate.  Every selector contains
both endpoints of one edge labelled by `q ∈ Q`, and rigidity makes that
edge the unique ambient order-two support of `q`. -/
theorem strongDeletion_rigidSelfBasisTail_finiteEdgeCertificate
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ M, ∃ K' ⊆ K, K'.Infinite ∧
      ∀ (F : ℕ → Finset ℕ)
        (_P : IsFiniteBlockPartition K' F),
        ∃ Q : Finset ℕ,
          (∀ q ∈ Q, M ≤ q) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          ∀ s : BlockSelector F, ∃ q ∈ Q,
            ∃ x ∈ selectedSet s, ∃ y ∈ selectedSet s,
              x ≠ y ∧ x + y = q ∧
              ∀ E ∈ additiveSupportFamily A 2 q,
                E = pairSupport q x := by
  obtain ⟨M, K', hK'K, hK', hbase⟩ :=
    strongDeletion_selfBasisTail_finitePairSumCertificate
      hstrong hbasis hB₀A hKB₀ hK hself
  have hK'A : K' ⊆ A := fun x hx => hB₀A (hKB₀ (hK'K hx))
  have hrigid' : IsPairwiseRigidSet A K' := by
    intro x hx y hy hxy
    exact hrigid x (hK'K hx) y (hK'K hy) hxy
  have hdouble' : HasNoRigidDoubles A K' := by
    intro x hx
    exact hdouble x (hK'K hx)
  refine ⟨M, K', hK'K, hK', ?_⟩
  intro F _P
  obtain ⟨Q, hQM, hcert, hpairs⟩ := hbase F _P
  refine ⟨Q, hQM, hcert, ?_⟩
  intro s
  obtain ⟨q, hqQ, hqdestroy, hallPairs,
      x, hxS, y, hyS, hxy⟩ := hpairs s
  have hxK' : x ∈ K' := _P.selectedSet_subset s hxS
  have hyK' : y ∈ K' := _P.selectedSet_subset s hyS
  have hxyNe : x ≠ y := by
    intro hxyEq
    subst y
    obtain ⟨E, hER, hEexternal⟩ :=
      exists_orderTwoSupport_not_subset_of_pairwiseRigid_noDoubles
        hK'A hrigid' hdouble' hxK'
    have hEqTarget : x + x = q := hxy
    have hERq : E ∈ additiveSupportFamily A 2 q := by
      rw [← hEqTarget]
      exact hER
    apply hEexternal
    intro z hzE
    exact _P.selectedSet_subset s (hallPairs E hERq hzE)
  refine ⟨q, hqQ, x, hxS, y, hyS, hxyNe, hxy, ?_⟩
  intro E hER
  have hrigidXY := hrigid' x hxK' y hyK' hxyNe
  have hER' : E ∈ additiveSupportFamily A 2 (x + y) := by
    rw [hxy]
    exact hER
  have hEq := hrigidXY E hER'
  rw [hxy] at hEq
  exact hEq

/-- A finite unique-edge certificate necessarily covers one entire block by
the union of finitely many order-two supports.  This is the precise finite
graph obstruction left by `Q`; the covered block has size at most twice the
number of used certificate targets. -/
theorem finiteUniquePairEdgeCertificate_exists_small_coveredBlock
    {A K : Set ℕ} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hKA : K ⊆ A)
    (P : IsFiniteBlockPartition K F)
    (hedge : ∀ s : BlockSelector F, ∃ q ∈ Q,
      ∃ x ∈ selectedSet s, ∃ y ∈ selectedSet s,
        x ≠ y ∧ x + y = q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          E = pairSupport q x) :
    ∃ Q' : Finset ℕ, Q' ⊆ Q ∧
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q',
        ∃ i, F i ⊆ finiteSupportChoiceUnion c ∧
          (F i).card ≤ 2 * Q'.card := by
  classical
  let Used : ℕ → Prop := fun q =>
    ∃ s : BlockSelector F, ∃ x ∈ selectedSet s,
      ∃ y ∈ selectedSet s,
        x ≠ y ∧ x + y = q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          E = pairSupport q x
  let Q' : Finset ℕ := Q.filter Used
  have hQ'Q : Q' ⊆ Q := Finset.filter_subset _ _
  have hused : ∀ q : {q // q ∈ Q'}, Used q.1 := by
    intro q
    exact (Finset.mem_filter.mp q.2).2
  have hsupport : ∀ q : {q // q ∈ Q'},
      ∃ E, E ∈ additiveSupportFamily A 2 q.1 := by
    intro q
    obtain ⟨s, x, hxS, y, hyS, _hxyNe, hxy, _hunique⟩ := hused q
    have hxA : x ∈ A := hKA (P.selectedSet_subset s hxS)
    have hyA : y ∈ A := hKA (P.selectedSet_subset s hyS)
    have hxq : x ≤ q.1 := by omega
    have hsub : q.1 - x = y := by omega
    exact ⟨pairSupport q.1 x,
      pairSupport_mem_additiveSupportFamily
        hxq hxA (hsub ▸ hyA)⟩
  choose support hsupportMem using hsupport
  let c : FiniteSupportChoice (additiveSupportFamily A 2) Q' :=
    fun q => ⟨support q, hsupportMem q⟩
  have hcertTwo : ∀ s : BlockSelector F, ∃ q ∈ Q',
      DestroysAt (additiveSupportFamily A 2) (selectedSet s) q := by
    intro s
    obtain ⟨q, hqQ, x, hxS, y, hyS, hxyNe, hxy, hunique⟩ :=
      hedge s
    have hqUsed : Used q :=
      ⟨s, x, hxS, y, hyS, hxyNe, hxy, hunique⟩
    refine ⟨q, Finset.mem_filter.mpr ⟨hqQ, hqUsed⟩, ?_⟩
    intro E hER
    rw [hunique E hER]
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, by simp [pairSupport], hxS⟩
  obtain ⟨i, hiCover, hiCard⟩ :=
    exists_small_covered_block_of_certificate
      (additiveSupportFamily_cardAtMost A 2) hcertTwo c
  exact ⟨Q', hQ'Q, c, i, hiCover, hiCard⟩

/-! ## A superincreasing finite-extension recursion -/

/-- A fresh point directly repairs its sums with the finite deletion prefix,
including its diagonal sum. -/
def HasFreshDirectTripleRepairExtension
    (A K : Set ℕ) (D : Finset ℕ) (T : ℕ) : Prop :=
  ∃ b, b ∈ K ∧ b ∉ D ∧ T ≤ b ∧
    ∀ d ∈ insert b D,
      ∃ E ∈ additiveSupportFamily A 3 (b + d),
        Disjoint (E : Set ℕ) (insert b D : Set ℕ)

/-- Exact logical form of a failed direct-repair extension: every eligible
candidate creates a pair sum destroyed by the enlarged finite prefix. -/
theorem not_hasFreshDirectTripleRepairExtension_iff
    {A K : Set ℕ} {D : Finset ℕ} {T : ℕ} :
    ¬ HasFreshDirectTripleRepairExtension A K D T ↔
      ∀ b, b ∈ K → b ∉ D → T ≤ b →
        ∃ d ∈ insert b D,
          DestroysAt (additiveSupportFamily A 3)
            (insert b D : Set ℕ) (b + d) := by
  classical
  simp only [HasFreshDirectTripleRepairExtension, DestroysAt]
  push Not
  rfl

/-- Name for the finite moving-destroyer obstruction exposed by a failed
direct-repair stage. -/
def HasFiniteDirectTripleRepairObstruction
    (A K : Set ℕ) (D : Finset ℕ) (T : ℕ) : Prop :=
  ∀ b, b ∈ K → b ∉ D → T ≤ b →
    ∃ d ∈ insert b D,
      DestroysAt (additiveSupportFamily A 3)
        (insert b D : Set ℕ) (b + d)

theorem not_hasFreshDirectTripleRepairExtension_iff_obstruction
    {A K : Set ℕ} {D : Finset ℕ} {T : ℕ} :
    ¬ HasFreshDirectTripleRepairExtension A K D T ↔
      HasFiniteDirectTripleRepairObstruction A K D T :=
  not_hasFreshDirectTripleRepairExtension_iff

/-- Pigeonholing the old finite prefix reduces any failed stage to one of
two moving target families: diagonal targets `b+b`, or translates `b+d`
for one fixed old deletion point `d`. -/
theorem HasFiniteDirectTripleRepairObstruction.infinite_diagonal_or_fixed
    {A K : Set ℕ} {D : Finset ℕ} {T : ℕ}
    (h : HasFiniteDirectTripleRepairObstruction A K D T)
    (hK : K.Infinite) :
    {b | b ∈ K ∧
      DestroysAt (additiveSupportFamily A 3)
        (insert b D : Set ℕ) (b + b)}.Infinite ∨
      ∃ d ∈ D, {b | b ∈ K ∧
        DestroysAt (additiveSupportFamily A 3)
          (insert b D : Set ℕ) (b + d)}.Infinite := by
  classical
  let X : Set ℕ := K \ ((D : Set ℕ) ∪ Set.Iio T)
  have hfiniteExcluded : ((D : Set ℕ) ∪ Set.Iio T).Finite :=
    D.finite_toSet.union (Set.finite_Iio T)
  have hX : X.Infinite := hK.diff hfiniteExcluded
  by_cases hdiag : {b | b ∈ K ∧
      DestroysAt (additiveSupportFamily A 3)
        (insert b D : Set ℕ) (b + b)}.Infinite
  · exact Or.inl hdiag
  · right
    by_contra hnofixed
    push Not at hnofixed
    have hdiagFinite : {b | b ∈ K ∧
        DestroysAt (additiveSupportFamily A 3)
          (insert b D : Set ℕ) (b + b)}.Finite :=
      Set.not_infinite.mp hdiag
    have hfixedFinite : ∀ d ∈ (D : Set ℕ),
        {b | b ∈ K ∧
          DestroysAt (additiveSupportFamily A 3)
            (insert b D : Set ℕ) (b + d)}.Finite := by
      intro d hdD
      exact hnofixed d hdD
    have hunionFinite :
        ({b | b ∈ K ∧
          DestroysAt (additiveSupportFamily A 3)
            (insert b D : Set ℕ) (b + b)} ∪
          ⋃ d ∈ (D : Set ℕ),
            {b | b ∈ K ∧
              DestroysAt (additiveSupportFamily A 3)
                (insert b D : Set ℕ) (b + d)}).Finite := by
      apply hdiagFinite.union
      exact D.finite_toSet.biUnion hfixedFinite
    apply hX
    apply hunionFinite.subset
    intro b hbX
    have hbK : b ∈ K := hbX.1
    have hbD : b ∉ D := by
      intro hbD
      exact hbX.2 (Or.inl hbD)
    have hbT : T ≤ b := Nat.le_of_not_gt fun hbLt =>
      hbX.2 (Or.inr hbLt)
    obtain ⟨d, hd, hdestroy⟩ := h b hbK hbD hbT
    rcases Finset.mem_insert.mp hd with rfl | hdD
    · exact Or.inl ⟨hbK, hdestroy⟩
    · exact Or.inr (Set.mem_iUnion₂.mpr
        ⟨d, hdD, hbK, hdestroy⟩)

/-- Every finite order-three destroyer contains a minimal destroyer in one
of the small, disjoint-repair, or common-anchor forms. -/
theorem finiteOrderThreeDestroyer_minimal_trichotomy
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) (D : Set ℕ) n) :
    ∃ D₀ : Finset ℕ, D₀ ⊆ D ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) D₀ n ∧
      (D₀.card ≤ 3 ∨
        HasTwoDisjointUniqueHitRepairs
          (additiveSupportFamily A 3) D₀ n ∨
        (4 ≤ D₀.card ∧
          HasCommonAnchorOrderThreeRepairs A D₀ n)) := by
  obtain ⟨D₀, hD₀D, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hdestroy
  refine ⟨D₀, hD₀D, hminimal, ?_⟩
  by_cases hsmall : D₀.card ≤ 3
  · exact Or.inl hsmall
  · have hfour : 4 ≤ D₀.card := by omega
    obtain hrepairs | hanchor :=
      minimalOrderThreeDestroyer_disjointRepairs_or_commonAnchor
        hminimal hfour
    · exact Or.inr (Or.inl hrepairs)
    · exact Or.inr (Or.inr ⟨hfour, hanchor⟩)

/-- On a pairwise-rigid reservoir, every large-minimal destroyer arising
from a failed extension has an almost-global unique-hit support.  Thus the
remaining obstruction is already in the exact form needed for a finite
anchor injury. -/
theorem HasFiniteDirectTripleRepairObstruction.rigid_minimal_trichotomy
    {A K : Set ℕ} {D : Finset ℕ} {T : ℕ}
    (h : HasFiniteDirectTripleRepairObstruction A K D T)
    (hDK : (D : Set ℕ) ⊆ K)
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K) :
    ∀ b, b ∈ K → b ∉ D → T ≤ b →
      ∃ d ∈ insert b D, ∃ D₀ : Finset ℕ,
        D₀ ⊆ insert b D ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A 3) D₀ (b + d) ∧
        (D₀.card ≤ 3 ∨
          HasTwoDisjointUniqueHitRepairs
            (additiveSupportFamily A 3) D₀ (b + d) ∨
          ∃ z, ∃ x : {x // x ∈ D₀},
            ∃ E ∈ additiveSupportFamily A 3 (b + d),
              x.1 ∈ E ∧
              (((E : Set ℕ) ∩ K) ⊆ ({x.1, z} : Set ℕ)) ∧
              (z ∉ K →
                ((E : Set ℕ) ∩ K) = ({x.1} : Set ℕ))) := by
  intro b hbK hbD hbT
  obtain ⟨d, hd, hdestroy⟩ := h b hbK hbD hbT
  have hdestroy' : DestroysAt (additiveSupportFamily A 3)
      ((insert b D : Finset ℕ) : Set ℕ) (b + d) := by
    simpa using hdestroy
  obtain ⟨D₀, hD₀sub, hminimal, htri⟩ :=
    finiteOrderThreeDestroyer_minimal_trichotomy hdestroy'
  refine ⟨d, hd, D₀, hD₀sub, hminimal, ?_⟩
  rcases htri with hsmall | hrepairs | hanchor
  · exact Or.inl hsmall
  · exact Or.inr (Or.inl hrepairs)
  · right; right
    obtain ⟨hfour, hanchor⟩ := hanchor
    obtain ⟨c, z, hz⟩ := hanchor
    have hinsertK : ((insert b D : Finset ℕ) : Set ℕ) ⊆ K := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxD
      · exact hbK
      · exact hDK hxD
    have hD₀K : (D₀ : Set ℕ) ⊆ K :=
      fun x hx => hinsertK (hD₀sub hx)
    obtain ⟨x, E, hER, hxE, hEK, hunique⟩ :=
      commonAnchor_exists_almostGlobalUniqueHit
        c hz hfour hD₀K hKA hrigid
    exact ⟨z, x, E, hER, hxE, hEK, hunique⟩

/-- Data chosen at one stage of the direct-repair recursion. -/
structure DirectTripleRepairRecursionStep
    (A K : Set ℕ) (D : Finset ℕ) (last : ℕ) where
  point : ℕ
  point_mem : point ∈ K
  point_not_chosen : point ∉ D
  point_lower : 2 * last + 1 ≤ point
  support : {d // d ∈ insert point D} → Finset ℕ
  support_mem : ∀ d,
    support d ∈ additiveSupportFamily A 3 (point + d.1)
  support_disjoint : ∀ d,
    Disjoint (support d : Set ℕ) (insert point D : Set ℕ)

theorem directTripleRepairRecursionStep_nonempty
    {A K : Set ℕ} {D : Finset ℕ} {last : ℕ}
    (hext : HasFreshDirectTripleRepairExtension
      A K D (2 * last + 1)) :
    Nonempty (DirectTripleRepairRecursionStep A K D last) := by
  classical
  obtain ⟨b, hbK, hbD, hbLower, hrepair⟩ := hext
  have hsupport : ∀ d : {d // d ∈ insert b D},
      ∃ E ∈ additiveSupportFamily A 3 (b + d.1),
        Disjoint (E : Set ℕ) (insert b D : Set ℕ) :=
    fun d => hrepair d.1 d.2
  choose support hsupportMem hsupportDisjoint using hsupport
  exact ⟨{
    point := b
    point_mem := hbK
    point_not_chosen := hbD
    point_lower := hbLower
    support := support
    support_mem := hsupportMem
    support_disjoint := hsupportDisjoint
  }⟩

/-- Finite state of the direct-repair recursion. -/
structure DirectTripleRepairRecursionState (K : Set ℕ) where
  chosen : Finset ℕ
  last : ℕ
  chosen_subset : (chosen : Set ℕ) ⊆ K

set_option maxHeartbeats 800000 in
/-- If every finite prefix admits a fresh direct-repair extension, a
superincreasing recursion produces an infinite deletion for which every
red-red pair sum has a blue order-three support. -/
theorem exists_directTripleRepairDeletion_of_freshExtensions
    {A K : Set ℕ}
    (hext : ∀ (D : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshDirectTripleRepairExtension A K D T) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasDirectTripleRepairsForDeletedPairs A B := by
  classical
  let State := DirectTripleRepairRecursionState K
  let initial : State := {
    chosen := ∅
    last := 0
    chosen_subset := by simp
  }
  let chooseStep : (s : State) →
      DirectTripleRepairRecursionStep A K s.chosen s.last :=
    fun s => Classical.choice <|
      directTripleRepairRecursionStep_nonempty
        (hext s.chosen s.chosen_subset (2 * s.last + 1))
  let advance (s : State) : State := {
    chosen := insert (chooseStep s).point s.chosen
    last := (chooseStep s).point
    chosen_subset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxOld
      · exact (chooseStep s).point_mem
      · exact s.chosen_subset hxOld
  }
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let step (i : ℕ) := chooseStep (state i)
  let b (i : ℕ) := (step i).point
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    change Nat.rec initial (fun _ s => advance s) (i + 1) =
      advance (Nat.rec initial (fun _ s => advance s) i)
    exact Nat.rec_add_one initial (fun _ s => advance s) i
  have hchosen_succ : ∀ i,
      (state (i + 1)).chosen = insert (b i) (state i).chosen := by
    intro i
    change (state (i + 1)).chosen =
      insert (chooseStep (state i)).point (state i).chosen
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).last = b i := by
    intro i
    change (state (i + 1)).last = (chooseStep (state i)).point
    rw [hstate_succ]
  have hchosen_step : ∀ i,
      (state i).chosen ⊆ (state (i + 1)).chosen := by
    intro i
    rw [hchosen_succ]
    exact Finset.subset_insert _ _
  have hchosen_mono : Monotone fun i => (state i).chosen :=
    monotone_nat_of_le_succ hchosen_step
  have hb_chosen_next : ∀ i, b i ∈ (state (i + 1)).chosen := by
    intro i
    rw [hchosen_succ]
    exact Finset.mem_insert_self _ _
  have hbK : ∀ i, b i ∈ K := fun i => (step i).point_mem
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower := (step (i + 1)).point_lower
    change 2 * (state (i + 1)).last + 1 ≤ b (i + 1) at hlower
    rw [hlast_succ] at hlower
    omega
  have hsuper : ∀ i, 2 * b i < b (i + 1) := by
    intro i
    have hlower := (step (i + 1)).point_lower
    change 2 * (state (i + 1)).last + 1 ≤ b (i + 1) at hlower
    rw [hlast_succ] at hlower
    omega
  have hprior_chosen : ∀ {i j}, i < j → b i ∈ (state j).chosen := by
    intro i j hij
    exact hchosen_mono (Nat.succ_le_of_lt hij) (hb_chosen_next i)
  have hfuture : ∀ {i j}, i < j → 2 * b i < b j := by
    intro i j hij
    exact lt_of_lt_of_le (hsuper i)
      (hbmono.monotone (Nat.succ_le_of_lt hij))
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbK i
  · intro x hxB y hyB
    obtain ⟨i, rfl⟩ := hxB
    obtain ⟨j, rfl⟩ := hyB
    rcases le_total i j with hij | hji
    · have hbi : b i ∈ insert (b j) (state j).chosen := by
        by_cases hijEq : i = j
        · subst i
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hprior_chosen (lt_of_le_of_ne hij hijEq))
      let d : {d // d ∈ insert (b j) (state j).chosen} := ⟨b i, hbi⟩
      let E := (step j).support d
      refine ⟨E, ?_, ?_⟩
      · have hmem := (step j).support_mem d
        change E ∈ additiveSupportFamily A 3 (b j + b i) at hmem
        rw [Nat.add_comm] at hmem
        exact hmem
      · rw [Set.disjoint_left]
        intro z hzE hzB
        obtain ⟨k, hk⟩ := hzB
        by_cases hkj : k ≤ j
        · have hbkCurrent : b k ∈ insert (b j) (state j).chosen := by
            by_cases hkjEq : k = j
            · subst k
              exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert_of_mem
                (hprior_chosen (lt_of_le_of_ne hkj hkjEq))
          apply Set.disjoint_left.mp ((step j).support_disjoint d) hzE
          have hzCurrent :
              z ∈ (insert (step j).point (state j).chosen : Finset ℕ) := by
            rw [← hk]
            simpa only [b] using hbkCurrent
          simpa using hzCurrent
        · have hjk : j < k := Nat.lt_of_not_ge hkj
          have hzle : z ≤ b j + b i :=
            additiveSupportFamily_supportsBounded A 3
              (b j + b i) E ((step j).support_mem d) z hzE
          have hbile : b i ≤ b j := hbmono.monotone hij
          have htarget : b j + b i ≤ 2 * b j := by omega
          have hlate := hfuture hjk
          omega
    · have hbj : b j ∈ insert (b i) (state i).chosen := by
        by_cases hjiEq : j = i
        · subst j
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hprior_chosen (lt_of_le_of_ne hji hjiEq))
      let d : {d // d ∈ insert (b i) (state i).chosen} := ⟨b j, hbj⟩
      let E := (step i).support d
      refine ⟨E, (step i).support_mem d, ?_⟩
      rw [Set.disjoint_left]
      intro z hzE hzB
      obtain ⟨k, hk⟩ := hzB
      by_cases hki : k ≤ i
      · have hbkCurrent : b k ∈ insert (b i) (state i).chosen := by
          by_cases hkiEq : k = i
          · subst k
            exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem
              (hprior_chosen (lt_of_le_of_ne hki hkiEq))
        apply Set.disjoint_left.mp ((step i).support_disjoint d) hzE
        have hzCurrent :
            z ∈ (insert (step i).point (state i).chosen : Finset ℕ) := by
          rw [← hk]
          simpa only [b] using hbkCurrent
        simpa using hzCurrent
      · have hik : i < k := Nat.lt_of_not_ge hki
        have hzle : z ≤ b i + b j :=
          additiveSupportFamily_supportsBounded A 3
            (b i + b j) E ((step i).support_mem d) z hzE
        have hbjle : b j ≤ b i := hbmono.monotone hji
        have htarget : b i + b j ≤ 2 * b i := by omega
        have hlate := hfuture hik
        omega

/-- The constructive target now has a single finite-stage arithmetic
obligation: fresh direct triple repairs. -/
theorem exists_infiniteDeletion_threeBasis_of_freshDirectTripleExtensions
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hext : ∀ (D : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshDirectTripleRepairExtension A K D T) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hBK, hB, hrepair⟩ :=
    exists_directTripleRepairDeletion_of_freshExtensions hext
  have hBA : B ⊆ A := fun x hx => hB₀A (hKB₀ (hBK hx))
  have hself' : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A :=
    exactTwoBasisAlong_self_of_deletion_subset
      (fun x hx => hKB₀ (hBK hx)) hself
  obtain ⟨B', hB'B, hB', hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_directTripleRepairs
      hbasis hBA hB hself' hrepair
  exact ⟨B', fun x hx => hBK (hB'B hx), hB', hthree⟩

/-- Under the contradictory strong-deletion hypothesis, the fresh-extension
property must fail at some finite stage.  This closes the logical loop
between the constructive recursion and strong deletion: only the finite
moving-destroyer obstruction can remain. -/
theorem strongDeletion_forces_failedDirectTripleRepairStage
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ K ∧
      ∃ T, ¬ HasFreshDirectTripleRepairExtension A K D T := by
  by_contra hnoFailure
  push Not at hnoFailure
  have hext : ∀ (D : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshDirectTripleRepairExtension A K D T := by
    intro D hDK T
    exact hnoFailure D hDK T
  obtain ⟨B, hBK, hB, hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_freshDirectTripleExtensions
      hbasis hB₀A hself hKB₀ hext
  have hBA : B ⊆ A := fun x hx => hB₀A (hKB₀ (hBK hx))
  obtain ⟨N, hN⟩ := hthree
  obtain ⟨n, hn, hdestroy⟩ := hstrong B hBA hB N
  obtain ⟨v, hvC, hvsum⟩ := hN n hn
  have hsurvive : ∃ E ∈ additiveSupportFamily A 3 n,
      Disjoint (E : Set ℕ) B :=
    exists_surviving_additiveSupport_iff.mpr ⟨v, hvC, hvsum⟩
  exact (not_destroysAt_iff.mpr hsurvive) hdestroy

/-- Consequently strong deletion forces one explicit stabilized moving
family: infinitely many diagonal finite destroyers, or infinitely many
destroyers at one fixed translate `b+d`. -/
theorem strongDeletion_forces_diagonal_or_fixedTripleDestroyers
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ K ∧
      ({b | b ∈ K ∧
        DestroysAt (additiveSupportFamily A 3)
          (insert b D : Set ℕ) (b + b)}.Infinite ∨
        ∃ d ∈ D, {b | b ∈ K ∧
          DestroysAt (additiveSupportFamily A 3)
            (insert b D : Set ℕ) (b + d)}.Infinite) := by
  obtain ⟨D, hDK, T, hfail⟩ :=
    strongDeletion_forces_failedDirectTripleRepairStage
      hstrong hbasis hB₀A hself hKB₀
  have hobstruction : HasFiniteDirectTripleRepairObstruction A K D T :=
    not_hasFreshDirectTripleRepairExtension_iff_obstruction.mp hfail
  exact ⟨D, hDK,
    hobstruction.infinite_diagonal_or_fixed hK⟩

end Erdos881
