import Erdos881.FiniteSearchCounterexamples

/-!
# Splittable independent deletions

This file gives a zero-free sufficient condition for an infinite deletion to
leave an exact order-three basis.  It separates the arithmetic replacement
step from the remaining selection problem.
-/

open scoped BigOperators

namespace Erdos881

/-- `a` can be replaced by two summands from `C`. -/
def SplitsIntoTwo (C : Set ℕ) (a : ℕ) : Prop :=
  ∃ u v, u ∈ C ∧ v ∈ C ∧ u + v = a

/-- Every sufficiently large target has a two-term representation from `A`
whose two entries are not both in the proposed deletion `B`. -/
def IsEventuallyPairIndependentDeletion
    (A B : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    ∃ x y, x ∈ A ∧ y ∈ A ∧ x + y = n ∧
      ¬ (x ∈ B ∧ y ∈ B)

/-- All deleted elements split in the complement. -/
def DeletionSplitsIntoComplement (A B : Set ℕ) : Prop :=
  ∀ b ∈ B, SplitsIntoTwo (A \ B) b

/-- Every sufficiently large retained element splits again inside the
retained set. -/
def ComplementEventuallySelfSplits (A B : Set ℕ) : Prop :=
  ∃ L, ∀ c, c ∈ A \ B → L ≤ c →
    SplitsIntoTwo (A \ B) c

/-- The complete structural package sought from the selection argument. -/
def IsSplittableIndependentDeletion (A B : Set ℕ) : Prop :=
  B ⊆ A ∧ B.Infinite ∧
    IsEventuallyPairIndependentDeletion A B ∧
    DeletionSplitsIntoComplement A B ∧
    ComplementEventuallySelfSplits A B

/-- Zero-free splittable-independent-deletion theorem.

For a late pair `n = x + y`, there are three cases.  If exactly one entry is
deleted, split that entry into two retained terms.  If neither is deleted,
then one entry is at least half of `n`; beyond `2 * L` it can be split inside
the complement.  The excluded fourth case is that both entries lie in `B`. -/
theorem exactThreeBasis_of_splittableIndependentDeletion
    {A B : Set ℕ}
    (hpair : IsEventuallyPairIndependentDeletion A B)
    (hsplitB : DeletionSplitsIntoComplement A B)
    (hsplitC : ComplementEventuallySelfSplits A B) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨N, hN⟩ := hpair
  obtain ⟨L, hL⟩ := hsplitC
  refine ⟨max N (2 * L), ?_⟩
  intro n hn
  have hnN : N ≤ n := le_trans (le_max_left N (2 * L)) hn
  have hnL : 2 * L ≤ n := le_trans (le_max_right N (2 * L)) hn
  obtain ⟨x, y, hxA, hyA, hxy, hnotBoth⟩ := hN n hnN
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

/-- A splittable independent deletion immediately solves the desired
selection problem. -/
theorem IsSplittableIndependentDeletion.exactThreeBasis
    {A B : Set ℕ}
    (h : IsSplittableIndependentDeletion A B) :
    IsExactTupleAsymptoticBasis (A \ B) 3 :=
  exactThreeBasis_of_splittableIndependentDeletion
    h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- Existence form used as the new bridge for Erdős 881 at order two. -/
theorem exists_infiniteDeletion_threeBasis_of_exists_splittableIndependent
    {A : Set ℕ}
    (h : ∃ B, IsSplittableIndependentDeletion A B) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.1, hB.2.1, hB.exactThreeBasis⟩

/-! ## Reduction to splitting only along `A` -/

/-- A cleaner selection package.  The complement need only remain an exact
order-two basis along targets which themselves belong to `A`; these are
precisely the targets which may later need to be split as summands. -/
def IsPairIndependentDeletionWithSelfBasis
    (A B : Set ℕ) : Prop :=
  B ⊆ A ∧ B.Infinite ∧
    IsEventuallyPairIndependentDeletion A B ∧
    IsExactTupleAsymptoticBasisAlong (A \ B) 2 A

/-! ## Support-coloring formulation -/

/-- Eventually every target has an additive support containing at least one
blue (retained) point.  In the red/blue language this excludes an all-red
support obstruction. -/
def HasEventuallySupportNotContained
    (R : SupportFamily) (B : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    ∃ E ∈ R n, ¬ (E : Set ℕ) ⊆ B

/-- For order two, pair independence is exactly the existence of an
eventual representation support which is not entirely red. -/
theorem pairIndependent_iff_supportNotContained
    {A B : Set ℕ} :
    IsEventuallyPairIndependentDeletion A B ↔
      HasEventuallySupportNotContained
        (additiveSupportFamily A 2) B := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨x, y, hxA, hyA, hxy, hnotBoth⟩ := hN n hn
    have hxn : x ≤ n := by omega
    have hcomp : n - x = y := by omega
    refine ⟨pairSupport n x,
      pairSupport_mem_additiveSupportFamily hxn hxA (hcomp ▸ hyA), ?_⟩
    intro hsub
    apply hnotBoth
    constructor
    · exact hsub (by simp [pairSupport])
    · apply hsub
      simp [pairSupport, hcomp]
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨E, hER, hnotSub⟩ := hN n hn
    obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    refine ⟨(v 0).1, (v 1).1, hvA 0, hvA 1, ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hvsum
    · rintro ⟨h0, h1⟩
      apply hnotSub
      intro z hz
      obtain ⟨i, rfl⟩ := mem_tupleSupport_iff.mp hz
      fin_cases i
      · exact h0
      · exact h1

/-- The exact finite-support certificate left by the bridge theorem: choose
infinitely many red points in `A`; every late integer has a support with a
blue point, and every late target lying in `A` has an all-blue support. -/
def IsRedBluePairSupportSelection (A B : Set ℕ) : Prop :=
  B ⊆ A ∧ B.Infinite ∧
    HasEventuallySupportNotContained
      (additiveSupportFamily A 2) B ∧
    HasEventuallySurvivingSupportAlong
      (additiveSupportFamily A 2) B A

/-- The support-coloring certificate is equivalent to the cleaner analytic
selection package. -/
theorem redBluePairSupportSelection_iff
    {A B : Set ℕ} :
    IsRedBluePairSupportSelection A B ↔
      IsPairIndependentDeletionWithSelfBasis A B := by
  rw [IsRedBluePairSupportSelection,
    IsPairIndependentDeletionWithSelfBasis,
    ← pairIndependent_iff_supportNotContained,
    hasEventuallySurvivingSupportAlong_additive_iff]

/-! ## The external-sum graph route -/

/-- Apart from a bounded initial range, every sum of two red points is itself
a target in `A`.  Equivalently, the tail of `B` is independent in the graph
on `A` whose edges are pairs with sum outside `A` (including diagonal
obstructions). -/
def IsEventuallySumClosedIn (A B : Set ℕ) : Prop :=
  ∃ K, ∀ x ∈ B, ∀ y ∈ B, K ≤ x + y → x + y ∈ A

/-- If red-red sums land back in `A`, the all-blue representations available
along `A` repair every red-red pair. -/
theorem pairIndependent_of_basis_selfBasis_sumClosed
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A)
    (hsum : IsEventuallySumClosedIn A B) :
    IsEventuallyPairIndependentDeletion A B := by
  obtain ⟨N, hN⟩ := hbasis
  obtain ⟨L, hL⟩ := hself
  obtain ⟨K, hK⟩ := hsum
  refine ⟨max N (max L K), ?_⟩
  intro n hn
  have hnN : N ≤ n :=
    le_trans (le_max_left N (max L K)) hn
  have hnL : L ≤ n :=
    le_trans (le_trans (le_max_left L K)
      (le_max_right N (max L K))) hn
  have hnK : K ≤ n :=
    le_trans (le_trans (le_max_right L K)
      (le_max_right N (max L K))) hn
  obtain ⟨v, hvA, hvsum⟩ := hN n hnN
  have hsumTwo : v 0 + v 1 = n := by
    simpa [Fin.sum_univ_two] using hvsum
  by_cases hboth : v 0 ∈ B ∧ v 1 ∈ B
  · have hnA : n ∈ A := by
      rw [← hsumTwo]
      exact hK (v 0) hboth.1 (v 1) hboth.2 (hsumTwo ▸ hnK)
    obtain ⟨w, hwC, hwsum⟩ := hL n hnL hnA
    refine ⟨w 0, w 1, (hwC 0).1, (hwC 1).1, ?_, ?_⟩
    · simpa [Fin.sum_univ_two] using hwsum
    · rintro ⟨hw0B, _hw1B⟩
      exact (hwC 0).2 hw0B
  · exact ⟨v 0, v 1, hvA 0, hvA 1, hsumTwo, hboth⟩

/-- An infinite deletion which is eventually sum-closed in `A` and whose
complement remains an order-two basis along `A` satisfies the red/blue
support certificate. -/
theorem redBluePairSupportSelection_of_sumClosed_selfBasis
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hBA : B ⊆ A)
    (hB : B.Infinite)
    (hsum : IsEventuallySumClosedIn A B)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A) :
    IsRedBluePairSupportSelection A B := by
  apply redBluePairSupportSelection_iff.mpr
  exact ⟨hBA, hB,
    pairIndependent_of_basis_selfBasis_sumClosed hbasis hself hsum,
    hself⟩

/-! ## Reserved alternative supports -/

/-- Every red-red pair has an alternative support containing a blue point.
This is the invariant maintained by a recursive construction which permanently
reserves one witness vertex for every newly created pair sum. -/
def HasReservedAlternativePairSupports
    (A B P : Set ℕ) : Prop :=
  Disjoint B P ∧
    ∀ x ∈ B, ∀ y ∈ B,
      ∃ E ∈ additiveSupportFamily A 2 (x + y),
        ¬ Disjoint (E : Set ℕ) P

/-- A reserved blue witness in each red-red pair sum gives the exact pair
independence needed by the bridge. -/
theorem pairIndependent_of_basis_reservedPairSupports
    {A B P : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hrepair : HasReservedAlternativePairSupports A B P) :
    IsEventuallyPairIndependentDeletion A B := by
  apply pairIndependent_iff_supportNotContained.mpr
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨E, hER, _hEempty⟩ := hN n hn
  by_cases hEsub : (E : Set ℕ) ⊆ B
  · obtain ⟨v, _hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have hv0E : (v 0).1 ∈ tupleSupport v :=
      mem_tupleSupport_iff.mpr ⟨0, rfl⟩
    have hv1E : (v 1).1 ∈ tupleSupport v :=
      mem_tupleSupport_iff.mpr ⟨1, rfl⟩
    have hv0B : (v 0).1 ∈ B := hEsub hv0E
    have hv1B : (v 1).1 ∈ B := hEsub hv1E
    have hvsumTwo : (v 0).1 + (v 1).1 = n := by
      simpa [Fin.sum_univ_two] using hvsum
    obtain ⟨G, hGR, hGP⟩ :=
      hrepair.2 (v 0).1 hv0B (v 1).1 hv1B
    rw [hvsumTwo] at hGR
    refine ⟨G, hGR, ?_⟩
    intro hGsub
    obtain ⟨z, hzG, hzP⟩ := Set.not_disjoint_iff.mp hGP
    exact Set.disjoint_left.mp hrepair.1 (hGsub hzG) hzP
  · exact ⟨E, hER, hEsub⟩

/-- Shrinking the deletion only enlarges its complement, so an order-two
basis along `A` survives every thinning. -/
theorem exactTwoBasisAlong_self_of_deletion_subset
    {A B B₀ : Set ℕ}
    (hBB₀ : B ⊆ B₀)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A) :
    IsExactTupleAsymptoticBasisAlong (A \ B) 2 A := by
  obtain ⟨N, hN⟩ := hself
  refine ⟨N, ?_⟩
  intro n hn hnA
  obtain ⟨v, hvC, hvsum⟩ := hN n hn hnA
  refine ⟨v, ?_, hvsum⟩
  intro i
  exact ⟨(hvC i).1, fun hviB => (hvC i).2 (hBB₀ hviB)⟩

/-- The constructive form of the new path: first find a self-basis deletion
reservoir `B₀`, then thin it while reserving one blue repair vertex for every
red-red pair. -/
theorem redBluePairSupportSelection_of_reserved_thinning
    {A B B₀ P : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hBB₀ : B ⊆ B₀)
    (hB : B.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hrepair : HasReservedAlternativePairSupports A B P) :
    IsRedBluePairSupportSelection A B := by
  apply redBluePairSupportSelection_iff.mpr
  have hself' := exactTwoBasisAlong_self_of_deletion_subset hBB₀ hself
  exact ⟨fun x hx => hB₀A (hBB₀ hx), hB,
    pairIndependent_of_basis_reservedPairSupports hbasis hrepair,
    hself'⟩

/-! ## What strong deletion and its finite certificate force -/

/-- A finite strong-deletion certificate, tested against a selector which
has blue supports at its internal targets and no all-red certified support,
must select an external target carrying a crossing support. -/
theorem finiteCertificate_forces_externalCrossing
    {R : SupportFamily} {A : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} (s : BlockSelector F)
    (hcert : ∀ t : BlockSelector F,
      ∃ q ∈ Q, DestroysAt R (selectedSet t) q)
    (hsurviveA : ∀ q ∈ Q, q ∈ A →
      ∃ E ∈ R q, Disjoint (E : Set ℕ) (selectedSet s))
    (hnotRed : ∀ q ∈ Q,
      ∃ E ∈ R q, ¬ (E : Set ℕ) ⊆ selectedSet s) :
    ∃ q ∈ Q, q ∉ A ∧
      DestroysAt R (selectedSet s) q ∧
      ∃ E ∈ R q,
        ¬ Disjoint (E : Set ℕ) (selectedSet s) ∧
        ¬ (E : Set ℕ) ⊆ selectedSet s := by
  obtain ⟨q, hqQ, hdestroy⟩ := hcert s
  have hqA : q ∉ A := by
    intro hqA
    obtain ⟨E, hER, hEblue⟩ := hsurviveA q hqQ hqA
    exact (hdestroy E hER) hEblue
  obtain ⟨E, hER, hEnotRed⟩ := hnotRed q hqQ
  exact ⟨q, hqQ, hqA, hdestroy, E, hER,
    hdestroy E hER, hEnotRed⟩

/-- Global version of the certificate conclusion.  Under strong order-two
deletion, a red/blue selection has arbitrarily late external targets at which
some representation pair crosses from the deletion to its complement. -/
theorem IsRedBluePairSupportSelection.exists_late_externalCrossing
    {A B : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 2) A)
    (h : IsRedBluePairSupportSelection A B) :
    ∀ M, ∃ n, M ≤ n ∧ n ∉ A ∧
      ∃ E ∈ additiveSupportFamily A 2 n,
        ¬ Disjoint (E : Set ℕ) B ∧
        ¬ (E : Set ℕ) ⊆ B := by
  obtain ⟨N, hnotRed⟩ := h.2.2.1
  obtain ⟨L, hsurviveA⟩ := h.2.2.2
  intro M
  obtain ⟨n, hn, hdestroy⟩ :=
    hstrong B h.1 h.2.1 (max M (max N L))
  have hnM : M ≤ n :=
    le_trans (le_max_left M (max N L)) hn
  have hnN : N ≤ n :=
    le_trans (le_trans (le_max_left N L)
      (le_max_right M (max N L))) hn
  have hnL : L ≤ n :=
    le_trans (le_trans (le_max_right N L)
      (le_max_right M (max N L))) hn
  have hnA : n ∉ A := by
    intro hnA
    obtain ⟨E, hER, hEblue⟩ := hsurviveA n hnL hnA
    exact (hdestroy E hER) hEblue
  obtain ⟨E, hER, hEnotRed⟩ := hnotRed n hnN
  exact ⟨n, hnM, hnA, E, hER, hdestroy E hER, hEnotRed⟩

/-! ## Exact obstruction to extending the reservation recursion -/

def HasFreshPairRepairExtension
    (A C : Set ℕ) (D P : Finset ℕ) (T : ℕ) : Prop :=
  ∃ b, b ∈ C ∧ b ∉ D ∧ b ∉ P ∧ T ≤ b ∧
    ∀ d ∈ insert b D,
      ∃ E ∈ additiveSupportFamily A 2 (b + d),
        ¬ E ⊆ insert b D

/-- Logical normal form of a failed reservation step: every eligible fresh
candidate has one pair sum all of whose representation vertices are trapped
inside the old prefix together with that candidate. -/
theorem not_hasFreshPairRepairExtension_iff
    {A C : Set ℕ} {D P : Finset ℕ} {T : ℕ} :
    ¬ HasFreshPairRepairExtension A C D P T ↔
      ∀ b, b ∈ C → b ∉ D → b ∉ P → T ≤ b →
        ∃ d ∈ insert b D,
          ∀ E ∈ additiveSupportFamily A 2 (b + d),
            E ⊆ insert b D := by
  classical
  simp only [HasFreshPairRepairExtension]
  push Not
  rfl

/-- Name for the finite rigid-star obstruction exposed by a failed step. -/
def HasFiniteRigidStarObstruction
    (A C : Set ℕ) (D P : Finset ℕ) (T : ℕ) : Prop :=
  ∀ b, b ∈ C → b ∉ D → b ∉ P → T ≤ b →
    ∃ d ∈ insert b D,
      ∀ E ∈ additiveSupportFamily A 2 (b + d),
        E ⊆ insert b D

theorem not_hasFreshPairRepairExtension_iff_rigidStar
    {A C : Set ℕ} {D P : Finset ℕ} {T : ℕ} :
    ¬ HasFreshPairRepairExtension A C D P T ↔
      HasFiniteRigidStarObstruction A C D P T :=
  not_hasFreshPairRepairExtension_iff

/-- The pair sum `b + d` is rigid if every ambient order-two support is the
canonical complementary pair `{b,d}`. -/
def IsRigidPairSum (A : Set ℕ) (b d : ℕ) : Prop :=
  ∀ E ∈ additiveSupportFamily A 2 (b + d),
    E = pairSupport (b + d) b

/-- Once `b` is larger than twice the sum of the finite old prefix, a support
for `b+d` trapped in `D ∪ {b}` must contain `b`; hence it is exactly the
canonical pair support. -/
theorem rigidPairSum_of_supports_subset_insert
    {A : Set ℕ} {D : Finset ℕ} {b d : ℕ}
    (hlarge : 2 * D.sum id < b)
    (htrap : ∀ E ∈ additiveSupportFamily A 2 (b + d),
      E ⊆ insert b D) :
    IsRigidPairSum A b d := by
  intro E hER
  apply additiveSupportFamily_two_eq_pairSupport_of_mem hER
  by_contra hbE
  obtain ⟨v, _hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have hvD : ∀ i, (v i).1 ∈ D := by
    intro i
    have hviE : (v i).1 ∈ tupleSupport v :=
      mem_tupleSupport_iff.mpr ⟨i, rfl⟩
    obtain hviEq | hviD := Finset.mem_insert.mp (htrap _ hER hviE)
    · rw [hviEq] at hviE
      exact (hbE hviE).elim
    · exact hviD
  have hv0le : (v 0).1 ≤ D.sum id :=
    Finset.single_le_sum (s := D) (f := id)
      (fun _ _ => Nat.zero_le _) (hvD 0)
  have hv1le : (v 1).1 ≤ D.sum id :=
    Finset.single_le_sum (s := D) (f := id)
      (fun _ _ => Nat.zero_le _) (hvD 1)
  have hsumTwo : (v 0).1 + (v 1).1 = b + d := by
    simpa [Fin.sum_univ_two] using hvsum
  omega

theorem HasFiniteRigidStarObstruction.eventually_rigidPair
    {A C : Set ℕ} {D P : Finset ℕ} {T : ℕ}
    (h : HasFiniteRigidStarObstruction A C D P T) :
    ∀ b, b ∈ C → b ∉ D → b ∉ P →
      max T (2 * D.sum id + 1) ≤ b →
      ∃ d ∈ insert b D, IsRigidPairSum A b d := by
  intro b hbC hbD hbP hbLarge
  have hbT : T ≤ b := le_trans (le_max_left _ _) hbLarge
  have hsumLarge : 2 * D.sum id < b := by
    have : 2 * D.sum id + 1 ≤ b :=
      le_trans (le_max_right _ _) hbLarge
    omega
  obtain ⟨d, hd, htrap⟩ := h b hbC hbD hbP hbT
  exact ⟨d, hd,
    rigidPairSum_of_supports_subset_insert hsumLarge htrap⟩

/-- Pigeonholing the finitely many old anchors gives the final failure
dichotomy.  On an infinite candidate reservoir, a failed step produces
either infinitely many rigid doubles or an infinite rigid star around one
fixed member of the old prefix. -/
theorem HasFiniteRigidStarObstruction.infinite_diagonal_or_star
    {A C : Set ℕ} {D P : Finset ℕ} {T : ℕ}
    (h : HasFiniteRigidStarObstruction A C D P T)
    (hC : C.Infinite) :
    {b | b ∈ C ∧ IsRigidPairSum A b b}.Infinite ∨
      ∃ d ∈ D, {b | b ∈ C ∧ IsRigidPairSum A b d}.Infinite := by
  classical
  let K := max T (2 * D.sum id + 1)
  let X : Set ℕ := C \ ((D : Set ℕ) ∪ (P : Set ℕ) ∪ Set.Iio K)
  have hfiniteExcluded :
      ((D : Set ℕ) ∪ (P : Set ℕ) ∪ Set.Iio K).Finite :=
    (D.finite_toSet.union P.finite_toSet).union (Set.finite_Iio K)
  have hX : X.Infinite := hC.diff hfiniteExcluded
  by_cases hdiag : {b | b ∈ C ∧ IsRigidPairSum A b b}.Infinite
  · exact Or.inl hdiag
  · right
    by_contra hnostar
    push Not at hnostar
    have hdiagFinite : {b | b ∈ C ∧ IsRigidPairSum A b b}.Finite :=
      by
        by_contra hnotFinite
        exact hdiag hnotFinite
    have hstarFinite : ∀ d ∈ (D : Set ℕ),
        {b | b ∈ C ∧ IsRigidPairSum A b d}.Finite := by
      intro d hdD
      exact hnostar d hdD
    have hunionFinite :
        ({b | b ∈ C ∧ IsRigidPairSum A b b} ∪
          ⋃ d ∈ (D : Set ℕ),
            {b | b ∈ C ∧ IsRigidPairSum A b d}).Finite := by
      apply hdiagFinite.union
      exact D.finite_toSet.biUnion hstarFinite
    apply hX
    apply hunionFinite.subset
    intro b hbX
    have hbC : b ∈ C := hbX.1
    have hbD : b ∉ D := by
      intro hbD
      exact hbX.2 (Or.inl (Or.inl hbD))
    have hbP : b ∉ P := by
      intro hbP
      exact hbX.2 (Or.inl (Or.inr hbP))
    have hbK : K ≤ b := Nat.le_of_not_gt fun hbLt =>
      hbX.2 (Or.inr hbLt)
    obtain ⟨d, hd, hrigid⟩ :=
      h.eventually_rigidPair b hbC hbD hbP hbK
    rcases Finset.mem_insert.mp hd with rfl | hdD
    · exact Or.inl ⟨hbC, hrigid⟩
    · apply Or.inr
      exact Set.mem_iUnion₂.mpr ⟨d, hdD, hbC, hrigid⟩

/-- From a pair-independent deletion whose complement is an order-two basis
along `A`, discard the finitely many deletion points below the along-basis
threshold.  The resulting tail deletion is splittable independent. -/
theorem IsPairIndependentDeletionWithSelfBasis.exists_tail_splittable
    {A B : Set ℕ}
    (h : IsPairIndependentDeletionWithSelfBasis A B) :
    ∃ B' ⊆ B, IsSplittableIndependentDeletion A B' := by
  obtain ⟨L, hL⟩ := h.2.2.2
  let B' : Set ℕ := B \ Set.Iio L
  have hB'B : B' ⊆ B := Set.diff_subset
  have hB'A : B' ⊆ A := fun _ hx => h.1 hx.1
  have hB'infinite : B'.Infinite := by
    exact h.2.1.diff (Set.finite_Iio L)
  have hpair' : IsEventuallyPairIndependentDeletion A B' := by
    obtain ⟨N, hN⟩ := h.2.2.1
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨x, y, hxA, hyA, hxy, hnotBoth⟩ := hN n hn
    refine ⟨x, y, hxA, hyA, hxy, ?_⟩
    rintro ⟨hxB', hyB'⟩
    exact hnotBoth ⟨hxB'.1, hyB'.1⟩
  have promote_split
      {a : ℕ} (haA : a ∈ A) (hLa : L ≤ a) :
      SplitsIntoTwo (A \ B') a := by
    obtain ⟨v, hvC, hvsum⟩ := hL a hLa haA
    refine ⟨v 0, v 1, ?_, ?_, ?_⟩
    · exact ⟨(hvC 0).1, fun hvB' => (hvC 0).2 hvB'.1⟩
    · exact ⟨(hvC 1).1, fun hvB' => (hvC 1).2 hvB'.1⟩
    · simpa [Fin.sum_univ_two] using hvsum
  have hsplitB' : DeletionSplitsIntoComplement A B' := by
    intro b hbB'
    have hLb : L ≤ b := Nat.le_of_not_gt hbB'.2
    exact promote_split (h.1 hbB'.1) hLb
  have hsplitC' : ComplementEventuallySelfSplits A B' := by
    refine ⟨L, ?_⟩
    intro c hcC hLc
    exact promote_split hcC.1 hLc
  exact ⟨B', hB'B,
    hB'A, hB'infinite, hpair', hsplitB', hsplitC'⟩

/-- Consequently the clean selection package already gives the desired
infinite successor-order deletion. -/
theorem IsPairIndependentDeletionWithSelfBasis.exists_infiniteDeletion_threeBasis
    {A B : Set ℕ}
    (h : IsPairIndependentDeletionWithSelfBasis A B) :
    ∃ B', B' ⊆ A ∧ B'.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B') 3 := by
  obtain ⟨B', _hB'B, hB'⟩ := h.exists_tail_splittable
  exact ⟨B', hB'.1, hB'.2.1, hB'.exactThreeBasis⟩

/-- Hence the red/blue support-selection problem is a sufficient finite
certificate for an infinite deletion leaving an exact order-three basis. -/
theorem IsRedBluePairSupportSelection.exists_infiniteDeletion_threeBasis
    {A B : Set ℕ}
    (h : IsRedBluePairSupportSelection A B) :
    ∃ B', B' ⊆ A ∧ B'.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B') 3 :=
  IsPairIndependentDeletionWithSelfBasis.exists_infiniteDeletion_threeBasis
    (redBluePairSupportSelection_iff.mp h)

end Erdos881
