import Erdos881.AdaptiveDirect
import Erdos881.InfiniteSunflower

namespace Erdos881

open Classical

/-- Data for the private alternative of `HasMarkedPointCofinalRankFork`, with
an explicit lower bound on the marked element. -/
structure MarkedPrivateCoreStage
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ) (L : ℕ) where
  marker : ℕ
  apex : ℕ
  target : ℕ
  upperTarget : ℕ
  core : Finset ℕ
  destroyer : Finset ℕ
  marker_mem : marker ∈ A
  apex_mem : apex ∈ A
  marker_large : L ≤ marker
  marker_le_target : marker ≤ target
  upper_eq : upperTarget = apex + target
  core_mem :
    core ∈ additiveSupportFamily A (k - 1) (target - marker)
  marker_not_core : marker ∉ core
  destroyer_nonempty : destroyer.Nonempty
  marker_mem_destroyer : marker ∈ destroyer
  destroyer_subset : destroyer ⊆ insert marker F
  destroyer_diff : destroyer \ F = {marker}
  destroyer_minimal :
    IsInclusionMinimalDestroyer
      (additiveSupportFamily A k) destroyer target
  core_destroyer_disjoint :
    Disjoint (core : Set ℕ) (destroyer : Set ℕ)
  lower_support_mem :
    insert marker core ∈ additiveSupportFamily A k target
  lower_support_private :
    insert marker core ∩ destroyer = {marker}
  upper_support_mem :
    insert apex (insert marker core) ∈
      additiveSupportFamily A (k + 1) upperTarget

/-- A private marked-core stage exists above every lower bound. -/
def HasCofinalMarkedPrivateCoreSupply
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ) : Prop :=
  ∀ L, Nonempty (MarkedPrivateCoreStage A k F L)

/-- The non-private alternative is either a diagonal equality or a strict
lower-rank descent. -/
def HasNonPrivateMarkedConeRankExit
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ)
    (b n L : ℕ) : Prop :=
  ∃ x D,
    x ∈ A ∧ x ∉ insert b F ∧
    x ≤ n ∧
    L ≤ n - x ∧
    D.Nonempty ∧ D ⊆ insert b F ∧
    b ∈ D ∧ D \ F = {b} ∧
    IsInclusionMinimalDestroyer
      (additiveSupportFamily A k) D (n - x) ∧
    ((n - x = k * b) ∨
      HasPrefixClearedCofinalNontrivialRankDescent
        A k F D L)

/-- Every outcome of the cofinal marked-cone theorem except the marked
point's private predecessor core. -/
def HasMarkedConeOuterExitAt
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ) (L : ℕ) : Prop :=
  ∃ b n,
    b ∈ A ∧ b ∉ F ∧ L ≤ b ∧ b ≤ n ∧
    PinnedAt A (k + 1) F b n ∧
    (n = (k + 1) * b ∨
      HasOldPrefixCone A k F b n ∨
      HasNonPrivateMarkedConeRankExit A k F b n L)

theorem HasCofinalMarkedConeRankFork.nonPrivateExit_or_privateCoreStage
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    {b n L : ℕ}
    (hbA : b ∈ A)
    (hLb : L ≤ b)
    (hcone : HasCofinalMarkedConeRankFork A k F b n L) :
    HasNonPrivateMarkedConeRankExit A k F b n L ∨
      Nonempty (MarkedPrivateCoreStage A k F L) := by
  classical
  obtain ⟨x, D, hxA, hxSupportTransversal, hxle, hLtarget,
      hDnonempty, hDSupportTransversal, hbD, hDdiff,
      hDminimal, hfork⟩ := hcone
  rcases hfork with hdiag | hrest
  · exact Or.inl ⟨x, D, hxA, hxSupportTransversal, hxle, hLtarget,
      hDnonempty, hDSupportTransversal, hbD, hDdiff,
      hDminimal, Or.inl hdiag⟩
  rcases hrest with hrank | hprivate
  · exact Or.inl ⟨x, D, hxA, hxSupportTransversal, hxle, hLtarget,
      hDnonempty, hDSupportTransversal, hbD, hDdiff,
      hDminimal, Or.inr hrank⟩
  · right
    obtain ⟨core, hcoreMem, hcoreD,
        hsupportMem, _hprivate⟩ := hprivate
    have hbTarget : b ≤ n - x :=
      additiveSupportFamily_supportsBounded
        A k (n - x) (insert b core) hsupportMem b
          (Finset.mem_insert_self b core)
    have hbCore : b ∉ core := by
      intro hbCore
      exact Set.disjoint_left.mp hcoreD
        (Finset.mem_coe.mpr hbCore)
        (Finset.mem_coe.mpr hbD)
    have hupperEq : n = x + (n - x) := by omega
    have hupperSupport :
        insert x (insert b core) ∈
          additiveSupportFamily A (k + 1) n := by
      rw [hupperEq]
      exact insert_mem_additiveSupportFamily_succ hxA hsupportMem
    exact ⟨{
      marker := b
      apex := x
      target := n - x
      upperTarget := n
      core := core
      destroyer := D
      marker_mem := hbA
      apex_mem := hxA
      marker_large := hLb
      marker_le_target := hbTarget
      upper_eq := hupperEq
      core_mem := hcoreMem
      marker_not_core := hbCore
      destroyer_nonempty := hDnonempty
      marker_mem_destroyer := hbD
      destroyer_subset := hDSupportTransversal
      destroyer_diff := hDdiff
      destroyer_minimal := hDminimal
      core_destroyer_disjoint := hcoreD
      lower_support_mem := hsupportMem
      lower_support_private := _hprivate
      upper_support_mem := hupperSupport
    }⟩

/-- One genuine infinite deletion carrying cofinally many reconstructed
successor-order supports at the original pinned targets.  This is a local
stream-survival endpoint, not yet the claim that `A \ X` is an exact
asymptotic basis. -/
def HasCofinalMarkedSupportSurvivalDeletion
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ X J : Set ℕ,
  ∃ marker target : ℕ → ℕ,
  ∃ support : ℕ → Finset ℕ,
  ∃ cell : ℕ → Finset ℕ,
    X ⊆ A ∧
    X.Infinite ∧
    IsFiniteBlockPartition X cell ∧
    (∀ i, (cell i).card ≤ k - 1) ∧
    J.Infinite ∧
    Set.InjOn marker J ∧
    (∀ i ∈ J,
      i ≤ marker i ∧
      marker i ∈ A ∧
      marker i ∈ support i ∧
      support i ∈ additiveSupportFamily A (k + 1) (target i) ∧
      Disjoint (support i : Set ℕ) X) ∧
    ∀ L, ∃ i ∈ J, L ≤ target i

/-- The local deletion endpoint contains exactly the strict successor
survival stream required by the existing counterexample machinery.  The
cofinal target image is infinite, so it can be enumerated increasingly;
one stored clean support is then pulled back along each enumerated target. -/
theorem HasCofinalMarkedSupportSurvivalDeletion.exists_strictSurvivalStream
    {A : Set ℕ} {k : ℕ}
    (hdel : HasCofinalMarkedSupportSurvivalDeletion A k) :
    ∃ X : Set ℕ,
    ∃ cell : ℕ → Finset ℕ,
      X ⊆ A ∧ X.Infinite ∧
      IsFiniteBlockPartition X cell ∧
      (∀ i, (cell i).card ≤ k - 1) ∧
      ∃ target : ℕ → ℕ,
        StrictMono target ∧
        ∀ n, ∃ E ∈
          additiveSupportFamily A (k + 1) (target n),
          Disjoint (E : Set ℕ) X := by
  classical
  obtain ⟨X, J, marker, oldTarget, support, cell,
      hXA, hXInfinite, hpartition, hcellCard,
      _hJInfinite, _hmarkerInj,
      hstage, hcofinal⟩ := hdel
  have htargetImageInfinite :
      (oldTarget '' J).Infinite := by
    intro hfinite
    obtain ⟨U, hU⟩ := hfinite.bddAbove
    obtain ⟨i, hiJ, hUi⟩ := hcofinal (U + 1)
    have hiUpper : oldTarget i ≤ U :=
      hU ⟨i, hiJ, rfl⟩
    omega
  obtain ⟨target, htargetStrict, htargetImage⟩ :=
    infiniteNatSet_extract_strictStream htargetImageInfinite
  refine ⟨X, cell, hXA, hXInfinite,
    hpartition, hcellCard, target,
    htargetStrict, ?_⟩
  intro n
  obtain ⟨i, hiJ, hiTarget⟩ := htargetImage n
  exact ⟨support i, hiTarget ▸ (hstage i hiJ).2.2.2.1,
    (hstage i hiJ).2.2.2.2⟩

/-- Under the counterexample hypothesis, a cofinal marked-support survival
deletion forces strict rank descent. The resulting rank may equal `1`. -/
theorem HasCofinalMarkedSupportSurvivalDeletion.forces_strictRankDescent
    {A : Set ℕ} {k : ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hdel : HasCofinalMarkedSupportSurvivalDeletion A k) :
    ∃ X : Set ℕ,
      X ⊆ A ∧ X.Infinite ∧
      ∃ q, ∃ D : Finset ℕ, ∃ ℓ n,
        D.Nonempty ∧
        (D : Set ℕ) ⊆ X ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A k) D q ∧
        0 < ℓ ∧ ℓ < k ∧
        (additiveSupportFamily A ℓ n).Nonempty ∧
        DestroysAt
          (additiveSupportFamily A ℓ)
          (D : Set ℕ) n := by
  classical
  obtain ⟨X, _cell, hXA, hXInfinite,
      _hpartition, _hcellCard, target,
      htargetStrict, hsurvival⟩ :=
    hdel.exists_strictSurvivalStream
  have hdescent :=
    counterexample_with_strictSuccessorSurvivalStream_forces_strictRankDescent
      hk hbasis hcounter hXA hXInfinite htargetStrict hsurvival
  exact ⟨X, hXA, hXInfinite, hdescent⟩

def HasBracketedPrivatePetalCounterexampleConflict
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ X : Set ℕ, ∃ cell : ℕ → Finset ℕ,
  ∃ oldTarget : ℕ → ℕ,
    X ⊆ A ∧
    X.Infinite ∧
    IsFiniteBlockPartition X cell ∧
    (∀ i, (cell i).card ≤ k - 1) ∧
    StrictMono oldTarget ∧
    (∀ n,
      ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
        Disjoint (E : Set ℕ) X) ∧
    (∀ N, ∃ m, N ≤ m ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) X m) ∧
    ∀ L, ∃ n m, ∃ E : Finset ℕ, ∃ a,
      L ≤ n ∧
      oldTarget n < m ∧
      m < oldTarget (n + 1) ∧
      E ∈ additiveSupportFamily A (k + 1) (oldTarget n) ∧
      Disjoint (E : Set ℕ) X ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) X m ∧
      a ∈ E ∧
      (k + 1) * a ≤ oldTarget n ∧
      L ≤ m - a ∧
      (additiveSupportFamily A k (m - a)).Nonempty ∧
      DestroysAt
        (additiveSupportFamily A k) X (m - a)

/-- A hypothetical strong successor counterexample turns the moving-petal
deletion into the preceding opposing-stream conflict.  Exactness at order
`k` makes the bracketed predecessor failures represented, so they are
genuine destructions rather than empty-family artifacts. -/
theorem HasCofinalMarkedSupportSurvivalDeletion.forces_bracketedConflict
    {A : Set ℕ} {k : ℕ}
    (hkpos : 0 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hdel : HasCofinalMarkedSupportSurvivalDeletion A k) :
    HasBracketedPrivatePetalCounterexampleConflict A k := by
  obtain ⟨X, cell, hXA, hXInfinite,
      hpartition, hcellCard, oldTarget,
      holdStrict, holdSurvival⟩ :=
    hdel.exists_strictSurvivalStream
  have hsuccessorDestroy : ∀ N, ∃ m, N ≤ m ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) X m :=
    strongExactDeletion_of_counterexample hcounter
      X hXA hXInfinite
  have hbracket :=
    bracketedDestroyedSuccessorTargets_force_cofinalRepresentedPredecessorDestroyers
      hkpos hbasis holdStrict holdSurvival hsuccessorDestroy
  exact ⟨X, cell, oldTarget, hXA, hXInfinite,
    hpartition, hcellCard, holdStrict, holdSurvival,
    hsuccessorDestroy, hbracket⟩

theorem HasBracketedPrivatePetalCounterexampleConflict.selectorFusion_forces_rankDescent_or_manyBlocks
    {A : Set ℕ} {k : ℕ}
    (hk : 1 < k)
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hcollision :
      HasBracketedPrivatePetalCounterexampleConflict A k) :
    ∃ X : Set ℕ, ∃ cell : ℕ → Finset ℕ,
    ∃ oldTarget : ℕ → ℕ,
      X ⊆ A ∧
      X.Infinite ∧
      IsFiniteBlockPartition X cell ∧
      StrictMono oldTarget ∧
      (∀ j, k < (cell j).card) ∧
      (∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s)) ∧
      ((∃ s : BlockSelector cell, ∃ q, ∃ D : Finset ℕ,
          ∃ ℓ n,
            D.Nonempty ∧
            (D : Set ℕ) ⊆ selectedSet s ∧
            IsInclusionMinimalDestroyer
              (additiveSupportFamily A k) D q ∧
            0 < ℓ ∧ ℓ < k ∧
            (additiveSupportFamily A ℓ n).Nonempty ∧
            DestroysAt
              (additiveSupportFamily A ℓ)
              (D : Set ℕ) n) ∨
        ∀ r, ∃ s : BlockSelector cell, ∃ q,
          ∃ D : Finset ℕ,
            D.Nonempty ∧
            (D : Set ℕ) ⊆ selectedSet s ∧
            IsInclusionMinimalDestroyer
              (additiveSupportFamily A k) D q ∧
            r < D.card) := by
  classical
  obtain ⟨X, rawCell, oldTarget, hXA, hXInfinite,
      hrawPartition, _hrawSmall, holdStrict,
      holdSurvival, _hsuccessorDestroy, _hbracket⟩ :=
    hcollision
  obtain ⟨cell, P, _hservice, hcellCard⟩ :=
    hrawPartition.exists_coarsening_preserving_evenBlocks_with_cardLower
      (fun _ => k + 1) (fun _ => Nat.zero_lt_succ k)
  have hblocks : ∀ j, k < (cell j).card := by
    intro j
    exact lt_of_lt_of_le (by omega) (hcellCard j)
  have hselectorSurvival :
      ∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s) := by
    intro s n
    obtain ⟨E, hER, hEX⟩ := holdSurvival n
    exact ⟨E, hER,
      Set.disjoint_of_subset_right (P.selectedSet_subset s) hEX⟩
  refine ⟨X, cell, oldTarget, hXA, hXInfinite, P,
    holdStrict, hblocks, hselectorSurvival, ?_⟩
  obtain hrank | hmany | hfusion :=
    hminimal.selectorRankDescent_or_manyBlocks_or_infiniteGapFusion
      (by omega) hXA P hblocks oldTarget hselectorSurvival
  · exact Or.inl hrank
  · exact Or.inr hmany
  · obtain ⟨Y, fusion, _stageSelector, _target, _anchor,
        _destroyer, _bound, hYfusion, hYX, hYInfinite,
        _htargetStrict, hterminal, _hstageData,
        _hnoRankDescent, _hdestroyY, _hcross,
        holdSurvivalY, _holdNotDestroyed⟩ := hfusion
    have hYA : Y ⊆ A := hYX.trans hXA
    have hcleanInfinite : (A \ Y).Infinite :=
      strictSurvivingAdditiveTargetStream_forces_cleanComplementInfinite
        holdStrict holdSurvivalY
    have hsuccessorDestroy :
        ∀ N, ∃ m, N ≤ m ∧
          DestroysAt
            (additiveSupportFamily A (k + 1)) Y m :=
      strongExactDeletion_of_counterexample hcounter
        Y hYA hYInfinite
    exact
      (terminalFusion_cofinalSuccessorDestruction_impossible
        hk hminimal.1 fusion hYfusion hterminal
          hcleanInfinite hsuccessorDestroy).elim

theorem HasBracketedPrivatePetalCounterexampleConflict.selectorNontrivialRankDescent_or_boundedProtectedRepair
    {A : Set ℕ} {k : ℕ}
    (hk : 1 < k)
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hcollision :
      HasBracketedPrivatePetalCounterexampleConflict A k) :
    ∀ C, ∃ X : Set ℕ, ∃ cell : ℕ → Finset ℕ,
    ∃ oldTarget : ℕ → ℕ,
      X ⊆ A ∧
      X.Infinite ∧
      IsFiniteBlockPartition X cell ∧
      StrictMono oldTarget ∧
      (∀ j, C + k < (cell j).card) ∧
      (∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s)) ∧
      ∀ s : BlockSelector cell, ∀ U : Finset ℕ,
        U.card ≤ C →
        Disjoint (U : Set ℕ) (selectedSet s) →
        ∀ L, ∃ q, ∃ D : Finset ℕ,
          L ≤ q ∧
          D.Nonempty ∧
          (D : Set ℕ) ⊆ selectedSet s ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A k) D q ∧
          ((∃ ℓ n,
              1 < ℓ ∧ ℓ < k ∧
              (additiveSupportFamily A ℓ n).Nonempty ∧
              DestroysAt
                (additiveSupportFamily A ℓ)
                (D : Set ℕ) n) ∨
            ∃ t : BlockSelector cell,
              Disjoint (U : Set ℕ) (selectedSet t) ∧
              ¬ DestroysAt
                (additiveSupportFamily A k)
                (selectedSet t) q) := by
  classical
  intro C
  obtain ⟨X, rawCell, oldTarget, hXA, hXInfinite,
      hrawPartition, _hrawSmall, holdStrict,
      holdSurvival, _hsuccessorDestroy, _hbracket⟩ :=
    hcollision
  obtain ⟨cell, P, _hservice, hcellCard⟩ :=
    hrawPartition.exists_coarsening_preserving_evenBlocks_with_cardLower
      (fun _ => C + k + 1) (fun _ => Nat.zero_lt_succ (C + k))
  have hlarge : ∀ j, C + k < (cell j).card := by
    intro j
    exact lt_of_lt_of_le (by omega) (hcellCard j)
  have hselectorSurvival :
      ∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s) := by
    intro s n
    obtain ⟨E, hER, hEX⟩ := holdSurvival n
    exact ⟨E, hER,
      Set.disjoint_of_subset_right (P.selectedSet_subset s) hEX⟩
  refine ⟨X, cell, oldTarget, hXA, hXInfinite, P,
    holdStrict, hlarge, hselectorSurvival, ?_⟩
  intro s U hUcard hUselected L
  have hblocks : ∀ j, U.card + k < (cell j).card := by
    intro j
    exact lt_of_le_of_lt
      (Nat.add_le_add_right hUcard k) (hlarge j)
  exact
    hminimal.cofinal_selectorNontrivialRankDescent_or_protectedRepair
      hk hXA P s U hUselected hblocks L

theorem HasBracketedPrivatePetalCounterexampleConflict.forces_unboundedLocalizedMigratingCertificates
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hcollision :
      HasBracketedPrivatePetalCounterexampleConflict A k) :
    ∃ X : Set ℕ, ∃ cell : ℕ → Finset ℕ,
    ∃ oldTarget : ℕ → ℕ,
      X ⊆ A ∧
      X.Infinite ∧
      IsFiniteBlockPartition X cell ∧
      StrictMono oldTarget ∧
      (∀ i, (i + k + 2) ^ 2 < (cell i).card) ∧
      (∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s)) ∧
      ∀ C L,
        let capacity := (k + 1) * C + (k + 1)
        let start := capacity + 1
        let tailCell : ℕ → Finset ℕ :=
          fun i => cell (start + i)
        ∃ Q : Finset ℕ,
          Q.Nonempty ∧
          (∀ q ∈ Q, ∃ i,
            start ≤ i ∧
            L ≤ i ∧
            oldTarget i < q ∧
            q < oldTarget (i + 1)) ∧
          (∀ s : BlockSelector tailCell, ∃ q ∈ Q,
            DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet s) q) ∧
          (∀ q ∈ Q, ∃ s : BlockSelector tailCell,
            DestroysAt
              (additiveSupportFamily A (k + 1))
              (selectedSet s) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt
                (additiveSupportFamily A (k + 1))
                (selectedSet s) q') ∧
          (∀ q ∈ Q,
            (additiveSupportFamily A (k + 1) q).Nonempty) ∧
          C < Q.card := by
  classical
  obtain ⟨X, rawCell, oldTarget, hXA, hXInfinite,
      hrawPartition, _hrawSmall, holdStrict,
      holdSurvival, _hsuccessorDestroy, _hbracket⟩ :=
    hcollision
  obtain ⟨cell, P, _hservice, hcellCard⟩ :=
    hrawPartition.exists_coarsening_preserving_evenBlocks_with_cardLower
      (fun i => (i + k + 2) ^ 2 + 1)
      (fun i => Nat.zero_lt_succ ((i + k + 2) ^ 2))
  have hquadratic : ∀ i, (i + k + 2) ^ 2 < (cell i).card := by
    intro i
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hcellCard i)
  have hselectorSurvival :
      ∀ s : BlockSelector cell, ∀ n,
        ∃ E ∈ additiveSupportFamily A (k + 1) (oldTarget n),
          Disjoint (E : Set ℕ) (selectedSet s) := by
    intro s n
    obtain ⟨E, hER, hEX⟩ := holdSurvival n
    exact ⟨E, hER,
      Set.disjoint_of_subset_right (P.selectedSet_subset s) hEX⟩
  refine ⟨X, cell, oldTarget, hXA, hXInfinite, P,
    holdStrict, hquadratic, hselectorSurvival, ?_⟩
  exact
    quadraticBlockTail_forces_largeBracketedTargetLocalizedCertificate
      hminimal.1.succ
      (strongExactDeletion_of_counterexample hcounter)
      hXA P hquadratic holdStrict hselectorSurvival

/-- The terminal aligned case: one nonempty lower support `R` at one fixed
residual target `t` is reinserted beside infinitely many injective moving
markers.  The corresponding inclusion-minimal destroyer is always the
moving marker adjoined to one fixed old-prefix part `P ⊆ F`, and the
translated support meets that destroyer exactly at its marker. -/
def HasFixedMarkedPrivateCoreConflict
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ) : Prop :=
  ∃ J : Set ℕ,
  ∃ marker target : ℕ → ℕ,
  ∃ destroyer : ℕ → Finset ℕ,
  ∃ P R : Finset ℕ, ∃ t : ℕ,
    J.Infinite ∧
    Set.InjOn marker J ∧
    P ⊆ F ∧
    R.Nonempty ∧
    R ∈ additiveSupportFamily A (k - 1) t ∧
    (∀ i ∈ J,
      i ≤ marker i ∧
      marker i ∈ A ∧
      marker i ∉ R ∧
      target i = marker i + t ∧
      (destroyer i).Nonempty ∧
      marker i ∈ destroyer i ∧
      destroyer i = insert (marker i) P ∧
      destroyer i ⊆ insert (marker i) F ∧
      destroyer i \ F = {marker i} ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A k) (destroyer i) (target i) ∧
      Disjoint (R : Set ℕ) (destroyer i : Set ℕ) ∧
      insert (marker i) R ∈
        additiveSupportFamily A k (target i) ∧
      insert (marker i) R ∩ destroyer i = {marker i}) ∧
    ∀ L, ∃ i ∈ J, L ≤ target i

theorem HasFixedMarkedPrivateCoreConflict.to_survivalDeletion
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hfixed : HasFixedMarkedPrivateCoreConflict A k F) :
    HasCofinalMarkedSupportSurvivalDeletion A k := by
  classical
  obtain ⟨J, marker, target, destroyer, P, R, t,
      hJ, hmarkerInj, _hPF, hRnonempty, hRmem,
      hdata, _htargetCofinal⟩ := hfixed
  have hbasic : ∀ i ∈ J,
      i ≤ marker i ∧
      marker i ∈ A ∧
      marker i ∉ R ∧
      target i = marker i + t ∧
      insert (marker i) R ∈
        additiveSupportFamily A k (target i) := by
    intro i hiJ
    obtain ⟨hiLarge, hiA, hiR, hiTarget,
        _hDnonempty, _hiD, _hDeq, _hDsub,
        _hDdiff, _hDminimal, _hRD,
        hiSupport, _hiPrivate⟩ := hdata i hiJ
    exact ⟨hiLarge, hiA, hiR, hiTarget, hiSupport⟩
  let a : ℕ := hRnonempty.choose
  have haR : a ∈ R := hRnonempty.choose_spec
  have haA : a ∈ A :=
    additiveSupportFamily_supportsIn
      A (k - 1) t R hRmem a haR
  obtain ⟨Even, Odd, hEvenJ, hOddJ,
      hEven, hOdd, hEvenOdd⟩ :=
    exists_two_disjoint_infinite_subsets_of_infinite hJ
  let X : Set ℕ := marker '' Even
  have hmarkerInjEven : Set.InjOn marker Even :=
    hmarkerInj.mono hEvenJ
  have hXInfinite : X.Infinite :=
    hEven.image hmarkerInjEven
  have hXA : X ⊆ A := by
    rintro x ⟨i, hiEven, rfl⟩
    exact (hbasic i (hEvenJ hiEven)).2.1
  let index : ℕ → ℕ := Nat.nth Even
  have hindexEven : ∀ n, index n ∈ Even := by
    intro n
    exact Nat.nth_mem_of_infinite hEven n
  have hindexStrict : StrictMono index :=
    Nat.nth_strictMono hEven
  let cell : ℕ → Finset ℕ := fun n => {marker (index n)}
  have hcellNonempty : ∀ n, (cell n).Nonempty := by
    intro n
    exact ⟨marker (index n), by simp [cell]⟩
  have hcellPairwise :
      Pairwise fun i j => Disjoint (cell i) (cell j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' : x = marker (index i) := by
      simpa only [cell, Finset.mem_singleton] using hxi
    have hxj' : x = marker (index j) := by
      simpa only [cell, Finset.mem_singleton] using hxj
    have hindexEq : index i = index j :=
      hmarkerInjEven (hindexEven i) (hindexEven j)
        (hxi'.symm.trans hxj')
    exact hij (hindexStrict.injective hindexEq)
  have hcellMem : ∀ x, x ∈ X ↔ ∃ n, x ∈ cell n := by
    intro x
    constructor
    · rintro ⟨i, hiEven, rfl⟩
      have hiRange : i ∈ Set.range index := by
        change i ∈ Set.range (Nat.nth Even)
        rw [Nat.range_nth_of_infinite hEven]
        exact hiEven
      obtain ⟨n, rfl⟩ := hiRange
      exact ⟨n, by simp [cell]⟩
    · rintro ⟨n, hxCell⟩
      have hx : x = marker (index n) := by
        simpa only [cell, Finset.mem_singleton] using hxCell
      exact hx ▸ ⟨index n, hindexEven n, rfl⟩
  have hpartition : IsFiniteBlockPartition X cell :=
    ⟨hcellNonempty, hcellPairwise, hcellMem⟩
  have hcellCard : ∀ n, (cell n).card ≤ k - 1 := by
    intro n
    simp only [cell, Finset.card_singleton]
    omega
  let upperTarget : ℕ → ℕ := fun i => a + target i
  let support : ℕ → Finset ℕ := fun i =>
    insert a (insert (marker i) R)
  have hsupportX : ∀ i ∈ Odd,
      Disjoint (support i : Set ℕ) X := by
    intro i hiOdd
    rw [Set.disjoint_left]
    rintro x hxSupport ⟨j, hjEven, rfl⟩
    have hiJ : i ∈ J := hOddJ hiOdd
    have hjJ : j ∈ J := hEvenJ hjEven
    have hmarkerJNotR : marker j ∉ R :=
      (hbasic j hjJ).2.2.1
    have hxCases :
        marker j = a ∨ marker j = marker i ∨ marker j ∈ R := by
      simpa only [support, Finset.mem_coe,
        Finset.mem_insert] using hxSupport
    rcases hxCases with hja | hji | hjR
    · exact hmarkerJNotR (hja ▸ haR)
    · have hjiIndex : j = i :=
        hmarkerInj hjJ hiJ hji
      exact Set.disjoint_left.mp hEvenOdd
        hjEven (hjiIndex ▸ hiOdd)
    · exact hmarkerJNotR hjR
  have hmarkerInjOdd : Set.InjOn marker Odd :=
    hmarkerInj.mono hOddJ
  have htargetCofinal : ∀ L,
      ∃ i ∈ Odd, L ≤ upperTarget i := by
    intro L
    obtain ⟨i, hiOdd, hLi⟩ := hOdd.exists_gt L
    have hiBasic := hbasic i (hOddJ hiOdd)
    refine ⟨i, hiOdd, ?_⟩
    dsimp only [upperTarget]
    rw [hiBasic.2.2.2.1]
    omega
  refine ⟨X, Odd, marker, upperTarget, support, cell,
    hXA, hXInfinite, hpartition, hcellCard,
    hOdd, hmarkerInjOdd, ?_, htargetCofinal⟩
  intro i hiOdd
  have hiBasic := hbasic i (hOddJ hiOdd)
  refine ⟨hiBasic.1, hiBasic.2.1, ?_, ?_,
    hsupportX i hiOdd⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · exact insert_mem_additiveSupportFamily_succ
      haA hiBasic.2.2.2.2

theorem cofinalMarkedPrivateCoreSupply_deletion_or_fixedConflict
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hsupply : HasCofinalMarkedPrivateCoreSupply A k F) :
    HasCofinalMarkedSupportSurvivalDeletion A k ∨
      HasFixedMarkedPrivateCoreConflict A k F := by
  classical
  let stage : (i : ℕ) → MarkedPrivateCoreStage A k F i :=
    fun i => Classical.choice (hsupply i)
  let marker : ℕ → ℕ := fun i => (stage i).marker
  let apex : ℕ → ℕ := fun i => (stage i).apex
  let target : ℕ → ℕ := fun i => (stage i).target
  let upperTarget : ℕ → ℕ := fun i => (stage i).upperTarget
  let core : ℕ → Finset ℕ := fun i => (stage i).core
  let destroyer : ℕ → Finset ℕ := fun i => (stage i).destroyer
  let support : ℕ → Finset ℕ := fun i =>
    insert (apex i) (insert (marker i) (core i))
  have hmarkerA : ∀ i, marker i ∈ A :=
    fun i => (stage i).marker_mem
  have hmarkerLarge : ∀ i, i ≤ marker i :=
    fun i => (stage i).marker_large
  have hmarkerTarget : ∀ i, marker i ≤ target i :=
    fun i => (stage i).marker_le_target
  have hupperEq : ∀ i, upperTarget i = apex i + target i :=
    fun i => (stage i).upper_eq
  have hmarkerUpper : ∀ i, marker i ≤ upperTarget i := by
    intro i
    rw [hupperEq i]
    exact (hmarkerTarget i).trans (Nat.le_add_left _ _)
  have hcoreMem : ∀ i,
      core i ∈ additiveSupportFamily A (k - 1)
        (target i - marker i) :=
    fun i => (stage i).core_mem
  have hmarkerCore : ∀ i, marker i ∉ core i :=
    fun i => (stage i).marker_not_core
  have hdestroyerNonempty : ∀ i, (destroyer i).Nonempty :=
    fun i => (stage i).destroyer_nonempty
  have hmarkerDestroyer : ∀ i, marker i ∈ destroyer i :=
    fun i => (stage i).marker_mem_destroyer
  have hdestroyerSubset : ∀ i,
      destroyer i ⊆ insert (marker i) F :=
    fun i => (stage i).destroyer_subset
  have hdestroyerDiff : ∀ i,
      destroyer i \ F = {marker i} :=
    fun i => (stage i).destroyer_diff
  have hdestroyerMinimal : ∀ i,
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A k) (destroyer i) (target i) :=
    fun i => (stage i).destroyer_minimal
  have hcoreDestroyer : ∀ i,
      Disjoint (core i : Set ℕ) (destroyer i : Set ℕ) :=
    fun i => (stage i).core_destroyer_disjoint
  have hlowerSupportMem : ∀ i,
      insert (marker i) (core i) ∈
        additiveSupportFamily A k (target i) :=
    fun i => (stage i).lower_support_mem
  have hlowerSupportPrivate : ∀ i,
      insert (marker i) (core i) ∩ destroyer i = {marker i} :=
    fun i => (stage i).lower_support_private
  have hsupportMem : ∀ i,
      support i ∈
        additiveSupportFamily A (k + 1) (upperTarget i) :=
    fun i => (stage i).upper_support_mem
  have hcoreCard : ∀ i, (core i).card ≤ k - 1 := by
    intro i
    exact additiveSupportFamily_cardAtMost
      A (k - 1) (target i - marker i)
        (core i) (hcoreMem i)
  have hcoreNonempty : ∀ i, (core i).Nonempty := by
    intro i
    exact additiveSupportFamily_supportsNonempty
      A (h := k - 1) (by omega)
        (target i - marker i) (core i) (hcoreMem i)
  have hsupportCard : ∀ i, (support i).card ≤ k + 1 := by
    intro i
    exact additiveSupportFamily_cardAtMost
      A (k + 1) (upperTarget i) (support i) (hsupportMem i)
  have hmarkerImageInfinite :
      (marker '' (Set.univ : Set ℕ)).Infinite := by
    intro hfinite
    obtain ⟨U, hU⟩ := hfinite.bddAbove
    have hupper : marker (U + 1) ≤ U :=
      hU (show marker (U + 1) ∈
          marker '' (Set.univ : Set ℕ) from
        ⟨U + 1, Set.mem_univ _, rfl⟩)
    have hlower := hmarkerLarge (U + 1)
    omega
  obtain ⟨I, _hIuniv, hmarkerBij⟩ :=
    Set.exists_subset_bijOn (Set.univ : Set ℕ) marker
  have hI : I.Infinite := by
    intro hIfinite
    apply hmarkerImageInfinite
    rw [← hmarkerBij.image_eq]
    exact hIfinite.image marker
  obtain ⟨L₀, hL₀I, hL₀, R, hdelta⟩ :=
    exists_infinite_deltaSystem_of_bounded_pointMap
      hI core (k - 1) (fun i _hi => hcoreCard i)
  have hRsub : ∀ i ∈ L₀, R ⊆ core i := by
    intro i hiL x hxR
    obtain ⟨j, hjL, hij⟩ := hL₀.exists_gt i
    have hne : i ≠ j := Nat.ne_of_lt hij
    have hxInter : x ∈ core i ∩ core j := by
      rw [hdelta i hiL j hjL hne]
      exact hxR
    exact (Finset.mem_inter.mp hxInter).1
  let petal : ℕ → Finset ℕ := fun i => core i \ R
  let Moving : Set ℕ :=
    {i | i ∈ L₀ ∧ (petal i).Nonempty}
  by_cases hMoving : Moving.Infinite
  · left
    have hMovingL₀ : Moving ⊆ L₀ := fun _i hi => hi.1
    have hpetalDisjoint :
        ∀ i ∈ Moving, ∀ j ∈ Moving, i ≠ j →
          Disjoint (petal i) (petal j) := by
      intro i hiM j hjM hij
      rw [Finset.disjoint_left]
      intro x hxi hxj
      have hxInter : x ∈ core i ∩ core j :=
        Finset.mem_inter.mpr
          ⟨(Finset.mem_sdiff.mp hxi).1,
            (Finset.mem_sdiff.mp hxj).1⟩
      rw [hdelta i hiM.1 j hjM.1 hij] at hxInter
      exact (Finset.mem_sdiff.mp hxi).2 hxInter
    obtain ⟨L, hLMoving, hL, hcross⟩ :=
      exists_infinite_crossDisjoint_of_pairwiseDisjointBlocks
        hMoving petal support hpetalDisjoint
          (fun i _hi => hsupportCard i)
    obtain ⟨Even, Odd, hEvenL, hOddL, hEven, hOdd,
        hEvenOdd⟩ :=
      exists_two_disjoint_infinite_subsets_of_infinite hL
    let X : Set ℕ :=
      {x | ∃ i ∈ Even, x ∈ petal i}
    have hXA : X ⊆ A := by
      rintro x ⟨i, hiEven, hxPetal⟩
      have hxCore : x ∈ core i :=
        (Finset.mem_sdiff.mp hxPetal).1
      exact additiveSupportFamily_supportsIn
        A (k - 1) (target i - marker i)
          (core i) (hcoreMem i) x hxCore
    let point : ℕ → ℕ := fun i =>
      if hi : i ∈ Moving then
        hi.2.choose
      else 0
    have hpointPetal : ∀ i ∈ Even, point i ∈ petal i := by
      intro i hiEven
      have hiMoving : i ∈ Moving :=
        hLMoving (hEvenL hiEven)
      simp only [point, dif_pos hiMoving]
      exact (hLMoving (hEvenL hiEven)).2.choose_spec
    have hpointInj : Set.InjOn point Even := by
      intro i hiEven j hjEven hp
      by_contra hij
      exact Finset.disjoint_left.mp
        (hpetalDisjoint i (hLMoving (hEvenL hiEven))
          j (hLMoving (hEvenL hjEven)) hij)
        (hpointPetal i hiEven)
        (hp ▸ hpointPetal j hjEven)
    have hpointImageInfinite : (point '' Even).Infinite :=
      hEven.image hpointInj
    have hpointImageX : point '' Even ⊆ X := by
      rintro x ⟨i, hiEven, rfl⟩
      exact ⟨i, hiEven, hpointPetal i hiEven⟩
    have hXInfinite : X.Infinite :=
      hpointImageInfinite.mono hpointImageX
    let index : ℕ → ℕ := Nat.nth Even
    have hindexEven : ∀ n, index n ∈ Even := by
      intro n
      exact Nat.nth_mem_of_infinite hEven n
    have hindexStrict : StrictMono index :=
      Nat.nth_strictMono hEven
    let cell : ℕ → Finset ℕ := fun n => petal (index n)
    have hcellNonempty : ∀ n, (cell n).Nonempty := by
      intro n
      exact (hLMoving (hEvenL (hindexEven n))).2
    have hcellPairwise :
        Pairwise fun i j => Disjoint (cell i) (cell j) := by
      intro i j hij
      exact hpetalDisjoint
        (index i) (hLMoving (hEvenL (hindexEven i)))
        (index j) (hLMoving (hEvenL (hindexEven j)))
        (hindexStrict.injective.ne hij)
    have hcellMem : ∀ x, x ∈ X ↔ ∃ n, x ∈ cell n := by
      intro x
      constructor
      · rintro ⟨i, hiEven, hxPetal⟩
        have hiRange : i ∈ Set.range index := by
          change i ∈ Set.range (Nat.nth Even)
          rw [Nat.range_nth_of_infinite hEven]
          exact hiEven
        obtain ⟨n, rfl⟩ := hiRange
        exact ⟨n, hxPetal⟩
      · rintro ⟨n, hxCell⟩
        exact ⟨index n, hindexEven n, hxCell⟩
    have P : IsFiniteBlockPartition X cell :=
      ⟨hcellNonempty, hcellPairwise, hcellMem⟩
    have hcellCard : ∀ n, (cell n).card ≤ k - 1 := by
      intro n
      exact (Finset.card_le_card (Finset.sdiff_subset)).trans
        (hcoreCard (index n))
    have hsupportX : ∀ i ∈ Odd,
        Disjoint (support i : Set ℕ) X := by
      intro i hiOdd
      rw [Set.disjoint_left]
      rintro x hxSupport ⟨j, hjEven, hxPetal⟩
      have hiL : i ∈ L := hOddL hiOdd
      have hjL : j ∈ L := hEvenL hjEven
      have hij : i ≠ j := by
        intro hij
        exact Set.disjoint_left.mp hEvenOdd
          hjEven (hij ▸ hiOdd)
      exact Finset.disjoint_left.mp
        (hcross i hiL j hjL hij)
        (Finset.mem_coe.mp hxSupport) hxPetal
    have hmarkerInjOdd : Set.InjOn marker Odd :=
      hmarkerBij.injOn.mono
        (hOddL.trans
          (hLMoving.trans (hMovingL₀.trans hL₀I)))
    have htargetCofinal : ∀ N, ∃ i ∈ Odd, N ≤ upperTarget i := by
      intro N
      obtain ⟨i, hiOdd, hNi⟩ := hOdd.exists_gt N
      exact ⟨i, hiOdd,
        (Nat.le_of_lt hNi).trans
          ((hmarkerLarge i).trans (hmarkerUpper i))⟩
    refine ⟨X, Odd, marker, upperTarget, support, cell,
      hXA, hXInfinite, P, hcellCard,
      hOdd, hmarkerInjOdd, ?_,
      htargetCofinal⟩
    intro i hiOdd
    exact ⟨hmarkerLarge i, hmarkerA i,
      Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      hsupportMem i, hsupportX i hiOdd⟩
  · right
    have hMovingFinite : Moving.Finite :=
      Set.not_infinite.mp hMoving
    let K : Set ℕ := L₀ \ Moving
    have hK : K.Infinite := hL₀.diff hMovingFinite
    have hKL₀ : K ⊆ L₀ := Set.diff_subset
    have hcoreEq : ∀ i ∈ K, core i = R := by
      intro i hiK
      apply Finset.Subset.antisymm
      · intro x hxCore
        by_contra hxR
        have hpetalNonempty : (petal i).Nonempty :=
          ⟨x, Finset.mem_sdiff.mpr ⟨hxCore, hxR⟩⟩
        exact hiK.2 ⟨hiK.1, hpetalNonempty⟩
      · exact hRsub i (hKL₀ hiK)
    have hRnonempty : R.Nonempty := by
      obtain ⟨i, hiK⟩ := hK.nonempty
      rw [← hcoreEq i hiK]
      exact hcoreNonempty i
    let residual : ℕ → ℕ := fun i => target i - marker i
    obtain ⟨N, hescape⟩ :=
      additiveSupportFamily_eventuallyEscapesFiniteCores
        A (k - 1) R
    have hresidualImageFinite : (residual '' K).Finite := by
      apply (Set.finite_Iio N).subset
      rintro t ⟨i, hiK, rfl⟩
      have hlt : residual i < N := by
        by_contra hnot
        have houtside := hescape (residual i)
          (Nat.le_of_not_gt hnot) R (by
            simpa only [hcoreEq i hiK] using hcoreMem i)
        rw [Finset.sdiff_self] at houtside
        exact Finset.not_nonempty_empty houtside
      exact hlt
    have hinfiniteFiber : ∃ t ∈ residual '' K,
        (K ∩ residual ⁻¹' ({t} : Set ℕ)).Infinite := by
      by_contra hnoFiber
      push Not at hnoFiber
      apply hK
      apply Set.Finite.of_finite_fibers
        residual hresidualImageFinite
      intro t htImage
      exact hnoFiber t htImage
    obtain ⟨t, _htImage, hJ⟩ := hinfiniteFiber
    let J : Set ℕ := K ∩ residual ⁻¹' ({t} : Set ℕ)
    have hJK : J ⊆ K := Set.inter_subset_left
    have hresidualFixed : ∀ i ∈ J, residual i = t := by
      intro i hiJ
      simpa only [J] using hiJ.2
    have hRmem :
        R ∈ additiveSupportFamily A (k - 1) t := by
      obtain ⟨i, hiJ⟩ := hJ.nonempty
      have hmem := hcoreMem i
      rw [hcoreEq i (hJK hiJ)] at hmem
      simpa only [residual, hresidualFixed i hiJ] using hmem
    let oldPart : ℕ → Finset ℕ := fun i => destroyer i ∩ F
    have holdPartImageFinite : (oldPart '' J).Finite := by
      apply F.powerset.finite_toSet.subset
      rintro P ⟨i, hiJ, rfl⟩
      exact Finset.mem_powerset.mpr Finset.inter_subset_right
    have holdPartFiber : ∃ P ∈ oldPart '' J,
        (J ∩ oldPart ⁻¹' ({P} : Set (Finset ℕ))).Infinite := by
      by_contra hnoFiber
      push Not at hnoFiber
      apply hJ
      apply Set.Finite.of_finite_fibers
        oldPart holdPartImageFinite
      intro P hPImage
      exact hnoFiber P hPImage
    obtain ⟨P, hPImage, hJ'⟩ := holdPartFiber
    let J' : Set ℕ := J ∩ oldPart ⁻¹' ({P} : Set (Finset ℕ))
    have hJ'J : J' ⊆ J := Set.inter_subset_left
    have holdPartFixed : ∀ i ∈ J', oldPart i = P := by
      intro i hiJ'
      simpa only [J'] using hiJ'.2
    have hPsub : P ⊆ F := by
      obtain ⟨i, hiJ, hiPart⟩ := hPImage
      rw [← hiPart]
      exact Finset.inter_subset_right
    have hdestroyerEq : ∀ i ∈ J',
        destroyer i = insert (marker i) P := by
      intro i hiJ'
      apply Finset.Subset.antisymm
      · intro x hxD
        rcases Finset.mem_insert.mp (hdestroyerSubset i hxD) with
          hxb | hxF
        · exact hxb ▸ Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem <| by
            rw [← holdPartFixed i hiJ']
            exact Finset.mem_inter.mpr ⟨hxD, hxF⟩
      · intro x hxInsert
        rcases Finset.mem_insert.mp hxInsert with hxb | hxP
        · exact hxb ▸ hmarkerDestroyer i
        · have hxOld : x ∈ oldPart i := by
            rw [holdPartFixed i hiJ']
            exact hxP
          exact (Finset.mem_inter.mp hxOld).1
    have hmarkerInjJ' : Set.InjOn marker J' :=
      hmarkerBij.injOn.mono
        (hJ'J.trans (hJK.trans (hKL₀.trans hL₀I)))
    have htargetCofinal : ∀ N, ∃ i ∈ J', N ≤ target i := by
      intro N
      obtain ⟨i, hiJ', hNi⟩ := hJ'.exists_gt N
      exact ⟨i, hiJ',
        (Nat.le_of_lt hNi).trans
          ((hmarkerLarge i).trans (hmarkerTarget i))⟩
    refine ⟨J', marker, target, destroyer, P, R, t, hJ',
      hmarkerInjJ', hPsub, hRnonempty, hRmem, ?_, htargetCofinal⟩
    intro i hiJ'
    have hiJ : i ∈ J := hJ'J hiJ'
    have hiK : i ∈ K := hJK hiJ
    have hsplit : target i = marker i + residual i := by
      dsimp only [residual]
      have hle := hmarkerTarget i
      omega
    have hmarkerR : marker i ∉ R := by
      rw [← hcoreEq i hiK]
      exact hmarkerCore i
    have hsupportFixed :
        insert (marker i) R ∈
          additiveSupportFamily A k (target i) := by
      rw [← hcoreEq i hiK]
      exact hlowerSupportMem i
    have hcoreDestroyerFixed :
        Disjoint (R : Set ℕ) (destroyer i : Set ℕ) := by
      rw [← hcoreEq i hiK]
      exact hcoreDestroyer i
    have hprivateFixed :
        insert (marker i) R ∩ destroyer i = {marker i} := by
      rw [← hcoreEq i hiK]
      exact hlowerSupportPrivate i
    exact ⟨hmarkerLarge i, hmarkerA i, hmarkerR,
      hsplit.trans (congrArg (marker i + ·)
        (hresidualFixed i hiJ)),
      hdestroyerNonempty i, hmarkerDestroyer i,
      hdestroyerEq i hiJ',
      hdestroyerSubset i, hdestroyerDiff i,
      hdestroyerMinimal i, hcoreDestroyerFixed,
      hsupportFixed, hprivateFixed⟩

theorem HasAtomicPinnedTail.outerExit_or_privateCoreStage
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F) :
    ∀ L,
      HasMarkedConeOuterExitAt A k F L ∨
        Nonempty (MarkedPrivateCoreStage A k F L) := by
  intro L
  obtain ⟨b, n, hbA, hbF, hLb, hbn, hpin, hout⟩ :=
    htail.cofinal_markedConeRankFork hk hbasis L
  rcases hout with hdiag | hold | hmarked
  · exact Or.inl ⟨b, n, hbA, hbF, hLb, hbn,
      hpin, Or.inl hdiag⟩
  · exact Or.inl ⟨b, n, hbA, hbF, hLb, hbn,
      hpin, Or.inr (Or.inl hold)⟩
  · obtain hnonprivate | hprivate :=
      hmarked.nonPrivateExit_or_privateCoreStage hbA hLb
    · exact Or.inl ⟨b, n, hbA, hbF, hLb, hbn,
        hpin, Or.inr (Or.inr hnonprivate)⟩
    · exact Or.inr hprivate

theorem HasAtomicPinnedTail.privateCoreCase_deletion_or_fixedConflict
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F)
    (hnoOuter : ∀ L,
      ¬ HasMarkedConeOuterExitAt A k F L) :
    HasCofinalMarkedSupportSurvivalDeletion A k ∨
      HasFixedMarkedPrivateCoreConflict A k F := by
  apply cofinalMarkedPrivateCoreSupply_deletion_or_fixedConflict
    hk
  intro L
  obtain houter | hprivate :=
    htail.outerExit_or_privateCoreStage hk hbasis L
  · exact (hnoOuter L houter).elim
  · exact hprivate

theorem HasAtomicPinnedTail.privateCoreCase_forces_survivalDeletion
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F)
    (hnoOuter : ∀ L,
      ¬ HasMarkedConeOuterExitAt A k F L) :
    HasCofinalMarkedSupportSurvivalDeletion A k := by
  obtain hdel | hfixed :=
    htail.privateCoreCase_deletion_or_fixedConflict
      hk hbasis hnoOuter
  · exact hdel
  · exact hfixed.to_survivalDeletion hk

/-- Under a strong successor counterexample, the whole persistent private
case—not merely its moving-petal side—therefore enters the same bracketed
predecessor-destruction configuration. -/
theorem HasAtomicPinnedTail.privateCoreCase_forces_bracketedConflict
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hnoOuter : ∀ L,
      ¬ HasMarkedConeOuterExitAt A k F L) :
    HasBracketedPrivatePetalCounterexampleConflict A k := by
  exact
    (htail.privateCoreCase_forces_survivalDeletion
      hk hbasis hnoOuter).forces_bracketedConflict
        (by omega) hbasis hcounter

theorem HasAtomicPinnedTail.privateCoreCase_bracketed_or_fixedConflict
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1))
    (hnoOuter : ∀ L,
      ¬ HasMarkedConeOuterExitAt A k F L) :
    HasBracketedPrivatePetalCounterexampleConflict A k ∨
      HasFixedMarkedPrivateCoreConflict A k F := by
  obtain hdel | hfixed :=
    htail.privateCoreCase_deletion_or_fixedConflict
      hk hbasis hnoOuter
  · exact Or.inl <|
      hdel.forces_bracketedConflict (by omega) hbasis hcounter
  · exact Or.inr hfixed

end Erdos881
