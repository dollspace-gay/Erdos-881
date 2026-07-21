import Erdos881.RigidDestroyerRepairs

/-!
# Infinite pair Ramsey reduction

This file proves the elementary countable infinite Ramsey theorem for a
symmetric binary relation on a subset of `ℕ`.  It then applies that theorem to
rigid order-two pair sums, closing the nonrigid branch of the
splittable-independent construction.
-/

namespace Erdos881

/-- One homogeneous thinning step inside an infinite set. -/
structure InfinitePairRamseyStep
    (R : ℕ → ℕ → Prop) (S : Set ℕ) (last : ℕ) where
  point : ℕ
  point_mem : point ∈ S
  point_lower : last < point
  color : Bool
  next : Set ℕ
  next_infinite : next.Infinite
  next_subset : next ⊆ S
  next_above : ∀ x ∈ next, point < x
  uniform_true : color = true → ∀ x ∈ next, R point x
  uniform_false : color = false → ∀ x ∈ next, ¬ R point x

/-- Every infinite set admits one homogeneous thinning step. -/
theorem infinitePairRamseyStep_nonempty
    {R : ℕ → ℕ → Prop} {S : Set ℕ} {last : ℕ}
    (hS : S.Infinite) :
    Nonempty (InfinitePairRamseyStep R S last) := by
  classical
  obtain ⟨p, hpS, hpLast⟩ := hS.exists_gt last
  let rest : Set ℕ := S \ Set.Iic p
  have hrest : rest.Infinite := hS.diff (Set.finite_Iic p)
  let yes : Set ℕ := {x | x ∈ rest ∧ R p x}
  let no : Set ℕ := {x | x ∈ rest ∧ ¬ R p x}
  by_cases hyes : yes.Infinite
  · exact ⟨{
      point := p
      point_mem := hpS
      point_lower := hpLast
      color := true
      next := yes
      next_infinite := hyes
      next_subset := by
        intro x hx
        exact hx.1.1
      next_above := by
        intro x hx
        exact Nat.lt_of_not_ge hx.1.2
      uniform_true := by
        intro _h x hx
        exact hx.2
      uniform_false := by simp
    }⟩
  · have hno : no.Infinite := by
      by_contra hno
      have hyesFinite : yes.Finite := Set.not_infinite.mp hyes
      have hnoFinite : no.Finite := Set.not_infinite.mp hno
      apply hrest
      apply (hyesFinite.union hnoFinite).subset
      intro x hxRest
      by_cases hxR : R p x
      · exact Or.inl ⟨hxRest, hxR⟩
      · exact Or.inr ⟨hxRest, hxR⟩
    exact ⟨{
      point := p
      point_mem := hpS
      point_lower := hpLast
      color := false
      next := no
      next_infinite := hno
      next_subset := by
        intro x hx
        exact hx.1.1
      next_above := by
        intro x hx
        exact Nat.lt_of_not_ge hx.1.2
      uniform_true := by simp
      uniform_false := by
        intro _h x hx
        exact hx.2
    }⟩

/-- Recursive state for the countable Ramsey construction. -/
structure InfinitePairRamseyState (K : Set ℕ) where
  candidates : Set ℕ
  candidates_infinite : candidates.Infinite
  candidates_subset : candidates ⊆ K
  last : ℕ

/-- Infinite Ramsey's theorem for a symmetric relation on a subset of the
naturals. -/
theorem infinite_pairRamsey_nat
    {K : Set ℕ} (hK : K.Infinite)
    (R : ℕ → ℕ → Prop) (hsymm : Symmetric R) :
    (∃ L, L ⊆ K ∧ L.Infinite ∧ L.Pairwise R) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧
        L.Pairwise fun x y => ¬ R x y := by
  classical
  let State := InfinitePairRamseyState K
  let initial : State := {
    candidates := K
    candidates_infinite := hK
    candidates_subset := Set.Subset.rfl
    last := 0
  }
  let chooseStep : (s : State) →
      InfinitePairRamseyStep R s.candidates s.last :=
    fun s => Classical.choice <|
      infinitePairRamseyStep_nonempty s.candidates_infinite
  let advance (s : State) : State := {
    candidates := (chooseStep s).next
    candidates_infinite := (chooseStep s).next_infinite
    candidates_subset :=
      (chooseStep s).next_subset.trans s.candidates_subset
    last := (chooseStep s).point
  }
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let step (i : ℕ) := chooseStep (state i)
  let a (i : ℕ) := (step i).point
  let color (i : ℕ) := (step i).color
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hcandidates_succ : ∀ i,
      (state (i + 1)).candidates = (step i).next := by
    intro i
    change (state (i + 1)).candidates =
      (chooseStep (state i)).next
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).last = a i := by
    intro i
    change (state (i + 1)).last = (chooseStep (state i)).point
    rw [hstate_succ]
  have hcandidates_step : ∀ i,
      (state (i + 1)).candidates ⊆ (state i).candidates := by
    intro i
    rw [hcandidates_succ]
    exact (step i).next_subset
  have hcandidates_antitone :
      Antitone fun i => (state i).candidates :=
    antitone_nat_of_succ_le hcandidates_step
  have haK : ∀ i, a i ∈ K := by
    intro i
    exact (state i).candidates_subset (step i).point_mem
  have haMono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower := (step (i + 1)).point_lower
    change (state (i + 1)).last < a (i + 1) at hlower
    rw [hlast_succ] at hlower
    exact hlower
  have hfuture : ∀ {i j}, i < j → a j ∈ (step i).next := by
    intro i j hij
    rw [← hcandidates_succ]
    exact hcandidates_antitone (Nat.succ_le_of_lt hij)
      (step j).point_mem
  obtain ⟨q, hqFiber⟩ := Finite.exists_infinite_fiber color
  let I : Set ℕ := {i | color i = q}
  have hI : I.Infinite := by
    apply Set.infinite_coe_iff.mp
    simpa [I] using hqFiber
  let L : Set ℕ := a '' I
  have hLinf : L.Infinite := by
    apply (Set.infinite_image_iff haMono.injective.injOn).mpr hI
  have hLK : L ⊆ K := by
    rintro _ ⟨i, _hiI, rfl⟩
    exact haK i
  cases q with
  | false =>
      right
      refine ⟨L, hLK, hLinf, ?_⟩
      rintro x ⟨i, hiI, rfl⟩ y ⟨j, hjI, rfl⟩ hxy
      have hij : i ≠ j := fun hij => hxy (congrArg a hij)
      have hci : color i = false := hiI
      have hcj : color j = false := hjI
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · exact (step i).uniform_false hci (a j) (hfuture hijlt)
      · intro hR
        exact (step j).uniform_false hcj (a i) (hfuture hjilt)
          (hsymm hR)
  | true =>
      left
      refine ⟨L, hLK, hLinf, ?_⟩
      rintro x ⟨i, hiI, rfl⟩ y ⟨j, hjI, rfl⟩ hxy
      have hij : i ≠ j := fun hij => hxy (congrArg a hij)
      have hci : color i = true := hiI
      have hcj : color j = true := hjI
      rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · exact (step i).uniform_true hci (a j) (hfuture hijlt)
      · exact hsymm <|
          (step j).uniform_true hcj (a i) (hfuture hjilt)

/-! ## Application to rigid pair sums -/

/-- Pair-sum rigidity is symmetric in its two displayed summands. -/
theorem isRigidPairSum_comm
    {A : Set ℕ} {x y : ℕ} :
    IsRigidPairSum A x y ↔ IsRigidPairSum A y x := by
  constructor
  · intro h E hER
    have hER' : E ∈ additiveSupportFamily A 2 (x + y) := by
      simpa [Nat.add_comm] using hER
    have hEq := h E hER'
    rw [hEq]
    ext z
    simp [pairSupport]
    omega
  · intro h E hER
    have hER' : E ∈ additiveSupportFamily A 2 (y + x) := by
      simpa [Nat.add_comm] using hER
    have hEq := h E hER'
    rw [hEq]
    ext z
    simp [pairSupport]
    omega

/-- Every infinite set with nonrigid doubles contains either an infinite
pairwise-nonrigid subset or an infinite pairwise-rigid subset. -/
theorem infinite_nonrigid_or_rigid_pairSums
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hdouble : HasNoRigidDoubles A K) :
    (∃ L, L ⊆ K ∧ L.Infinite ∧
      HasNoRigidDoubles A L ∧ IsPairwiseNonrigidSet A L) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧
        HasNoRigidDoubles A L ∧ IsPairwiseRigidSet A L := by
  have hsymm : Symmetric fun x y => IsRigidPairSum A x y := by
    intro x y hxy
    exact isRigidPairSum_comm.mp hxy
  obtain hrigid | hnonrigid :=
    infinite_pairRamsey_nat hK (fun x y => IsRigidPairSum A x y) hsymm
  · right
    obtain ⟨L, hLK, hL, hpair⟩ := hrigid
    exact ⟨L, hLK, hL, fun x hx => hdouble x (hLK hx),
      fun x hx y hy hxy => hpair hx hy hxy⟩
  · left
    obtain ⟨L, hLK, hL, hpair⟩ := hnonrigid
    exact ⟨L, hLK, hL, fun x hx => hdouble x (hLK hx),
      fun x hx y hy hxy => hpair hx hy hxy⟩

/-- Rigid doubles inside a proposed self-basis deletion reservoir. -/
def rigidDoubleSet (A B₀ : Set ℕ) : Set ℕ :=
  {x | x ∈ B₀ ∧ IsRigidPairSum A x x}

/-- Complete Ramsey reduction of the splittable-independent construction
once a self-basis reservoir has been found.  The construction succeeds unless
there are infinitely many rigid doubles or an infinite pairwise-rigid clique.
The clique can moreover be chosen with no rigid doubles. -/
theorem infiniteDeletion_or_rigidObstruction_of_selfBasisReservoir
    {A B₀ : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A) (hB₀ : B₀.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A) :
    (∃ B, B ⊆ B₀ ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      (rigidDoubleSet A B₀).Infinite ∨
      ∃ K, K ⊆ B₀ ∧ K.Infinite ∧
        HasNoRigidDoubles A K ∧ IsPairwiseRigidSet A K := by
  classical
  by_cases hdiag : (rigidDoubleSet A B₀).Infinite
  · exact Or.inr (Or.inl hdiag)
  · have hdiagFinite : (rigidDoubleSet A B₀).Finite :=
      Set.not_infinite.mp hdiag
    let K : Set ℕ := B₀ \ rigidDoubleSet A B₀
    have hK : K.Infinite := hB₀.diff hdiagFinite
    have hKB₀ : K ⊆ B₀ := Set.diff_subset
    have hdouble : HasNoRigidDoubles A K := by
      intro x hxK hxRigid
      exact hxK.2 ⟨hxK.1, hxRigid⟩
    obtain hnonrigid | hrigid :=
      infinite_nonrigid_or_rigid_pairSums hK hdouble
    · left
      obtain ⟨L, hLK, hL, hLdouble, hLnonrigid⟩ := hnonrigid
      obtain ⟨B, hBL, hB, hthree⟩ :=
        exists_infiniteDeletion_threeBasis_of_nonrigidSelfBasisReservoir
          hbasis hB₀A hself (fun x hx => hKB₀ (hLK hx))
          hL hLnonrigid hLdouble
      exact ⟨B, fun x hx => hKB₀ (hLK (hBL hx)), hB, hthree⟩
    · right; right
      obtain ⟨L, hLK, hL, hLdouble, hLrigid⟩ := hrigid
      exact ⟨L, fun x hx => hKB₀ (hLK hx), hL,
        hLdouble, hLrigid⟩

/-- Matching growth for order-two supports along targets in `A` constructs
the self-basis reservoir automatically.  Hence that whole growth branch is
reduced to the two explicit rigid obstructions above. -/
theorem infiniteDeletion_or_rigidObstruction_of_selfMatchingGrowth
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hgrowth : MatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A 2) ∅ A) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      (∃ B₀, B₀ ⊆ A ∧ B₀.Infinite ∧
        IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A ∧
        (rigidDoubleSet A B₀).Infinite) ∨
      ∃ B₀ K, B₀ ⊆ A ∧ B₀.Infinite ∧
        IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A ∧
        K ⊆ B₀ ∧ K.Infinite ∧
        HasNoRigidDoubles A K ∧ IsPairwiseRigidSet A K := by
  obtain ⟨B₀, hB₀A, hB₀, _hB₀empty, hsurvive⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutsideAlong
      (C := A) (S := A)
      (R := additiveSupportFamily A 2) (F := ∅)
      (additiveSupportFamily_supportsBounded A 2)
      hgrowth (hbasis.unboundedOutside ∅)
  have hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A :=
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive
  obtain hdone | hdiag | hclique :=
    infiniteDeletion_or_rigidObstruction_of_selfBasisReservoir
      hbasis hB₀A hB₀ hself
  · left
    obtain ⟨B, hBB₀, hB, hthree⟩ := hdone
    exact ⟨B, fun x hx => hB₀A (hBB₀ hx), hB, hthree⟩
  · right; left
    exact ⟨B₀, hB₀A, hB₀, hself, hdiag⟩
  · right; right
    obtain ⟨K, hKB₀, hK, hdouble, hrigid⟩ := hclique
    exact ⟨B₀, K, hB₀A, hB₀, hself,
      hKB₀, hK, hdouble, hrigid⟩

end Erdos881
