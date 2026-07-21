import Erdos881.BoundedStratumSplitting
import Erdos881.CertificateAmplification
import Erdos881.HybridPairTripleRepairs
import Erdos881.InfiniteSunflower

/-!
# Free-set thinning of local direct triple repairs

If every distinct pair in an infinite reservoir has a triple repair avoiding
its two endpoints, choose one such repair for every unordered pair.  Its
support has cardinality at most three, so the bounded pair-map free-set
theorem thins the reservoir until every chosen repair avoids the entire
thinned set.  Nonrigid doubles then supply the diagonal hybrid repairs.
-/

namespace Erdos881

/-- Every distinct pair has some direct order-three repair avoiding just its
two endpoints.  The free-set theorem will upgrade this local avoidance to
avoidance of one common infinite deletion. -/
def HasPairwiseLocalDirectTripleRepairs
    (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
    ∃ G ∈ additiveSupportFamily A 3 (x + y),
      Disjoint (G : Set ℕ) (({x, y} : Finset ℕ) : Set ℕ)

/-- Free-set thinning upgrades endpoint avoidance for distinct pairs to
avoidance of one common infinite set. -/
theorem exists_infinite_distinctDirectRepairs_of_pairwiseLocalDirectRepairs
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hlocal : HasPairwiseLocalDirectTripleRepairs A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      ∀ x ∈ B, ∀ y ∈ B, x ≠ y →
        ∃ G ∈ additiveSupportFamily A 3 (x + y),
          Disjoint (G : Set ℕ) B := by
  classical
  let HasRepair (P : Finset ℕ) : Prop :=
    ∃ G ∈ additiveSupportFamily A 3 (P.sum id),
      Disjoint (G : Set ℕ) (P : Set ℕ)
  let chooseSupport (P : Finset ℕ) : Finset ℕ :=
    if h : HasRepair P then Classical.choose h else ∅
  let f : ℕ → ℕ → Finset ℕ := fun x y =>
    chooseSupport {x, y}
  have hfsymm : ∀ x y, f x y = f y x := by
    intro x y
    have hp : ({x, y} : Finset ℕ) = {y, x} := by
      ext z
      simp [or_comm]
    simp only [f, hp]
  have hfRepair : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      f x y ∈ additiveSupportFamily A 3 (x + y) ∧
        Disjoint (f x y : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ) := by
    intro x hxK y hyK hxy
    obtain ⟨G, hGR, hGpair⟩ := hlocal x hxK y hyK hxy
    have hHas : HasRepair {x, y} := by
      refine ⟨G, ?_, hGpair⟩
      simpa [hxy] using hGR
    have hspec : chooseSupport {x, y} ∈
          additiveSupportFamily A 3 (({x, y} : Finset ℕ).sum id) ∧
        Disjoint (chooseSupport {x, y} : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ) := by
      simp only [chooseSupport, dif_pos hHas]
      exact Classical.choose_spec hHas
    change chooseSupport {x, y} ∈
          additiveSupportFamily A 3 (x + y) ∧
        Disjoint (chooseSupport {x, y} : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ)
    simpa [hxy] using hspec
  have hfcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      (f x y).card ≤ 3 := by
    intro x hxK y hyK hxy
    exact additiveSupportFamily_cardAtMost A 3 (x + y)
      (f x y) (hfRepair x hxK y hyK hxy).1
  have hfavoid : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      x ∉ f x y ∧ y ∉ f x y := by
    intro x hxK y hyK hxy
    have hdisj := (hfRepair x hxK y hyK hxy).2
    constructor
    · intro hx
      exact Set.disjoint_left.mp hdisj hx (by simp)
    · intro hy
      exact Set.disjoint_left.mp hdisj hy (by simp)
  obtain ⟨B, hBK, hB, hfree⟩ :=
    exists_infinite_freeSet_of_symmetric_bounded_pairMap
      hK f 3 hfsymm hfcard hfavoid
  refine ⟨B, hBK, hB, ?_⟩
  intro x hxB y hyB hxy
  exact ⟨f x y, (hfRepair x (hBK hxB) y (hBK hyB) hxy).1,
    hfree x hxB y hyB hxy⟩

/-- Local endpoint-avoiding direct repairs on the rigid/no-double branch can
be thinned to the global hybrid repair invariant. -/
theorem exists_infinite_hybridRepairs_of_pairwiseLocalDirectRepairs
    {A K : Set ℕ}
    (hKA : K ⊆ A)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K)
    (hlocal : HasPairwiseLocalDirectTripleRepairs A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧ HasHybridPairTripleRepairs A B := by
  classical
  let HasRepair (P : Finset ℕ) : Prop :=
    ∃ G ∈ additiveSupportFamily A 3 (P.sum id),
      Disjoint (G : Set ℕ) (P : Set ℕ)
  let chooseSupport (P : Finset ℕ) : Finset ℕ :=
    if h : HasRepair P then Classical.choose h else ∅
  let f : ℕ → ℕ → Finset ℕ := fun x y =>
    chooseSupport {x, y}
  have hfsymm : ∀ x y, f x y = f y x := by
    intro x y
    have hp : ({x, y} : Finset ℕ) = {y, x} := by
      ext z
      simp [or_comm]
    simp only [f, hp]
  have hfRepair : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      f x y ∈ additiveSupportFamily A 3 (x + y) ∧
        Disjoint (f x y : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ) := by
    intro x hxK y hyK hxy
    obtain ⟨G, hGR, hGpair⟩ := hlocal x hxK y hyK hxy
    have hHas : HasRepair {x, y} := by
      refine ⟨G, ?_, hGpair⟩
      simpa [hxy] using hGR
    have hspec : chooseSupport {x, y} ∈
          additiveSupportFamily A 3 (({x, y} : Finset ℕ).sum id) ∧
        Disjoint (chooseSupport {x, y} : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ) := by
      simp only [chooseSupport, dif_pos hHas]
      exact Classical.choose_spec hHas
    change chooseSupport {x, y} ∈
          additiveSupportFamily A 3 (x + y) ∧
        Disjoint (chooseSupport {x, y} : Set ℕ)
          (({x, y} : Finset ℕ) : Set ℕ)
    simpa [hxy] using hspec
  have hfcard : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      (f x y).card ≤ 3 := by
    intro x hxK y hyK hxy
    exact additiveSupportFamily_cardAtMost A 3 (x + y)
      (f x y) (hfRepair x hxK y hyK hxy).1
  have hfavoid : ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
      x ∉ f x y ∧ y ∉ f x y := by
    intro x hxK y hyK hxy
    have hdisj := (hfRepair x hxK y hyK hxy).2
    constructor
    · intro hx
      exact Set.disjoint_left.mp hdisj hx (by simp)
    · intro hy
      exact Set.disjoint_left.mp hdisj hy (by simp)
  obtain ⟨B, hBK, hB, hfree⟩ :=
    exists_infinite_freeSet_of_symmetric_bounded_pairMap
      hK f 3 hfsymm hfcard hfavoid
  refine ⟨B, hBK, hB, ?_⟩
  intro x hxB y hyB
  by_cases hxy : x = y
  · subst y
    left
    obtain ⟨E, hER, hEnotK⟩ :=
      exists_orderTwoSupport_not_subset_of_pairwiseRigid_noDoubles
        hKA hrigid hdouble (hBK hxB)
    exact ⟨E, hER, fun hEB => hEnotK (hEB.trans hBK)⟩
  · right
    have hrepair := hfRepair x (hBK hxB) y (hBK hyB) hxy
    exact ⟨f x y, hrepair.1, hfree x hxB y hyB hxy⟩

/-- Complete bridge from local endpoint-avoiding repairs to the desired
infinite deletion leaving an exact order-three basis. -/
theorem exists_infiniteDeletion_threeBasis_of_pairwiseLocalDirectRepairs
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K)
    (hlocal : HasPairwiseLocalDirectTripleRepairs A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hKA : K ⊆ A := fun x hx => hB₀A (hKB₀ hx)
  obtain ⟨B, hBK, hB, hrepair⟩ :=
    exists_infinite_hybridRepairs_of_pairwiseLocalDirectRepairs
      hKA hK hrigid hdouble hlocal
  have hBA : B ⊆ A := hBK.trans hKA
  have hselfB : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A :=
    exactTwoBasisAlong_self_of_deletion_subset
      (hBK.trans hKB₀) hself
  obtain ⟨B', hB'B, hB', hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_hybridRepairs
      hbasis hBA hB hselfB hrepair
  exact ⟨B', hB'B.trans hBK, hB', hthree⟩

/-- Every diagonal sum has a direct triple repair avoiding its repeated
endpoint. -/
def HasLocalDirectTripleRepairsForDoubles
    (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∃ G ∈ additiveSupportFamily A 3 (x + x),
    Disjoint (G : Set ℕ) (({x} : Finset ℕ) : Set ℕ)

/-- Pair-map free thinning followed by point-map free thinning makes both
the distinct-pair and diagonal local repairs avoid one common infinite set.
-/
theorem exists_infinite_directRepairs_of_localPairAndDoubleRepairs
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hpairs : HasPairwiseLocalDirectTripleRepairs A K)
    (hdoubles : HasLocalDirectTripleRepairsForDoubles A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasDirectTripleRepairsForDeletedPairs A B := by
  classical
  obtain ⟨B₁, hB₁K, hB₁, hpairs₁⟩ :=
    exists_infinite_distinctDirectRepairs_of_pairwiseLocalDirectRepairs
      hK hpairs
  let HasDoubleRepair (x : ℕ) : Prop :=
    ∃ G ∈ additiveSupportFamily A 3 (x + x),
      Disjoint (G : Set ℕ) (({x} : Finset ℕ) : Set ℕ)
  let g : ℕ → Finset ℕ := fun x =>
    if h : HasDoubleRepair x then Classical.choose h else ∅
  have hgRepair : ∀ x ∈ B₁,
      g x ∈ additiveSupportFamily A 3 (x + x) ∧
        Disjoint (g x : Set ℕ) (({x} : Finset ℕ) : Set ℕ) := by
    intro x hxB₁
    have hHas : HasDoubleRepair x := hdoubles x (hB₁K hxB₁)
    simp only [g, dif_pos hHas]
    exact Classical.choose_spec hHas
  have hgcard : ∀ x ∈ B₁, (g x).card ≤ 3 := by
    intro x hxB₁
    exact additiveSupportFamily_cardAtMost A 3 (x + x)
      (g x) (hgRepair x hxB₁).1
  have hgavoid : ∀ x ∈ B₁, x ∉ g x := by
    intro x hxB₁ hxg
    exact Set.disjoint_left.mp (hgRepair x hxB₁).2 hxg (by simp)
  obtain ⟨B, hBB₁, hB, hgfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hB₁ g 3 hgcard hgavoid
  refine ⟨B, hBB₁.trans hB₁K, hB, ?_⟩
  intro x hxB y hyB
  by_cases hxy : x = y
  · subst y
    exact ⟨g x, (hgRepair x (hBB₁ hxB)).1, hgfree x hxB⟩
  · obtain ⟨G, hGR, hGB₁⟩ :=
      hpairs₁ x (hBB₁ hxB) y (hBB₁ hyB) hxy
    exact ⟨G, hGR, hGB₁.mono_right hBB₁⟩

/-- Local repairs for every distinct pair and every double already imply the
desired infinite deletion on a self-basis reservoir. -/
theorem exists_infiniteDeletion_threeBasis_of_localPairAndDoubleRepairs
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hpairs : HasPairwiseLocalDirectTripleRepairs A K)
    (hdoubles : HasLocalDirectTripleRepairsForDoubles A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hBK, hB, hrepair⟩ :=
    exists_infinite_directRepairs_of_localPairAndDoubleRepairs
      hK hpairs hdoubles
  have hBA : B ⊆ A := fun x hx => hB₀A (hKB₀ (hBK hx))
  have hselfB : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A :=
    exactTwoBasisAlong_self_of_deletion_subset
      (hBK.trans hKB₀) hself
  obtain ⟨B', hB'B, hB', hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_directTripleRepairs
      hbasis hBA hB hselfB hrepair
  exact ⟨B', hB'B.trans hBK, hB', hthree⟩

/-! ## Ramsey reduction to two-point order-three destroyers -/

/-- Every distinct pair in `K` destroys all order-three supports at its own
sum.  This is the exact clique obstruction left after free-set thinning. -/
def IsPairwiseOrderThreeSumDestroyerSet
    (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y →
    DestroysAt (additiveSupportFamily A 3)
      ((({x, y} : Finset ℕ) : Set ℕ)) (x + y)

theorem orderThreePairSumDestroyer_comm
    {A : Set ℕ} {x y : ℕ} :
    DestroysAt (additiveSupportFamily A 3)
        ((({x, y} : Finset ℕ) : Set ℕ)) (x + y) ↔
      DestroysAt (additiveSupportFamily A 3)
        ((({y, x} : Finset ℕ) : Set ℕ)) (y + x) := by
  have hp : ({x, y} : Finset ℕ) = {y, x} := by
    ext z
    simp [or_comm]
  rw [hp, Nat.add_comm]

/-- On the pairwise-rigid/no-double branch, pair Ramsey plus bounded
free-set thinning either completes the desired deletion or leaves an
infinite clique of genuine two-point order-three destroyers. -/
theorem infiniteDeletionThreeBasis_or_pairwiseOrderThreeDestroyers
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    (∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧
        IsPairwiseRigidSet A L ∧ HasNoRigidDoubles A L ∧
        IsPairwiseOrderThreeSumDestroyerSet A L := by
  let R : ℕ → ℕ → Prop := fun x y =>
    DestroysAt (additiveSupportFamily A 3)
      ((({x, y} : Finset ℕ) : Set ℕ)) (x + y)
  have hRcomm : Symmetric R := by
    intro x y hxy
    exact orderThreePairSumDestroyer_comm.mp hxy
  obtain ⟨L, hLK, hL, hdestroy⟩ | ⟨L, hLK, hL, hrepair⟩ :=
    infinite_pairRamsey_nat hK R hRcomm
  · right
    have hrigidL : IsPairwiseRigidSet A L := by
      intro x hx y hy hxy
      exact hrigid x (hLK hx) y (hLK hy) hxy
    have hdoubleL : HasNoRigidDoubles A L := by
      intro x hx
      exact hdouble x (hLK hx)
    exact ⟨L, hLK, hL, hrigidL, hdoubleL, hdestroy⟩
  · left
    have hlocal : HasPairwiseLocalDirectTripleRepairs A L := by
      intro x hx y hy hxy
      exact not_destroysAt_iff.mp (hrepair hx hy hxy)
    have hrigidL : IsPairwiseRigidSet A L := by
      intro x hx y hy hxy
      exact hrigid x (hLK hx) y (hLK hy) hxy
    have hdoubleL : HasNoRigidDoubles A L := by
      intro x hx
      exact hdouble x (hLK hx)
    obtain ⟨B, hBL, hB, hthree⟩ :=
      exists_infiniteDeletion_threeBasis_of_pairwiseLocalDirectRepairs
        hbasis hB₀A hself (hLK.trans hKB₀) hL
        hrigidL hdoubleL hlocal
    exact ⟨B, hBL.trans hLK, hB, hthree⟩

/-! ## Eliminating the two-point destroyer clique -/

/-- Fix `a ∈ A`.  On a two-point order-three destroyer clique, at most one
sufficiently late point can fail to have its backward translate by `a` in
`A`.  Indeed, a pair representation of `x + y - a`, lifted through `a`, must
hit `x` or `y`; removing that hit leaves respectively `y - a` or `x - a` in
`A`. -/
theorem pairwiseOrderThreeDestroyers_backwardTranslateExceptions_subsingleton
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hdestroy : IsPairwiseOrderThreeSumDestroyerSet A K)
    {a : ℕ} (haA : a ∈ A) :
    ∃ T, {x | x ∈ K ∧ T ≤ x ∧ x - a ∉ A}.Subsingleton := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N + a + 1, ?_⟩
  intro x hx y hy
  by_contra hxy
  let n := x + y - a
  have hxT : N + a + 1 ≤ x := hx.2.1
  have hyT : N + a + 1 ≤ y := hy.2.1
  have haX : a < x := by omega
  have haY : a < y := by omega
  have hnN : N ≤ n := by
    dsimp only [n]
    omega
  obtain ⟨E, hER, _hEempty⟩ := hN n hnN
  have hGR : insert a E ∈ additiveSupportFamily A 3 (x + y) := by
    have hlift := insert_mem_additiveSupportFamily_succ haA hER
    have hsum : a + n = x + y := by
      dsimp only [n]
      omega
    simpa [hsum] using hlift
  have hhit := hdestroy x hx.1 y hy.1 hxy (insert a E) hGR
  obtain ⟨z, hzG, hzPair⟩ := Set.not_disjoint_iff.mp hhit
  have hzG' : z = a ∨ z ∈ E := by
    simpa using hzG
  have hzPair' : z = x ∨ z = y := by
    simpa using hzPair
  have hzE : z ∈ E := by
    rcases hzG' with rfl | hzE
    · rcases hzPair' with hax | hay
      · exact (Nat.ne_of_lt haX hax).elim
      · exact (Nat.ne_of_lt haY hay).elim
    · exact hzE
  rcases hzPair' with hzx | hzy
  · have hxE : x ∈ E := hzx ▸ hzE
    have hxle : x ≤ n := by
      dsimp only [n]
      omega
    have hEq := additiveSupportFamily_two_eq_pairSupport_of_mem hER hxE
    have hcompE : n - x ∈ E := by
      rw [hEq]
      simp [pairSupport]
    have hcompA := additiveSupportFamily_supportsIn A 2 n E hER
      (n - x) hcompE
    have hcomp : n - x = y - a := by
      dsimp only [n]
      omega
    exact hy.2.2 (hcomp ▸ hcompA)
  · have hyE : y ∈ E := hzy ▸ hzE
    have hyle : y ≤ n := by
      dsimp only [n]
      omega
    have hEq := additiveSupportFamily_two_eq_pairSupport_of_mem hER hyE
    have hcompE : n - y ∈ E := by
      rw [hEq]
      simp [pairSupport]
    have hcompA := additiveSupportFamily_supportsIn A 2 n E hER
      (n - y) hcompE
    have hcomp : n - y = x - a := by
      dsimp only [n]
      omega
    exact hx.2.2 (hcomp ▸ hcompA)

/-- The self-basis splitting available on the deletion reservoir rules out an
infinite two-point order-three destroyer clique.  Split one fixed clique point
`d = c + e` outside the reservoir.  Almost every later clique point has both
backward translates by `c` and by `e` in `A`; for suitable `x < y`, the triple
`{x-c, y-e, d}` then represents `x+y` while avoiding both endpoints. -/
theorem not_infinite_pairwiseOrderThreeDestroyers_of_selfBasis
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite) :
    ¬ IsPairwiseOrderThreeSumDestroyerSet A K := by
  classical
  intro hdestroy
  obtain ⟨L, hL⟩ := hself
  obtain ⟨d, hdK, hdL⟩ := hK.exists_gt L
  have hdA : d ∈ A := hB₀A (hKB₀ hdK)
  obtain ⟨v, hvC, hvsum⟩ := hL d (Nat.le_of_lt hdL) hdA
  let c := v 0
  let e := v 1
  have hcC : c ∈ A \ B₀ := hvC 0
  have heC : e ∈ A \ B₀ := hvC 1
  have hce : c + e = d := by
    simpa [c, e, Fin.sum_univ_two] using hvsum
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    have hed : e = d := by omega
    exact heC.2 (hed ▸ hKB₀ hdK)
  have hepos : 0 < e := by
    by_contra he
    have he0 : e = 0 := Nat.eq_zero_of_not_pos he
    have hcd : c = d := by omega
    exact hcC.2 (hcd ▸ hKB₀ hdK)
  obtain ⟨Tc, hbadc⟩ :=
    pairwiseOrderThreeDestroyers_backwardTranslateExceptions_subsingleton
      hbasis hdestroy hcC.1
  obtain ⟨Te, hbade⟩ :=
    pairwiseOrderThreeDestroyers_backwardTranslateExceptions_subsingleton
      hbasis hdestroy heC.1
  let BadC : Set ℕ := {x | x ∈ K ∧ Tc ≤ x ∧ x - c ∉ A}
  let BadE : Set ℕ := {x | x ∈ K ∧ Te ≤ x ∧ x - e ∉ A}
  let excluded : Set ℕ :=
    Set.Iic (max d (max Tc Te)) ∪ BadC ∪ BadE
  have hexcluded : excluded.Finite := by
    apply ((Set.finite_Iic (max d (max Tc Te))).union hbadc.finite).union
    exact hbade.finite
  let H : Set ℕ := K \ excluded
  have hH : H.Infinite := hK.diff hexcluded
  obtain ⟨x, hxH⟩ := hH.nonempty
  have hHavoid : (H \ ({x + e} : Set ℕ)).Infinite :=
    hH.diff (Set.finite_singleton (x + e))
  obtain ⟨y, hyH', hxy⟩ := hHavoid.exists_gt x
  have hyH : y ∈ H := hyH'.1
  have hyGap : y ≠ x + e := hyH'.2
  have hxK : x ∈ K := hxH.1
  have hyK : y ∈ K := hyH.1
  have hxNotExcluded : x ∉ excluded := hxH.2
  have hyNotExcluded : y ∉ excluded := hyH.2
  have hdltx : d < x := by
    have hxIic : x ∉ Set.Iic (max d (max Tc Te)) := by
      intro hx
      exact hxNotExcluded (Or.inl (Or.inl hx))
    have hmaxlt : max d (max Tc Te) < x := Nat.lt_of_not_ge hxIic
    exact lt_of_le_of_lt (le_max_left _ _) hmaxlt
  have hxTc : Tc ≤ x := by
    have hxIic : x ∉ Set.Iic (max d (max Tc Te)) := by
      intro hx
      exact hxNotExcluded (Or.inl (Or.inl hx))
    have hmaxlt : max d (max Tc Te) < x := Nat.lt_of_not_ge hxIic
    exact le_trans (le_trans (le_max_left Tc Te)
      (le_max_right d (max Tc Te))) (Nat.le_of_lt hmaxlt)
  have hyTe : Te ≤ y := by
    have hyIic : y ∉ Set.Iic (max d (max Tc Te)) := by
      intro hy
      exact hyNotExcluded (Or.inl (Or.inl hy))
    have hmaxlt : max d (max Tc Te) < y := Nat.lt_of_not_ge hyIic
    exact le_trans (le_trans (le_max_right Tc Te)
      (le_max_right d (max Tc Te))) (Nat.le_of_lt hmaxlt)
  have hxcA : x - c ∈ A := by
    by_contra hnot
    apply hxNotExcluded
    exact Or.inl (Or.inr ⟨hxK, hxTc, hnot⟩)
  have hyeA : y - e ∈ A := by
    by_contra hnot
    apply hyNotExcluded
    exact Or.inr ⟨hyK, hyTe, hnot⟩
  let m := (x - c) + (y - e)
  have hpair : pairSupport m (x - c) ∈
      additiveSupportFamily A 2 m := by
    apply pairSupport_mem_additiveSupportFamily (by simp [m]) hxcA
    have hsub : m - (x - c) = y - e := by simp [m]
    simpa [hsub] using hyeA
  let G : Finset ℕ := insert d (pairSupport m (x - c))
  have hGR : G ∈ additiveSupportFamily A 3 (x + y) := by
    have hlift := insert_mem_additiveSupportFamily_succ hdA hpair
    have hsum : d + m = x + y := by
      dsimp only [m]
      omega
    simpa [G, hsum] using hlift
  have hGdisjoint : Disjoint (G : Set ℕ)
      ((({x, y} : Finset ℕ) : Set ℕ)) := by
    rw [Set.disjoint_left]
    intro z hzG hzPair
    have hzG' : z = d ∨ z = x - c ∨ z = y - e := by
      have hsub : m - (x - c) = y - e := by simp [m]
      simpa [G, pairSupport, hsub] using hzG
    have hzPair' : z = x ∨ z = y := by simpa using hzPair
    rcases hzG' with rfl | rfl | rfl <;>
      rcases hzPair' with hEq | hEq
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  exact (hdestroy x hxK y hyK (Nat.ne_of_lt hxy) G hGR) hGdisjoint

/-- Consequently the Ramsey alternative above always lands on the completed
deletion side; the two-point destroyer clique is incompatible with the
self-basis reservoir. -/
theorem exists_infiniteDeletion_threeBasis_of_rigidNoDoubles
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain hdone | ⟨L, hLK, hL, _hrigidL, _hdoubleL, htripleL⟩ :=
    infiniteDeletionThreeBasis_or_pairwiseOrderThreeDestroyers
      hbasis hB₀A hself hKB₀ hK hrigid hdouble
  · exact hdone
  · exact (not_infinite_pairwiseOrderThreeDestroyers_of_selfBasis
      hbasis hB₀A hself (hLK.trans hKB₀) hL htripleL).elim

/-! ## Diagonal order-three destroyers -/

/-- A singleton destroyer at `2*x` forces every sufficiently late backward
translate `x-a` by a fixed anchor `a ∈ A` to lie in `A`. -/
theorem singletonOrderThreeDoubleDestroyer_backwardTranslate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    {a : ℕ} (haA : a ∈ A) :
    ∃ T, ∀ x, T ≤ x →
      DestroysAt (additiveSupportFamily A 3)
        ((({x} : Finset ℕ) : Set ℕ)) (x + x) →
      x - a ∈ A := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N + a + 1, ?_⟩
  intro x hxT hdestroy
  let n := x + x - a
  have hax : a < x := by omega
  have hnN : N ≤ n := by
    dsimp only [n]
    omega
  obtain ⟨E, hER, _hEempty⟩ := hN n hnN
  have hGR : insert a E ∈ additiveSupportFamily A 3 (x + x) := by
    have hlift := insert_mem_additiveSupportFamily_succ haA hER
    have hsum : a + n = x + x := by
      dsimp only [n]
      omega
    simpa [hsum] using hlift
  have hhit := hdestroy (insert a E) hGR
  obtain ⟨z, hzG, hzX⟩ := Set.not_disjoint_iff.mp hhit
  have hzx : z = x := by simpa using hzX
  have hxG : x = a ∨ x ∈ E := by
    simpa [hzx] using hzG
  have hxE : x ∈ E := hxG.resolve_left (Nat.ne_of_lt hax).symm
  have hxle : x ≤ n := by
    dsimp only [n]
    omega
  have hEq := additiveSupportFamily_two_eq_pairSupport_of_mem hER hxE
  have hcompE : n - x ∈ E := by
    rw [hEq]
    simp [pairSupport]
  have hcompA := additiveSupportFamily_supportsIn A 2 n E hER
    (n - x) hcompE
  have hcomp : n - x = x - a := by
    dsimp only [n]
    omega
  exact hcomp ▸ hcompA

/-- A zero-atomic target cannot have any positive backward translate by an
element of `A` still lying in `A`: that translate would give a second
order-two support of the target. -/
theorem zeroAtom_forbids_positiveBackwardTranslate
    {A : Set ℕ} {x a : ℕ}
    (hnormal : ∀ E ∈ additiveSupportFamily A 2 x, E = {x, 0})
    (haA : a ∈ A) (hapos : 0 < a) (hax : a < x) :
    x - a ∉ A := by
  intro hsubA
  have hER : pairSupport x a ∈ additiveSupportFamily A 2 x :=
    pairSupport_mem_additiveSupportFamily
      (Nat.le_of_lt hax) haA hsubA
  have haPair : a ∈ pairSupport x a := by
    simp [pairSupport]
  have haCanonical : a ∈ ({x, 0} : Finset ℕ) := by
    rw [← hnormal (pairSupport x a) hER]
    exact haPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at haCanonical
  omega

/-- The backward-translate obstruction rules out an infinite two-point
order-three destroyer clique on zero-atoms. -/
theorem not_pairwiseOrderThreeDestroyers_of_zeroAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite)
    (hnormal : ∀ x ∈ K, ∀ E ∈ additiveSupportFamily A 2 x,
      E = {x, 0}) :
    ¬ IsPairwiseOrderThreeSumDestroyerSet A K := by
  intro hdestroy
  obtain ⟨a, haA, haPos⟩ := hbasis.infinite.exists_gt 0
  obtain ⟨T, hexceptions⟩ :=
    pairwiseOrderThreeDestroyers_backwardTranslateExceptions_subsingleton
      hbasis hdestroy haA
  let H : Set ℕ := K \ Set.Iio (max T (a + 1))
  have hH : H.Infinite :=
    hK.diff (Set.finite_Iio (max T (a + 1)))
  obtain ⟨x, hxH⟩ := hH.nonempty
  have hH' : (H \ ({x} : Set ℕ)).Infinite :=
    hH.diff (Set.finite_singleton x)
  obtain ⟨y, hyH'⟩ := hH'.nonempty
  have hyH : y ∈ H := hyH'.1
  have hyx : y ≠ x := by simpa using hyH'.2
  have hxT : T ≤ x := by
    have hmax : max T (a + 1) ≤ x := Nat.le_of_not_gt hxH.2
    exact le_trans (le_max_left _ _) hmax
  have hyT : T ≤ y := by
    have hmax : max T (a + 1) ≤ y := Nat.le_of_not_gt hyH.2
    exact le_trans (le_max_left _ _) hmax
  have hax : a < x := by
    have hmax : max T (a + 1) ≤ x := Nat.le_of_not_gt hxH.2
    omega
  have hay : a < y := by
    have hmax : max T (a + 1) ≤ y := Nat.le_of_not_gt hyH.2
    omega
  have hxException : x ∈ {z | z ∈ K ∧ T ≤ z ∧ z - a ∉ A} :=
    ⟨hxH.1, hxT,
      zeroAtom_forbids_positiveBackwardTranslate
        (hnormal x hxH.1) haA haPos hax⟩
  have hyException : y ∈ {z | z ∈ K ∧ T ≤ z ∧ z - a ∉ A} :=
    ⟨hyH.1, hyT,
      zeroAtom_forbids_positiveBackwardTranslate
        (hnormal y hyH.1) haA haPos hay⟩
  exact hyx (hexceptions hyException hxException)

/-- Only finitely many zero-atoms can be singleton order-three destroyers at
their doubles. -/
theorem finite_singletonOrderThreeDoubleDestroyers_of_zeroAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hnormal : ∀ x ∈ K, ∀ E ∈ additiveSupportFamily A 2 x,
      E = {x, 0}) :
    {x | x ∈ K ∧
      DestroysAt (additiveSupportFamily A 3)
        ((({x} : Finset ℕ) : Set ℕ)) (x + x)}.Finite := by
  apply Set.not_infinite.mp
  intro hBad
  obtain ⟨a, haA, haPos⟩ := hbasis.infinite.exists_gt 0
  obtain ⟨T, hback⟩ :=
    singletonOrderThreeDoubleDestroyer_backwardTranslate hbasis haA
  let Bad : Set ℕ := {x | x ∈ K ∧
    DestroysAt (additiveSupportFamily A 3)
      ((({x} : Finset ℕ) : Set ℕ)) (x + x)}
  let H : Set ℕ := Bad \ Set.Iio (max T (a + 1))
  have hH : H.Infinite :=
    hBad.diff (Set.finite_Iio (max T (a + 1)))
  obtain ⟨x, hxH⟩ := hH.nonempty
  have hxBad : x ∈ Bad := hxH.1
  have hxT : T ≤ x := by
    have hmax : max T (a + 1) ≤ x := Nat.le_of_not_gt hxH.2
    exact le_trans (le_max_left _ _) hmax
  have hax : a < x := by
    have hmax : max T (a + 1) ≤ x := Nat.le_of_not_gt hxH.2
    omega
  have hsubA : x - a ∈ A := hback x hxT hxBad.2
  exact
    (zeroAtom_forbids_positiveBackwardTranslate
      (hnormal x hxBad.1) haA haPos hax) hsubA

/-- Every infinite zero-atomic reservoir has an infinite thinning with
simultaneous direct order-three repairs for all sums of two deleted points.
The diagonal bad set is finite, pair Ramsey handles distinct pairs, and the
zero-atom backward-translate obstruction eliminates the destroyer clique. -/
theorem exists_infinite_directRepairs_of_zeroAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite)
    (hnormal : ∀ x ∈ K, ∀ E ∈ additiveSupportFamily A 2 x,
      E = {x, 0}) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasDirectTripleRepairsForDeletedPairs A B := by
  classical
  let Bad : Set ℕ := {x | x ∈ K ∧
    DestroysAt (additiveSupportFamily A 3)
      ((({x} : Finset ℕ) : Set ℕ)) (x + x)}
  have hBadFinite : Bad.Finite :=
    finite_singletonOrderThreeDoubleDestroyers_of_zeroAtoms
      hbasis hnormal
  let K₀ : Set ℕ := K \ Bad
  have hK₀K : K₀ ⊆ K := Set.diff_subset
  have hK₀ : K₀.Infinite := hK.diff hBadFinite
  have hdoubles : HasLocalDirectTripleRepairsForDoubles A K₀ := by
    intro x hxK₀
    have hnot : ¬ DestroysAt (additiveSupportFamily A 3)
        ((({x} : Finset ℕ) : Set ℕ)) (x + x) := by
      intro hdestroy
      exact hxK₀.2 ⟨hxK₀.1, hdestroy⟩
    exact not_destroysAt_iff.mp hnot
  let R : ℕ → ℕ → Prop := fun x y =>
    DestroysAt (additiveSupportFamily A 3)
      ((({x, y} : Finset ℕ) : Set ℕ)) (x + y)
  have hRcomm : Symmetric R := by
    intro x y hxy
    exact orderThreePairSumDestroyer_comm.mp hxy
  obtain ⟨L, hLK₀, hL, hclique⟩ |
      ⟨L, hLK₀, hL, hpairs⟩ :=
    infinite_pairRamsey_nat hK₀ R hRcomm
  · have hnormalL : ∀ x ∈ L,
        ∀ E ∈ additiveSupportFamily A 2 x, E = {x, 0} := by
      intro x hx
      exact hnormal x (hK₀K (hLK₀ hx))
    exact
      (not_pairwiseOrderThreeDestroyers_of_zeroAtoms
        hbasis hL hnormalL hclique).elim
  · have hpairsLocal : HasPairwiseLocalDirectTripleRepairs A L := by
      intro x hx y hy hxy
      exact not_destroysAt_iff.mp (hpairs hx hy hxy)
    have hdoublesL : HasLocalDirectTripleRepairsForDoubles A L := by
      intro x hx
      exact hdoubles x (hLK₀ hx)
    obtain ⟨B, hBL, hB, hrepairs⟩ :=
      exists_infinite_directRepairs_of_localPairAndDoubleRepairs
        hL hpairsLocal hdoublesL
    exact ⟨B, hBL.trans hLK₀ |>.trans hK₀K, hB, hrepairs⟩

/-- The target `x` has a direct order-three representation whose support
does not use `x` itself. -/
def HasSelfAvoidingTripleSupport (A : Set ℕ) (x : ℕ) : Prop :=
  ∃ G ∈ additiveSupportFamily A 3 x, x ∉ G

/-- Every order-two basis eventually gives self-avoiding order-three
supports at all targets.  Fix a positive `d ∈ A`, represent `x - d` by two
elements of `A`, and adjoin `d`.  Every entry is strictly smaller than `x`. -/
theorem eventually_selfAvoidingTripleSupport_of_orderTwoBasis
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ T, ∀ x, T ≤ x → HasSelfAvoidingTripleSupport A x := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨d, hdA, hdPos⟩ := hbasis.infinite.exists_gt 0
  refine ⟨N + d + 1, ?_⟩
  intro x hx
  have hdx : d < x := by omega
  have hNsub : N ≤ x - d := by omega
  obtain ⟨E, hER, _hEempty⟩ := hN (x - d) hNsub
  let G : Finset ℕ := insert d E
  have hGR : G ∈ additiveSupportFamily A 3 x := by
    have hlift := insert_mem_additiveSupportFamily_succ hdA hER
    have hsum : d + (x - d) = x := Nat.add_sub_of_le (Nat.le_of_lt hdx)
    simpa [G, hsum] using hlift
  have hxG : x ∉ G := by
    intro hxmem
    rcases Finset.mem_insert.mp hxmem with hxd | hxE
    · exact (Nat.ne_of_lt hdx hxd.symm).elim
    · have hxle : x ≤ x - d :=
        additiveSupportFamily_supportsBounded A 2 (x - d) E hER x hxE
      omega
  exact ⟨G, hGR, hxG⟩

/-- A triple support at target `x` which is forced to contain `x` can only
be the canonical support `{x, 0}`: all other tuple entries must sum to zero. -/
theorem orderThreeSupport_eq_self_zero_of_not_selfAvoiding
    {A : Set ℕ} {x : ℕ}
    (hatom : ¬ HasSelfAvoidingTripleSupport A x)
    {G : Finset ℕ} (hGR : G ∈ additiveSupportFamily A 3 x) :
    G = {x, 0} := by
  have hxG : x ∈ G := by
    by_contra hxG
    exact hatom ⟨G, hGR, hxG⟩
  obtain ⟨v, _hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hGR
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxG
  have hsum : (v 0).1 + ((v 1).1 + (v 2).1) = x := by
    simpa [Fin.sum_univ_succ] using hvsum
  fin_cases i
  · have hi0 : (v 0).1 = x := by simpa using hi
    have h1 : (v 1).1 = 0 := by omega
    have h2 : (v 2).1 = 0 := by omega
    ext z
    rw [mem_tupleSupport_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨0, hi0⟩
      · exact ⟨1, h1⟩
  · have hi1 : (v 1).1 = x := by simpa using hi
    have h0 : (v 0).1 = 0 := by omega
    have h2 : (v 2).1 = 0 := by omega
    ext z
    rw [mem_tupleSupport_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨1, hi1⟩
      · exact ⟨0, h0⟩
  · have hi2 : (v 2).1 = x := by simpa using hi
    have h0 : (v 0).1 = 0 := by omega
    have h1 : (v 1).1 = 0 := by omega
    ext z
    rw [mem_tupleSupport_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨j, hj⟩
      fin_cases j <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨2, hi2⟩
      · exact ⟨0, h0⟩

/-- Point free-set thinning makes a chosen self-avoiding triple support at
every retained reservoir point avoid the entire thinned deletion. -/
theorem exists_infinite_selfTripleRepairs
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hlocal : ∀ x ∈ K, HasSelfAvoidingTripleSupport A x) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      ∀ x ∈ B, ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B := by
  classical
  let chooseSupport (x : ℕ) : Finset ℕ :=
    if h : HasSelfAvoidingTripleSupport A x then Classical.choose h else ∅
  have hchoose : ∀ x ∈ K,
      chooseSupport x ∈ additiveSupportFamily A 3 x ∧
        x ∉ chooseSupport x := by
    intro x hxK
    have hx := hlocal x hxK
    simp only [chooseSupport, dif_pos hx]
    exact Classical.choose_spec hx
  have hcard : ∀ x ∈ K, (chooseSupport x).card ≤ 3 := by
    intro x hxK
    exact additiveSupportFamily_cardAtMost A 3 x
      (chooseSupport x) (hchoose x hxK).1
  have havoid : ∀ x ∈ K, x ∉ chooseSupport x := by
    intro x hxK
    exact (hchoose x hxK).2
  obtain ⟨B, hBK, hB, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK chooseSupport 3 hcard havoid
  exact ⟨B, hBK, hB, fun x hxB =>
    ⟨chooseSupport x, (hchoose x (hBK hxB)).1, hfree x hxB⟩⟩

/-- Zero-atoms with simultaneous red-red pair repairs split once more.  On
one branch their own targets also have simultaneous blue triple repairs.  On
the other, infinitely many points are canonical atoms at both orders two
and three. -/
theorem zeroAtoms_pairAndSelfRepairs_or_orderThreeAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite)
    (hnormal : ∀ x ∈ K, ∀ E ∈ additiveSupportFamily A 2 x,
      E = {x, 0}) :
    (∃ B, B ⊆ K ∧ B.Infinite ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      ∀ x ∈ B, ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧
        (∀ x ∈ L, ∀ E ∈ additiveSupportFamily A 2 x,
          E = {x, 0}) ∧
        ∀ x ∈ L, ∀ G ∈ additiveSupportFamily A 3 x,
          G = {x, 0} := by
  obtain ⟨B₀, hB₀K, hB₀, hpairRepairs⟩ :=
    exists_infinite_directRepairs_of_zeroAtoms hbasis hK hnormal
  let Good : Set ℕ :=
    {x | x ∈ B₀ ∧ HasSelfAvoidingTripleSupport A x}
  let Atom : Set ℕ :=
    {x | x ∈ B₀ ∧ ¬ HasSelfAvoidingTripleSupport A x}
  by_cases hGood : Good.Infinite
  · left
    obtain ⟨B, hBGood, hB, hselfRepairs⟩ :=
      exists_infinite_selfTripleRepairs hGood (fun x hx => hx.2)
    have hBB₀ : B ⊆ B₀ := fun x hx => (hBGood hx).1
    exact ⟨B, hBB₀.trans hB₀K, hB,
      hpairRepairs.mono hBB₀, hselfRepairs⟩
  · right
    have hAtom : Atom.Infinite := by
      by_contra hnotAtom
      have hfinite : (Good ∪ Atom).Finite :=
        (Set.not_infinite.mp hGood).union
          (Set.not_infinite.mp hnotAtom)
      apply hB₀
      apply hfinite.subset
      intro x hxB₀
      by_cases hx : HasSelfAvoidingTripleSupport A x
      · exact Or.inl ⟨hxB₀, hx⟩
      · exact Or.inr ⟨hxB₀, hx⟩
    have hAtomK : Atom ⊆ K := fun x hx => hB₀K hx.1
    refine ⟨Atom, hAtomK, hAtom, ?_, ?_⟩
    · intro x hx
      exact hnormal x (hAtomK hx)
    · intro x hx G hGR
      exact orderThreeSupport_eq_self_zero_of_not_selfAvoiding
        hx.2 hGR

/-- The order-three-atomic branch above is impossible in an order-two basis,
because sufficiently late targets always have a self-avoiding triple
support. -/
theorem not_infinite_orderThreeAtoms_of_orderTwoBasis
    {A L : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hL : L.Infinite)
    (hnormal : ∀ x ∈ L, ∀ G ∈ additiveSupportFamily A 3 x,
      G = {x, 0}) : False := by
  obtain ⟨T, hself⟩ :=
    eventually_selfAvoidingTripleSupport_of_orderTwoBasis hbasis
  obtain ⟨x, hxL, hxT⟩ := hL.exists_gt T
  obtain ⟨G, hGR, hxG⟩ := hself x (Nat.le_of_lt hxT)
  apply hxG
  rw [hnormal x hxL G hGR]
  simp

/-- Consequently every infinite zero-atomic reservoir has an infinite
thinning on which both all red-red pair sums and every deleted point's own
target have simultaneous surviving order-three repairs. -/
theorem exists_infinite_pairAndSelfTripleRepairs_of_zeroAtoms
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hK : K.Infinite)
    (hnormal : ∀ x ∈ K, ∀ E ∈ additiveSupportFamily A 2 x,
      E = {x, 0}) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      ∀ x ∈ B, ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B := by
  obtain hdone | ⟨L, _hLK, hL, _hnormalTwo, hnormalThree⟩ :=
    zeroAtoms_pairAndSelfRepairs_or_orderThreeAtoms
      hbasis hK hnormal
  · exact hdone
  · exact
      (not_infinite_orderThreeAtoms_of_orderTwoBasis
        hbasis hL hnormalThree).elim

/-- Failure of every infinite order-three deletion is exactly strong
order-three deletion in support-hypergraph form. -/
theorem strongOrderThreeDeletion_of_counterexample
    {A : Set ℕ}
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    StrongInfiniteDeletion (additiveSupportFamily A 3) A := by
  rw [strongInfiniteDeletion_additiveSupportFamily_iff]
  intro B hBA hB N
  have hnot := hcounter B hBA hB
  simp only [IsExactTupleAsymptoticBasis, not_exists, not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  refine ⟨n, hn, ?_⟩
  rintro ⟨v, hv⟩
  exact hnrep v hv

/-- If zero is retained and every red-red pair sum has a direct blue triple
repair, an order-three destroyer forces every order-two support to cross the
red/blue boundary.  An all-blue pair could be padded by zero; an all-red pair
would invoke its direct repair. -/
theorem orderTwoSupports_crossing_of_zero_directRepairs_destroyer
    {A B : Set ℕ} {n : ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hdestroy : DestroysAt (additiveSupportFamily A 3) B n) :
    ∀ E ∈ additiveSupportFamily A 2 n,
      ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  intro E hER
  constructor
  · intro hEB
    have hGR : insert 0 E ∈ additiveSupportFamily A 3 n := by
      have hlift := insert_mem_additiveSupportFamily_succ hzeroA hER
      simpa using hlift
    have hGB : Disjoint ((insert 0 E : Finset ℕ) : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxG hxB
      rcases Finset.mem_insert.mp hxG with rfl | hxE
      · exact hzeroB hxB
      · exact Set.disjoint_left.mp hEB hxE hxB
    exact (hdestroy (insert 0 E) hGR) hGB
  · intro hEsub
    obtain ⟨v, _hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have hv0B : (v 0).1 ∈ B := hEsub
      (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
    have hv1B : (v 1).1 ∈ B := hEsub
      (mem_tupleSupport_iff.mpr ⟨1, rfl⟩)
    have hsum : (v 0).1 + (v 1).1 = n := by
      simpa [Fin.sum_univ_two] using hvsum
    obtain ⟨G, hGR, hGB⟩ :=
      hrepairs (v 0).1 hv0B (v 1).1 hv1B
    rw [hsum] at hGR
    exact (hdestroy G hGR) hGB

/-- If zero and the target are both retained, the tautological pair
zero plus n is wholly retained.  Hence a target at which every pair support
crosses the deletion boundary must lie outside A as soon as it lies
outside the deletion. -/
theorem target_not_mem_of_zero_allPairSupports_crossing
    {A B : Set ℕ} {n : ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hnB : n ∉ B)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 n,
      ¬ Disjoint (E : Set ℕ) B) :
    n ∉ A := by
  intro hnA
  have hER : pairSupport n 0 ∈ additiveSupportFamily A 2 n := by
    simpa using
      (pairSupport_mem_additiveSupportFamily
        (Nat.zero_le n) hzeroA hnA)
  apply hcross (pairSupport n 0) hER
  rw [Set.disjoint_left]
  intro x hxE hxB
  have hx : x = 0 ∨ x = n := by
    simpa [pairSupport] using hxE
  rcases hx with rfl | rfl
  · exact hzeroB hxB
  · exact hnB hxB

/-- Eventually, every target has at least one pair support which is not
genuinely mixed across the deletion boundary: it is either wholly retained
or wholly deleted. -/
def HasEventuallyNoncrossingPairSupport
    (A B : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    ∃ E ∈ additiveSupportFamily A 2 n,
      Disjoint (E : Set ℕ) B ∨ (E : Set ℕ) ⊆ B

/-- This is the exact remaining bridge after direct red-red repairs have
been installed.  A wholly retained pair is padded by the retained zero,
whereas a wholly deleted pair is replaced by its direct retained triple. -/
theorem exactThreeBasis_of_zero_directRepairs_noncrossing
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hnoncross : HasEventuallyNoncrossingPairSupport A B) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  apply hasEventuallySurvivingSupport_additive_iff.mp
  obtain ⟨N, hN⟩ := hnoncross
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨E, hER, hblue | hred⟩ := hN n hn
  · let G : Finset ℕ := insert 0 E
    have hGR : G ∈ additiveSupportFamily A 3 n := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hER)
    have hGB : Disjoint (G : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxG hxB
      rcases Finset.mem_insert.mp hxG with rfl | hxE
      · exact hzeroB hxB
      · exact Set.disjoint_left.mp hblue hxE hxB
    exact ⟨G, hGR, hGB⟩
  · obtain ⟨v, _hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have hv0B : (v 0).1 ∈ B :=
      hred (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
    have hv1B : (v 1).1 ∈ B :=
      hred (mem_tupleSupport_iff.mpr ⟨1, rfl⟩)
    have hsum : (v 0).1 + (v 1).1 = n := by
      simpa [Fin.sum_univ_two] using hvsum
    obtain ⟨G, hGR, hGB⟩ :=
      hrepairs (v 0).1 hv0B (v 1).1 hv1B
    rw [hsum] at hGR
    exact ⟨G, hGR, hGB⟩

/-- A sum of two positive retained elements cannot land in the zero-atomic
part of the deletion: that would be a noncanonical pair representation of
the resulting zero-atom. -/
theorem pairSum_mem_complement_of_positive_zeroAtoms
    {A B : Set ℕ}
    (hnormal : ∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
      E = {b, 0})
    {x y : ℕ}
    (hxC : x ∈ A \ B) (hyC : y ∈ A \ B)
    (hxpos : 0 < x) (hypos : 0 < y)
    (hxyA : x + y ∈ A) :
    x + y ∈ A \ B := by
  refine ⟨hxyA, ?_⟩
  intro hxyB
  have hER : pairSupport (x + y) x ∈
      additiveSupportFamily A 2 (x + y) := by
    simpa using
      (pairSupport_mem_additiveSupportFamily
        (Nat.le_add_right x y) hxC.1 (by simpa using hyC.1))
  have hxPair : x ∈ pairSupport (x + y) x := by
    simp [pairSupport]
  have hxCanonical : x ∈ ({x + y, 0} : Finset ℕ) := by
    rw [← hnormal (x + y) hxyB (pairSupport (x + y) x) hER]
    exact hxPair
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxCanonical
  omega

/-- If four positive retained summands add to a target destroyed by the
deletion, then the sum of the first two cannot lie in A.  Otherwise their
sum is retained by zero-atomicity and compresses the four terms to a
surviving triple. -/
theorem pairSum_not_mem_of_positive_fourSum_destroyer
    {A B : Set ℕ} {n x y z w : ℕ}
    (hnormal : ∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
      E = {b, 0})
    (hxC : x ∈ A \ B) (hyC : y ∈ A \ B)
    (hzC : z ∈ A \ B) (hwC : w ∈ A \ B)
    (hxpos : 0 < x) (hypos : 0 < y)
    (hsum : x + y + z + w = n)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) B n) :
    x + y ∉ A := by
  intro hxyA
  have hxyC : x + y ∈ A \ B :=
    pairSum_mem_complement_of_positive_zeroAtoms
      hnormal hxC hyC hxpos hypos hxyA
  have hnotuple :=
    destroysAt_additiveSupportFamily_iff.mp hdestroy
  apply hnotuple
  refine ⟨![x + y, z, w], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [hxyC, hzC, hwC]
  · simp [Fin.sum_univ_succ]
    omega

/-- A zero-atom with a surviving self repair, when used as the deleted
endpoint of a destroyed mixed sum, produces four positive retained summands
whose every pair sum lies outside A.  This is the precise external-clique
shape forced by the final crossing obstruction. -/
theorem exists_externalFourClique_of_zeroAtom_crossingDestroyer
    {A B : Set ℕ} {n b c : ℕ}
    (hnormal : ∀ d ∈ B, ∀ E ∈ additiveSupportFamily A 2 d,
      E = {d, 0})
    (hbB : b ∈ B)
    (hcC : c ∈ A \ B)
    (hbc : b + c = n)
    (hself : ∃ G ∈ additiveSupportFamily A 3 b,
      Disjoint (G : Set ℕ) B)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) B n) :
    ∃ x y z,
      x ∈ A \ B ∧ y ∈ A \ B ∧ z ∈ A \ B ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < c ∧
      x + y + z = b ∧
      x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
      x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A := by
  obtain ⟨G, hGR, hGB⟩ := hself
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hGR
  let x := (v 0).1
  let y := (v 1).1
  let z := (v 2).1
  have hxC : x ∈ A \ B := by
    refine ⟨hvA 0, ?_⟩
    intro hxB
    exact Set.disjoint_left.mp hGB
      (mem_tupleSupport_iff.mpr ⟨0, rfl⟩) hxB
  have hyC : y ∈ A \ B := by
    refine ⟨hvA 1, ?_⟩
    intro hyB
    exact Set.disjoint_left.mp hGB
      (mem_tupleSupport_iff.mpr ⟨1, rfl⟩) hyB
  have hzC : z ∈ A \ B := by
    refine ⟨hvA 2, ?_⟩
    intro hzB
    exact Set.disjoint_left.mp hGB
      (mem_tupleSupport_iff.mpr ⟨2, rfl⟩) hzB
  have hxyz : x + y + z = b := by
    have hsum' : (v 0).1 + ((v 1).1 + (v 2).1) = b := by
      simpa [Fin.sum_univ_succ] using hvsum
    dsimp only [x, y, z]
    omega
  have hnoSplit : ¬ SplitsIntoTwo (A \ B) b := by
    rintro ⟨p, q, hpC, hqC, hpq⟩
    have hp_le : p ≤ b := by omega
    have hcomp : b - p = q := by omega
    have hER : pairSupport b p ∈
        additiveSupportFamily A 2 b := by
      exact pairSupport_mem_additiveSupportFamily
        hp_le hpC.1 (hcomp ▸ hqC.1)
    have hbPair : b ∈ pairSupport b p := by
      rw [hnormal b hbB (pairSupport b p) hER]
      simp
    have hbpq : b = p ∨ b = q := by
      simpa [pairSupport, hcomp] using hbPair
    rcases hbpq with hbp | hbq
    · exact hpC.2 (hbp ▸ hbB)
    · exact hqC.2 (hbq ▸ hbB)
  have hxpos : 0 < x := by
    by_contra hx
    have hx0 : x = 0 := Nat.eq_zero_of_not_pos hx
    apply hnoSplit
    exact ⟨y, z, hyC, hzC, by omega⟩
  have hypos : 0 < y := by
    by_contra hy
    have hy0 : y = 0 := Nat.eq_zero_of_not_pos hy
    apply hnoSplit
    exact ⟨x, z, hxC, hzC, by omega⟩
  have hzpos : 0 < z := by
    by_contra hz
    have hz0 : z = 0 := Nat.eq_zero_of_not_pos hz
    apply hnoSplit
    exact ⟨x, y, hxC, hyC, by omega⟩
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    have hbn : b = n := by omega
    have hGRn : tupleSupport v ∈
        additiveSupportFamily A 3 n := by
      rw [← hbn]
      exact hGR
    exact (hdestroy (tupleSupport v) hGRn) hGB
  have hxy : x + y ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hxC hyC hzC hcC hxpos hypos (by omega) hdestroy
  have hxz : x + z ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hxC hzC hyC hcC hxpos hzpos (by omega) hdestroy
  have hyz : y + z ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hyC hzC hxC hcC hypos hzpos (by omega) hdestroy
  have hxc : x + c ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hxC hcC hyC hzC hxpos hcpos (by omega) hdestroy
  have hyc : y + c ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hyC hcC hxC hzC hypos hcpos (by omega) hdestroy
  have hzc : z + c ∉ A :=
    pairSum_not_mem_of_positive_fourSum_destroyer
      hnormal hzC hcC hxC hyC hzpos hcpos (by omega) hdestroy
  exact ⟨x, y, z, hxC, hyC, hzC, hxpos, hypos, hzpos, hcpos,
    hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- At a represented target where every pair support crosses, choose its
deleted endpoint and retained endpoint.  A surviving self repair of the
deleted zero-atom then realizes the external four-clique obstruction. -/
theorem exists_externalFourClique_of_repairedCrossingTarget
    {A B : Set ℕ} {n : ℕ}
    (hnormal : ∀ d ∈ B, ∀ E ∈ additiveSupportFamily A 2 d,
      E = {d, 0})
    (hself : ∀ d ∈ B, ∃ G ∈ additiveSupportFamily A 3 d,
      Disjoint (G : Set ℕ) B)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) B n)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 n,
      ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B)
    (hrep : (additiveSupportFamily A 2 n).Nonempty) :
    ∃ b c x y z,
      b ∈ B ∧ c ∈ A \ B ∧ b + c = n ∧
      x ∈ A \ B ∧ y ∈ A \ B ∧ z ∈ A \ B ∧
      0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < c ∧
      x + y + z = b ∧
      x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
      x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A := by
  obtain ⟨E, hER⟩ := hrep
  obtain ⟨b, hbE, hbB⟩ :=
    Set.not_disjoint_iff.mp (hcross E hER).1
  obtain ⟨c, hcE, hcB⟩ :=
    Set.not_subset.mp (hcross E hER).2
  have hbFin : b ∈ E := Finset.mem_coe.mp hbE
  have hcFin : c ∈ E := Finset.mem_coe.mp hcE
  have hEq : E = pairSupport n b :=
    additiveSupportFamily_two_eq_pairSupport_of_mem hER hbFin
  have hble : b ≤ n :=
    additiveSupportFamily_supportsBounded A 2 n E hER b hbFin
  have hcCases : c = b ∨ c = n - b := by
    rw [hEq] at hcFin
    simpa [pairSupport] using hcFin
  have hcb : c ≠ b := by
    intro hcb
    exact hcB (hcb ▸ hbB)
  have hcEq : c = n - b := hcCases.resolve_left hcb
  have hbc : b + c = n := by omega
  have hcA : c ∈ A :=
    additiveSupportFamily_supportsIn A 2 n E hER c
      (Finset.mem_coe.mp hcE)
  obtain ⟨x, y, z, hxC, hyC, hzC, hxpos, hypos, hzpos,
      hcpos, hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩ :=
    exists_externalFourClique_of_zeroAtom_crossingDestroyer
      hnormal hbB ⟨hcA, hcB⟩ hbc (hself b hbB) hdestroy
  exact ⟨b, c, x, y, z, hbB, ⟨hcA, hcB⟩, hbc,
    hxC, hyC, hzC, hxpos, hypos, hzpos, hcpos,
    hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- Under the counterexample assumption, the crossing obstruction above
occurs at arbitrarily large targets. -/
theorem counterexample_forces_late_allCrossingPairSupports
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hBA : B ⊆ A)
    (hB : B.Infinite)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ N, ∃ n, N ≤ n ∧
      ∀ E ∈ additiveSupportFamily A 2 n,
        ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  intro N
  obtain ⟨n, hn, hdestroy⟩ :=
    strongOrderThreeDeletion_of_counterexample hcounter
      B hBA hB N
  exact ⟨n, hn,
    orderTwoSupports_crossing_of_zero_directRepairs_destroyer
      hzeroA hzeroB hrepairs hdestroy⟩

/-- If the deleted points themselves also have surviving triple repairs,
the late crossing targets can be chosen outside the deletion and outside
all red-red pair sums. -/
theorem counterexample_forces_late_crossingSupports_off_repairedTargets
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hBA : B ⊆ A)
    (hB : B.Infinite)
    (hpairRepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hselfRepairs : ∀ x ∈ B,
      ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ N, ∃ n, N ≤ n ∧ n ∉ B ∧
      (∀ x ∈ B, ∀ y ∈ B, n ≠ x + y) ∧
      ∀ E ∈ additiveSupportFamily A 2 n,
        ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  intro N
  obtain ⟨n, hn, hdestroy⟩ :=
    strongOrderThreeDeletion_of_counterexample hcounter
      B hBA hB N
  have hnB : n ∉ B := by
    intro hnB
    obtain ⟨G, hGR, hGB⟩ := hselfRepairs n hnB
    exact (hdestroy G hGR) hGB
  have hnPair : ∀ x ∈ B, ∀ y ∈ B, n ≠ x + y := by
    intro x hx y hy hnxy
    obtain ⟨G, hGR, hGB⟩ := hpairRepairs x hx y hy
    rw [← hnxy] at hGR
    exact (hdestroy G hGR) hGB
  exact ⟨n, hn, hnB, hnPair,
    orderTwoSupports_crossing_of_zero_directRepairs_destroyer
      hzeroA hzeroB hpairRepairs hdestroy⟩

/-- The repaired crossing targets are necessarily external to A: otherwise
the retained tautological support containing zero and n would not cross the
deletion. -/
theorem counterexample_forces_late_externalCrossingSupports_off_repairedTargets
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB : 0 ∉ B)
    (hBA : B ⊆ A)
    (hB : B.Infinite)
    (hpairRepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hselfRepairs : ∀ x ∈ B,
      ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ N, ∃ n, N ≤ n ∧ n ∉ A ∧ n ∉ B ∧
      (∀ x ∈ B, ∀ y ∈ B, n ≠ x + y) ∧
      DestroysAt (additiveSupportFamily A 3) B n ∧
      ∀ E ∈ additiveSupportFamily A 2 n,
        ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  intro N
  obtain ⟨n, hn, hdestroy⟩ :=
    strongOrderThreeDeletion_of_counterexample hcounter
      B hBA hB N
  have hnB : n ∉ B := by
    intro hnB
    obtain ⟨G, hGR, hGB⟩ := hselfRepairs n hnB
    exact (hdestroy G hGR) hGB
  have hnPair : ∀ x ∈ B, ∀ y ∈ B, n ≠ x + y := by
    intro x hx y hy hnxy
    obtain ⟨G, hGR, hGB⟩ := hpairRepairs x hx y hy
    rw [← hnxy] at hGR
    exact (hdestroy G hGR) hGB
  have hcross :=
    orderTwoSupports_crossing_of_zero_directRepairs_destroyer
      hzeroA hzeroB hpairRepairs hdestroy
  have hnA : n ∉ A :=
    target_not_mem_of_zero_allPairSupports_crossing
      hzeroA hzeroB hnB (fun E hER => (hcross E hER).1)
  exact ⟨n, hn, hnA, hnB, hnPair, hdestroy, hcross⟩

/-- An infinite family of singleton destroyers at the doubles is impossible
inside a self-basis deletion reservoir.  Splitting one fixed reservoir point
`d=c+e` and applying the backward-translate lemma twice produces the
surviving triple `{d, x-c, x-e}` at `2*x`. -/
theorem not_infinite_singletonOrderThreeDoubleDestroyers_of_selfBasis
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hdestroy : ∀ x ∈ K,
      DestroysAt (additiveSupportFamily A 3)
        ((({x} : Finset ℕ) : Set ℕ)) (x + x)) : False := by
  classical
  obtain ⟨L, hL⟩ := hself
  obtain ⟨d, hdK, hdL⟩ := hK.exists_gt L
  have hdA : d ∈ A := hB₀A (hKB₀ hdK)
  obtain ⟨v, hvC, hvsum⟩ := hL d (Nat.le_of_lt hdL) hdA
  let c := v 0
  let e := v 1
  have hcC : c ∈ A \ B₀ := hvC 0
  have heC : e ∈ A \ B₀ := hvC 1
  have hce : c + e = d := by
    simpa [c, e, Fin.sum_univ_two] using hvsum
  have hcpos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    have hed : e = d := by omega
    exact heC.2 (hed ▸ hKB₀ hdK)
  have hepos : 0 < e := by
    by_contra he
    have he0 : e = 0 := Nat.eq_zero_of_not_pos he
    have hcd : c = d := by omega
    exact hcC.2 (hcd ▸ hKB₀ hdK)
  obtain ⟨Tc, hbackc⟩ :=
    singletonOrderThreeDoubleDestroyer_backwardTranslate hbasis hcC.1
  obtain ⟨Te, hbacke⟩ :=
    singletonOrderThreeDoubleDestroyer_backwardTranslate hbasis heC.1
  obtain ⟨x, hxK, hxlarge⟩ := hK.exists_gt (max d (max Tc Te))
  have hdltx : d < x := lt_of_le_of_lt (le_max_left _ _) hxlarge
  have hxTc : Tc ≤ x := le_trans
    (le_trans (le_max_left Tc Te) (le_max_right d (max Tc Te)))
    (Nat.le_of_lt hxlarge)
  have hxTe : Te ≤ x := le_trans
    (le_trans (le_max_right Tc Te) (le_max_right d (max Tc Te)))
    (Nat.le_of_lt hxlarge)
  have hxcA : x - c ∈ A := hbackc x hxTc (hdestroy x hxK)
  have hxeA : x - e ∈ A := hbacke x hxTe (hdestroy x hxK)
  let m := (x - c) + (x - e)
  have hpair : pairSupport m (x - c) ∈
      additiveSupportFamily A 2 m := by
    apply pairSupport_mem_additiveSupportFamily (by simp [m]) hxcA
    have hsub : m - (x - c) = x - e := by simp [m]
    simpa [hsub] using hxeA
  let G : Finset ℕ := insert d (pairSupport m (x - c))
  have hGR : G ∈ additiveSupportFamily A 3 (x + x) := by
    have hlift := insert_mem_additiveSupportFamily_succ hdA hpair
    have hsum : d + m = x + x := by
      dsimp only [m]
      omega
    simpa [G, hsum] using hlift
  have hGdisjoint : Disjoint (G : Set ℕ)
      ((({x} : Finset ℕ) : Set ℕ)) := by
    rw [Set.disjoint_left]
    intro z hzG hzX
    have hzx : z = x := by simpa using hzX
    subst z
    have hxG : x = d ∨ x = x - c ∨ x = x - e := by
      have hsub : m - (x - c) = x - e := by simp [m]
      simpa [G, pairSupport, hsub] using hzG
    rcases hxG with hxd | hxc | hxe <;> omega
  exact (hdestroy x hxK G hGR) hGdisjoint

/-- Main completion of the splittable-independent deletion argument once an
infinite self-basis reservoir has been found.  Singleton diagonal destroyers
form only a finite exception.  Pair Ramsey on the remaining reservoir either
gives local repairs for every distinct pair, which the free-set theorems make
simultaneous, or an impossible two-point destroyer clique. -/
theorem exists_infiniteDeletion_threeBasis_of_selfBasisReservoir
    {A B₀ : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hB₀ : B₀.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A) :
    ∃ B, B ⊆ B₀ ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  classical
  let Bad : Set ℕ := {x | x ∈ B₀ ∧
    DestroysAt (additiveSupportFamily A 3)
      ((({x} : Finset ℕ) : Set ℕ)) (x + x)}
  have hBadFinite : Bad.Finite := by
    apply Set.not_infinite.mp
    intro hBad
    exact not_infinite_singletonOrderThreeDoubleDestroyers_of_selfBasis
      hbasis hB₀A hself (fun _ hx => hx.1) hBad (fun _ hx => hx.2)
  let K : Set ℕ := B₀ \ Bad
  have hK : K.Infinite := hB₀.diff hBadFinite
  have hKB₀ : K ⊆ B₀ := Set.diff_subset
  have hdoubles : HasLocalDirectTripleRepairsForDoubles A K := by
    intro x hxK
    have hnotDestroy : ¬ DestroysAt (additiveSupportFamily A 3)
        ((({x} : Finset ℕ) : Set ℕ)) (x + x) := by
      intro hdestroy
      exact hxK.2 ⟨hxK.1, hdestroy⟩
    exact not_destroysAt_iff.mp hnotDestroy
  let R : ℕ → ℕ → Prop := fun x y =>
    DestroysAt (additiveSupportFamily A 3)
      ((({x, y} : Finset ℕ) : Set ℕ)) (x + y)
  have hRcomm : Symmetric R := by
    intro x y hxy
    exact orderThreePairSumDestroyer_comm.mp hxy
  obtain ⟨L, hLK, hL, hclique⟩ | ⟨L, hLK, hL, hpairs⟩ :=
    infinite_pairRamsey_nat hK R hRcomm
  · exact (not_infinite_pairwiseOrderThreeDestroyers_of_selfBasis
      hbasis hB₀A hself (hLK.trans hKB₀) hL hclique).elim
  · have hpairsLocal : HasPairwiseLocalDirectTripleRepairs A L := by
      intro x hx y hy hxy
      exact not_destroysAt_iff.mp (hpairs hx hy hxy)
    have hdoublesL : HasLocalDirectTripleRepairsForDoubles A L := by
      intro x hx
      exact hdoubles x (hLK hx)
    obtain ⟨B, hBL, hB, hthree⟩ :=
      exists_infiniteDeletion_threeBasis_of_localPairAndDoubleRepairs
        hbasis hB₀A hself (hLK.trans hKB₀) hL
        hpairsLocal hdoublesL
    exact ⟨B, hBL.trans hLK |>.trans hKB₀, hB, hthree⟩

/-- When zero is retained, a reservoir whose deleted points split in its
complement is already a self-basis reservoir.  The completed self-basis
theorem therefore supplies the desired order-three deletion. -/
theorem exists_infiniteDeletion_threeBasis_of_zero_splittingReservoir
    {A B₀ : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hB₀ : B₀.Infinite)
    (hsplit : DeletionSplitsIntoComplement A B₀) :
    ∃ B, B ⊆ B₀ ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A :=
    exactTwoBasisAlong_self_of_zero_and_deletedSplits
      hzeroA hzeroB₀ hsplit
  exact exists_infiniteDeletion_threeBasis_of_selfBasisReservoir
    hbasis hB₀A hB₀ hself

/-- Exhaustive reduction after completing the self-basis-reservoir branch.
Relative order-two matching growth along targets in `A` constructs such a
reservoir and hence the desired deletion.  The sole remaining alternative is
a recurrent bounded moving transversal for the pair-support matchings at
targets which themselves lie in `A`. -/
theorem infiniteDeletionThreeBasis_or_boundedMovingPairTransversalsAlongSelf
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      HasBoundedMovingOutsideTransversalsAlong
        (additiveSupportFamily A 2) A A := by
  obtain ⟨F, hFA, hgrowth⟩ | hmoving :=
    exists_finiteCore_outsideMatchingAlong_or_boundedMovingAlong
      (A := A) (S := A) (R := additiveSupportFamily A 2)
      (r := 2) (additiveSupportFamily_supportsIn A 2)
      (additiveSupportFamily_cardAtMost A 2)
  · left
    have hmatches : MatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A 2) F A :=
      matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong hgrowth
    obtain ⟨B₀, hB₀A, hB₀, _hB₀F, hsurvive⟩ :=
      sparseDeletion_of_matchingTendsToInfinityOutsideAlong
        (C := A) (S := A) (R := additiveSupportFamily A 2)
        (F := F) (additiveSupportFamily_supportsBounded A 2)
        hmatches (hbasis.unboundedOutside F)
    have hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A :=
      hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive
    obtain ⟨B, hBB₀, hB, hthree⟩ :=
      exists_infiniteDeletion_threeBasis_of_selfBasisReservoir
        (B₀ := B₀) hbasis hB₀A hB₀ hself
    exact ⟨B, hBB₀.trans hB₀A, hB, hthree⟩
  · exact Or.inr hmoving

/-- The bounded-moving residual already forces a fixed bound on the complete
order-two support family at arbitrarily large targets belonging to `A`.
With empty protected core, every pair support is a nonempty edge of the
outside hypergraph; since the pair supports form a matching, any transversal
has cardinality at least the number of supports. -/
theorem recurrently_bounded_pairSupports_on_self_of_boundedMoving
    {A : Set ℕ}
    (hmoving : HasBoundedMovingOutsideTransversalsAlong
      (additiveSupportFamily A 2) A A) :
    ∃ m, ∀ N, ∃ n, N ≤ n ∧ n ∈ A ∧
      (additiveSupportFamily A 2 n).card ≤ m := by
  obtain ⟨m, hm⟩ := hmoving ∅ (by simp)
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hnA, _hTA, _hTempty, hTcard, htrans⟩ := hm N
  have hdestroy : DestroysAt
      (additiveSupportFamily A 2) (T : Set ℕ) n := by
    intro E hER
    have hEnonempty :=
      additiveSupportFamily_supportsNonempty A (by omega) n E hER
    have hEout : E ∈ outsideSupportHypergraph
        (additiveSupportFamily A 2) ∅ n := by
      apply Finset.mem_erase.mpr
      refine ⟨Finset.nonempty_iff_ne_empty.mp hEnonempty, ?_⟩
      exact Finset.mem_image.mpr ⟨E, hER, by simp⟩
    obtain ⟨x, hx⟩ := htrans E hEout
    have hx' := Finset.mem_inter.mp hx
    exact Set.not_disjoint_iff.mpr
      ⟨x, hx'.1, Finset.mem_coe.mpr hx'.2⟩
  have hsupportCard : (additiveSupportFamily A 2 n).card ≤ T.card :=
    card_supports_le_card_of_matching_of_destroysAt
      (fun E hER =>
        additiveSupportFamily_supportsNonempty A (by omega) n E hER)
      (additiveSupportFamily_two_isMatching A n) hdestroy
  exact ⟨n, hn, hnA, hsupportCard.trans hTcard⟩

/-- Numerically explicit final reduction: either the desired infinite
deletion exists, or the pair-representation function is uniformly bounded
along an unbounded sequence of targets which are themselves elements of the
basis. -/
theorem infiniteDeletionThreeBasis_or_recurrentlyBoundedPairSupportsOnSelf
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      ∃ m, ∀ N, ∃ n, N ≤ n ∧ n ∈ A ∧
        (additiveSupportFamily A 2 n).card ≤ m := by
  obtain hdone | hmoving :=
    infiniteDeletionThreeBasis_or_boundedMovingPairTransversalsAlongSelf
      hbasis
  · exact Or.inl hdone
  · exact Or.inr <|
      recurrently_bounded_pairSupports_on_self_of_boundedMoving hmoving

/-- A concrete positive subclass: if the number of order-two supports tends
to infinity along the targets which lie in `A`, the bounded residual is
impossible, so the desired infinite deletion exists. -/
theorem exists_infiniteDeletion_threeBasis_of_pairSupportsGrowOnSelf
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hgrowth : ∀ m, ∃ N, ∀ n, N ≤ n → n ∈ A →
      m < (additiveSupportFamily A 2 n).card) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain hdone | ⟨m, hbounded⟩ :=
    infiniteDeletionThreeBasis_or_recurrentlyBoundedPairSupportsOnSelf
      hbasis
  · exact hdone
  · obtain ⟨N, hN⟩ := hgrowth m
    obtain ⟨n, hn, hnA, hncard⟩ := hbounded N
    exact (not_lt_of_ge hncard) (hN n hn hnA) |>.elim

/-- Conversely, any genuine order-two counterexample to the desired
successor deletion must exhibit one fixed representation bound along an
unbounded sequence of elements of the basis itself. -/
theorem counterexample_forces_recurrentlyBoundedPairSupportsOnSelf
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ m, ∀ N, ∃ n, N ≤ n ∧ n ∈ A ∧
      (additiveSupportFamily A 2 n).card ≤ m := by
  obtain hdone | hbounded :=
    infiniteDeletionThreeBasis_or_recurrentlyBoundedPairSupportsOnSelf
      hbasis
  · obtain ⟨B, hBA, hB, hthree⟩ := hdone
    exact (hcounter B hBA hB hthree).elim
  · exact hbounded

/-- The recurrent bounded-representation residual can be sharpened using
the point free-set theorem.  Any counterexample has one of two forms:

* there is already an infinite deletion whose every deleted element splits
  into two retained elements; or
* an infinite bounded-representation tail consists entirely of zero-atoms,
  with the unique order-two support `{a, 0}` at every target in the tail.

Thus the remaining work on the splittable-independent route is either to
add pair-independence/complement splitting to the first branch, or to
eliminate the explicit zero-atomic branch by fixed-translate repairs. -/
theorem counterexample_forces_splittingDeletion_or_boundedZeroAtoms
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      DeletionSplitsIntoComplement A B) ∨
      ∃ m, ∃ L, L ⊆ A ∧ L.Infinite ∧ 0 ∈ A ∧
        (∀ a ∈ L, (additiveSupportFamily A 2 a).card ≤ m) ∧
        ∀ a ∈ L, ∀ E ∈ additiveSupportFamily A 2 a,
          E = {a, 0} := by
  obtain ⟨m, hbounded⟩ :=
    counterexample_forces_recurrentlyBoundedPairSupportsOnSelf
      hbasis hcounter
  let K : Set ℕ := {a | a ∈ A ∧
    (additiveSupportFamily A 2 a).card ≤ m}
  have hK : K.Infinite := by
    by_contra hnot
    have hfinite : K.Finite := Set.not_infinite.mp hnot
    obtain ⟨U, hU⟩ := hfinite.bddAbove
    obtain ⟨a, haU, haA, hacard⟩ := hbounded (U + 1)
    have haK : a ∈ K := ⟨haA, hacard⟩
    have hale : a ≤ U := hU haK
    omega
  obtain hsplit | ⟨L, hLK, hL, hzero, hnormal⟩ :=
    infiniteDeletionSplits_or_infiniteZeroAtoms hbasis hK
  · left
    obtain ⟨B, hBK, hB, hsplitB⟩ := hsplit
    exact ⟨B, fun a ha => (hBK ha).1, hB, hsplitB⟩
  · right
    refine ⟨m, L, ?_, hL, hzero, ?_, hnormal⟩
    · intro a haL
      exact (hLK haL).1
    · intro a haL
      exact (hLK haL).2

/-- In a zero-containing basis, the splitting branch is impossible for a
counterexample: remove zero from that deletion reservoir and invoke the
completed self-basis theorem.  Hence a counterexample is forced entirely
into the bounded zero-atomic normal form. -/
theorem counterexample_forces_boundedZeroAtoms_of_zero_mem
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ m, ∃ L, L ⊆ A ∧ L.Infinite ∧ 0 ∈ A ∧
      (∀ a ∈ L, (additiveSupportFamily A 2 a).card ≤ m) ∧
      ∀ a ∈ L, ∀ E ∈ additiveSupportFamily A 2 a,
        E = {a, 0} := by
  obtain ⟨B₀, hB₀A, hB₀, hsplit⟩ |
      ⟨m, L, hLA, hL, hzero, hbounded, hnormal⟩ :=
    counterexample_forces_splittingDeletion_or_boundedZeroAtoms
      hbasis hcounter
  · let B₁ : Set ℕ := B₀ \ ({0} : Set ℕ)
    have hB₁B₀ : B₁ ⊆ B₀ := Set.diff_subset
    have hB₁A : B₁ ⊆ A := hB₁B₀.trans hB₀A
    have hB₁ : B₁.Infinite :=
      hB₀.diff (Set.finite_singleton 0)
    have hzeroB₁ : 0 ∉ B₁ := by simp [B₁]
    have hsplit₁ : DeletionSplitsIntoComplement A B₁ :=
      hsplit.mono hB₁B₀
    obtain ⟨B, hBB₁, hB, hthree⟩ :=
      exists_infiniteDeletion_threeBasis_of_zero_splittingReservoir
        hbasis hzeroA hzeroB₁ hB₁A hB₁ hsplit₁
    exact (hcounter B (hBB₁.trans hB₁A) hB hthree).elim
  · exact ⟨m, L, hLA, hL, hzero, hbounded, hnormal⟩

/-- Fully sharpened zero-normalized residual.  Any counterexample with
`0 ∈ A` has an infinite zero-atomic deletion reservoir `B` such that all
red-red pair sums already possess simultaneous blue triple repairs.  The
only remaining late failures are targets at which every order-two support
crosses between `B` and `A \ B`. -/
theorem counterexample_forces_zeroAtomicCrossingReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      (∀ x ∈ B, ∀ E ∈ additiveSupportFamily A 2 x,
        E = {x, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      ∀ N, ∃ n, N ≤ n ∧
        ∀ E ∈ additiveSupportFamily A 2 n,
          ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  obtain ⟨_m, L, hLA, hL, _hzero, _hbounded, hnormal⟩ :=
    counterexample_forces_boundedZeroAtoms_of_zero_mem
      hbasis hzeroA hcounter
  obtain ⟨B₀, hB₀L, hB₀, hrepairs₀⟩ :=
    exists_infinite_directRepairs_of_zeroAtoms hbasis hL hnormal
  let B : Set ℕ := B₀ \ ({0} : Set ℕ)
  have hBB₀ : B ⊆ B₀ := Set.diff_subset
  have hBA : B ⊆ A := hBB₀.trans (hB₀L.trans hLA)
  have hB : B.Infinite := hB₀.diff (Set.finite_singleton 0)
  have hzeroB : 0 ∉ B := by simp [B]
  have hnormalB : ∀ x ∈ B,
      ∀ E ∈ additiveSupportFamily A 2 x, E = {x, 0} := by
    intro x hx
    exact hnormal x (hB₀L (hBB₀ hx))
  have hrepairs : HasDirectTripleRepairsForDeletedPairs A B :=
    hrepairs₀.mono hBB₀
  have hcrossing :=
    counterexample_forces_late_allCrossingPairSupports
      hzeroA hzeroB hBA hB hrepairs hcounter
  exact ⟨B, hBA, hB, hzeroB, hnormalB, hrepairs, hcrossing⟩

/-- Final refinement of the zero-normalized residual.  Either there is an
infinite zero-atomic reservoir whose own targets and all red-red sums have
simultaneous triple repairs, leaving only genuinely mixed crossing targets;
or infinitely many elements are canonical atoms at both orders two and
three.  The latter is the exact counterexample-shaped branch. -/
theorem counterexample_forces_repairedCrossing_or_orderThreeAtoms
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      (∀ x ∈ B, ∀ E ∈ additiveSupportFamily A 2 x,
        E = {x, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      (∀ x ∈ B, ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B) ∧
      ∀ N, ∃ n, N ≤ n ∧ n ∉ B ∧
        (∀ x ∈ B, ∀ y ∈ B, n ≠ x + y) ∧
        ∀ E ∈ additiveSupportFamily A 2 n,
          ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B) ∨
      ∃ L, L ⊆ A ∧ L.Infinite ∧
        (∀ x ∈ L, ∀ E ∈ additiveSupportFamily A 2 x,
          E = {x, 0}) ∧
        ∀ x ∈ L, ∀ G ∈ additiveSupportFamily A 3 x,
          G = {x, 0} := by
  obtain ⟨_m, K, hKA, hK, _hzero, _hbounded, hnormal⟩ :=
    counterexample_forces_boundedZeroAtoms_of_zero_mem
      hbasis hzeroA hcounter
  obtain ⟨B₀, hB₀K, hB₀, hpairRepairs₀, hselfRepairs₀⟩ |
      ⟨L, hLK, hL, hnormalTwo, hnormalThree⟩ :=
    zeroAtoms_pairAndSelfRepairs_or_orderThreeAtoms
      hbasis hK hnormal
  · left
    let B : Set ℕ := B₀ \ ({0} : Set ℕ)
    have hBB₀ : B ⊆ B₀ := Set.diff_subset
    have hBA : B ⊆ A := hBB₀.trans (hB₀K.trans hKA)
    have hB : B.Infinite := hB₀.diff (Set.finite_singleton 0)
    have hzeroB : 0 ∉ B := by simp [B]
    have hnormalB : ∀ x ∈ B,
        ∀ E ∈ additiveSupportFamily A 2 x, E = {x, 0} := by
      intro x hx
      exact hnormal x (hB₀K (hBB₀ hx))
    have hpairRepairs : HasDirectTripleRepairsForDeletedPairs A B :=
      hpairRepairs₀.mono hBB₀
    have hselfRepairs : ∀ x ∈ B,
        ∃ G ∈ additiveSupportFamily A 3 x,
          Disjoint (G : Set ℕ) B := by
      intro x hx
      obtain ⟨G, hGR, hGB₀⟩ := hselfRepairs₀ x (hBB₀ hx)
      exact ⟨G, hGR, hGB₀.mono_right hBB₀⟩
    have hcrossing :=
      counterexample_forces_late_crossingSupports_off_repairedTargets
        hzeroA hzeroB hBA hB hpairRepairs hselfRepairs hcounter
    exact ⟨B, hBA, hB, hzeroB, hnormalB,
      hpairRepairs, hselfRepairs, hcrossing⟩
  · right
    exact ⟨L, hLK.trans hKA, hL, hnormalTwo, hnormalThree⟩

/-- The order-three-atomic alternative is impossible in an order-two basis,
so the sharpened zero-normalized residual consists solely of repaired mixed
crossing targets.  Thus a counterexample supplies an infinite zero-atomic
deletion reservoir whose own points and all red-red pair sums already have
surviving triple repairs; arbitrarily late failures lie outside both classes,
and every one of their pair supports crosses the deletion boundary. -/
theorem counterexample_forces_repairedCrossingReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ 0 ∉ B ∧
      (∀ x ∈ B, ∀ E ∈ additiveSupportFamily A 2 x,
        E = {x, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      (∀ x ∈ B, ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B) ∧
      ∀ N, ∃ n, N ≤ n ∧ n ∉ A ∧ n ∉ B ∧
        (∀ x ∈ B, ∀ y ∈ B, n ≠ x + y) ∧
        DestroysAt (additiveSupportFamily A 3) B n ∧
        ∀ E ∈ additiveSupportFamily A 2 n,
          ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B := by
  obtain ⟨_m, K, hKA, hK, _hzero, _hbounded, hnormal⟩ :=
    counterexample_forces_boundedZeroAtoms_of_zero_mem
      hbasis hzeroA hcounter
  obtain ⟨B₀, hB₀K, hB₀, hpairRepairs₀, hselfRepairs₀⟩ :=
    exists_infinite_pairAndSelfTripleRepairs_of_zeroAtoms
      hbasis hK hnormal
  let B : Set ℕ := B₀ \ ({0} : Set ℕ)
  have hBB₀ : B ⊆ B₀ := Set.diff_subset
  have hBA : B ⊆ A := hBB₀.trans (hB₀K.trans hKA)
  have hB : B.Infinite := hB₀.diff (Set.finite_singleton 0)
  have hzeroB : 0 ∉ B := by simp [B]
  have hnormalB : ∀ x ∈ B,
      ∀ E ∈ additiveSupportFamily A 2 x, E = {x, 0} := by
    intro x hx
    exact hnormal x (hB₀K (hBB₀ hx))
  have hpairRepairs : HasDirectTripleRepairsForDeletedPairs A B :=
    hpairRepairs₀.mono hBB₀
  have hselfRepairs : ∀ x ∈ B,
      ∃ G ∈ additiveSupportFamily A 3 x,
        Disjoint (G : Set ℕ) B := by
    intro x hx
    obtain ⟨G, hGR, hGB₀⟩ := hselfRepairs₀ x (hBB₀ hx)
    exact ⟨G, hGR, hGB₀.mono_right hBB₀⟩
  have hcrossing :=
    counterexample_forces_late_externalCrossingSupports_off_repairedTargets
      hzeroA hzeroB hBA hB hpairRepairs hselfRepairs hcounter
  exact ⟨B, hBA, hB, hzeroB, hnormalB,
    hpairRepairs, hselfRepairs, hcrossing⟩

/-- Absolute arithmetic form of the surviving obstruction.  A
zero-normalized counterexample forces arbitrarily large external targets
which are sums of four positive elements of A, all six of whose pairwise
sums lie outside A.  Three of the four terms sum to an element b of A whose
only pair support is the canonical one containing b and zero. -/
theorem counterexample_forces_arbitrarilyLate_externalFourCliques
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ N, ∃ n b c x y z,
      N ≤ n ∧ n ∉ A ∧
      b ∈ A ∧ c ∈ A ∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      x + y + z = b ∧ b + c = n ∧
      (∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0}) ∧
      x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
      x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A := by
  obtain ⟨B, hBA, _hB, _hzeroB, hnormal,
      _hpairRepairs, hselfRepairs, hlate⟩ :=
    counterexample_forces_repairedCrossingReservoir
      hbasis hzeroA hcounter
  obtain ⟨R, hR⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro N
  obtain ⟨n, hn, hnA, _hnB, _hnPair, hdestroy, hcross⟩ :=
    hlate (max N R)
  have hnN : N ≤ n := le_trans (le_max_left N R) hn
  have hnR : R ≤ n := le_trans (le_max_right N R) hn
  obtain ⟨E, hER, _hEempty⟩ := hR n hnR
  obtain ⟨b, c, x, y, z, hbB, hcC, hbc,
      hxC, hyC, hzC, hxpos, hypos, hzpos, hcpos,
      hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩ :=
    exists_externalFourClique_of_repairedCrossingTarget
      hnormal hselfRepairs hdestroy hcross ⟨E, hER⟩
  exact ⟨n, b, c, x, y, z, hnN, hnA,
    hBA hbB, hcC.1, hxC.1, hyC.1, hzC.1,
    hcpos, hxpos, hypos, hzpos, hxyz, hbc,
    hnormal b hbB, hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- Hereditary form of the external-clique obstruction.  The reservoir can
be thinned to any infinite subset D, and arbitrarily late bad targets still
produce a fresh zero-atom b in D together with four positive elements of
A minus D whose six pair sums all lie outside A. -/
theorem counterexample_forces_hereditaryExternalFourCliques
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∀ D, D ⊆ B → D.Infinite → ∀ N,
        ∃ n b c x y z,
          N ≤ n ∧ n ∉ A ∧
          b ∈ D ∧
          c ∈ A \ D ∧ x ∈ A \ D ∧
          y ∈ A \ D ∧ z ∈ A \ D ∧
          0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
          x + y + z = b ∧ b + c = n ∧
          (∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0}) ∧
          x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
          x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A := by
  obtain ⟨B, hBA, hB, hzeroB, hnormal,
      hpairRepairs, hselfRepairs, _hlate⟩ :=
    counterexample_forces_repairedCrossingReservoir
      hbasis hzeroA hcounter
  obtain ⟨R, hR⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨B, hBA, hB, ?_⟩
  intro D hDB hD N
  have hDA : D ⊆ A := hDB.trans hBA
  have hzeroD : 0 ∉ D := fun h0D => hzeroB (hDB h0D)
  have hnormalD : ∀ d ∈ D,
      ∀ E ∈ additiveSupportFamily A 2 d, E = {d, 0} := by
    intro d hd
    exact hnormal d (hDB hd)
  have hpairD : HasDirectTripleRepairsForDeletedPairs A D :=
    hpairRepairs.mono hDB
  have hselfD : ∀ d ∈ D,
      ∃ G ∈ additiveSupportFamily A 3 d,
        Disjoint (G : Set ℕ) D := by
    intro d hd
    obtain ⟨G, hGR, hGB⟩ := hselfRepairs d (hDB hd)
    exact ⟨G, hGR, hGB.mono_right hDB⟩
  obtain ⟨n, hn, hnA, _hnD, _hnPair, hdestroy, hcross⟩ :=
    counterexample_forces_late_externalCrossingSupports_off_repairedTargets
      hzeroA hzeroD hDA hD hpairD hselfD hcounter (max N R)
  have hnN : N ≤ n := le_trans (le_max_left N R) hn
  have hnR : R ≤ n := le_trans (le_max_right N R) hn
  obtain ⟨E, hER, _hEempty⟩ := hR n hnR
  obtain ⟨b, c, x, y, z, hbD, hcD, hbc,
      hxD, hyD, hzD, hxpos, hypos, hzpos, hcpos,
      hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩ :=
    exists_externalFourClique_of_repairedCrossingTarget
      hnormalD hselfD hdestroy hcross ⟨E, hER⟩
  exact ⟨n, b, c, x, y, z, hnN, hnA, hbD,
    hcD, hxD, hyD, hzD, hcpos, hxpos, hypos, hzpos,
    hxyz, hbc, hnormalD b hbD,
    hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- An intrinsic zero-atom obstruction: b is the sum of three positive
elements of A which, together with a fourth positive element, form a clique
in the graph whose edges are pairs with sum outside A. -/
def HasExternalFourCliqueAtAtom (A : Set ℕ) (b : ℕ) : Prop :=
  ∃ c x y z,
    c ∈ A ∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
    c ≠ b ∧
    0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y + z = b ∧
    x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
    x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A

structure ExternalFourCliqueWitness (A : Set ℕ) (b : ℕ) where
  c : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  c_mem : c ∈ A
  x_mem : x ∈ A
  y_mem : y ∈ A
  z_mem : z ∈ A
  c_ne_atom : c ≠ b
  c_pos : 0 < c
  x_pos : 0 < x
  y_pos : 0 < y
  z_pos : 0 < z
  sum_atom : x + y + z = b
  xy_external : x + y ∉ A
  xz_external : x + z ∉ A
  yz_external : y + z ∉ A
  xc_external : x + c ∉ A
  yc_external : y + c ∉ A
  zc_external : z + c ∉ A

namespace ExternalFourCliqueWitness

def vertices {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) : Finset ℕ :=
  {w.c, w.x, w.y, w.z}

/-- The three vertices which repair the atom itself, excluding the external
complementary vertex `c`. -/
def repairVertices {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) : Finset ℕ :=
  {w.x, w.y, w.z}

theorem repairVertices_card_le_three
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    w.repairVertices.card ≤ 3 :=
  Finset.card_le_three

theorem repairVertices_subset_vertices
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    w.repairVertices ⊆ w.vertices := by
  intro a ha
  simp only [repairVertices, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> simp [vertices]

theorem repairVertices_subset
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    (w.repairVertices : Set ℕ) ⊆ A := by
  intro a ha
  simp only [repairVertices, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact w.x_mem
  · exact w.y_mem
  · exact w.z_mem

theorem repairVertex_lt_atom
    {A : Set ℕ} {b p : ℕ}
    (w : ExternalFourCliqueWitness A b)
    (hp : p ∈ w.repairVertices) :
    p < b := by
  simp only [repairVertices, Finset.mem_insert, Finset.mem_singleton] at hp
  have hsum := w.sum_atom
  change w.x + w.y + w.z = b at hsum
  have hx := w.x_pos
  have hy := w.y_pos
  have hz := w.z_pos
  rcases hp with rfl | rfl | rfl <;> omega

theorem repairVertices_sdiff_nonempty_of_large
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) (R : Finset ℕ)
    (hlarge : 3 * R.sum id < b) :
    (w.repairVertices \ R).Nonempty := by
  rw [Finset.sdiff_nonempty]
  intro hsub
  have hxR : w.x ∈ R := hsub (by simp [repairVertices])
  have hyR : w.y ∈ R := hsub (by simp [repairVertices])
  have hzR : w.z ∈ R := hsub (by simp [repairVertices])
  have hxle : w.x ≤ R.sum id :=
    Finset.single_le_sum (s := R) (f := id)
      (fun _ _ => Nat.zero_le _) hxR
  have hyle : w.y ≤ R.sum id :=
    Finset.single_le_sum (s := R) (f := id)
      (fun _ _ => Nat.zero_le _) hyR
  have hzle : w.z ≤ R.sum id :=
    Finset.single_le_sum (s := R) (f := id)
      (fun _ _ => Nat.zero_le _) hzR
  have hsum := w.sum_atom
  change w.x + w.y + w.z = b at hsum
  omega

theorem vertices_card_le_four
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    w.vertices.card ≤ 4 :=
  Finset.card_le_four

theorem vertices_subset
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    (w.vertices : Set ℕ) ⊆ A := by
  intro q hq
  simp only [vertices, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact w.c_mem
  · exact w.x_mem
  · exact w.y_mem
  · exact w.z_mem

theorem atom_not_mem_vertices
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    b ∉ w.vertices := by
  simp only [vertices, Finset.mem_insert, Finset.mem_singleton]
  intro h
  rcases h with hbc | hbx | hby | hbz
  · exact w.c_ne_atom hbc.symm
  · have hsum := w.sum_atom
    have heq : w.x + w.y + w.z = w.x := hsum.trans hbx
    have hypos := w.y_pos
    have hzpos := w.z_pos
    omega
  · have hsum := w.sum_atom
    have heq : w.x + w.y + w.z = w.y := hsum.trans hby
    have hxpos := w.x_pos
    have hzpos := w.z_pos
    omega
  · have hsum := w.sum_atom
    have heq : w.x + w.y + w.z = w.z := hsum.trans hbz
    have hxpos := w.x_pos
    have hypos := w.y_pos
    omega

theorem atom_pos
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    0 < b := by
  have hsum := w.sum_atom
  change w.x + w.y + w.z = b at hsum
  have hx := w.x_pos
  omega

theorem zero_not_mem_vertices
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    0 ∉ w.vertices := by
  simp only [vertices, Finset.mem_insert, Finset.mem_singleton]
  intro h
  rcases h with hc | hx | hy | hz
  · exact (Nat.ne_of_gt w.c_pos) hc.symm
  · exact (Nat.ne_of_gt w.x_pos) hx.symm
  · exact (Nat.ne_of_gt w.y_pos) hy.symm
  · exact (Nat.ne_of_gt w.z_pos) hz.symm

/-- The three summands stored in an external four-clique witness give a
surviving order-three support of the atom itself. -/
theorem repairSupport_mem
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    insert w.x (pairSupport (w.y + w.z) w.y) ∈
      additiveSupportFamily A 3 b := by
  have hpair : pairSupport (w.y + w.z) w.y ∈
      additiveSupportFamily A 2 (w.y + w.z) := by
    apply pairSupport_mem_additiveSupportFamily (by omega) w.y_mem
    simpa using w.z_mem
  have hlift := insert_mem_additiveSupportFamily_succ w.x_mem hpair
  have hsum : w.x + (w.y + w.z) = b := by
    have hsum' := w.sum_atom
    change w.x + w.y + w.z = b at hsum'
    omega
  simpa [hsum] using hlift

theorem repairSupport_subset_vertices
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    insert w.x (pairSupport (w.y + w.z) w.y) ⊆ w.vertices := by
  intro a ha
  simp only [Finset.mem_insert, pairSupport, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | ha
  · simp [vertices]
  · simp [vertices]
  · have hsub : w.y + w.z - w.y = w.z := by omega
    rw [hsub] at ha
    subst a
    simp [vertices]

theorem repairSupport_subset_repairVertices
    {A : Set ℕ} {b : ℕ}
    (w : ExternalFourCliqueWitness A b) :
    insert w.x (pairSupport (w.y + w.z) w.y) ⊆
      w.repairVertices := by
  intro a ha
  simp only [Finset.mem_insert, pairSupport, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | ha
  · simp [repairVertices]
  · simp [repairVertices]
  · have hsub : w.y + w.z - w.y = w.z := by omega
    rw [hsub] at ha
    subst a
    simp [repairVertices]

end ExternalFourCliqueWitness

theorem hasExternalFourCliqueAtAtom_iff_nonempty
    {A : Set ℕ} {b : ℕ} :
    HasExternalFourCliqueAtAtom A b ↔
      Nonempty (ExternalFourCliqueWitness A b) := by
  constructor
  · rintro ⟨c, x, y, z, hcA, hxA, hyA, hzA, hcb,
      hcpos, hxpos, hypos, hzpos, hxyz,
      hxy, hxz, hyz, hxc, hyc, hzc⟩
    exact ⟨{
      c := c
      x := x
      y := y
      z := z
      c_mem := hcA
      x_mem := hxA
      y_mem := hyA
      z_mem := hzA
      c_ne_atom := hcb
      c_pos := hcpos
      x_pos := hxpos
      y_pos := hypos
      z_pos := hzpos
      sum_atom := hxyz
      xy_external := hxy
      xz_external := hxz
      yz_external := hyz
      xc_external := hxc
      yc_external := hyc
      zc_external := hzc
    }⟩
  · rintro ⟨w⟩
    exact ⟨w.c, w.x, w.y, w.z,
      w.c_mem, w.x_mem, w.y_mem, w.z_mem, w.c_ne_atom,
      w.c_pos, w.x_pos, w.y_pos, w.z_pos, w.sum_atom,
      w.xy_external, w.xz_external, w.yz_external,
      w.xc_external, w.yc_external, w.zc_external⟩

/-- The simultaneous version in which all four clique vertices are retained
outside a proposed deletion L. -/
def HasExternalFourCliqueAtAtomAvoiding
    (A L : Set ℕ) (b : ℕ) : Prop :=
  ∃ c x y z,
    c ∈ A \ L ∧ x ∈ A \ L ∧ y ∈ A \ L ∧ z ∈ A \ L ∧
    c ≠ b ∧
    0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
    x + y + z = b ∧
    x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
    x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A

theorem HasExternalFourCliqueAtAtomAvoiding.mono
    {A L L' : Set ℕ} {b : ℕ}
    (h : HasExternalFourCliqueAtAtomAvoiding A L b)
    (hL'L : L' ⊆ L) :
    HasExternalFourCliqueAtAtomAvoiding A L' b := by
  obtain ⟨c, x, y, z, hc, hx, hy, hz, hcb,
      hcpos, hxpos, hypos, hzpos, hxyz,
      hxy, hxz, hyz, hxc, hyc, hzc⟩ := h
  exact ⟨c, x, y, z,
    ⟨hc.1, fun hcL' => hc.2 (hL'L hcL')⟩,
    ⟨hx.1, fun hxL' => hx.2 (hL'L hxL')⟩,
    ⟨hy.1, fun hyL' => hy.2 (hL'L hyL')⟩,
    ⟨hz.1, fun hzL' => hz.2 (hL'L hzL')⟩,
    hcb, hcpos, hxpos, hypos, hzpos, hxyz,
    hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- Bounded point-map thinning makes the four clique witnesses simultaneous:
an infinite family of clique atoms has an infinite subset L for which every
chosen atom's four witness vertices all avoid L. -/
theorem exists_infinite_externalFourCliqueAtoms_avoiding
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hclique : ∀ b ∈ K, HasExternalFourCliqueAtAtom A b) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L, HasExternalFourCliqueAtAtomAvoiding A L b := by
  classical
  have hw : ∀ b : K, ∃ c x y z,
      c ∈ A ∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      c ≠ b.1 ∧
      0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      x + y + z = b.1 ∧
      x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
      x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A := by
    intro b
    exact hclique b.1 b.2
  choose c x y z hdata using hw
  let f : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ K then
      {c ⟨b, hb⟩, x ⟨b, hb⟩, y ⟨b, hb⟩, z ⟨b, hb⟩}
    else ∅
  have hcard : ∀ b ∈ K, (f b).card ≤ 4 := by
    intro b hb
    simp only [f, dif_pos hb]
    exact Finset.card_le_four
  have hself : ∀ b ∈ K, b ∉ f b := by
    intro b hb
    obtain ⟨_hcA, _hxA, _hyA, _hzA, hcb,
        _hcpos, hxpos, hypos, hzpos, hxyz,
        _hxy, _hxz, _hyz, _hxc, _hyc, _hzc⟩ :=
      hdata ⟨b, hb⟩
    change c ⟨b, hb⟩ ≠ b at hcb
    change x ⟨b, hb⟩ + y ⟨b, hb⟩ + z ⟨b, hb⟩ = b at hxyz
    simp only [f, dif_pos hb, Finset.mem_insert, Finset.mem_singleton]
    intro hmem
    rcases hmem with hbc | hbx | hby | hbz
    · exact hcb hbc.symm
    · omega
    · omega
    · omega
  obtain ⟨L, hLK, hL, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK f 4 hcard hself
  refine ⟨L, hLK, hL, ?_⟩
  intro b hbL
  have hbK : b ∈ K := hLK hbL
  obtain ⟨hcA, hxA, hyA, hzA, hcb,
      hcpos, hxpos, hypos, hzpos, hxyz,
      hxy, hxz, hyz, hxc, hyc, hzc⟩ :=
    hdata ⟨b, hbK⟩
  have hdisj : Disjoint
      (({c ⟨b, hbK⟩, x ⟨b, hbK⟩,
        y ⟨b, hbK⟩, z ⟨b, hbK⟩} : Finset ℕ) : Set ℕ) L := by
    simpa [f, hbK] using hfree b hbL
  have hcL : c ⟨b, hbK⟩ ∉ L := by
    intro hcL
    exact Set.disjoint_left.mp hdisj (by simp) hcL
  have hxL : x ⟨b, hbK⟩ ∉ L := by
    intro hxL
    exact Set.disjoint_left.mp hdisj (by simp) hxL
  have hyL : y ⟨b, hbK⟩ ∉ L := by
    intro hyL
    exact Set.disjoint_left.mp hdisj (by simp) hyL
  have hzL : z ⟨b, hbK⟩ ∉ L := by
    intro hzL
    exact Set.disjoint_left.mp hdisj (by simp) hzL
  exact ⟨c ⟨b, hbK⟩, x ⟨b, hbK⟩,
    y ⟨b, hbK⟩, z ⟨b, hbK⟩,
    ⟨hcA, hcL⟩, ⟨hxA, hxL⟩, ⟨hyA, hyL⟩, ⟨hzA, hzL⟩,
    hcb, hcpos, hxpos, hypos, hzpos, hxyz,
    hxy, hxz, hyz, hxc, hyc, hzc⟩

/-- Sunflower refinement of the simultaneous clique thinning.  The chosen
witness vertex sets have one fixed intersection root; after removing that
root their nonempty petals are pairwise disjoint, and every whole witness set
avoids the selected atoms. -/
theorem exists_infinite_externalFourCliqueSunflower
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hclique : ∀ b ∈ K, HasExternalFourCliqueAtAtom A b) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
        (∀ b ∈ L, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ L, Disjoint (f b : Set ℕ) L) ∧
        (∀ b ∈ L, (f b \ R).Nonempty) ∧
        ∀ b ∈ L, ∀ d ∈ L, b ≠ d →
          Disjoint (f b \ R) (f d \ R) := by
  classical
  let wK : (b : K) → ExternalFourCliqueWitness A b.1 :=
    fun b => Classical.choice <|
      hasExternalFourCliqueAtAtom_iff_nonempty.mp
        (hclique b.1 b.2)
  let f : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ K then (wK ⟨b, hb⟩).vertices else ∅
  have hcard : ∀ b ∈ K, (f b).card ≤ 4 := by
    intro b hb
    simp only [f, dif_pos hb]
    exact (wK ⟨b, hb⟩).vertices_card_le_four
  have hself : ∀ b ∈ K, b ∉ f b := by
    intro b hb
    simp only [f, dif_pos hb]
    exact (wK ⟨b, hb⟩).atom_not_mem_vertices
  obtain ⟨L₀, hL₀K, hL₀, R, hdelta⟩ :=
    exists_infinite_deltaSystem_of_bounded_pointMap
      hK f 4 hcard
  have hcard₀ : ∀ b ∈ L₀, (f b).card ≤ 4 := by
    intro b hb
    exact hcard b (hL₀K hb)
  have hself₀ : ∀ b ∈ L₀, b ∉ f b := by
    intro b hb
    exact hself b (hL₀K hb)
  obtain ⟨L₁, hL₁L₀, hL₁, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hL₀ f 4 hcard₀ hself₀
  let EmptyPetal : Set ℕ :=
    {b | b ∈ L₁ ∧ f b \ R = ∅}
  have hEmptyFinite : EmptyPetal.Finite := by
    apply (Set.finite_Iic (3 * R.sum id)).subset
    intro b hb
    have hbL₀ : b ∈ L₀ := hL₁L₀ hb.1
    have hbK : b ∈ K := hL₀K hbL₀
    let w := wK ⟨b, hbK⟩
    have hfw : f b = w.vertices := by
      simp [f, hbK, w]
    have hsub : f b ⊆ R :=
      Finset.sdiff_eq_empty_iff_subset.mp hb.2
    have hxR : w.x ∈ R := by
      apply hsub
      rw [hfw]
      simp [ExternalFourCliqueWitness.vertices]
    have hyR : w.y ∈ R := by
      apply hsub
      rw [hfw]
      simp [ExternalFourCliqueWitness.vertices]
    have hzR : w.z ∈ R := by
      apply hsub
      rw [hfw]
      simp [ExternalFourCliqueWitness.vertices]
    have hxle : w.x ≤ R.sum id :=
      Finset.single_le_sum (s := R) (f := id)
        (fun _ _ => Nat.zero_le _) hxR
    have hyle : w.y ≤ R.sum id :=
      Finset.single_le_sum (s := R) (f := id)
        (fun _ _ => Nat.zero_le _) hyR
    have hzle : w.z ≤ R.sum id :=
      Finset.single_le_sum (s := R) (f := id)
        (fun _ _ => Nat.zero_le _) hzR
    have hsum := w.sum_atom
    change w.x + w.y + w.z = b at hsum
    have hle :
        w.x + w.y + w.z ≤
          R.sum id + R.sum id + R.sum id :=
      Nat.add_le_add (Nat.add_le_add hxle hyle) hzle
    change b ≤ 3 * R.sum id
    omega
  let L : Set ℕ := L₁ \ EmptyPetal
  have hLL₁ : L ⊆ L₁ := Set.diff_subset
  have hL : L.Infinite := hL₁.diff hEmptyFinite
  refine ⟨L, hLL₁.trans (hL₁L₀.trans hL₀K), hL, R, f,
    ?_, ?_, ?_, ?_⟩
  · intro b hbL
    have hbK : b ∈ K :=
      hL₀K (hL₁L₀ (hLL₁ hbL))
    exact ⟨wK ⟨b, hbK⟩, by simp [f, hbK]⟩
  · intro b hbL
    exact (hfree b (hLL₁ hbL)).mono_right hLL₁
  · intro b hbL
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hbL.2 ⟨hbL.1, hempty⟩
  · intro b hbL d hdL hbd
    rw [Finset.disjoint_left]
    intro q hqb hqd
    have hqInter : q ∈ f b ∩ f d := by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hqb).1,
          (Finset.mem_sdiff.mp hqd).1⟩
    have hqR : q ∈ R := by
      rw [← hdelta b (hL₁L₀ (hLL₁ hbL))
        d (hL₁L₀ (hLL₁ hdL)) hbd]
      exact hqInter
    exact (Finset.mem_sdiff.mp hqb).2 hqR

/-- The petals can be chosen from the three actual repair summands and made
self-repairing.  After discarding the bounded atoms, each witness has a
repair vertex outside the fixed sunflower root.  These chosen vertices are
pairwise distinct, hence eventually large enough to admit self-avoiding
triple supports.  A final bounded point-map thinning makes all those supports
simultaneously avoid the thinned atom set. -/
theorem exists_infinite_selfRepaired_repairPetals
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB : B.Infinite)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R)) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ p : ℕ → ℕ, ∃ g : ℕ → Finset ℕ,
        (∀ b ∈ L, p b ∈ f b \ R ∧ p b < b) ∧
        ∀ b ∈ L,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧
          Disjoint (g b : Set ℕ) L ∧
          ∀ d ∈ L, p d ∉ g b := by
  classical
  obtain ⟨T, hselfAvoid⟩ :=
    eventually_selfAvoidingTripleSupport_of_orderTwoBasis hbasis
  let B₀ : Set ℕ := B \ Set.Iic (3 * R.sum id)
  have hB₀ : B₀.Infinite := hB.diff (Set.finite_Iic _)
  have hpExists : ∀ b : B₀, ∃ p,
      p ∈ f b.1 \ R ∧ p < b.1 := by
    intro b
    obtain ⟨w, hfw⟩ := hwitness b.1 b.2.1
    have hlarge : 3 * R.sum id < b.1 := by
      have hbNotLe : ¬ b.1 ≤ 3 * R.sum id := by
        simpa using b.2.2
      omega
    obtain ⟨p, hpRepair⟩ :=
      w.repairVertices_sdiff_nonempty_of_large R hlarge
    have hpRepair' := Finset.mem_sdiff.mp hpRepair
    refine ⟨p, ?_, w.repairVertex_lt_atom hpRepair'.1⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hpRepair'.2⟩
    rw [hfw]
    exact w.repairVertices_subset_vertices hpRepair'.1
  choose petal hpetal hpetalLt using hpExists
  let p : ℕ → ℕ := fun b =>
    if hb : b ∈ B₀ then petal ⟨b, hb⟩ else 0
  have hpPetal : ∀ b ∈ B₀, p b ∈ f b \ R := by
    intro b hb
    simpa [p, hb] using hpetal ⟨b, hb⟩
  have hpLt : ∀ b ∈ B₀, p b < b := by
    intro b hb
    simpa [p, hb] using hpetalLt ⟨b, hb⟩
  have hpInj : Set.InjOn p B₀ := by
    intro b hb d hd hpd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hpetalDisjoint b hb.1 d hd.1 hbd)
      (hpPetal b hb) (hpd ▸ hpPetal d hd)
  let Low : Set ℕ := {b | b ∈ B₀ ∧ p b < T}
  have hLowFinite : Low.Finite := by
    apply Set.Finite.of_finite_image (f := p)
    · apply (Set.finite_Iio T).subset
      rintro y ⟨b, hbLow, rfl⟩
      exact hbLow.2
    · exact hpInj.mono (fun _ hb => hb.1)
  let K : Set ℕ := B₀ \ Low
  have hK : K.Infinite := hB₀.diff hLowFinite
  have hKB₀ : K ⊆ B₀ := Set.diff_subset
  have hpLarge : ∀ b ∈ K, T ≤ p b := by
    intro b hb
    by_contra hnot
    exact hb.2 ⟨hb.1, Nat.lt_of_not_ge hnot⟩
  have hgExists : ∀ b : K, ∃ G,
      G ∈ additiveSupportFamily A 3 (p b.1) ∧ p b.1 ∉ G := by
    intro b
    exact hselfAvoid (p b.1) (hpLarge b.1 b.2)
  choose repair hrepairR hrepairSelf using hgExists
  let g : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ K then repair ⟨b, hb⟩ else ∅
  have hgR : ∀ b ∈ K,
      g b ∈ additiveSupportFamily A 3 (p b) := by
    intro b hb
    simpa [g, hb] using hrepairR ⟨b, hb⟩
  have hgSelf : ∀ b ∈ K, p b ∉ g b := by
    intro b hb
    simpa [g, hb] using hrepairSelf ⟨b, hb⟩
  have hgCard : ∀ b ∈ K, (g b).card ≤ 3 := by
    intro b hb
    exact additiveSupportFamily_cardAtMost A 3
      (p b) (g b) (hgR b hb)
  have hbNotG : ∀ b ∈ K, b ∉ g b := by
    intro b hb hbG
    have hble : b ≤ p b :=
      additiveSupportFamily_supportsBounded A 3
        (p b) (g b) (hgR b hb) b hbG
    have hpblt : p b < b := hpLt b (hKB₀ hb)
    omega
  let HasOwner : ℕ → Prop := fun x => ∃ d ∈ K, p d = x
  let owner : ℕ → ℕ := fun x =>
    if hx : HasOwner x then Classical.choose hx else 0
  have hownerSpec : ∀ x, HasOwner x →
      owner x ∈ K ∧ p (owner x) = x := by
    intro x hx
    simp only [owner, dif_pos hx]
    exact Classical.choose_spec hx
  let collision : ℕ → Finset ℕ := fun b =>
    ((g b).filter HasOwner).image owner
  have hcollisionCard : ∀ b ∈ K, (collision b).card ≤ 3 := by
    intro b hb
    calc
      (collision b).card ≤ ((g b).filter HasOwner).card :=
        Finset.card_image_le
      _ ≤ (g b).card := Finset.card_filter_le _ _
      _ ≤ 3 := hgCard b hb
  have hcollisionMem : ∀ b, ∀ d ∈ K, p d ∈ g b →
      d ∈ collision b := by
    intro b d hd hpdG
    have howned : HasOwner (p d) := ⟨d, hd, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨p d, Finset.mem_filter.mpr ⟨hpdG, howned⟩, ?_⟩
    have hspec := hownerSpec (p d) howned
    exact hpInj (hKB₀ hspec.1) (hKB₀ hd) hspec.2
  have hbNotCollision : ∀ b ∈ K, b ∉ collision b := by
    intro b hb hbCollision
    obtain ⟨x, hxFilter, hownerb⟩ :=
      Finset.mem_image.mp hbCollision
    have hxG := (Finset.mem_filter.mp hxFilter).1
    have hxOwned := (Finset.mem_filter.mp hxFilter).2
    have hspec := hownerSpec x hxOwned
    have hpbx : p b = x := by
      rw [← hownerb]
      exact hspec.2
    exact hgSelf b hb (hpbx ▸ hxG)
  let avoidMap : ℕ → Finset ℕ := fun b => g b ∪ collision b
  have hAvoidCard : ∀ b ∈ K, (avoidMap b).card ≤ 6 := by
    intro b hb
    calc
      (avoidMap b).card ≤ (g b).card + (collision b).card :=
        by simpa [avoidMap] using
          (Finset.card_union_le (g b) (collision b))
      _ ≤ 3 + 3 := Nat.add_le_add (hgCard b hb)
        (hcollisionCard b hb)
      _ = 6 := by omega
  have hbNotAvoid : ∀ b ∈ K, b ∉ avoidMap b := by
    intro b hb hbAvoid
    rcases Finset.mem_union.mp hbAvoid with hbG | hbCollision
    · exact hbNotG b hb hbG
    · exact hbNotCollision b hb hbCollision
  obtain ⟨L, hLK, hL, hAvoidFree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK avoidMap 6 hAvoidCard hbNotAvoid
  refine ⟨L, hLK.trans (hKB₀.trans Set.diff_subset), hL,
    p, g, ?_, ?_⟩
  · intro b hb
    exact ⟨hpPetal b (hKB₀ (hLK hb)),
      hpLt b (hKB₀ (hLK hb))⟩
  · intro b hb
    have hgFree : Disjoint (g b : Set ℕ) L := by
      apply (hAvoidFree b hb).mono_left
      intro x hxG
      exact Finset.mem_union_left _ (Finset.mem_coe.mp hxG)
    refine ⟨hgR b (hLK hb), hgSelf b (hLK hb), hgFree, ?_⟩
    intro d hd hpG
    apply Set.disjoint_left.mp (hAvoidFree b hb)
      (Finset.mem_union_right _
        (hcollisionMem b d (hLK hd) hpG)) hd

/-- Any sequence of pairwise-disjoint nonempty finite cells contained in A
can be completed to a finite-block partition of all of A while retaining
each cell in its corresponding block. -/
theorem exists_finiteBlockPartition_extending_disjointCells
    {A : Set ℕ} {cell : ℕ → Finset ℕ}
    (hcellA : ∀ i, (cell i : Set ℕ) ⊆ A)
    (hcellNonempty : ∀ i, (cell i).Nonempty)
    (hcellDisjoint : Pairwise fun i j =>
      Disjoint (cell i) (cell j)) :
    ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      ∀ i, cell i ⊆ F i := by
  let H : SupportFamily := fun i => {cell i}
  let S : EscapingTransversalSequence H A := {
    n := id
    T := cell
    n_strictMono := strictMono_id
    subset := fun i x hx => hcellA i hx
    disjoint := hcellDisjoint
    nonempty := hcellNonempty
    destroys := by
      intro i E hEH
      have hE : E = cell i := by simpa [H] using hEH
      subst E
      obtain ⟨x, hx⟩ := hcellNonempty i
      apply Set.not_disjoint_iff.mpr
      exact ⟨x, Finset.mem_coe.mpr hx, Finset.mem_coe.mpr hx⟩
  }
  exact S.exists_finiteBlockPartition

def externalCliqueCell
    (R : Finset ℕ) (f : ℕ → Finset ℕ) (b : ℕ) : Finset ℕ :=
  insert b (f b \ R)

/-- The sunflower cells consisting of one atom and its nonempty petal can be
embedded as dedicated cores of a finite-block partition of A. -/
theorem exists_finiteBlockPartition_for_externalCliqueSunflower
    {A B : Set ℕ}
    (hBA : B ⊆ A)
    (hB : B.Infinite)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetal : ∀ b ∈ B, (f b \ R).Nonempty)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R)) :
    ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, externalCliqueCell R f (e i).1 ⊆ F i) ∧
      ∀ i, 2 ≤ (externalCliqueCell R f (e i).1).card := by
  classical
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let cell : ℕ → Finset ℕ := fun i =>
    externalCliqueCell R f (e i).1
  have hcellA : ∀ i, (cell i : Set ℕ) ⊆ A := by
    intro i q hq
    rcases Finset.mem_insert.mp hq with hqb | hqpetal
    · exact hqb ▸ hBA (e i).2
    · obtain ⟨w, hfw⟩ := hwitness (e i).1 (e i).2
      apply w.vertices_subset
      rw [← hfw]
      exact Finset.sdiff_subset hqpetal
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    exact ⟨(e i).1, Finset.mem_insert_self _ _⟩
  have hcellDisjoint : Pairwise fun i j =>
      Disjoint (cell i) (cell j) := by
    intro i j hij
    have hbij : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      apply e.injective
      exact Subtype.ext h
    rw [Finset.disjoint_left]
    intro q hqi hqj
    rcases Finset.mem_insert.mp hqi with hqbi | hqpi <;>
      rcases Finset.mem_insert.mp hqj with hqbj | hqpj
    · exact hbij (hqbi.symm.trans hqbj)
    · subst q
      have hmem : (e i).1 ∈ f (e j).1 :=
        Finset.sdiff_subset hqpj
      exact Set.disjoint_left.mp
        (havoid (e j).1 (e j).2)
        hmem (e i).2
    · subst q
      have hmem : (e j).1 ∈ f (e i).1 :=
        Finset.sdiff_subset hqpi
      exact Set.disjoint_left.mp
        (havoid (e i).1 (e i).2)
        hmem (e j).2
    · exact Finset.disjoint_left.mp
        (hpetalDisjoint (e i).1 (e i).2
          (e j).1 (e j).2 hbij)
        hqpi hqpj
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  refine ⟨e, F, P, hcore, ?_⟩
  intro i
  have hbiNotPetal : (e i).1 ∉ f (e i).1 \ R := by
    intro hmem
    exact Set.disjoint_left.mp
      (havoid (e i).1 (e i).2)
      (Finset.sdiff_subset hmem) (e i).2
  rw [externalCliqueCell, Finset.card_insert_of_notMem hbiNotPetal]
  have hone : 1 ≤ (f (e i).1 \ R).card :=
    Finset.one_le_card.mpr (hpetal (e i).1 (e i).2)
  omega

/-- The hereditary obstruction yields an infinite stratum of distinct
zero-atoms carrying intrinsic external four-cliques.  If only finitely many
atoms carried one, delete those finitely many from the hereditary reservoir;
the next fresh obstruction would produce another. -/
theorem counterexample_forces_infinite_externalFourCliqueAtoms
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ K, K ⊆ A ∧ K.Infinite ∧
      (∀ b ∈ K, ∀ E ∈ additiveSupportFamily A 2 b,
        E = {b, 0}) ∧
      ∀ b ∈ K, HasExternalFourCliqueAtAtom A b := by
  obtain ⟨B, hBA, hB, hhered⟩ :=
    counterexample_forces_hereditaryExternalFourCliques
      hbasis hzeroA hcounter
  let K : Set ℕ :=
    {b | b ∈ B ∧ HasExternalFourCliqueAtAtom A b ∧
      ∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0}}
  have hK : K.Infinite := by
    by_contra hnot
    have hKfinite : K.Finite := Set.not_infinite.mp hnot
    let D : Set ℕ := B \ K
    have hDB : D ⊆ B := Set.diff_subset
    have hD : D.Infinite := hB.diff hKfinite
    obtain ⟨_n, b, c, x, y, z, _hn, _hnA, hbD,
        hcD, hxD, hyD, hzD, hcpos, hxpos, hypos, hzpos,
        hxyz, _hbc, _hnormal, hxy, hxz, hyz, hxc, hyc, hzc⟩ :=
      hhered D hDB hD 0
    have hbProp : HasExternalFourCliqueAtAtom A b :=
      ⟨c, x, y, z, hcD.1, hxD.1, hyD.1, hzD.1,
        (fun hcb => hcD.2 (hcb.symm ▸ hbD)),
        hcpos, hxpos, hypos, hzpos,
        hxyz, hxy, hxz, hyz, hxc, hyc, hzc⟩
    have hbK : b ∈ K := ⟨hDB hbD, hbProp, _hnormal⟩
    exact hbD.2 hbK
  refine ⟨K, ?_, hK, ?_, ?_⟩
  · intro b hbK
    exact hBA hbK.1
  · intro b hbK E hER
    exact hbK.2.2 E hER
  · intro b hbK
    exact hbK.2.1

/-- Coherent external-clique residual.  A zero-normalized counterexample has
an infinite zero-atomic deletion reservoir B such that every red-red sum has
a direct retained triple repair and every b in B has a fixed retained
external four-clique witness. -/
theorem counterexample_forces_cliqueRepairedReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
        E = {b, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B ∧
      ∀ b ∈ B, HasExternalFourCliqueAtAtomAvoiding A B b := by
  obtain ⟨K, hKA, hK, hnormalK, hcliqueK⟩ :=
    counterexample_forces_infinite_externalFourCliqueAtoms
      hbasis hzeroA hcounter
  obtain ⟨L, hLK, hL, hcliqueL⟩ :=
    exists_infinite_externalFourCliqueAtoms_avoiding
      hK hcliqueK
  have hnormalL : ∀ b ∈ L,
      ∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0} := by
    intro b hb
    exact hnormalK b (hLK hb)
  obtain ⟨B, hBL, hB, hpairRepairs⟩ :=
    exists_infinite_directRepairs_of_zeroAtoms
      hbasis hL hnormalL
  refine ⟨B, hBL.trans (hLK.trans hKA), hB, ?_,
    hpairRepairs, ?_⟩
  · intro b hb E hER
    exact hnormalL b (hBL hb) E hER
  · intro b hb
    exact (hcliqueL b (hBL hb)).mono hBL

/-- Sunflower-and-repair residual.  Besides the direct repairs, the clique
witnesses can be organized into a fixed root and pairwise-disjoint nonempty
petals, with every witness set disjoint from the selected atoms. -/
theorem counterexample_forces_sunflowerRepairedReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R) := by
  obtain ⟨K, hKA, hK, hnormalK, hcliqueK⟩ :=
    counterexample_forces_infinite_externalFourCliqueAtoms
      hbasis hzeroA hcounter
  obtain ⟨L, hLK, hL, R, f, hwitness,
      havoid, hpetal, hpetalDisjoint⟩ :=
    exists_infinite_externalFourCliqueSunflower hK hcliqueK
  have hnormalL : ∀ b ∈ L,
      ∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0} := by
    intro b hb
    exact hnormalK b (hLK hb)
  obtain ⟨B, hBL, hB, hrepairs⟩ :=
    exists_infinite_directRepairs_of_zeroAtoms
      hbasis hL hnormalL
  refine ⟨B, hBL.trans (hLK.trans hKA), hB, R, f,
    ?_, hrepairs, ?_, ?_, ?_, ?_⟩
  · intro b hb E hER
    exact hnormalL b (hBL hb) E hER
  · intro b hb
    exact hwitness b (hBL hb)
  · intro b hb
    exact (havoid b (hBL hb)).mono_right hBL
  · intro b hb
    exact hpetal b (hBL hb)
  · intro b hb d hd hbd
    exact hpetalDisjoint b (hBL hb) d (hBL hd) hbd

/-- Strengthened sunflower residual with a distinguished repair petal at
every atom.  Each chosen petal lies strictly below its atom and has a
self-avoiding order-three support which simultaneously avoids the final
atom reservoir. -/
theorem counterexample_forces_selfRepairedPetalReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p : ℕ → ℕ, ∃ g : ℕ → Finset ℕ,
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ b ∈ B, p b ∈ f b \ R ∧ p b < b) ∧
        ∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧
          Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b := by
  obtain ⟨B₀, hB₀A, hB₀, R, f, hnormal₀, hrepairs₀,
      hwitness₀, havoid₀, hpetal₀, hpetalDisjoint₀⟩ :=
    counterexample_forces_sunflowerRepairedReservoir
      hbasis hzeroA hcounter
  obtain ⟨B, hBB₀, hB, p, g, hp, hg⟩ :=
    exists_infinite_selfRepaired_repairPetals
      hbasis hB₀ hwitness₀ hpetalDisjoint₀
  refine ⟨B, hBB₀.trans hB₀A, hB, R, f, p, g,
    ?_, hrepairs₀.mono hBB₀, ?_, ?_, ?_, ?_, hp, hg⟩
  · intro b hb E hER
    exact hnormal₀ b (hBB₀ hb) E hER
  · intro b hb
    exact hwitness₀ b (hBB₀ hb)
  · intro b hb
    exact (havoid₀ b (hBB₀ hb)).mono_right hBB₀
  · intro b hb
    exact hpetal₀ b (hBB₀ hb)
  · intro b hb d hd hbd
    exact hpetalDisjoint₀ b (hBB₀ hb) d (hBB₀ hd) hbd

/-- The direct collision between strong order-two deletion and the final
counterexample geometry.  For one sunflower reservoir and one finite-block
partition containing its atom-plus-petal cells, amplified pair certificates
force every finite pair-support choice to cover arbitrarily many whole
dedicated cells. -/
theorem stronglyMinimal_counterexample_forces_manyCoveredSunflowerCells
    {A : Set ℕ}
    (hminimal : IsStronglyMinimalExactBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ i, externalCliqueCell R f (e i).1 ⊆ F i) ∧
        (∀ i, 2 ≤ (externalCliqueCell R f (e i).1).card) ∧
        ∀ M start N, ∃ Q : Finset ℕ,
          (∀ q ∈ Q, N ≤ q) ∧
          ∀ c : FiniteSupportChoice
              (additiveSupportFamily A 2) Q,
            ∃ I : Finset ℕ,
              I.card = M ∧
              (∀ i ∈ I, start ≤ i) ∧
              ∀ i ∈ I,
                externalCliqueCell R f (e i).1 ⊆
                  finiteSupportChoiceUnion c := by
  obtain ⟨B, hBA, hB, R, f, hnormal, hrepairs,
      hwitness, havoid, hpetal, hpetalDisjoint⟩ :=
    counterexample_forces_sunflowerRepairedReservoir
      hminimal.1 hzeroA hcounter
  obtain ⟨e, F, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_for_externalCliqueSunflower
      hBA hB hwitness havoid hpetal hpetalDisjoint
  refine ⟨B, hBA, hB, R, f, e, F, P, hnormal,
    hrepairs, hwitness, havoid, hpetal, hpetalDisjoint,
    hcore, hcellCard, ?_⟩
  intro M start N
  obtain ⟨Q, hQN, hmany⟩ :=
    exists_manyCoveredBlocks_of_strongInfiniteDeletion
      P hminimal.2 M start N
  refine ⟨Q, hQN, ?_⟩
  intro c
  obtain ⟨I, hIcard, hIstart, hIcover⟩ := hmany c
  exact ⟨I, hIcard, hIstart, fun i hi =>
    (hcore i).trans (hIcover i hi)⟩

set_option maxHeartbeats 5000000 in
/-- The exact finite-certificate bridge on a sunflower reservoir.  One and
the same late target set `Q` is an order-three selector certificate, contains
an external target destroyed by the atom selector `B` with a crossing
order-two support, and forces every order-two support choice to cover
arbitrarily many atom-plus-petal cells.

The last conclusion is obtained by padding every chosen pair support with
zero.  No sunflower cell contains zero, so coverage by the padded triple
supports descends back to coverage by the original pair supports. -/
theorem exists_certifiedCoveredSunflowerTargets
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q) ∧
      (∃ q ∈ Q, q ∉ A ∧
        DestroysAt (additiveSupportFamily A 3) B q ∧
        ∃ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B ∧
          ¬ (E : Set ℕ) ⊆ B) ∧
      ∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I,
            externalCliqueCell R f (e i).1 ⊆
              finiteSupportChoiceUnion c := by
  classical
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w, _hfw⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w.atom_pos) rfl
  let s : BlockSelector F := fun i =>
    ⟨(e i).1, hcore i (by
      simp [externalCliqueCell])⟩
  have hsB : selectedSet s = B := by
    ext b
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hbB
      obtain ⟨i, hi⟩ := e.surjective ⟨b, hbB⟩
      refine ⟨i, ?_⟩
      exact congrArg Subtype.val hi
  have hcellZero : ∀ i,
      0 ∉ externalCliqueCell R f (e i).1 := by
    intro i h0cell
    obtain ⟨w, hfw⟩ := hwitness (e i).1 (e i).2
    rcases Finset.mem_insert.mp h0cell with h0b | h0petal
    · have hbpos := w.atom_pos
      omega
    · apply w.zero_not_mem_vertices
      rw [← hfw]
      exact Finset.sdiff_subset h0petal
  intro M start N
  obtain ⟨Q, hQlate, hcert, hmany⟩ :=
    exists_manyCoveredBlocks_and_certificate_of_strongInfiniteDeletion
      P (strongOrderThreeDeletion_of_counterexample hcounter)
      M start (max N N₂)
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hq
    exact (le_max_left N N₂).trans (hQlate q hq)
  have hQN₂ : ∀ q ∈ Q, N₂ ≤ q := by
    intro q hq
    exact (le_max_right N N₂).trans (hQlate q hq)
  have hsurviveA : ∀ q ∈ Q, q ∈ A →
      ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro q hqQ hqA
    rw [hsB]
    by_cases hqB : q ∈ B
    · obtain ⟨w, hfw⟩ := hwitness q hqB
      let G : Finset ℕ :=
        insert w.x (pairSupport (w.y + w.z) w.y)
      refine ⟨G, w.repairSupport_mem, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxB
      apply Set.disjoint_left.mp (havoid q hqB) ?_ hxB
      rw [hfw]
      exact w.repairSupport_subset_vertices
        (Finset.mem_coe.mp hxG)
    · have hpair : pairSupport q 0 ∈
          additiveSupportFamily A 2 q := by
        apply pairSupport_mem_additiveSupportFamily
          (Nat.zero_le q) hzeroA
        simpa using hqA
      have htriple : insert 0 (pairSupport q 0) ∈
          additiveSupportFamily A 3 q := by
        simpa using
          (insert_mem_additiveSupportFamily_succ hzeroA hpair)
      refine ⟨insert 0 (pairSupport q 0), htriple, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxB
      have hx : x = 0 ∨ x = q := by
        simpa [pairSupport] using (Finset.mem_coe.mp hxG)
      rcases hx with rfl | rfl
      · exact hzeroB hxB
      · exact hqB hxB
  obtain ⟨q, hqQ, hdestroyS⟩ := hcert s
  have hdestroyB :
      DestroysAt (additiveSupportFamily A 3) B q := by
    simpa [hsB] using hdestroyS
  have hqA : q ∉ A := by
    intro hqA
    obtain ⟨G, hGR, hGblue⟩ := hsurviveA q hqQ hqA
    exact (hdestroyS G hGR) hGblue
  obtain ⟨E, hER, _hEempty⟩ := hN₂ q (hQN₂ q hqQ)
  have hcross :=
    orderTwoSupports_crossing_of_zero_directRepairs_destroyer
      hzeroA hzeroB hrepairs hdestroyB E hER
  refine ⟨Q, hQN, hcert,
    ⟨q, hqQ, hqA, hdestroyB, E, hER, hcross⟩, ?_⟩
  intro c
  let c₃ : FiniteSupportChoice (additiveSupportFamily A 3) Q :=
    fun q =>
      ⟨insert 0 (c q).1,
        by simpa using
          (insert_mem_additiveSupportFamily_succ hzeroA (c q).2)⟩
  obtain ⟨I, hIcard, hIstart, hIcover⟩ := hmany c₃
  refine ⟨I, hIcard, hIstart, ?_⟩
  intro i hiI x hxcell
  have hxU₃ : x ∈ finiteSupportChoiceUnion c₃ :=
    hIcover i hiI (hcore i hxcell)
  obtain ⟨q', _hq'attach, hxG⟩ := Finset.mem_biUnion.mp hxU₃
  change x ∈ insert 0 (c q').1 at hxG
  rcases Finset.mem_insert.mp hxG with hx0 | hxpair
  · subst x
    exact (hcellZero i hxcell).elim
  · exact finiteSupportChoice_subset_union c q' hxpair

/-- A genuinely crossing order-two support consists of one deleted endpoint
and one retained endpoint, whose sum is the represented target. -/
theorem exists_endpoints_of_crossingPairSupport
    {A B : Set ℕ} {q : ℕ} {E : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hhit : ¬ Disjoint (E : Set ℕ) B)
    (hnotSub : ¬ (E : Set ℕ) ⊆ B) :
    ∃ b ∈ B, ∃ c ∈ A \ B,
      b + c = q ∧ E = {b, c} := by
  obtain ⟨b, hbE, hbB⟩ := Set.not_disjoint_iff.mp hhit
  obtain ⟨c, hcE, hcB⟩ := Set.not_subset.mp hnotSub
  have hbFin : b ∈ E := Finset.mem_coe.mp hbE
  have hcFin : c ∈ E := Finset.mem_coe.mp hcE
  have hEq : E = pairSupport q b :=
    additiveSupportFamily_two_eq_pairSupport_of_mem hER hbFin
  have hble : b ≤ q :=
    additiveSupportFamily_supportsBounded A 2 q E hER b hbFin
  have hcCases : c = b ∨ c = q - b := by
    rw [hEq] at hcFin
    simpa [pairSupport] using hcFin
  have hcb : c ≠ b := by
    intro hcb
    exact hcB (hcb ▸ hbB)
  have hcEq : c = q - b := hcCases.resolve_left hcb
  have hbc : b + c = q := by omega
  have hcA : c ∈ A :=
    additiveSupportFamily_supportsIn A 2 q E hER c
      (Finset.mem_coe.mp hcE)
  refine ⟨b, hbB, c, ⟨hcA, hcB⟩, hbc, ?_⟩
  rw [hEq]
  simp [pairSupport, ← hcEq]

/-- Replacing one atom selector value by a positive retained point different
from the complementary endpoint repairs the corresponding crossing target.
Indeed, the padded pair support `{0,b,c}` then avoids the modified selector. -/
theorem exists_singleCellOverride_surviving_crossingTarget
    {A B : Set ℕ} {F : ℕ → Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A) (hzeroB : 0 ∉ B)
    (e : ℕ ≃ B) {i b c p q : ℕ}
    (hatom : ∀ j, (e j).1 ∈ F j)
    (hbi : (e i).1 = b)
    (hpF : p ∈ F i)
    (hpC : p ∈ A \ B) (hppos : 0 < p)
    (hcC : c ∈ A \ B)
    (hbc : b + c = q) (hpc : p ≠ c) :
    ∃ s : BlockSelector F,
      selectedSet s ⊆ insert p B ∧
      p ∈ selectedSet s ∧
      b ∉ selectedSet s ∧
      ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
  classical
  let s : BlockSelector F := fun j =>
    if hji : j = i then
      ⟨p, hji ▸ hpF⟩
    else ⟨(e j).1, hatom j⟩
  have hbB : b ∈ B := hbi ▸ (e i).2
  have hble : b ≤ q := by omega
  have hsub : q - b = c := by omega
  have hpair : pairSupport q b ∈
      additiveSupportFamily A 2 q := by
    apply pairSupport_mem_additiveSupportFamily hble (hBA hbB)
    simpa [hsub] using hcC.1
  let G : Finset ℕ := insert 0 (pairSupport q b)
  have hGR : G ∈ additiveSupportFamily A 3 q := by
    simpa [G] using
      (insert_mem_additiveSupportFamily_succ hzeroA hpair)
  have hsSub : selectedSet s ⊆ insert p B := by
    rintro x ⟨j, rfl⟩
    by_cases hji : j = i
    · left
      simp [s, hji]
    · right
      simp [s, hji]
  have hpS : p ∈ selectedSet s := by
    refine ⟨i, ?_⟩
    simp [s]
  have hbNotS : b ∉ selectedSet s := by
    rintro ⟨j, hj⟩
    change (s j).1 = b at hj
    by_cases hji : j = i
    · subst j
      have hpb : p = b := by simpa [s] using hj
      exact hpC.2 (hpb ▸ hbB)
    · have hejb : (e j).1 = b := by simpa [s, hji] using hj
      apply hji
      apply e.injective
      apply Subtype.ext
      exact hejb.trans hbi.symm
  refine ⟨s, hsSub, hpS, hbNotS, G, hGR, ?_⟩
  rw [Set.disjoint_left]
  intro x hxG hxs
  have hxCases : x = 0 ∨ x = b ∨ x = c := by
    have hxFin := Finset.mem_coe.mp hxG
    simpa [G, pairSupport, hsub] using hxFin
  obtain ⟨j, hj⟩ := hxs
  change (s j).1 = x at hj
  by_cases hji : j = i
  · subst j
    have hpx : p = x := by simpa [s] using hj
    rcases hxCases with rfl | rfl | rfl
    · exact (Nat.ne_of_gt hppos) hpx
    · exact hpC.2 (hpx.trans hbi.symm ▸ (e i).2)
    · exact hpc hpx
  · have hejx : (e j).1 = x := by simpa [s, hji] using hj
    rcases hxCases with rfl | rfl | rfl
    · exact hzeroB (hejx ▸ (e j).2)
    · apply hji
      apply e.injective
      apply Subtype.ext
      exact hejx.trans hbi.symm
    · exact hcC.2 (hejx ▸ (e j).2)

/-- Consequently a finite selector certificate cannot keep the same crossing
target after a non-complementary petal override: it must move its destruction
witness to another target in `Q`. -/
theorem certificate_moves_after_singleCellOverride
    {A B : Set ℕ} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A) (hzeroB : 0 ∉ B)
    (e : ℕ ≃ B) {i b c p q : ℕ}
    (hatom : ∀ j, (e j).1 ∈ F j)
    (hbi : (e i).1 = b)
    (hpF : p ∈ F i)
    (hpC : p ∈ A \ B) (hppos : 0 < p)
    (hcC : c ∈ A \ B)
    (hbc : b + c = q) (hpc : p ≠ c)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    ∃ q' ∈ Q, q' ≠ q ∧
      ∃ s : BlockSelector F,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q' ∧
        selectedSet s ⊆ insert p B ∧
        p ∈ selectedSet s ∧
        b ∉ selectedSet s ∧
        ∃ G ∈ additiveSupportFamily A 3 q,
          Disjoint (G : Set ℕ) (selectedSet s) := by
  obtain ⟨s, hsSub, hpS, hbNotS, G, hGR, hGblue⟩ :=
    exists_singleCellOverride_surviving_crossingTarget
      hBA hzeroA hzeroB e hatom hbi hpF hpC hppos hcC hbc hpc
  obtain ⟨q', hq'Q, hq'destroy⟩ := hcert s
  have hq'q : q' ≠ q := by
    intro hEq
    subst q'
    exact (hq'destroy G hGR) hGblue
  exact ⟨q', hq'Q, hq'q, s, hq'destroy,
    hsSub, hpS, hbNotS, G, hGR, hGblue⟩

/-- On a sunflower reservoir, the only internal target that can be destroyed
after replacing atom `b` by its petal point `p` is `p` itself.  Other retained
non-atoms use the trivial zero-padded support; `b` uses that same support
after being removed; and every other atom uses its own repair support, whose
petal is disjoint from the petal of `b`. -/
theorem internal_destroyer_of_singlePetalOverride_eq_petal
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    (hzeroA : 0 ∈ A) (hzeroB : 0 ∉ B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    {b p q' : ℕ} (hbB : b ∈ B) (hpPetal : p ∈ f b \ R)
    (hppos : 0 < p)
    {F : ℕ → Finset ℕ} {s : BlockSelector F}
    (hsSub : selectedSet s ⊆ insert p B)
    (hbNotS : b ∉ selectedSet s)
    (hdestroy : DestroysAt (additiveSupportFamily A 3)
      (selectedSet s) q')
    (hq'A : q' ∈ A) :
    q' = p := by
  classical
  have htrivial : ∀ t, t ∈ A → t ∉ selectedSet s →
      ∃ G ∈ additiveSupportFamily A 3 t,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro t htA htS
    have hpair : pairSupport t 0 ∈
        additiveSupportFamily A 2 t := by
      apply pairSupport_mem_additiveSupportFamily
        (Nat.zero_le t) hzeroA
      simpa using htA
    let G : Finset ℕ := insert 0 (pairSupport t 0)
    have hGR : G ∈ additiveSupportFamily A 3 t := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hpair)
    refine ⟨G, hGR, ?_⟩
    rw [Set.disjoint_left]
    intro x hxG hxS
    have hx : x = 0 ∨ x = t := by
      simpa [G, pairSupport] using (Finset.mem_coe.mp hxG)
    rcases hx with rfl | rfl
    · rcases hsSub hxS with h0p | h0B
      · exact (Nat.ne_of_gt hppos) h0p.symm
      · exact hzeroB h0B
    · exact htS hxS
  by_contra hq'p
  by_cases hq'B : q' ∈ B
  · by_cases hq'b : q' = b
    · subst q'
      obtain ⟨G, hGR, hGblue⟩ := htrivial b hq'A hbNotS
      exact (hdestroy G hGR) hGblue
    · obtain ⟨w, hfw⟩ := hwitness q' hq'B
      let G : Finset ℕ :=
        insert w.x (pairSupport (w.y + w.z) w.y)
      have hGR : G ∈ additiveSupportFamily A 3 q' :=
        w.repairSupport_mem
      have hpNotF : p ∉ f q' := by
        intro hpF
        have hpR : p ∉ R := (Finset.mem_sdiff.mp hpPetal).2
        have hpOtherPetal : p ∈ f q' \ R :=
          Finset.mem_sdiff.mpr ⟨hpF, hpR⟩
        exact Finset.disjoint_left.mp
          (hpetalDisjoint b hbB q' hq'B (fun h => hq'b h.symm))
          hpPetal hpOtherPetal
      have hGblue : Disjoint (G : Set ℕ) (selectedSet s) := by
        rw [Set.disjoint_left]
        intro x hxG hxS
        rcases hsSub hxS with hxp | hxB
        · subst x
          apply hpNotF
          rw [hfw]
          exact w.repairSupport_subset_vertices
            (Finset.mem_coe.mp hxG)
        · apply Set.disjoint_left.mp (havoid q' hq'B) ?_ hxB
          rw [hfw]
          exact w.repairSupport_subset_vertices
            (Finset.mem_coe.mp hxG)
      exact (hdestroy G hGR) hGblue
  · have hq'NotS : q' ∉ selectedSet s := by
      intro hq'S
      rcases hsSub hq'S with hq'p' | hq'B'
      · exact hq'p hq'p'
      · exact hq'B hq'B'
    obtain ⟨G, hGR, hGblue⟩ := htrivial q' hq'A hq'NotS
    exact (hdestroy G hGR) hGblue

/-- The new petal point is contained in every atom-avoiding triple support
of a target destroyed by a one-petal override. -/
theorem petal_mem_of_overrideDestroyer_of_atomAvoidingSupport
    {A B : Set ℕ} {p q' : ℕ}
    {F : ℕ → Finset ℕ} {s : BlockSelector F}
    (hsSub : selectedSet s ⊆ insert p B)
    (hdestroy : DestroysAt (additiveSupportFamily A 3)
      (selectedSet s) q') :
    ∀ G ∈ additiveSupportFamily A 3 q',
      Disjoint (G : Set ℕ) B → p ∈ G := by
  intro G hGR hGB
  obtain ⟨x, hxG, hxS⟩ :=
    Set.not_disjoint_iff.mp (hdestroy G hGR)
  rcases hsSub hxS with hxp | hxB
  · exact hxp ▸ Finset.mem_coe.mp hxG
  · exact (Set.disjoint_left.mp hGB hxG hxB).elim

/-- Every internal target survives an arbitrary finite simultaneous petal
override.  Atoms which were overridden use the zero-padded trivial support;
unmodified atoms use their own clique repair; a selected petal uses its
self-repair; and every other retained non-atom again uses the trivial
support. -/
theorem internalTarget_survives_finitePetalOverride
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    {S : Finset ℕ} (hSB : ∀ b ∈ S, b ∈ B)
    {F : ℕ → Finset ℕ} {s : BlockSelector F}
    (hsSub : selectedSet s ⊆ B ∪ p '' (S : Set ℕ))
    (hremoved : ∀ b ∈ S, b ∉ selectedSet s) :
    ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
      Disjoint (G : Set ℕ) (selectedSet s) := by
  classical
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  have hpPos : ∀ b ∈ B, 0 < p b := by
    intro b hb
    obtain ⟨w, hfw⟩ := hwitness b hb
    have hpV : p b ∈ w.vertices := by
      rw [← hfw]
      exact Finset.sdiff_subset (hp b hb).1
    have hp0 : p b ≠ 0 := by
      intro hp0
      apply w.zero_not_mem_vertices
      exact hp0 ▸ hpV
    omega
  have hzeroS : 0 ∉ selectedSet s := by
    intro h0S
    rcases hsSub h0S with h0B | ⟨d, hdS, hpd⟩
    · exact hzeroB h0B
    · have hdB : d ∈ B := hSB d (Finset.mem_coe.mp hdS)
      have hpdpos := hpPos d hdB
      omega
  have htrivial : ∀ q, q ∈ A → q ∉ selectedSet s →
      ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro q hqA hqS
    have hpair : pairSupport q 0 ∈
        additiveSupportFamily A 2 q := by
      apply pairSupport_mem_additiveSupportFamily
        (Nat.zero_le q) hzeroA
      simpa using hqA
    let G : Finset ℕ := insert 0 (pairSupport q 0)
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hpair)
    refine ⟨G, hGR, ?_⟩
    rw [Set.disjoint_left]
    intro x hxG hxS
    have hx : x = 0 ∨ x = q := by
      simpa [G, pairSupport] using (Finset.mem_coe.mp hxG)
    rcases hx with rfl | rfl
    · exact hzeroS hxS
    · exact hqS hxS
  intro q hqA
  by_cases hqB : q ∈ B
  · by_cases hqS : q ∈ S
    · exact htrivial q hqA (hremoved q hqS)
    · obtain ⟨w, hfw⟩ := hwitness q hqB
      let G : Finset ℕ :=
        insert w.x (pairSupport (w.y + w.z) w.y)
      refine ⟨G, w.repairSupport_mem, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxSelected
      rcases hsSub hxSelected with hxB | ⟨d, hdS, hpd⟩
      · apply Set.disjoint_left.mp (havoid q hqB) ?_ hxB
        rw [hfw]
        exact w.repairSupport_subset_vertices
          (Finset.mem_coe.mp hxG)
      · have hdSfin : d ∈ S := Finset.mem_coe.mp hdS
        have hdB : d ∈ B := hSB d hdSfin
        have hqd : q ≠ d := by
          intro hqd
          exact hqS (hqd ▸ hdSfin)
        have hpqPetal : p d ∈ f q \ R := by
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, (Finset.mem_sdiff.mp (hp d hdB).1).2⟩
          rw [hfw]
          apply w.repairSupport_subset_vertices
          exact Finset.mem_coe.mp (hpd ▸ hxG)
        exact Finset.disjoint_left.mp
          (hpetalDisjoint q hqB d hdB hqd)
          hpqPetal (hp d hdB).1
  · by_cases hqPetal : q ∈ p '' (S : Set ℕ)
    · obtain ⟨d, hdS, hpdq⟩ := hqPetal
      have hdSfin : d ∈ S := Finset.mem_coe.mp hdS
      have hdB : d ∈ B := hSB d hdSfin
      have hGblue : Disjoint (g d : Set ℕ) (selectedSet s) := by
        rw [Set.disjoint_left]
        intro x hxG hxSelected
        rcases hsSub hxSelected with hxB | ⟨a, haS, hpa⟩
        · exact Set.disjoint_left.mp (hg d hdB).2.2.1 hxG hxB
        · have haB : a ∈ B := hSB a (Finset.mem_coe.mp haS)
          exact (hg d hdB).2.2.2 a haB
            (Finset.mem_coe.mp (hpa ▸ hxG))
      rw [← hpdq]
      exact ⟨g d, (hg d hdB).1, hGblue⟩
    · have hqNotSelected : q ∉ selectedSet s := by
        intro hqSelected
        rcases hsSub hqSelected with hqB' | hqPetal'
        · exact hqB hqB'
        · exact hqPetal hqPetal'
      exact htrivial q hqA hqNotSelected

/-- Simultaneously override any finite set of atom blocks by their
distinguished petals.  The resulting selector is contained in the old atom
set together with those petals, removes every overridden atom, and selects
every requested petal. -/
theorem exists_finitePetalOverrideSelector
    {B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (S : Finset ℕ) (hSB : ∀ b ∈ S, b ∈ B) :
    ∃ s : BlockSelector F,
      selectedSet s ⊆ B ∪ p '' (S : Set ℕ) ∧
      (∀ b ∈ S, b ∉ selectedSet s) ∧
      ∀ b ∈ S, p b ∈ selectedSet s := by
  classical
  let s : BlockSelector F := fun i =>
    if hi : (e i).1 ∈ S then
      ⟨p (e i).1, hcore i (by
        rw [externalCliqueCell]
        exact Finset.mem_insert_of_mem (hp (e i).1 (e i).2))⟩
    else
      ⟨(e i).1, hcore i (by
        rw [externalCliqueCell]
        exact Finset.mem_insert_self _ _)⟩
  have hpNotB : ∀ b ∈ B, p b ∉ B := by
    intro b hb hpB
    exact Set.disjoint_left.mp (havoid b hb)
      (Finset.sdiff_subset (hp b hb)) hpB
  refine ⟨s, ?_, ?_, ?_⟩
  · rintro x ⟨i, rfl⟩
    by_cases hi : (e i).1 ∈ S
    · right
      refine ⟨(e i).1, Finset.mem_coe.mpr hi, ?_⟩
      simp [s, hi]
    · left
      simp [s, hi]
  · intro b hbS hbSelected
    obtain ⟨i, hi⟩ := hbSelected
    change (s i).1 = b at hi
    by_cases heiS : (e i).1 ∈ S
    · have hpib : p (e i).1 = b := by simpa [s, heiS] using hi
      exact hpNotB (e i).1 (e i).2 (hpib ▸ hSB b hbS)
    · have heib : (e i).1 = b := by simpa [s, heiS] using hi
      exact heiS (heib ▸ hbS)
  · intro b hbS
    let bi : B := ⟨b, hSB b hbS⟩
    let i : ℕ := e.symm bi
    refine ⟨i, ?_⟩
    have hei : e i = bi := e.apply_symm_apply bi
    have hval : (e i).1 = b := congrArg Subtype.val hei
    have heiS : (e i).1 ∈ S := hval ▸ hbS
    change (s i).1 = p b
    dsimp only [s]
    split
    · exact congrArg p hval
    · rename_i h
      exact (h heiS).elim

/-- A prescribed finite override batch forces external migration whenever it
contains an atom endpoint for every certificate target destroyed by `B`, and
the corresponding complementary endpoint avoids all selected petals.  This
choice-sensitive form is what allows several disjoint batches to be compared. -/
theorem finiteCertificate_forces_externalPetalEssential_of_coveringEndpoints
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q S : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hSB : ∀ b ∈ S, b ∈ B)
    (hcover : ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ b ∈ S, ∃ c ∈ A \ B,
        b + c = q ∧ c ∉ p '' (S : Set ℕ)) :
    ∃ q' ∈ Q, q' ∉ A ∧
      ¬ DestroysAt (additiveSupportFamily A 3) B q' ∧
      ∀ H ∈ additiveSupportFamily A 3 q',
        Disjoint (H : Set ℕ) B →
        ¬ Disjoint (H : Set ℕ) (p '' (S : Set ℕ)) := by
  classical
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  obtain ⟨s, hsSub, hremoved, _hpetalsSelected⟩ :=
    exists_finitePetalOverrideSelector
      havoid (fun b hb => (hp b hb).1) hcore S hSB
  have hBdestroyedSurvives : ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro q hqQ hqDestroy
    obtain ⟨b, hbS, c, hcC, hsum, hcPetal⟩ :=
      hcover q hqQ hqDestroy
    have hbB := hSB b hbS
    have hbA : b ∈ A := hBA hbB
    have hcA : c ∈ A := hcC.1
    have hble : b ≤ q := by omega
    have hsub : q - b = c := by omega
    have hpairR : pairSupport q b ∈
        additiveSupportFamily A 2 q := by
      apply pairSupport_mem_additiveSupportFamily hble hbA
      simpa [hsub] using hcA
    let G : Finset ℕ := insert 0 (pairSupport q b)
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hpairR)
    refine ⟨G, hGR, ?_⟩
    rw [Set.disjoint_left]
    intro x hxG hxSelected
    have hx : x = 0 ∨ x = b ∨ x = c := by
      simpa [G, pairSupport, hsub] using (Finset.mem_coe.mp hxG)
    rcases hx with hx0 | hxb | hxc
    · subst x
      rcases hsSub hxSelected with h0B | ⟨d, hdS, hpd⟩
      · exact hzeroB h0B
      · have hdB := hSB d (Finset.mem_coe.mp hdS)
        obtain ⟨w, hfw⟩ := hwitness d hdB
        have hp0 : p d ≠ 0 := by
          intro hp0
          have hpV : p d ∈ w.vertices := by
            rw [← hfw]
            exact Finset.sdiff_subset (hp d hdB).1
          exact w.zero_not_mem_vertices (hp0 ▸ hpV)
        exact hp0 hpd
    · subst x
      exact hremoved b hbS hxSelected
    · subst x
      rcases hsSub hxSelected with hcB | hcP
      · exact hcC.2 hcB
      · exact hcPetal hcP
  obtain ⟨q', hq'Q, hq'Destroy⟩ := hcert s
  have hq'NotDestroyB :
      ¬ DestroysAt (additiveSupportFamily A 3) B q' := by
    intro hq'B
    obtain ⟨G, hGR, hGblue⟩ :=
      hBdestroyedSurvives q' hq'Q hq'B
    exact (hq'Destroy G hGR) hGblue
  have hq'NotA : q' ∉ A := by
    intro hq'A
    obtain ⟨G, hGR, hGblue⟩ :=
      internalTarget_survives_finitePetalOverride
        hzeroA hwitness havoid hpetalDisjoint hp hg
        hSB hsSub hremoved q' hq'A
    exact (hq'Destroy G hGR) hGblue
  refine ⟨q', hq'Q, hq'NotA, hq'NotDestroyB, ?_⟩
  intro H hHR hHB
  obtain ⟨x, hxH, hxSelected⟩ :=
    Set.not_disjoint_iff.mp (hq'Destroy H hHR)
  rcases hsSub hxSelected with hxB | hxPetal
  · exact (Set.disjoint_left.mp hHB hxH hxB).elim
  · exact Set.not_disjoint_iff.mpr ⟨x, hxH, hxPetal⟩

/-- Pairwise-disjoint finite batches cannot all be essential for external
targets from one fixed finite certificate.  For each certificate target fix
one order-three support surviving `B`.  Every batch assigned to that target
must consume a different point of that support, so at most three batches can
be assigned to each target. -/
theorem card_pairwiseDisjoint_externalEssentialBatches_le
    {A B : Set ℕ} {Q : Finset ℕ} {batches : Finset (Finset ℕ)}
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hpair : IsMatching batches)
    (hessential : ∀ T ∈ batches, ∃ q ∈ Q,
      ¬ DestroysAt (additiveSupportFamily A 3) B q ∧
      ∀ H ∈ additiveSupportFamily A 3 q,
        Disjoint (H : Set ℕ) B →
        ¬ Disjoint (H : Set ℕ) (T : Set ℕ)) :
    batches.card ≤ 3 * Q.card := by
  classical
  let c : FiniteSupportChoice (additiveSupportFamily A 3) Q := fun q =>
    if hq : ¬ DestroysAt (additiveSupportFamily A 3) B q.1 then
      ⟨(not_destroysAt_iff.mp hq).choose,
        (not_destroysAt_iff.mp hq).choose_spec.1⟩
    else
      ⟨(hrepresented q.1 q.2).choose,
        (hrepresented q.1 q.2).choose_spec⟩
  have hcBlue : ∀ q : {n // n ∈ Q},
      ¬ DestroysAt (additiveSupportFamily A 3) B q.1 →
      Disjoint (((c q).1 : Finset ℕ) : Set ℕ) B := by
    intro q hq
    simp only [c, dif_pos hq]
    exact (not_destroysAt_iff.mp hq).choose_spec.2
  have hessential' : ∀ T : {T // T ∈ batches},
      ∃ q : {n // n ∈ Q},
        ¬ DestroysAt (additiveSupportFamily A 3) B q.1 ∧
        ∀ H ∈ additiveSupportFamily A 3 q.1,
          Disjoint (H : Set ℕ) B →
          ¬ Disjoint (H : Set ℕ) (T.1 : Set ℕ) := by
    intro T
    obtain ⟨q, hqQ, hqBlue, hqEssential⟩ :=
      hessential T.1 T.2
    exact ⟨⟨q, hqQ⟩, hqBlue, hqEssential⟩
  choose target htargetBlue htargetEssential using hessential'
  let U := finiteSupportChoiceUnion c
  let pick : ∀ T : {T // T ∈ batches}, {x // x ∈ U} := fun T =>
    let w := Set.not_disjoint_iff.mp
      (htargetEssential T (c (target T)).1 (c (target T)).2
        (hcBlue (target T) (htargetBlue T)))
    ⟨w.choose,
      finiteSupportChoice_subset_union c (target T) w.choose_spec.1⟩
  have hpick_mem : ∀ T : {T // T ∈ batches}, (pick T).1 ∈ T.1 := by
    intro T
    change
      (Set.not_disjoint_iff.mp
        (htargetEssential T (c (target T)).1 (c (target T)).2
          (hcBlue (target T) (htargetBlue T)))).choose ∈ T.1
    exact Finset.mem_coe.mp
      (Set.not_disjoint_iff.mp
        (htargetEssential T (c (target T)).1 (c (target T)).2
          (hcBlue (target T) (htargetBlue T)))).choose_spec.2
  have hpick_injective : Function.Injective pick := by
    intro T T' hpick
    apply Subtype.ext
    by_contra hTT'
    have hdisj : Disjoint T.1 T'.1 := hpair T.2 T'.2 hTT'
    have hx : (pick T).1 = (pick T').1 :=
      congrArg Subtype.val hpick
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick T).1, hpick_mem T, hx ▸ hpick_mem T'⟩) hdisj
  have hcardU : batches.card ≤ U.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  exact hcardU.trans <|
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 3) c

/-- Choosing one point from each disjoint sunflower petal gives an injective
map on the atom reservoir. -/
theorem repairPetalMap_injOn
    {B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ} {p : ℕ → ℕ}
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R) :
    Set.InjOn p B := by
  intro b hb d hd hpd
  by_contra hbd
  exact Finset.disjoint_left.mp
    (hpetalDisjoint b hb d hd hbd)
    (hp b hb) (hpd ▸ hp d hd)

/-- A crude but useful finite Hall bound.  If every member of a finite
indexed family has at least `r * D.card` candidates, then one can choose `r`
systems of representatives which are globally pairwise disjoint.  Each
system contains a representative from every candidate set. -/
theorem exists_pairwiseDisjoint_coveringSystems_of_uniform_card
    {α β : Type*} [DecidableEq β]
    {D : Finset α} {E : α → Finset β} {r : ℕ}
    (hlarge : ∀ q ∈ D, r * D.card ≤ (E q).card) :
    ∃ systems : Fin r → Finset β,
      (∀ t, systems t ⊆ D.biUnion E) ∧
      (∀ t, ∀ q ∈ D, ∃ x ∈ systems t, x ∈ E q) ∧
      Pairwise fun t u => Disjoint (systems t) (systems u) := by
  classical
  let ι := Fin r × {q // q ∈ D}
  let candidates : ι → Finset β := fun x => E x.2.1
  have hιcard : Fintype.card ι = r * D.card := by
    simp [ι]
  have hHall : ∀ U : Finset ι,
      U.card ≤ (U.biUnion candidates).card := by
    intro U
    by_cases hU : U.Nonempty
    · obtain ⟨x, hxU⟩ := hU
      calc
        U.card ≤ Fintype.card ι := Finset.card_le_univ U
        _ = r * D.card := hιcard
        _ ≤ (E x.2.1).card := hlarge x.2.1 x.2.2
        _ ≤ (U.biUnion candidates).card := by
          apply Finset.card_le_card
          intro y hy
          exact Finset.mem_biUnion.mpr ⟨x, hxU, hy⟩
    · have hUempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [hUempty]
  obtain ⟨pick, hpickInj, hpickMem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      candidates).mp hHall
  let systems : Fin r → Finset β := fun t =>
    D.attach.image fun q => pick (t, q)
  refine ⟨systems, ?_, ?_, ?_⟩
  · intro t x hx
    obtain ⟨q, _hqAttach, hqx⟩ := Finset.mem_image.mp hx
    apply Finset.mem_biUnion.mpr
    refine ⟨q.1, q.2, ?_⟩
    exact hqx ▸ hpickMem (t, q)
  · intro t q hqD
    let qsub : {q // q ∈ D} := ⟨q, hqD⟩
    refine ⟨pick (t, qsub), ?_, hpickMem (t, qsub)⟩
    exact Finset.mem_image.mpr ⟨qsub, by simp, rfl⟩
  · intro t u htu
    rw [Finset.disjoint_left]
    intro x hxt hxu
    obtain ⟨q, _hqAttach, hqx⟩ := Finset.mem_image.mp hxt
    obtain ⟨d, _hdAttach, hdx⟩ := Finset.mem_image.mp hxu
    have hpickEq : pick (t, q) = pick (u, d) :=
      hqx.trans hdx.symm
    have hindexEq : (t, q) = (u, d) := hpickInj hpickEq
    exact htu (congrArg Prod.fst hindexEq)

/-- Finite-family packaging of the preceding Hall construction.  When the
target index set is nonempty, the `r` systems are distinct as well as
pairwise disjoint, hence form a matching of cardinality exactly `r`. -/
theorem exists_matching_coveringSystems_of_uniform_card
    {α β : Type*} [DecidableEq β]
    {D : Finset α} {E : α → Finset β} {r : ℕ}
    (hD : D.Nonempty)
    (hlarge : ∀ q ∈ D, r * D.card ≤ (E q).card) :
    ∃ systems : Finset (Finset β),
      systems.card = r ∧ IsMatching systems ∧
      ∀ S ∈ systems,
        S ⊆ D.biUnion E ∧
        ∀ q ∈ D, ∃ x ∈ S, x ∈ E q := by
  classical
  obtain ⟨indexed, hsubset, hcover, hpair⟩ :=
    exists_pairwiseDisjoint_coveringSystems_of_uniform_card hlarge
  have hindexedInj : Function.Injective indexed := by
    intro t u hEq
    by_contra htu
    obtain ⟨q, hqD⟩ := hD
    obtain ⟨x, hxt, _hxE⟩ := hcover t q hqD
    have hxu : x ∈ indexed u := by
      rw [← hEq]
      exact hxt
    exact (Finset.not_disjoint_iff.mpr ⟨x, hxt, hxu⟩)
      (hpair htu)
  let systems : Finset (Finset β) :=
    Finset.univ.image indexed
  refine ⟨systems, ?_, ?_, ?_⟩
  · simp [systems, Finset.card_image_iff.mpr hindexedInj.injOn]
  · rw [IsMatching]
    intro S hS T hT hST
    change S ∈ systems at hS
    change T ∈ systems at hT
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hT
    apply hpair
    intro htu
    subst u
    exact hST rfl
  · intro S hS
    obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hS
    exact ⟨hsubset t, hcover t⟩

/-- Atom endpoints of crossing order-two representations of `q` relative to
the red set `B`.  The complementary endpoint is canonically `q - b`. -/
noncomputable def crossingAtomEndpoints
    (A B : Set ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (q + 1)).filter fun b =>
    b ∈ B ∧ q - b ∈ A \ B

theorem mem_crossingAtomEndpoints_iff
    {A B : Set ℕ} {q b : ℕ} :
    b ∈ crossingAtomEndpoints A B q ↔
      b ≤ q ∧ b ∈ B ∧ q - b ∈ A \ B := by
  classical
  simp [crossingAtomEndpoints]

theorem crossingAtomEndpoint_sum
    {A B : Set ℕ} {q b : ℕ}
    (hb : b ∈ crossingAtomEndpoints A B q) :
    b + (q - b) = q := by
  have hble := (mem_crossingAtomEndpoints_iff.mp hb).1
  omega

/-- At a target whose every pair support crosses `B`, the entire pair-support
family is obtained by mapping each crossing atom endpoint to its canonical
pair support. -/
theorem pairSupports_eq_image_crossingAtomEndpoints
    {A B : Set ℕ} {q : ℕ}
    (hBA : B ⊆ A)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B) :
    additiveSupportFamily A 2 q =
      (crossingAtomEndpoints A B q).image (pairSupport q) := by
  classical
  ext E
  constructor
  · intro hER
    obtain ⟨b, hbB, c, hcC, hbc, hE⟩ :=
      exists_endpoints_of_crossingPairSupport
        hER (hcross E hER).1 (hcross E hER).2
    have hble : b ≤ q := by omega
    have hsub : q - b = c := by omega
    apply Finset.mem_image.mpr
    refine ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hble, hbB, hsub ▸ hcC⟩, ?_⟩
    simpa [pairSupport, hsub] using hE.symm
  · intro hE
    obtain ⟨b, hbEndpoint, rfl⟩ := Finset.mem_image.mp hE
    have hbData := mem_crossingAtomEndpoints_iff.mp hbEndpoint
    exact pairSupport_mem_additiveSupportFamily
      hbData.1 (hBA hbData.2.1) hbData.2.2.1

/-- The canonical-pair map is injective on crossing atom endpoints, because
the other endpoint lies outside `B` and hence cannot be another atom
endpoint of the same support. -/
theorem pairSupport_injOn_crossingAtomEndpoints
    {A B : Set ℕ} {q : ℕ} :
    Set.InjOn (pairSupport q)
      (crossingAtomEndpoints A B q : Set ℕ) := by
  intro b hb d hd hEq
  have hbData := mem_crossingAtomEndpoints_iff.mp
    (Finset.mem_coe.mp hb)
  have hdData := mem_crossingAtomEndpoints_iff.mp
    (Finset.mem_coe.mp hd)
  have hbIn : b ∈ pairSupport q b := by simp [pairSupport]
  have hbCases : b = d ∨ b = q - d := by
    rw [hEq] at hbIn
    simpa [pairSupport] using hbIn
  rcases hbCases with hbd | hbd
  · exact hbd
  · exact (hdData.2.2.2 (hbd ▸ hbData.2.1)).elim

/-- Consequently crossing atom endpoints and crossing pair supports have
exactly the same finite cardinality. -/
theorem card_pairSupports_eq_card_crossingAtomEndpoints
    {A B : Set ℕ} {q : ℕ}
    (hBA : B ⊆ A)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B ∧ ¬ (E : Set ℕ) ⊆ B) :
    (additiveSupportFamily A 2 q).card =
      (crossingAtomEndpoints A B q).card := by
  rw [pairSupports_eq_image_crossingAtomEndpoints hBA hcross]
  exact Finset.card_image_iff.mpr
    pairSupport_injOn_crossingAtomEndpoints

/-- The certificate targets destroyed by a fixed deletion set. -/
noncomputable def destroyedCertificateTargets
    (A B : Set ℕ) (Q : Finset ℕ) : Finset ℕ := by
  classical
  exact Q.filter fun q =>
    DestroysAt (additiveSupportFamily A 3) B q

theorem mem_destroyedCertificateTargets_iff
    {A B : Set ℕ} {Q : Finset ℕ} {q : ℕ} :
    q ∈ destroyedCertificateTargets A B Q ↔
      q ∈ Q ∧ DestroysAt (additiveSupportFamily A 3) B q := by
  classical
  simp [destroyedCertificateTargets]

/-- An injective petal map preserves both the size and the matching property
of any finite family of pairwise-disjoint atom batches. -/
theorem petalBatchImages_card_eq_and_matching
    {B : Set ℕ} {p : ℕ → ℕ} {systems : Finset (Finset ℕ)}
    (hpInj : Set.InjOn p B)
    (hsystemsB : ∀ S ∈ systems, (S : Set ℕ) ⊆ B)
    (hmatching : IsMatching systems) :
    (systems.image fun S => S.image p).card = systems.card ∧
      IsMatching (systems.image fun S => S.image p) := by
  classical
  have himageInj : Set.InjOn (fun S : Finset ℕ => S.image p)
      (systems : Set (Finset ℕ)) := by
    intro S hS D hD hEq
    apply Finset.coe_injective
    apply (hpInj.image_eq_image_iff
      (hsystemsB S hS) (hsystemsB D hD)).mp
    simpa only [Finset.coe_image] using
      congrArg (fun T : Finset ℕ => (T : Set ℕ)) hEq
  refine ⟨Finset.card_image_iff.mpr himageInj, ?_⟩
  rw [IsMatching, Finset.coe_image]
  apply himageInj.pairwiseDisjoint_image.mpr
  intro S hS D hD hSD
  have hdisj := hmatching hS hD hSD
  simp only [Function.onFun, Function.comp_apply, id_eq]
  rw [Finset.disjoint_left]
  intro x hxS hxD
  obtain ⟨b, hbS, hpb⟩ := Finset.mem_image.mp hxS
  obtain ⟨d, hdD, hpd⟩ := Finset.mem_image.mp hxD
  have hbd : b = d := hpInj
    (hsystemsB S hS (Finset.mem_coe.mpr hbS))
    (hsystemsB D hD (Finset.mem_coe.mpr hdD))
    (hpb.trans hpd.symm)
  exact Finset.disjoint_left.mp hdisj hbS (hbd ▸ hdD)

/-- The choice-sensitive certificate bridge and the three-point counting
bound combine to limit the number of pairwise-disjoint petal batches which
simultaneously provide alignment-free crossing endpoints for every target
destroyed by `B`. -/
theorem card_pairwiseDisjoint_coveringEndpointPetalBatches_le
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    {systems : Finset (Finset ℕ)}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hsystemsB : ∀ S ∈ systems, ∀ b ∈ S, b ∈ B)
    (hpair : IsMatching (systems.image fun S => S.image p))
    (hcover : ∀ S ∈ systems, ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ b ∈ S, ∃ c ∈ A \ B,
        b + c = q ∧ c ∉ p '' (S : Set ℕ)) :
    (systems.image fun S => S.image p).card ≤ 3 * Q.card := by
  apply card_pairwiseDisjoint_externalEssentialBatches_le
    hrepresented hpair
  intro T hT
  obtain ⟨S, hSsystems, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨q, hqQ, _hqA, hqBlue, hqEssential⟩ :=
    finiteCertificate_forces_externalPetalEssential_of_coveringEndpoints
      hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
        (hsystemsB S hSsystems) (hcover S hSsystems)
  refine ⟨q, hqQ, hqBlue, ?_⟩
  intro H hHR hHB
  simpa only [Finset.coe_image] using hqEssential H hHR hHB

/-- Direct atom-batch form of the finite obstruction.  No more than
`3 * Q.card` pairwise-disjoint endpoint systems can all cover every
`B`-destroyed certificate target with an alignment-free crossing pair. -/
theorem card_pairwiseDisjoint_coveringEndpointSystems_le
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    {systems : Finset (Finset ℕ)}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hsystemsB : ∀ S ∈ systems, ∀ b ∈ S, b ∈ B)
    (hmatching : IsMatching systems)
    (hcover : ∀ S ∈ systems, ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ b ∈ S, ∃ c ∈ A \ B,
        b + c = q ∧ c ∉ p '' (S : Set ℕ)) :
    systems.card ≤ 3 * Q.card := by
  have hsystemsB' : ∀ S ∈ systems, (S : Set ℕ) ⊆ B := by
    intro S hS b hb
    exact hsystemsB S hS b (Finset.mem_coe.mp hb)
  have himage := petalBatchImages_card_eq_and_matching
    (repairPetalMap_injOn hpetalDisjoint (fun b hb => (hp b hb).1))
    hsystemsB' hmatching
  rw [← himage.1]
  exact card_pairwiseDisjoint_coveringEndpointPetalBatches_le
    hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
      hrepresented hsystemsB himage.2 hcover

/-- Alignment-free transversal form of the endpoint-system bound.  Each
atom batch need only contain some crossing atom endpoint for every target
destroyed by `B`; excluding all internal equations `q = b + p d` then turns
those endpoints into the alignment-free covers required above. -/
theorem card_pairwiseDisjoint_alignmentFreeCrossingTransversals_le
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    {systems : Finset (Finset ℕ)}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hsystemsB : ∀ S ∈ systems, ∀ b ∈ S, b ∈ B)
    (hmatching : IsMatching systems)
    (hcrossingCover : ∀ S ∈ systems, ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q)
    (halignmentFree : ∀ S ∈ systems, ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∀ b ∈ S, ∀ d ∈ S, b + p d ≠ q) :
    systems.card ≤ 3 * Q.card := by
  apply card_pairwiseDisjoint_coveringEndpointSystems_le
    hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
      hrepresented hsystemsB hmatching
  intro S hS q hqQ hqDestroy
  obtain ⟨b, hbS, c, hcC, hbc⟩ :=
    hcrossingCover S hS q hqQ hqDestroy
  refine ⟨b, hbS, c, hcC, hbc, ?_⟩
  rintro ⟨d, hdS, hpd⟩
  apply halignmentFree S hS q hqQ hqDestroy b hbS d
    (Finset.mem_coe.mp hdS)
  omega

set_option maxHeartbeats 5000000 in
/-- High crossing-endpoint multiplicity is forced into the arithmetic
alignment branch.  Hall's theorem builds `3 * Q.card + 1` pairwise-disjoint
systems, each meeting the crossing-endpoint set of every target destroyed by
`B`.  The finite-certificate count then says that at least one such system
contains an equation `q = b + p d`. -/
theorem many_crossingEndpoints_force_aligned_coveringSystem
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hmanyEndpoints : ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      (3 * Q.card + 1) *
          (destroyedCertificateTargets A B Q).card ≤
        (crossingAtomEndpoints A B q).card) :
    ∃ systems : Finset (Finset ℕ),
      systems.card = 3 * Q.card + 1 ∧
      IsMatching systems ∧
      (∀ S ∈ systems,
        (∀ b ∈ S, b ∈ B) ∧
        ∀ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q →
          ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q) ∧
      ∃ S ∈ systems, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q ∧
        ∃ b ∈ S, ∃ d ∈ S, b + p d = q := by
  classical
  let atomSelector : BlockSelector F := fun i =>
    ⟨(e i).1, hcore i (by
      rw [externalCliqueCell]
      exact Finset.mem_insert_self _ _)⟩
  have hselectedAtom : selectedSet atomSelector = B := by
    ext b
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hbB
      obtain ⟨i, hi⟩ := e.surjective ⟨b, hbB⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q₀, hq₀Q, hq₀DestroySelector⟩ := hcert atomSelector
  have hq₀Destroy :
      DestroysAt (additiveSupportFamily A 3) B q₀ := by
    simpa [hselectedAtom] using hq₀DestroySelector
  let D : Finset ℕ := destroyedCertificateTargets A B Q
  have hD : D.Nonempty :=
    ⟨q₀, mem_destroyedCertificateTargets_iff.mpr
      ⟨hq₀Q, hq₀Destroy⟩⟩
  have hlarge : ∀ q ∈ D,
      (3 * Q.card + 1) * D.card ≤
        (crossingAtomEndpoints A B q).card := by
    intro q hqD
    have hq := mem_destroyedCertificateTargets_iff.mp hqD
    exact hmanyEndpoints q hq.1 hq.2
  obtain ⟨systems, hsystemsCard, hmatching, hsystems⟩ :=
    exists_matching_coveringSystems_of_uniform_card hD hlarge
  have hsystemsData : ∀ S ∈ systems,
      (∀ b ∈ S, b ∈ B) ∧
      ∀ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q →
        ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q := by
    intro S hS
    have hSdata := hsystems S hS
    constructor
    · intro b hbS
      obtain ⟨q, hqD, hbEndpoint⟩ :=
        Finset.mem_biUnion.mp (hSdata.1 hbS)
      exact (mem_crossingAtomEndpoints_iff.mp hbEndpoint).2.1
    · intro q hqQ hqDestroy
      have hqD : q ∈ D :=
        mem_destroyedCertificateTargets_iff.mpr ⟨hqQ, hqDestroy⟩
      obtain ⟨b, hbS, hbEndpoint⟩ := hSdata.2 q hqD
      have hbData := mem_crossingAtomEndpoints_iff.mp hbEndpoint
      exact ⟨b, hbS, q - b, hbData.2.2,
        crossingAtomEndpoint_sum hbEndpoint⟩
  have haligned : ∃ S ∈ systems, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q ∧
      ∃ b ∈ S, ∃ d ∈ S, b + p d = q := by
    by_contra hnone
    have halignmentFree : ∀ S ∈ systems, ∀ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q →
        ∀ b ∈ S, ∀ d ∈ S, b + p d ≠ q := by
      intro S hS q hqQ hqDestroy b hbS d hdS hEq
      exact hnone ⟨S, hS, q, hqQ, hqDestroy,
        b, hbS, d, hdS, hEq⟩
    have hle :=
      card_pairwiseDisjoint_alignmentFreeCrossingTransversals_le
        hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
          hrepresented
          (fun S hS => (hsystemsData S hS).1)
          hmatching
          (fun S hS => (hsystemsData S hS).2)
          halignmentFree
    omega
  exact ⟨systems, hsystemsCard, hmatching, hsystemsData, haligned⟩

set_option maxHeartbeats 5000000 in
/-- Exact bounded-endpoint/high-alignment dichotomy for one finite
certificate.  Either a target destroyed by `B` has fewer than the crude Hall
threshold of crossing atom endpoints, or the high-multiplicity construction
above produces `3 * Q.card + 1` disjoint covering systems and a certified
cross-alignment inside one of them. -/
theorem finiteCertificate_forces_boundedEndpoints_or_highAlignment
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty) :
    (∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q ∧
      (crossingAtomEndpoints A B q).card <
        (3 * Q.card + 1) *
          (destroyedCertificateTargets A B Q).card) ∨
    ∃ systems : Finset (Finset ℕ),
      systems.card = 3 * Q.card + 1 ∧
      IsMatching systems ∧
      (∀ S ∈ systems,
        (∀ b ∈ S, b ∈ B) ∧
        ∀ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q →
          ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q) ∧
      ∃ S ∈ systems, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q ∧
        ∃ b ∈ S, ∃ d ∈ S, b + p d = q := by
  classical
  by_cases hsmall : ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q ∧
      (crossingAtomEndpoints A B q).card <
        (3 * Q.card + 1) *
          (destroyedCertificateTargets A B Q).card
  · exact Or.inl hsmall
  · right
    apply many_crossingEndpoints_force_aligned_coveringSystem
      hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
        hrepresented
    intro q hqQ hqDestroy
    by_contra hnotle
    exact hsmall ⟨q, hqQ, hqDestroy, Nat.lt_of_not_ge hnotle⟩

set_option maxHeartbeats 5000000 in
/-- Arithmetic form of the preceding dichotomy.  Zero retention and direct
triple repairs make every order-two support at a `B`-destroyed target cross
the boundary, so the bounded endpoint count is exactly a bounded pair-support
count. -/
theorem finiteCertificate_forces_boundedPairSupports_or_highAlignment
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty) :
    (∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q ∧
      (additiveSupportFamily A 2 q).card <
        (3 * Q.card + 1) *
          (destroyedCertificateTargets A B Q).card) ∨
    ∃ systems : Finset (Finset ℕ),
      systems.card = 3 * Q.card + 1 ∧
      IsMatching systems ∧
      (∀ S ∈ systems,
        (∀ b ∈ S, b ∈ B) ∧
        ∀ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q →
          ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q) ∧
      ∃ S ∈ systems, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q ∧
        ∃ b ∈ S, ∃ d ∈ S, b + p d = q := by
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  obtain hbounded | haligned :=
    finiteCertificate_forces_boundedEndpoints_or_highAlignment
      hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
        hrepresented
  · left
    obtain ⟨q, hqQ, hqDestroy, hqBound⟩ := hbounded
    have hcross :=
      orderTwoSupports_crossing_of_zero_directRepairs_destroyer
        hzeroA hzeroB hrepairs hqDestroy
    refine ⟨q, hqQ, hqDestroy, ?_⟩
    rw [card_pairSupports_eq_card_crossingAtomEndpoints hBA hcross]
    exact hqBound
  · exact Or.inr haligned

/-- Contrapositive finite-incidence obstruction.  In any family of more than
`3 * Q.card` pairwise-disjoint atom batches, some batch and some target
destroyed by `B` have no alignment-free crossing endpoint inside that batch:
every available complement is one of the same batch's selected petals. -/
theorem exists_batch_with_only_aligned_coveringEndpoints
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    {systems : Finset (Finset ℕ)}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty)
    (hsystemsB : ∀ S ∈ systems, ∀ b ∈ S, b ∈ B)
    (hmatching : IsMatching systems)
    (hmany : 3 * Q.card < systems.card) :
    ∃ S ∈ systems, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q ∧
      ∀ b ∈ S, ∀ c ∈ A \ B,
        b + c = q → c ∈ p '' (S : Set ℕ) := by
  classical
  by_contra hnone
  have hcover : ∀ S ∈ systems, ∀ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) B q →
      ∃ b ∈ S, ∃ c ∈ A \ B,
        b + c = q ∧ c ∉ p '' (S : Set ℕ) := by
    intro S hS q hqQ hqDestroy
    by_contra hnoCover
    apply hnone
    refine ⟨S, hS, q, hqQ, hqDestroy, ?_⟩
    intro b hbS c hcC hsum
    by_contra hcPetal
    exact hnoCover ⟨b, hbS, c, hcC, hsum, hcPetal⟩
  have hle := card_pairwiseDisjoint_coveringEndpointSystems_le
    hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
      hrepresented hsystemsB hmatching hcover
  omega

set_option maxHeartbeats 5000000 in
/-- Simultaneously repair every certificate target destroyed by the atom
selector.  Either one chosen crossing complement is itself one of the
selected petals (a cross-alignment equation `q = b + p d`), or the
certificate is forced onto a new external target not destroyed by `B`; every
`B`-surviving triple support of that target must hit the finite selected
petal set. -/
theorem finiteCertificate_forces_crossAlignment_or_externalPetalEssential
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hpair : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty) :
    ∃ S : Finset ℕ,
      S.Nonempty ∧ (∀ b ∈ S, b ∈ B) ∧
      ((∃ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q ∧
          ∃ b ∈ S, ∃ d ∈ S, b + p d = q) ∨
        ∃ q' ∈ Q, q' ∉ A ∧
          ¬ DestroysAt (additiveSupportFamily A 3) B q' ∧
          ∀ H ∈ additiveSupportFamily A 3 q',
            Disjoint (H : Set ℕ) B →
            ¬ Disjoint (H : Set ℕ) (p '' (S : Set ℕ))) := by
  classical
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  let atomSelector : BlockSelector F := fun i =>
    ⟨(e i).1, hcore i (by
      rw [externalCliqueCell]
      exact Finset.mem_insert_self _ _)⟩
  have hselectedAtom : selectedSet atomSelector = B := by
    ext b
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hbB
      obtain ⟨i, hi⟩ := e.surjective ⟨b, hbB⟩
      refine ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q₀, hq₀Q, hq₀destroyS⟩ := hcert atomSelector
  have hq₀destroy :
      DestroysAt (additiveSupportFamily A 3) B q₀ := by
    simpa [hselectedAtom] using hq₀destroyS
  let D : Finset ℕ := Q.filter fun q =>
    DestroysAt (additiveSupportFamily A 3) B q
  have hq₀D : q₀ ∈ D :=
    Finset.mem_filter.mpr ⟨hq₀Q, hq₀destroy⟩
  have hD : D.Nonempty := ⟨q₀, hq₀D⟩
  have hendpoints : ∀ q : {q // q ∈ D},
      ∃ b ∈ B, ∃ c ∈ A \ B, b + c = q.1 := by
    intro q
    have hqQ : q.1 ∈ Q := (Finset.mem_filter.mp q.2).1
    have hqDestroy := (Finset.mem_filter.mp q.2).2
    obtain ⟨E, hER⟩ := hpair q.1 hqQ
    have hcross :=
      orderTwoSupports_crossing_of_zero_directRepairs_destroyer
        hzeroA hzeroB hrepairs hqDestroy E hER
    obtain ⟨b, hbB, c, hcC, hbc, _hEbc⟩ :=
      exists_endpoints_of_crossingPairSupport hER hcross.1 hcross.2
    exact ⟨b, hbB, c, hcC, hbc⟩
  choose atom hatomB complement hcomplementC hsum using hendpoints
  let S : Finset ℕ := D.attach.image atom
  have hSB : ∀ b ∈ S, b ∈ B := by
    intro b hbS
    obtain ⟨q, _hqAttach, rfl⟩ := Finset.mem_image.mp hbS
    exact hatomB q
  have hS : S.Nonempty := by
    obtain ⟨q, hqD⟩ := hD
    exact ⟨atom ⟨q, hqD⟩,
      Finset.mem_image.mpr ⟨⟨q, hqD⟩, by simp, rfl⟩⟩
  by_cases halign : ∃ q : {q // q ∈ D},
      complement q ∈ p '' (S : Set ℕ)
  · obtain ⟨q, d, hdS, hpd⟩ := halign
    refine ⟨S, hS, hSB, Or.inl ⟨q.1,
      (Finset.mem_filter.mp q.2).1,
      (Finset.mem_filter.mp q.2).2,
      atom q, ?_, d, Finset.mem_coe.mp hdS, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨q, by simp, rfl⟩
    · have hsumq := hsum q
      omega
  · obtain ⟨s, hsSub, hremoved, _hpetalsSelected⟩ :=
      exists_finitePetalOverrideSelector
        havoid (fun b hb => (hp b hb).1) hcore S hSB
    have hDsurvives : ∀ q ∈ D,
        ∃ G ∈ additiveSupportFamily A 3 q,
          Disjoint (G : Set ℕ) (selectedSet s) := by
      intro q hqD
      let qsub : {q // q ∈ D} := ⟨q, hqD⟩
      have hbA : atom qsub ∈ A := hBA (hatomB qsub)
      have hcA : complement qsub ∈ A := (hcomplementC qsub).1
      have hpairR : pairSupport q (atom qsub) ∈
          additiveSupportFamily A 2 q := by
        have hble : atom qsub ≤ q := by
          have hsum' := hsum qsub
          change atom qsub + complement qsub = q at hsum'
          omega
        apply pairSupport_mem_additiveSupportFamily hble hbA
        have hsub : q - atom qsub = complement qsub := by
          have hsum' := hsum qsub
          change atom qsub + complement qsub = q at hsum'
          omega
        simpa [hsub] using hcA
      let G : Finset ℕ := insert 0 (pairSupport q (atom qsub))
      have hGR : G ∈ additiveSupportFamily A 3 q := by
        simpa [G] using
          (insert_mem_additiveSupportFamily_succ hzeroA hpairR)
      refine ⟨G, hGR, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxSelected
      have hsub : q - atom qsub = complement qsub := by
        have hsum' := hsum qsub
        change atom qsub + complement qsub = q at hsum'
        omega
      have hx : x = 0 ∨ x = atom qsub ∨ x = complement qsub := by
        simpa [G, pairSupport, hsub] using (Finset.mem_coe.mp hxG)
      rcases hx with rfl | rfl | rfl
      · rcases hsSub hxSelected with h0B | ⟨d, hdS, hpd⟩
        · exact hzeroB h0B
        · have hdB := hSB d (Finset.mem_coe.mp hdS)
          obtain ⟨w, hfw⟩ := hwitness d hdB
          have hp0 : p d ≠ 0 := by
            intro hp0
            have hpV : p d ∈ w.vertices := by
              rw [← hfw]
              exact Finset.sdiff_subset (hp d hdB).1
            exact w.zero_not_mem_vertices (hp0 ▸ hpV)
          exact hp0 hpd
      · exact hremoved (atom qsub)
          (Finset.mem_image.mpr ⟨qsub, by simp, rfl⟩) hxSelected
      · rcases hsSub hxSelected with hcB | hcPetal
        · exact (hcomplementC qsub).2 hcB
        · exact halign ⟨qsub, hcPetal⟩
    obtain ⟨q', hq'Q, hq'destroy⟩ := hcert s
    have hq'NotD : q' ∉ D := by
      intro hq'D
      obtain ⟨G, hGR, hGblue⟩ := hDsurvives q' hq'D
      exact (hq'destroy G hGR) hGblue
    have hq'NotDestroyB :
        ¬ DestroysAt (additiveSupportFamily A 3) B q' := by
      intro hdestroyB
      exact hq'NotD (Finset.mem_filter.mpr ⟨hq'Q, hdestroyB⟩)
    have hq'NotA : q' ∉ A := by
      intro hq'A
      obtain ⟨G, hGR, hGblue⟩ :=
        internalTarget_survives_finitePetalOverride
          hzeroA hwitness havoid hpetalDisjoint hp hg
          hSB hsSub hremoved q' hq'A
      exact (hq'destroy G hGR) hGblue
    refine ⟨S, hS, hSB, Or.inr
      ⟨q', hq'Q, hq'NotA, hq'NotDestroyB, ?_⟩⟩
    intro H hHR hHB
    obtain ⟨x, hxH, hxSelected⟩ :=
      Set.not_disjoint_iff.mp (hq'destroy H hHR)
    rcases hsSub hxSelected with hxB | hxPetal
    · exact (Set.disjoint_left.mp hHB hxH hxB).elim
    · exact Set.not_disjoint_iff.mpr ⟨x, hxH, hxPetal⟩

/-- Specializing the override to a nonempty sunflower petal gives the exact
new residual: either the chosen petal point is the complementary endpoint of
the crossing pair, or the finite certificate migrates to a different target
after overriding that atom's block. -/
theorem certificate_forces_petalAlignment_or_targetMigration
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetal : ∀ b ∈ B, (f b \ R).Nonempty)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    {q : ℕ} {E : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hcross : ¬ Disjoint (E : Set ℕ) B ∧
      ¬ (E : Set ℕ) ⊆ B) :
    ∃ b ∈ B, ∃ c ∈ A \ B, ∃ i, (e i).1 = b ∧
      b + c = q ∧
      ∃ p ∈ f b \ R,
        p = c ∨
          ∃ q' ∈ Q, q' ≠ q ∧
            ∃ s : BlockSelector F,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet s) q' ∧
              selectedSet s ⊆ insert p B ∧
              p ∈ selectedSet s ∧
              b ∉ selectedSet s ∧
              ∃ G ∈ additiveSupportFamily A 3 q,
                Disjoint (G : Set ℕ) (selectedSet s) := by
  classical
  obtain ⟨b, hbB, c, hcC, hbc, _hEbc⟩ :=
    exists_endpoints_of_crossingPairSupport hER hcross.1 hcross.2
  obtain ⟨i, hi⟩ := e.surjective ⟨b, hbB⟩
  have hbi : (e i).1 = b := congrArg Subtype.val hi
  obtain ⟨p, hpPetal⟩ := hpetal b hbB
  obtain ⟨w, hfw⟩ := hwitness b hbB
  have hpF : p ∈ F i := by
    apply hcore i
    rw [externalCliqueCell, hbi]
    exact Finset.mem_insert_of_mem hpPetal
  have hatom : ∀ j, (e j).1 ∈ F j := by
    intro j
    apply hcore j
    rw [externalCliqueCell]
    exact Finset.mem_insert_self _ _
  have hpA : p ∈ A := by
    apply w.vertices_subset
    rw [← hfw]
    exact Finset.sdiff_subset hpPetal
  have hpB : p ∉ B := by
    intro hpB
    exact Set.disjoint_left.mp (havoid b hbB)
      (Finset.sdiff_subset hpPetal) hpB
  have hppos : 0 < p := by
    have hp0 : p ≠ 0 := by
      intro hp0
      subst p
      apply w.zero_not_mem_vertices
      rw [← hfw]
      exact Finset.sdiff_subset hpPetal
    omega
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  refine ⟨b, hbB, c, hcC, i, hbi, hbc, p, hpPetal, ?_⟩
  by_cases hpc : p = c
  · exact Or.inl hpc
  · exact Or.inr <|
      certificate_moves_after_singleCellOverride
        hBA hzeroA hzeroB e hatom hbi hpF ⟨hpA, hpB⟩ hppos
        hcC hbc hpc hcert

/-- With the self-repaired distinguished petals, the migrated certificate
target cannot be internal.  Thus every crossing target either aligns its
retained endpoint exactly with the distinguished petal, or overriding its
atom forces a different *external* target.  If that external target was not
already destroyed by `B`, every `B`-surviving triple support of it must use
the distinguished petal. -/
theorem certificate_forces_petalAlignment_or_externalTargetMigration
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    {q : ℕ} {E : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hcross : ¬ Disjoint (E : Set ℕ) B ∧
      ¬ (E : Set ℕ) ⊆ B) :
    ∃ b ∈ B, ∃ c ∈ A \ B, ∃ i, (e i).1 = b ∧
      b + c = q ∧
      (p b = c ∨
        ∃ q' ∈ Q, q' ≠ q ∧ q' ∉ A ∧
          ∃ s : BlockSelector F,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q' ∧
            selectedSet s ⊆ insert (p b) B ∧
            p b ∈ selectedSet s ∧
            b ∉ selectedSet s ∧
            (¬ DestroysAt (additiveSupportFamily A 3) B q' →
              ∀ H ∈ additiveSupportFamily A 3 q',
                Disjoint (H : Set ℕ) B → p b ∈ H) ∧
            ∃ G ∈ additiveSupportFamily A 3 q,
              Disjoint (G : Set ℕ) (selectedSet s)) := by
  classical
  obtain ⟨b, hbB, c, hcC, hbc, _hEbc⟩ :=
    exists_endpoints_of_crossingPairSupport hER hcross.1 hcross.2
  obtain ⟨i, hi⟩ := e.surjective ⟨b, hbB⟩
  have hbi : (e i).1 = b := congrArg Subtype.val hi
  have hpPetal := (hp b hbB).1
  obtain ⟨w, hfw⟩ := hwitness b hbB
  have hpF : p b ∈ F i := by
    apply hcore i
    rw [externalCliqueCell, hbi]
    exact Finset.mem_insert_of_mem hpPetal
  have hatom : ∀ j, (e j).1 ∈ F j := by
    intro j
    apply hcore j
    rw [externalCliqueCell]
    exact Finset.mem_insert_self _ _
  have hpA : p b ∈ A := by
    apply w.vertices_subset
    rw [← hfw]
    exact Finset.sdiff_subset hpPetal
  have hpB : p b ∉ B := by
    intro hpB
    exact Set.disjoint_left.mp (havoid b hbB)
      (Finset.sdiff_subset hpPetal) hpB
  have hppos : 0 < p b := by
    have hp0 : p b ≠ 0 := by
      intro hp0
      apply w.zero_not_mem_vertices
      rw [← hfw, ← hp0]
      exact Finset.sdiff_subset hpPetal
    omega
  have hzeroB : 0 ∉ B := by
    intro h0B
    obtain ⟨w0, _hfw0⟩ := hwitness 0 h0B
    exact (Nat.ne_of_gt w0.atom_pos) rfl
  refine ⟨b, hbB, c, hcC, i, hbi, hbc, ?_⟩
  by_cases hpc : p b = c
  · exact Or.inl hpc
  · right
    obtain ⟨q', hq'Q, hq'q, s, hq'destroy,
        hsSub, hpS, hbNotS, G, hGR, hGblue⟩ :=
      certificate_moves_after_singleCellOverride
        hBA hzeroA hzeroB e hatom hbi hpF ⟨hpA, hpB⟩ hppos
        hcC hbc hpc hcert
    have hq'notA : q' ∉ A := by
      intro hq'A
      have hq'p :=
        internal_destroyer_of_singlePetalOverride_eq_petal
          hzeroA hzeroB hwitness havoid hpetalDisjoint
          hbB hpPetal hppos hsSub hbNotS hq'destroy hq'A
      subst q'
      have hgBlue : Disjoint (g b : Set ℕ) (selectedSet s) := by
        rw [Set.disjoint_left]
        intro x hxG hxS
        rcases hsSub hxS with hxp | hxB
        · subst x
          exact (hg b hbB).2.1 (Finset.mem_coe.mp hxG)
        · exact Set.disjoint_left.mp (hg b hbB).2.2 hxG hxB
      exact (hq'destroy (g b) (hg b hbB).1) hgBlue
    refine ⟨q', hq'Q, hq'q, hq'notA, s, hq'destroy,
      hsSub, hpS, hbNotS, ?_, G, hGR, hGblue⟩
    intro hnotDestroyB H hHR hHB
    exact petal_mem_of_overrideDestroyer_of_atomAvoidingSupport
      hsSub hq'destroy H hHR hHB

/-- Packaged finite residual produced by the self-repaired petal override. -/
def HasPetalAlignmentOrExternalMigration
    (A B : Set ℕ) (p : ℕ → ℕ)
    (e : ℕ ≃ B) (F : ℕ → Finset ℕ)
    (Q : Finset ℕ) (q : ℕ) : Prop :=
  ∃ b ∈ B, ∃ c ∈ A \ B, ∃ i, (e i).1 = b ∧
    b + c = q ∧
    (p b = c ∨
      ∃ q' ∈ Q, q' ≠ q ∧ q' ∉ A ∧
        ∃ s : BlockSelector F,
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet s) q' ∧
          selectedSet s ⊆ insert (p b) B ∧
          p b ∈ selectedSet s ∧
          b ∉ selectedSet s ∧
          (¬ DestroysAt (additiveSupportFamily A 3) B q' →
            ∀ H ∈ additiveSupportFamily A 3 q',
              Disjoint (H : Set ℕ) B → p b ∈ H) ∧
          ∃ G ∈ additiveSupportFamily A 3 q,
            Disjoint (G : Set ℕ) (selectedSet s))

theorem hasPetalAlignmentOrExternalMigration_of_crossingSupport
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hBA : B ⊆ A)
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    {q : ℕ} {E : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hcross : ¬ Disjoint (E : Set ℕ) B ∧
      ¬ (E : Set ℕ) ⊆ B) :
    HasPetalAlignmentOrExternalMigration A B p e F Q q :=
  certificate_forces_petalAlignment_or_externalTargetMigration
    hBA hzeroA hwitness havoid hpetalDisjoint hp hg
      hcore hcert hER hcross

set_option maxHeartbeats 5000000 in
/-- The combined certificate can be chosen on the self-repaired petal
reservoir.  Its actual atom destroyer therefore carries the packaged
alignment-or-external-migration residual, while every pair-support choice on
the same `Q` still covers arbitrarily many sunflower cells. -/
theorem exists_certifiedCoveredSelfRepairedPetalTargets
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hBA : B ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q) ∧
      (∃ q ∈ Q, q ∉ A ∧
        DestroysAt (additiveSupportFamily A 3) B q ∧
        ∃ E ∈ additiveSupportFamily A 2 q,
          (¬ Disjoint (E : Set ℕ) B ∧
            ¬ (E : Set ℕ) ⊆ B) ∧
          HasPetalAlignmentOrExternalMigration
            A B p e F Q q) ∧
      ∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I,
            externalCliqueCell R f (e i).1 ⊆
              finiteSupportChoiceUnion c := by
  intro M start N
  obtain ⟨Q, hQN, hcert, hexternal, hmany⟩ :=
    exists_certifiedCoveredSunflowerTargets
      hbasis hzeroA hcounter P hrepairs hwitness havoid hcore
      M start N
  obtain ⟨q, hqQ, hqA, hdestroy, E, hER, hcross⟩ := hexternal
  have hmigrate : HasPetalAlignmentOrExternalMigration
      A B p e F Q q :=
    hasPetalAlignmentOrExternalMigration_of_crossingSupport
      hBA hzeroA hwitness havoid hpetalDisjoint hp hg
        hcore hcert hER hcross
  exact ⟨Q, hQN, hcert,
    ⟨q, hqQ, hqA, hdestroy, E, hER, hcross, hmigrate⟩,
    hmany⟩

set_option maxHeartbeats 5000000 in
/-- Batch form of the exact finite bridge.  The same amplified certificate
`Q` has represented order-two targets, forces arbitrarily many covered
sunflower cells, and satisfies the simultaneous-override dichotomy between a
cross-alignment equation and a new external petal-essential target. -/
theorem exists_certifiedCoveredBatchPetalObstruction
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hBA : B ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i) :
    ∀ M start N, ∃ Q : Finset ℕ, ∃ S : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ q ∈ Q, (additiveSupportFamily A 2 q).Nonempty) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q) ∧
      S.Nonempty ∧ (∀ b ∈ S, b ∈ B) ∧
      ((∃ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q ∧
          ∃ b ∈ S, ∃ d ∈ S, b + p d = q) ∨
        ∃ q' ∈ Q, q' ∉ A ∧
          ¬ DestroysAt (additiveSupportFamily A 3) B q' ∧
          ∀ H ∈ additiveSupportFamily A 3 q',
            Disjoint (H : Set ℕ) B →
            ¬ Disjoint (H : Set ℕ) (p '' (S : Set ℕ))) ∧
      (∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I,
            externalCliqueCell R f (e i).1 ⊆
              finiteSupportChoiceUnion c) ∧
      ∀ systems : Finset (Finset ℕ),
        (∀ T ∈ systems, ∀ b ∈ T, b ∈ B) →
        IsMatching systems →
        (∀ T ∈ systems, ∀ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q →
          ∃ b ∈ T, ∃ c ∈ A \ B,
            b + c = q ∧ c ∉ p '' (T : Set ℕ)) →
        systems.card ≤ 3 * Q.card := by
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro M start N
  obtain ⟨Q, hQlate, hcert, _hexternal, hmany⟩ :=
    exists_certifiedCoveredSelfRepairedPetalTargets
      hbasis hzeroA hcounter P hBA hrepairs hwitness havoid
        hpetalDisjoint hp
        (fun b hb => ⟨(hg b hb).1, (hg b hb).2.1,
          (hg b hb).2.2.1⟩)
        hcore M start (max N N₂)
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hq
    exact (le_max_left N N₂).trans (hQlate q hq)
  have hpair : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hq
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQlate q hq))
    exact ⟨E, hER⟩
  obtain ⟨S, hS, hSB, hdichotomy⟩ :=
    finiteCertificate_forces_crossAlignment_or_externalPetalEssential
      hBA hzeroA hrepairs hwitness havoid hpetalDisjoint
        hp hg hcore hcert hpair
  have htriple : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty := by
    intro q hq
    obtain ⟨E, hER⟩ := hpair q hq
    exact ⟨insert 0 E,
      by simpa using
        (insert_mem_additiveSupportFamily_succ hzeroA hER)⟩
  have hsystemBound : ∀ systems : Finset (Finset ℕ),
      (∀ T ∈ systems, ∀ b ∈ T, b ∈ B) →
      IsMatching systems →
      (∀ T ∈ systems, ∀ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) B q →
        ∃ b ∈ T, ∃ c ∈ A \ B,
          b + c = q ∧ c ∉ p '' (T : Set ℕ)) →
      systems.card ≤ 3 * Q.card := by
    intro systems hsystemsB hmatching hcover
    exact card_pairwiseDisjoint_coveringEndpointSystems_le
      hBA hzeroA hwitness havoid hpetalDisjoint hp hg hcore hcert
        htriple hsystemsB hmatching hcover
  exact ⟨Q, S, hQN, hpair, hcert, hS, hSB,
    hdichotomy, hmany, hsystemBound⟩

set_option maxHeartbeats 5000000 in
/-- Any order-three selector certificate on the sunflower partition already
forces one whole sunflower cell into the union of every chosen family of pair
supports.  Pad the pairs by zero, apply certificate duality, and remove the
padding because no sunflower cell contains zero. -/
theorem exists_coveredSunflowerCell_of_tripleCertificate_and_pairChoice
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q) :
    ∃ i, externalCliqueCell R f (e i).1 ⊆
      finiteSupportChoiceUnion c := by
  classical
  have hcellZero : ∀ i,
      0 ∉ externalCliqueCell R f (e i).1 := by
    intro i h0cell
    obtain ⟨w, hfw⟩ := hwitness (e i).1 (e i).2
    rcases Finset.mem_insert.mp h0cell with h0b | h0petal
    · exact (Nat.ne_of_gt w.atom_pos) h0b.symm
    · apply w.zero_not_mem_vertices
      rw [← hfw]
      exact Finset.sdiff_subset h0petal
  let c₃ : FiniteSupportChoice (additiveSupportFamily A 3) Q :=
    fun q =>
      ⟨insert 0 (c q).1, by simpa using
        (insert_mem_additiveSupportFamily_succ hzeroA (c q).2)⟩
  obtain ⟨i, hiCover⟩ :=
    exists_block_subset_supportChoiceUnion_of_certificate hcert c₃
  refine ⟨i, ?_⟩
  intro x hxCell
  have hxU₃ := hiCover (hcore i hxCell)
  obtain ⟨q, _hqAttach, hxSupport⟩ :=
    Finset.mem_biUnion.mp hxU₃
  change x ∈ insert 0 (c q).1 at hxSupport
  rcases Finset.mem_insert.mp hxSupport with hx0 | hxPair
  · subst x
    exact (hcellZero i hxCell).elim
  · exact finiteSupportChoice_subset_union c q hxPair

/-- Incidence-only consequence of sunflower-cell coverage: every pair-support
choice for a triple selector certificate contains both some atom `b` and its
distinguished petal `p b`. -/
theorem exists_atom_and_petal_in_pairChoiceUnion_of_tripleCertificate
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q) :
    ∃ b ∈ B,
      b ∈ finiteSupportChoiceUnion c ∧
      p b ∈ finiteSupportChoiceUnion c := by
  obtain ⟨i, hiCover⟩ :=
    exists_coveredSunflowerCell_of_tripleCertificate_and_pairChoice
      hzeroA hwitness hcore hcert c
  let b := (e i).1
  have hbCell : b ∈ externalCliqueCell R f b := by
    exact Finset.mem_insert_self _ _
  have hpCell : p b ∈ externalCliqueCell R f b := by
    rw [externalCliqueCell]
    exact Finset.mem_insert_of_mem (hp b (e i).2)
  exact ⟨b, (e i).2, hiCover hbCell, hiCover hpCell⟩

/-- Target-indexed form of the same incidence: the atom and its petal each
occur in one of the selected pair supports, possibly at different certified
targets. -/
theorem exists_atomPetal_supportIncidences_of_tripleCertificate
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q) :
    ∃ b ∈ B, ∃ q : {n // n ∈ Q}, ∃ r : {n // n ∈ Q},
      b ∈ (c q).1 ∧ p b ∈ (c r).1 := by
  obtain ⟨b, hbB, hbU, hpU⟩ :=
    exists_atom_and_petal_in_pairChoiceUnion_of_tripleCertificate
      hzeroA hwitness hp hcore hcert c
  obtain ⟨q, _hqAttach, hbq⟩ := Finset.mem_biUnion.mp hbU
  obtain ⟨r, _hrAttach, hpr⟩ := Finset.mem_biUnion.mp hpU
  exact ⟨b, hbB, q, r, hbq, hpr⟩

set_option maxHeartbeats 5000000 in
/-- Greedy avoidance for pair-support choices.  If every target has more than
`2 * Q.card` pair supports and no individual support already contains an
atom together with its petal, choose the supports successively.  The partners
of the previously chosen union form a forbidden set of cardinality at most
`2 * Q.card`; since each pair-support family is a matching, the next target
has a support avoiding it.  The final union contains no atom-petal pair. -/
theorem exists_pairSupportChoice_avoiding_atomPetal_of_large_noDiagonal
    {A B : Set ℕ} {p : ℕ → ℕ} {Q : Finset ℕ}
    (hpOut : ∀ b ∈ B, p b ∉ B)
    (hpInj : Set.InjOn p B)
    (hlarge : ∀ q ∈ Q,
      2 * Q.card < (additiveSupportFamily A 2 q).card)
    (hnoDiagonal : ∀ q ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 q,
      ∀ b ∈ B, ¬ (b ∈ E ∧ p b ∈ E)) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∀ b ∈ B,
        ¬ (b ∈ finiteSupportChoiceUnion c ∧
          p b ∈ finiteSupportChoiceUnion c) := by
  classical
  revert hlarge hnoDiagonal
  induction Q using Finset.induction_on with
  | empty =>
      intro _hlarge _hnoDiagonal
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) ∅ := fun q =>
        isEmptyElim q
      refine ⟨c, ?_⟩
      intro b _hbB
      simp [finiteSupportChoiceUnion]
  | @insert q S hqS ih =>
      intro hlarge hnoDiagonal
      have hlargeS : ∀ r ∈ S,
          2 * S.card < (additiveSupportFamily A 2 r).card := by
        intro r hrS
        have hrLarge := hlarge r (Finset.mem_insert_of_mem hrS)
        have hScard : S.card < (insert q S).card := by
          simp [Finset.card_insert_of_notMem hqS]
        omega
      have hnoDiagonalS : ∀ r ∈ S,
          ∀ E ∈ additiveSupportFamily A 2 r,
          ∀ b ∈ B, ¬ (b ∈ E ∧ p b ∈ E) := by
        intro r hrS
        exact hnoDiagonal r (Finset.mem_insert_of_mem hrS)
      obtain ⟨cS, hcS⟩ := ih hlargeS hnoDiagonalS
      let U : Finset ℕ := finiteSupportChoiceUnion cS
      let HasOwner : ℕ → Prop := fun x => ∃ b ∈ B, p b = x
      let owner : ℕ → ℕ := fun x =>
        if hx : HasOwner x then Classical.choose hx else 0
      have hownerSpec : ∀ x, HasOwner x →
          owner x ∈ B ∧ p (owner x) = x := by
        intro x hx
        simp only [owner, dif_pos hx]
        exact Classical.choose_spec hx
      let partner : ℕ → ℕ := fun x =>
        if hxB : x ∈ B then p x
        else if hxOwner : HasOwner x then owner x else 0
      have hpartnerB : ∀ b ∈ B, partner b = p b := by
        intro b hbB
        simp [partner, hbB]
      have hpartnerPetal : ∀ b ∈ B, partner (p b) = b := by
        intro b hbB
        have hpbOut := hpOut b hbB
        have howned : HasOwner (p b) := ⟨b, hbB, rfl⟩
        simp only [partner, dif_neg hpbOut, dif_pos howned]
        have hspec := hownerSpec (p b) howned
        exact hpInj hspec.1 hbB hspec.2
      let T : Finset ℕ := U.image partner
      have hUcard : U.card ≤ 2 * S.card := by
        exact finiteSupportChoiceUnion_card_le
          (additiveSupportFamily_cardAtMost A 2) cS
      have hTcard : T.card ≤ 2 * (insert q S).card := by
        calc
          T.card ≤ U.card := Finset.card_image_le
          _ ≤ 2 * S.card := hUcard
          _ ≤ 2 * (insert q S).card := by
            exact Nat.mul_le_mul_left 2
              (Finset.card_le_card (Finset.subset_insert q S))
      have hqNotDestroy : ¬ DestroysAt
          (additiveSupportFamily A 2) (T : Set ℕ) q := by
        intro hqDestroy
        have hsupportLe :=
          card_supports_le_card_of_matching_of_destroysAt
            (fun E hER =>
              additiveSupportFamily_supportsNonempty A (by omega)
                q E hER)
            (additiveSupportFamily_two_isMatching A q)
            hqDestroy
        have hqLarge := hlarge q (Finset.mem_insert_self q S)
        omega
      obtain ⟨E, hER, hET⟩ :=
        not_destroysAt_iff.mp hqNotDestroy
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) (insert q S) := fun t =>
        if ht : t.1 = q then
          ⟨E, by simpa [ht] using hER⟩
        else
          let tS : {n // n ∈ S} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          ⟨(cS tS).1, (cS tS).2⟩
      have hcCases : ∀ x,
          x ∈ finiteSupportChoiceUnion c → x ∈ E ∨ x ∈ U := by
        intro x hx
        obtain ⟨t, _htAttach, hxt⟩ := Finset.mem_biUnion.mp hx
        by_cases ht : t.1 = q
        · left
          simpa [c, ht] using hxt
        · right
          let tS : {n // n ∈ S} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          apply finiteSupportChoice_subset_union cS tS
          simpa [c, ht, tS] using hxt
      refine ⟨c, ?_⟩
      intro b hbB hboth
      rcases hcCases b hboth.1 with hbE | hbU <;>
        rcases hcCases (p b) hboth.2 with hpE | hpU
      · exact hnoDiagonal q (Finset.mem_insert_self q S)
          E hER b hbB ⟨hbE, hpE⟩
      · have hbT : b ∈ T := by
          apply Finset.mem_image.mpr
          exact ⟨p b, hpU, hpartnerPetal b hbB⟩
        exact Set.disjoint_left.mp hET hbE
          (Finset.mem_coe.mpr hbT)
      · have hpT : p b ∈ T := by
          apply Finset.mem_image.mpr
          exact ⟨b, hbU, hpartnerB b hbB⟩
        exact Set.disjoint_left.mp hET hpE
          (Finset.mem_coe.mpr hpT)
      · exact hcS b hbB ⟨hbU, hpU⟩

/-- Sharp incidence dichotomy for a sunflower selector certificate.  Since
every pair-support choice must contain an atom together with its petal, the
greedy lemma shows that either some certified target has at most
`2 * Q.card` pair supports, or one individual pair support already contains
both `b` and `p b` for some atom `b`. -/
theorem tripleCertificate_forces_smallPairFamily_or_diagonalPetalSupport
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    (∃ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤ 2 * Q.card) ∨
    ∃ q ∈ Q, ∃ E ∈ additiveSupportFamily A 2 q,
      ∃ b ∈ B, b ∈ E ∧ p b ∈ E := by
  classical
  by_cases hdiagonal : ∃ q ∈ Q,
      ∃ E ∈ additiveSupportFamily A 2 q,
      ∃ b ∈ B, b ∈ E ∧ p b ∈ E
  · exact Or.inr hdiagonal
  · left
    by_contra hsmall
    have hlarge : ∀ q ∈ Q,
        2 * Q.card < (additiveSupportFamily A 2 q).card := by
      intro q hqQ
      apply Nat.lt_of_not_ge
      intro hle
      exact hsmall ⟨q, hqQ, hle⟩
    have hnoDiagonal : ∀ q ∈ Q,
        ∀ E ∈ additiveSupportFamily A 2 q,
        ∀ b ∈ B, ¬ (b ∈ E ∧ p b ∈ E) := by
      intro q hqQ E hER b hbB hboth
      exact hdiagonal ⟨q, hqQ, E, hER, b, hbB, hboth⟩
    have hpOut : ∀ b ∈ B, p b ∉ B := by
      intro b hbB hpbB
      exact Set.disjoint_left.mp (havoid b hbB)
        (Finset.sdiff_subset (hp b hbB)) hpbB
    obtain ⟨c, hcAvoid⟩ :=
      exists_pairSupportChoice_avoiding_atomPetal_of_large_noDiagonal
        hpOut
        (repairPetalMap_injOn hpetalDisjoint hp)
        hlarge hnoDiagonal
    obtain ⟨b, hbB, hbU, hpU⟩ :=
      exists_atom_and_petal_in_pairChoiceUnion_of_tripleCertificate
        hzeroA hwitness hp hcore hcert c
    exact hcAvoid b hbB ⟨hbU, hpU⟩

/-- Destruction of a diagonal target `b + p` descends to destruction of the
petal target `p`, provided that the anchor `b` itself was not deleted.  Any
order-two support of `p` avoiding the deletion would lift, by adjoining `b`,
to an order-three support of `b + p` avoiding the same deletion. -/
theorem diagonalTarget_destroyer_descends_to_petal
    {A D : Set ℕ} {b p : ℕ}
    (hbA : b ∈ A) (hbD : b ∉ D)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) D (b + p)) :
    DestroysAt (additiveSupportFamily A 2) D p := by
  intro E hER hEdisjoint
  apply hdestroy (insert b E)
  · simpa using insert_mem_additiveSupportFamily_succ hbA hER
  · rw [Set.disjoint_left] at hEdisjoint ⊢
    intro x hxInsert hxD
    have hx : x = b ∨ x ∈ E := by simpa using hxInsert
    rcases hx with rfl | hxE
    · exact hbD hxD
    · exact hEdisjoint hxE hxD

/-- If zero is retained, every order-three destroyer of a target is already
an order-two destroyer of that same target.  Indeed, any surviving pair
support could be padded by zero to give a surviving triple support. -/
theorem orderThree_destroyer_descends_to_orderTwo_of_zero_retained
    {A D : Set ℕ} {q : ℕ}
    (hzeroA : 0 ∈ A) (hzeroD : 0 ∉ D)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) D q) :
    DestroysAt (additiveSupportFamily A 2) D q := by
  intro E hER hEdisjoint
  apply hdestroy (insert 0 E)
  · simpa using insert_mem_additiveSupportFamily_succ hzeroA hER
  · rw [Set.disjoint_left] at hEdisjoint ⊢
    intro x hxInsert hxD
    have hx : x = 0 ∨ x ∈ E := by simpa using hxInsert
    rcases hx with rfl | hxE
    · exact hzeroD hxD
    · exact hEdisjoint hxE hxD

/-- For a canonical zero-atom `p`, order-two destruction is exactly deletion
of `p` or deletion of zero. -/
theorem zeroAtom_destroysAt_two_iff_mem_or_zero
    {A D : Set ℕ} {p : ℕ}
    (hzeroA : 0 ∈ A) (hpA : p ∈ A)
    (hnormal : ∀ E ∈ additiveSupportFamily A 2 p,
      E = {p, 0}) :
    DestroysAt (additiveSupportFamily A 2) D p ↔
      p ∈ D ∨ 0 ∈ D := by
  constructor
  · intro hdestroy
    have hcanonical : pairSupport p p ∈
        additiveSupportFamily A 2 p := by
      apply pairSupport_mem_additiveSupportFamily (Nat.le_refl p) hpA
      simpa using hzeroA
    obtain ⟨x, hxSupport, hxD⟩ :=
      Set.not_disjoint_iff.mp (hdestroy (pairSupport p p) hcanonical)
    have hx : x = p ∨ x = 0 := by
      simpa [pairSupport] using (Finset.mem_coe.mp hxSupport)
    exact hx.elim (fun h => Or.inl (h ▸ hxD))
      (fun h => Or.inr (h ▸ hxD))
  · intro hdeleted E hER hdisjoint
    rw [Set.disjoint_left] at hdisjoint
    rw [hnormal E hER] at hdisjoint
    rcases hdeleted with hpD | hzeroD
    · exact hdisjoint (by simp) hpD
    · exact hdisjoint (by simp) hzeroD

/-- Exact selector consequence of diagonal descent at a zero-atomic petal:
if neither zero nor the anchor is deleted, then destruction of `b + p`
forces the petal `p` itself to be deleted. -/
theorem diagonalTarget_destroyer_forces_petal_mem
    {A D : Set ℕ} {b p : ℕ}
    (hzeroA : 0 ∈ A) (hbA : b ∈ A) (hpA : p ∈ A)
    (hnormal : ∀ E ∈ additiveSupportFamily A 2 p,
      E = {p, 0})
    (hzeroD : 0 ∉ D) (hbD : b ∉ D)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) D (b + p)) :
    p ∈ D := by
  have hpetalDestroy :=
    diagonalTarget_destroyer_descends_to_petal hbA hbD hdestroy
  rcases (zeroAtom_destroysAt_two_iff_mem_or_zero
      hzeroA hpA hnormal).mp hpetalDestroy with hpD | hzeroD'
  · exact hpD
  · exact (hzeroD hzeroD').elim

/-- A pair support containing an atom and its (external) petal is exactly the
diagonal atom-petal pair, and its represented target is their sum. -/
theorem pairSupport_eq_atomPetal_of_both_mem
    {A B : Set ℕ} {p : ℕ → ℕ} {q b : ℕ} {E : Finset ℕ}
    (hpOut : p b ∉ B) (hbB : b ∈ B)
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hbE : b ∈ E) (hpE : p b ∈ E) :
    E = {b, p b} ∧ q = b + p b := by
  have hEq : E = pairSupport q b :=
    additiveSupportFamily_two_eq_pairSupport_of_mem hER hbE
  have hble : b ≤ q :=
    additiveSupportFamily_supportsBounded A 2 q E hER b hbE
  have hpCases : p b = b ∨ p b = q - b := by
    rw [hEq] at hpE
    simpa [pairSupport] using hpE
  have hpNe : p b ≠ b := by
    intro hpb
    exact hpOut (hpb.symm ▸ hbB)
  have hpSub : p b = q - b := hpCases.resolve_left hpNe
  constructor
  · rw [hEq]
    simp [pairSupport, ← hpSub]
  · omega

/-- Arithmetic normal form of the sharp certificate dichotomy: either one
target has at most `2 * Q.card` pair representations, or `Q` contains a
target exactly of the form `b + p b` with canonical support `{b, p b}`. -/
theorem tripleCertificate_forces_smallPairFamily_or_diagonalPetalEquation
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    (∃ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤ 2 * Q.card) ∨
    ∃ q ∈ Q, ∃ b ∈ B,
      q = b + p b ∧
      {b, p b} ∈ additiveSupportFamily A 2 q := by
  obtain hsmall | ⟨q, hqQ, E, hER, b, hbB, hbE, hpE⟩ :=
    tripleCertificate_forces_smallPairFamily_or_diagonalPetalSupport
      hzeroA hwitness havoid hpetalDisjoint hp hcore hcert
  · exact Or.inl hsmall
  · right
    have hpOut : p b ∉ B := by
      intro hpbB
      exact Set.disjoint_left.mp (havoid b hbB)
        (Finset.sdiff_subset (hp b hbB)) hpbB
    obtain ⟨hE, hq⟩ :=
      pairSupport_eq_atomPetal_of_both_mem
        hpOut hbB hER hbE hpE
    exact ⟨q, hqQ, b, hbB, hq, hE ▸ hER⟩

/-- Hereditary atomicity forced by a counterexample.  Every infinite
zero-free reservoir `K ⊆ A` contains an infinite canonical zero-atomic
subreservoir.  Indeed, the alternative supplied by the splittable/atomic
dichotomy is an infinite splitting deletion, and the completed
zero-splitting theorem would then give the desired order-three deletion. -/
theorem counterexample_forces_infiniteZeroAtoms_in_zeroFreeReservoir
    {A K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (hKA : K ⊆ A) (hK : K.Infinite) (hzeroK : 0 ∉ K) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ a ∈ L, ∀ E ∈ additiveSupportFamily A 2 a,
        E = {a, 0} := by
  obtain ⟨D, hDK, hD, hsplit⟩ |
      ⟨L, hLK, hL, _hzero, hnormal⟩ :=
    infiniteDeletionSplits_or_infiniteZeroAtoms hbasis hK
  · have hDA : D ⊆ A := hDK.trans hKA
    have hzeroD : 0 ∉ D := fun h0D => hzeroK (hDK h0D)
    obtain ⟨D', hD'D, hD', hthree⟩ :=
      exists_infiniteDeletion_threeBasis_of_zero_splittingReservoir
        hbasis hzeroA hzeroD hDA hD hsplit
    exact (hcounter D' (hD'D.trans hDA) hD' hthree).elim
  · exact ⟨L, hLK, hL, hnormal⟩

/-- Applying hereditary atomicity to the injective petal image produces an
infinite subreservoir on which both each atom `b` and its strictly smaller
petal `p b` are canonical order-two zero-atoms. -/
theorem exists_infinite_doublyAtomicPetalSubreservoir
    {A B : Set ℕ} {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (hB : B.Infinite)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R) :
    ∃ B', B' ⊆ B ∧ B'.Infinite ∧
      ∀ b ∈ B', ∀ E ∈ additiveSupportFamily A 2 (p b),
        E = {p b, 0} := by
  classical
  have hpInj : Set.InjOn p B :=
    repairPetalMap_injOn hpetalDisjoint hp
  let P : Set ℕ := p '' B
  have hP : P.Infinite := hB.image hpInj
  have hPA : P ⊆ A := by
    rintro x ⟨b, hbB, rfl⟩
    obtain ⟨w, hfw⟩ := hwitness b hbB
    apply w.vertices_subset
    rw [← hfw]
    exact Finset.sdiff_subset (hp b hbB)
  have hzeroP : 0 ∉ P := by
    rintro ⟨b, hbB, hpb0⟩
    obtain ⟨w, hfw⟩ := hwitness b hbB
    apply w.zero_not_mem_vertices
    rw [← hfw]
    exact Finset.sdiff_subset (hpb0 ▸ hp b hbB)
  obtain ⟨L, hLP, hL, hnormalL⟩ :=
    counterexample_forces_infiniteZeroAtoms_in_zeroFreeReservoir
      hbasis hzeroA hcounter hPA hP hzeroP
  let B' : Set ℕ := {b | b ∈ B ∧ p b ∈ L}
  have hB'B : B' ⊆ B := fun _ hb => hb.1
  have himage : p '' B' = L := by
    apply Set.Subset.antisymm
    · rintro x ⟨b, hbB', rfl⟩
      exact hbB'.2
    · intro x hxL
      obtain ⟨b, hbB, hpbx⟩ := hLP hxL
      exact ⟨b, ⟨hbB, hpbx ▸ hxL⟩, hpbx⟩
  have hB' : B'.Infinite := by
    by_contra hnot
    have hfiniteImage : (p '' B').Finite :=
      (Set.not_infinite.mp hnot).image p
    rw [himage] at hfiniteImage
    exact hL hfiniteImage
  refine ⟨B', hB'B, hB', ?_⟩
  intro b hbB' E hER
  exact hnormalL (p b) hbB'.2 E hER

/-- Global doubly-atomic reservoir forced by a zero-normalized
counterexample.  In addition to all self-repaired sunflower geometry, both
`b` and the injective strictly smaller petal `p b` have only their canonical
order-two supports with zero. -/
theorem counterexample_forces_doublyAtomicSelfRepairedPetalReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p : ℕ → ℕ, ∃ g : ℕ → Finset ℕ,
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 (p b),
          E = {p b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ b ∈ B, p b ∈ f b \ R ∧ p b < b) ∧
        ∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b := by
  obtain ⟨B₀, hB₀A, hB₀, R, f, p, g, hnormal₀,
      hrepairs₀, hwitness₀, havoid₀, hpetal₀,
      hpetalDisjoint₀, hp₀, hg₀⟩ :=
    counterexample_forces_selfRepairedPetalReservoir
      hbasis hzeroA hcounter
  obtain ⟨B, hBB₀, hB, hnormalPetal⟩ :=
    exists_infinite_doublyAtomicPetalSubreservoir
      hbasis hzeroA hcounter hB₀ hwitness₀
        hpetalDisjoint₀ (fun b hb => (hp₀ b hb).1)
  refine ⟨B, hBB₀.trans hB₀A, hB, R, f, p, g,
    ?_, hnormalPetal, hrepairs₀.mono hBB₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb E hER
    exact hnormal₀ b (hBB₀ hb) E hER
  · intro b hb
    exact hwitness₀ b (hBB₀ hb)
  · intro b hb
    exact (havoid₀ b (hBB₀ hb)).mono_right hBB₀
  · intro b hb
    exact hpetal₀ b (hBB₀ hb)
  · intro b hb d hd hbd
    exact hpetalDisjoint₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    exact hp₀ b (hBB₀ hb)
  · intro b hb
    have hgb := hg₀ b (hBB₀ hb)
    exact ⟨hgb.1, hgb.2.1,
      hgb.2.2.1.mono_right hBB₀,
      fun d hd => hgb.2.2.2 d (hBB₀ hd)⟩

/-- A bounded point-map can be thinned so that it avoids both the retained
indices and the image of any injective marked-point map.  The auxiliary
collision map pulls every marked point occurring in `h b` back to its unique
owner, after which the ordinary bounded free-set theorem handles both kinds
of collision simultaneously. -/
theorem exists_infinite_freeSet_avoiding_injectiveImage
    {K : Set ℕ} (hK : K.Infinite)
    (u : ℕ → ℕ) (huInj : Set.InjOn u K)
    (h : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ b ∈ K, (h b).card ≤ r)
    (hbNotH : ∀ b ∈ K, b ∉ h b)
    (huNotH : ∀ b ∈ K, u b ∉ h b) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L,
        Disjoint (h b : Set ℕ) L ∧
        ∀ d ∈ L, u d ∉ h b := by
  classical
  let HasOwner : ℕ → Prop := fun x => ∃ d ∈ K, u d = x
  let owner : ℕ → ℕ := fun x =>
    if hx : HasOwner x then Classical.choose hx else 0
  have hownerSpec : ∀ x, HasOwner x →
      owner x ∈ K ∧ u (owner x) = x := by
    intro x hx
    simp only [owner, dif_pos hx]
    exact Classical.choose_spec hx
  let collision : ℕ → Finset ℕ := fun b =>
    ((h b).filter HasOwner).image owner
  have hcollisionCard : ∀ b ∈ K, (collision b).card ≤ r := by
    intro b hb
    calc
      (collision b).card ≤ ((h b).filter HasOwner).card :=
        Finset.card_image_le
      _ ≤ (h b).card := Finset.card_filter_le _ _
      _ ≤ r := hcard b hb
  have hcollisionMem : ∀ b, ∀ d ∈ K, u d ∈ h b →
      d ∈ collision b := by
    intro b d hd hudH
    have howned : HasOwner (u d) := ⟨d, hd, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨u d, Finset.mem_filter.mpr ⟨hudH, howned⟩, ?_⟩
    have hspec := hownerSpec (u d) howned
    exact huInj hspec.1 hd hspec.2
  have hbNotCollision : ∀ b ∈ K, b ∉ collision b := by
    intro b hb hbCollision
    obtain ⟨x, hxFilter, hownerb⟩ :=
      Finset.mem_image.mp hbCollision
    have hxH := (Finset.mem_filter.mp hxFilter).1
    have hxOwned := (Finset.mem_filter.mp hxFilter).2
    have hspec := hownerSpec x hxOwned
    have hubx : u b = x := by
      rw [← hownerb]
      exact hspec.2
    exact huNotH b hb (hubx ▸ hxH)
  let avoidMap : ℕ → Finset ℕ := fun b => h b ∪ collision b
  have hAvoidCard : ∀ b ∈ K, (avoidMap b).card ≤ 2 * r := by
    intro b hb
    calc
      (avoidMap b).card ≤ (h b).card + (collision b).card := by
        simpa [avoidMap] using
          (Finset.card_union_le (h b) (collision b))
      _ ≤ r + r := Nat.add_le_add (hcard b hb)
        (hcollisionCard b hb)
      _ = 2 * r := by omega
  have hbNotAvoid : ∀ b ∈ K, b ∉ avoidMap b := by
    intro b hb hbAvoid
    rcases Finset.mem_union.mp hbAvoid with hbH | hbCollision
    · exact hbNotH b hb hbH
    · exact hbNotCollision b hb hbCollision
  obtain ⟨L, hLK, hL, hAvoidFree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK avoidMap (2 * r) hAvoidCard hbNotAvoid
  refine ⟨L, hLK, hL, ?_⟩
  intro b hb
  have hHFree : Disjoint (h b : Set ℕ) L := by
    apply (hAvoidFree b hb).mono_left
    intro x hxH
    exact Finset.mem_union_left _ (Finset.mem_coe.mp hxH)
  refine ⟨hHFree, ?_⟩
  intro d hd hudH
  exact Set.disjoint_left.mp (hAvoidFree b hb)
    (Finset.mem_coe.mpr (Finset.mem_union_right _
      (hcollisionMem b d (hLK hd) hudH))) hd

/-- Any injective third-option map strictly below both its atom and the first
petal has an infinite thinning with simultaneous self-repairs.  Two uses of
`exists_infinite_freeSet_avoiding_injectiveImage` make the chosen repairs
avoid the retained atoms, every first petal, and every third option. -/
theorem exists_infinite_selfRepairedThirdOptions
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB : B.Infinite)
    (p r : ℕ → ℕ)
    (hpInj : Set.InjOn p B)
    (hrInj : Set.InjOn r B)
    (hrp : ∀ b ∈ B, r b < p b)
    (hrb : ∀ b ∈ B, r b < b) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ h : ℕ → Finset ℕ, ∀ b ∈ L,
        h b ∈ additiveSupportFamily A 3 (r b) ∧
        r b ∉ h b ∧
        Disjoint (h b : Set ℕ) L ∧
        (∀ d ∈ L, p d ∉ h b) ∧
        ∀ d ∈ L, r d ∉ h b := by
  classical
  obtain ⟨T, hselfAvoid⟩ :=
    eventually_selfAvoidingTripleSupport_of_orderTwoBasis hbasis
  let Low : Set ℕ := {b | b ∈ B ∧ r b < T}
  have hLowFinite : Low.Finite := by
    apply Set.Finite.of_finite_image (f := r)
    · apply (Set.finite_Iio T).subset
      rintro y ⟨b, hbLow, rfl⟩
      exact hbLow.2
    · exact hrInj.mono (fun _ hb => hb.1)
  let K : Set ℕ := B \ Low
  have hK : K.Infinite := hB.diff hLowFinite
  have hKB : K ⊆ B := Set.diff_subset
  have hrLarge : ∀ b ∈ K, T ≤ r b := by
    intro b hb
    by_contra hnot
    exact hb.2 ⟨hb.1, Nat.lt_of_not_ge hnot⟩
  have hhExists : ∀ b : K, ∃ H,
      H ∈ additiveSupportFamily A 3 (r b.1) ∧ r b.1 ∉ H := by
    intro b
    exact hselfAvoid (r b.1) (hrLarge b.1 b.2)
  choose repair hrepairR hrepairSelf using hhExists
  let h : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ K then repair ⟨b, hb⟩ else ∅
  have hhR : ∀ b ∈ K,
      h b ∈ additiveSupportFamily A 3 (r b) := by
    intro b hb
    simpa [h, hb] using hrepairR ⟨b, hb⟩
  have hhSelf : ∀ b ∈ K, r b ∉ h b := by
    intro b hb
    simpa [h, hb] using hrepairSelf ⟨b, hb⟩
  have hhCard : ∀ b ∈ K, (h b).card ≤ 3 := by
    intro b hb
    exact additiveSupportFamily_cardAtMost A 3
      (r b) (h b) (hhR b hb)
  have hbNotH : ∀ b ∈ K, b ∉ h b := by
    intro b hb hbH
    have hble : b ≤ r b :=
      additiveSupportFamily_supportsBounded A 3
        (r b) (h b) (hhR b hb) b hbH
    exact (not_le_of_gt (hrb b (hKB hb))) hble
  have hpNotH : ∀ b ∈ K, p b ∉ h b := by
    intro b hb hpH
    have hple : p b ≤ r b :=
      additiveSupportFamily_supportsBounded A 3
        (r b) (h b) (hhR b hb) (p b) hpH
    exact (not_le_of_gt (hrp b (hKB hb))) hple
  obtain ⟨L₁, hL₁K, hL₁, havoidP⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImage
      hK p (hpInj.mono hKB) h 3 hhCard hbNotH hpNotH
  obtain ⟨L, hLL₁, hL, havoidR⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImage
      hL₁ r (hrInj.mono (hL₁K.trans hKB)) h 3
        (fun b hb => hhCard b (hL₁K hb))
        (fun b hb => hbNotH b (hL₁K hb))
        (fun b hb => hhSelf b (hL₁K hb))
  refine ⟨L, hLL₁.trans (hL₁K.trans hKB), hL, h, ?_⟩
  intro b hb
  have hbL₁ := hLL₁ hb
  have hbK := hL₁K hbL₁
  refine ⟨hhR b hbK, hhSelf b hbK,
    (havoidR b hb).1, ?_, (havoidR b hb).2⟩
  intro d hd
  exact (havoidP b hbL₁).2 d (hLL₁ hd)

/-- Joint sunflower refinement of the clique supports `f b` and the
self-repair supports `g b`.  After thinning, the distinguished petal `p b`
still lies in the clique petal, while the self-repair support has a nonempty
petal outside the same root.  Thus every surviving atom has a third private
selector option, separate from both the atom and every distinguished petal. -/
theorem exists_infinite_jointCliqueSelfRepairSunflower
    {A B : Set ℕ}
    (hB : B.Infinite)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ S : Finset ℕ,
        0 ∈ S ∧
        (∀ b ∈ L, p b ∈ f b \ S) ∧
        (∀ b ∈ L, (g b \ S).Nonempty) ∧
        ∀ b ∈ L, ∀ d ∈ L, b ≠ d →
          Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S) := by
  classical
  let h : ℕ → Finset ℕ := fun b => f b ∪ g b
  have hcard : ∀ b ∈ B, (h b).card ≤ 7 := by
    intro b hb
    obtain ⟨w, hfw⟩ := hwitness b hb
    have hfCard : (f b).card ≤ 4 := by
      rw [hfw]
      exact w.vertices_card_le_four
    have hgCard : (g b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (p b) (g b) (hg b hb).1
    exact (Finset.card_union_le (f b) (g b)).trans (by omega)
  obtain ⟨L₀, hL₀B, hL₀, S₀, hdelta⟩ :=
    exists_infinite_deltaSystem_of_bounded_pointMap
      hB h 7 hcard
  let S : Finset ℕ := insert 0 S₀
  have hpInj : Set.InjOn p B :=
    repairPetalMap_injOn hpetalDisjoint hp
  let EmptyRepairPetal : Set ℕ :=
    {b | b ∈ L₀ ∧ g b \ S = ∅}
  have hEmptyFinite : EmptyRepairPetal.Finite := by
    apply Set.Finite.of_finite_image (f := p)
    · apply (Set.finite_Iic (3 * S.sum id)).subset
      rintro y ⟨b, hbEmpty, rfl⟩
      have hbB : b ∈ B := hL₀B hbEmpty.1
      have hsub : g b ⊆ S :=
        Finset.sdiff_eq_empty_iff_subset.mp hbEmpty.2
      obtain ⟨v, _hvA, hvsum, hvSupport⟩ :=
        mem_additiveSupportFamily_iff.mp (hg b hbB).1
      have hvle : ∀ i, (v i).1 ≤ S.sum id := by
        intro i
        apply Finset.single_le_sum (s := S) (f := id)
          (fun _ _ => Nat.zero_le _)
        apply hsub
        rw [← hvSupport]
        exact mem_tupleSupport_iff.mpr ⟨i, rfl⟩
      have hsumle :
          ∑ i, (v i).1 ≤ ∑ _i : Fin 3, S.sum id := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hvle i
      rw [hvsum] at hsumle
      simpa using hsumle
    · exact hpInj.mono (fun _ hb => hL₀B hb.1)
  let L : Set ℕ := L₀ \ EmptyRepairPetal
  have hLL₀ : L ⊆ L₀ := Set.diff_subset
  have hL : L.Infinite := hL₀.diff hEmptyFinite
  refine ⟨L, hLL₀.trans hL₀B, hL, S, Finset.mem_insert_self _ _,
    ?_, ?_, ?_⟩
  · intro b hbL
    have hbL₀ : b ∈ L₀ := hLL₀ hbL
    have hbB : b ∈ B := hL₀B hbL₀
    have hpbOld := hp b hbB
    apply Finset.mem_sdiff.mpr
    refine ⟨(Finset.mem_sdiff.mp hpbOld).1, ?_⟩
    intro hpbS
    rcases Finset.mem_insert.mp hpbS with hpbZero | hpbRoot
    · obtain ⟨w, hfw⟩ := hwitness b hbB
      apply w.zero_not_mem_vertices
      rw [← hpbZero, ← hfw]
      exact (Finset.mem_sdiff.mp hpbOld).1
    · obtain ⟨d, hdL₀, hbd⟩ := hL₀.exists_gt b
      have hbdNe : b ≠ d := Nat.ne_of_lt hbd
      have hpbInter : p b ∈ h b ∩ h d := by
        rw [hdelta b hbL₀ d hdL₀ hbdNe]
        exact hpbRoot
      have hpbHd : p b ∈ h d := (Finset.mem_inter.mp hpbInter).2
      rcases Finset.mem_union.mp hpbHd with hpfd | hpgd
      · have hpbOtherPetal : p b ∈ f d \ R :=
          Finset.mem_sdiff.mpr
            ⟨hpfd, (Finset.mem_sdiff.mp hpbOld).2⟩
        exact Finset.disjoint_left.mp
          (hpetalDisjoint b hbB d (hL₀B hdL₀) hbdNe)
          hpbOld hpbOtherPetal
      · exact (hg d (hL₀B hdL₀)).2.2 b hbB hpgd
  · intro b hbL
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hbL.2 ⟨hLL₀ hbL, hempty⟩
  · intro b hbL d hdL hbd
    rw [Finset.disjoint_left]
    intro x hxb hxd
    have hxInter : x ∈ h b ∩ h d := by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hxb).1,
          (Finset.mem_sdiff.mp hxd).1⟩
    have hxRoot : x ∈ S₀ := by
      rw [← hdelta b (hLL₀ hbL) d (hLL₀ hdL) hbd]
      exact hxInter
    exact (Finset.mem_sdiff.mp hxb).2
      (Finset.mem_insert_of_mem hxRoot)

/-- Add one chosen self-repair petal to the old atom/clique cell. -/
def enrichedExternalCliqueCell
    (S : Finset ℕ) (f r : ℕ → Finset ℕ) (b : ℕ) : Finset ℕ :=
  r b ∪ externalCliqueCell S f b

/-- The exact three-option subcell: the atom, its distinguished clique
petal, and the singleton chosen from its self-repair petal. -/
def atomPetalRepairCell
    (p : ℕ → ℕ) (r : ℕ → Finset ℕ) (b : ℕ) : Finset ℕ :=
  insert b (insert (p b) (r b))

/-- Point-valued form of the same exact three-option cell. -/
def atomPetalRepairPointCell
    (p r : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  insert b {p b, r b}

/-- A finset-valued map which is singleton on `B` can be represented there
by an ordinary point map. -/
theorem exists_pointMap_of_card_one_on
    {B : Set ℕ} (r : ℕ → Finset ℕ)
    (hrCard : ∀ b ∈ B, (r b).card = 1) :
    ∃ ρ : ℕ → ℕ, ∀ b ∈ B, r b = {ρ b} := by
  classical
  have hexists : ∀ b : B, ∃ x, r b.1 = {x} := by
    intro b
    exact Finset.card_eq_one.mp (hrCard b.1 b.2)
  choose ρB hρB using hexists
  let ρ : ℕ → ℕ := fun b =>
    if hb : b ∈ B then ρB ⟨b, hb⟩ else 0
  refine ⟨ρ, ?_⟩
  intro b hb
  simpa [ρ, hb] using hρB ⟨b, hb⟩

/-- A block selector cannot select two distinct elements of one block. -/
theorem IsFiniteBlockPartition.eq_of_mem_sameBlock_of_mem_selectedSet
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F)
    {i x y : ℕ}
    (hxF : x ∈ F i) (hyF : y ∈ F i)
    (hxS : x ∈ selectedSet s) (hyS : y ∈ selectedSet s) :
    x = y := by
  have hxIndex : blockIndex P x = i := P.blockIndex_eq_of_mem hxF
  have hyIndex : blockIndex P y = i := P.blockIndex_eq_of_mem hyF
  have hxValue := (P.mem_selectedSet_iff s).mp hxS
  have hyValue := (P.mem_selectedSet_iff s).mp hyS
  rw [hxIndex] at hxValue
  rw [hyIndex] at hyValue
  exact hxValue.symm.trans hyValue

/-- Pairwise-disjoint atom/first-petal/third-option triples extend to a
finite-block partition. -/
theorem exists_finiteBlockPartition_for_atomPetalRepairPointCells
    {A B : Set ℕ}
    (hBA : B ⊆ A) (hB : B.Infinite)
    (p r : ℕ → ℕ)
    (hpA : ∀ b ∈ B, p b ∈ A)
    (hrA : ∀ b ∈ B, r b ∈ A)
    (hpOut : ∀ b ∈ B, p b ∉ B)
    (hrOut : ∀ b ∈ B, r b ∉ B)
    (hpr : ∀ b ∈ B, p b ≠ r b)
    (hoptionsDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint ({p b, r b} : Finset ℕ) {p d, r d}) :
    ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, atomPetalRepairPointCell p r (e i).1 ⊆ F i) ∧
      ∀ i, (atomPetalRepairPointCell p r (e i).1).card = 3 := by
  classical
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let cell : ℕ → Finset ℕ := fun i =>
    atomPetalRepairPointCell p r (e i).1
  have hcellA : ∀ i, (cell i : Set ℕ) ⊆ A := by
    intro i x hx
    rcases Finset.mem_insert.mp hx with hxb | hxOption
    · exact hxb ▸ hBA (e i).2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hxOption
      rcases hxOption with hxp | hxr
      · exact hxp ▸ hpA (e i).1 (e i).2
      · exact hxr ▸ hrA (e i).1 (e i).2
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    exact ⟨(e i).1, Finset.mem_insert_self _ _⟩
  have hcellDisjoint : Pairwise fun i j =>
      Disjoint (cell i) (cell j) := by
    intro i j hij
    have hbij : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      apply e.injective
      exact Subtype.ext h
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases Finset.mem_insert.mp hxi with hxiAtom | hxiOption <;>
      rcases Finset.mem_insert.mp hxj with hxjAtom | hxjOption
    · exact hbij (hxiAtom.symm.trans hxjAtom)
    · subst x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxjOption
      rcases hxjOption with hxp | hxr
      · exact hpOut (e j).1 (e j).2 (hxp ▸ (e i).2)
      · exact hrOut (e j).1 (e j).2 (hxr ▸ (e i).2)
    · subst x
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxiOption
      rcases hxiOption with hxp | hxr
      · exact hpOut (e i).1 (e i).2 (hxp ▸ (e j).2)
      · exact hrOut (e i).1 (e i).2 (hxr ▸ (e j).2)
    · exact Finset.disjoint_left.mp
        (hoptionsDisjoint (e i).1 (e i).2
          (e j).1 (e j).2 hbij)
        hxiOption hxjOption
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  refine ⟨e, F, P, hcore, ?_⟩
  intro i
  let b := (e i).1
  have hbp : b ≠ p b := by
    intro hEq
    exact hpOut b (e i).2 (hEq ▸ (e i).2)
  have hbr : b ≠ r b := by
    intro hEq
    exact hrOut b (e i).2 (hEq ▸ (e i).2)
  change (insert b ({p b, r b} : Finset ℕ)).card = 3
  rw [Finset.card_insert_of_notMem (by simpa [hbp, hbr])]
  rw [Finset.card_insert_of_notMem
    (by simpa using hpr b (e i).2)]
  simp

/-- The joint sunflower gives a finite-block partition with three dedicated
and pairwise distinct options in every atom block: `b`, `p b`, and a chosen
point from the self-repair petal. -/
theorem exists_finiteBlockPartition_for_enrichedCliqueSunflower
    {A B : Set ℕ}
    (hBA : B ⊆ A) (hB : B.Infinite)
    {S : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hp : ∀ b ∈ B, p b ∈ f b \ S)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B)
    (hrepairPetal : ∀ b ∈ B, (g b \ S).Nonempty)
    (hjointDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S)) :
    ∃ r : ℕ → Finset ℕ,
      (∀ b ∈ B, r b ⊆ g b \ S ∧ (r b).card = 1) ∧
      ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ i, enrichedExternalCliqueCell S f r (e i).1 ⊆ F i) ∧
        ∀ i, 3 ≤ (enrichedExternalCliqueCell S f r (e i).1).card := by
  classical
  let r : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ B then
      {Classical.choose (hrepairPetal b hb)}
    else ∅
  have hr : ∀ b ∈ B, r b ⊆ g b \ S ∧ (r b).card = 1 := by
    intro b hb
    constructor
    · intro x hx
      have hxEq : x = Classical.choose (hrepairPetal b hb) := by
        simpa [r, hb] using hx
      rw [hxEq]
      exact Classical.choose_spec (hrepairPetal b hb)
    · simp [r, hb]
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let cell : ℕ → Finset ℕ := fun i =>
    enrichedExternalCliqueCell S f r (e i).1
  have hjointAvoid : ∀ b ∈ B,
      Disjoint ((f b ∪ g b : Finset ℕ) : Set ℕ) B := by
    intro b hb
    rw [Set.disjoint_left]
    intro x hxUnion hxB
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hxUnion) with hxf | hxg
    · exact Set.disjoint_left.mp (havoid b hb)
        (Finset.mem_coe.mpr hxf) hxB
    · exact Set.disjoint_left.mp (hg b hb).2.2
        (Finset.mem_coe.mpr hxg) hxB
  have hcellCases : ∀ b ∈ B, ∀ x ∈ enrichedExternalCliqueCell S f r b,
      x = b ∨ x ∈ (f b ∪ g b) \ S := by
    intro b hb x hxCell
    rcases Finset.mem_union.mp hxCell with hxr | hxExternal
    · right
      have hxrPetal := (hr b hb).1 hxr
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_union_right _
        (Finset.mem_sdiff.mp hxrPetal).1,
        (Finset.mem_sdiff.mp hxrPetal).2⟩
    · rcases Finset.mem_insert.mp hxExternal with hxb | hxf
      · exact Or.inl hxb
      · right
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hxf).1,
            (Finset.mem_sdiff.mp hxf).2⟩
  have hcellA : ∀ i, (cell i : Set ℕ) ⊆ A := by
    intro i x hxCell
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hxCell) with hxr | hxExternal
    · have hxrPetal := (hr (e i).1 (e i).2).1 hxr
      exact additiveSupportFamily_supportsIn A 3 (p (e i).1)
        (g (e i).1) (hg (e i).1 (e i).2).1 x
        (Finset.mem_sdiff.mp hxrPetal).1
    · rcases Finset.mem_insert.mp hxExternal with hxb | hxf
      · exact hxb ▸ hBA (e i).2
      · obtain ⟨w, hfw⟩ := hwitness (e i).1 (e i).2
        apply w.vertices_subset
        rw [← hfw]
        exact Finset.sdiff_subset hxf
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    exact ⟨(e i).1, Finset.mem_union_right _
      (Finset.mem_insert_self _ _)⟩
  have hcellDisjoint : Pairwise fun i j =>
      Disjoint (cell i) (cell j) := by
    intro i j hij
    have hbij : (e i).1 ≠ (e j).1 := by
      intro h
      apply hij
      apply e.injective
      exact Subtype.ext h
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rcases hcellCases (e i).1 (e i).2 x hxi with hxiAtom | hxiPetal <;>
      rcases hcellCases (e j).1 (e j).2 x hxj with hxjAtom | hxjPetal
    · exact hbij (hxiAtom.symm.trans hxjAtom)
    · subst x
      exact Set.disjoint_left.mp
        (hjointAvoid (e j).1 (e j).2)
        (Finset.mem_coe.mpr (Finset.sdiff_subset hxjPetal)) (e i).2
    · subst x
      exact Set.disjoint_left.mp
        (hjointAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (Finset.sdiff_subset hxiPetal)) (e j).2
    · exact Finset.disjoint_left.mp
        (hjointDisjoint (e i).1 (e i).2
          (e j).1 (e j).2 hbij)
        hxiPetal hxjPetal
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  refine ⟨r, hr, e, F, P, hcore, ?_⟩
  intro i
  let b := (e i).1
  have hrNonempty : (r b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hrEmpty
    have hcardZero : (r b).card = 0 := Finset.card_eq_zero.mpr hrEmpty
    rw [(hr b (e i).2).2] at hcardZero
    omega
  let rb := Classical.choose hrNonempty
  have hrbMem : rb ∈ r b := Classical.choose_spec hrNonempty
  have hpbMem : p b ∈ externalCliqueCell S f b := by
    rw [externalCliqueCell]
    exact Finset.mem_insert_of_mem (hp b (e i).2)
  have hbMem : b ∈ externalCliqueCell S f b :=
    Finset.mem_insert_self _ _
  have hbp : b ≠ p b := by
    intro hEq
    exact Set.disjoint_left.mp (havoid b (e i).2)
      (Finset.mem_coe.mpr (Finset.sdiff_subset (hp b (e i).2)))
      (hEq ▸ (e i).2)
  have hbr : b ≠ rb := by
    intro hEq
    have hrbG : rb ∈ g b :=
      (Finset.mem_sdiff.mp ((hr b (e i).2).1 hrbMem)).1
    exact Set.disjoint_left.mp (hg b (e i).2).2.2
      (Finset.mem_coe.mpr hrbG) (hEq ▸ (e i).2)
  have hpr : p b ≠ rb := by
    intro hEq
    apply (hg b (e i).2).2.1
    rw [hEq]
    exact (Finset.mem_sdiff.mp ((hr b (e i).2).1 hrbMem)).1
  have hthreeSubset : ({b, p b, rb} : Finset ℕ) ⊆
      enrichedExternalCliqueCell S f r b := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_right _ hbMem
    · exact Finset.mem_union_right _ hpbMem
    · exact Finset.mem_union_left _ hrbMem
  have hthreeCard : ({b, p b, rb} : Finset ℕ).card = 3 := by
    simp [hbp, hbr, hpr]
  have hcardle := Finset.card_le_card hthreeSubset
  rw [hthreeCard] at hcardle
  exact hcardle

/-- A counterexample forces an infinite reservoir with three coherent
selector options at every atom.  The first petal `p b` and the strictly
smaller third option `r b` have self-repair supports; all three repair layers
avoid the retained atom set, and the last layer simultaneously avoids every
first and third option. -/
theorem counterexample_forces_triplySelfRepairedOptionReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ S : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p r : ℕ → ℕ, ∃ g h : ℕ → Finset ℕ,
        0 ∈ S ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, p b ∈ f b \ S ∧ p b < b) ∧
        (∀ b ∈ B, r b ∈ g b \ S ∧ r b < p b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S)) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        ∀ b ∈ B,
          h b ∈ additiveSupportFamily A 3 (r b) ∧
          r b ∉ h b ∧ Disjoint (h b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ h b) ∧
          ∀ d ∈ B, r d ∉ h b := by
  classical
  obtain ⟨B₀, hB₀A, hB₀, R, f, p, g,
      _hnormalAtom, _hnormalPetal, _hrepairs,
      hwitness₀, hAvoid₀, _hpetal₀, hpetalDisjoint₀, hp₀, hg₀⟩ :=
    counterexample_forces_doublyAtomicSelfRepairedPetalReservoir
      hbasis hzeroA hcounter
  obtain ⟨B₁, hB₁B₀, hB₁, S, hzeroS, hpS,
      hgPetal, hjointDisjoint⟩ :=
    exists_infinite_jointCliqueSelfRepairSunflower
      hB₀ hwitness₀ hpetalDisjoint₀
        (fun b hb => (hp₀ b hb).1)
        (fun b hb => ⟨(hg₀ b hb).1,
          (hg₀ b hb).2.2.1,
          (hg₀ b hb).2.2.2⟩)
  have hB₁A : B₁ ⊆ A := hB₁B₀.trans hB₀A
  have hwitness₁ : ∀ b ∈ B₁, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices := fun b hb => hwitness₀ b (hB₁B₀ hb)
  have hAvoid₁ : ∀ b ∈ B₁, Disjoint (f b : Set ℕ) B₁ := by
    intro b hb
    exact (hAvoid₀ b (hB₁B₀ hb)).mono_right hB₁B₀
  have hg₁ : ∀ b ∈ B₁,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B₁ ∧
      ∀ d ∈ B₁, p d ∉ g b := by
    intro b hb
    have hgb := hg₀ b (hB₁B₀ hb)
    exact ⟨hgb.1, hgb.2.1,
      hgb.2.2.1.mono_right hB₁B₀,
      fun d hd => hgb.2.2.2 d (hB₁B₀ hd)⟩
  obtain ⟨rFin, hrFin, _e, _F, _P, _hcore, _hcard⟩ :=
    exists_finiteBlockPartition_for_enrichedCliqueSunflower
      hB₁A hB₁ hwitness₁ hAvoid₁ hpS
        (fun b hb => ⟨(hg₁ b hb).1, (hg₁ b hb).2.1,
          (hg₁ b hb).2.2.1⟩)
        hgPetal hjointDisjoint
  obtain ⟨r, hrEq⟩ :=
    exists_pointMap_of_card_one_on rFin
      (fun b hb => (hrFin b hb).2)
  have hrPetal : ∀ b ∈ B₁, r b ∈ g b \ S := by
    intro b hb
    apply (hrFin b hb).1
    rw [hrEq b hb]
    simp
  have hrInj : Set.InjOn r B₁ := by
    intro b hb d hd hrd
    by_contra hbd
    have hrbJoint : r b ∈ (f b ∪ g b) \ S :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp (hrPetal b hb)).1,
          (Finset.mem_sdiff.mp (hrPetal b hb)).2⟩
    have hrdJoint : r d ∈ (f d ∪ g d) \ S :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp (hrPetal d hd)).1,
          (Finset.mem_sdiff.mp (hrPetal d hd)).2⟩
    exact Finset.disjoint_left.mp
      (hjointDisjoint b hb d hd hbd)
      hrbJoint (hrd ▸ hrdJoint)
  have hpInj : Set.InjOn p B₁ :=
    (repairPetalMap_injOn hpetalDisjoint₀
      (fun b hb => (hp₀ b hb).1)).mono hB₁B₀
  have hrp : ∀ b ∈ B₁, r b < p b := by
    intro b hb
    have hrle : r b ≤ p b :=
      additiveSupportFamily_supportsBounded A 3
        (p b) (g b) (hg₁ b hb).1 (r b)
        (Finset.mem_sdiff.mp (hrPetal b hb)).1
    have hrne : r b ≠ p b := by
      intro hEq
      exact (hg₁ b hb).2.1
        (hEq ▸ (Finset.mem_sdiff.mp (hrPetal b hb)).1)
    omega
  have hrb : ∀ b ∈ B₁, r b < b := by
    intro b hb
    exact (hrp b hb).trans (hp₀ b (hB₁B₀ hb)).2
  obtain ⟨B, hBB₁, hB, h, hh⟩ :=
    exists_infinite_selfRepairedThirdOptions
      hbasis hB₁ p r hpInj hrInj hrp hrb
  have hBA : B ⊆ A := hBB₁.trans hB₁A
  refine ⟨B, hBA, hB, S, f, p, r, g, h, hzeroS,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact hwitness₁ b (hBB₁ hb)
  · intro b hb
    exact (hAvoid₁ b (hBB₁ hb)).mono_right hBB₁
  · intro b hb
    exact ⟨hpS b (hBB₁ hb), (hp₀ b (hB₁B₀ (hBB₁ hb))).2⟩
  · intro b hb
    exact ⟨hrPetal b (hBB₁ hb), hrp b (hBB₁ hb)⟩
  · intro b hb d hd hbd
    exact hjointDisjoint b (hBB₁ hb) d (hBB₁ hd) hbd
  · intro b hb
    have hgb := hg₁ b (hBB₁ hb)
    exact ⟨hgb.1, hgb.2.1,
      hgb.2.2.1.mono_right hBB₁,
      fun d hd => hgb.2.2.2 d (hBB₁ hd)⟩
  · exact hh

/-- Every selector restricted to the coherent three-option cells preserves
an order-three support for every internal target `q ∈ A`.  Selected atoms use
their clique repair, selected first petals use `g`, selected third options
use `h`, and unselected internal targets use the zero-padded trivial pair. -/
theorem internalTarget_survives_atomPetalRepairPointSelector
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    {S : Finset ℕ} {f : ℕ → Finset ℕ}
    {p r : ℕ → ℕ} {g h : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroS : 0 ∈ S)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hAvoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hp : ∀ b ∈ B, p b ∈ f b \ S)
    (hr : ∀ b ∈ B, r b ∈ g b \ S)
    (hjointDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S))
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hh : ∀ b ∈ B,
      h b ∈ additiveSupportFamily A 3 (r b) ∧
      r b ∉ h b ∧ Disjoint (h b : Set ℕ) B ∧
      (∀ d ∈ B, p d ∉ h b) ∧
      ∀ d ∈ B, r d ∉ h b)
    (hcore : ∀ i, atomPetalRepairPointCell p r (e i).1 ⊆ F i)
    (s : BlockSelector F)
    (hsCore : ∀ i, (s i).1 ∈
      atomPetalRepairPointCell p r (e i).1) :
    ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
      Disjoint (G : Set ℕ) (selectedSet s) := by
  classical
  have hpOut : ∀ b ∈ B, p b ∉ B := by
    intro b hb hpbB
    exact Set.disjoint_left.mp (hAvoid b hb)
      (Finset.mem_coe.mpr (Finset.sdiff_subset (hp b hb))) hpbB
  have hrOut : ∀ b ∈ B, r b ∉ B := by
    intro b hb hrbB
    exact Set.disjoint_left.mp (hg b hb).2.2.1
      (Finset.mem_coe.mpr (Finset.sdiff_subset (hr b hb))) hrbB
  have hpr : ∀ b ∈ B, p b ≠ r b := by
    intro b hb hEq
    exact (hg b hb).2.1
      (hEq ▸ Finset.sdiff_subset (hr b hb))
  have hsCases : ∀ x ∈ selectedSet s,
      ∃ b ∈ B, x = b ∨ x = p b ∨ x = r b := by
    rintro x ⟨i, rfl⟩
    have hsi := hsCore i
    simp only [atomPetalRepairPointCell, Finset.mem_insert,
      Finset.mem_singleton] at hsi
    exact ⟨(e i).1, (e i).2, hsi⟩
  have hselectedUnique : ∀ b ∈ B, ∀ x y,
      x ∈ atomPetalRepairPointCell p r b →
      y ∈ atomPetalRepairPointCell p r b →
      x ∈ selectedSet s → y ∈ selectedSet s → x = y := by
    intro b hb x y hxCell hyCell hxSelected hySelected
    obtain ⟨i, hi⟩ := e.surjective ⟨b, hb⟩
    have hib : (e i).1 = b := congrArg Subtype.val hi
    apply P.eq_of_mem_sameBlock_of_mem_selectedSet s
      (hcore i (by simpa [hib] using hxCell))
      (hcore i (by simpa [hib] using hyCell))
      hxSelected hySelected
  have hzeroSelected : 0 ∉ selectedSet s := by
    intro hzeroSelected
    obtain ⟨b, hb, hzeroB | hzeroP | hzeroR⟩ :=
      hsCases 0 hzeroSelected
    · obtain ⟨w, _hfw⟩ := hwitness b hb
      have hbpos := w.atom_pos
      omega
    · obtain ⟨w, hfw⟩ := hwitness b hb
      apply w.zero_not_mem_vertices
      rw [← hfw, hzeroP]
      exact Finset.sdiff_subset (hp b hb)
    · have hrPetal := hr b hb
      have hzeroNotS := (Finset.mem_sdiff.mp hrPetal).2
      exact hzeroNotS (hzeroR ▸ hzeroS)
  have hcross : ∀ b ∈ B, ∀ d ∈ B, b ≠ d → ∀ x,
      x ∈ f b ∪ g b → x ∉ S → x ∈ f d ∪ g d → False := by
    intro b hb d hd hbd x hxb hxS hxd
    exact Finset.disjoint_left.mp
      (hjointDisjoint b hb d hd hbd)
      (Finset.mem_sdiff.mpr ⟨hxb, hxS⟩)
      (Finset.mem_sdiff.mpr ⟨hxd, hxS⟩)
  have htrivial : ∀ q, q ∈ A → q ∉ selectedSet s →
      ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro q hqA hqNotSelected
    have hpair : pairSupport q 0 ∈
        additiveSupportFamily A 2 q := by
      apply pairSupport_mem_additiveSupportFamily
        (Nat.zero_le q) hzeroA
      simpa using hqA
    let G : Finset ℕ := insert 0 (pairSupport q 0)
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hpair)
    refine ⟨G, hGR, ?_⟩
    rw [Set.disjoint_left]
    intro x hxG hxSelected
    have hx : x = 0 ∨ x = q := by
      simpa [G, pairSupport] using (Finset.mem_coe.mp hxG)
    rcases hx with rfl | rfl
    · exact hzeroSelected hxSelected
    · exact hqNotSelected hxSelected
  intro q hqA
  by_cases hqSelected : q ∈ selectedSet s
  · obtain ⟨b, hb, hqb | hqp | hqr⟩ := hsCases q hqSelected
    · subst q
      obtain ⟨w, hfw⟩ := hwitness b hb
      let G : Finset ℕ :=
        insert w.x (pairSupport (w.y + w.z) w.y)
      refine ⟨G, w.repairSupport_mem, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxSelected
      have hxF : x ∈ f b := by
        rw [hfw]
        exact w.repairSupport_subset_vertices (Finset.mem_coe.mp hxG)
      obtain ⟨d, hd, hxd | hxp | hxr⟩ := hsCases x hxSelected
      · subst x
        exact Set.disjoint_left.mp (hAvoid b hb)
          (Finset.mem_coe.mpr hxF) hd
      · subst x
        by_cases hbd : b = d
        · subst d
          have hEq := hselectedUnique b hb b (p b)
            (by simp [atomPetalRepairPointCell])
            (by simp [atomPetalRepairPointCell])
            hqSelected hxSelected
          exact hpOut b hb (hEq ▸ hb)
        · exact hcross b hb d hd hbd (p d)
            (Finset.mem_union_left _ hxF)
            (Finset.mem_sdiff.mp (hp d hd)).2
            (Finset.mem_union_left _
              (Finset.mem_sdiff.mp (hp d hd)).1)
      · subst x
        by_cases hbd : b = d
        · subst d
          have hEq := hselectedUnique b hb b (r b)
            (by simp [atomPetalRepairPointCell])
            (by simp [atomPetalRepairPointCell])
            hqSelected hxSelected
          exact hrOut b hb (hEq ▸ hb)
        · exact hcross b hb d hd hbd (r d)
            (Finset.mem_union_left _ hxF)
            (Finset.mem_sdiff.mp (hr d hd)).2
            (Finset.mem_union_right _
              (Finset.mem_sdiff.mp (hr d hd)).1)
    · subst q
      refine ⟨g b, (hg b hb).1, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxSelected
      obtain ⟨d, hd, hxd | hxp | hxr⟩ := hsCases x hxSelected
      · subst x
        exact Set.disjoint_left.mp (hg b hb).2.2.1 hxG hd
      · subst x
        exact (hg b hb).2.2.2 d hd (Finset.mem_coe.mp hxG)
      · subst x
        by_cases hbd : b = d
        · subst d
          have hEq := hselectedUnique b hb (p b) (r b)
            (by simp [atomPetalRepairPointCell])
            (by simp [atomPetalRepairPointCell])
            hqSelected hxSelected
          exact hpr b hb hEq
        · exact hcross b hb d hd hbd (r d)
            (Finset.mem_union_right _ (Finset.mem_coe.mp hxG))
            (Finset.mem_sdiff.mp (hr d hd)).2
            (Finset.mem_union_right _
              (Finset.mem_sdiff.mp (hr d hd)).1)
    · subst q
      refine ⟨h b, (hh b hb).1, ?_⟩
      rw [Set.disjoint_left]
      intro x hxH hxSelected
      obtain ⟨d, hd, hxd | hxp | hxr⟩ := hsCases x hxSelected
      · subst x
        exact Set.disjoint_left.mp (hh b hb).2.2.1 hxH hd
      · subst x
        exact (hh b hb).2.2.2.1 d hd (Finset.mem_coe.mp hxH)
      · subst x
        exact (hh b hb).2.2.2.2 d hd (Finset.mem_coe.mp hxH)
  · exact htrivial q hqA hqSelected

set_option maxHeartbeats 5000000 in
/-- Greedily choose one order-two support at every finite target while never
covering an entire cell of size at least three.  At a new target, forbid all
cells touched by the old support union.  Their union has size at most
`k * |U|`; a large matching of pair supports contains one support disjoint
from that forbidden union.  Since a pair support has at most two vertices,
it cannot cover a previously untouched three-point cell by itself. -/
theorem exists_pairSupportChoice_avoiding_threePointCells_of_large
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcellUpper : ∀ i, (cell i).card ≤ k)
    (hlarge : ∀ q ∈ Q,
      2 * k * Q.card < (additiveSupportFamily A 2 q).card) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∀ i, ¬ cell i ⊆ finiteSupportChoiceUnion c := by
  classical
  revert hlarge
  induction Q using Finset.induction_on with
  | empty =>
      intro _hlarge
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) ∅ := fun q => isEmptyElim q
      refine ⟨c, ?_⟩
      intro i hcovered
      have hnonempty : (cell i).Nonempty :=
        Finset.card_pos.mp
          (lt_of_lt_of_le (by norm_num : 0 < 3) (hcellLower i))
      obtain ⟨x, hxCell⟩ := hnonempty
      have hxUnion := hcovered hxCell
      simpa [finiteSupportChoiceUnion] using hxUnion
  | @insert q Q hqQ ih =>
      intro hlarge
      have hlargeQ : ∀ r ∈ Q,
          2 * k * Q.card < (additiveSupportFamily A 2 r).card := by
        intro r hrQ
        have hrLarge := hlarge r (Finset.mem_insert_of_mem hrQ)
        have hcardLt : Q.card < (insert q Q).card := by
          simp [Finset.card_insert_of_notMem hqQ]
        have hkpos : 0 < 2 * k := by
          have hlower := hcellLower 0
          have hupper := hcellUpper 0
          omega
        exact (Nat.mul_lt_mul_of_pos_left hcardLt hkpos).trans hrLarge
      obtain ⟨cQ, hcQ⟩ := ih hlargeQ
      let U : Finset ℕ := finiteSupportChoiceUnion cQ
      let T : Finset ℕ :=
        U.biUnion fun x => cell (blockIndex P x)
      have hUcard : U.card ≤ 2 * Q.card :=
        finiteSupportChoiceUnion_card_le
          (additiveSupportFamily_cardAtMost A 2) cQ
      have hTcard : T.card ≤ 2 * k * (insert q Q).card := by
        calc
          T.card ≤ ∑ x ∈ U, (cell (blockIndex P x)).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _x ∈ U, k := by
            apply Finset.sum_le_sum
            intro x _hx
            exact hcellUpper (blockIndex P x)
          _ = U.card * k := by simp
          _ ≤ (2 * Q.card) * k := Nat.mul_le_mul_right k hUcard
          _ = (2 * k) * Q.card := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ ≤ (2 * k) * (insert q Q).card :=
            Nat.mul_le_mul_left (2 * k)
              (Finset.card_le_card (Finset.subset_insert q Q))
      have hqNotDestroy : ¬ DestroysAt
          (additiveSupportFamily A 2) (T : Set ℕ) q := by
        intro hqDestroy
        have hsupportLe :=
          card_supports_le_card_of_matching_of_destroysAt
            (fun E hER =>
              additiveSupportFamily_supportsNonempty A (by omega)
                q E hER)
            (additiveSupportFamily_two_isMatching A q)
            hqDestroy
        have hqLarge := hlarge q (Finset.mem_insert_self q Q)
        omega
      obtain ⟨E, hER, hET⟩ :=
        not_destroysAt_iff.mp hqNotDestroy
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) (insert q Q) := fun t =>
        if ht : t.1 = q then
          ⟨E, by simpa [ht] using hER⟩
        else
          let tQ : {n // n ∈ Q} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          ⟨(cQ tQ).1, (cQ tQ).2⟩
      have hcCases : ∀ x,
          x ∈ finiteSupportChoiceUnion c → x ∈ E ∨ x ∈ U := by
        intro x hx
        obtain ⟨t, _htAttach, hxt⟩ := Finset.mem_biUnion.mp hx
        by_cases ht : t.1 = q
        · left
          simpa [c, ht] using hxt
        · right
          let tQ : {n // n ∈ Q} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          apply finiteSupportChoice_subset_union cQ tQ
          simpa [c, ht, tQ] using hxt
      refine ⟨c, ?_⟩
      intro i hcovered
      have hhitU : ¬ Disjoint (cell i) U := by
        intro hdisjoint
        have hcellE : cell i ⊆ E := by
          intro x hxCell
          rcases hcCases x (hcovered hxCell) with hxE | hxU
          · exact hxE
          · exact (Finset.disjoint_left.mp hdisjoint hxCell hxU).elim
        have hcellCardLe : (cell i).card ≤ E.card :=
          Finset.card_le_card hcellE
        have hEcard : E.card ≤ 2 :=
          additiveSupportFamily_cardAtMost A 2 q E hER
        have hcellCard := hcellLower i
        omega
      obtain ⟨u, huCell, huU⟩ :=
        Finset.not_disjoint_iff.mp hhitU
      have huIndex : blockIndex P u = i :=
        P.blockIndex_eq_of_mem (hcore i huCell)
      have hcellT : cell i ⊆ T := by
        intro x hxCell
        apply Finset.mem_biUnion.mpr
        refine ⟨u, huU, ?_⟩
        simpa [huIndex] using hxCell
      apply hcQ i
      intro x hxCell
      rcases hcCases x (hcovered hxCell) with hxE | hxU
      · exact (Set.disjoint_left.mp hET
          (Finset.mem_coe.mpr hxE)
          (Finset.mem_coe.mpr (hcellT hxCell))).elim
      · exact hxU

set_option maxHeartbeats 5000000 in
/-- Sharp greedy form for three-point cells.  A previously touched cell can
forbid at most one new pair support: two distinct supports completing that
same cell would share any point of the cell still missing from the old
union, contradicting the matching property of order-two supports.  Thus the
factor given by the cell size is unnecessary. -/
theorem exists_pairSupportChoice_avoiding_threePointCells_of_large_sharp
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hlarge : ∀ q ∈ Q,
      2 * Q.card < (additiveSupportFamily A 2 q).card) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∀ i, ¬ cell i ⊆ finiteSupportChoiceUnion c := by
  classical
  revert hlarge
  induction Q using Finset.induction_on with
  | empty =>
      intro _hlarge
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) ∅ := fun q => isEmptyElim q
      refine ⟨c, ?_⟩
      intro i hcovered
      have hnonempty : (cell i).Nonempty :=
        Finset.card_pos.mp
          (lt_of_lt_of_le (by norm_num : 0 < 3) (hcellLower i))
      obtain ⟨x, hxCell⟩ := hnonempty
      have hxUnion := hcovered hxCell
      simpa [finiteSupportChoiceUnion] using hxUnion
  | @insert q Q hqQ ih =>
      intro hlarge
      have hlargeQ : ∀ r ∈ Q,
          2 * Q.card < (additiveSupportFamily A 2 r).card := by
        intro r hrQ
        have hrLarge := hlarge r (Finset.mem_insert_of_mem hrQ)
        have hcardInsert : (insert q Q).card = Q.card + 1 := by
          simp [Finset.card_insert_of_notMem hqQ]
        rw [hcardInsert] at hrLarge
        omega
      obtain ⟨cQ, hcQ⟩ := ih hlargeQ
      let U : Finset ℕ := finiteSupportChoiceUnion cQ
      let I : Finset ℕ := U.image (blockIndex P)
      let Bad : Finset (Finset ℕ) :=
        (additiveSupportFamily A 2 q).filter fun E =>
          ∃ i ∈ I, cell i ⊆ U ∪ E
      have hbadWitness : ∀ E : {E // E ∈ Bad},
          ∃ i, i ∈ I ∧ cell i ⊆ U ∪ E.1 := by
        intro E
        exact (Finset.mem_filter.mp E.2).2
      choose badIndex hbadIndexMem hbadCover using hbadWitness
      let badIndexSub : {E // E ∈ Bad} → {i // i ∈ I} := fun E =>
        ⟨badIndex E, hbadIndexMem E⟩
      have hbadIndexInj : Function.Injective badIndexSub := by
        intro E E' hindex
        apply Subtype.ext
        by_contra hEE'
        have hindexVal : badIndex E = badIndex E' :=
          congrArg Subtype.val hindex
        have hnotCovered := hcQ (badIndex E)
        obtain ⟨x, hxCell, hxU⟩ :=
          Finset.not_subset.mp hnotCovered
        have hxE : x ∈ E.1 := by
          rcases Finset.mem_union.mp (hbadCover E hxCell) with hxU' | hxE
          · exact (hxU hxU').elim
          · exact hxE
        have hxCell' : x ∈ cell (badIndex E') := by
          simpa [hindexVal] using hxCell
        have hxE' : x ∈ E'.1 := by
          rcases Finset.mem_union.mp (hbadCover E' hxCell') with hxU' | hxE'
          · exact (hxU hxU').elim
          · exact hxE'
        have hER : E.1 ∈ additiveSupportFamily A 2 q :=
          (Finset.mem_filter.mp E.2).1
        have hE'R : E'.1 ∈ additiveSupportFamily A 2 q :=
          (Finset.mem_filter.mp E'.2).1
        exact Finset.disjoint_left.mp
          (additiveSupportFamily_two_isMatching A q hER hE'R hEE')
          hxE hxE'
      have hbadCardI : Bad.card ≤ I.card := by
        simpa only [Fintype.card_coe] using
          Fintype.card_le_of_injective badIndexSub hbadIndexInj
      have hIcardU : I.card ≤ U.card := by
        exact Finset.card_image_le
      have hUcard : U.card ≤ 2 * Q.card :=
        finiteSupportChoiceUnion_card_le
          (additiveSupportFamily_cardAtMost A 2) cQ
      have hbadCard : Bad.card ≤ 2 * Q.card :=
        hbadCardI.trans (hIcardU.trans hUcard)
      have hbadLt : Bad.card <
          (additiveSupportFamily A 2 q).card := by
        have hqLarge := hlarge q (Finset.mem_insert_self q Q)
        have hcardInsert : (insert q Q).card = Q.card + 1 := by
          simp [Finset.card_insert_of_notMem hqQ]
        rw [hcardInsert] at hqLarge
        omega
      obtain ⟨E, hER, hENotBad⟩ :=
        Finset.exists_mem_notMem_of_card_lt_card hbadLt
      let c : FiniteSupportChoice
          (additiveSupportFamily A 2) (insert q Q) := fun t =>
        if ht : t.1 = q then
          ⟨E, by simpa [ht] using hER⟩
        else
          let tQ : {n // n ∈ Q} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          ⟨(cQ tQ).1, (cQ tQ).2⟩
      have hcCases : ∀ x,
          x ∈ finiteSupportChoiceUnion c → x ∈ E ∨ x ∈ U := by
        intro x hx
        obtain ⟨t, _htAttach, hxt⟩ := Finset.mem_biUnion.mp hx
        by_cases ht : t.1 = q
        · left
          simpa [c, ht] using hxt
        · right
          let tQ : {n // n ∈ Q} :=
            ⟨t.1, (Finset.mem_insert.mp t.2).resolve_left ht⟩
          apply finiteSupportChoice_subset_union cQ tQ
          simpa [c, ht, tQ] using hxt
      refine ⟨c, ?_⟩
      intro i hcovered
      have hcellUE : cell i ⊆ U ∪ E := by
        intro x hxCell
        rcases hcCases x (hcovered hxCell) with hxE | hxU
        · exact Finset.mem_union_right U hxE
        · exact Finset.mem_union_left E hxU
      have hcellNotE : ¬ cell i ⊆ E := by
        intro hcellE
        have hcardLe := Finset.card_le_card hcellE
        have hEcard :=
          additiveSupportFamily_cardAtMost A 2 q E hER
        have hcellCard := hcellLower i
        omega
      obtain ⟨u, huCell, huE⟩ := Finset.not_subset.mp hcellNotE
      have huU : u ∈ U := by
        rcases Finset.mem_union.mp (hcellUE huCell) with huU | huE'
        · exact huU
        · exact (huE huE').elim
      have huIndex : blockIndex P u = i :=
        P.blockIndex_eq_of_mem (hcore i huCell)
      have hiI : i ∈ I := by
        apply Finset.mem_image.mpr
        exact ⟨u, huU, huIndex⟩
      apply hENotBad
      exact Finset.mem_filter.mpr ⟨hER, i, hiI, hcellUE⟩

/-- Pair-support padding transfers a triple selector certificate to coverage
of any zero-free dedicated cell in the partition. -/
theorem exists_coveredCell_of_tripleCertificate_and_pairChoice
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q) :
    ∃ i, cell i ⊆ finiteSupportChoiceUnion c := by
  let c₃ : FiniteSupportChoice (additiveSupportFamily A 3) Q :=
    fun q =>
      ⟨insert 0 (c q).1, by simpa using
        (insert_mem_additiveSupportFamily_succ hzeroA (c q).2)⟩
  obtain ⟨i, hiCover⟩ :=
    exists_block_subset_supportChoiceUnion_of_certificate hcert c₃
  refine ⟨i, ?_⟩
  intro x hxCell
  have hxU₃ := hiCover (hcore i hxCell)
  obtain ⟨q, _hqAttach, hxSupport⟩ :=
    Finset.mem_biUnion.mp hxU₃
  change x ∈ insert 0 (c q).1 at hxSupport
  rcases Finset.mem_insert.mp hxSupport with hx0 | hxPair
  · subst x
    exact (hcellZero i hxCell).elim
  · exact finiteSupportChoice_subset_union c q hxPair

set_option maxHeartbeats 5000000 in
/-- A selector certificate on uniformly bounded cells of size at least three
forces a target with bounded order-two multiplicity.  The former diagonal
atom-petal escape is impossible because one pair support cannot cover three
distinct dedicated choices. -/
theorem tripleCertificate_forces_boundedPairFamily_of_threePointCells
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcellUpper : ∀ i, (cell i).card ≤ k)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    ∃ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤ 2 * k * Q.card := by
  classical
  by_contra hsmall
  have hlarge : ∀ q ∈ Q,
      2 * k * Q.card < (additiveSupportFamily A 2 q).card := by
    intro q hqQ
    apply Nat.lt_of_not_ge
    intro hle
    exact hsmall ⟨q, hqQ, hle⟩
  obtain ⟨c, hcAvoid⟩ :=
    exists_pairSupportChoice_avoiding_threePointCells_of_large
      P hcore hcellLower hcellUpper hlarge
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_tripleCertificate_and_pairChoice
      hzeroA hcellZero hcore hcert c
  exact hcAvoid i hiCover

/-- The support-choice duality only needs a certificate on selectors which
choose inside the dedicated cells.  If no cell were covered, choose in every
cell a point outside the selected support union; the resulting core selector
would avoid the very support of the target certified against it. -/
theorem exists_coveredCell_of_coreSelectorCertificate_and_pairChoice
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q) :
    ∃ i, cell i ⊆ finiteSupportChoiceUnion c := by
  classical
  let c₃ : FiniteSupportChoice (additiveSupportFamily A 3) Q :=
    fun q =>
      ⟨insert 0 (c q).1, by simpa using
        (insert_mem_additiveSupportFamily_succ hzeroA (c q).2)⟩
  let U₃ : Finset ℕ := finiteSupportChoiceUnion c₃
  have hcovered₃ : ∃ i, cell i ⊆ U₃ := by
    by_contra hnone
    have hchoice : ∀ i, ∃ x, x ∈ cell i ∧ x ∉ U₃ := by
      intro i
      by_contra hi
      push_neg at hi
      apply hnone
      exact ⟨i, hi⟩
    choose x hxCell hxNotU using hchoice
    let s : BlockSelector F := fun i =>
      ⟨x i, hcore i (hxCell i)⟩
    obtain ⟨q, hqQ, hqDestroy⟩ :=
      hcert s (fun i => hxCell i)
    have hsupportDisjoint : Disjoint ((c₃ ⟨q, hqQ⟩).1 : Set ℕ)
        (selectedSet s) := by
      rw [Set.disjoint_left]
      intro y hySupport hySelected
      obtain ⟨i, hi⟩ := hySelected
      change (s i).1 = y at hi
      apply hxNotU i
      apply finiteSupportChoice_subset_union c₃ ⟨q, hqQ⟩
      have hxy : x i = y := by simpa [s] using hi
      rw [hxy]
      exact Finset.mem_coe.mp hySupport
    exact (hqDestroy (c₃ ⟨q, hqQ⟩).1
      (c₃ ⟨q, hqQ⟩).2) hsupportDisjoint
  obtain ⟨i, hiCover⟩ := hcovered₃
  refine ⟨i, ?_⟩
  intro x hxCell
  have hxU₃ := hiCover hxCell
  obtain ⟨q, _hqAttach, hxSupport⟩ :=
    Finset.mem_biUnion.mp hxU₃
  change x ∈ insert 0 (c q).1 at hxSupport
  rcases Finset.mem_insert.mp hxSupport with hx0 | hxPair
  · subst x
    exact (hcellZero i hxCell).elim
  · exact finiteSupportChoice_subset_union c q hxPair

set_option maxHeartbeats 5000000 in
/-- A certificate restricted to uniformly bounded three-point core selectors
already forces a bounded order-two target. -/
theorem coreSelectorCertificate_forces_boundedPairFamily_of_threePointCells
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcellUpper : ∀ i, (cell i).card ≤ k)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    ∃ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤ 2 * k * Q.card := by
  classical
  by_contra hsmall
  have hlarge : ∀ q ∈ Q,
      2 * k * Q.card < (additiveSupportFamily A 2 q).card := by
    intro q hqQ
    apply Nat.lt_of_not_ge
    intro hle
    exact hsmall ⟨q, hqQ, hle⟩
  obtain ⟨c, hcAvoid⟩ :=
    exists_pairSupportChoice_avoiding_threePointCells_of_large
      P hcore hcellLower hcellUpper hlarge
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_coreSelectorCertificate_and_pairChoice
      hzeroA hcellZero hcore hcert c
  exact hcAvoid i hiCover

set_option maxHeartbeats 5000000 in
/-- Sharp certificate bound for cells of size at least three.  The refined
greedy argument counts touched cells rather than every vertex in those
cells, so neither an upper cell-size bound nor the corresponding factor is
needed. -/
theorem coreSelectorCertificate_forces_boundedPairFamily_sharp
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    ∃ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  by_contra hsmall
  have hlarge : ∀ q ∈ Q,
      2 * Q.card < (additiveSupportFamily A 2 q).card := by
    intro q hqQ
    apply Nat.lt_of_not_ge
    intro hle
    exact hsmall ⟨q, hqQ, hle⟩
  obtain ⟨c, hcAvoid⟩ :=
    exists_pairSupportChoice_avoiding_threePointCells_of_large_sharp
      P hcore hcellLower hlarge
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_coreSelectorCertificate_and_pairChoice
      hzeroA hcellZero hcore hcert c
  exact hcAvoid i hiCover

set_option maxHeartbeats 5000000 in
/-- Global three-option-cell residual.  A zero-normalized counterexample
forces an infinite deletion reservoir and one fixed finite-block partition
with zero-free dedicated three-point cells.  Every late cardinal-minimal
selector certificate on this partition contains a target with at most
`2 * Q.card` order-two supports.  In particular, the former
diagonal atom-petal branch has been eliminated rather than merely renamed. -/
theorem counterexample_forces_minimalEnrichedCell_boundedPairCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ F cell : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ i, cell i ⊆ F i) ∧
        (∀ i, 0 ∉ cell i) ∧
        (∀ i, 3 ≤ (cell i).card) ∧
        (∀ i, (cell i).card ≤ 6) ∧
        ∀ N, ∃ Q : Finset ℕ,
          Q.Nonempty ∧
          (∀ q ∈ Q, N ≤ q) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          (∀ q ∈ Q, ∃ s : BlockSelector F,
            DestroysAt (additiveSupportFamily A 3)
                (selectedSet s) q ∧
              ∀ q' ∈ Q, q' ≠ q →
                ¬ DestroysAt (additiveSupportFamily A 3)
                  (selectedSet s) q') ∧
          ∃ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨B₀, hB₀A, hB₀, R, f, p, g,
      _hnormalAtom, _hnormalPetal, _hrepairs,
      hwitness₀, hAvoid₀, _hpetal₀, hpetalDisjoint₀, hp₀, hg₀⟩ :=
    counterexample_forces_doublyAtomicSelfRepairedPetalReservoir
      hbasis hzeroA hcounter
  obtain ⟨B, hBB₀, hB, S, hzeroS, hpS,
      hrepairPetal, hjointDisjoint⟩ :=
    exists_infinite_jointCliqueSelfRepairSunflower
      hB₀ hwitness₀ hpetalDisjoint₀
        (fun b hb => (hp₀ b hb).1)
        (fun b hb => ⟨(hg₀ b hb).1,
          (hg₀ b hb).2.2.1,
          (hg₀ b hb).2.2.2⟩)
  have hBA : B ⊆ A := hBB₀.trans hB₀A
  have hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices := fun b hb => hwitness₀ b (hBB₀ hb)
  have hAvoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B := by
    intro b hb
    exact (hAvoid₀ b (hBB₀ hb)).mono_right hBB₀
  have hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B := by
    intro b hb
    have hgb := hg₀ b (hBB₀ hb)
    exact ⟨hgb.1, hgb.2.1, hgb.2.2.1.mono_right hBB₀⟩
  obtain ⟨r, hr, e, F, P, hEnrichedCore, _hEnrichedLower⟩ :=
    exists_finiteBlockPartition_for_enrichedCliqueSunflower
      hBA hB hwitness hAvoid hpS hg hrepairPetal hjointDisjoint
  let cell : ℕ → Finset ℕ := fun i =>
    atomPetalRepairCell p r (e i).1
  have hcellEnriched : ∀ i, cell i ⊆
      enrichedExternalCliqueCell S f r (e i).1 := by
    intro i x hxCell
    simp only [cell, atomPetalRepairCell, Finset.mem_insert] at hxCell
    rcases hxCell with hxb | hxp | hxr
    · exact Finset.mem_union_right _ (hxb ▸ Finset.mem_insert_self _ _)
    · apply Finset.mem_union_right
      rw [externalCliqueCell]
      exact Finset.mem_insert_of_mem (hxp ▸ hpS (e i).1 (e i).2)
    · exact Finset.mem_union_left _ hxr
  have hcore : ∀ i, cell i ⊆ F i := fun i =>
    (hcellEnriched i).trans (hEnrichedCore i)
  have hEnrichedZero : ∀ i,
      0 ∉ enrichedExternalCliqueCell S f r (e i).1 := by
    intro i hzeroCell
    let b := (e i).1
    rcases Finset.mem_union.mp hzeroCell with hzeroR | hzeroExternal
    · have hzeroPetal := (hr b (e i).2).1 hzeroR
      exact (Finset.mem_sdiff.mp hzeroPetal).2 hzeroS
    · rcases Finset.mem_insert.mp hzeroExternal with hzeroB | hzeroF
      · obtain ⟨w, _hfw⟩ := hwitness b (e i).2
        have hbpos := w.atom_pos
        omega
      · obtain ⟨w, hfw⟩ := hwitness b (e i).2
        apply w.zero_not_mem_vertices
        rw [← hfw]
        exact Finset.sdiff_subset hzeroF
  have hcellZero : ∀ i, 0 ∉ cell i := by
    intro i hzeroCell
    exact hEnrichedZero i (hcellEnriched i hzeroCell)
  have hcellCard : ∀ i, (cell i).card = 3 := by
    intro i
    let b := (e i).1
    have hpb : b ≠ p b := by
      intro hEq
      exact Set.disjoint_left.mp (hAvoid b (e i).2)
        (Finset.mem_coe.mpr (Finset.sdiff_subset (hpS b (e i).2)))
        (hEq ▸ (e i).2)
    have hpNotR : p b ∉ r b := by
      intro hpr
      apply (hg b (e i).2).2.1
      exact (Finset.mem_sdiff.mp ((hr b (e i).2).1 hpr)).1
    have hbNotR : b ∉ r b := by
      intro hbr
      have hbG := (Finset.mem_sdiff.mp ((hr b (e i).2).1 hbr)).1
      exact Set.disjoint_left.mp (hg b (e i).2).2.2
        (Finset.mem_coe.mpr hbG) (e i).2
    change (atomPetalRepairCell p r b).card = 3
    rw [atomPetalRepairCell,
      Finset.card_insert_of_notMem (by simpa [hpb] using hbNotR),
      Finset.card_insert_of_notMem hpNotR,
      (hr b (e i).2).2]
  have hcellLower : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have hcellUpper : ∀ i, (cell i).card ≤ 3 := by
    intro i
    rw [hcellCard i]
  refine ⟨B, hBA, hB, F, cell, P, hcore,
    hcellZero, hcellLower,
    (fun i => (hcellUpper i).trans (by omega)), ?_⟩
  intro N
  obtain ⟨Q₁, hQ₁N, hcert₁⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      (strongOrderThreeDeletion_of_counterexample hcounter) F P N
  obtain ⟨Q, hQQ₁, hcert, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate hcert₁
  let arbitrarySelector : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q₀, hq₀Q, _hq₀Destroy⟩ := hcert arbitrarySelector
  have hQ : Q.Nonempty := ⟨q₀, hq₀Q⟩
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hqQ
    exact hQ₁N q (hQQ₁ hqQ)
  obtain ⟨q, hqQ, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLower (fun s _hs => hcert s)
  refine ⟨Q, hQ, hQN, hcert, hlocalized, q, hqQ, ?_⟩
  simpa using hqBound

set_option maxHeartbeats 5000000 in
/-- Strongest external-target form of the three-option bridge.  A
zero-normalized counterexample supplies one fixed partition into dedicated
three-point cores such that, at every late threshold, a finite set of targets
outside `A` certifies every selector restricted to those cores.  One of those
external targets has at most `2 * Q.card` order-two supports. -/
theorem counterexample_forces_externalCoreCertificate_boundedPairFamily
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ F cell : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ i, cell i ⊆ F i) ∧
        (∀ i, 0 ∉ cell i) ∧
        (∀ i, (cell i).card = 3) ∧
        ∀ N, ∃ Q : Finset ℕ,
          Q.Nonempty ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ s : BlockSelector F,
            (∀ i, (s i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet s) q) ∧
          ∃ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨B, hBA, hB, S, f, p, r, g, h,
      hzeroS, hwitness, hAvoid, hpData, hrData,
      hjointDisjoint, hg, hh⟩ :=
    counterexample_forces_triplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  have hpA : ∀ b ∈ B, p b ∈ A := by
    intro b hb
    obtain ⟨w, hfw⟩ := hwitness b hb
    apply w.vertices_subset
    rw [← hfw]
    exact Finset.sdiff_subset (hpData b hb).1
  have hrA : ∀ b ∈ B, r b ∈ A := by
    intro b hb
    exact additiveSupportFamily_supportsIn A 3 (p b) (g b)
      (hg b hb).1 (r b)
      (Finset.mem_sdiff.mp (hrData b hb).1).1
  have hpOut : ∀ b ∈ B, p b ∉ B := by
    intro b hb hpbB
    exact Set.disjoint_left.mp (hAvoid b hb)
      (Finset.mem_coe.mpr
        (Finset.sdiff_subset (hpData b hb).1)) hpbB
  have hrOut : ∀ b ∈ B, r b ∉ B := by
    intro b hb hrbB
    exact Set.disjoint_left.mp (hg b hb).2.2.1
      (Finset.mem_coe.mpr
        (Finset.sdiff_subset (hrData b hb).1)) hrbB
  have hpr : ∀ b ∈ B, p b ≠ r b := by
    intro b hb hEq
    exact (hg b hb).2.1
      (hEq ▸ Finset.sdiff_subset (hrData b hb).1)
  have hoptionPetal : ∀ b ∈ B, ∀ x ∈ ({p b, r b} : Finset ℕ),
      x ∈ (f b ∪ g b) \ S := by
    intro b hb x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hpData b hb).1).1,
          (Finset.mem_sdiff.mp (hpData b hb).1).2⟩
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hrData b hb).1).1,
          (Finset.mem_sdiff.mp (hrData b hb).1).2⟩
  have hoptionsDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint ({p b, r b} : Finset ℕ) {p d, r d} := by
    intro b hb d hd hbd
    rw [Finset.disjoint_left]
    intro x hxb hxd
    exact Finset.disjoint_left.mp
      (hjointDisjoint b hb d hd hbd)
      (hoptionPetal b hb x hxb) (hoptionPetal d hd x hxd)
  obtain ⟨e, F, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_for_atomPetalRepairPointCells
      hBA hB p r hpA hrA hpOut hrOut hpr hoptionsDisjoint
  let cell : ℕ → Finset ℕ := fun i =>
    atomPetalRepairPointCell p r (e i).1
  have hcellZero : ∀ i, 0 ∉ cell i := by
    intro i hzeroCell
    let b := (e i).1
    simp only [cell, atomPetalRepairPointCell, Finset.mem_insert,
      Finset.mem_singleton] at hzeroCell
    rcases hzeroCell with hzeroB | hzeroP | hzeroR
    · obtain ⟨w, _hfw⟩ := hwitness b (e i).2
      have hbpos := w.atom_pos
      omega
    · obtain ⟨w, hfw⟩ := hwitness b (e i).2
      apply w.zero_not_mem_vertices
      rw [← hfw, hzeroP]
      exact Finset.sdiff_subset (hpData b (e i).2).1
    · exact (Finset.mem_sdiff.mp (hrData b (e i).2).1).2
        (hzeroR ▸ hzeroS)
  have hsurviveCore : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet s) := by
    intro s hs
    exact internalTarget_survives_atomPetalRepairPointSelector
      hzeroA P hzeroS hwitness hAvoid
        (fun b hb => (hpData b hb).1)
        (fun b hb => (hrData b hb).1)
        hjointDisjoint hg hh hcore s hs
  refine ⟨B, hBA, hB, F, cell, P, hcore,
    hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q₀, hQ₀N, hcert₀⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      (strongOrderThreeDeletion_of_counterexample hcounter) F P N
  let Q : Finset ℕ := Q₀.filter fun q => q ∉ A
  have hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q := by
    intro s hs
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ s
    have hqA : q ∉ A := by
      intro hqA
      obtain ⟨G, hGR, hGdisjoint⟩ := hsurviveCore s hs q hqA
      exact (hqDestroy G hGR) hGdisjoint
    exact ⟨q, Finset.mem_filter.mpr ⟨hqQ₀, hqA⟩, hqDestroy⟩
  let atomSelector : BlockSelector F := fun i =>
    ⟨(e i).1, hcore i (by
      simp [cell, atomPetalRepairPointCell])⟩
  have hatomCore : ∀ i, (atomSelector i).1 ∈ cell i := by
    intro i
    simp [atomSelector, cell, atomPetalRepairPointCell]
  obtain ⟨q₀, hq₀Q, _hq₀Destroy⟩ := hcert atomSelector hatomCore
  have hQ : Q.Nonempty := ⟨q₀, hq₀Q⟩
  have hQN : ∀ q ∈ Q, N ≤ q ∧ q ∉ A := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨hQ₀N q hq.1, hq.2⟩
  have hcellLower : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  obtain ⟨q, hqQ, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLower hcert
  refine ⟨Q, hQ, hQN, hcert, q, hqQ, ?_⟩
  simpa using hqBound

set_option maxHeartbeats 5000000 in
/-- Minimal external-core residual.  In addition to excluding every target
in `A`, shrink the restricted three-option certificate until every remaining
external target has a private core selector: that selector destroys the
chosen target and no other target in the same certificate.  The sharp
`2 * Q.card` pair-support bound is retained after shrinking. -/
theorem counterexample_forces_minimalExternalCoreCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ F cell : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ i, cell i ⊆ F i) ∧
        (∀ i, 0 ∉ cell i) ∧
        (∀ i, (cell i).card = 3) ∧
        ∀ N, ∃ Q : Finset ℕ,
          Q.Nonempty ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ s : BlockSelector F,
            (∀ i, (s i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet s) q) ∧
          (∀ q ∈ Q, ∃ s : BlockSelector F,
            (∀ i, (s i).1 ∈ cell i) ∧
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q ∧
            DestroysAt (additiveSupportFamily A 2)
              (selectedSet s) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt (additiveSupportFamily A 3)
                (selectedSet s) q') ∧
          ∃ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
      hcellCard, hresidual⟩ :=
    counterexample_forces_externalCoreCertificate_boundedPairFamily
      hbasis hzeroA hcounter
  refine ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
    hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, hQN, hcert, _hqBound⟩ := hresidual N
  let Good : BlockSelector F → Prop := fun s =>
    ∀ i, (s i).1 ∈ cell i
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    exact Finset.card_pos.mp (by rw [hcellCard i]; omega)
  let coreSelector : BlockSelector F := fun i =>
    ⟨(hcellNonempty i).choose,
      hcore i (hcellNonempty i).choose_spec⟩
  have hcoreSelector : Good coreSelector := by
    intro i
    exact (hcellNonempty i).choose_spec
  obtain ⟨q₀, hq₀Q₀, _hq₀Destroy⟩ :=
    hcert₀ coreSelector hcoreSelector
  have hQ₀ : Q₀.Nonempty := ⟨q₀, hq₀Q₀⟩
  have hQ₀N : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    exact hQN q (hQ₀Q hqQ₀)
  have hcellLower : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  obtain ⟨q, hqQ₀, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLower hcert₀
  have hlocalized₂ : ∀ q ∈ Q₀, ∃ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) ∧
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q ∧
      DestroysAt (additiveSupportFamily A 2) (selectedSet s) q ∧
      ∀ q' ∈ Q₀, q' ≠ q →
        ¬ DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q' := by
    intro q hqQ₀
    obtain ⟨s, hsCore, hqDestroy, hprivate⟩ :=
      hlocalized q hqQ₀
    have hzeroSelected : 0 ∉ selectedSet s := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hsCore i
    exact ⟨s, hsCore, hqDestroy,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy,
      hprivate⟩
  refine ⟨Q₀, hQ₀, hQ₀N, hcert₀, hlocalized₂,
    q, hqQ₀, ?_⟩
  simpa using hqBound

set_option maxHeartbeats 5000000 in
/-- Same-certificate arithmetic fork.  The amplified target set `Q`
simultaneously certifies all selectors and covers arbitrarily many sunflower
cells; on that very `Q`, either one `B`-destroyed target has bounded pair
multiplicity, or `3 * Q.card + 1` disjoint covering systems force a genuine
cross-alignment. -/
theorem exists_certifiedCovered_boundedPairSupports_or_highAlignment
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hBA : B ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ q ∈ Q, (additiveSupportFamily A 2 q).Nonempty) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q) ∧
      (∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I,
            externalCliqueCell R f (e i).1 ⊆
              finiteSupportChoiceUnion c) ∧
      ((∃ q ∈ Q,
          DestroysAt (additiveSupportFamily A 3) B q ∧
          (additiveSupportFamily A 2 q).card <
            (3 * Q.card + 1) *
              (destroyedCertificateTargets A B Q).card) ∨
        ∃ systems : Finset (Finset ℕ),
          systems.card = 3 * Q.card + 1 ∧
          IsMatching systems ∧
          (∀ S ∈ systems,
            (∀ b ∈ S, b ∈ B) ∧
            ∀ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3) B q →
              ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q) ∧
          ∃ S ∈ systems, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3) B q ∧
            ∃ b ∈ S, ∃ d ∈ S, b + p d = q) := by
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro M start N
  obtain ⟨Q, hQlate, hcert, _hexternal, hmany⟩ :=
    exists_certifiedCoveredSelfRepairedPetalTargets
      hbasis hzeroA hcounter P hBA hrepairs hwitness havoid
        hpetalDisjoint hp
        (fun b hb => ⟨(hg b hb).1, (hg b hb).2.1,
          (hg b hb).2.2.1⟩)
        hcore M start (max N N₂)
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hq
    exact (le_max_left N N₂).trans (hQlate q hq)
  have hpair : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hq
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQlate q hq))
    exact ⟨E, hER⟩
  have htriple : ∀ q ∈ Q,
      (additiveSupportFamily A 3 q).Nonempty := by
    intro q hq
    obtain ⟨E, hER⟩ := hpair q hq
    exact ⟨insert 0 E, by simpa using
      (insert_mem_additiveSupportFamily_succ hzeroA hER)⟩
  have hdichotomy :=
    finiteCertificate_forces_boundedPairSupports_or_highAlignment
      hBA hzeroA hrepairs hwitness havoid hpetalDisjoint hp hg
        hcore hcert htriple
  exact ⟨Q, hQN, hpair, hcert, hmany, hdichotomy⟩

set_option maxHeartbeats 5000000 in
/-- Minimal-certificate sharpening of the arithmetic fork.  The large set
`Q` retains the amplified covered-cell property, while a cardinal-minimal
subcertificate `Q₀ ⊆ Q` controls the selector obstruction.  Every target of
`Q₀` has a private selector, and all bounded-support/high-alignment thresholds
now involve `Q₀.card` rather than the possibly much larger amplified union. -/
theorem exists_coveredTargets_and_minimalCertificate_arithmeticFork
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    {R : Finset ℕ} {f : ℕ → Finset ℕ}
    {p : ℕ → ℕ} {g : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hBA : B ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (havoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hpetalDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (f b \ R) (f d \ R))
    (hp : ∀ b ∈ B, p b ∈ f b \ R ∧ p b < b)
    (hg : ∀ b ∈ B,
      g b ∈ additiveSupportFamily A 3 (p b) ∧
      p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
      ∀ d ∈ B, p d ∉ g b)
    (hcore : ∀ i, externalCliqueCell R f (e i).1 ⊆ F i) :
    ∀ M start N, ∃ Q Q₀ : Finset ℕ,
      Q₀ ⊆ Q ∧ Q₀.Nonempty ∧
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ q ∈ Q, (additiveSupportFamily A 2 q).Nonempty) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q₀,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q) ∧
      (∀ q ∈ Q₀, ∃ s : BlockSelector F,
        DestroysAt (additiveSupportFamily A 3)
            (selectedSet s) q ∧
          ∀ q' ∈ Q₀, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q') ∧
      (∀ c₀ : FiniteSupportChoice
          (additiveSupportFamily A 2) Q₀,
        ∃ i, externalCliqueCell R f (e i).1 ⊆
          finiteSupportChoiceUnion c₀) ∧
      (∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I,
            externalCliqueCell R f (e i).1 ⊆
              finiteSupportChoiceUnion c) ∧
      ((∃ q ∈ Q₀,
          (additiveSupportFamily A 2 q).card ≤ 2 * Q₀.card) ∨
        ∃ q ∈ Q₀, ∃ b ∈ B,
          q = b + p b ∧
          {b, p b} ∈ additiveSupportFamily A 2 q) ∧
      ((∃ q ∈ Q₀,
          DestroysAt (additiveSupportFamily A 3) B q ∧
          (additiveSupportFamily A 2 q).card <
            (3 * Q₀.card + 1) *
              (destroyedCertificateTargets A B Q₀).card) ∨
        ∃ systems : Finset (Finset ℕ),
          systems.card = 3 * Q₀.card + 1 ∧
          IsMatching systems ∧
          (∀ S ∈ systems,
            (∀ b ∈ S, b ∈ B) ∧
            ∀ q ∈ Q₀,
              DestroysAt (additiveSupportFamily A 3) B q →
              ∃ b ∈ S, ∃ c ∈ A \ B, b + c = q) ∧
          ∃ S ∈ systems, ∃ q ∈ Q₀,
            DestroysAt (additiveSupportFamily A 3) B q ∧
            ∃ b ∈ S, ∃ d ∈ S, b + p d = q) := by
  intro M start N
  obtain ⟨Q, hQN, hpair, hcert, hmany, _hfork⟩ :=
    exists_certifiedCovered_boundedPairSupports_or_highAlignment
      hbasis hzeroA hcounter P hBA hrepairs hwitness havoid
        hpetalDisjoint hp hg hcore M start N
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate hcert
  let arbitrarySelector : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q₀, hq₀Q₀, _hq₀Destroy⟩ := hcert₀ arbitrarySelector
  have hQ₀ : Q₀.Nonempty := ⟨q₀, hq₀Q₀⟩
  have htriple₀ : ∀ q ∈ Q₀,
      (additiveSupportFamily A 3 q).Nonempty := by
    intro q hqQ₀
    obtain ⟨E, hER⟩ := hpair q (hQ₀Q hqQ₀)
    exact ⟨insert 0 E, by simpa using
      (insert_mem_additiveSupportFamily_succ hzeroA hER)⟩
  have hfork₀ :=
    finiteCertificate_forces_boundedPairSupports_or_highAlignment
      hBA hzeroA hrepairs hwitness havoid hpetalDisjoint hp hg
        hcore hcert₀ htriple₀
  have hcovered₀ : ∀ c₀ : FiniteSupportChoice
      (additiveSupportFamily A 2) Q₀,
      ∃ i, externalCliqueCell R f (e i).1 ⊆
        finiteSupportChoiceUnion c₀ := by
    intro c₀
    exact exists_coveredSunflowerCell_of_tripleCertificate_and_pairChoice
      hzeroA hwitness hcore hcert₀ c₀
  have hsharpFork₀ :=
    tripleCertificate_forces_smallPairFamily_or_diagonalPetalEquation
      hzeroA hwitness havoid hpetalDisjoint
        (fun b hb => (hp b hb).1) hcore hcert₀
  exact ⟨Q, Q₀, hQ₀Q, hQ₀, hQN, hpair, hcert₀,
    hlocalized, hcovered₀, hmany, hsharpFork₀, hfork₀⟩

set_option maxHeartbeats 5000000 in
/-- Global quantitative batch residual.  A zero-normalized counterexample
contains one self-repaired sunflower reservoir on which, at every scale, the
same amplified certificate both covers arbitrarily many cells and permits at
most `3 * Q.card` pairwise-disjoint alignment-free endpoint systems. -/
theorem counterexample_forces_certifiedBatchPetalObstruction
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p : ℕ → ℕ, ∃ g : ℕ → Finset ℕ,
      ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ b ∈ B, p b ∈ f b \ R ∧ p b < b) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        (∀ i, externalCliqueCell R f (e i).1 ⊆ F i) ∧
        (∀ i, 2 ≤ (externalCliqueCell R f (e i).1).card) ∧
        ∀ M start N, ∃ Q : Finset ℕ, ∃ S : Finset ℕ,
          (∀ q ∈ Q, N ≤ q) ∧
          (∀ q ∈ Q,
            (additiveSupportFamily A 2 q).Nonempty) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          S.Nonempty ∧ (∀ b ∈ S, b ∈ B) ∧
          ((∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3) B q ∧
              ∃ b ∈ S, ∃ d ∈ S, b + p d = q) ∨
            ∃ q' ∈ Q, q' ∉ A ∧
              ¬ DestroysAt (additiveSupportFamily A 3) B q' ∧
              ∀ H ∈ additiveSupportFamily A 3 q',
                Disjoint (H : Set ℕ) B →
                ¬ Disjoint (H : Set ℕ)
                  (p '' (S : Set ℕ))) ∧
          (∀ c : FiniteSupportChoice
              (additiveSupportFamily A 2) Q,
            ∃ I : Finset ℕ,
              I.card = M ∧
              (∀ i ∈ I, start ≤ i) ∧
              ∀ i ∈ I,
                externalCliqueCell R f (e i).1 ⊆
                  finiteSupportChoiceUnion c) ∧
          ∀ systems : Finset (Finset ℕ),
            (∀ T ∈ systems, ∀ b ∈ T, b ∈ B) →
            IsMatching systems →
            (∀ T ∈ systems, ∀ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3) B q →
              ∃ b ∈ T, ∃ c ∈ A \ B,
                b + c = q ∧ c ∉ p '' (T : Set ℕ)) →
            systems.card ≤ 3 * Q.card := by
  obtain ⟨B, hBA, hB, R, f, p, g, hnormal, hrepairs,
      hwitness, havoid, hpetal, hpetalDisjoint, hp, hg⟩ :=
    counterexample_forces_selfRepairedPetalReservoir
      hbasis hzeroA hcounter
  obtain ⟨e, F, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_for_externalCliqueSunflower
      hBA hB hwitness havoid hpetal hpetalDisjoint
  refine ⟨B, hBA, hB, R, f, p, g, e, F, P,
    hnormal, hrepairs, hwitness, havoid, hpetal,
    hpetalDisjoint, hp, hg, hcore, hcellCard, ?_⟩
  exact exists_certifiedCoveredBatchPetalObstruction
    hbasis hzeroA hcounter P hBA hrepairs hwitness havoid
      hpetalDisjoint hp hg hcore

set_option maxHeartbeats 5000000 in
/-- Global strongest residual currently obtained from a zero-normalized
counterexample: one fixed self-repaired sunflower reservoir supports the
combined finite certificate, coverage, and external-migration conclusions at
every requested scale. -/
theorem counterexample_forces_certifiedSelfRepairedPetalMigration
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p : ℕ → ℕ, ∃ g : ℕ → Finset ℕ,
      ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ b ∈ B, p b ∈ f b \ R ∧ p b < b) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        (∀ i, externalCliqueCell R f (e i).1 ⊆ F i) ∧
        (∀ i, 2 ≤ (externalCliqueCell R f (e i).1).card) ∧
        ∀ M start N, ∃ Q : Finset ℕ,
          (∀ q ∈ Q, N ≤ q) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          (∃ q ∈ Q, q ∉ A ∧
            DestroysAt (additiveSupportFamily A 3) B q ∧
            ∃ E ∈ additiveSupportFamily A 2 q,
              (¬ Disjoint (E : Set ℕ) B ∧
                ¬ (E : Set ℕ) ⊆ B) ∧
              HasPetalAlignmentOrExternalMigration
                A B p e F Q q) ∧
          ∀ c : FiniteSupportChoice
              (additiveSupportFamily A 2) Q,
            ∃ I : Finset ℕ,
              I.card = M ∧
              (∀ i ∈ I, start ≤ i) ∧
              ∀ i ∈ I,
                externalCliqueCell R f (e i).1 ⊆
                  finiteSupportChoiceUnion c := by
  obtain ⟨B, hBA, hB, R, f, p, g, hnormal, hrepairs,
      hwitness, havoid, hpetal, hpetalDisjoint, hp, hg⟩ :=
    counterexample_forces_selfRepairedPetalReservoir
      hbasis hzeroA hcounter
  obtain ⟨e, F, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_for_externalCliqueSunflower
      hBA hB hwitness havoid hpetal hpetalDisjoint
  refine ⟨B, hBA, hB, R, f, p, g, e, F, P,
    hnormal, hrepairs, hwitness, havoid, hpetal,
    hpetalDisjoint, hp, hg, hcore, hcellCard, ?_⟩
  exact exists_certifiedCoveredSelfRepairedPetalTargets
    hbasis hzeroA hcounter P hBA hrepairs hwitness havoid
      hpetalDisjoint hp
      (fun b hb => ⟨(hg b hb).1, (hg b hb).2.1,
        (hg b hb).2.2.1⟩) hcore

set_option maxHeartbeats 5000000 in
/-- Global form of the certified sunflower bridge.  A zero-normalized
counterexample contains one fixed repaired sunflower reservoir and block
partition on which the combined conclusion of
`exists_certifiedCoveredSunflowerTargets` holds at every scale. -/
theorem counterexample_forces_certifiedCoveredSunflowerCells
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ R : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        (∀ b ∈ B, ∀ E ∈ additiveSupportFamily A 2 b,
          E = {b, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, (f b \ R).Nonempty) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint (f b \ R) (f d \ R)) ∧
        (∀ i, externalCliqueCell R f (e i).1 ⊆ F i) ∧
        (∀ i, 2 ≤ (externalCliqueCell R f (e i).1).card) ∧
        ∀ M start N, ∃ Q : Finset ℕ,
          (∀ q ∈ Q, N ≤ q) ∧
          (∀ s : BlockSelector F, ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet s) q) ∧
          (∃ q ∈ Q, q ∉ A ∧
            DestroysAt (additiveSupportFamily A 3) B q ∧
            ∃ E ∈ additiveSupportFamily A 2 q,
              ¬ Disjoint (E : Set ℕ) B ∧
              ¬ (E : Set ℕ) ⊆ B) ∧
          ∀ c : FiniteSupportChoice
              (additiveSupportFamily A 2) Q,
            ∃ I : Finset ℕ,
              I.card = M ∧
              (∀ i ∈ I, start ≤ i) ∧
              ∀ i ∈ I,
                externalCliqueCell R f (e i).1 ⊆
                  finiteSupportChoiceUnion c := by
  obtain ⟨B, hBA, hB, R, f, hnormal, hrepairs,
      hwitness, havoid, hpetal, hpetalDisjoint⟩ :=
    counterexample_forces_sunflowerRepairedReservoir
      hbasis hzeroA hcounter
  obtain ⟨e, F, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_for_externalCliqueSunflower
      hBA hB hwitness havoid hpetal hpetalDisjoint
  refine ⟨B, hBA, hB, R, f, e, F, P, hnormal,
    hrepairs, hwitness, havoid, hpetal, hpetalDisjoint,
    hcore, hcellCard, ?_⟩
  exact exists_certifiedCoveredSunflowerTargets
    hbasis hzeroA hcounter P hrepairs hwitness havoid hcore

/-- Strong order-two deletion supplies the amplified finite certificate in
the exact pair-support form needed to confront the external four-clique
obstruction. -/
theorem strongOrderTwoDeletion_forces_arbitrarilyManyCoveredPairBlocks
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 2) A) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      ∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c :=
  exists_manyCoveredBlocks_of_strongInfiniteDeletion P hstrong

/-- Combined verified residual for a zero-normalized strongly minimal
order-two basis.  If no infinite deletion leaves order three, then both the
arbitrarily late external four-cliques and the arbitrarily large covered-block
pair certificates must coexist. -/
theorem stronglyMinimal_counterexample_forces_fourCliques_and_pairCertificates
    {A : Set ℕ}
    (hminimal : IsStronglyMinimalExactBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    (∀ N, ∃ n b c x y z,
      N ≤ n ∧ n ∉ A ∧
      b ∈ A ∧ c ∈ A ∧ x ∈ A ∧ y ∈ A ∧ z ∈ A ∧
      0 < c ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      x + y + z = b ∧ b + c = n ∧
      (∀ E ∈ additiveSupportFamily A 2 b, E = {b, 0}) ∧
      x + y ∉ A ∧ x + z ∉ A ∧ y + z ∉ A ∧
      x + c ∉ A ∧ y + c ∉ A ∧ z + c ∉ A) ∧
    ∀ (F : ℕ → Finset ℕ), IsFiniteBlockPartition A F →
      ∀ M start N, ∃ Q : Finset ℕ,
        (∀ q ∈ Q, N ≤ q) ∧
        ∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
          ∃ I : Finset ℕ,
            I.card = M ∧
            (∀ i ∈ I, start ≤ i) ∧
            ∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c := by
  constructor
  · exact counterexample_forces_arbitrarilyLate_externalFourCliques
      hminimal.1 hzeroA hcounter
  · intro F P
    exact
      strongOrderTwoDeletion_forces_arbitrarilyManyCoveredPairBlocks
        P hminimal.2

/-- In any counterexample, order-three certificates force arbitrarily many
whole blocks at once.  This is the amplified finite-certificate obstruction
that a bounded-stratum construction must now beat by a uniform upper bound. -/
theorem counterexample_forces_arbitrarilyManyCoveredTripleBlocks
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      ∀ c : FiniteSupportChoice (additiveSupportFamily A 3) Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c :=
  exists_manyCoveredBlocks_of_strongInfiniteDeletion P
    (strongOrderThreeDeletion_of_counterexample hcounter)

/-- Equivalently, no block partition of a counterexample can admit a
uniform bound on the number of blocks covered by suitably chosen finite
order-three supports. -/
theorem counterexample_forbids_uniformCoveredTripleBlockChoices
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ¬ HasUniformCoveredBlockSupportChoices
      (additiveSupportFamily A 3) F := by
  intro hbound
  exact
    (not_strongInfiniteDeletion_of_uniformCoveredBlockSupportChoices
      P hbound)
      (strongOrderThreeDeletion_of_counterexample hcounter)

end Erdos881
