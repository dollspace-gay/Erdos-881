import Erdos881.BoundedStratumSplitting
import Erdos881.CertificateAmplification
import Erdos881.HybridPairTripleRepairs
import Erdos881.InfiniteSunflower
import Erdos881.ReflectionDefects

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

/-! ## The crossing-endpoint thinning bridge -/

/-- A thinning `B ⊆ B₀` eventually omits a crossing endpoint at every
target whose entire order-two support family crosses the old reservoir
`B₀`.  This is the exact finite-edge independence condition left after
direct triple repairs have been installed on `B₀`: an omitted old-red
endpoint turns its crossing pair into a wholly retained pair for `B`. -/
def HasEventuallyOmittedCrossingEndpoint
    (A B₀ B : Set ℕ) : Prop :=
  ∃ N, ∀ q, N ≤ q →
    (∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) →
    ¬ (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ B

/-- Exact completion theorem for the crossing-endpoint formulation.  Pair
supports which are blue relative to `B₀` remain blue after thinning;
supports wholly inside `B₀` use the already installed direct triple
repair; and at an all-crossing target the omitted endpoint supplied by
`HasEventuallyOmittedCrossingEndpoint` gives a blue pair for the thinning.

Thus constructing an infinite `B ⊆ B₀` with the omitted-endpoint
property is sufficient for the desired infinite deletion. -/
theorem exactThreeBasis_of_omittedCrossingEndpoint_thinning
    {A B₀ B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hBB₀ : B ⊆ B₀)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (homit : HasEventuallyOmittedCrossingEndpoint A B₀ B) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  apply hasEventuallySurvivingSupport_additive_iff.mp
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨Nₒ, hNₒ⟩ := homit
  refine ⟨max N₂ Nₒ, ?_⟩
  intro q hq
  have hqN₂ : N₂ ≤ q := (le_max_left N₂ Nₒ).trans hq
  have hqNₒ : Nₒ ≤ q := (le_max_right N₂ Nₒ).trans hq
  by_cases hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀
  · have hnsub := hNₒ q hqNₒ hcross
    obtain ⟨b, hbEndpoint, hbB⟩ := Set.not_subset.mp hnsub
    have hbData := mem_crossingAtomEndpoints_iff.mp
      (Finset.mem_coe.mp hbEndpoint)
    let E : Finset ℕ := pairSupport q b
    have hER : E ∈ additiveSupportFamily A 2 q := by
      exact pairSupport_mem_additiveSupportFamily hbData.1
        (hB₀A hbData.2.1) hbData.2.2.1
    have hEB : Disjoint (E : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxE hxB
      have hxCases : x = b ∨ x = q - b := by
        simpa [E, pairSupport] using hxE
      rcases hxCases with rfl | rfl
      · exact hbB hxB
      · exact hbData.2.2.2 (hBB₀ hxB)
    let G : Finset ℕ := insert 0 E
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hER)
    have hGB : Disjoint (G : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxG hxB
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hxG) with rfl | hxE
      · exact hzeroB₀ (hBB₀ hxB)
      · exact Set.disjoint_left.mp hEB
          (Finset.mem_coe.mpr hxE) hxB
    exact ⟨G, hGR, hGB⟩
  · push Not at hcross
    obtain ⟨E, hER, hnotCross⟩ := hcross
    by_cases hblue₀ : Disjoint (E : Set ℕ) B₀
    · let G : Finset ℕ := insert 0 E
      have hGR : G ∈ additiveSupportFamily A 3 q := by
        simpa [G] using
          (insert_mem_additiveSupportFamily_succ hzeroA hER)
      have hGB : Disjoint (G : Set ℕ) B := by
        rw [Set.disjoint_left]
        intro x hxG hxB
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hxG) with rfl | hxE
        · exact hzeroB₀ (hBB₀ hxB)
        · exact Set.disjoint_left.mp hblue₀
            (Finset.mem_coe.mpr hxE) (hBB₀ hxB)
      exact ⟨G, hGR, hGB⟩
    · have hred₀ : (E : Set ℕ) ⊆ B₀ := hnotCross hblue₀
      obtain ⟨v, _hvA, hvsum, rfl⟩ :=
        mem_additiveSupportFamily_iff.mp hER
      have hv0B₀ : (v 0).1 ∈ B₀ :=
        hred₀ (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
      have hv1B₀ : (v 1).1 ∈ B₀ :=
        hred₀ (mem_tupleSupport_iff.mpr ⟨1, rfl⟩)
      have hsum : (v 0).1 + (v 1).1 = q := by
        simpa [Fin.sum_univ_two] using hvsum
      obtain ⟨G, hGR, hGB₀⟩ :=
        hrepairs (v 0).1 hv0B₀ (v 1).1 hv1B₀
      rw [hsum] at hGR
      exact ⟨G, hGR, hGB₀.mono_right hBB₀⟩

/-- Existence wrapper in the form used by the deletion problem. -/
theorem exists_infiniteDeletion_threeBasis_of_omittedCrossingEndpoints
    {A B₀ : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hselection : ∃ B, B ⊆ B₀ ∧ B.Infinite ∧
      HasEventuallyOmittedCrossingEndpoint A B₀ B) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hBB₀, hB, homit⟩ := hselection
  exact ⟨B, hBB₀.trans hB₀A, hB,
    exactThreeBasis_of_omittedCrossingEndpoint_thinning
      hbasis hzeroA hzeroB₀ hB₀A hBB₀ hrepairs homit⟩

/-- A support hypergraph encoding the crossing-endpoint obstruction.  At an
all-crossing target it consists of the singleton old-red endpoints.  At
every other target it contains the empty support, making destruction
impossible.  Consequently destruction by `B` says exactly that the target
is all-crossing relative to `B₀` and every one of its old-red endpoints
has been retained in `B`. -/
noncomputable def crossingEndpointObstructionFamily
    (A B₀ : Set ℕ) : SupportFamily := by
  classical
  intro q
  exact if ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ then
    (crossingAtomEndpoints A B₀ q).image fun b => {b}
  else
    {∅}

set_option maxHeartbeats 2000000 in
theorem destroysAt_crossingEndpointObstructionFamily_iff
    {A B₀ B : Set ℕ} {q : ℕ} :
    DestroysAt (crossingEndpointObstructionFamily A B₀) B q ↔
      (∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ B := by
  classical
  by_cases hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀
  · constructor
    · intro hdestroy
      refine ⟨hcross, ?_⟩
      intro b hbEndpoint
      by_contra hbB
      have hsingleton : ({b} : Finset ℕ) ∈
          crossingEndpointObstructionFamily A B₀ q := by
        simp only [crossingEndpointObstructionFamily, if_pos hcross]
        exact Finset.mem_image.mpr
          ⟨b, Finset.mem_coe.mp hbEndpoint, rfl⟩
      apply hdestroy ({b} : Finset ℕ) hsingleton
      rw [Set.disjoint_left]
      intro x hxSingleton hxB
      have hxb : x = b := by simpa using hxSingleton
      exact hbB (hxb ▸ hxB)
    · rintro ⟨_hcross, hsub⟩ E hE hdisjoint
      simp only [crossingEndpointObstructionFamily, if_pos hcross] at hE
      obtain ⟨b, hbEndpoint, rfl⟩ := Finset.mem_image.mp hE
      exact Set.disjoint_left.mp hdisjoint (by simp)
        (hsub (Finset.mem_coe.mpr hbEndpoint))
  · constructor
    · intro hdestroy
      have hempty : (∅ : Finset ℕ) ∈
          crossingEndpointObstructionFamily A B₀ q := by
        simp [crossingEndpointObstructionFamily, hcross]
      exact (hdestroy ∅ hempty (by simp)).elim
    · rintro ⟨h, _hsub⟩
      exact (hcross h).elim

/-- Strengthened obstruction family retaining the genuine order-three
failure.  At an all-crossing target it contains both every order-three
support and every singleton crossing endpoint.  Destruction therefore says
simultaneously that the target is all-crossing relative to `B₀`, that `B`
destroys its order-three support family, and that every old-red crossing
endpoint belongs to `B`. -/
noncomputable def crossingEndpointTripleObstructionFamily
    (A B₀ : Set ℕ) : SupportFamily := by
  classical
  intro q
  exact if ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ then
    additiveSupportFamily A 3 q ∪
      (crossingAtomEndpoints A B₀ q).image fun b => {b}
  else
    {∅}

set_option maxHeartbeats 2000000 in
theorem destroysAt_crossingEndpointTripleObstructionFamily_iff
    {A B₀ B : Set ℕ} {q : ℕ} :
    DestroysAt
        (crossingEndpointTripleObstructionFamily A B₀) B q ↔
      (∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      DestroysAt (additiveSupportFamily A 3) B q ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ B := by
  classical
  by_cases hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀
  · constructor
    · intro hdestroy
      refine ⟨hcross, ?_, ?_⟩
      · intro G hGR
        exact hdestroy G (by
          simp only [crossingEndpointTripleObstructionFamily,
            if_pos hcross]
          exact Finset.mem_union_left _ hGR)
      · intro b hbEndpoint
        by_contra hbB
        have hsingleton : ({b} : Finset ℕ) ∈
            crossingEndpointTripleObstructionFamily A B₀ q := by
          simp only [crossingEndpointTripleObstructionFamily,
            if_pos hcross]
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨b, Finset.mem_coe.mp hbEndpoint, rfl⟩
        apply hdestroy ({b} : Finset ℕ) hsingleton
        rw [Set.disjoint_left]
        intro x hxSingleton hxB
        have hxb : x = b := by simpa using hxSingleton
        exact hbB (hxb ▸ hxB)
    · rintro ⟨_hcross, htriple, hsub⟩ G hG hdisjoint
      simp only [crossingEndpointTripleObstructionFamily,
        if_pos hcross] at hG
      rcases Finset.mem_union.mp hG with hGR | hsingleton
      · exact htriple G hGR hdisjoint
      · obtain ⟨b, hbEndpoint, rfl⟩ :=
          Finset.mem_image.mp hsingleton
        exact Set.disjoint_left.mp hdisjoint (by simp)
          (hsub (Finset.mem_coe.mpr hbEndpoint))
  · constructor
    · intro hdestroy
      have hempty : (∅ : Finset ℕ) ∈
          crossingEndpointTripleObstructionFamily A B₀ q := by
        simp [crossingEndpointTripleObstructionFamily, hcross]
      exact (hdestroy ∅ hempty (by simp)).elim
    · rintro ⟨h, _htriple, _hsub⟩
      exact (hcross h).elim

/-- Every support in the combined crossing/triple obstruction has at most
three points.  At a crossing target it is either a genuine order-three
support or a singleton endpoint; away from the crossing case it is empty. -/
theorem crossingEndpointTripleObstructionFamily_cardAtMost
    {A B₀ : Set ℕ} :
    SupportsCardAtMost
      (crossingEndpointTripleObstructionFamily A B₀) 3 := by
  classical
  intro q E hE
  by_cases hcross : ∀ G ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (G : Set ℕ) B₀ ∧ ¬ (G : Set ℕ) ⊆ B₀
  · simp only [crossingEndpointTripleObstructionFamily,
      if_pos hcross] at hE
    rcases Finset.mem_union.mp hE with hEthree | hEsingle
    · exact additiveSupportFamily_cardAtMost A 3 q E hEthree
    · obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hEsingle
      simp
  · simp only [crossingEndpointTripleObstructionFamily,
      if_neg hcross, Finset.mem_singleton] at hE
    subst E
    simp

/-- A genuine order-three destroyer on a thinning `B ⊆ B₀` must satisfy
the two additional crossing-endpoint conditions.  A pair support disjoint
from `B₀` could be zero-padded; one contained in `B₀` could use the direct
repair installed on the old reservoir; and a crossing support whose old-red
endpoint was omitted from `B` would again be wholly retained after thinning. -/
theorem crossingEndpointTripleObstruction_of_orderThreeDestroyer
    {A B₀ B : Set ℕ} {q : ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hBB₀ : B ⊆ B₀)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hdestroy : DestroysAt (additiveSupportFamily A 3) B q) :
    DestroysAt
      (crossingEndpointTripleObstructionFamily A B₀) B q := by
  have hzeroB : 0 ∉ B := fun hzero => hzeroB₀ (hBB₀ hzero)
  have hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ := by
    intro E hER
    constructor
    · intro hblue₀
      let G : Finset ℕ := insert 0 E
      have hGR : G ∈ additiveSupportFamily A 3 q := by
        simpa [G] using
          (insert_mem_additiveSupportFamily_succ hzeroA hER)
      have hGB : Disjoint (G : Set ℕ) B := by
        rw [Set.disjoint_left]
        intro x hxG hxB
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hxG) with rfl | hxE
        · exact hzeroB hxB
        · exact Set.disjoint_left.mp hblue₀
            (Finset.mem_coe.mpr hxE) (hBB₀ hxB)
      exact (hdestroy G hGR) hGB
    · intro hred₀
      obtain ⟨v, _hvA, hvsum, rfl⟩ :=
        mem_additiveSupportFamily_iff.mp hER
      have hv0B₀ : (v 0).1 ∈ B₀ :=
        hred₀ (mem_tupleSupport_iff.mpr ⟨0, rfl⟩)
      have hv1B₀ : (v 1).1 ∈ B₀ :=
        hred₀ (mem_tupleSupport_iff.mpr ⟨1, rfl⟩)
      have hsum : (v 0).1 + (v 1).1 = q := by
        simpa [Fin.sum_univ_two] using hvsum
      obtain ⟨G, hGR, hGB₀⟩ :=
        hrepairs (v 0).1 hv0B₀ (v 1).1 hv1B₀
      rw [hsum] at hGR
      exact (hdestroy G hGR) (hGB₀.mono_right hBB₀)
  have hendpointSub :
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ B := by
    intro b hbEndpoint
    by_contra hbB
    have hbData := mem_crossingAtomEndpoints_iff.mp
      (Finset.mem_coe.mp hbEndpoint)
    let E : Finset ℕ := pairSupport q b
    have hER : E ∈ additiveSupportFamily A 2 q :=
      pairSupport_mem_additiveSupportFamily hbData.1
        (hB₀A hbData.2.1) hbData.2.2.1
    have hEB : Disjoint (E : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxE hxB
      have hxCases : x = b ∨ x = q - b := by
        simpa [E, pairSupport] using hxE
      rcases hxCases with rfl | rfl
      · exact hbB hxB
      · exact hbData.2.2.2 (hBB₀ hxB)
    let G : Finset ℕ := insert 0 E
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      simpa [G] using
        (insert_mem_additiveSupportFamily_succ hzeroA hER)
    have hGB : Disjoint (G : Set ℕ) B := by
      rw [Set.disjoint_left]
      intro x hxG hxB
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hxG) with rfl | hxE
      · exact hzeroB hxB
      · exact Set.disjoint_left.mp hEB
          (Finset.mem_coe.mpr hxE) hxB
    exact (hdestroy G hGR) hGB
  exact destroysAt_crossingEndpointTripleObstructionFamily_iff.mpr
    ⟨hcross, hdestroy, hendpointSub⟩

/-- Under the counterexample assumption, the strengthened endpoint/triple
family is strongly deleting on the repaired reservoir. -/
theorem strongCrossingEndpointTripleObstruction_of_counterexample
    {A B₀ : Set ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    StrongInfiniteDeletion
      (crossingEndpointTripleObstructionFamily A B₀) B₀ := by
  intro B hBB₀ hB N
  obtain ⟨q, hNq, hqDestroy⟩ :=
    strongOrderThreeDeletion_of_counterexample hcounter
      B (hBB₀.trans hB₀A) hB N
  exact ⟨q, hNq,
    crossingEndpointTripleObstruction_of_orderThreeDestroyer
      hzeroA hzeroB₀ hB₀A hBB₀ hrepairs hqDestroy⟩

/-- Compact finite certificates for the strengthened obstruction.  Every
selector genuinely destroys an order-three target in `Q` and simultaneously
contains that target's entire crossing-endpoint set. -/
theorem finiteCrossingEndpointTripleCertificates_of_counterexample
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F) :
    ∀ N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
  classical
  intro N
  have hstrong :=
    strongCrossingEndpointTripleObstruction_of_counterexample
      hzeroA hzeroB₀ hB₀A hrepairs hcounter
  obtain ⟨Q₀, hQ₀late, hcert₀⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion hstrong F P N
  let Cross : ℕ → Prop := fun q =>
    ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀
  let Q : Finset ℕ := Q₀.filter Cross
  have hQdata : ∀ q ∈ Q, N ≤ q ∧ Cross q := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨hQ₀late q hq.1, hq.2⟩
  refine ⟨Q, ?_, ?_⟩
  · simpa [Cross] using hQdata
  · intro sel
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ sel
    have hqData :=
      destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
        hqDestroy
    have hqQ : q ∈ Q := Finset.mem_filter.mpr ⟨hqQ₀, hqData.1⟩
    exact ⟨q, hqQ, hqData.2.1, hqData.2.2⟩

/-- Negating the omitted-endpoint completion theorem gives a strong
hypergraph obstruction on every infinite thinning of `B₀`.  This is the
precise strong-deletion statement whose compact finite certificates must be
defeated to construct the desired `B`. -/
theorem strongCrossingEndpointObstruction_of_counterexample
    {A B₀ : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    StrongInfiniteDeletion
      (crossingEndpointObstructionFamily A B₀) B₀ := by
  intro B hBB₀ hB N
  by_contra hnot
  push Not at hnot
  have homit : HasEventuallyOmittedCrossingEndpoint A B₀ B := by
    refine ⟨N, ?_⟩
    intro q hNq hcross
    intro hsub
    exact hnot q hNq
      (destroysAt_crossingEndpointObstructionFamily_iff.mpr
        ⟨hcross, hsub⟩)
  have hthree : IsExactTupleAsymptoticBasis (A \ B) 3 :=
    exactThreeBasis_of_omittedCrossingEndpoint_thinning
      hbasis hzeroA hzeroB₀ hB₀A hBB₀ hrepairs homit
  exact hcounter B (hBB₀.trans hB₀A) hB hthree

/-- Counterexample-level package of the new reduction.  The previously
constructed infinite zero-atomic reservoir carries direct repairs for every
old-red pair, and the only way all of its infinite thinnings can fail is the
strong crossing-endpoint obstruction above. -/
theorem counterexample_forces_strongCrossingEndpointReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B₀, B₀ ⊆ A ∧ B₀.Infinite ∧ 0 ∉ B₀ ∧
      (∀ x ∈ B₀, ∀ E ∈ additiveSupportFamily A 2 x,
        E = {x, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B₀ ∧
      StrongInfiniteDeletion
        (crossingEndpointObstructionFamily A B₀) B₀ := by
  obtain ⟨B₀, hB₀A, hB₀, hzeroB₀, hnormal,
      hrepairs, _hselfRepairs, _hlate⟩ :=
    counterexample_forces_repairedCrossingReservoir
      hbasis hzeroA hcounter
  have hstrong : StrongInfiniteDeletion
      (crossingEndpointObstructionFamily A B₀) B₀ :=
    strongCrossingEndpointObstruction_of_counterexample
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
  exact ⟨B₀, hB₀A, hB₀, hzeroB₀,
    hnormal, hrepairs, hstrong⟩

/-- Stronger counterexample package retaining genuine order-three
destruction in the crossing-endpoint obstruction. -/
theorem counterexample_forces_strongCrossingEndpointTripleReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ B₀, B₀ ⊆ A ∧ B₀.Infinite ∧ 0 ∉ B₀ ∧
      (∀ x ∈ B₀, ∀ E ∈ additiveSupportFamily A 2 x,
        E = {x, 0}) ∧
      HasDirectTripleRepairsForDeletedPairs A B₀ ∧
      StrongInfiniteDeletion
        (crossingEndpointTripleObstructionFamily A B₀) B₀ := by
  obtain ⟨B₀, hB₀A, hB₀, hzeroB₀, hnormal,
      hrepairs, _hselfRepairs, _hlate⟩ :=
    counterexample_forces_repairedCrossingReservoir
      hbasis hzeroA hcounter
  have hstrong : StrongInfiniteDeletion
      (crossingEndpointTripleObstructionFamily A B₀) B₀ :=
    strongCrossingEndpointTripleObstruction_of_counterexample
      hzeroA hzeroB₀ hB₀A hrepairs hcounter
  exact ⟨B₀, hB₀A, hB₀, hzeroB₀,
    hnormal, hrepairs, hstrong⟩

/-- Compactness now produces the exact finite certificate `Q` for the new
bridge.  Every block selector entirely contains the crossing-endpoint set
of one late target in `Q`; each certified target is genuinely all-crossing
relative to the old repaired reservoir. -/
theorem finiteCrossingEndpointCertificates_of_counterexample
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F) :
    ∀ N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
  classical
  intro N
  have hstrong := strongCrossingEndpointObstruction_of_counterexample
    hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
  obtain ⟨Q₀, hQ₀late, hcert₀⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion hstrong F P N
  let Cross : ℕ → Prop := fun q =>
    ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀
  let Q : Finset ℕ := Q₀.filter Cross
  have hQdata : ∀ q ∈ Q, N ≤ q ∧ Cross q := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨hQ₀late q hq.1, hq.2⟩
  refine ⟨Q, ?_, ?_⟩
  · simpa [Cross] using hQdata
  · intro sel
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ sel
    have hqData :=
      destroysAt_crossingEndpointObstructionFamily_iff.mp hqDestroy
    have hqQ : q ∈ Q := Finset.mem_filter.mpr ⟨hqQ₀, hqData.1⟩
    exact ⟨q, hqQ, hqData.2⟩

/-- A finite family of nonempty endpoint sets cannot cover selectors of
`k`-point cores by containment unless it has at least `k` targets.  Choose
one endpoint from each target.  If there were fewer than `k`, every core
would contain a point outside the finite set of chosen endpoints, producing
a selector which contains none of the endpoint sets. -/
theorem crossingEndpointCertificate_forces_targetCard_lower
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, k ≤ (cell i).card)
    (hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    k ≤ Q.card := by
  classical
  by_contra hnot
  have hQlt : Q.card < k := Nat.lt_of_not_ge hnot
  have hchoose : ∀ q : {q // q ∈ Q}, ∃ b,
      b ∈ crossingAtomEndpoints A B₀ q.1 := by
    intro q
    exact hendpoint q.1 q.2
  choose point hpoint using hchoose
  let H : Finset ℕ := Q.attach.image point
  have hHcard : H.card ≤ Q.card := by
    exact (Finset.card_image_le.trans_eq (by simp))
  have houtside : ∀ i, ∃ x, x ∈ cell i ∧ x ∉ H := by
    intro i
    have hnsub : ¬ cell i ⊆ H := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      have hki := hcellLower i
      omega
    exact Finset.not_subset.mp hnsub
  choose selected hselectedCell hselectedH using houtside
  let sel : BlockSelector F := fun i =>
    ⟨selected i, hcore i (hselectedCell i)⟩
  have hselCore : ∀ i, (sel i).1 ∈ cell i := by
    intro i
    exact hselectedCell i
  have hselH : Disjoint (H : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro x hxH hxSelected
    obtain ⟨i, hi⟩ := hxSelected
    apply hselectedH i
    have : selected i = x := hi
    exact this ▸ Finset.mem_coe.mp hxH
  obtain ⟨q, hqQ, hqSub⟩ := hcert sel hselCore
  let qQ : {q // q ∈ Q} := ⟨q, hqQ⟩
  have hpH : point qQ ∈ H := by
    exact Finset.mem_image.mpr
      ⟨qQ, Finset.mem_attach Q qQ, rfl⟩
  have hpSelected : point qQ ∈ selectedSet sel := by
    exact hqSub (Finset.mem_coe.mpr (hpoint qQ))
  exact Set.disjoint_left.mp hselH
    (Finset.mem_coe.mpr hpH) hpSelected

/-- Quantitative form of the compact crossing-endpoint certificate.  On a
partition whose blocks have at least `k` points, the late certificate `Q`
has at least `k` targets.  This improves the earlier pair-support coverage
bounds because the new obstruction requires containment of a whole endpoint
set rather than merely one intersection. -/
theorem finiteCrossingEndpointCertificates_targetCard_lower
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card) :
    ∀ N, ∃ Q : Finset ℕ,
      k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro N
  obtain ⟨Q, hQdata, hcert⟩ :=
    finiteCrossingEndpointCertificates_of_counterexample
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter P (max N N₂)
  have hQlate : ∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ := by
    intro q hqQ
    exact ⟨(le_max_left N N₂).trans (hQdata q hqQ).1,
      (hQdata q hqQ).2⟩
  have hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty := by
    intro q hqQ
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQdata q hqQ).1)
    obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
      exists_endpoints_of_crossingPairSupport hER
        ((hQdata q hqQ).2 E hER).1
        ((hQdata q hqQ).2 E hER).2
    have hbLe : b ≤ q := by omega
    have hsub : q - b = c := by omega
    exact ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩⟩
  have hQcard : k ≤ Q.card :=
    crossingEndpointCertificate_forces_targetCard_lower
      (A := A) (B₀ := B₀) (cell := F)
      (fun _ => Finset.Subset.rfl) hblockLower hendpoint
      (fun sel _hsel => hcert sel)
  exact ⟨Q, hQcard, hQlate, hcert⟩

/-- The strengthened compact certificate obeys the same linear lower bound
while retaining genuine order-three destruction at its selected target. -/
theorem finiteCrossingEndpointTripleCertificates_targetCard_lower
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card) :
    ∀ N, ∃ Q : Finset ℕ,
      k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro N
  obtain ⟨Q, hQdata, hcert⟩ :=
    finiteCrossingEndpointTripleCertificates_of_counterexample
      hzeroA hzeroB₀ hB₀A hrepairs hcounter P (max N N₂)
  have hQlate : ∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ := by
    intro q hqQ
    exact ⟨(le_max_left N N₂).trans (hQdata q hqQ).1,
      (hQdata q hqQ).2⟩
  have hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty := by
    intro q hqQ
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQdata q hqQ).1)
    obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
      exists_endpoints_of_crossingPairSupport hER
        ((hQdata q hqQ).2 E hER).1
        ((hQdata q hqQ).2 E hER).2
    have hbLe : b ≤ q := by omega
    have hsub : q - b = c := by omega
    exact ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩⟩
  have hcontain : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ F i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
    intro sel _hsel
    obtain ⟨q, hqQ, _hqDestroy, hqSub⟩ := hcert sel
    exact ⟨q, hqQ, hqSub⟩
  have hQcard : k ≤ Q.card :=
    crossingEndpointCertificate_forces_targetCard_lower
      (A := A) (B₀ := B₀) (cell := F)
      (fun _ => Finset.Subset.rfl) hblockLower hendpoint hcontain
  exact ⟨Q, hQcard, hQlate, hcert⟩

/-- Endpoint-containment duality.  After choosing one endpoint from every
certificate target, their chosen points must cover an entire core; otherwise
select outside their union in every block, contradicting the certificate. -/
theorem exists_coveredCell_of_crossingEndpointCertificate
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (point : {q // q ∈ Q} → ℕ)
    (hpoint : ∀ q, point q ∈ crossingAtomEndpoints A B₀ q.1)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    ∃ i, cell i ⊆ Q.attach.image point := by
  classical
  let H : Finset ℕ := Q.attach.image point
  by_contra hnot
  push Not at hnot
  have houtside : ∀ i, ∃ x, x ∈ cell i ∧ x ∉ H := by
    intro i
    exact Finset.not_subset.mp (hnot i)
  choose selected hselectedCell hselectedH using houtside
  let sel : BlockSelector F := fun i =>
    ⟨selected i, hcore i (hselectedCell i)⟩
  have hselCore : ∀ i, (sel i).1 ∈ cell i := by
    intro i
    exact hselectedCell i
  obtain ⟨q, hqQ, hqSub⟩ := hcert sel hselCore
  let qQ : {q // q ∈ Q} := ⟨q, hqQ⟩
  have hpSelected : point qQ ∈ selectedSet sel :=
    hqSub (Finset.mem_coe.mpr (hpoint qQ))
  obtain ⟨i, hi⟩ := hpSelected
  have hpH : point qQ ∈ H := Finset.mem_image.mpr
    ⟨qQ, Finset.mem_attach Q qQ, rfl⟩
  have hselectedEq : selected i = point qQ := hi
  exact hselectedH i (hselectedEq ▸ hpH)

set_option maxHeartbeats 2000000 in
/- Sharp classification of the new lower bound.  If a `k`-point core is
covered by exactly `k` targets, choosing one endpoint from each target
fills one whole core bijectively.  Forcing the chosen endpoint of `q` in
that block and varying every other coordinate shows that `q` can have no
second endpoint.  Hence every sharp target has a singleton crossing set,
and the singleton endpoints partition one core. -/
theorem sharpCrossingEndpointCertificate_forces_singletons
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 2 ≤ k)
    (hQcard : Q.card = k)
    (hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
      cell i = Q.attach.image point ∧
      Function.Injective point ∧
      ∀ q, crossingAtomEndpoints A B₀ q.1 = {point q} := by
  classical
  have hchoose : ∀ q : {q // q ∈ Q}, ∃ b,
      b ∈ crossingAtomEndpoints A B₀ q.1 := by
    intro q
    exact hendpoint q.1 q.2
  choose point hpoint using hchoose
  obtain ⟨i, hcellH⟩ :=
    exists_coveredCell_of_crossingEndpointCertificate
      hcore point hpoint hcert
  let H : Finset ℕ := Q.attach.image point
  have hHcardUpper : H.card ≤ Q.card := by
    exact (Finset.card_image_le.trans_eq (by simp))
  have hcellEq : cell i = H := by
    apply Finset.eq_of_subset_of_card_le hcellH
    rw [hcellCard i, ← hQcard]
    exact hHcardUpper
  have hHcard : H.card = Q.attach.card := by
    calc
      H.card = (cell i).card := congrArg Finset.card hcellEq.symm
      _ = k := hcellCard i
      _ = Q.card := hQcard.symm
      _ = Q.attach.card := by simp
  have hpointInjOn : Set.InjOn point (Q.attach : Set {q // q ∈ Q}) :=
    Finset.card_image_iff.mp (by simpa [H] using hHcard)
  have hpointInj : Function.Injective point := by
    intro q r hqr
    exact hpointInjOn (Finset.mem_attach Q q)
      (Finset.mem_attach Q r) hqr
  refine ⟨point, i, ?_, hpointInj, ?_⟩
  · exact hcellEq
  · intro q
    apply Finset.Subset.antisymm
    · intro x hxEndpoint
      have hpH : point q ∈ H := Finset.mem_image.mpr
        ⟨q, Finset.mem_attach Q q, rfl⟩
      have hpCell : point q ∈ cell i := by
        rw [hcellEq]
        exact hpH
      by_contra hxSingleton
      have hxp : x ≠ point q := by simpa using hxSingleton
      have houtside : ∀ j, ∃ y, y ∈ cell j ∧ y ≠ x := by
        intro j
        have hnsub : ¬ cell j ⊆ ({x} : Finset ℕ) := by
          intro hsub
          have hcard := Finset.card_le_card hsub
          have hjcard := hcellCard j
          simp only [Finset.card_singleton] at hcard
          omega
        obtain ⟨y, hyCell, hy⟩ := Finset.not_subset.mp hnsub
        exact ⟨y, hyCell, by simpa using hy⟩
      choose other hotherCell hotherNe using houtside
      let value : ℕ → ℕ := fun j =>
        if hj : j = i then point q else other j
      have hvalueCell : ∀ j, value j ∈ cell j := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa [value] using hpCell
        · simpa [value, hj] using hotherCell j
      have hvalueNe : ∀ j, value j ≠ x := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa [value] using hxp.symm
        · simpa [value, hj] using hotherNe j
      let sel : BlockSelector F := fun j =>
        ⟨value j, hcore j (hvalueCell j)⟩
      have hselCore : ∀ j, (sel j).1 ∈ cell j := by
        intro j
        exact hvalueCell j
      have hselI : (sel i).1 = point q := by simp [sel, value]
      have hxNotSelected : x ∉ selectedSet sel := by
        rintro ⟨j, hj⟩
        exact hvalueNe j hj
      obtain ⟨r, hrQ, hrSub⟩ := hcert sel hselCore
      let rQ : {r // r ∈ Q} := ⟨r, hrQ⟩
      have hprSelected : point rQ ∈ selectedSet sel :=
        hrSub (Finset.mem_coe.mpr (hpoint rQ))
      have hprH : point rQ ∈ H := Finset.mem_image.mpr
        ⟨rQ, Finset.mem_attach Q rQ, rfl⟩
      have hprCell : point rQ ∈ cell i := by
        rw [hcellEq]
        exact hprH
      obtain ⟨j, hj⟩ := hprSelected
      have hji : j = i := by
        by_contra hji
        have hprFj : point rQ ∈ F j := by
          rw [← hj]
          exact (sel j).2
        exact Finset.disjoint_left.mp
          (P.disjoint (fun hij => hji hij.symm))
          (hcore i hprCell) hprFj
      have hprEq : point rQ = point q := by
        subst j
        exact hj.symm.trans hselI
      have hrq : rQ = q := hpointInj hprEq
      have hrVal : r = q.1 := congrArg Subtype.val hrq
      have hxSelected : x ∈ selectedSet sel := by
        apply hrSub
        simpa [hrVal] using hxEndpoint
      exact hxNotSelected hxSelected
    · intro x hx
      have hxEq : x = point q := by simpa using hx
      exact hxEq ▸ hpoint q

set_option maxHeartbeats 3000000 in
/- Sharp classification for the strengthened certificate.  In addition to
the singleton endpoint conclusion, every order-three support of the matched
target contains that singleton.  Otherwise force its endpoint in the common
core while avoiding the proposed support everywhere; the endpoint
classification makes every other target ineligible, so the certificate must
destroy the same target with a disjoint selector. -/
theorem sharpCrossingEndpointTripleCertificate_forces_singletonDestroyers
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k)
    (hQcard : Q.card = k)
    (hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
      cell i = Q.attach.image point ∧
      Function.Injective point ∧
      ∀ q,
        crossingAtomEndpoints A B₀ q.1 = {point q} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({point q} : Set ℕ) q.1 := by
  classical
  have hcontain : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
    intro sel hsel
    obtain ⟨q, hqQ, _hqDestroy, hqSub⟩ := hcert sel hsel
    exact ⟨q, hqQ, hqSub⟩
  obtain ⟨point, i, hcellEq, hpointInj, hsingle⟩ :=
    sharpCrossingEndpointCertificate_forces_singletons
      P hcore hcellCard (by omega) hQcard hendpoint hcontain
  refine ⟨point, i, hcellEq, hpointInj, ?_⟩
  intro q
  refine ⟨hsingle q, ?_⟩
  intro G hGR hGsingleton
  have hpNotG : point q ∉ G := by
    intro hpG
    exact Set.disjoint_left.mp hGsingleton
      (Finset.mem_coe.mpr hpG) (by simp)
  have hpCell : point q ∈ cell i := by
    rw [hcellEq]
    exact Finset.mem_image.mpr
      ⟨q, Finset.mem_attach Q q, rfl⟩
  have hGcard : G.card ≤ 3 :=
    additiveSupportFamily_cardAtMost A 3 q.1 G hGR
  have houtside : ∀ j, ∃ y, y ∈ cell j ∧ y ∉ G := by
    intro j
    have hnsub : ¬ cell j ⊆ G := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      have hjcard := hcellCard j
      omega
    exact Finset.not_subset.mp hnsub
  choose other hotherCell hotherG using houtside
  let value : ℕ → ℕ := fun j =>
    if hj : j = i then point q else other j
  have hvalueCell : ∀ j, value j ∈ cell j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hpCell
    · simpa [value, hj] using hotherCell j
  have hvalueG : ∀ j, value j ∉ G := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hpNotG
    · simpa [value, hj] using hotherG j
  let sel : BlockSelector F := fun j =>
    ⟨value j, hcore j (hvalueCell j)⟩
  have hselCore : ∀ j, (sel j).1 ∈ cell j := by
    intro j
    exact hvalueCell j
  have hselI : (sel i).1 = point q := by simp [sel, value]
  have hGselected : Disjoint (G : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro x hxG hxSelected
    obtain ⟨j, hj⟩ := hxSelected
    apply hvalueG j
    have : value j = x := hj
    exact this ▸ Finset.mem_coe.mp hxG
  obtain ⟨r, hrQ, hrDestroy, hrSub⟩ := hcert sel hselCore
  let rQ : {r // r ∈ Q} := ⟨r, hrQ⟩
  have hprEndpoint : point rQ ∈ crossingAtomEndpoints A B₀ r := by
    rw [hsingle rQ]
    simp
  have hprSelected : point rQ ∈ selectedSet sel :=
    hrSub (Finset.mem_coe.mpr hprEndpoint)
  have hprCell : point rQ ∈ cell i := by
    rw [hcellEq]
    exact Finset.mem_image.mpr
      ⟨rQ, Finset.mem_attach Q rQ, rfl⟩
  obtain ⟨j, hj⟩ := hprSelected
  have hji : j = i := by
    by_contra hji
    have hprFj : point rQ ∈ F j := by
      rw [← hj]
      exact (sel j).2
    exact Finset.disjoint_left.mp
      (P.disjoint (fun hij => hji hij.symm))
      (hcore i hprCell) hprFj
  have hprEq : point rQ = point q := by
    subst j
    exact hj.symm.trans hselI
  have hrq : rQ = q := hpointInj hprEq
  have hrVal : r = q.1 := congrArg Subtype.val hrq
  have hqDestroy : DestroysAt (additiveSupportFamily A 3)
      (selectedSet sel) q.1 := by
    simpa [hrVal] using hrDestroy
  exact (hqDestroy G hGR) hGselected

/-- At an all-crossing target, a singleton endpoint set is equivalent to a
unique canonical pair support. -/
theorem pairSupports_eq_singleton_of_crossingEndpoint_eq_singleton
    {A B₀ : Set ℕ} {q b : ℕ}
    (hB₀A : B₀ ⊆ A)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀)
    (hsingle : crossingAtomEndpoints A B₀ q = {b}) :
    additiveSupportFamily A 2 q = {pairSupport q b} := by
  rw [pairSupports_eq_image_crossingAtomEndpoints hB₀A hcross,
    hsingle]
  simp

/-- The same singleton endpoint is an honest rigid pair sum with its
complementary endpoint `q - b`.  Thus equality in the new `|Q| ≥ k` bound
lands exactly in the rigid obstruction language used by the reservation
construction. -/
theorem rigidPairSum_of_crossingEndpoint_eq_singleton
    {A B₀ : Set ℕ} {q b : ℕ}
    (hB₀A : B₀ ⊆ A)
    (hcross : ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀)
    (hsingle : crossingAtomEndpoints A B₀ q = {b}) :
    IsRigidPairSum A b (q - b) := by
  have hbEndpoint : b ∈ crossingAtomEndpoints A B₀ q := by
    rw [hsingle]
    simp
  have hsum : b + (q - b) = q :=
    crossingAtomEndpoint_sum hbEndpoint
  have hfamily :=
    pairSupports_eq_singleton_of_crossingEndpoint_eq_singleton
      hB₀A hcross hsingle
  intro E hER
  rw [hsum] at hER ⊢
  rw [hfamily] at hER
  simpa using hER

/-- Every infinite subset of the naturals admits a finite-block partition
with dedicated exact `k`-point cores, for every positive `k`.  Pairing the
block index with `Fin k` gives disjoint finite cells inside the set; the
generic partition-completion theorem absorbs all unused elements. -/
theorem exists_finiteBlockPartition_with_exactCoreCard
    {B₀ : Set ℕ} (hB₀ : B₀.Infinite) {k : ℕ} (hk : 0 < k) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition B₀ F ∧
      (∀ i, cell i ⊆ F i) ∧
      ∀ i, (cell i).card = k := by
  classical
  letI : Infinite B₀ := hB₀.to_subtype
  letI : Denumerable B₀ := Denumerable.ofEncodableOfInfinite B₀
  let e : ℕ ≃ B₀ := (Denumerable.eqv B₀).symm
  let value : ℕ → Fin k → ℕ := fun i a =>
    (e (Nat.pair i a.1)).1
  let cell : ℕ → Finset ℕ := fun i =>
    (Finset.univ : Finset (Fin k)).image (value i)
  have hvalueInj : ∀ i, Function.Injective (value i) := by
    intro i a b hab
    apply Fin.ext
    have heq : Nat.pair i a.1 = Nat.pair i b.1 := by
      apply e.injective
      exact Subtype.ext hab
    exact (Nat.pair_eq_pair.mp heq).2
  have hcellA : ∀ i, (cell i : Set ℕ) ⊆ B₀ := by
    intro i x hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact (e (Nat.pair i a.1)).2
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    let a : Fin k := ⟨0, hk⟩
    exact ⟨value i a, Finset.mem_image.mpr
      ⟨a, Finset.mem_univ a, rfl⟩⟩
  have hcellDisjoint : Pairwise fun i j =>
      Disjoint (cell i) (cell j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, _hb, hbx⟩ := Finset.mem_image.mp hxj
    have hvalueEq : value i a = value j b := hax.trans hbx.symm
    have hpairEq : Nat.pair i a.1 = Nat.pair j b.1 := by
      apply e.injective
      exact Subtype.ext hvalueEq
    exact hij (Nat.pair_eq_pair.mp hpairEq).1
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  have hcellCard : ∀ i, (cell i).card = k := by
    intro i
    calc
      (cell i).card = (Finset.univ : Finset (Fin k)).card := by
        exact Finset.card_image_iff.mpr (hvalueInj i).injOn
      _ = k := by simp
  exact ⟨F, cell, P, hcore, hcellCard⟩

/-- Exhaustive late fork for exact `k`-point blocks.  A strengthened
crossing-endpoint certificate is either strictly larger than the block, or
its sharp case fills one whole block with singleton order-three destroyers;
each matched singleton is also the unique old-red endpoint of an honest
rigid pair sum. -/
theorem finiteCrossingEndpointTripleCertificates_strict_or_rigidCore
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    ∀ N, ∃ Q : Finset ℕ,
      k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀) ∧
      (∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∧
      (k < Q.card ∨
        ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
          cell i = Q.attach.image point ∧
          Function.Injective point ∧
          ∀ q,
            crossingAtomEndpoints A B₀ q.1 = {point q} ∧
            DestroysAt (additiveSupportFamily A 3)
              ({point q} : Set ℕ) q.1 ∧
            IsRigidPairSum A (point q) (q.1 - point q)) := by
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro N
  have hblockLower : ∀ i, k ≤ (F i).card := by
    intro i
    rw [← hcellCard i]
    exact Finset.card_le_card (hcore i)
  obtain ⟨Q, hQlower, hQdata, hcert⟩ :=
    finiteCrossingEndpointTripleCertificates_targetCard_lower
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter P hblockLower
        (max N N₂)
  have hQlate : ∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧ ¬ (E : Set ℕ) ⊆ B₀ := by
    intro q hqQ
    exact ⟨(le_max_left N N₂).trans (hQdata q hqQ).1,
      (hQdata q hqQ).2⟩
  have hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty := by
    intro q hqQ
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQdata q hqQ).1)
    obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
      exists_endpoints_of_crossingPairSupport hER
        ((hQdata q hqQ).2 E hER).1
        ((hQdata q hqQ).2 E hER).2
    have hbLe : b ≤ q := by omega
    have hsub : q - b = c := by omega
    exact ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩⟩
  refine ⟨Q, hQlower, hQlate, hcert, ?_⟩
  by_cases hsharp : Q.card = k
  · right
    obtain ⟨point, i, hcellEq, hpointInj, hsingleDestroy⟩ :=
      sharpCrossingEndpointTripleCertificate_forces_singletonDestroyers
        P hcore hcellCard hk hsharp hendpoint
          (fun sel _hsel => hcert sel)
    refine ⟨point, i, hcellEq, hpointInj, ?_⟩
    intro q
    have hsingle := (hsingleDestroy q).1
    have hdestroy := (hsingleDestroy q).2
    have hcross := (hQdata q.1 q.2).2
    exact ⟨hsingle, hdestroy,
      rigidPairSum_of_crossingEndpoint_eq_singleton
        hB₀A hcross hsingle⟩
  · left
    omega

set_option maxHeartbeats 3000000 in
/-- Cardinal-minimal version of the strict/sharp endpoint fork.  Minimizing
inside the combined crossing/triple obstruction family preserves the exact
certificate relation and gives every retained target a private selector.
Consequently `Q.card > k` is now a substantive alternative rather than an
artifact of freely enlarging a certificate. -/
theorem finiteMinimalCrossingEndpointTripleCertificates_strict_or_rigidCore
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    ∀ N, ∃ Q : Finset ℕ,
      k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      (∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∧
      (∀ q ∈ Q, ∃ sel : BlockSelector F,
        DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q ∧
        ∀ q' ∈ Q, q' ≠ q →
          ¬ DestroysAt
            (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet sel) q') ∧
      (k < Q.card ∨
        ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
          cell i = Q.attach.image point ∧
          Function.Injective point ∧
          ∀ q,
            crossingAtomEndpoints A B₀ q.1 = {point q} ∧
            DestroysAt (additiveSupportFamily A 3)
              ({point q} : Set ℕ) q.1 ∧
            IsRigidPairSum A (point q) (q.1 - point q)) := by
  classical
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro N
  let R : SupportFamily :=
    crossingEndpointTripleObstructionFamily A B₀
  have hstrong : StrongInfiniteDeletion R B₀ := by
    simpa [R] using
      strongCrossingEndpointTripleObstruction_of_counterexample
        hzeroA hzeroB₀ hB₀A hrepairs hcounter
  obtain ⟨Qraw, hQrawLate, hQrawCert⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      hstrong F P (max N N₂)
  obtain ⟨Q, hQQraw, hcertR, hlocalizedR⟩ :=
    exists_minimal_targetLocalized_subcertificate hQrawCert
  have hQdata : ∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀ := by
    intro q hqQ
    obtain ⟨sel, hqDestroy, _hprivate⟩ := hlocalizedR q hqQ
    have hqData :=
      destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
        (by simpa [R] using hqDestroy)
    exact ⟨(le_max_left N N₂).trans
      (hQrawLate q (hQQraw hqQ)), hqData.1⟩
  have hcert : ∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3)
        (selectedSet sel) q ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
        selectedSet sel := by
    intro sel
    obtain ⟨q, hqQ, hqDestroy⟩ := hcertR sel
    have hqData :=
      destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
        (by simpa [R] using hqDestroy)
    exact ⟨q, hqQ, hqData.2.1, hqData.2.2⟩
  have hlocalized : ∀ q ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q' := by
    intro q hqQ
    obtain ⟨sel, hqDestroy, hprivate⟩ := hlocalizedR q hqQ
    refine ⟨sel, by simpa [R] using hqDestroy, ?_⟩
    intro q' hq'Q hq'ne
    simpa [R] using hprivate q' hq'Q hq'ne
  have hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty := by
    intro q hqQ
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans
        (hQrawLate q (hQQraw hqQ)))
    obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
      exists_endpoints_of_crossingPairSupport hER
        ((hQdata q hqQ).2 E hER).1
        ((hQdata q hqQ).2 E hER).2
    have hbLe : b ≤ q := by omega
    have hsub : q - b = c := by omega
    exact ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩⟩
  have hblockLower : ∀ i, k ≤ (F i).card := by
    intro i
    rw [← hcellCard i]
    exact Finset.card_le_card (hcore i)
  have hQlower : k ≤ Q.card :=
    crossingEndpointCertificate_forces_targetCard_lower
      (A := A) (B₀ := B₀) (cell := F)
      (fun _ => Finset.Subset.rfl) hblockLower hendpoint
      (fun sel _hsel => by
        obtain ⟨q, hqQ, _hqDestroy, hqSub⟩ := hcert sel
        exact ⟨q, hqQ, hqSub⟩)
  refine ⟨Q, hQlower, hQdata, hcert, hlocalized, ?_⟩
  by_cases hsharp : Q.card = k
  · right
    obtain ⟨point, i, hcellEq, hpointInj, hsingleDestroy⟩ :=
      sharpCrossingEndpointTripleCertificate_forces_singletonDestroyers
        P hcore hcellCard hk hsharp hendpoint
          (fun sel _hsel => hcert sel)
    refine ⟨point, i, hcellEq, hpointInj, ?_⟩
    intro q
    have hsingle := (hsingleDestroy q).1
    exact ⟨hsingle, (hsingleDestroy q).2,
      rigidPairSum_of_crossingEndpoint_eq_singleton
        hB₀A (hQdata q.1 q.2).2 hsingle⟩
  · left
    omega

set_option maxHeartbeats 5000000 in
/-- Structural block cover behind private-selector occupancy.  Once one
surviving support has been fixed for every target other than `q`, replacing
`q`'s support by a selected singleton `x` forces the remainder of `x`'s
block into the fixed union of those other supports. -/
theorem targetLocalized_singletonSupports_force_blockCover_of_choice
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    {Q X : Finset ℕ} {q : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt R (selectedSet sel) t)
    (base : BlockSelector F)
    (cOther : FiniteSupportChoice R (Q.erase q))
    (hOtherDisjoint : ∀ t : {n // n ∈ Q.erase q},
      Disjoint ((cOther t).1 : Set ℕ) (selectedSet base))
    (hXsupport : ∀ x ∈ X, ({x} : Finset ℕ) ∈ R q) :
    ∀ x ∈ X,
      F (blockIndex P x) \ {x} ⊆ finiteSupportChoiceUnion cOther := by
  classical
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  have hUDisjoint : Disjoint (U : Set ℕ) (selectedSet base) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨t, _htAttach, hxt⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hOtherDisjoint t)
      (Finset.mem_coe.mpr hxt) hxSelected
  intro x hxX
  let cFull : FiniteSupportChoice R Q := fun t =>
    if htq : t.1 = q then
      ⟨{x}, by simpa [htq] using hXsupport x hxX⟩
    else
      let t' : {n // n ∈ Q.erase q} :=
        ⟨t.1, Finset.mem_erase.mpr ⟨htq, t.2⟩⟩
      ⟨(cOther t').1, (cOther t').2⟩
  have hfullCases : ∀ y,
      y ∈ finiteSupportChoiceUnion cFull → y = x ∨ y ∈ U := by
    intro y hy
    obtain ⟨t, _htAttach, hyt⟩ := Finset.mem_biUnion.mp hy
    by_cases htq : t.1 = q
    · left
      simpa [cFull, htq] using hyt
    · right
      let t' : {n // n ∈ Q.erase q} :=
        ⟨t.1, Finset.mem_erase.mpr ⟨htq, t.2⟩⟩
      apply finiteSupportChoice_subset_union cOther t'
      simpa [cFull, htq, t'] using hyt
  obtain ⟨i, hiCover⟩ :=
    exists_block_subset_supportChoiceUnion_of_certificate hcert cFull
  have hsiUnion : (base i).1 ∈
      finiteSupportChoiceUnion cFull := hiCover (base i).2
  have hsiEq : (base i).1 = x := by
    rcases hfullCases (base i).1 hsiUnion with hix | hiU
    · exact hix
    · exact (Set.disjoint_left.mp hUDisjoint
        (Finset.mem_coe.mpr hiU) ⟨i, rfl⟩).elim
  have hxFi : x ∈ F i := by
    rw [← hsiEq]
    exact (base i).2
  have hindex : blockIndex P x = i :=
    P.blockIndex_eq_of_mem hxFi
  intro y hyDiff
  have hyFi : y ∈ F i := by
    rw [← hindex]
    exact (Finset.mem_sdiff.mp hyDiff).1
  rcases hfullCases y (hiCover hyFi) with hyx | hyU
  · exact ((Finset.mem_sdiff.mp hyDiff).2 (by simp [hyx])).elim
  · simpa [U] using hyU

/-- The union of the nonselected remainders of the blocks indexed by `X`. -/
noncomputable def selectedBlockRemainderUnion
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (X : Finset ℕ) : Finset ℕ :=
  X.biUnion fun x => F (blockIndex P x) \ {x}

/-- Distinct points of one block selector index distinct partition blocks,
so their block remainders are disjoint and contribute independently. -/
theorem selectedBlockRemainderUnion_card_lower
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    {X : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (base : BlockSelector F)
    (hXselected : (X : Set ℕ) ⊆ selectedSet base) :
    (k - 1) * X.card ≤ (selectedBlockRemainderUnion P X).card := by
  classical
  have hindexInj : Set.InjOn (blockIndex P) (X : Set ℕ) := by
    intro x hxX y hyX hindex
    have hxSelected := hXselected hxX
    have hySelected := hXselected hyX
    rw [P.mem_selectedSet_iff base] at hxSelected hySelected
    calc
      x = (base (blockIndex P x)).1 := hxSelected.symm
      _ = (base (blockIndex P y)).1 := by rw [hindex]
      _ = y := hySelected
  have hpairwise : (X : Set ℕ).PairwiseDisjoint
      (fun x => F (blockIndex P x) \ {x}) := by
    intro x hxX y hyX hxy
    have hindexNe : blockIndex P x ≠ blockIndex P y := by
      intro hindex
      exact hxy (hindexInj hxX hyX hindex)
    exact (P.disjoint hindexNe).mono
      Finset.sdiff_subset Finset.sdiff_subset
  have hpieceLower : ∀ x ∈ X,
      k - 1 ≤ (F (blockIndex P x) \ {x}).card := by
    intro x hxX
    have hxSelected : x ∈ selectedSet base :=
      hXselected (Finset.mem_coe.mpr hxX)
    obtain ⟨i, hi⟩ := hxSelected
    have hxFi : x ∈ F i := by
      rw [← hi]
      exact (base i).2
    have hxA : x ∈ A := (P.mem_iff x).2 ⟨i, hxFi⟩
    have hxBlock : x ∈ F (blockIndex P x) :=
      P.mem_blockIndex hxA
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hxBlock]
    have hlower := hblockLower (blockIndex P x)
    omega
  dsimp only [selectedBlockRemainderUnion]
  rw [Finset.card_biUnion hpairwise]
  calc
    (k - 1) * X.card = ∑ x ∈ X, (k - 1) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ X,
        (F (blockIndex P x) \ {x}).card := by
      apply Finset.sum_le_sum
      intro x hxX
      exact hpieceLower x hxX

/-- Pointwise block-remainder covers combine into a cover of their union. -/
theorem selectedBlockRemainderUnion_subset
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    {X U : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcover : ∀ x ∈ X, F (blockIndex P x) \ {x} ⊆ U) :
    selectedBlockRemainderUnion P X ⊆ U := by
  classical
  intro y hy
  obtain ⟨x, hxX, hyPiece⟩ := Finset.mem_biUnion.mp hy
  exact hcover x hxX hyPiece

set_option maxHeartbeats 5000000 in
/-- Quantitative occupancy forced by a target-private selector.  Suppose a
minimal selector certificate has a private selector for `q`, and `X` is a
finite family of singleton supports of `q` all selected by that selector.
For every other target choose a surviving support disjoint from the private
selector.  Varying the singleton chosen at `q` forces those other supports
to cover the rest of the singleton's block.  Distinct selected singletons
lie in distinct blocks, so

`(k - 1) * X.card ≤ (finiteSupportChoiceUnion cOther).card`.

This is the cardinal information supplied by target localization which is
lost if the certificate is enlarged without re-minimizing. -/
theorem targetLocalized_singletonSupports_force_blockOccupancy_of_choice
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    {Q X : Finset ℕ} {q k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt R (selectedSet sel) t)
    (base : BlockSelector F)
    (cOther : FiniteSupportChoice R (Q.erase q))
    (hOtherDisjoint : ∀ t : {n // n ∈ Q.erase q},
      Disjoint ((cOther t).1 : Set ℕ) (selectedSet base))
    (hXselected : (X : Set ℕ) ⊆ selectedSet base)
    (hXsupport : ∀ x ∈ X, ({x} : Finset ℕ) ∈ R q) :
    (k - 1) * X.card ≤ (finiteSupportChoiceUnion cOther).card := by
  classical
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  have hUDisjoint : Disjoint (U : Set ℕ) (selectedSet base) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨t, _htAttach, hxt⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hOtherDisjoint t)
      (Finset.mem_coe.mpr hxt) hxSelected
  have hblockCover : ∀ x ∈ X,
      F (blockIndex P x) \ {x} ⊆ U := by
    intro x hxX
    let cFull : FiniteSupportChoice R Q := fun t =>
      if htq : t.1 = q then
        ⟨{x}, by simpa [htq] using hXsupport x hxX⟩
      else
        let t' : {n // n ∈ Q.erase q} :=
          ⟨t.1, Finset.mem_erase.mpr ⟨htq, t.2⟩⟩
        ⟨(cOther t').1, (cOther t').2⟩
    have hfullCases : ∀ y,
        y ∈ finiteSupportChoiceUnion cFull → y = x ∨ y ∈ U := by
      intro y hy
      obtain ⟨t, _htAttach, hyt⟩ := Finset.mem_biUnion.mp hy
      by_cases htq : t.1 = q
      · left
        simpa [cFull, htq] using hyt
      · right
        let t' : {n // n ∈ Q.erase q} :=
          ⟨t.1, Finset.mem_erase.mpr ⟨htq, t.2⟩⟩
        apply finiteSupportChoice_subset_union cOther t'
        simpa [cFull, htq, t'] using hyt
    obtain ⟨i, hiCover⟩ :=
      exists_block_subset_supportChoiceUnion_of_certificate hcert cFull
    have hsiUnion : (base i).1 ∈
        finiteSupportChoiceUnion cFull := hiCover (base i).2
    have hsiEq : (base i).1 = x := by
      rcases hfullCases (base i).1 hsiUnion with hix | hiU
      · exact hix
      · exact (Set.disjoint_left.mp hUDisjoint
          (Finset.mem_coe.mpr hiU) ⟨i, rfl⟩).elim
    have hxFi : x ∈ F i := by
      rw [← hsiEq]
      exact (base i).2
    have hindex : blockIndex P x = i :=
      P.blockIndex_eq_of_mem hxFi
    intro y hyDiff
    have hyFi : y ∈ F i := by
      rw [← hindex]
      exact (Finset.mem_sdiff.mp hyDiff).1
    rcases hfullCases y (hiCover hyFi) with hyx | hyU
    · exact ((Finset.mem_sdiff.mp hyDiff).2 (by simp [hyx])).elim
    · exact hyU
  have hindexInj : Set.InjOn (blockIndex P) (X : Set ℕ) := by
    intro x hxX y hyX hindex
    have hxSelected := hXselected hxX
    have hySelected := hXselected hyX
    rw [P.mem_selectedSet_iff base] at hxSelected hySelected
    calc
      x = (base (blockIndex P x)).1 := hxSelected.symm
      _ = (base (blockIndex P y)).1 := by rw [hindex]
      _ = y := hySelected
  let V : Finset ℕ := X.biUnion fun x =>
    F (blockIndex P x) \ {x}
  have hpairwise : (X : Set ℕ).PairwiseDisjoint
      (fun x => F (blockIndex P x) \ {x}) := by
    intro x hxX y hyX hxy
    have hindexNe : blockIndex P x ≠ blockIndex P y := by
      intro hindex
      exact hxy (hindexInj hxX hyX hindex)
    exact (P.disjoint hindexNe).mono
      Finset.sdiff_subset Finset.sdiff_subset
  have hpieceLower : ∀ x ∈ X,
      k - 1 ≤ (F (blockIndex P x) \ {x}).card := by
    intro x hxX
    have hxSelected : x ∈ selectedSet base :=
      hXselected (Finset.mem_coe.mpr hxX)
    obtain ⟨i, hi⟩ := hxSelected
    have hxFi : x ∈ F i := by
      rw [← hi]
      exact (base i).2
    have hxA : x ∈ A := (P.mem_iff x).2 ⟨i, hxFi⟩
    have hxBlock : x ∈ F (blockIndex P x) :=
      P.mem_blockIndex hxA
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.card_erase_of_mem hxBlock]
    have hlower := hblockLower (blockIndex P x)
    omega
  have hVLower : (k - 1) * X.card ≤ V.card := by
    dsimp only [V]
    rw [Finset.card_biUnion hpairwise]
    calc
      (k - 1) * X.card = ∑ x ∈ X, (k - 1) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ X,
          (F (blockIndex P x) \ {x}).card := by
        apply Finset.sum_le_sum
        intro x hxX
        exact hpieceLower x hxX
  have hVsub : V ⊆ U := by
    intro y hyV
    obtain ⟨x, hxX, hyPiece⟩ := Finset.mem_biUnion.mp hyV
    exact hblockCover x hxX hyPiece
  simpa [U] using hVLower.trans (Finset.card_le_card hVsub)

/-- Uniform-cardinality consequence of
`targetLocalized_singletonSupports_force_blockOccupancy_of_choice`.
Minimality supplies one surviving support for every other target, and the
uniform support bound controls their union. -/
theorem targetLocalized_singletonSupports_force_blockOccupancy
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    {Q X : Finset ℕ} {q k r : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hcard : SupportsCardAtMost R r)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt R (selectedSet sel) t)
    (base : BlockSelector F)
    (hprivate : ∀ t ∈ Q, t ≠ q →
      ¬ DestroysAt R (selectedSet base) t)
    (hXselected : (X : Set ℕ) ⊆ selectedSet base)
    (hXsupport : ∀ x ∈ X, ({x} : Finset ℕ) ∈ R q) :
    (k - 1) * X.card ≤ r * (Q.erase q).card := by
  classical
  have hsurvive : ∀ t : {n // n ∈ Q.erase q},
      ∃ E ∈ R t.1, Disjoint (E : Set ℕ) (selectedSet base) := by
    intro t
    have ht := Finset.mem_erase.mp t.2
    exact not_destroysAt_iff.mp
      (hprivate t.1 ht.2 ht.1)
  choose chosen hchosenMem hchosenDisjoint using hsurvive
  let cOther : FiniteSupportChoice R (Q.erase q) := fun t =>
    ⟨chosen t, hchosenMem t⟩
  have hoccupancy : (k - 1) * X.card ≤
      (finiteSupportChoiceUnion cOther).card :=
    targetLocalized_singletonSupports_force_blockOccupancy_of_choice
      P hblockLower hcert base cOther
        (fun t => by simpa [cOther] using hchosenDisjoint t)
        hXselected hXsupport
  exact hoccupancy.trans
    (finiteSupportChoiceUnion_card_le hcard cOther)

/-- In a cardinal-minimal strengthened crossing certificate, every target's
crossing endpoint family obeys the private-selector occupancy bound. -/
theorem minimalCrossingEndpointTripleCertificate_forces_scaledEndpointBound
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ q ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q)
    (hlocalized : ∀ q ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q') :
    ∀ q ∈ Q,
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        3 * (Q.erase q).card := by
  classical
  intro q hqQ
  obtain ⟨sel, hqDestroy, hprivate⟩ := hlocalized q hqQ
  have hendpointSelected :
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
        selectedSet sel :=
    (destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
      hqDestroy).2.2
  have hsingleton : ∀ x ∈ crossingAtomEndpoints A B₀ q,
      ({x} : Finset ℕ) ∈
        crossingEndpointTripleObstructionFamily A B₀ q := by
    intro x hx
    simp only [crossingEndpointTripleObstructionFamily,
      if_pos (hQcross q hqQ)]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact targetLocalized_singletonSupports_force_blockOccupancy
    P hblockLower
      crossingEndpointTripleObstructionFamily_cardAtMost
      hcert sel hprivate hendpointSelected hsingleton

/-- Other certificate targets whose entire crossing-endpoint family is
already contained in a fixed selector. -/
noncomputable def crossingEndpointAlignedTargets
    (A B₀ : Set ℕ) {F : ℕ → Finset ℕ}
    (Q : Finset ℕ) (base : BlockSelector F) (q : ℕ) : Finset ℕ := by
  classical
  exact (Q.erase q).filter fun t =>
    (crossingAtomEndpoints A B₀ t : Set ℕ) ⊆ selectedSet base

/-- Aligned targets are, by definition, other targets in the certificate. -/
theorem crossingEndpointAlignedTargets_subset
    (A B₀ : Set ℕ) {F : ℕ → Finset ℕ}
    (Q : Finset ℕ) (base : BlockSelector F) (q : ℕ) :
    crossingEndpointAlignedTargets A B₀ Q base q ⊆ Q.erase q := by
  classical
  intro t ht
  exact (Finset.mem_filter.mp ht).1

/-- The total of the `3`/`1` capacities is one per index plus two per
distinguished index. -/
theorem sum_attach_ite_three_one_eq_card_add_twice
    {Q Aligned : Finset ℕ} (hAlignedSub : Aligned ⊆ Q) :
    (∑ t ∈ Q.attach, if t.1 ∈ Aligned then 3 else 1) =
      Q.card + 2 * Aligned.card := by
  classical
  calc
    (∑ t ∈ Q.attach, if t.1 ∈ Aligned then 3 else 1) =
        ∑ t ∈ Q.attach,
          (1 + 2 * (if t.1 ∈ Aligned then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro t _ht
      split_ifs <;> omega
    _ = Q.card + 2 * Aligned.card := by
      have hbool :
          (∑ t ∈ Q.attach,
            if t.1 ∈ Aligned then 1 else 0) = Aligned.card := by
        rw [Finset.sum_boole]
        have hfilterCard :
            (Q.attach.filter fun t => t.1 ∈ Aligned).card =
              (Q.filter fun t => t ∈ Aligned).card := by
          have hfilter := congrArg Finset.card
            (Finset.filter_attach (fun t => t ∈ Aligned) Q)
          simpa only [Finset.card_map, Finset.card_attach] using hfilter
        have hfilterEq :
            Q.filter (fun t => t ∈ Aligned) = Aligned := by
          ext t
          simp only [Finset.mem_filter]
          constructor
          · exact fun ht => ht.2
          · exact fun ht => ⟨hAlignedSub ht, ht⟩
        rw [hfilterCard, hfilterEq]
        simp
      have htwos :
          (∑ t ∈ Q.attach,
            2 * (if t.1 ∈ Aligned then 1 else 0)) =
              2 * Aligned.card := by
        calc
          (∑ t ∈ Q.attach,
              2 * (if t.1 ∈ Aligned then 1 else 0)) =
              2 * (∑ t ∈ Q.attach,
                if t.1 ∈ Aligned then 1 else 0) := by
            rw [Finset.mul_sum]
          _ = 2 * Aligned.card := by rw [hbool]
      calc
        (∑ t ∈ Q.attach,
            (1 + 2 * (if t.1 ∈ Aligned then 1 else 0))) =
            Q.card +
              (∑ t ∈ Q.attach,
                2 * (if t.1 ∈ Aligned then 1 else 0)) := by
          simp [Finset.sum_add_distrib]
        _ = Q.card + 2 * Aligned.card := by rw [htwos]

/-- If the union of a finite support choice is within `d` of the sum of
prescribed pointwise capacities, then at most `d` chosen supports are
strictly below their capacity.  Any overlap only makes this conclusion
stronger. -/
theorem finiteSupportChoice_shortIndices_card_le_defect
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q)
    (capacity : {n // n ∈ Q} → ℕ)
    {M d : ℕ}
    (hcard : ∀ t : {n // n ∈ Q}, (c t).1.card ≤ capacity t)
    (hcapacitySum : ∑ t ∈ Q.attach, capacity t = M)
    (hunionLower : M - d ≤ (finiteSupportChoiceUnion c).card) :
    (Q.attach.filter fun t => (c t).1.card < capacity t).card ≤ d := by
  classical
  let Short : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => (c t).1.card < capacity t
  have hpoint : ∀ t ∈ Q.attach,
      (c t).1.card + (if t ∈ Short then 1 else 0) ≤ capacity t := by
    intro t _ht
    by_cases htShort : t ∈ Short
    · have hlt : (c t).1.card < capacity t :=
        (Finset.mem_filter.mp htShort).2
      simp [htShort]
      omega
    · simp [htShort]
      exact hcard t
  have hsum :
      (∑ t ∈ Q.attach, (c t).1.card) + Short.card ≤ M := by
    have hsumPoint :
        (∑ t ∈ Q.attach,
          ((c t).1.card + (if t ∈ Short then 1 else 0))) ≤
            ∑ t ∈ Q.attach, capacity t := by
      apply Finset.sum_le_sum
      intro t ht
      exact hpoint t ht
    have hshortSum :
        (∑ t ∈ Q.attach, if t ∈ Short then 1 else 0) =
          Short.card := by
      rw [Finset.sum_boole]
      have hfilterEq : Q.attach.filter (fun t => t ∈ Short) = Short := by
        ext t
        simp only [Finset.mem_filter]
        constructor
        · exact fun ht => ht.2
        · exact fun ht =>
            ⟨(Finset.mem_filter.mp ht).1, ht⟩
      rw [hfilterEq]
      simp
    rw [Finset.sum_add_distrib, hshortSum, hcapacitySum] at hsumPoint
    exact hsumPoint
  have hunionSum : (finiteSupportChoiceUnion c).card ≤
      ∑ t ∈ Q.attach, (c t).1.card :=
    Finset.card_biUnion_le
  change Short.card ≤ d
  omega

/-- If a covered set already has all but `d` of the total incidence
capacity, at most `d` chosen supports can use any point outside that set. -/
theorem finiteSupportChoice_not_subset_card_le_defect
    {R : SupportFamily} {Q V : Finset ℕ}
    (c : FiniteSupportChoice R Q)
    (capacity : {n // n ∈ Q} → ℕ)
    {M d : ℕ}
    (hcard : ∀ t : {n // n ∈ Q}, (c t).1.card ≤ capacity t)
    (hcapacitySum : ∑ t ∈ Q.attach, capacity t = M)
    (hVsub : V ⊆ finiteSupportChoiceUnion c)
    (hVlower : M - d ≤ V.card) :
    (Q.attach.filter fun t => ¬ (c t).1 ⊆ V).card ≤ d := by
  classical
  let Bad : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => ¬ (c t).1 ⊆ V
  have hbadPoint : ∀ t ∈ Q.attach,
      (if ¬ (c t).1 ⊆ V then 1 else 0) ≤ ((c t).1 \ V).card := by
    intro t _ht
    by_cases htSub : (c t).1 ⊆ V
    · simp [htSub]
    · have hnonempty : ((c t).1 \ V).Nonempty :=
        Finset.sdiff_nonempty.mpr htSub
      simp [htSub]
      exact hnonempty
  have hbadSum :
      (∑ t ∈ Q.attach,
        if ¬ (c t).1 ⊆ V then 1 else 0) = Bad.card := by
    rw [Finset.sum_boole]
    rfl
  have hbadOutside : Bad.card ≤
      ∑ t ∈ Q.attach, ((c t).1 \ V).card := by
    rw [← hbadSum]
    apply Finset.sum_le_sum
    intro t ht
    exact hbadPoint t ht
  have hVcover : V ⊆
      Q.attach.biUnion fun t => (c t).1 ∩ V := by
    intro x hxV
    obtain ⟨t, _htAttach, hxt⟩ :=
      Finset.mem_biUnion.mp (hVsub hxV)
    apply Finset.mem_biUnion.mpr
    exact ⟨t, Finset.mem_attach Q t,
      Finset.mem_inter.mpr ⟨hxt, hxV⟩⟩
  have hVincidence : V.card ≤
      ∑ t ∈ Q.attach, ((c t).1 ∩ V).card := by
    exact (Finset.card_le_card hVcover).trans Finset.card_biUnion_le
  have htotal :
      (∑ t ∈ Q.attach, (c t).1.card) ≤ M := by
    calc
      (∑ t ∈ Q.attach, (c t).1.card) ≤
          ∑ t ∈ Q.attach, capacity t := by
        apply Finset.sum_le_sum
        intro t _ht
        exact hcard t
      _ = M := hcapacitySum
  have hdecomp :
      (∑ t ∈ Q.attach, (c t).1.card) =
        (∑ t ∈ Q.attach, ((c t).1 ∩ V).card) +
          ∑ t ∈ Q.attach, ((c t).1 \ V).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    exact (Finset.card_inter_add_card_sdiff (c t).1 V).symm
  change Bad.card ≤ d
  omega

/-- Every aligned index is either a full three-point choice or is short
relative to the `3`/`1` capacity profile. -/
theorem aligned_card_le_fullThree_add_short
    {R : SupportFamily} {Q Aligned : Finset ℕ}
    (c : FiniteSupportChoice R Q)
    (hAlignedSub : Aligned ⊆ Q)
    (hcard : ∀ t : {n // n ∈ Q},
      (c t).1.card ≤ if t.1 ∈ Aligned then 3 else 1) :
    Aligned.card ≤
      (Q.attach.filter fun t =>
        t.1 ∈ Aligned ∧ (c t).1.card = 3).card +
      (Q.attach.filter fun t =>
        (c t).1.card < if t.1 ∈ Aligned then 3 else 1).card := by
  classical
  let I : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => t.1 ∈ Aligned
  let Full : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => t.1 ∈ Aligned ∧ (c t).1.card = 3
  let Short : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t =>
      (c t).1.card < if t.1 ∈ Aligned then 3 else 1
  have hIcard : I.card = Aligned.card := by
    have hfilterCard :
        (Q.attach.filter fun t => t.1 ∈ Aligned).card =
          (Q.filter fun t => t ∈ Aligned).card := by
      have hfilter := congrArg Finset.card
        (Finset.filter_attach (fun t => t ∈ Aligned) Q)
      simpa only [Finset.card_map, Finset.card_attach] using hfilter
    have hfilterEq : Q.filter (fun t => t ∈ Aligned) = Aligned := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · exact fun ht => ht.2
      · exact fun ht => ⟨hAlignedSub ht, ht⟩
    simpa [I, hfilterEq] using hfilterCard
  have hIsub : I ⊆ Full ∪ Short := by
    intro t htI
    have htAligned : t.1 ∈ Aligned := (Finset.mem_filter.mp htI).2
    have htCard : (c t).1.card ≤ 3 := by
      simpa [htAligned] using hcard t
    by_cases hfull : (c t).1.card = 3
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach Q t, htAligned, hfull⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_attach Q t, ?_⟩
      simp [htAligned]
      omega
  have hcardSub : I.card ≤ (Full ∪ Short).card :=
    Finset.card_le_card hIsub
  have hunionCard : (Full ∪ Short).card ≤ Full.card + Short.card :=
    Finset.card_union_le Full Short
  simpa [I, Full, Short, hIcard] using hcardSub.trans hunionCard

/-- A full aligned choice either lies entirely in `V` or belongs to the
family of choices using a point outside `V`. -/
theorem fullAlignedThree_card_le_internal_add_notSubset
    {R : SupportFamily} {Q Aligned V : Finset ℕ}
    (c : FiniteSupportChoice R Q) :
    (Q.attach.filter fun t =>
      t.1 ∈ Aligned ∧ (c t).1.card = 3).card ≤
      (Q.attach.filter fun t =>
        t.1 ∈ Aligned ∧ (c t).1.card = 3 ∧ (c t).1 ⊆ V).card +
      (Q.attach.filter fun t => ¬ (c t).1 ⊆ V).card := by
  classical
  let Full : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => t.1 ∈ Aligned ∧ (c t).1.card = 3
  let Internal : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t =>
      t.1 ∈ Aligned ∧ (c t).1.card = 3 ∧ (c t).1 ⊆ V
  let Outside : Finset {n // n ∈ Q} :=
    Q.attach.filter fun t => ¬ (c t).1 ⊆ V
  have hsub : Full ⊆ Internal ∪ Outside := by
    intro t htFull
    have ht := (Finset.mem_filter.mp htFull).2
    by_cases hinside : (c t).1 ⊆ V
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach Q t, ht.1, ht.2, hinside⟩
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_attach Q t, hinside⟩
  have hcardSub : Full.card ≤ (Internal ∪ Outside).card :=
    Finset.card_le_card hsub
  have hunionCard : (Internal ∪ Outside).card ≤
      Internal.card + Outside.card :=
    Finset.card_union_le Internal Outside
  simpa [Full, Internal, Outside] using hcardSub.trans hunionCard

/-- Every finite indexed set family has a pairwise-disjoint subfamily whose
discarded-index count is at most the incidence defect
`sum(card) - card(union)`.  The subtraction-free displayed inequality is
stable over natural numbers and is the form used below. -/
theorem exists_pairwiseDisjoint_subfamily_with_card_union_bound
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (f : ι → Finset α) :
    ∃ G : Finset ι,
      G ⊆ I ∧
      (G : Set ι).PairwiseDisjoint f ∧
      I.card + (I.biUnion f).card ≤
        G.card + ∑ i ∈ I, (f i).card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
      exact ⟨∅, Finset.Subset.rfl, by simp, by simp⟩
  | @insert a S haS ih =>
      obtain ⟨G, hGS, hpair, hbound⟩ := ih
      let U : Finset α := S.biUnion f
      change S.card + U.card ≤
        G.card + ∑ i ∈ S, (f i).card at hbound
      have hbiUnion : (insert a S).biUnion f = f a ∪ U := by
        simp [U]
      by_cases hdisjoint : Disjoint (f a) U
      · have haG : a ∉ G := by
          intro haG
          exact haS (hGS haG)
        have hpairInsert :
            ((insert a G : Finset ι) : Set ι).PairwiseDisjoint f := by
          rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
          refine ⟨hpair, ?_⟩
          intro g hgG _hga
          apply hdisjoint.mono_right
          intro x hxg
          apply Finset.mem_biUnion.mpr
          exact ⟨g, hGS hgG, hxg⟩
        refine ⟨insert a G, ?_, hpairInsert, ?_⟩
        · intro g hg
          rcases Finset.mem_insert.mp hg with rfl | hgG
          · exact Finset.mem_insert_self _ S
          · exact Finset.mem_insert_of_mem (hGS hgG)
        · rw [Finset.card_insert_of_notMem haS,
            Finset.card_insert_of_notMem haG, hbiUnion,
            Finset.sum_insert haS]
          have hUnionCard : (f a ∪ U).card = (f a).card + U.card :=
            Finset.card_union_of_disjoint hdisjoint
          omega
      · refine ⟨G, ?_, hpair, ?_⟩
        · intro g hgG
          exact Finset.mem_insert_of_mem (hGS hgG)
        · rw [Finset.card_insert_of_notMem haS, hbiUnion,
            Finset.sum_insert haS]
          have hinterNonempty : (f a ∩ U).Nonempty := by
            obtain ⟨x, hxfa, hxU⟩ :=
              Finset.not_disjoint_iff.mp hdisjoint
            exact ⟨x, Finset.mem_inter.mpr ⟨hxfa, hxU⟩⟩
          have hinterPos : 0 < (f a ∩ U).card :=
            Finset.card_pos.mpr hinterNonempty
          have hUnionInter :=
            Finset.card_union_add_card_inter (f a) U
          omega

/-- Support-choice specialization of the preceding near-disjointness
lemma. -/
theorem finiteSupportChoice_exists_pairwiseDisjoint_subfamily
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) :
    ∃ G : Finset {n // n ∈ Q},
      G ⊆ Q.attach ∧
      (G : Set {n // n ∈ Q}).PairwiseDisjoint
        (fun t => (c t).1) ∧
      Q.card + (finiteSupportChoiceUnion c).card ≤
        G.card + ∑ t ∈ Q.attach, (c t).1.card := by
  simpa [finiteSupportChoiceUnion] using
    exists_pairwiseDisjoint_subfamily_with_card_union_bound
      Q.attach (fun t => (c t).1)

/-- Union bound for a support choice in which ordinary indices cost one
point and a distinguished subfamily may cost three. -/
theorem finiteSupportChoiceUnion_card_le_one_plus_two_aligned
    {R : SupportFamily} {Q Aligned : Finset ℕ}
    (c : FiniteSupportChoice R Q)
    (hAlignedSub : Aligned ⊆ Q)
    (hcard : ∀ t : {n // n ∈ Q},
      (c t).1.card ≤ if t.1 ∈ Aligned then 3 else 1) :
    (finiteSupportChoiceUnion c).card ≤
      Q.card + 2 * Aligned.card := by
  classical
  calc
    (finiteSupportChoiceUnion c).card ≤
        ∑ t ∈ Q.attach, (c t).1.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ t ∈ Q.attach,
        if t.1 ∈ Aligned then 3 else 1 := by
      apply Finset.sum_le_sum
      intro t _ht
      exact hcard t
    _ = Q.card + 2 * Aligned.card := by
      calc
        (∑ t ∈ Q.attach,
            if t.1 ∈ Aligned then 3 else 1) =
            ∑ t ∈ Q.attach,
              (1 + 2 * (if t.1 ∈ Aligned then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro t _ht
          split_ifs <;> omega
        _ = Q.card + 2 * Aligned.card := by
          have hbool :
              (∑ t ∈ Q.attach,
                if t.1 ∈ Aligned then 1 else 0) = Aligned.card := by
            rw [Finset.sum_boole]
            have hfilterCard :
                (Q.attach.filter fun t => t.1 ∈ Aligned).card =
                  (Q.filter fun t => t ∈ Aligned).card := by
              have hfilter := congrArg Finset.card
                (Finset.filter_attach (fun t => t ∈ Aligned) Q)
              simpa only [Finset.card_map, Finset.card_attach] using hfilter
            have hfilterEq :
                Q.filter (fun t => t ∈ Aligned) = Aligned := by
              ext t
              simp only [Finset.mem_filter]
              constructor
              · exact fun ht => ht.2
              · exact fun ht => ⟨hAlignedSub ht, ht⟩
            rw [hfilterCard, hfilterEq]
            simp
          have htwos :
              (∑ t ∈ Q.attach,
                2 * (if t.1 ∈ Aligned then 1 else 0)) =
                  2 * Aligned.card := by
            calc
              (∑ t ∈ Q.attach,
                  2 * (if t.1 ∈ Aligned then 1 else 0)) =
                  2 * (∑ t ∈ Q.attach,
                    if t.1 ∈ Aligned then 1 else 0) := by
                rw [Finset.mul_sum]
              _ = 2 * Aligned.card := by rw [hbool]
          calc
            (∑ t ∈ Q.attach,
                (1 + 2 * (if t.1 ∈ Aligned then 1 else 0))) =
                Q.card +
                  (∑ t ∈ Q.attach,
                    2 * (if t.1 ∈ Aligned then 1 else 0)) := by
              simp [Finset.sum_add_distrib]
            _ = Q.card + 2 * Aligned.card := by rw [htwos]

/-- A target-private selector admits a controlled surviving-support choice
for all other certificate targets.  An unaligned target supplies a missing
endpoint singleton, while an aligned target supplies a genuine surviving
order-three support. -/
theorem exists_controlledCrossingEndpointSupportChoice_of_private
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {q : ℕ}
    (hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (base : BlockSelector F)
    (hprivate : ∀ t ∈ Q, t ≠ q →
      ¬ DestroysAt
        (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet base) t) :
    ∃ cOther : FiniteSupportChoice
        (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q),
      (∀ t : {n // n ∈ Q.erase q},
        Disjoint ((cOther t).1 : Set ℕ) (selectedSet base)) ∧
      (∀ t : {n // n ∈ Q.erase q},
        (cOther t).1.card ≤
          if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
          then 3 else 1) ∧
      ∀ t : {n // n ∈ Q.erase q},
        if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
        then (cOther t).1 ∈ additiveSupportFamily A 3 t.1
        else (cOther t).1.card = 1 := by
  classical
  let Aligned : Finset ℕ :=
    crossingEndpointAlignedTargets A B₀ Q base q
  have hcontrolled : ∀ t : {n // n ∈ Q.erase q}, ∃ E : Finset ℕ,
      E ∈ crossingEndpointTripleObstructionFamily A B₀ t.1 ∧
      Disjoint (E : Set ℕ) (selectedSet base) ∧
      E.card ≤ (if t.1 ∈ Aligned then 3 else 1) ∧
      (if t.1 ∈ Aligned then
        E ∈ additiveSupportFamily A 3 t.1 else E.card = 1) := by
    intro t
    have htErase := Finset.mem_erase.mp t.2
    have htQ : t.1 ∈ Q := htErase.2
    by_cases htAligned : t.1 ∈ Aligned
    · have hendpointSub :
          (crossingAtomEndpoints A B₀ t.1 : Set ℕ) ⊆
            selectedSet base := by
        change t.1 ∈ (Q.erase q).filter (fun u =>
          (crossingAtomEndpoints A B₀ u : Set ℕ) ⊆
            selectedSet base) at htAligned
        exact (Finset.mem_filter.mp htAligned).2
      have hnotTriple : ¬ DestroysAt (additiveSupportFamily A 3)
          (selectedSet base) t.1 := by
        intro htriple
        apply hprivate t.1 htQ htErase.1
        exact destroysAt_crossingEndpointTripleObstructionFamily_iff.mpr
          ⟨hQcross t.1 htQ, htriple, hendpointSub⟩
      obtain ⟨G, hGR, hGdisjoint⟩ :=
        not_destroysAt_iff.mp hnotTriple
      refine ⟨G, ?_, hGdisjoint, ?_, ?_⟩
      · simp only [crossingEndpointTripleObstructionFamily,
          if_pos (hQcross t.1 htQ)]
        exact Finset.mem_union_left _ hGR
      · simpa [htAligned] using
          additiveSupportFamily_cardAtMost A 3 t.1 G hGR
      · simpa [htAligned] using hGR
    · have hendpointNotSub :
          ¬ (crossingAtomEndpoints A B₀ t.1 : Set ℕ) ⊆
            selectedSet base := by
        intro hsub
        apply htAligned
        change t.1 ∈ (Q.erase q).filter (fun u =>
          (crossingAtomEndpoints A B₀ u : Set ℕ) ⊆
            selectedSet base)
        exact Finset.mem_filter.mpr ⟨t.2, hsub⟩
      obtain ⟨x, hxEndpoint, hxNotSelected⟩ :=
        Set.not_subset.mp hendpointNotSub
      refine ⟨{x}, ?_, ?_, ?_, ?_⟩
      · simp only [crossingEndpointTripleObstructionFamily,
          if_pos (hQcross t.1 htQ)]
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨x, Finset.mem_coe.mp hxEndpoint, rfl⟩
      · rw [Set.disjoint_left]
        intro y hySingleton hySelected
        have hyx : y = x := by simpa using hySingleton
        exact hxNotSelected (hyx ▸ hySelected)
      · simp [htAligned]
      · simp [htAligned]
  choose chosen hchosenMem hchosenDisjoint hchosenCard hchosenKind using
    hcontrolled
  let cOther : FiniteSupportChoice
      (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q) := fun t =>
    ⟨chosen t, hchosenMem t⟩
  refine ⟨cOther, ?_, ?_, ?_⟩
  · intro t
    simpa [cOther] using hchosenDisjoint t
  · intro t
    simpa [cOther, Aligned] using hchosenCard t
  · intro t
    simpa [cOther, Aligned] using hchosenKind t

/-- Structural form of refined endpoint occupancy.  For each private target
there is one controlled surviving support for every other target, and their
union covers the remainder of every block selected by a crossing endpoint
of the private target. -/
theorem minimalCrossingEndpointTripleCertificate_forces_refinedEndpointCover
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hQcross : ∀ q ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q)
    (hlocalized : ∀ q ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q') :
    ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet base) q ∧
      (∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet base) q') ∧
      ∃ cOther : FiniteSupportChoice
          (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q),
        (∀ t : {n // n ∈ Q.erase q},
          Disjoint ((cOther t).1 : Set ℕ) (selectedSet base)) ∧
        (∀ t : {n // n ∈ Q.erase q},
          (cOther t).1.card ≤
            if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
            then 3 else 1) ∧
        (∀ t : {n // n ∈ Q.erase q},
          if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
          then (cOther t).1 ∈ additiveSupportFamily A 3 t.1
          else (cOther t).1.card = 1) ∧
        (finiteSupportChoiceUnion cOther).card ≤
          (Q.erase q).card +
            2 * (crossingEndpointAlignedTargets A B₀ Q base q).card ∧
        ∀ x ∈ crossingAtomEndpoints A B₀ q,
          F (blockIndex P x) \ {x} ⊆
            finiteSupportChoiceUnion cOther := by
  classical
  intro q hqQ
  obtain ⟨base, hqDestroy, hprivate⟩ := hlocalized q hqQ
  obtain ⟨cOther, hdisjoint, hcard, hkind⟩ :=
    exists_controlledCrossingEndpointSupportChoice_of_private
      hQcross base hprivate
  have hsingleton : ∀ x ∈ crossingAtomEndpoints A B₀ q,
      ({x} : Finset ℕ) ∈
        crossingEndpointTripleObstructionFamily A B₀ q := by
    intro x hx
    simp only [crossingEndpointTripleObstructionFamily,
      if_pos (hQcross q hqQ)]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hcover : ∀ x ∈ crossingAtomEndpoints A B₀ q,
      F (blockIndex P x) \ {x} ⊆
        finiteSupportChoiceUnion cOther :=
    targetLocalized_singletonSupports_force_blockCover_of_choice
      P hcert base cOther hdisjoint hsingleton
  have hunion : (finiteSupportChoiceUnion cOther).card ≤
      (Q.erase q).card +
        2 * (crossingEndpointAlignedTargets A B₀ Q base q).card :=
    finiteSupportChoiceUnion_card_le_one_plus_two_aligned
      cOther
        (crossingEndpointAlignedTargets_subset A B₀ Q base q)
        hcard
  exact ⟨base, hqDestroy, hprivate, cOther,
    hdisjoint, hcard, hkind, hunion, hcover⟩

set_option maxHeartbeats 5000000 in
/-- Refined private-selector occupancy.  An unaligned other target has a
missing singleton endpoint, so it contributes only one point to the support
union.  Only an aligned target can require a surviving triple support and
contribute three points.  Thus, if `a_q` counts the aligned other targets,

`(k - 1) * |X_q| ≤ (|Q| - 1) + 2 * a_q`.

For near-sharp certificates this forces any two- or three-endpoint target to
share its private selector with many other endpoint families. -/
theorem minimalCrossingEndpointTripleCertificate_forces_refinedEndpointBound
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ q ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q)
    (hlocalized : ∀ q ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q') :
    ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet base) q ∧
      (∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet base) q') ∧
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card +
          2 * (crossingEndpointAlignedTargets A B₀ Q base q).card := by
  classical
  intro q hqQ
  obtain ⟨base, hqDestroy, hprivate, cOther,
      hdisjoint, _hchosenCard, _hchosenKind, hunion, _hpointCover⟩ :=
    minimalCrossingEndpointTripleCertificate_forces_refinedEndpointCover
      P hQcross hcert hlocalized q hqQ
  have hendpointSelected :
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
        selectedSet base :=
    (destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
      hqDestroy).2.2
  have hsingleton : ∀ x ∈ crossingAtomEndpoints A B₀ q,
      ({x} : Finset ℕ) ∈
        crossingEndpointTripleObstructionFamily A B₀ q := by
    intro x hx
    simp only [crossingEndpointTripleObstructionFamily,
      if_pos (hQcross q hqQ)]
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hoccupancy :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (finiteSupportChoiceUnion cOther).card :=
    targetLocalized_singletonSupports_force_blockOccupancy_of_choice
      P hblockLower hcert base cOther
        hdisjoint
        hendpointSelected hsingleton
  refine ⟨base, hqDestroy, hprivate, ?_⟩
  exact hoccupancy.trans hunion

/-- At the first strict cardinality above a `k`-point block, the scaled
occupancy inequality forces every endpoint family to have size at most
three as soon as `k ≥ 5`. -/
theorem nearSharp_scaledEndpointBound_forces_endpointCard_le_three
    {A B₀ : Set ℕ} {Q : Finset ℕ} {q k : ℕ}
    (hk : 5 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card ≤ k + 1)
    (hscaled :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        3 * (Q.erase q).card) :
    (crossingAtomEndpoints A B₀ q).card ≤ 3 := by
  have heraseCard : (Q.erase q).card = Q.card - 1 :=
    Finset.card_erase_of_mem hqQ
  have heraseLe : (Q.erase q).card ≤ k := by
    rw [heraseCard]
    omega
  by_contra hnot
  have hfour : 4 ≤ (crossingAtomEndpoints A B₀ q).card := by
    omega
  have hlower : 4 * (k - 1) ≤
      (k - 1) * (crossingAtomEndpoints A B₀ q).card := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (k - 1) hfour
  have hupper : 3 * (Q.erase q).card ≤ 3 * k :=
    Nat.mul_le_mul_left 3 heraseLe
  have : 4 * (k - 1) ≤ 3 * k :=
    hlower.trans (hscaled.trans hupper)
  omega

/-- In a near-sharp certificate, a three-endpoint target forces its private
selector to align with all but at most one of the other targets. -/
theorem nearSharp_refinedEndpointBound_three_forces_almostAllAligned
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {base : BlockSelector F} {q k : ℕ}
    (hk : 2 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card ≤ k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3)
    (hrefined :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card +
          2 * (crossingEndpointAlignedTargets A B₀ Q base q).card) :
    k - 1 ≤
      (crossingEndpointAlignedTargets A B₀ Q base q).card := by
  have heraseCard : (Q.erase q).card = Q.card - 1 :=
    Finset.card_erase_of_mem hqQ
  have heraseLe : (Q.erase q).card ≤ k := by
    rw [heraseCard]
    omega
  by_contra hnot
  have halignedLe :
      (crossingEndpointAlignedTargets A B₀ Q base q).card ≤ k - 2 := by
    omega
  rw [hendpointCard] at hrefined
  omega

/-- At the exact first strict size `|Q| = k + 1`, a three-endpoint target's
private selector contains the full endpoint families of either all other
targets or all but exactly one of them. -/
theorem nearSharp_refinedEndpointBound_three_aligned_eq_k_or_pred
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {base : BlockSelector F} {q k : ℕ}
    (hk : 2 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3)
    (hrefined :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card +
          2 * (crossingEndpointAlignedTargets A B₀ Q base q).card) :
    (crossingEndpointAlignedTargets A B₀ Q base q).card = k - 1 ∨
      (crossingEndpointAlignedTargets A B₀ Q base q).card = k := by
  have hlower : k - 1 ≤
      (crossingEndpointAlignedTargets A B₀ Q base q).card :=
    nearSharp_refinedEndpointBound_three_forces_almostAllAligned
      hk hqQ (by omega) hendpointCard hrefined
  have hsubset :
      crossingEndpointAlignedTargets A B₀ Q base q ⊆ Q.erase q :=
    crossingEndpointAlignedTargets_subset A B₀ Q base q
  have hupper :
      (crossingEndpointAlignedTargets A B₀ Q base q).card ≤ k := by
    have heraseCard : (Q.erase q).card = k := by
      rw [Finset.card_erase_of_mem hqQ, hQcard]
      omega
    exact (Finset.card_le_card hsubset).trans_eq heraseCard
  omega

set_option maxHeartbeats 5000000 in
/-- Structural near-equality in the first strict certificate size.  For a
three-endpoint private target, the three disjoint block remainders lie in
the surviving-support union.  If exactly one other target is unaligned the
union has at most one further point; if all other targets align it has at
most three further points. -/
theorem minimalCrossingEndpointTripleCertificate_threeEndpoint_nearCover
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {q k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t)
    (hlocalized : ∀ t ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t ∧
      ∀ t' ∈ Q, t' ≠ t →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) t')
    (hk : 2 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3) :
    ∃ base : BlockSelector F,
      ∃ cOther : FiniteSupportChoice
          (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q),
        DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet base) q ∧
        (∀ t ∈ Q, t ≠ q →
          ¬ DestroysAt
            (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet base) t) ∧
        (∀ t : {n // n ∈ Q.erase q},
          Disjoint ((cOther t).1 : Set ℕ) (selectedSet base)) ∧
        (∀ t : {n // n ∈ Q.erase q},
          (cOther t).1.card ≤
            if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
            then 3 else 1) ∧
        (∀ t : {n // n ∈ Q.erase q},
          if t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q
          then (cOther t).1 ∈ additiveSupportFamily A 3 t.1
          else (cOther t).1.card = 1) ∧
        selectedBlockRemainderUnion P
            (crossingAtomEndpoints A B₀ q) ⊆
          finiteSupportChoiceUnion cOther ∧
        (((crossingEndpointAlignedTargets A B₀ Q base q).card =
              k - 1 ∧
            (finiteSupportChoiceUnion cOther).card ≤
              (selectedBlockRemainderUnion P
                (crossingAtomEndpoints A B₀ q)).card + 1 ∧
            ((Q.erase q).attach.filter fun t =>
              (cOther t).1.card <
                if t.1 ∈ crossingEndpointAlignedTargets
                    A B₀ Q base q then 3 else 1).card ≤ 1 ∧
            k - 2 ≤ ((Q.erase q).attach.filter fun t =>
              t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
                (cOther t).1.card = 3).card ∧
            ((Q.erase q).attach.filter fun t =>
              ¬ (cOther t).1 ⊆ selectedBlockRemainderUnion P
                (crossingAtomEndpoints A B₀ q)).card ≤ 1 ∧
            k - 3 ≤ ((Q.erase q).attach.filter fun t =>
              t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
                (cOther t).1.card = 3 ∧
                (cOther t).1 ⊆ selectedBlockRemainderUnion P
                  (crossingAtomEndpoints A B₀ q)).card) ∨
          ((crossingEndpointAlignedTargets A B₀ Q base q).card = k ∧
            (finiteSupportChoiceUnion cOther).card ≤
              (selectedBlockRemainderUnion P
                (crossingAtomEndpoints A B₀ q)).card + 3 ∧
            ((Q.erase q).attach.filter fun t =>
              (cOther t).1.card <
                if t.1 ∈ crossingEndpointAlignedTargets
                    A B₀ Q base q then 3 else 1).card ≤ 3 ∧
            k - 3 ≤ ((Q.erase q).attach.filter fun t =>
              t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
                (cOther t).1.card = 3).card ∧
            ((Q.erase q).attach.filter fun t =>
              ¬ (cOther t).1 ⊆ selectedBlockRemainderUnion P
                (crossingAtomEndpoints A B₀ q)).card ≤ 3 ∧
            k - 6 ≤ ((Q.erase q).attach.filter fun t =>
              t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
                (cOther t).1.card = 3 ∧
                (cOther t).1 ⊆ selectedBlockRemainderUnion P
                  (crossingAtomEndpoints A B₀ q)).card)) := by
  classical
  obtain ⟨base, hqDestroy, hprivate, cOther,
      hdisjoint, hchosenCard, hchosenKind, hunion, hpointCover⟩ :=
    minimalCrossingEndpointTripleCertificate_forces_refinedEndpointCover
      P hQcross hcert hlocalized q hqQ
  let X : Finset ℕ := crossingAtomEndpoints A B₀ q
  let V : Finset ℕ := selectedBlockRemainderUnion P X
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  let Aligned : Finset ℕ :=
    crossingEndpointAlignedTargets A B₀ Q base q
  have hendpointSelected : (X : Set ℕ) ⊆ selectedSet base := by
    simpa [X] using
      (destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
        hqDestroy).2.2
  have hVlower : 3 * (k - 1) ≤ V.card := by
    have hlower := selectedBlockRemainderUnion_card_lower
      P hblockLower base hendpointSelected
    rw [hendpointCard] at hlower
    simpa [V, X, Nat.mul_comm] using hlower
  have hVsub : V ⊆ U := by
    apply selectedBlockRemainderUnion_subset P
    intro x hxX
    simpa [U, X] using hpointCover x hxX
  have hUupper : U.card ≤ (Q.erase q).card + 2 * Aligned.card := by
    simpa [U, Aligned] using hunion
  have hrefined :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card + 2 * Aligned.card := by
    have hVU : V.card ≤ U.card := Finset.card_le_card hVsub
    rw [hendpointCard]
    have : 3 * (k - 1) ≤
        (Q.erase q).card + 2 * Aligned.card :=
      hVlower.trans (hVU.trans hUupper)
    simpa [Nat.mul_comm] using this
  have halignedCases : Aligned.card = k - 1 ∨ Aligned.card = k := by
    simpa [Aligned] using
      nearSharp_refinedEndpointBound_three_aligned_eq_k_or_pred
        (A := A) (B₀ := B₀) hk hqQ hQcard
          hendpointCard (by simpa [Aligned] using hrefined)
  have heraseCard : (Q.erase q).card = k := by
    rw [Finset.card_erase_of_mem hqQ, hQcard]
    omega
  have hVU : V.card ≤ U.card := Finset.card_le_card hVsub
  have hULower : 3 * (k - 1) ≤ U.card := hVlower.trans hVU
  refine ⟨base, cOther, hqDestroy, hprivate, hdisjoint,
    hchosenCard, hchosenKind,
    by simpa [V, U, X] using hVsub, ?_⟩
  rcases halignedCases with haligned | haligned
  · left
    have hUcap : U.card ≤ 3 * k - 2 := by
      rw [heraseCard, haligned] at hUupper
      omega
    have hslack : U.card ≤ V.card + 1 := by omega
    have hcapacitySum :
        (∑ t ∈ (Q.erase q).attach,
          if t.1 ∈ Aligned then 3 else 1) = 3 * k - 2 := by
      calc
        (∑ t ∈ (Q.erase q).attach,
            if t.1 ∈ Aligned then 3 else 1) =
            (Q.erase q).card + 2 * Aligned.card :=
          sum_attach_ite_three_one_eq_card_add_twice
            (by simpa [Aligned] using
              crossingEndpointAlignedTargets_subset A B₀ Q base q)
        _ = 3 * k - 2 := by rw [heraseCard, haligned]; omega
    have hshort := finiteSupportChoice_shortIndices_card_le_defect
      cOther (fun t => if t.1 ∈ Aligned then 3 else 1)
        (fun t => by simpa [Aligned] using hchosenCard t)
        hcapacitySum (d := 1) (by
          have heq : (3 * k - 2) - 1 = 3 * (k - 1) := by omega
          rw [heq]
          exact hULower)
    have hfullBound := aligned_card_le_fullThree_add_short
      cOther
        (by simpa [Aligned] using
          crossingEndpointAlignedTargets_subset A B₀ Q base q)
        (fun t => by simpa [Aligned] using hchosenCard t)
    change Aligned.card ≤
      ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card +
      ((Q.erase q).attach.filter fun t =>
        (cOther t).1.card <
          if t.1 ∈ Aligned then 3 else 1).card at hfullBound
    change ((Q.erase q).attach.filter fun t =>
      (cOther t).1.card <
        if t.1 ∈ Aligned then 3 else 1).card ≤ 1 at hshort
    have hfullLower : k - 2 ≤
        ((Q.erase q).attach.filter fun t =>
          t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card := by
      rw [haligned] at hfullBound
      have hkPred : k - 1 = (k - 2) + 1 := by omega
      rw [hkPred] at hfullBound
      omega
    have houtside := finiteSupportChoice_not_subset_card_le_defect
      cOther (fun t => if t.1 ∈ Aligned then 3 else 1)
        (fun t => by simpa [Aligned] using hchosenCard t)
        hcapacitySum hVsub (d := 1) (by
          have heq : (3 * k - 2) - 1 = 3 * (k - 1) := by omega
          rw [heq]
          exact hVlower)
    change ((Q.erase q).attach.filter fun t =>
      ¬ (cOther t).1 ⊆ V).card ≤ 1 at houtside
    have hinternalBound :=
      fullAlignedThree_card_le_internal_add_notSubset
        (Aligned := Aligned) (V := V) cOther
    change ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card ≤
      ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3 ∧
          (cOther t).1 ⊆ V).card +
      ((Q.erase q).attach.filter fun t =>
        ¬ (cOther t).1 ⊆ V).card at hinternalBound
    have hinternalLower : k - 3 ≤
        ((Q.erase q).attach.filter fun t =>
          t.1 ∈ Aligned ∧ (cOther t).1.card = 3 ∧
            (cOther t).1 ⊆ V).card := by
      by_cases hkThree : 3 ≤ k
      · have hkPred : k - 2 = (k - 3) + 1 := by omega
        rw [hkPred] at hfullLower
        omega
      · omega
    exact ⟨by simpa [Aligned] using haligned,
      by simpa [U, V, X] using hslack,
      by simpa [Aligned] using hshort,
      by simpa [Aligned] using hfullLower,
      by simpa [V, X] using houtside,
      by simpa [Aligned, V, X] using hinternalLower⟩
  · right
    have hUcap : U.card ≤ 3 * k := by
      rw [heraseCard, haligned] at hUupper
      omega
    have hslack : U.card ≤ V.card + 3 := by omega
    have hcapacitySum :
        (∑ t ∈ (Q.erase q).attach,
          if t.1 ∈ Aligned then 3 else 1) = 3 * k := by
      calc
        (∑ t ∈ (Q.erase q).attach,
            if t.1 ∈ Aligned then 3 else 1) =
            (Q.erase q).card + 2 * Aligned.card :=
          sum_attach_ite_three_one_eq_card_add_twice
            (by simpa [Aligned] using
              crossingEndpointAlignedTargets_subset A B₀ Q base q)
        _ = 3 * k := by rw [heraseCard, haligned]; omega
    have hshort := finiteSupportChoice_shortIndices_card_le_defect
      cOther (fun t => if t.1 ∈ Aligned then 3 else 1)
        (fun t => by simpa [Aligned] using hchosenCard t)
        hcapacitySum (d := 3) (by
          have heq : 3 * k - 3 = 3 * (k - 1) := by omega
          rw [heq]
          exact hULower)
    have hfullBound := aligned_card_le_fullThree_add_short
      cOther
        (by simpa [Aligned] using
          crossingEndpointAlignedTargets_subset A B₀ Q base q)
        (fun t => by simpa [Aligned] using hchosenCard t)
    change Aligned.card ≤
      ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card +
      ((Q.erase q).attach.filter fun t =>
        (cOther t).1.card <
          if t.1 ∈ Aligned then 3 else 1).card at hfullBound
    change ((Q.erase q).attach.filter fun t =>
      (cOther t).1.card <
        if t.1 ∈ Aligned then 3 else 1).card ≤ 3 at hshort
    have hfullLower : k - 3 ≤
        ((Q.erase q).attach.filter fun t =>
          t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card := by
      rw [haligned] at hfullBound
      by_cases hkThree : 3 ≤ k
      · have hkPred : k = (k - 3) + 3 := by omega
        rw [hkPred] at hfullBound
        omega
      · omega
    have houtside := finiteSupportChoice_not_subset_card_le_defect
      cOther (fun t => if t.1 ∈ Aligned then 3 else 1)
        (fun t => by simpa [Aligned] using hchosenCard t)
        hcapacitySum hVsub (d := 3) (by
          have heq : 3 * k - 3 = 3 * (k - 1) := by omega
          rw [heq]
          exact hVlower)
    change ((Q.erase q).attach.filter fun t =>
      ¬ (cOther t).1 ⊆ V).card ≤ 3 at houtside
    have hinternalBound :=
      fullAlignedThree_card_le_internal_add_notSubset
        (Aligned := Aligned) (V := V) cOther
    change ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3).card ≤
      ((Q.erase q).attach.filter fun t =>
        t.1 ∈ Aligned ∧ (cOther t).1.card = 3 ∧
          (cOther t).1 ⊆ V).card +
      ((Q.erase q).attach.filter fun t =>
        ¬ (cOther t).1 ⊆ V).card at hinternalBound
    have hinternalLower : k - 6 ≤
        ((Q.erase q).attach.filter fun t =>
          t.1 ∈ Aligned ∧ (cOther t).1.card = 3 ∧
            (cOther t).1 ⊆ V).card := by
      by_cases hkSix : 6 ≤ k
      · have hkPred : k - 3 = (k - 6) + 3 := by omega
        rw [hkPred] at hfullLower
        omega
      · omega
    exact ⟨by simpa [Aligned] using haligned,
      by simpa [U, V, X] using hslack,
      by simpa [Aligned] using hshort,
      by simpa [Aligned] using hfullLower,
      by simpa [V, X] using houtside,
      by simpa [Aligned, V, X] using hinternalLower⟩

/-- A three-point support of an order-three additive representation uses
each of its three vertices exactly once, so its finset sum is the target. -/
theorem additiveSupportFamily_three_sum_eq_of_card_eq_three
    {A : Set ℕ} {q : ℕ} {G : Finset ℕ}
    (hGR : G ∈ additiveSupportFamily A 3 q)
    (hGcard : G.card = 3) :
    G.sum id = q := by
  classical
  obtain ⟨v, _hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hGR
  have himageCard :
      (Finset.univ.image fun i : Fin 3 => (v i).1).card =
        (Finset.univ : Finset (Fin 3)).card := by
    rw [← tupleSupport]
    rw [hGcard]
    simp
  have hinj : Set.InjOn (fun i : Fin 3 => (v i).1)
      ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) :=
    Finset.card_image_iff.mp himageCard
  rw [tupleSupport, Finset.sum_image]
  · simpa using hvsum
  · exact hinj

set_option maxHeartbeats 5000000 in
/-- Uniform payload of the three-endpoint near-cover theorem.  Regardless
of which alignment case occurs, at least `k - 6` distinct other targets have
a genuine three-point additive support, disjoint from the private selector
and contained in the same three block remainders. -/
theorem minimalCrossingEndpointTripleCertificate_threeEndpoint_forces_trappedTripleSupports
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {q k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t)
    (hlocalized : ∀ t ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t ∧
      ∀ t' ∈ Q, t' ≠ t →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) t')
    (hk : 2 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3) :
    ∃ base : BlockSelector F,
      ∃ cOther : FiniteSupportChoice
          (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q),
        ∃ T : Finset {n // n ∈ Q.erase q},
          DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet base) q ∧
          (∀ t ∈ Q, t ≠ q →
            ¬ DestroysAt
              (crossingEndpointTripleObstructionFamily A B₀)
              (selectedSet base) t) ∧
          k - 6 ≤ T.card ∧
          ∀ t ∈ T,
            t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
            (cOther t).1 ∈ additiveSupportFamily A 3 t.1 ∧
            (cOther t).1.card = 3 ∧
            (cOther t).1.sum id = t.1 ∧
            (cOther t).1 ⊆ selectedBlockRemainderUnion P
              (crossingAtomEndpoints A B₀ q) ∧
            Disjoint ((cOther t).1 : Set ℕ) (selectedSet base) := by
  classical
  obtain ⟨base, cOther, hqDestroy, hprivate, hdisjoint,
      _hcard, hkind, _hVsub, hcases⟩ :=
    minimalCrossingEndpointTripleCertificate_threeEndpoint_nearCover
      P hblockLower hQcross hcert hlocalized hk hqQ hQcard hendpointCard
  let T : Finset {n // n ∈ Q.erase q} :=
    (Q.erase q).attach.filter fun t =>
      t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
      (cOther t).1.card = 3 ∧
      (cOther t).1 ⊆ selectedBlockRemainderUnion P
        (crossingAtomEndpoints A B₀ q)
  have hTlower : k - 6 ≤ T.card := by
    rcases hcases with
        ⟨_haligned, _hslack, _hshort, _hfull,
          _houtside, hinternal⟩ |
        ⟨_haligned, _hslack, _hshort, _hfull,
          _houtside, hinternal⟩
    · have : k - 6 ≤ k - 3 := by omega
      exact this.trans (by simpa [T] using hinternal)
    · simpa [T] using hinternal
  have hTdata : ∀ t ∈ T,
      t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
      (cOther t).1 ∈ additiveSupportFamily A 3 t.1 ∧
      (cOther t).1.card = 3 ∧
      (cOther t).1.sum id = t.1 ∧
      (cOther t).1 ⊆ selectedBlockRemainderUnion P
        (crossingAtomEndpoints A B₀ q) ∧
      Disjoint ((cOther t).1 : Set ℕ) (selectedSet base) := by
    intro t htT
    have ht := (Finset.mem_filter.mp htT).2
    have htriple : (cOther t).1 ∈ additiveSupportFamily A 3 t.1 := by
      simpa [ht.1] using hkind t
    have hsum : (cOther t).1.sum id = t.1 :=
      additiveSupportFamily_three_sum_eq_of_card_eq_three
        htriple ht.2.1
    exact ⟨ht.1, htriple, ht.2.1, hsum,
      ht.2.2, hdisjoint t⟩
  exact ⟨base, cOther, T, hqDestroy, hprivate, hTlower, hTdata⟩

set_option maxHeartbeats 5000000 in
/-- Near-equality also forces an almost-complete matching: after losing at
most the three incidence-defect indices and the exceptional trapped-support
indices, at least `k - 9` genuine three-point supports remain pairwise
disjoint inside the same three block remainders. -/
theorem minimalCrossingEndpointTripleCertificate_threeEndpoint_forces_disjointTrappedTripleSupports
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {q k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t)
    (hlocalized : ∀ t ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t ∧
      ∀ t' ∈ Q, t' ≠ t →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) t')
    (hk : 2 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3) :
    ∃ base : BlockSelector F,
      ∃ cOther : FiniteSupportChoice
          (crossingEndpointTripleObstructionFamily A B₀) (Q.erase q),
        ∃ T : Finset {n // n ∈ Q.erase q},
          DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet base) q ∧
          (∀ t ∈ Q, t ≠ q →
            ¬ DestroysAt
              (crossingEndpointTripleObstructionFamily A B₀)
              (selectedSet base) t) ∧
          k - 9 ≤ T.card ∧
          (T : Set {n // n ∈ Q.erase q}).PairwiseDisjoint
            (fun t => (cOther t).1) ∧
          (selectedBlockRemainderUnion P
              (crossingAtomEndpoints A B₀ q) \
            T.biUnion fun t => (cOther t).1).card ≤ 27 ∧
          ∀ t ∈ T,
            t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
            (cOther t).1 ∈ additiveSupportFamily A 3 t.1 ∧
            (cOther t).1.card = 3 ∧
            (cOther t).1.sum id = t.1 ∧
            (cOther t).1 ⊆ selectedBlockRemainderUnion P
              (crossingAtomEndpoints A B₀ q) ∧
            Disjoint ((cOther t).1 : Set ℕ) (selectedSet base) := by
  classical
  obtain ⟨base, cOther, hqDestroy, hprivate, hdisjoint,
      hcard, hkind, hVsubRaw, hcases⟩ :=
    minimalCrossingEndpointTripleCertificate_threeEndpoint_nearCover
      P hblockLower hQcross hcert hlocalized hk hqQ hQcard hendpointCard
  let Aligned : Finset ℕ :=
    crossingEndpointAlignedTargets A B₀ Q base q
  let V : Finset ℕ := selectedBlockRemainderUnion P
    (crossingAtomEndpoints A B₀ q)
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  let Internal : Finset {n // n ∈ Q.erase q} :=
    (Q.erase q).attach.filter fun t =>
      t.1 ∈ Aligned ∧ (cOther t).1.card = 3 ∧ (cOther t).1 ⊆ V
  have hVsub : V ⊆ U := by
    simpa [V, U] using hVsubRaw
  have hendpointSelected :
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ selectedSet base :=
    (destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
      hqDestroy).2.2
  have hVlower : 3 * (k - 1) ≤ V.card := by
    have hlower := selectedBlockRemainderUnion_card_lower
      P hblockLower base hendpointSelected
    rw [hendpointCard] at hlower
    simpa [V, Nat.mul_comm] using hlower
  have hULower : 3 * (k - 1) ≤ U.card :=
    hVlower.trans (Finset.card_le_card hVsub)
  have heraseCard : (Q.erase q).card = k := by
    rw [Finset.card_erase_of_mem hqQ, hQcard]
    omega
  obtain ⟨Good, hGoodSub, hGoodPair, hGoodBound⟩ :=
    finiteSupportChoice_exists_pairwiseDisjoint_subfamily cOther
  change (Q.erase q).card + U.card ≤
    Good.card + ∑ t ∈ (Q.erase q).attach, (cOther t).1.card at hGoodBound
  have hcaseBounds :
      (k - 1 ≤ Good.card ∧ k - 3 ≤ Internal.card) ∨
      (k - 3 ≤ Good.card ∧ k - 6 ≤ Internal.card) := by
    rcases hcases with
        ⟨haligned, _hslack, _hshort, _hfull,
          _houtside, hinternal⟩ |
        ⟨haligned, _hslack, _hshort, _hfull,
          _houtside, hinternal⟩
    · left
      have hcapacitySum :
          (∑ t ∈ (Q.erase q).attach,
            if t.1 ∈ Aligned then 3 else 1) = 3 * k - 2 := by
        calc
          (∑ t ∈ (Q.erase q).attach,
              if t.1 ∈ Aligned then 3 else 1) =
              (Q.erase q).card + 2 * Aligned.card :=
            sum_attach_ite_three_one_eq_card_add_twice
              (by simpa [Aligned] using
                crossingEndpointAlignedTargets_subset A B₀ Q base q)
          _ = 3 * k - 2 := by
            rw [heraseCard]
            have haligned' : Aligned.card = k - 1 := by
              simpa [Aligned] using haligned
            rw [haligned']
            omega
      have hsumUpper :
          (∑ t ∈ (Q.erase q).attach, (cOther t).1.card) ≤
            3 * k - 2 := by
        calc
          (∑ t ∈ (Q.erase q).attach, (cOther t).1.card) ≤
              ∑ t ∈ (Q.erase q).attach,
                if t.1 ∈ Aligned then 3 else 1 := by
            apply Finset.sum_le_sum
            intro t _ht
            simpa [Aligned] using hcard t
          _ = 3 * k - 2 := hcapacitySum
      have hGoodLower : k - 1 ≤ Good.card := by
        rw [heraseCard] at hGoodBound
        omega
      exact ⟨hGoodLower, by simpa [Internal, Aligned, V] using hinternal⟩
    · right
      have hcapacitySum :
          (∑ t ∈ (Q.erase q).attach,
            if t.1 ∈ Aligned then 3 else 1) = 3 * k := by
        calc
          (∑ t ∈ (Q.erase q).attach,
              if t.1 ∈ Aligned then 3 else 1) =
              (Q.erase q).card + 2 * Aligned.card :=
            sum_attach_ite_three_one_eq_card_add_twice
              (by simpa [Aligned] using
                crossingEndpointAlignedTargets_subset A B₀ Q base q)
          _ = 3 * k := by
            rw [heraseCard]
            have haligned' : Aligned.card = k := by
              simpa [Aligned] using haligned
            rw [haligned']
            omega
      have hsumUpper :
          (∑ t ∈ (Q.erase q).attach, (cOther t).1.card) ≤
            3 * k := by
        calc
          (∑ t ∈ (Q.erase q).attach, (cOther t).1.card) ≤
              ∑ t ∈ (Q.erase q).attach,
                if t.1 ∈ Aligned then 3 else 1 := by
            apply Finset.sum_le_sum
            intro t _ht
            simpa [Aligned] using hcard t
          _ = 3 * k := hcapacitySum
      have hGoodLower : k - 3 ≤ Good.card := by
        rw [heraseCard] at hGoodBound
        omega
      exact ⟨hGoodLower, by simpa [Internal, Aligned, V] using hinternal⟩
  let T : Finset {n // n ∈ Q.erase q} := Good ∩ Internal
  have hUnionSub : Good ∪ Internal ⊆ (Q.erase q).attach := by
    exact Finset.union_subset hGoodSub (Finset.filter_subset _ _)
  have hUnionCard : (Good ∪ Internal).card ≤ k := by
    have := Finset.card_le_card hUnionSub
    simpa [heraseCard] using this
  have hcardIdentity := Finset.card_union_add_card_inter Good Internal
  have hTlower : k - 9 ≤ T.card := by
    rcases hcaseBounds with hcase | hcase
    · by_cases hkNine : 9 ≤ k
      · have hkOne : k - 1 = (k - 9) + 8 := by omega
        have hkThree : k - 3 = (k - 9) + 6 := by omega
        rw [hkOne] at hcase
        rw [hkThree] at hcase
        dsimp only [T]
        omega
      · omega
    · by_cases hkNine : 9 ≤ k
      · have hkThree : k - 3 = (k - 9) + 6 := by omega
        have hkSix : k - 6 = (k - 9) + 3 := by omega
        rw [hkThree] at hcase
        rw [hkSix] at hcase
        dsimp only [T]
        omega
      · omega
  have hTpair :
      (T : Set {n // n ∈ Q.erase q}).PairwiseDisjoint
        (fun t => (cOther t).1) := by
    intro t htT r hrT htr
    have htGood := (Finset.mem_inter.mp (Finset.mem_coe.mp htT)).1
    have hrGood := (Finset.mem_inter.mp (Finset.mem_coe.mp hrT)).1
    exact hGoodPair (Finset.mem_coe.mpr htGood)
      (Finset.mem_coe.mpr hrGood) htr
  have hTdata : ∀ t ∈ T,
      t.1 ∈ crossingEndpointAlignedTargets A B₀ Q base q ∧
      (cOther t).1 ∈ additiveSupportFamily A 3 t.1 ∧
      (cOther t).1.card = 3 ∧
      (cOther t).1.sum id = t.1 ∧
      (cOther t).1 ⊆ selectedBlockRemainderUnion P
        (crossingAtomEndpoints A B₀ q) ∧
      Disjoint ((cOther t).1 : Set ℕ) (selectedSet base) := by
    intro t htT
    have htInternal :=
      (Finset.mem_inter.mp htT).2
    have ht := (Finset.mem_filter.mp htInternal).2
    have htriple : (cOther t).1 ∈ additiveSupportFamily A 3 t.1 := by
      simpa [Aligned, ht.1] using hkind t
    have hsum : (cOther t).1.sum id = t.1 :=
      additiveSupportFamily_three_sum_eq_of_card_eq_three
        htriple ht.2.1
    exact ⟨by simpa [Aligned] using ht.1, htriple, ht.2.1,
      hsum, by simpa [V] using ht.2.2, hdisjoint t⟩
  let W : Finset ℕ := T.biUnion fun t => (cOther t).1
  have hWcard : W.card = 3 * T.card := by
    dsimp only [W]
    rw [Finset.card_biUnion hTpair]
    calc
      (∑ t ∈ T, (cOther t).1.card) = ∑ _t ∈ T, 3 := by
        apply Finset.sum_congr rfl
        intro t htT
        exact (hTdata t htT).2.2.1
      _ = 3 * T.card := by simp [Nat.mul_comm]
  have hWsub : W ⊆ V := by
    intro x hxW
    obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp hxW
    exact (hTdata t htT).2.2.2.2.1 hxt
  have hUupper : U.card ≤ 3 * k := by
    have hraw := finiteSupportChoiceUnion_card_le
      (crossingEndpointTripleObstructionFamily_cardAtMost
        (A := A) (B₀ := B₀)) cOther
    simpa [U, heraseCard] using hraw
  have hVupper : V.card ≤ 3 * k :=
    (Finset.card_le_card hVsub).trans hUupper
  have hcoverage : (V \ W).card ≤ 27 := by
    have hdiff : (V \ W).card = V.card - W.card :=
      Finset.card_sdiff_of_subset hWsub
    rw [hdiff]
    by_cases hkNine : 9 ≤ k
    · have hkPred : k = (k - 9) + 9 := by omega
      rw [hkPred] at hVupper
      omega
    · omega
  exact ⟨base, cOther, T, hqDestroy, hprivate,
    hTlower, hTpair, by simpa [V, W] using hcoverage, hTdata⟩

/-- The three anchor blocks of a late near-sharp certificate must migrate.
If all three endpoint blocks belonged to a prescribed finite index set `J`,
the trapped-support theorem would express a late target as a sum of points
from the fixed finite union of those blocks. -/
theorem minimalCrossingEndpointTripleCertificate_threeEndpoint_forces_freshAnchorBlock
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {q k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀)
    (hcert : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t)
    (hlocalized : ∀ t ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t ∧
      ∀ t' ∈ Q, t' ≠ t →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) t')
    (hk : 10 ≤ k)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 3)
    (J : Finset ℕ)
    (hQlate : ∀ t ∈ Q, (J.biUnion F).sum id + 1 ≤ t) :
    ∃ x ∈ crossingAtomEndpoints A B₀ q,
      blockIndex P x ∉ J := by
  classical
  by_contra hnone
  have hindexJ : ∀ x ∈ crossingAtomEndpoints A B₀ q,
      blockIndex P x ∈ J := by
    intro x hxEndpoint
    by_contra hxJ
    exact hnone ⟨x, hxEndpoint, hxJ⟩
  obtain ⟨base, cOther, T, _hqDestroy, _hprivate,
      hTlower, _hTpair, _hcoverage, hTdata⟩ :=
    minimalCrossingEndpointTripleCertificate_threeEndpoint_forces_disjointTrappedTripleSupports
      P hblockLower hQcross hcert hlocalized (by omega)
        hqQ hQcard hendpointCard
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    have : 1 ≤ k - 9 := by omega
    exact this.trans hTlower
  obtain ⟨t, htT⟩ := hTnonempty
  let Core : Finset ℕ := J.biUnion F
  have hVCore : selectedBlockRemainderUnion P
      (crossingAtomEndpoints A B₀ q) ⊆ Core := by
    intro y hyV
    dsimp only [selectedBlockRemainderUnion] at hyV
    obtain ⟨x, hxEndpoint, hyPiece⟩ := Finset.mem_biUnion.mp hyV
    apply Finset.mem_biUnion.mpr
    exact ⟨blockIndex P x, hindexJ x hxEndpoint,
      (Finset.mem_sdiff.mp hyPiece).1⟩
  have htData := hTdata t htT
  have hsupportCore : (cOther t).1 ⊆ Core :=
    htData.2.2.2.2.1.trans hVCore
  have hsumLe : (cOther t).1.sum id ≤ Core.sum id :=
    Finset.sum_le_sum_of_subset hsupportCore
  have htLate : Core.sum id + 1 ≤ t.1 := by
    simpa [Core] using hQlate t.1 (Finset.mem_of_mem_erase t.2)
  have hsumEq : (cOther t).1.sum id = t.1 :=
    htData.2.2.2.1
  omega

/-- Named package for the exact first-strict-size, three-endpoint branch. -/
def IsMinimalNearSharpThreeEndpointCertificate
    (A B₀ : Set ℕ) (F : ℕ → Finset ℕ)
    (k N : ℕ) (Q : Finset ℕ) (q : ℕ) : Prop :=
  q ∈ Q ∧
  Q.card = k + 1 ∧
  (∀ t ∈ Q, N ≤ t ∧
    ∀ E ∈ additiveSupportFamily A 2 t,
      ¬ Disjoint (E : Set ℕ) B₀ ∧
      ¬ (E : Set ℕ) ⊆ B₀) ∧
  (crossingAtomEndpoints A B₀ q).card = 3 ∧
  (∀ sel : BlockSelector F, ∃ t ∈ Q,
    DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
      (selectedSet sel) t) ∧
  ∀ t ∈ Q, ∃ sel : BlockSelector F,
    DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
      (selectedSet sel) t ∧
    ∀ t' ∈ Q, t' ≠ t →
      ¬ DestroysAt
        (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t'

/-- A block index which occurs as one of the three anchors in some late
near-sharp certificate. -/
noncomputable def IsNearSharpThreeAnchorBlockIndex
    (A B₀ : Set ℕ) {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition B₀ F) (k i : ℕ) : Prop :=
  ∃ N Q q x,
    IsMinimalNearSharpThreeEndpointCertificate A B₀ F k N Q q ∧
    x ∈ crossingAtomEndpoints A B₀ q ∧
    blockIndex P x = i

/-- If exact `k + 1` minimal certificates with a three-endpoint target occur
beyond every threshold, their anchor blocks form an infinite set. -/
theorem cofinalMinimalNearSharpThreeEndpointCertificates_force_infiniteAnchorBlocks
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card)
    (hk : 10 ≤ k)
    (hcofinal : ∀ N, ∃ Q q,
      IsMinimalNearSharpThreeEndpointCertificate A B₀ F k N Q q) :
    {i | IsNearSharpThreeAnchorBlockIndex A B₀ P k i}.Infinite := by
  classical
  let Moving : Set ℕ :=
    {i | IsNearSharpThreeAnchorBlockIndex A B₀ P k i}
  change Moving.Infinite
  apply Set.not_finite.mp
  intro hMovingFinite
  let J : Finset ℕ := hMovingFinite.toFinset
  let N : ℕ := (J.biUnion F).sum id + 1
  obtain ⟨Q, q, hnear⟩ := hcofinal N
  obtain ⟨hqQ, hQcard, hQdata, hendpointCard,
      hcert, hlocalized⟩ := hnear
  have hQcross : ∀ t ∈ Q,
      ∀ E ∈ additiveSupportFamily A 2 t,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀ := by
    intro t htQ
    exact (hQdata t htQ).2
  have hQlate : ∀ t ∈ Q, (J.biUnion F).sum id + 1 ≤ t := by
    intro t htQ
    simpa [N] using (hQdata t htQ).1
  obtain ⟨x, hxEndpoint, hxFresh⟩ :=
    minimalCrossingEndpointTripleCertificate_threeEndpoint_forces_freshAnchorBlock
      P hblockLower hQcross hcert hlocalized hk hqQ hQcard
        hendpointCard J hQlate
  let i : ℕ := blockIndex P x
  have hiMoving : i ∈ Moving := by
    change IsNearSharpThreeAnchorBlockIndex A B₀ P k i
    exact ⟨N, Q, q, x,
      ⟨hqQ, hQcard, hQdata, hendpointCard, hcert, hlocalized⟩,
      hxEndpoint, rfl⟩
  have hiJ : i ∈ J := hMovingFinite.mem_toFinset.mpr hiMoving
  exact hxFresh hiJ

/-- Infinitely many migrating near-sharp anchor blocks lift to an actual
infinite subset of `B₀`, choosing the endpoint witness carried by each block.
Distinct block indices force the chosen endpoints to be distinct. -/
theorem infiniteNearSharpThreeAnchorBlocks_give_infiniteEndpointSet
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hMoving :
      {i | IsNearSharpThreeAnchorBlockIndex A B₀ P k i}.Infinite) :
    ∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalNearSharpThreeEndpointCertificate
          A B₀ F k N Q q ∧
        x ∈ crossingAtomEndpoints A B₀ q := by
  classical
  let Moving : Set ℕ :=
    {i | IsNearSharpThreeAnchorBlockIndex A B₀ P k i}
  have hMoving' : Moving.Infinite := by
    simpa [Moving] using hMoving
  have hwitness : ∀ i, i ∈ Moving → ∃ x N Q q,
      x ∈ B₀ ∧
      blockIndex P x = i ∧
      IsMinimalNearSharpThreeEndpointCertificate
        A B₀ F k N Q q ∧
      x ∈ crossingAtomEndpoints A B₀ q := by
    intro i hiMoving
    change IsNearSharpThreeAnchorBlockIndex A B₀ P k i at hiMoving
    obtain ⟨N, Q, q, x, hnear, hxEndpoint, hindex⟩ := hiMoving
    have hxB₀ : x ∈ B₀ :=
      (mem_crossingAtomEndpoints_iff.mp hxEndpoint).2.1
    exact ⟨x, N, Q, q, hxB₀, hindex, hnear, hxEndpoint⟩
  choose point N Q q hpointB₀ hpointIndex hnear hpointEndpoint using
    hwitness
  let pick : ℕ → ℕ := fun i =>
    if hi : i ∈ Moving then point i hi else 0
  have hpickB₀ : ∀ i ∈ Moving, pick i ∈ B₀ := by
    intro i hi
    simpa [pick, hi] using hpointB₀ i hi
  have hpickIndex : ∀ i ∈ Moving, blockIndex P (pick i) = i := by
    intro i hi
    simpa [pick, hi] using hpointIndex i hi
  have hpickInj : Set.InjOn pick Moving := by
    intro i hi j hj hpickEq
    calc
      i = blockIndex P (pick i) := (hpickIndex i hi).symm
      _ = blockIndex P (pick j) := by rw [hpickEq]
      _ = j := hpickIndex j hj
  let L : Set ℕ := pick '' Moving
  have hL : L.Infinite := hMoving'.image hpickInj
  have hLB₀ : L ⊆ B₀ := by
    rintro x ⟨i, hiMoving, rfl⟩
    exact hpickB₀ i hiMoving
  refine ⟨L, hLB₀, hL, ?_⟩
  rintro x ⟨i, hiMoving, rfl⟩
  refine ⟨N i hiMoving, Q i hiMoving, q i hiMoving,
    hnear i hiMoving, ?_⟩
  simpa [pick, hiMoving] using hpointEndpoint i hiMoving

/-- The analogous two-endpoint consequence: at least half of the available
`k - 2` occupancy must be paid for by aligned other targets. -/
theorem nearSharp_refinedEndpointBound_two_forces_manyAligned
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {Q : Finset ℕ} {base : BlockSelector F} {q k : ℕ}
    (hqQ : q ∈ Q)
    (hQcard : Q.card ≤ k + 1)
    (hendpointCard :
      (crossingAtomEndpoints A B₀ q).card = 2)
    (hrefined :
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card +
          2 * (crossingEndpointAlignedTargets A B₀ Q base q).card) :
    k - 2 ≤
      2 * (crossingEndpointAlignedTargets A B₀ Q base q).card := by
  have heraseCard : (Q.erase q).card = Q.card - 1 :=
    Finset.card_erase_of_mem hqQ
  have heraseLe : (Q.erase q).card ≤ k := by
    rw [heraseCard]
    omega
  rw [hendpointCard] at hrefined
  omega

/-- A sharp private-destroyer certificate cannot recur arbitrarily late on
one fixed core of size at least four.  At most three basis elements have
arbitrarily late singleton order-three destruction, so every such core
contains a point with a personal cutoff; once all certificate targets lie
beyond that cutoff, a bijective sharp matching onto the core is impossible.
-/
theorem eventually_no_sharpPrivateCertificate_on_fixedCore
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k i : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ j, cell j ⊆ F j)
    (hcellCard : ∀ j, (cell j).card = k)
    (hk : 4 ≤ k) :
    ∃ N, ∀ {Q : Finset ℕ}
      (point : {q // q ∈ Q} → ℕ),
      (∀ q ∈ Q, N ≤ q) →
      cell i = Q.attach.image point →
      (∀ q, DestroysAt (additiveSupportFamily A 3)
        ({point q} : Set ℕ) q.1) → False := by
  classical
  let Bad : Set ℕ := {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
    DestroysAt (additiveSupportFamily A 3)
      ({a} : Set ℕ) n}
  have hBad : Bad.Finite :=
    finite_arbitrarilyLateSingletonDestruction_orderThree hbasis
  have hBadCard : hBad.toFinset.card ≤ 3 := by
    rw [← Set.ncard_eq_toFinset_card Bad hBad]
    simpa [Bad] using
      ncard_arbitrarilyLateSingletonDestruction_orderThree_le_three
        hbasis
  have hnsub : ¬ cell i ⊆ hBad.toFinset := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    rw [hcellCard i] at hcard
    omega
  obtain ⟨x, hxCell, hxBadFinset⟩ := Finset.not_subset.mp hnsub
  have hxB₀ : x ∈ B₀ :=
    (P.mem_iff x).2 ⟨i, hcore i hxCell⟩
  have hxA : x ∈ A := hB₀A hxB₀
  have hxNotBad : x ∉ Bad := by
    intro hxBad
    exact hxBadFinset (hBad.mem_toFinset.mpr hxBad)
  have hxNotLate : ¬ (∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3)
        ({x} : Set ℕ) n) := by
    intro hxLate
    exact hxNotBad ⟨hxA, hxLate⟩
  push Not at hxNotLate
  obtain ⟨N, hN⟩ := hxNotLate
  refine ⟨N, ?_⟩
  intro Q point hQlate hcellEq hdestroy
  have hxImage : x ∈ Q.attach.image point := by
    rw [← hcellEq]
    exact hxCell
  obtain ⟨q, _hqAttach, hqx⟩ := Finset.mem_image.mp hxImage
  have hxEq : point q = x := hqx
  exact hN q.1 (hQlate q.1 q.2) (by
    simpa [hxEq] using hdestroy q)

/-- The sharp branch must migrate beyond every prescribed finite collection
of cores.  Choose a personal singleton-destruction cutoff for one safe point
in each core in `J`, then ask for the endpoint certificate beyond the maximum
of those cutoffs.  Equality `Q.card = k` may still occur, but its matched
core cannot belong to `J`; otherwise its sharp singleton destroyers violate
that core's cutoff. -/
theorem finiteCrossingEndpointTripleCertificates_strict_or_freshRigidCore
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) (J : Finset ℕ) :
    ∀ N, ∃ Q : Finset ℕ,
      k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      (∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∧
      (k < Q.card ∨
        ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
          i ∉ J ∧
          cell i = Q.attach.image point ∧
          Function.Injective point ∧
          ∀ q,
            crossingAtomEndpoints A B₀ q.1 = {point q} ∧
            DestroysAt (additiveSupportFamily A 3)
              ({point q} : Set ℕ) q.1 ∧
            IsRigidPairSum A (point q) (q.1 - point q)) := by
  classical
  have hcutoffExists : ∀ i, ∃ Ni, ∀ {Q : Finset ℕ}
      (point : {q // q ∈ Q} → ℕ),
      (∀ q ∈ Q, Ni ≤ q) →
      cell i = Q.attach.image point →
      (∀ q, DestroysAt (additiveSupportFamily A 3)
        ({point q} : Set ℕ) q.1) → False := by
    intro i
    exact eventually_no_sharpPrivateCertificate_on_fixedCore
      hbasis hB₀A P hcore hcellCard hk
  choose cutoff hcutoff using hcutoffExists
  let T : ℕ := J.sup cutoff
  intro N
  obtain ⟨Q, hQlower, hQdata, hcert, hfork⟩ :=
    finiteCrossingEndpointTripleCertificates_strict_or_rigidCore
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
        P hcore hcellCard hk (max N T)
  have hQlate : ∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀ := by
    intro q hqQ
    exact ⟨(le_max_left N T).trans (hQdata q hqQ).1,
      (hQdata q hqQ).2⟩
  refine ⟨Q, hQlower, hQlate, hcert, ?_⟩
  rcases hfork with hstrict | ⟨point, i, hcellEq, hpointInj, hsharp⟩
  · exact Or.inl hstrict
  · right
    have hiJ : i ∉ J := by
      intro hiJ
      have hcutoffT : cutoff i ≤ T := by
        exact Finset.le_sup (f := cutoff) hiJ
      apply hcutoff i point
      · intro q hqQ
        exact hcutoffT.trans
          ((le_max_right N T).trans (hQdata q hqQ).1)
      · exact hcellEq
      · intro q
        exact (hsharp q).2.1
    exact ⟨point, i, hiJ, hcellEq, hpointInj, hsharp⟩

/-- Global dichotomy extracted from fresh-core migration.  Either strict
`Q.card > k` endpoint certificates exist beyond every threshold, or from
one threshold onward there are infinitely many distinct cores admitting a
sharp bijective matching by private rigid endpoint targets.  The latter is
the precise moving (rather than recurrent-at-one-core) obstruction left by
the sharp branch. -/
theorem strictCrossingEndpointCertificates_or_infiniteMovingRigidCores
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    (∀ N, ∃ Q : Finset ℕ,
      k < Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∨
      ∃ N₀, {i | ∃ Q : Finset ℕ,
        ∃ point : {q // q ∈ Q} → ℕ,
          (∀ q ∈ Q, N₀ ≤ q ∧
            ∀ E ∈ additiveSupportFamily A 2 q,
              ¬ Disjoint (E : Set ℕ) B₀ ∧
              ¬ (E : Set ℕ) ⊆ B₀) ∧
          cell i = Q.attach.image point ∧
          Function.Injective point ∧
          ∀ q,
            crossingAtomEndpoints A B₀ q.1 = {point q} ∧
            DestroysAt (additiveSupportFamily A 3)
              ({point q} : Set ℕ) q.1 ∧
            IsRigidPairSum A (point q)
              (q.1 - point q)}.Infinite := by
  classical
  let StrictAt : ℕ → Prop := fun N =>
    ∃ Q : Finset ℕ,
      k < Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel
  by_cases hstrict : ∀ N, StrictAt N
  · left
    simpa [StrictAt] using hstrict
  · right
    push Not at hstrict
    obtain ⟨N₀, hnoStrict⟩ := hstrict
    let Moving : Set ℕ := {i | ∃ Q : Finset ℕ,
      ∃ point : {q // q ∈ Q} → ℕ,
        (∀ q ∈ Q, N₀ ≤ q ∧
          ∀ E ∈ additiveSupportFamily A 2 q,
            ¬ Disjoint (E : Set ℕ) B₀ ∧
            ¬ (E : Set ℕ) ⊆ B₀) ∧
        cell i = Q.attach.image point ∧
        Function.Injective point ∧
        ∀ q,
          crossingAtomEndpoints A B₀ q.1 = {point q} ∧
          DestroysAt (additiveSupportFamily A 3)
            ({point q} : Set ℕ) q.1 ∧
          IsRigidPairSum A (point q) (q.1 - point q)}
    refine ⟨N₀, ?_⟩
    change Moving.Infinite
    apply Set.not_finite.mp
    intro hMovingFinite
    let J : Finset ℕ := hMovingFinite.toFinset
    obtain ⟨Q, _hQlower, hQdata, hcert, hfork⟩ :=
      finiteCrossingEndpointTripleCertificates_strict_or_freshRigidCore
        hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
          P hcore hcellCard hk J N₀
    rcases hfork with hQstrict |
        ⟨point, i, hiJ, hcellEq, hpointInj, hsharp⟩
    · exact hnoStrict ⟨Q, hQstrict, hQdata, hcert⟩
    · have hiMoving : i ∈ Moving := by
        exact ⟨Q, point, hQdata, hcellEq, hpointInj, hsharp⟩
      have hiJ' : i ∈ J :=
        hMovingFinite.mem_toFinset.mpr hiMoving
      exact hiJ hiJ'

/-- Named pointwise predicate for the moving sharp-core branch. -/
def IsSharpCrossingEndpointRigidCore
    (A B₀ : Set ℕ) (cell : ℕ → Finset ℕ)
    (N₀ i : ℕ) : Prop :=
  ∃ Q : Finset ℕ, ∃ point : {q // q ∈ Q} → ℕ,
    (∀ q ∈ Q, N₀ ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀) ∧
    cell i = Q.attach.image point ∧
    Function.Injective point ∧
    ∀ q,
      crossingAtomEndpoints A B₀ q.1 = {point q} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({point q} : Set ℕ) q.1 ∧
      IsRigidPairSum A (point q) (q.1 - point q)

/-- A genuinely strict cardinal-minimal endpoint certificate.  Target
localization records minimality and prevents this predicate from becoming
true merely by adjoining irrelevant targets.  The final scaled occupancy
bound records the quantitative consequence of those private selectors. -/
def HasMinimalStrictCrossingEndpointCertificate
    (A B₀ : Set ℕ) (F : ℕ → Finset ℕ)
    (k N : ℕ) : Prop :=
  ∃ Q : Finset ℕ,
    k < Q.card ∧
    (∀ q ∈ Q, N ≤ q ∧
      ∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀) ∧
    (∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3)
        (selectedSet sel) q ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
        selectedSet sel) ∧
    (∀ q ∈ Q, ∃ sel : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet sel) q') ∧
    (∀ q ∈ Q,
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        3 * (Q.erase q).card) ∧
    ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet base) q ∧
      (∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (crossingEndpointTripleObstructionFamily A B₀)
          (selectedSet base) q') ∧
      (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
        (Q.erase q).card +
          2 * (crossingEndpointAlignedTargets A B₀ Q base q).card

/-- Target-set-indexed form of `HasMinimalStrictCrossingEndpointCertificate`,
used to compare certificate cardinalities without losing their witnesses. -/
def IsMinimalStrictCrossingEndpointCertificateData
    (A B₀ : Set ℕ) (F : ℕ → Finset ℕ)
    (k N : ℕ) (Q : Finset ℕ) : Prop :=
  k < Q.card ∧
  (∀ q ∈ Q, N ≤ q ∧
    ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧
      ¬ (E : Set ℕ) ⊆ B₀) ∧
  (∀ sel : BlockSelector F, ∃ q ∈ Q,
    DestroysAt (additiveSupportFamily A 3)
      (selectedSet sel) q ∧
    (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
      selectedSet sel) ∧
  (∀ q ∈ Q, ∃ sel : BlockSelector F,
    DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
      (selectedSet sel) q ∧
    ∀ q' ∈ Q, q' ≠ q →
      ¬ DestroysAt
        (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) q') ∧
  (∀ q ∈ Q,
    (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
      3 * (Q.erase q).card) ∧
  ∀ q ∈ Q, ∃ base : BlockSelector F,
    DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
      (selectedSet base) q ∧
    (∀ q' ∈ Q, q' ≠ q →
      ¬ DestroysAt
        (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet base) q') ∧
    (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
      (Q.erase q).card +
        2 * (crossingEndpointAlignedTargets A B₀ Q base q).card

theorem hasMinimalStrictCrossingEndpointCertificate_iff_data
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k N : ℕ} :
    HasMinimalStrictCrossingEndpointCertificate A B₀ F k N ↔
      ∃ Q, IsMinimalStrictCrossingEndpointCertificateData
        A B₀ F k N Q := by
  rfl

/-- Lowering the target threshold preserves fixed-target-set certificate
data. -/
theorem IsMinimalStrictCrossingEndpointCertificateData.mono_threshold
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {k N N' : ℕ} {Q : Finset ℕ}
    (hNN' : N ≤ N')
    (h : IsMinimalStrictCrossingEndpointCertificateData
      A B₀ F k N' Q) :
    IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q := by
  rcases h with ⟨hstrict, hQdata, hcert, hlocalized,
    hscaled, hrefined⟩
  refine ⟨hstrict, ?_, hcert, hlocalized, hscaled, hrefined⟩
  intro q hqQ
  exact ⟨hNN'.trans (hQdata q hqQ).1, (hQdata q hqQ).2⟩

/-- Exact `k + 1` data with a three-endpoint target gives the named
near-sharp package. -/
theorem IsMinimalStrictCrossingEndpointCertificateData.to_nearSharpThree
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {k N : ℕ} {Q : Finset ℕ} {q : ℕ}
    (h : IsMinimalStrictCrossingEndpointCertificateData
      A B₀ F k N Q)
    (hqQ : q ∈ Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard : (crossingAtomEndpoints A B₀ q).card = 3) :
    IsMinimalNearSharpThreeEndpointCertificate A B₀ F k N Q q := by
  rcases h with ⟨_hstrict, hQdata, hcert, hlocalized,
    _hscaled, _hrefined⟩
  have hcertCombined : ∀ sel : BlockSelector F, ∃ t ∈ Q,
      DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
        (selectedSet sel) t := by
    intro sel
    obtain ⟨t, htQ, htDestroy, htEndpoints⟩ := hcert sel
    exact ⟨t, htQ,
      destroysAt_crossingEndpointTripleObstructionFamily_iff.mpr
        ⟨(hQdata t htQ).2, htDestroy, htEndpoints⟩⟩
  exact ⟨hqQ, hQcard, hQdata, hendpointCard,
    hcertCombined, hlocalized⟩

/-- Exhaustive refinement of the cofinal minimal-strict branch.  Either
minimal certificates of size at least `k + 2` recur cofinally, exact
`k + 1` certificates with a three-endpoint target recur cofinally, or after
one threshold an exact `k + 1` certificate exists at every later threshold
and all its endpoint families have size at most two. -/
theorem cofinalMinimalStrictCrossingEndpointCertificates_trichotomy
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hk : 5 ≤ k)
    (hcofinal : ∀ N,
      HasMinimalStrictCrossingEndpointCertificate A B₀ F k N) :
    (∀ N, ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      k + 2 ≤ Q.card) ∨
    (∀ N, ∃ Q q,
      IsMinimalNearSharpThreeEndpointCertificate A B₀ F k N Q q) ∨
    ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card ≤ 2 := by
  classical
  let LargeAt : ℕ → Prop := fun N =>
    ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      k + 2 ≤ Q.card
  by_cases hlarge : ∀ N, LargeAt N
  · left
    simpa [LargeAt] using hlarge
  · right
    push Not at hlarge
    obtain ⟨Nlarge, hnoLarge⟩ := hlarge
    let ThreeAt : ℕ → Prop := fun N =>
      ∃ Q q,
        IsMinimalNearSharpThreeEndpointCertificate A B₀ F k N Q q
    by_cases hthree : ∀ N, ThreeAt N
    · left
      simpa [ThreeAt] using hthree
    · right
      push Not at hthree
      obtain ⟨Nthree, hnoThree⟩ := hthree
      refine ⟨max Nlarge Nthree, ?_⟩
      intro N hN
      obtain ⟨Q, hdata⟩ :=
        hasMinimalStrictCrossingEndpointCertificate_iff_data.mp
          (hcofinal N)
      rcases hdata with ⟨hstrict, hQdata, hcert, hlocalized,
        hscaled, hrefined⟩
      have hdataFull : IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k N Q :=
        ⟨hstrict, hQdata, hcert, hlocalized, hscaled, hrefined⟩
      have hNlarge : Nlarge ≤ N := (le_max_left _ _).trans hN
      have hNthree : Nthree ≤ N := (le_max_right _ _).trans hN
      have hdataLarge : IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k Nlarge Q :=
        IsMinimalStrictCrossingEndpointCertificateData.mono_threshold
          hNlarge hdataFull
      have hnotLarge : ¬ k + 2 ≤ Q.card := by
        intro hcard
        exact hnoLarge ⟨Q, hdataLarge, hcard⟩
      have hQcard : Q.card = k + 1 := by omega
      have hendpointSmall : ∀ q ∈ Q,
          (crossingAtomEndpoints A B₀ q).card ≤ 2 := by
        intro q hqQ
        have hthreeUpper :
            (crossingAtomEndpoints A B₀ q).card ≤ 3 :=
          nearSharp_scaledEndpointBound_forces_endpointCard_le_three
            hk hqQ (by omega) (hscaled q hqQ)
        by_contra hnotTwo
        have hthreeCard :
            (crossingAtomEndpoints A B₀ q).card = 3 := by omega
        have hdataThree :
            IsMinimalStrictCrossingEndpointCertificateData
              A B₀ F k Nthree Q :=
          IsMinimalStrictCrossingEndpointCertificateData.mono_threshold
            hNthree hdataFull
        have hnear : IsMinimalNearSharpThreeEndpointCertificate
            A B₀ F k Nthree Q q :=
          hdataThree.to_nearSharpThree hqQ hQcard hthreeCard
        exact hnoThree ⟨Q, q, hnear⟩
      exact ⟨Q, hdataFull, hQcard, hendpointSmall⟩

/-- Named package for the exact first-strict-size two-endpoint branch.  The
private selector has to align with enough other endpoint families to pay for
the two selected block remainders. -/
def IsMinimalNearSharpDenseTwoEndpointCertificate
    (A B₀ : Set ℕ) (F : ℕ → Finset ℕ)
    (k N : ℕ) (Q : Finset ℕ) (q : ℕ)
    (base : BlockSelector F) : Prop :=
  IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
  Q.card = k + 1 ∧
  (∀ t ∈ Q, (crossingAtomEndpoints A B₀ t).card ≤ 2) ∧
  q ∈ Q ∧
  (crossingAtomEndpoints A B₀ q).card = 2 ∧
  DestroysAt (crossingEndpointTripleObstructionFamily A B₀)
    (selectedSet base) q ∧
  (∀ q' ∈ Q, q' ≠ q →
    ¬ DestroysAt
      (crossingEndpointTripleObstructionFamily A B₀)
      (selectedSet base) q') ∧
  k - 2 ≤
    2 * (crossingEndpointAlignedTargets A B₀ Q base q).card

/-- At scale at least five, dense two-endpoint alignment contains two
distinct other targets.  Consequently the endpoint families of three
distinct certificate targets (`q`, `t`, and `u`) fit simultaneously into
one block selector. -/
theorem IsMinimalNearSharpDenseTwoEndpointCertificate.exists_two_aligned
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    {k N : ℕ} {Q : Finset ℕ} {q : ℕ}
    {base : BlockSelector F}
    (hk : 5 ≤ k)
    (h : IsMinimalNearSharpDenseTwoEndpointCertificate
      A B₀ F k N Q q base) :
    ∃ t ∈ Q, ∃ u ∈ Q,
      t ≠ q ∧ u ≠ q ∧ t ≠ u ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ selectedSet base ∧
      (crossingAtomEndpoints A B₀ t : Set ℕ) ⊆ selectedSet base ∧
      (crossingAtomEndpoints A B₀ u : Set ℕ) ⊆ selectedSet base := by
  classical
  rcases h with ⟨_hdata, _hQcard, _hsmall, _hqQ, _hendpointCard,
    hdestroy, _hprivate, haligned⟩
  let Aligned : Finset ℕ :=
    crossingEndpointAlignedTargets A B₀ Q base q
  have hcard : 2 ≤ Aligned.card := by
    dsimp only [Aligned]
    omega
  obtain ⟨t, htAligned, u, huAligned, htu⟩ :=
    Finset.one_lt_card.mp (show 1 < Aligned.card by omega)
  have htFilter := Finset.mem_filter.mp htAligned
  have huFilter := Finset.mem_filter.mp huAligned
  have htErase := Finset.mem_erase.mp htFilter.1
  have huErase := Finset.mem_erase.mp huFilter.1
  have hqSelected :
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆ selectedSet base :=
    (destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
      hdestroy).2.2
  exact ⟨t, htErase.2, u, huErase.2, htErase.1, huErase.1,
    htu, hqSelected, htFilter.2, huFilter.2⟩

/-- The surviving exact-size, at-most-two-endpoint branch has a further
exhaustive split.  Either dense two-endpoint certificates occur beyond every
threshold, or after one threshold every endpoint family in the available
exact-size certificates has cardinality at most one. -/
theorem eventualMinimalNearSharpSmallEndpointCertificates_two_or_singleton
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hsmall : ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card ≤ 2) :
    (∀ N, ∃ Q q base,
      IsMinimalNearSharpDenseTwoEndpointCertificate
        A B₀ F k N Q q base) ∨
    ∃ N₁, ∀ N, N₁ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card ≤ 1 := by
  classical
  let TwoAt : ℕ → Prop := fun N =>
    ∃ Q q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      (∀ t ∈ Q, (crossingAtomEndpoints A B₀ t).card ≤ 2) ∧
      q ∈ Q ∧
      (crossingAtomEndpoints A B₀ q).card = 2
  by_cases htwo : ∀ N, TwoAt N
  · left
    intro N
    obtain ⟨Q, q, hdata, hQcard, hendpointSmall, hqQ,
      hendpointCard⟩ := htwo N
    obtain ⟨base, hdestroy, hprivate, hrefined⟩ :=
      hdata.2.2.2.2.2 q hqQ
    have haligned : k - 2 ≤
        2 * (crossingEndpointAlignedTargets A B₀ Q base q).card :=
      nearSharp_refinedEndpointBound_two_forces_manyAligned
        hqQ (by omega) hendpointCard hrefined
    exact ⟨Q, q, base, hdata, hQcard, hendpointSmall, hqQ, hendpointCard,
      hdestroy, hprivate, haligned⟩
  · right
    push Not at htwo
    obtain ⟨Ntwo, hnoTwo⟩ := htwo
    obtain ⟨Nsmall, hsmall⟩ := hsmall
    refine ⟨max Nsmall Ntwo, ?_⟩
    intro N hN
    have hNsmall : Nsmall ≤ N := (le_max_left _ _).trans hN
    have hNtwo : Ntwo ≤ N := (le_max_right _ _).trans hN
    obtain ⟨Q, hdata, hQcard, hendpointSmall⟩ :=
      hsmall N hNsmall
    refine ⟨Q, hdata, hQcard, ?_⟩
    intro q hqQ
    have hleTwo := hendpointSmall q hqQ
    by_contra hnotOne
    have hcardTwo :
        (crossingAtomEndpoints A B₀ q).card = 2 := by omega
    have hdataTwo :
        IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k Ntwo Q :=
      hdata.mono_threshold hNtwo
    exact hnoTwo
      ⟨Q, q, hdataTwo, hQcard, hendpointSmall, hqQ, hcardTwo⟩

/-- Once targets lie beyond the order-two basis threshold, the singleton
side of the preceding split is exact: every crossing endpoint family is
nonempty, hence its cardinality is one rather than zero. -/
theorem eventualMinimalNearSharpSingletonEndpointCertificates_exact
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hsingle : ∃ N₁, ∀ N, N₁ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card ≤ 1) :
    ∃ N₂, ∀ N, N₂ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card = 1 := by
  obtain ⟨Nbasis, hNbasis⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨Nsingle, hsingle⟩ := hsingle
  refine ⟨max Nbasis Nsingle, ?_⟩
  intro N hN
  have hNsingle : Nsingle ≤ N := (le_max_right _ _).trans hN
  have hNbasisN : Nbasis ≤ N := (le_max_left _ _).trans hN
  obtain ⟨Q, hdata, hQcard, hendpointLe⟩ :=
    hsingle N hNsingle
  refine ⟨Q, hdata, hQcard, ?_⟩
  intro q hqQ
  have hQdata := hdata.2.1 q hqQ
  obtain ⟨E, hER, _hEempty⟩ :=
    hNbasis q (hNbasisN.trans hQdata.1)
  obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
    exists_endpoints_of_crossingPairSupport hER
      (hQdata.2 E hER).1 (hQdata.2 E hER).2
  have hbLe : b ≤ q := by omega
  have hsub : q - b = c := by omega
  have hbEndpoint : b ∈ crossingAtomEndpoints A B₀ q :=
    mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩
  have hpositive : 0 < (crossingAtomEndpoints A B₀ q).card :=
    Finset.card_pos.mpr ⟨b, hbEndpoint⟩
  exact Nat.le_antisymm (hendpointLe q hqQ) (by omega)

/-- Near-sharp singleton endpoint certificates cover one whole exact core
with only one unit of slack.  The chosen endpoint image has cardinality `k`
or `k + 1`, contains a `k`-point core, and has at most one point outside
that core. -/
theorem nearSharpSingletonCrossingEndpointCertificate_forces_oneDefectCoreCover
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hQcard : Q.card = k + 1)
    (hendpointCard : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).card = 1)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
      (∀ q, crossingAtomEndpoints A B₀ q.1 = {point q}) ∧
      cell i ⊆ Q.attach.image point ∧
      ((Q.attach.image point).card = k ∨
        (Q.attach.image point).card = k + 1) ∧
      ((Q.attach.image point) \ cell i).card ≤ 1 := by
  classical
  have hchoose : ∀ q : {q // q ∈ Q}, ∃ b,
      crossingAtomEndpoints A B₀ q.1 = {b} := by
    intro q
    exact Finset.card_eq_one.mp (hendpointCard q.1 q.2)
  choose point hpoint using hchoose
  have hpointMem : ∀ q,
      point q ∈ crossingAtomEndpoints A B₀ q.1 := by
    intro q
    rw [hpoint q]
    simp
  obtain ⟨i, hcellSub⟩ :=
    exists_coveredCell_of_crossingEndpointCertificate
      hcore point hpointMem hcert
  let H : Finset ℕ := Q.attach.image point
  have hHlower : k ≤ H.card := by
    rw [← hcellCard i]
    exact Finset.card_le_card hcellSub
  have hHupper : H.card ≤ k + 1 := by
    calc
      H.card ≤ Q.attach.card := Finset.card_image_le
      _ = Q.card := by simp
      _ = k + 1 := hQcard
  have hHcard : H.card = k ∨ H.card = k + 1 := by omega
  have hdiffIdentity : (H \ cell i).card + (cell i).card = H.card :=
    Finset.card_sdiff_add_card_eq_card hcellSub
  have hdiff : (H \ cell i).card ≤ 1 := by
    rw [hcellCard i] at hdiffIdentity
    omega
  exact ⟨point, i, hpoint, hcellSub, hHcard, hdiff⟩

set_option maxHeartbeats 3000000 in
/-- The one-defect core cover still forces almost a whole core of genuine
singleton order-three destroyers.  Choose one target above each core point;
there is only one target left over, so deleting its endpoint leaves at least
`k - 1` core points with a unique target.  Avoiding a proposed triple support
and the single off-core endpoint then forces the certificate to use that
unique target. -/
theorem nearSharpSingletonCrossingEndpointTripleCertificate_forces_almostCoreDestroyers
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 5 ≤ k)
    (hQcard : Q.card = k + 1)
    (hendpointCard : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).card = 1)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) :
    ∃ (Good : Finset ℕ) (target : ℕ → ℕ) (i : ℕ),
      Good ⊆ cell i ∧
      k - 1 ≤ Good.card ∧
      ∀ x ∈ Good,
        target x ∈ Q ∧
        crossingAtomEndpoints A B₀ (target x) = {x} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) (target x) := by
  classical
  have hcontain : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
    intro sel hsel
    obtain ⟨q, hqQ, _hdestroy, hqSub⟩ := hcert sel hsel
    exact ⟨q, hqQ, hqSub⟩
  obtain ⟨point, i, hpoint, hcellSub, _hHcard, hoffCore⟩ :=
    nearSharpSingletonCrossingEndpointCertificate_forces_oneDefectCoreCover
      hcore hcellCard hQcard hendpointCard hcontain
  let H : Finset ℕ := Q.attach.image point
  have hpreimage : ∀ x : {x // x ∈ cell i},
      ∃ q : {q // q ∈ Q}, point q = x.1 := by
    intro x
    have hxH : x.1 ∈ H := hcellSub x.2
    obtain ⟨q, _hqAttach, hqx⟩ := Finset.mem_image.mp hxH
    exact ⟨q, hqx⟩
  choose targetCell htargetCellPoint using hpreimage
  let target : ℕ → ℕ := fun x =>
    if hx : x ∈ cell i then (targetCell ⟨x, hx⟩).1 else 0
  have htargetQ : ∀ x, x ∈ cell i → target x ∈ Q := by
    intro x hx
    simpa [target, hx] using (targetCell ⟨x, hx⟩).2
  have htargetPoint : ∀ x, ∀ hx : x ∈ cell i,
      point ⟨target x, htargetQ x hx⟩ = x := by
    intro x hx
    simpa [target, hx] using htargetCellPoint ⟨x, hx⟩
  let Used : Finset ℕ := (cell i).image target
  have htargetInj : Set.InjOn target (cell i : Set ℕ) := by
    intro x hxCell y hyCell hxy
    let qx : {q // q ∈ Q} := ⟨target x, htargetQ x hxCell⟩
    let qy : {q // q ∈ Q} := ⟨target y, htargetQ y hyCell⟩
    have hqxy : qx = qy := Subtype.ext hxy
    calc
      x = point qx := (htargetPoint x hxCell).symm
      _ = point qy := congrArg point hqxy
      _ = y := htargetPoint y hyCell
  have hUsedSub : Used ⊆ Q := by
    intro q hqUsed
    obtain ⟨x, hxCell, rfl⟩ := Finset.mem_image.mp hqUsed
    exact htargetQ x hxCell
  have hUsedCard : Used.card = k := by
    calc
      Used.card = (cell i).card := by
        exact Finset.card_image_iff.mpr htargetInj
      _ = k := hcellCard i
  have hUnusedIdentity : (Q \ Used).card + Used.card = Q.card :=
    Finset.card_sdiff_add_card_eq_card hUsedSub
  have hUnusedCard : (Q \ Used).card = 1 := by
    rw [hUsedCard, hQcard] at hUnusedIdentity
    omega
  obtain ⟨extra, hUnusedEq⟩ := Finset.card_eq_one.mp hUnusedCard
  have hextraUnused : extra ∈ Q \ Used := by
    rw [hUnusedEq]
    simp
  have hextraQ : extra ∈ Q := (Finset.mem_sdiff.mp hextraUnused).1
  let extraQ : {q // q ∈ Q} := ⟨extra, hextraQ⟩
  let Good : Finset ℕ := cell i \ {point extraQ}
  have hGoodSub : Good ⊆ cell i := Finset.sdiff_subset
  have hGoodCard : k - 1 ≤ Good.card := by
    change k - 1 ≤ (cell i \ {point extraQ}).card
    rw [Finset.sdiff_singleton_eq_erase, ← hcellCard i]
    exact Finset.pred_card_le_card_erase
  have hunique : ∀ x, x ∈ Good → ∀ r, ∀ hrQ : r ∈ Q,
      point ⟨r, hrQ⟩ = x → r = target x := by
    intro x hxGood r hrQ hpointRx
    have hxCell : x ∈ cell i := hGoodSub hxGood
    by_cases hrUsed : r ∈ Used
    · obtain ⟨y, hyCell, hyr⟩ := Finset.mem_image.mp hrUsed
      have hxy : x = y := by
        calc
          x = point ⟨r, hrQ⟩ := hpointRx.symm
          _ = point ⟨target y, htargetQ y hyCell⟩ := by
            apply congrArg point
            exact Subtype.ext hyr.symm
          _ = y := htargetPoint y hyCell
      rw [hxy]
      exact hyr.symm
    · have hrUnused : r ∈ Q \ Used :=
        Finset.mem_sdiff.mpr ⟨hrQ, hrUsed⟩
      have hrExtra : r = extra := by
        have : r ∈ ({extra} : Finset ℕ) := by
          rw [← hUnusedEq]
          exact hrUnused
        simpa using this
      have hxNotExtra : x ∉ ({point extraQ} : Finset ℕ) :=
        (Finset.mem_sdiff.mp hxGood).2
      apply False.elim
      apply hxNotExtra
      simp only [Finset.mem_singleton]
      subst r
      exact hpointRx.symm
  refine ⟨Good, target, i, hGoodSub, hGoodCard, ?_⟩
  intro x hxGood
  have hxCell : x ∈ cell i := hGoodSub hxGood
  have htargetEndpoint :
      crossingAtomEndpoints A B₀ (target x) = {x} := by
    let qx : {q // q ∈ Q} := ⟨target x, htargetQ x hxCell⟩
    calc
      crossingAtomEndpoints A B₀ (target x) = {point qx} := hpoint qx
      _ = {x} := by rw [htargetPoint x hxCell]
  refine ⟨htargetQ x hxCell, htargetEndpoint, ?_⟩
  intro G hGR hGsingleton
  have hxNotG : x ∉ G := by
    intro hxG
    exact Set.disjoint_left.mp hGsingleton
      (Finset.mem_coe.mpr hxG) (by simp)
  have hGcard : G.card ≤ 3 :=
    additiveSupportFamily_cardAtMost A 3 (target x) G hGR
  let Forbidden : Finset ℕ := G ∪ (H \ cell i)
  have hForbiddenCard : Forbidden.card ≤ 4 := by
    have hunion := Finset.card_union_le G (H \ cell i)
    have hoffCoreH : (H \ cell i).card ≤ 1 := by
      simpa [H] using hoffCore
    dsimp only [Forbidden]
    omega
  have houtside : ∀ j, ∃ y, y ∈ cell j ∧ y ∉ Forbidden := by
    intro j
    have hnsub : ¬ cell j ⊆ Forbidden := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      rw [hcellCard j] at hcard
      omega
    exact Finset.not_subset.mp hnsub
  choose other hotherCell hotherForbidden using houtside
  let value : ℕ → ℕ := fun j =>
    if hj : j = i then x else other j
  have hvalueCell : ∀ j, value j ∈ cell j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxCell
    · simpa [value, hj] using hotherCell j
  have hvalueG : ∀ j, value j ∉ G := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxNotG
    · intro hG
      apply hotherForbidden j
      apply Finset.mem_union_left
      simpa [value, hj] using hG
  let sel : BlockSelector F := fun j =>
    ⟨value j, hcore j (hvalueCell j)⟩
  have hselCore : ∀ j, (sel j).1 ∈ cell j := by
    intro j
    exact hvalueCell j
  have hselI : (sel i).1 = x := by simp [sel, value]
  have hGselected : Disjoint (G : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro z hzG hzSelected
    obtain ⟨j, hj⟩ := hzSelected
    apply hvalueG j
    have : value j = z := hj
    exact this ▸ Finset.mem_coe.mp hzG
  have hHselected : ∀ z, z ∈ H → z ∈ selectedSet sel → z = x := by
    intro z hzH hzSelected
    obtain ⟨j, hj⟩ := hzSelected
    by_cases hji : j = i
    · subst j
      exact hj.symm.trans hselI
    · have hzCellj : z ∈ cell j := by
        rw [← hj]
        exact hvalueCell j
      have hzNotCelli : z ∉ cell i := by
        intro hzCelli
        exact Finset.disjoint_left.mp
          (P.disjoint (fun hij => hji hij.symm))
          (hcore i hzCelli) (hcore j hzCellj)
      have hzOff : z ∈ H \ cell i :=
        Finset.mem_sdiff.mpr ⟨hzH, hzNotCelli⟩
      apply False.elim
      apply hotherForbidden j
      apply Finset.mem_union_right
      have hotherEq : other j = z := by
        simpa [sel, value, hji] using hj
      exact hotherEq ▸ hzOff
  obtain ⟨r, hrQ, hrDestroy, hrSub⟩ := hcert sel hselCore
  let rQ : {r // r ∈ Q} := ⟨r, hrQ⟩
  have hpointEndpoint :
      point rQ ∈ crossingAtomEndpoints A B₀ r := by
    rw [hpoint rQ]
    simp
  have hpointSelected : point rQ ∈ selectedSet sel :=
    hrSub (Finset.mem_coe.mpr hpointEndpoint)
  have hpointH : point rQ ∈ H :=
    Finset.mem_image.mpr ⟨rQ, Finset.mem_attach Q rQ, rfl⟩
  have hpointEq : point rQ = x :=
    hHselected (point rQ) hpointH hpointSelected
  have hrTarget : r = target x := hunique x hxGood r hrQ hpointEq
  have htargetDestroy : DestroysAt (additiveSupportFamily A 3)
      (selectedSet sel) (target x) := by
    simpa [hrTarget] using hrDestroy
  exact (htargetDestroy G hGR) hGselected

/-- A fixed core cannot carry arbitrarily late near-sharp singleton
certificates with `k - 1` singleton destroyers.  Globally, at most three
basis elements admit arbitrarily late singleton order-three destruction;
an almost-full core of size at least five contains a safe point, and the
maximum of the finitely many safe-point cutoffs rules out the certificate. -/
theorem eventually_no_nearSharpSingletonAlmostCoreDestroyers_on_fixedCore
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {k i : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ j, cell j ⊆ F j)
    (hk : 5 ≤ k) :
    ∃ N, ∀ {Q Good : Finset ℕ} (target : ℕ → ℕ),
      (∀ q ∈ Q, N ≤ q) →
      Good ⊆ cell i →
      k - 1 ≤ Good.card →
      (∀ x ∈ Good,
        target x ∈ Q ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) (target x)) → False := by
  classical
  let Bad : Set ℕ := {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
    DestroysAt (additiveSupportFamily A 3)
      ({a} : Set ℕ) n}
  have hBad : Bad.Finite :=
    finite_arbitrarilyLateSingletonDestruction_orderThree hbasis
  have hBadCard : hBad.toFinset.card ≤ 3 := by
    rw [← Set.ncard_eq_toFinset_card Bad hBad]
    simpa [Bad] using
      ncard_arbitrarilyLateSingletonDestruction_orderThree_le_three
        hbasis
  let Safe : Finset ℕ := cell i \ hBad.toFinset
  have hsafeCutoffExists : ∀ x : {x // x ∈ Safe}, ∃ N,
      ∀ n, N ≤ n →
        ¬ DestroysAt (additiveSupportFamily A 3)
          ({x.1} : Set ℕ) n := by
    intro x
    have hxCell : x.1 ∈ cell i := (Finset.mem_sdiff.mp x.2).1
    have hxB₀ : x.1 ∈ B₀ :=
      (P.mem_iff x.1).2 ⟨i, hcore i hxCell⟩
    have hxA : x.1 ∈ A := hB₀A hxB₀
    have hxNotBad : x.1 ∉ Bad := by
      intro hxBad
      exact (Finset.mem_sdiff.mp x.2).2 (hBad.mem_toFinset.mpr hxBad)
    have hxNotLate : ¬ (∀ N, ∃ n, N ≤ n ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x.1} : Set ℕ) n) := by
      intro hxLate
      exact hxNotBad ⟨hxA, hxLate⟩
    push Not at hxNotLate
    exact hxNotLate
  choose cutoffSafe hcutoffSafe using hsafeCutoffExists
  let cutoff : ℕ → ℕ := fun x =>
    if hx : x ∈ Safe then cutoffSafe ⟨x, hx⟩ else 0
  let N : ℕ := Safe.sup cutoff
  refine ⟨N, ?_⟩
  intro Q Good target hQlate hGoodSub hGoodCard hdestroy
  have hnotBadSub : ¬ Good ⊆ hBad.toFinset := by
    intro hsub
    have hcard := Finset.card_le_card hsub
    omega
  obtain ⟨x, hxGood, hxNotBad⟩ := Finset.not_subset.mp hnotBadSub
  have hxCell : x ∈ cell i := hGoodSub hxGood
  have hxSafe : x ∈ Safe :=
    Finset.mem_sdiff.mpr ⟨hxCell, hxNotBad⟩
  have hcutoffN : cutoff x ≤ N :=
    Finset.le_sup (f := cutoff) hxSafe
  have hcutoffTarget : cutoffSafe ⟨x, hxSafe⟩ ≤ target x := by
    have hcutoffEq : cutoff x = cutoffSafe ⟨x, hxSafe⟩ := by
      simp [cutoff, hxSafe]
    rw [← hcutoffEq]
    exact hcutoffN.trans (hQlate (target x) (hdestroy x hxGood).1)
  exact hcutoffSafe ⟨x, hxSafe⟩ (target x) hcutoffTarget
    (hdestroy x hxGood).2

/-- Named core-indexed package produced by a near-sharp singleton
certificate. -/
def IsNearSharpSingletonAlmostCoreCertificate
    (A B₀ : Set ℕ) (F cell : ℕ → Finset ℕ)
    (k N i : ℕ) : Prop :=
  ∃ Q Good : Finset ℕ, ∃ target : ℕ → ℕ,
    IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
    Q.card = k + 1 ∧
    (∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card = 1) ∧
    Good ⊆ cell i ∧
    k - 1 ≤ Good.card ∧
    ∀ x ∈ Good,
      target x ∈ Q ∧
      crossingAtomEndpoints A B₀ (target x) = {x} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({x} : Set ℕ) (target x)

/-- Every exact near-sharp singleton certificate supplies an almost-full
destroyer set in one partition core. -/
theorem minimalNearSharpSingletonCertificate_gives_almostCoreCertificate
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {Q : Finset ℕ} {k N : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 5 ≤ k)
    (hdata : IsMinimalStrictCrossingEndpointCertificateData
      A B₀ F k N Q)
    (hQcard : Q.card = k + 1)
    (hendpointCard : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).card = 1) :
    ∃ i, IsNearSharpSingletonAlmostCoreCertificate
      A B₀ F cell k N i := by
  rcases hdata with ⟨hstrict, hQdata, hcert, hlocalized,
    hscaled, hrefined⟩
  obtain ⟨Good, target, i, hGoodSub, hGoodCard, hGoodData⟩ :=
    nearSharpSingletonCrossingEndpointTripleCertificate_forces_almostCoreDestroyers
      P hcore hcellCard hk hQcard hendpointCard
        (fun sel _hsel => hcert sel)
  refine ⟨i, Q, Good, target, ?_, hQcard, hendpointCard,
    hGoodSub, hGoodCard, hGoodData⟩
  exact ⟨hstrict, hQdata, hcert, hlocalized, hscaled, hrefined⟩

/-- Cofinal exact singleton certificates must migrate through infinitely many
partition cores.  Otherwise take the maximum fixed-core cutoff over their
finite set of possible cores and request one later certificate. -/
theorem cofinalMinimalNearSharpSingletonCertificates_force_infiniteCores
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 5 ≤ k)
    (hcofinal : ∀ N, ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card = 1) :
    {i | ∃ N, IsNearSharpSingletonAlmostCoreCertificate
      A B₀ F cell k N i}.Infinite := by
  classical
  let Moving : Set ℕ := {i | ∃ N,
    IsNearSharpSingletonAlmostCoreCertificate A B₀ F cell k N i}
  change Moving.Infinite
  apply Set.not_finite.mp
  intro hMovingFinite
  let J : Finset ℕ := hMovingFinite.toFinset
  have hcutoffExists : ∀ i, ∃ Ni, ∀ {Q Good : Finset ℕ}
      (target : ℕ → ℕ),
      (∀ q ∈ Q, Ni ≤ q) →
      Good ⊆ cell i →
      k - 1 ≤ Good.card →
      (∀ x ∈ Good,
        target x ∈ Q ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) (target x)) → False := by
    intro i
    exact eventually_no_nearSharpSingletonAlmostCoreDestroyers_on_fixedCore
      hbasis hB₀A P hcore hk
  choose cutoff hcutoff using hcutoffExists
  let N : ℕ := J.sup cutoff
  obtain ⟨Q, hdata, hQcard, hendpointCard⟩ := hcofinal N
  obtain ⟨i, hcoreCert⟩ :=
    minimalNearSharpSingletonCertificate_gives_almostCoreCertificate
      P hcore hcellCard hk hdata hQcard hendpointCard
  have hiMoving : i ∈ Moving := ⟨N, hcoreCert⟩
  have hiJ : i ∈ J := hMovingFinite.mem_toFinset.mpr hiMoving
  have hcutoffN : cutoff i ≤ N := Finset.le_sup (f := cutoff) hiJ
  obtain ⟨Q', Good, target, hdata', _hQcard', _hendpointCard',
    hGoodSub, hGoodCard, hGoodData⟩ := hcoreCert
  apply hcutoff i target
  · intro q hqQ
    exact hcutoffN.trans (hdata'.2.1 q hqQ).1
  · exact hGoodSub
  · exact hGoodCard
  · intro x hxGood
    exact ⟨(hGoodData x hxGood).1, (hGoodData x hxGood).2.2⟩

/-- Migrating almost-full singleton cores lift to an actual infinite subset
of `B₀`, one certified singleton destroyer chosen from each core. -/
theorem infiniteNearSharpSingletonCores_give_infiniteEndpointSet
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hk : 5 ≤ k)
    (hMoving : {i | ∃ N,
      IsNearSharpSingletonAlmostCoreCertificate
        A B₀ F cell k N i}.Infinite) :
    ∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k N Q ∧
        Q.card = k + 1 ∧
        q ∈ Q ∧
        crossingAtomEndpoints A B₀ q = {x} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) q := by
  classical
  let Moving : Set ℕ := {i | ∃ N,
    IsNearSharpSingletonAlmostCoreCertificate A B₀ F cell k N i}
  have hMoving' : Moving.Infinite := by
    simpa [Moving] using hMoving
  have hwitness : ∀ i, i ∈ Moving → ∃ x N Q q,
      x ∈ B₀ ∧
      blockIndex P x = i ∧
      IsMinimalStrictCrossingEndpointCertificateData
        A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      q ∈ Q ∧
      crossingAtomEndpoints A B₀ q = {x} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({x} : Set ℕ) q := by
    intro i hiMoving
    change ∃ N, IsNearSharpSingletonAlmostCoreCertificate
      A B₀ F cell k N i at hiMoving
    obtain ⟨N, Q, Good, target, hdata, hQcard,
      _hendpointCard, hGoodSub, hGoodCard, hGoodData⟩ := hiMoving
    have hGoodNonempty : Good.Nonempty := by
      apply Finset.card_pos.mp
      have : 1 ≤ k - 1 := by omega
      exact this.trans hGoodCard
    obtain ⟨x, hxGood⟩ := hGoodNonempty
    have hxCell : x ∈ cell i := hGoodSub hxGood
    have hxF : x ∈ F i := hcore i hxCell
    have hxB₀ : x ∈ B₀ := (P.mem_iff x).2 ⟨i, hxF⟩
    have hxIndex : blockIndex P x = i := P.blockIndex_eq_of_mem hxF
    exact ⟨x, N, Q, target x, hxB₀, hxIndex, hdata, hQcard,
      (hGoodData x hxGood).1, (hGoodData x hxGood).2.1,
      (hGoodData x hxGood).2.2⟩
  choose point N Q q hpointB₀ hpointIndex hdata hQcard hqQ
    hendpoint hdestroy using hwitness
  let pick : ℕ → ℕ := fun i =>
    if hi : i ∈ Moving then point i hi else 0
  have hpickB₀ : ∀ i ∈ Moving, pick i ∈ B₀ := by
    intro i hi
    simpa [pick, hi] using hpointB₀ i hi
  have hpickIndex : ∀ i ∈ Moving, blockIndex P (pick i) = i := by
    intro i hi
    simpa [pick, hi] using hpointIndex i hi
  have hpickInj : Set.InjOn pick Moving := by
    intro i hi j hj hpickEq
    calc
      i = blockIndex P (pick i) := (hpickIndex i hi).symm
      _ = blockIndex P (pick j) := by rw [hpickEq]
      _ = j := hpickIndex j hj
  let L : Set ℕ := pick '' Moving
  have hL : L.Infinite := hMoving'.image hpickInj
  have hLB₀ : L ⊆ B₀ := by
    rintro x ⟨i, hiMoving, rfl⟩
    exact hpickB₀ i hiMoving
  refine ⟨L, hLB₀, hL, ?_⟩
  rintro x ⟨i, hiMoving, rfl⟩
  refine ⟨N i hiMoving, Q i hiMoving, q i hiMoving,
    hdata i hiMoving, hQcard i hiMoving, hqQ i hiMoving, ?_, ?_⟩
  · simpa [pick, hiMoving] using hendpoint i hiMoving
  · simpa [pick, hiMoving] using hdestroy i hiMoving

/-- Eventual exact singleton certificates therefore already yield an actual
infinite subset of `B₀` carrying singleton order-three destroyers. -/
theorem eventualMinimalNearSharpSingletonCertificates_give_infiniteEndpointSet
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 5 ≤ k)
    (hsingle : ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card = 1) :
    ∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k N Q ∧
        Q.card = k + 1 ∧
        q ∈ Q ∧
        crossingAtomEndpoints A B₀ q = {x} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) q := by
  obtain ⟨N₀, hsingle⟩ := hsingle
  have hcofinal : ∀ N, ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card = 1 := by
    intro N
    obtain ⟨Q, hdata, hQcard, hendpointCard⟩ :=
      hsingle (max N N₀) (le_max_right _ _)
    have hdataN : IsMinimalStrictCrossingEndpointCertificateData
        A B₀ F k N Q :=
      hdata.mono_threshold (le_max_left _ _)
    exact ⟨Q, hdataN, hQcard, hendpointCard⟩
  have hMoving :=
    cofinalMinimalNearSharpSingletonCertificates_force_infiniteCores
      hbasis hB₀A P hcore hcellCard hk hcofinal
  exact infiniteNearSharpSingletonCores_give_infiniteEndpointSet
    P hcore hk hMoving

/-- Meaningful minimal-certificate dichotomy.  Either cardinal-minimal
crossing certificates are strictly larger than `k` beyond every threshold,
or sharp equality certificates migrate through infinitely many distinct
rigid cores.  Unlike the earlier nonminimal version, the strict side cannot
be manufactured by amplification. -/
theorem minimalStrictCrossingEndpointCertificates_or_infiniteMovingRigidCores
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    (∀ N, HasMinimalStrictCrossingEndpointCertificate
      A B₀ F k N) ∨
      ∃ N₀, {i | IsSharpCrossingEndpointRigidCore
        A B₀ cell N₀ i}.Infinite := by
  classical
  by_cases hstrict : ∀ N,
      HasMinimalStrictCrossingEndpointCertificate A B₀ F k N
  · exact Or.inl hstrict
  · right
    push Not at hstrict
    obtain ⟨N₀, hnoStrict⟩ := hstrict
    let Moving : Set ℕ := {i | IsSharpCrossingEndpointRigidCore
      A B₀ cell N₀ i}
    refine ⟨N₀, ?_⟩
    change Moving.Infinite
    apply Set.not_finite.mp
    intro hMovingFinite
    let J : Finset ℕ := hMovingFinite.toFinset
    have hcutoffExists : ∀ i, ∃ Ni, ∀ {Q : Finset ℕ}
        (point : {q // q ∈ Q} → ℕ),
        (∀ q ∈ Q, Ni ≤ q) →
        cell i = Q.attach.image point →
        (∀ q, DestroysAt (additiveSupportFamily A 3)
          ({point q} : Set ℕ) q.1) → False := by
      intro i
      exact eventually_no_sharpPrivateCertificate_on_fixedCore
        hbasis hB₀A P hcore hcellCard hk
    choose cutoff hcutoff using hcutoffExists
    let T : ℕ := J.sup cutoff
    obtain ⟨Q, _hQlower, hQdata, hcert, hlocalized, hfork⟩ :=
      finiteMinimalCrossingEndpointTripleCertificates_strict_or_rigidCore
        hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
          P hcore hcellCard hk (max N₀ T)
    have hQdata₀ : ∀ q ∈ Q, N₀ ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀ := by
      intro q hqQ
      exact ⟨(le_max_left N₀ T).trans (hQdata q hqQ).1,
        (hQdata q hqQ).2⟩
    rcases hfork with hQstrict |
        ⟨point, i, hcellEq, hpointInj, hsharp⟩
    · apply hnoStrict
      have hblockLower : ∀ i, k ≤ (F i).card := by
        intro i
        rw [← hcellCard i]
        exact Finset.card_le_card (hcore i)
      have hcertCombined : ∀ sel : BlockSelector F, ∃ q ∈ Q,
          DestroysAt
            (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet sel) q := by
        intro sel
        obtain ⟨q, hqQ, hqDestroy, hqEndpoints⟩ := hcert sel
        exact ⟨q, hqQ,
          destroysAt_crossingEndpointTripleObstructionFamily_iff.mpr
            ⟨(hQdata q hqQ).2, hqDestroy, hqEndpoints⟩⟩
      have hscaled : ∀ q ∈ Q,
          (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
            3 * (Q.erase q).card :=
        minimalCrossingEndpointTripleCertificate_forces_scaledEndpointBound
          P hblockLower (fun q hqQ => (hQdata q hqQ).2)
            hcertCombined hlocalized
      have hrefined : ∀ q ∈ Q, ∃ base : BlockSelector F,
          DestroysAt
            (crossingEndpointTripleObstructionFamily A B₀)
            (selectedSet base) q ∧
          (∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt
              (crossingEndpointTripleObstructionFamily A B₀)
              (selectedSet base) q') ∧
          (k - 1) * (crossingAtomEndpoints A B₀ q).card ≤
            (Q.erase q).card +
              2 * (crossingEndpointAlignedTargets
                A B₀ Q base q).card :=
        minimalCrossingEndpointTripleCertificate_forces_refinedEndpointBound
          P hblockLower (fun q hqQ => (hQdata q hqQ).2)
            hcertCombined hlocalized
      exact ⟨Q, hQstrict, hQdata₀, hcert, hlocalized,
        hscaled, hrefined⟩
    · have hiMoving : i ∈ Moving := by
        exact ⟨Q, point, hQdata₀, hcellEq, hpointInj, hsharp⟩
      have hiJ : i ∈ J :=
        hMovingFinite.mem_toFinset.mpr hiMoving
      have hcutoffT : cutoff i ≤ T :=
        Finset.le_sup (f := cutoff) hiJ
      apply hcutoff i point
      · intro q hqQ
        exact hcutoffT.trans
          ((le_max_right N₀ T).trans (hQdata q hqQ).1)
      · exact hcellEq
      · intro q
        exact (hsharp q).2.1

/-- Infinitely many moving sharp cores yield an actual infinite subset of
the repaired reservoir consisting of distinct private rigid endpoints.
Choose one point from each core.  Block disjointness makes this choice
injective, while the sharp bijection supplies the matched late target and
its singleton destruction/rigid-pair data. -/
theorem infiniteMovingRigidCores_give_infiniteRigidEndpointSet
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ}
    {k N₀ : ℕ}
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k)
    (hMoving : {i | IsSharpCrossingEndpointRigidCore
      A B₀ cell N₀ i}.Infinite) :
    ∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ b ∈ L, ∃ q,
        N₀ ≤ q ∧
        (∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
        crossingAtomEndpoints A B₀ q = {b} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({b} : Set ℕ) q ∧
        IsRigidPairSum A b (q - b) := by
  classical
  have hcellNonempty : ∀ i, (cell i).Nonempty := by
    intro i
    apply Finset.card_pos.mp
    rw [hcellCard i]
    omega
  choose pick hpick using hcellNonempty
  let Moving : Set ℕ := {i | IsSharpCrossingEndpointRigidCore
    A B₀ cell N₀ i}
  have hpickInj : Set.InjOn pick Moving := by
    intro i hiI j hjI hij
    by_contra hne
    have hipickF : pick i ∈ F i := hcore i (hpick i)
    have hjpickF : pick j ∈ F j := hcore j (hpick j)
    exact Finset.disjoint_left.mp (P.disjoint hne)
      hipickF (hij ▸ hjpickF)
  let L : Set ℕ := pick '' Moving
  have hMoving' : Moving.Infinite := by
    simpa [Moving] using hMoving
  have hL : L.Infinite := hMoving'.image hpickInj
  have hLB₀ : L ⊆ B₀ := by
    rintro b ⟨i, hiMoving, rfl⟩
    exact (P.mem_iff (pick i)).2 ⟨i, hcore i (hpick i)⟩
  refine ⟨L, hLB₀, hL, ?_⟩
  rintro b ⟨i, hiMoving, rfl⟩
  change IsSharpCrossingEndpointRigidCore
    A B₀ cell N₀ i at hiMoving
  obtain ⟨Q, point, hQdata, hcellEq, _hpointInj, hsharp⟩ :=
    hiMoving
  have hpickImage : pick i ∈ Q.attach.image point := by
    rw [← hcellEq]
    exact hpick i
  obtain ⟨q, _hqAttach, hpointEq⟩ :=
    Finset.mem_image.mp hpickImage
  refine ⟨q.1, (hQdata q.1 q.2).1, (hQdata q.1 q.2).2, ?_⟩
  have hqSharp := hsharp q
  simpa [hpointEq] using hqSharp

/-- Endpoint-set form of the cardinal-minimal migration dichotomy.  The
strict alternative retains target localization, while failure of that
alternative produces an actual infinite subset of `B₀` whose elements are
private endpoints of late rigid crossing pairs. -/
theorem minimalStrictCrossingEndpointCertificates_or_infiniteMovingRigidEndpoints
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    (∀ N, HasMinimalStrictCrossingEndpointCertificate
      A B₀ F k N) ∨
      ∃ N₀ L, L ⊆ B₀ ∧ L.Infinite ∧
        ∀ b ∈ L, ∃ q,
          N₀ ≤ q ∧
          (∀ E ∈ additiveSupportFamily A 2 q,
            ¬ Disjoint (E : Set ℕ) B₀ ∧
            ¬ (E : Set ℕ) ⊆ B₀) ∧
          crossingAtomEndpoints A B₀ q = {b} ∧
          DestroysAt (additiveSupportFamily A 3)
            ({b} : Set ℕ) q ∧
          IsRigidPairSum A b (q - b) := by
  obtain hstrict | ⟨N₀, hMoving⟩ :=
    minimalStrictCrossingEndpointCertificates_or_infiniteMovingRigidCores
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
        P hcore hcellCard hk
  · exact Or.inl hstrict
  · right
    obtain ⟨L, hLB₀, hL, hdata⟩ :=
      infiniteMovingRigidCores_give_infiniteRigidEndpointSet
        P hcore hcellCard hk hMoving
    exact ⟨N₀, L, hLB₀, hL, hdata⟩

/-- Four-way endpoint form of the full cardinal-minimal certificate analysis.
Under the counterexample hypothesis, either genuinely larger minimal
certificates recur, exact first-strict-size certificates eventually have only
one- or two-endpoint targets, or one of the two migration mechanisms already
produces an actual infinite subset of `B₀`.  Thus only the first two
alternatives remain finite-certificate branches. -/
theorem minimalCrossingEndpointCertificates_four_way
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 10 ≤ k) :
    (∀ N, ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      k + 2 ≤ Q.card) ∨
    (∃ N₀, ∀ N, N₀ ≤ N → ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      Q.card = k + 1 ∧
      ∀ q ∈ Q, (crossingAtomEndpoints A B₀ q).card ≤ 2) ∨
    (∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalNearSharpThreeEndpointCertificate
          A B₀ F k N Q q ∧
        x ∈ crossingAtomEndpoints A B₀ q) ∨
    ∃ N₀ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ b ∈ L, ∃ q,
        N₀ ≤ q ∧
        (∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
        crossingAtomEndpoints A B₀ q = {b} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({b} : Set ℕ) q ∧
        IsRigidPairSum A b (q - b) := by
  obtain hstrict | hrigid :=
    minimalStrictCrossingEndpointCertificates_or_infiniteMovingRigidEndpoints
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
        P hcore hcellCard (by omega)
  · obtain hlarge | hnear | hsmall :=
      cofinalMinimalStrictCrossingEndpointCertificates_trichotomy
        (by omega) hstrict
    · exact Or.inl hlarge
    · have hblockLower : ∀ i, k ≤ (F i).card := by
        intro i
        rw [← hcellCard i]
        exact Finset.card_le_card (hcore i)
      have hMoving :=
        cofinalMinimalNearSharpThreeEndpointCertificates_force_infiniteAnchorBlocks
          P hblockLower hk hnear
      obtain ⟨L, hLB₀, hL, hdata⟩ :=
        infiniteNearSharpThreeAnchorBlocks_give_infiniteEndpointSet
          P hMoving
      exact Or.inr (Or.inr (Or.inl ⟨L, hLB₀, hL, hdata⟩))
    · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr (Or.inr hrigid))

/-- Refined global classification after eliminating the eventual singleton
finite-certificate branch.  Only cofinal oversized certificates and cofinal
dense two-endpoint certificates remain as finite obstructions; all other
alternatives already carry an actual infinite subset of `B₀`. -/
theorem minimalCrossingEndpointCertificates_two_finite_branches_or_infiniteEndpoints
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 10 ≤ k) :
    (∀ N, ∃ Q,
      IsMinimalStrictCrossingEndpointCertificateData A B₀ F k N Q ∧
      k + 2 ≤ Q.card) ∨
    (∀ N, ∃ Q q base,
      IsMinimalNearSharpDenseTwoEndpointCertificate
        A B₀ F k N Q q base) ∨
    (∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalNearSharpThreeEndpointCertificate
          A B₀ F k N Q q ∧
        x ∈ crossingAtomEndpoints A B₀ q) ∨
    (∃ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ x ∈ L, ∃ N Q q,
        IsMinimalStrictCrossingEndpointCertificateData
          A B₀ F k N Q ∧
        Q.card = k + 1 ∧
        q ∈ Q ∧
        crossingAtomEndpoints A B₀ q = {x} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({x} : Set ℕ) q) ∨
    ∃ N₀ L, L ⊆ B₀ ∧ L.Infinite ∧
      ∀ b ∈ L, ∃ q,
        N₀ ≤ q ∧
        (∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
        crossingAtomEndpoints A B₀ q = {b} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({b} : Set ℕ) q ∧
        IsRigidPairSum A b (q - b) := by
  obtain hlarge | hsmall | hthree | hrigid :=
    minimalCrossingEndpointCertificates_four_way
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
        P hcore hcellCard hk
  · exact Or.inl hlarge
  · obtain hdense | hsingleLe :=
      eventualMinimalNearSharpSmallEndpointCertificates_two_or_singleton
        hsmall
    · exact Or.inr (Or.inl hdense)
    · have hsingle :=
        eventualMinimalNearSharpSingletonEndpointCertificates_exact
          hbasis hsingleLe
      obtain ⟨L, hLB₀, hL, hdata⟩ :=
        eventualMinimalNearSharpSingletonCertificates_give_infiniteEndpointSet
          hbasis hB₀A P hcore hcellCard (by omega) hsingle
      exact Or.inr (Or.inr (Or.inr
        (Or.inl ⟨L, hLB₀, hL, hdata⟩)))
  · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hrigid)))

/-- Endpoint-set form of the global migration dichotomy.  If the strict
certificate branch is not cofinal, the sharp branch yields an infinite
subset of `B₀` carrying distinct late private targets with unique rigid
crossing pairs. -/
theorem strictCrossingEndpointCertificates_or_infiniteMovingRigidEndpoints
    {A B₀ : Set ℕ} {F cell : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 4 ≤ k) :
    (∀ N, ∃ Q : Finset ℕ,
      k < Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∨
      ∃ N₀ L, L ⊆ B₀ ∧ L.Infinite ∧
        ∀ b ∈ L, ∃ q,
          N₀ ≤ q ∧
          (∀ E ∈ additiveSupportFamily A 2 q,
            ¬ Disjoint (E : Set ℕ) B₀ ∧
            ¬ (E : Set ℕ) ⊆ B₀) ∧
          crossingAtomEndpoints A B₀ q = {b} ∧
          DestroysAt (additiveSupportFamily A 3)
            ({b} : Set ℕ) q ∧
          IsRigidPairSum A b (q - b) := by
  obtain hstrict | ⟨N₀, hMoving⟩ :=
    strictCrossingEndpointCertificates_or_infiniteMovingRigidCores
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
        P hcore hcellCard hk
  · exact Or.inl hstrict
  · right
    have hMoving' : {i | IsSharpCrossingEndpointRigidCore
        A B₀ cell N₀ i}.Infinite := by
      simpa [IsSharpCrossingEndpointRigidCore] using hMoving
    obtain ⟨L, hLB₀, hL, hdata⟩ :=
      infiniteMovingRigidCores_give_infiniteRigidEndpointSet
        P hcore hcellCard hk hMoving'
    exact ⟨N₀, L, hLB₀, hL, hdata⟩

/-- Complements of moving private crossing endpoints escape to infinity.
Fix a basis element `a > T`.  Once `b` is beyond the order-two threshold
plus `a`, a private target `q` whose crossing endpoint is `b` reflects `a`
to `q - b - a`; in particular `b + a ≤ q`, so `T < a ≤ q - b`.
Thus the moving sharp branch cannot collapse to a bounded rigid star. -/
theorem privateCrossingEndpoint_complements_eventuallyLarge
    {A B₀ L : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∀ T, ∃ K, ∀ b ∈ L, K ≤ b → ∀ q,
      crossingAtomEndpoints A B₀ q = {b} →
      DestroysAt (additiveSupportFamily A 3)
        ({b} : Set ℕ) q →
      T ≤ q - b := by
  have hAinf := hbasis.infinite
  obtain ⟨N, hN⟩ := hbasis
  intro T
  obtain ⟨a, haA, hTa⟩ := hAinf.exists_gt T
  refine ⟨N + a + 1, ?_⟩
  intro b _hbL hbLarge q hendpoint hdestroy
  have hba : a ≠ b := by omega
  have hbEndpoint : b ∈ crossingAtomEndpoints A B₀ q := by
    rw [hendpoint]
    simp
  have hbLe : b ≤ q :=
    (mem_crossingAtomEndpoints_iff.mp hbEndpoint).1
  have hNaq : N + a ≤ q := by omega
  obtain ⟨hbaq, _hreflected⟩ :=
    privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy a haA hba hNaq
  omega

/-- A private rigid target forbids a nontrivial small forward translation
of its distinguished endpoint.  If `q = b + c`, `d ∈ A`, and `b + d ∈ A`,
the private reflection at `q` puts `c - d` in `A`.  These two translated
points give a second pair representation of `q`; rigidity leaves only the
trivial possibilities `d = 0` or `b + d = c`. -/
theorem privateRigidPair_forbids_smallForwardTranslate_of_threshold
    {A : Set ℕ} {b c q d N : ℕ}
    (hN : ∀ n, N ≤ n →
      ∃ v : Fin 2 → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = n)
    (hq : q = b + c)
    (hdestroy : DestroysAt (additiveSupportFamily A 3)
      ({b} : Set ℕ) q)
    (hrigid : IsRigidPairSum A b c)
    (hdA : d ∈ A) (hbdA : b + d ∈ A)
    (hdpos : 0 < d) (hdb : d ≠ b)
    (hdc : d ≤ c) (hbdc : b + d ≠ c)
    (hNd : N + d ≤ q) : False := by
  obtain ⟨_hbdq, hsubA⟩ :=
    privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy d hdA hdb hNd
  have hcomp : (b + c) - (b + d) = c - d := by omega
  have hcsubA : c - d ∈ A := by
    have hsubEq : q - b - d = c - d := by
      rw [hq]
      omega
    exact hsubEq ▸ hsubA
  let E : Finset ℕ := pairSupport (b + c) (b + d)
  have hER : E ∈ additiveSupportFamily A 2 (b + c) := by
    apply pairSupport_mem_additiveSupportFamily (by omega) hbdA
    simpa [E, hcomp] using hcsubA
  have hEcanonical : E = pairSupport (b + c) b :=
    hrigid E hER
  have hbdE : b + d ∈ E := by simp [E, pairSupport]
  have hbdCanonical : b + d ∈ pairSupport (b + c) b := by
    rw [← hEcanonical]
    exact hbdE
  have hcases : b + d = b ∨ b + d = c := by
    simpa [pairSupport] using hbdCanonical
  rcases hcases with hzero | hswap
  · omega
  · exact hbdc hswap

/-- Explicit center-gap obstruction for three moving private targets.  The
second and third targets translate both `0` and the first endpoint `b₀` by
the difference of their reflection centers.  If that positive gap lies
strictly inside the first rigid pair (and is not its swapping displacement),
the preceding lemma gives a second representation of the first target. -/
theorem three_privateRigidTargets_forbid_smallCenterGap_of_threshold
    {A : Set ℕ} {b₀ c₀ q₀ b₁ q₁ b₂ q₂ N : ℕ}
    (hN : ∀ n, N ≤ n →
      ∃ v : Fin 2 → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = n)
    (hzeroA : 0 ∈ A) (hb₀A : b₀ ∈ A)
    (hq₀ : q₀ = b₀ + c₀)
    (hdestroy₀ : DestroysAt (additiveSupportFamily A 3)
      ({b₀} : Set ℕ) q₀)
    (hrigid₀ : IsRigidPairSum A b₀ c₀)
    (hdestroy₁ : DestroysAt (additiveSupportFamily A 3)
      ({b₁} : Set ℕ) q₁)
    (hdestroy₂ : DestroysAt (additiveSupportFamily A 3)
      ({b₂} : Set ℕ) q₂)
    (hzeroNe₁ : 0 ≠ b₁) (hb₀Ne₁ : b₀ ≠ b₁)
    (hNq₁ : N ≤ q₁) (hNb₀q₁ : N + b₀ ≤ q₁)
    (hreflectedZeroNe : q₁ - b₁ ≠ b₂)
    (hreflectedBNe : q₁ - b₁ - b₀ ≠ b₂)
    (hNreflectedZero : N + (q₁ - b₁) ≤ q₂)
    (hNreflectedB : N + (q₁ - b₁ - b₀) ≤ q₂)
    (hcenter : q₁ - b₁ ≤ q₂ - b₂)
    (hcenterStrict : q₁ - b₁ < q₂ - b₂)
    (hgapNeB₀ : (q₂ - b₂) - (q₁ - b₁) ≠ b₀)
    (hgapLe : (q₂ - b₂) - (q₁ - b₁) ≤ c₀)
    (hgapNoSwap : b₀ + ((q₂ - b₂) - (q₁ - b₁)) ≠ c₀)
    (hNgap : N + ((q₂ - b₂) - (q₁ - b₁)) ≤ q₀) :
    False := by
  let d := (q₂ - b₂) - (q₁ - b₁)
  have hdpos : 0 < d := by
    dsimp only [d]
    omega
  have hdA : d ∈ A := by
    simpa [d] using
      (two_privateOrderThreeTargets_imply_crossTranslation_of_threshold
        hN hdestroy₁ hdestroy₂ hzeroA hzeroNe₁ hNq₁
          hreflectedZeroNe hNreflectedZero hcenter)
  have hb₀dA : b₀ + d ∈ A := by
    simpa [d] using
      (two_privateOrderThreeTargets_imply_crossTranslation_of_threshold
        hN hdestroy₁ hdestroy₂ hb₀A hb₀Ne₁ hNb₀q₁
          hreflectedBNe hNreflectedB hcenter)
  exact privateRigidPair_forbids_smallForwardTranslate_of_threshold
    hN hq₀ hdestroy₀ hrigid₀ hdA hb₀dA hdpos
      (by simpa [d] using hgapNeB₀)
      (by simpa [d] using hgapLe)
      (by simpa [d] using hgapNoSwap)
      (by simpa [d] using hNgap)

/-- Functional parametrization of an infinite moving rigid-endpoint set.
Choose one private target for every endpoint.  Its complementary center
`target b - b` tends to infinity along the natural ordering of the endpoint
set, by `privateCrossingEndpoint_complements_eventuallyLarge`. -/
theorem exists_movingRigidEndpointParametrization
    {A B₀ L : Set ℕ} {N₀ : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hdata : ∀ b ∈ L, ∃ q,
      N₀ ≤ q ∧
      (∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀) ∧
      crossingAtomEndpoints A B₀ q = {b} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({b} : Set ℕ) q ∧
      IsRigidPairSum A b (q - b)) :
    ∃ target : L → ℕ,
      (∀ b,
        N₀ ≤ target b ∧
        (∀ E ∈ additiveSupportFamily A 2 (target b),
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
        crossingAtomEndpoints A B₀ (target b) = {b.1} ∧
        DestroysAt (additiveSupportFamily A 3)
          ({b.1} : Set ℕ) (target b) ∧
        IsRigidPairSum A b.1 (target b - b.1)) ∧
      ∀ T, ∃ K, ∀ b : L, K ≤ b.1 →
        T ≤ target b - b.1 := by
  classical
  have hchoose : ∀ b : L, ∃ q,
      N₀ ≤ q ∧
      (∀ E ∈ additiveSupportFamily A 2 q,
        ¬ Disjoint (E : Set ℕ) B₀ ∧
        ¬ (E : Set ℕ) ⊆ B₀) ∧
      crossingAtomEndpoints A B₀ q = {b.1} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({b.1} : Set ℕ) q ∧
      IsRigidPairSum A b.1 (q - b.1) := by
    intro b
    exact hdata b.1 b.2
  choose target htarget using hchoose
  refine ⟨target, htarget, ?_⟩
  intro T
  obtain ⟨K, hK⟩ :=
    privateCrossingEndpoint_complements_eventuallyLarge
      (B₀ := B₀) (L := L) hbasis T
  refine ⟨K, ?_⟩
  intro b hbLarge
  exact hK b.1 b.2 hbLarge (target b)
    (htarget b).2.2.1 (htarget b).2.2.2.1

/-- Lacunarity forced on any parametrized moving rigid-endpoint system.
Take three sufficiently separated endpoints `u < v < w`.  Reflections at
the targets of `v` and `w` translate both `0` and `u` by their positive
center gap.  The rigid target at `u` then forces that gap either to exceed
the whole earlier center or to be one of the two trivial exceptional
displacements (`gap = u` or `u + gap = center u`). -/
theorem movingRigidEndpoint_centerGap_large_or_exception
    {A B₀ L : Set ℕ} {target : L → ℕ} {N : ℕ}
    (hN : ∀ n, N ≤ n →
      ∃ v : Fin 2 → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = n)
    (hzeroA : 0 ∈ A) (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (htarget : ∀ b,
      crossingAtomEndpoints A B₀ (target b) = {b.1} ∧
      DestroysAt (additiveSupportFamily A 3)
        ({b.1} : Set ℕ) (target b) ∧
      IsRigidPairSum A b.1 (target b - b.1))
    {u v w : L}
    (huv : u.1 ≠ v.1)
    (hNu : N ≤ u.1)
    (hNuv : N + u.1 ≤ v.1)
    (hNcenterW : N + (target v - v.1) + 1 ≤ w.1)
    (hcenter : target v - v.1 < target w - w.1) :
    target u - u.1 <
        (target w - w.1) - (target v - v.1) ∨
      (target w - w.1) - (target v - v.1) = u.1 ∨
      u.1 + ((target w - w.1) - (target v - v.1)) =
        target u - u.1 := by
  classical
  let gap := (target w - w.1) - (target v - v.1)
  have endpointMem (b : L) :
      b.1 ∈ crossingAtomEndpoints A B₀ (target b) := by
    rw [(htarget b).1]
    simp
  have hvalueLe (b : L) : b.1 ≤ target b :=
    (mem_crossingAtomEndpoints_iff.mp (endpointMem b)).1
  have hvalueB₀ (b : L) : b.1 ∈ B₀ :=
    (mem_crossingAtomEndpoints_iff.mp (endpointMem b)).2.1
  have htargetEq (b : L) :
      target b = b.1 + (target b - b.1) := by
    exact (Nat.add_sub_of_le (hvalueLe b)).symm
  have hvpos : 0 ≠ v.1 := by
    intro hvzero
    exact hzeroB₀ (hvzero ▸ hvalueB₀ v)
  have hvTarget : v.1 ≤ target v := hvalueLe v
  have hwTarget : w.1 ≤ target w := hvalueLe w
  have hNqv : N ≤ target v := by omega
  have hNuvTarget : N + u.1 ≤ target v := hNuv.trans hvTarget
  have hcenterVW : target v - v.1 ≤ target w - w.1 :=
    Nat.le_of_lt hcenter
  have hreflectedZeroNe : target v - v.1 ≠ w.1 := by omega
  have hreflectedUNe : target v - v.1 - u.1 ≠ w.1 := by omega
  have hNreflectedZero : N + (target v - v.1) ≤ target w := by
    omega
  have hNreflectedU : N + (target v - v.1 - u.1) ≤ target w := by
    omega
  by_contra hnot
  push Not at hnot
  have hgapLe : gap ≤ target u - u.1 := by omega
  have hNgap : N + gap ≤ target u := by
    rw [htargetEq u]
    omega
  exact three_privateRigidTargets_forbid_smallCenterGap_of_threshold
    hN hzeroA (hB₀A (hvalueB₀ u)) (htargetEq u)
      (htarget u).2.1 (htarget u).2.2
      (htarget v).2.1 (htarget w).2.1
      hvpos huv hNqv hNuvTarget hreflectedZeroNe hreflectedUNe
      hNreflectedZero hNreflectedU hcenterVW hcenter
      (by simpa [gap] using hnot.2.1)
      (by simpa [gap] using hgapLe)
      (by simpa [gap] using hnot.2.2)
      (by simpa [gap] using hNgap)

/-- Counterexample-level form of the scalable crossing-endpoint fork.  For
every finite scale `k ≥ 4`, one fixed repaired zero-atomic reservoir admits
an exact `k`-point core partition.  Arbitrarily late strengthened endpoint
certificates on that partition are either strictly larger than a core, or
their sharp case fills one core with private order-three destroyers whose
targets have unique rigid crossing-pair representations. -/
theorem counterexample_forces_arbitraryCrossingEndpointTripleFork
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ k, 4 ≤ k →
      ∃ B₀, B₀ ⊆ A ∧ B₀.Infinite ∧ 0 ∉ B₀ ∧
        (∀ x ∈ B₀, ∀ E ∈ additiveSupportFamily A 2 x,
          E = {x, 0}) ∧
        HasDirectTripleRepairsForDeletedPairs A B₀ ∧
        (∀ x ∈ B₀, ∃ G ∈ additiveSupportFamily A 3 x,
          Disjoint (G : Set ℕ) B₀) ∧
        ∃ F cell : ℕ → Finset ℕ,
          IsFiniteBlockPartition B₀ F ∧
          (∀ i, cell i ⊆ F i) ∧
          (∀ i, (cell i).card = k) ∧
          ∀ N, ∃ Q : Finset ℕ,
            k ≤ Q.card ∧
            (∀ q ∈ Q, N ≤ q ∧
              ∀ E ∈ additiveSupportFamily A 2 q,
                ¬ Disjoint (E : Set ℕ) B₀ ∧
                ¬ (E : Set ℕ) ⊆ B₀) ∧
            (∀ sel : BlockSelector F, ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q ∧
              (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
                selectedSet sel) ∧
            (k < Q.card ∨
              ∃ point : {q // q ∈ Q} → ℕ, ∃ i,
                cell i = Q.attach.image point ∧
                Function.Injective point ∧
                ∀ q,
                  crossingAtomEndpoints A B₀ q.1 = {point q} ∧
                  DestroysAt (additiveSupportFamily A 3)
                    ({point q} : Set ℕ) q.1 ∧
                  IsRigidPairSum A (point q)
                    (q.1 - point q)) := by
  intro k hk
  obtain ⟨B₀, hB₀A, hB₀, hzeroB₀, hnormal,
      hrepairs, hselfRepairs, _hcrossing⟩ :=
    counterexample_forces_repairedCrossingReservoir
      hbasis hzeroA hcounter
  obtain ⟨F, cell, P, hcore, hcellCard⟩ :=
    exists_finiteBlockPartition_with_exactCoreCard hB₀ (by omega : 0 < k)
  refine ⟨B₀, hB₀A, hB₀, hzeroB₀, hnormal,
    hrepairs, hselfRepairs, F, cell, P, hcore, hcellCard, ?_⟩
  exact finiteCrossingEndpointTripleCertificates_strict_or_rigidCore
    hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter
      P hcore hcellCard hk

set_option maxHeartbeats 3000000 in
/-- Amplified endpoint certificate on one repaired reservoir.  A single late
finite target set still certifies every selector, and every choice of one
crossing endpoint per target covers any prescribed number of whole blocks.
This is the endpoint-specific form of strong deletion amplification: the
order-three supports cannot hide the growth because singleton endpoint
supports are available in the strengthened obstruction family. -/
theorem amplifiedCrossingEndpointTripleCertificates_of_counterexample
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      (∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel) ∧
      ∀ point : {q // q ∈ Q} → ℕ,
        (∀ q, point q ∈ crossingAtomEndpoints A B₀ q.1) →
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I, F i ⊆ Q.attach.image point := by
  classical
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro M start N
  let R : SupportFamily :=
    crossingEndpointTripleObstructionFamily A B₀
  have hstrong : StrongInfiniteDeletion R B₀ := by
    simpa [R] using
      strongCrossingEndpointTripleObstruction_of_counterexample
        hzeroA hzeroB₀ hB₀A hrepairs hcounter
  obtain ⟨Q₀, hQ₀late, hcert₀, hmany₀⟩ :=
    exists_manyCoveredBlocks_and_certificate_of_strongInfiniteDeletion
      P hstrong M start (max N N₂)
  let Cross : ℕ → Prop := fun q =>
    ∀ E ∈ additiveSupportFamily A 2 q,
      ¬ Disjoint (E : Set ℕ) B₀ ∧
      ¬ (E : Set ℕ) ⊆ B₀
  let Q : Finset ℕ := Q₀.filter Cross
  have hQdata : ∀ q ∈ Q, N ≤ q ∧ Cross q := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨(le_max_left N N₂).trans (hQ₀late q hq.1), hq.2⟩
  have hcert : ∀ sel : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A 3)
        (selectedSet sel) q ∧
      (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
        selectedSet sel := by
    intro sel
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ sel
    have hqData :=
      destroysAt_crossingEndpointTripleObstructionFamily_iff.mp
        (by simpa [R] using hqDestroy)
    exact ⟨q, Finset.mem_filter.mpr ⟨hqQ₀, hqData.1⟩,
      hqData.2.1, hqData.2.2⟩
  refine ⟨Q, ?_, hcert, ?_⟩
  · simpa [Cross] using hQdata
  · intro point hpoint
    let c : FiniteSupportChoice R Q₀ := fun q => by
      by_cases hcross : Cross q.1
      · let qQ : {n // n ∈ Q} :=
          ⟨q.1, Finset.mem_filter.mpr ⟨q.2, hcross⟩⟩
        refine ⟨{point qQ}, ?_⟩
        change (∀ E ∈ additiveSupportFamily A 2 q.1,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) at hcross
        simp only [R, crossingEndpointTripleObstructionFamily,
          if_pos hcross]
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr
          ⟨point qQ, hpoint qQ, rfl⟩
      · refine ⟨∅, ?_⟩
        change ¬ (∀ E ∈ additiveSupportFamily A 2 q.1,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) at hcross
        simp [R, crossingEndpointTripleObstructionFamily, hcross]
    obtain ⟨I, hIcard, hIstart, hIcover⟩ := hmany₀ c
    refine ⟨I, hIcard, hIstart, ?_⟩
    intro i hiI x hxi
    have hxUnion : x ∈ finiteSupportChoiceUnion c :=
      hIcover i hiI hxi
    obtain ⟨q, _hqAttach, hxq⟩ :=
      Finset.mem_biUnion.mp hxUnion
    by_cases hcross : Cross q.1
    · let qQ : {n // n ∈ Q} :=
        ⟨q.1, Finset.mem_filter.mpr ⟨q.2, hcross⟩⟩
      have hxEq : x = point qQ := by
        simpa [c, hcross, qQ] using hxq
      subst x
      exact Finset.mem_image.mpr
        ⟨qQ, Finset.mem_attach Q qQ, rfl⟩
    · simpa [c, hcross] using hxq

/-- Quantitative consequence of the amplified endpoint certificate.  If
every partition block has at least `k` points, forcing `M` pairwise-disjoint
blocks into one chosen endpoint per target requires at least `M * k`
distinct targets.  Thus the crossing obstruction has arbitrarily large
linear finite certificates, not merely the one-core lower bound. -/
theorem amplifiedCrossingEndpointTripleCertificates_targetCard_lower
    {A B₀ : Set ℕ} {F : ℕ → Finset ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hzeroB₀ : 0 ∉ B₀)
    (hB₀A : B₀ ⊆ A)
    (hrepairs : HasDirectTripleRepairsForDeletedPairs A B₀)
    (hcounter : ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (P : IsFiniteBlockPartition B₀ F)
    (hblockLower : ∀ i, k ≤ (F i).card) :
    ∀ M N, ∃ Q : Finset ℕ,
      M * k ≤ Q.card ∧
      (∀ q ∈ Q, N ≤ q ∧
        ∀ E ∈ additiveSupportFamily A 2 q,
          ¬ Disjoint (E : Set ℕ) B₀ ∧
          ¬ (E : Set ℕ) ⊆ B₀) ∧
      ∀ sel : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q ∧
        (crossingAtomEndpoints A B₀ q : Set ℕ) ⊆
          selectedSet sel := by
  classical
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro M N
  obtain ⟨Q, hQdata, hcert, hcover⟩ :=
    amplifiedCrossingEndpointTripleCertificates_of_counterexample
      hbasis hzeroA hzeroB₀ hB₀A hrepairs hcounter P
        M 0 (max N N₂)
  have hendpoint : ∀ q ∈ Q,
      (crossingAtomEndpoints A B₀ q).Nonempty := by
    intro q hqQ
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQdata q hqQ).1)
    obtain ⟨b, hbB₀, c, hcC, hbc, _hEeq⟩ :=
      exists_endpoints_of_crossingPairSupport hER
        ((hQdata q hqQ).2 E hER).1
        ((hQdata q hqQ).2 E hER).2
    have hbLe : b ≤ q := by omega
    have hsub : q - b = c := by omega
    exact ⟨b, mem_crossingAtomEndpoints_iff.mpr
      ⟨hbLe, hbB₀, hsub ▸ hcC⟩⟩
  let point : {q // q ∈ Q} → ℕ := fun q =>
    (hendpoint q.1 q.2).choose
  have hpoint : ∀ q,
      point q ∈ crossingAtomEndpoints A B₀ q.1 := by
    intro q
    exact (hendpoint q.1 q.2).choose_spec
  obtain ⟨I, hIcard, _hIstart, hIcover⟩ := hcover point hpoint
  let U : Finset ℕ := I.biUnion F
  have hpairwise : (I : Set ℕ).PairwiseDisjoint F := by
    intro i hiI j hjI hij
    exact P.disjoint hij
  have hUsub : U ⊆ Q.attach.image point := by
    intro x hxU
    obtain ⟨i, hiI, hxi⟩ := Finset.mem_biUnion.mp hxU
    exact hIcover i hiI hxi
  have htargetCard : M * k ≤ Q.card := by
    calc
      M * k = I.card * k := by rw [hIcard]
      _ = ∑ i ∈ I, k := by simp
      _ ≤ ∑ i ∈ I, (F i).card := by
        apply Finset.sum_le_sum
        intro i hiI
        exact hblockLower i
      _ = U.card := by
        dsimp only [U]
        rw [Finset.card_biUnion hpairwise]
      _ ≤ (Q.attach.image point).card :=
        Finset.card_le_card hUsub
      _ ≤ Q.attach.card := Finset.card_image_le
      _ = Q.card := by simp
  refine ⟨Q, htargetCard, ?_, hcert⟩
  intro q hqQ
  exact ⟨(le_max_left N N₂).trans (hQdata q hqQ).1,
    (hQdata q hqQ).2⟩

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

/-- Finite-family form of
`exists_infinite_freeSet_avoiding_injectiveImage`.  Iterated thinning makes
one bounded support map avoid the retained indices and every one of `k`
injective marked-point images simultaneously.  This is the avoidance engine
needed by an arbitrary finite repaired-option extension. -/
theorem exists_infinite_freeSet_avoiding_injectiveImages
    {K : Set ℕ} (hK : K.Infinite) (k : ℕ)
    (u : Fin k → ℕ → ℕ)
    (huInj : ∀ a, Set.InjOn (u a) K)
    (h : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ b ∈ K, (h b).card ≤ r)
    (hbNotH : ∀ b ∈ K, b ∉ h b)
    (huNotH : ∀ b ∈ K, ∀ a, u a b ∉ h b) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L,
        Disjoint (h b : Set ℕ) L ∧
        ∀ a, ∀ d ∈ L, u a d ∉ h b := by
  induction k generalizing K with
  | zero =>
      obtain ⟨L, hLK, hL, hfree⟩ :=
        exists_infinite_freeSet_of_bounded_pointMap
          hK h r hcard hbNotH
      refine ⟨L, hLK, hL, ?_⟩
      intro b hb
      refine ⟨hfree b hb, ?_⟩
      intro a
      exact Fin.elim0 a
  | succ k ih =>
      let u₀ : ℕ → ℕ := u 0
      obtain ⟨L₀, hL₀K, hL₀, havoid₀⟩ :=
        exists_infinite_freeSet_avoiding_injectiveImage
          hK u₀ (huInj 0) h r hcard hbNotH
            (fun b hb => huNotH b hb 0)
      let uTail : Fin k → ℕ → ℕ := fun a => u a.succ
      obtain ⟨L, hLL₀, hL, havoidTail⟩ :=
        ih hL₀ uTail
          (fun a => (huInj a.succ).mono hL₀K)
          (fun b hb => hcard b (hL₀K hb))
          (fun b hb => hbNotH b (hL₀K hb))
          (fun b hb a => huNotH b (hL₀K hb) a.succ)
      refine ⟨L, hLL₀.trans hL₀K, hL, ?_⟩
      intro b hb
      have hbL₀ := hLL₀ hb
      refine ⟨(havoidTail b hb).1, ?_⟩
      intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · intro d hd
        exact (havoid₀ b hbL₀).2 d (hLL₀ hd)
      · exact (havoidTail b hb).2 a

/- Cross-block image avoidance does not require the support map to avoid the
index set itself.  Erase the diagonal marked point, pull every remaining
marked point back to its unique owner, and take a free set for that bounded
owner map.  This is the index-agnostic form needed to extend an abstract
`RepairedOptionSystem`, whose block indices need not themselves be elements
of `A`. -/
theorem exists_infinite_crossAvoiding_injectiveImage
    {K : Set ℕ} (hK : K.Infinite)
    (u : ℕ → ℕ) (huInj : Set.InjOn u K)
    (h : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ b ∈ K, (h b).card ≤ r) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ b ∈ L, ∀ d ∈ L, b ≠ d → u d ∉ h b := by
  classical
  let erased : ℕ → Finset ℕ := fun b => (h b).erase (u b)
  let HasOwner : ℕ → Prop := fun x => ∃ d ∈ K, u d = x
  let owner : ℕ → ℕ := fun x =>
    if hx : HasOwner x then Classical.choose hx else 0
  have hownerSpec : ∀ x, HasOwner x →
      owner x ∈ K ∧ u (owner x) = x := by
    intro x hx
    simp only [owner, dif_pos hx]
    exact Classical.choose_spec hx
  let collision : ℕ → Finset ℕ := fun b =>
    ((erased b).filter HasOwner).image owner
  have hcollisionCard : ∀ b ∈ K, (collision b).card ≤ r := by
    intro b hb
    calc
      (collision b).card ≤ ((erased b).filter HasOwner).card :=
        Finset.card_image_le
      _ ≤ (erased b).card := Finset.card_filter_le _ _
      _ ≤ (h b).card := Finset.card_erase_le
      _ ≤ r := hcard b hb
  have hcollisionMem : ∀ b, ∀ d ∈ K,
      u d ∈ erased b → d ∈ collision b := by
    intro b d hd hud
    have howned : HasOwner (u d) := ⟨d, hd, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨u d, Finset.mem_filter.mpr ⟨hud, howned⟩, ?_⟩
    have hspec := hownerSpec (u d) howned
    exact huInj hspec.1 hd hspec.2
  have hbNotCollision : ∀ b ∈ K, b ∉ collision b := by
    intro b hb hbCollision
    obtain ⟨x, hxFilter, hownerb⟩ :=
      Finset.mem_image.mp hbCollision
    have hxErased := (Finset.mem_filter.mp hxFilter).1
    have hxOwned := (Finset.mem_filter.mp hxFilter).2
    have hspec := hownerSpec x hxOwned
    have hubx : u b = x := by
      rw [← hownerb]
      exact hspec.2
    exact (Finset.mem_erase.mp hxErased).1 hubx.symm
  obtain ⟨L, hLK, hL, hfree⟩ :=
    exists_infinite_freeSet_of_bounded_pointMap
      hK collision r hcollisionCard hbNotCollision
  refine ⟨L, hLK, hL, ?_⟩
  intro b hb d hd hbd hud
  have hune : u d ≠ u b := by
    intro hEq
    exact hbd (huInj (hLK hd) (hLK hb) hEq).symm
  have hudErased : u d ∈ erased b :=
    Finset.mem_erase.mpr ⟨hune, hud⟩
  exact Set.disjoint_left.mp (hfree b hb)
    (Finset.mem_coe.mpr
      (hcollisionMem b d (hLK hd) hudErased)) hd

/- Finite-family version of cross-block image avoidance.  The support map
is thinned successively against each injective marked image; previously
obtained avoidance properties persist under further thinning. -/
theorem exists_infinite_crossAvoiding_injectiveImages
    {K : Set ℕ} (hK : K.Infinite) (k : ℕ)
    (u : Fin k → ℕ → ℕ)
    (huInj : ∀ a, Set.InjOn (u a) K)
    (h : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ b ∈ K, (h b).card ≤ r) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ a, ∀ b ∈ L, ∀ d ∈ L, b ≠ d → u a d ∉ h b := by
  induction k generalizing K with
  | zero =>
      exact ⟨K, Set.Subset.rfl, hK, fun a => Fin.elim0 a⟩
  | succ k ih =>
      let u₀ : ℕ → ℕ := u 0
      obtain ⟨L₀, hL₀K, hL₀, havoid₀⟩ :=
        exists_infinite_crossAvoiding_injectiveImage
          hK u₀ (huInj 0) h r hcard
      let uTail : Fin k → ℕ → ℕ := fun a => u a.succ
      obtain ⟨L, hLL₀, hL, havoidTail⟩ :=
        ih hL₀ uTail
          (fun a => (huInj a.succ).mono hL₀K)
          (fun b hb => hcard b (hL₀K hb))
      refine ⟨L, hLL₀.trans hL₀K, hL, ?_⟩
      intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · intro b hb d hd hbd
        exact havoid₀ b (hLL₀ hb) d (hLL₀ hd) hbd
      · exact havoidTail a

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

/-- Finite-option generalization of the self-repair construction.  If an
injective new option `t b` lies strictly below the atom and every one of a
finite family of old injective options, then after thinning it has a
self-avoiding order-three repair which avoids all retained atoms, all new
options, and every old option image. -/
theorem exists_infinite_selfRepair_avoiding_finiteOptions
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB : B.Infinite)
    (t : ℕ → ℕ) (htInj : Set.InjOn t B)
    (htb : ∀ b ∈ B, t b < b)
    (k : ℕ) (oldOption : Fin k → ℕ → ℕ)
    (holdInj : ∀ a, Set.InjOn (oldOption a) B)
    (htOld : ∀ b ∈ B, ∀ a, t b < oldOption a b) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ repair : ℕ → Finset ℕ, ∀ b ∈ L,
        repair b ∈ additiveSupportFamily A 3 (t b) ∧
        t b ∉ repair b ∧
        Disjoint (repair b : Set ℕ) L ∧
        (∀ d ∈ L, t d ∉ repair b) ∧
        ∀ a, ∀ d ∈ L, oldOption a d ∉ repair b := by
  classical
  obtain ⟨T, hselfAvoid⟩ :=
    eventually_selfAvoidingTripleSupport_of_orderTwoBasis hbasis
  let Low : Set ℕ := {b | b ∈ B ∧ t b < T}
  have hLowFinite : Low.Finite := by
    apply Set.Finite.of_finite_image (f := t)
    · apply (Set.finite_Iio T).subset
      rintro y ⟨b, hbLow, rfl⟩
      exact hbLow.2
    · exact htInj.mono (fun _ hb => hb.1)
  let K : Set ℕ := B \ Low
  have hK : K.Infinite := hB.diff hLowFinite
  have hKB : K ⊆ B := Set.diff_subset
  have htLarge : ∀ b ∈ K, T ≤ t b := by
    intro b hb
    by_contra hnot
    exact hb.2 ⟨hb.1, Nat.lt_of_not_ge hnot⟩
  have hrepairExists : ∀ b : K, ∃ H,
      H ∈ additiveSupportFamily A 3 (t b.1) ∧ t b.1 ∉ H := by
    intro b
    exact hselfAvoid (t b.1) (htLarge b.1 b.2)
  choose chosen hchosenR hchosenSelf using hrepairExists
  let repair : ℕ → Finset ℕ := fun b =>
    if hb : b ∈ K then chosen ⟨b, hb⟩ else ∅
  have hrepairR : ∀ b ∈ K,
      repair b ∈ additiveSupportFamily A 3 (t b) := by
    intro b hb
    simpa [repair, hb] using hchosenR ⟨b, hb⟩
  have hrepairSelf : ∀ b ∈ K, t b ∉ repair b := by
    intro b hb
    simpa [repair, hb] using hchosenSelf ⟨b, hb⟩
  have hrepairCard : ∀ b ∈ K, (repair b).card ≤ 3 := by
    intro b hb
    exact additiveSupportFamily_cardAtMost A 3
      (t b) (repair b) (hrepairR b hb)
  have hbNotRepair : ∀ b ∈ K, b ∉ repair b := by
    intro b hb hbRepair
    have hble : b ≤ t b :=
      additiveSupportFamily_supportsBounded A 3
        (t b) (repair b) (hrepairR b hb) b hbRepair
    exact (not_le_of_gt (htb b (hKB hb))) hble
  have holdNotRepair : ∀ b ∈ K, ∀ a,
      oldOption a b ∉ repair b := by
    intro b hb a holdRepair
    have holdle : oldOption a b ≤ t b :=
      additiveSupportFamily_supportsBounded A 3
        (t b) (repair b) (hrepairR b hb)
          (oldOption a b) holdRepair
    exact (not_le_of_gt (htOld b (hKB hb) a)) holdle
  let allOption : Fin k.succ → ℕ → ℕ := fun a =>
    Fin.cases t (fun a => oldOption a) a
  have hallInj : ∀ a, Set.InjOn (allOption a) K := by
    intro a
    refine Fin.cases (htInj.mono hKB)
      (fun a => (holdInj a).mono hKB) a
  have hallNotRepair : ∀ b ∈ K, ∀ a,
      allOption a b ∉ repair b := by
    intro b hb a
    refine Fin.cases (hrepairSelf b hb)
      (fun a => holdNotRepair b hb a) a
  obtain ⟨L, hLK, hL, havoid⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImages
      hK k.succ allOption hallInj repair 3 hrepairCard
        hbNotRepair hallNotRepair
  refine ⟨L, hLK.trans hKB, hL, repair, ?_⟩
  intro b hb
  have hbK := hLK hb
  refine ⟨hrepairR b hbK, hrepairSelf b hbK,
    (havoid b hb).1, ?_, ?_⟩
  · intro d hd
    exact (havoid b hb).2 0 d hd
  · intro a d hd
    exact (havoid b hb).2 a.succ d hd

/-- An injective family of targets with self-avoiding three-term repair
supports has an infinite thinning with an injective chosen repair point
strictly below its target.  Apply the infinite delta-system theorem to the
repair supports.  Empty petals can occur only at bounded targets, hence only
finitely often by target injectivity; points chosen from the remaining
pairwise-disjoint petals are automatically injective. -/
theorem exists_infinite_injectiveRepairPoint
    {A B : Set ℕ} (hB : B.Infinite)
    (t : ℕ → ℕ) (htInj : Set.InjOn t B)
    (h : ℕ → Finset ℕ)
    (hhR : ∀ b ∈ B,
      h b ∈ additiveSupportFamily A 3 (t b))
    (htNotH : ∀ b ∈ B, t b ∉ h b) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ s : ℕ → ℕ, Set.InjOn s L ∧
        ∀ b ∈ L, s b ∈ h b ∧ 0 < s b ∧ s b < t b := by
  classical
  have hhCard : ∀ b ∈ B, (h b).card ≤ 3 := by
    intro b hb
    exact additiveSupportFamily_cardAtMost A 3
      (t b) (h b) (hhR b hb)
  obtain ⟨L₀, hL₀B, hL₀, S₀, hdelta⟩ :=
    exists_infinite_deltaSystem_of_bounded_pointMap
      hB h 3 hhCard
  let S : Finset ℕ := insert 0 S₀
  let EmptyPetal : Set ℕ :=
    {b | b ∈ L₀ ∧ h b \ S = ∅}
  have hEmptyFinite : EmptyPetal.Finite := by
    apply Set.Finite.of_finite_image (f := t)
    · apply (Set.finite_Iic (3 * S.sum id)).subset
      rintro y ⟨b, hbEmpty, rfl⟩
      have hbB : b ∈ B := hL₀B hbEmpty.1
      have hsub : h b ⊆ S :=
        Finset.sdiff_eq_empty_iff_subset.mp hbEmpty.2
      obtain ⟨v, _hvA, hvsum, hvSupport⟩ :=
        mem_additiveSupportFamily_iff.mp (hhR b hbB)
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
    · exact htInj.mono (fun _ hb => hL₀B hb.1)
  let L : Set ℕ := L₀ \ EmptyPetal
  have hLL₀ : L ⊆ L₀ := Set.diff_subset
  have hL : L.Infinite := hL₀.diff hEmptyFinite
  have hpetal : ∀ b : L, (h b.1 \ S).Nonempty := by
    intro b
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact b.2.2 ⟨hLL₀ b.2, hempty⟩
  let s : ℕ → ℕ := fun b =>
    if hb : b ∈ L then Classical.choose (hpetal ⟨b, hb⟩) else 0
  have hsPetal : ∀ b ∈ L, s b ∈ h b \ S := by
    intro b hb
    simpa [s, hb] using Classical.choose_spec (hpetal ⟨b, hb⟩)
  have hsInj : Set.InjOn s L := by
    intro b hb d hd hsd
    by_contra hbd
    have hsInter : s b ∈ h b ∩ h d :=
      Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp (hsPetal b hb)).1,
          hsd ▸ (Finset.mem_sdiff.mp (hsPetal d hd)).1⟩
    have hsRoot₀ : s b ∈ S₀ := by
      rw [← hdelta b (hLL₀ hb) d (hLL₀ hd) hbd]
      exact hsInter
    exact (Finset.mem_sdiff.mp (hsPetal b hb)).2
      (Finset.mem_insert_of_mem hsRoot₀)
  refine ⟨L, hLL₀.trans hL₀B, hL, s, hsInj, ?_⟩
  intro b hb
  have hsH := (Finset.mem_sdiff.mp (hsPetal b hb)).1
  have hsle := additiveSupportFamily_supportsBounded A 3
    (t b) (h b) (hhR b ((hLL₀.trans hL₀B) hb)) (s b) hsH
  have hsne : s b ≠ t b := by
    intro hEq
    exact htNotH b ((hLL₀.trans hL₀B) hb) (hEq ▸ hsH)
  have hsZero : s b ≠ 0 := by
    intro hEq
    exact (Finset.mem_sdiff.mp (hsPetal b hb)).2
      (hEq ▸ Finset.mem_insert_self 0 S₀)
  exact ⟨hsH, Nat.pos_of_ne_zero hsZero,
    lt_of_le_of_ne hsle hsne⟩

/-- Choose an injective new option from a self-avoiding repair family and
then thin so every bounded old support belonging to one block avoids the new
options of all other blocks.  Erasing the same-block chosen point makes the
ordinary marked-image free-set theorem applicable. -/
theorem exists_infinite_crossAvoidingRepairPoint
    {A B : Set ℕ} (hB : B.Infinite)
    (target : ℕ → ℕ) (htargetInj : Set.InjOn target B)
    (parentRepair : ℕ → Finset ℕ)
    (hparentR : ∀ b ∈ B,
      parentRepair b ∈ additiveSupportFamily A 3 (target b))
    (hparentSelf : ∀ b ∈ B, target b ∉ parentRepair b)
    (oldSupports : ℕ → Finset ℕ) (R : ℕ)
    (holdCard : ∀ b ∈ B, (oldSupports b).card ≤ R)
    (hbNotOld : ∀ b ∈ B, b ∉ oldSupports b) :
    ∃ L, L ⊆ B ∧ L.Infinite ∧
      ∃ newOption : ℕ → ℕ,
        Set.InjOn newOption L ∧
        (∀ b ∈ L,
          newOption b ∈ parentRepair b ∧
          0 < newOption b ∧ newOption b < target b) ∧
        ∀ b ∈ L, ∀ d ∈ L, b ≠ d →
          newOption d ∉ oldSupports b := by
  classical
  obtain ⟨K, hKB, hK, newOption, hnewInj, hnewData⟩ :=
    exists_infinite_injectiveRepairPoint
      hB target htargetInj parentRepair hparentR hparentSelf
  let oldErased : ℕ → Finset ℕ := fun b =>
    (oldSupports b).erase (newOption b)
  have holdErasedCard : ∀ b ∈ K,
      (oldErased b).card ≤ R := by
    intro b hb
    exact Finset.card_erase_le.trans
      (holdCard b (hKB hb))
  have hbNotErased : ∀ b ∈ K, b ∉ oldErased b := by
    intro b hb hbErased
    exact hbNotOld b (hKB hb) (Finset.mem_erase.mp hbErased).2
  have hnewNotErased : ∀ b ∈ K,
      newOption b ∉ oldErased b := by
    intro b hb
    simp [oldErased]
  obtain ⟨L, hLK, hL, havoidNew⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImage
      hK newOption hnewInj oldErased R holdErasedCard
        hbNotErased hnewNotErased
  refine ⟨L, hLK.trans hKB, hL, newOption,
    hnewInj.mono hLK, ?_, ?_⟩
  · intro b hb
    exact hnewData b (hLK hb)
  · intro b hb d hd hbd hnewOld
    have hnewNe : newOption d ≠ newOption b := by
      intro hEq
      exact hbd (hnewInj (hLK hd) (hLK hb) hEq).symm
    have hnewErased : newOption d ∈ oldErased b :=
      Finset.mem_erase.mpr ⟨hnewNe, hnewOld⟩
    exact (havoidNew b hb).2 d hd hnewErased

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

/-- A fourth coherent selector option can be added to the triply repaired
counterexample reservoir.  Choose `s b` injectively from the repair support
of `r b`, thin so all old repair supports avoid fourth options belonging to
other blocks, and then construct a self-repair `j b` for `s b` avoiding all
four option images. -/
theorem counterexample_forces_quadruplySelfRepairedOptionReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ S : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p r s : ℕ → ℕ, ∃ g h j : ℕ → Finset ℕ,
        0 ∈ S ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, p b ∈ f b \ S ∧ p b < b) ∧
        (∀ b ∈ B, r b ∈ g b \ S ∧ r b < p b) ∧
        (∀ b ∈ B, s b ∈ h b ∧ 0 < s b ∧ s b < r b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S)) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        (∀ b ∈ B,
          h b ∈ additiveSupportFamily A 3 (r b) ∧
          r b ∉ h b ∧ Disjoint (h b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ h b) ∧
          ∀ d ∈ B, r d ∉ h b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          s d ∉ (f b ∪ g b) ∪ h b) ∧
        ∀ b ∈ B,
          j b ∈ additiveSupportFamily A 3 (s b) ∧
          s b ∉ j b ∧ Disjoint (j b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ j b) ∧
          (∀ d ∈ B, r d ∉ j b) ∧
          ∀ d ∈ B, s d ∉ j b := by
  classical
  obtain ⟨B₀, hB₀A, hB₀, S, f, p, r, g, h,
      hzeroS, hwitness₀, hAvoid₀, hp₀, hr₀,
      hjoint₀, hg₀, hh₀⟩ :=
    counterexample_forces_triplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  have hpInj : Set.InjOn p B₀ := by
    intro b hb d hd hpd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hp₀ b hb).1).2⟩)
      (hpd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hp₀ d hd).1).2⟩)
  have hrInj : Set.InjOn r B₀ := by
    intro b hb d hd hrd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hr₀ b hb).1).2⟩)
      (hrd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hr₀ d hd).1).2⟩)
  obtain ⟨L, hLB₀, hL, s, hsInj, hsData⟩ :=
    exists_infinite_injectiveRepairPoint hB₀ r hrInj h
      (fun b hb => (hh₀ b hb).1)
      (fun b hb => (hh₀ b hb).2.1)
  let oldSupports : ℕ → Finset ℕ := fun b =>
    (f b ∪ g b) ∪ h b
  let oldSupportsErased : ℕ → Finset ℕ := fun b =>
    (oldSupports b).erase (s b)
  have holdCard : ∀ b ∈ L, (oldSupportsErased b).card ≤ 10 := by
    intro b hb
    have hbB₀ := hLB₀ hb
    obtain ⟨w, hfw⟩ := hwitness₀ b hbB₀
    have hfCard : (f b).card ≤ 4 := by
      rw [hfw]
      exact w.vertices_card_le_four
    have hgCard : (g b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (p b) (g b) (hg₀ b hbB₀).1
    have hhCard : (h b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (r b) (h b) (hh₀ b hbB₀).1
    have hunion : (oldSupports b).card ≤ 10 := by
      dsimp only [oldSupports]
      calc
        ((f b ∪ g b) ∪ h b).card ≤
            (f b ∪ g b).card + (h b).card :=
          Finset.card_union_le (f b ∪ g b) (h b)
        _ ≤ ((f b).card + (g b).card) + (h b).card :=
          Nat.add_le_add_right
            (Finset.card_union_le (f b) (g b)) (h b).card
        _ ≤ 10 := by omega
    exact (Finset.card_erase_le).trans hunion
  have hbNotOldErased : ∀ b ∈ L, b ∉ oldSupportsErased b := by
    intro b hb hbOld
    have hbB₀ := hLB₀ hb
    have hbUnion := (Finset.mem_erase.mp hbOld).2
    rcases Finset.mem_union.mp hbUnion with hbFG | hbH
    · rcases Finset.mem_union.mp hbFG with hbF | hbG
      · exact Set.disjoint_left.mp (hAvoid₀ b hbB₀)
          (Finset.mem_coe.mpr hbF) hbB₀
      · exact Set.disjoint_left.mp (hg₀ b hbB₀).2.2.1
          (Finset.mem_coe.mpr hbG) hbB₀
    · exact Set.disjoint_left.mp (hh₀ b hbB₀).2.2.1
        (Finset.mem_coe.mpr hbH) hbB₀
  have hsNotOldErased : ∀ b ∈ L, s b ∉ oldSupportsErased b := by
    intro b hb
    simp [oldSupportsErased]
  obtain ⟨L₁, hL₁L, hL₁, havoidS⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImage
      hL s hsInj oldSupportsErased 10 holdCard
        hbNotOldErased hsNotOldErased
  have hcrossS : ∀ b ∈ L₁, ∀ d ∈ L₁, b ≠ d →
      s d ∉ oldSupports b := by
    intro b hb d hd hbd hsdOld
    have hsdne : s d ≠ s b := by
      intro hEq
      exact hbd (hsInj (hL₁L hb) (hL₁L hd) hEq.symm)
    have hsdErase : s d ∈ oldSupportsErased b :=
      Finset.mem_erase.mpr ⟨hsdne, hsdOld⟩
    exact (havoidS b hb).2 d hd hsdErase
  have hsr : ∀ b ∈ L₁, s b < r b := by
    intro b hb
    exact (hsData b (hL₁L hb)).2.2
  have hsb : ∀ b ∈ L₁, s b < b := by
    intro b hb
    exact (hsr b hb).trans
      ((hr₀ b (hLB₀ (hL₁L hb))).2.trans
        (hp₀ b (hLB₀ (hL₁L hb))).2)
  obtain ⟨L₂, hL₂L₁, hL₂, j, hj₀⟩ :=
    exists_infinite_selfRepairedThirdOptions
      hbasis hL₁ r s
        (hrInj.mono (hL₁L.trans hLB₀))
        (hsInj.mono hL₁L) hsr hsb
  have hpNotJ : ∀ b ∈ L₂, p b ∉ j b := by
    intro b hb hpbJ
    have hpLe : p b ≤ s b :=
      additiveSupportFamily_supportsBounded A 3
        (s b) (j b) (hj₀ b hb).1 (p b) hpbJ
    have hsLessP : s b < p b :=
      (hsr b (hL₂L₁ hb)).trans
        (hr₀ b (hLB₀ (hL₁L (hL₂L₁ hb)))).2
    omega
  have hjCard : ∀ b ∈ L₂, (j b).card ≤ 3 := by
    intro b hb
    exact additiveSupportFamily_cardAtMost A 3
      (s b) (j b) (hj₀ b hb).1
  have hbNotJ : ∀ b ∈ L₂, b ∉ j b := by
    intro b hb hbJ
    exact Set.disjoint_left.mp (hj₀ b hb).2.2.1
      (Finset.mem_coe.mpr hbJ) hb
  obtain ⟨B, hBL₂, hB, havoidP⟩ :=
    exists_infinite_freeSet_avoiding_injectiveImage
      hL₂ p (hpInj.mono
        (hL₂L₁.trans (hL₁L.trans hLB₀)))
      j 3 hjCard hbNotJ hpNotJ
  have hBB₀ : B ⊆ B₀ :=
    hBL₂.trans (hL₂L₁.trans (hL₁L.trans hLB₀))
  refine ⟨B, hBB₀.trans hB₀A, hB, S, f, p, r, s, g, h, j,
    hzeroS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact hwitness₀ b (hBB₀ hb)
  · intro b hb
    exact (hAvoid₀ b (hBB₀ hb)).mono_right hBB₀
  · intro b hb
    exact hp₀ b (hBB₀ hb)
  · intro b hb
    exact hr₀ b (hBB₀ hb)
  · intro b hb
    exact hsData b (hL₁L (hL₂L₁ (hBL₂ hb)))
  · intro b hb d hd hbd
    exact hjoint₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hgb := hg₀ b (hBB₀ hb)
    exact ⟨hgb.1, hgb.2.1, hgb.2.2.1.mono_right hBB₀,
      fun d hd => hgb.2.2.2 d (hBB₀ hd)⟩
  · intro b hb
    have hhb := hh₀ b (hBB₀ hb)
    exact ⟨hhb.1, hhb.2.1, hhb.2.2.1.mono_right hBB₀,
      fun d hd => hhb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hhb.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossS b (hL₂L₁ (hBL₂ hb))
      d (hL₂L₁ (hBL₂ hd)) hbd
  · intro b hb
    have hjb := hj₀ b (hBL₂ hb)
    refine ⟨hjb.1, hjb.2.1, (havoidP b hb).1,
      (havoidP b hb).2, ?_, ?_⟩
    · intro d hd
      exact hjb.2.2.2.1 d (hBL₂ hd)
    · intro d hd
      exact hjb.2.2.2.2 d (hBL₂ hd)

/-- The fourth repaired reservoir extends once more.  Choose a fifth option
`u b` from `j b`, use the cross-avoidance thinning lemma on the union of all
old repair supports, and then construct a repair `k b` avoiding the four old
option images and every fifth option. -/
theorem counterexample_forces_quintuplySelfRepairedOptionReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ S : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p r s u : ℕ → ℕ, ∃ g h j k : ℕ → Finset ℕ,
        0 ∈ S ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, p b ∈ f b \ S ∧ p b < b) ∧
        (∀ b ∈ B, r b ∈ g b \ S ∧ r b < p b) ∧
        (∀ b ∈ B, s b ∈ h b ∧ 0 < s b ∧ s b < r b) ∧
        (∀ b ∈ B, u b ∈ j b ∧ 0 < u b ∧ u b < s b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S)) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        (∀ b ∈ B,
          h b ∈ additiveSupportFamily A 3 (r b) ∧
          r b ∉ h b ∧ Disjoint (h b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ h b) ∧
          ∀ d ∈ B, r d ∉ h b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          s d ∉ (f b ∪ g b) ∪ h b) ∧
        (∀ b ∈ B,
          j b ∈ additiveSupportFamily A 3 (s b) ∧
          s b ∉ j b ∧ Disjoint (j b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ j b) ∧
          (∀ d ∈ B, r d ∉ j b) ∧
          ∀ d ∈ B, s d ∉ j b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          u d ∉ ((f b ∪ g b) ∪ h b) ∪ j b) ∧
        ∀ b ∈ B,
          k b ∈ additiveSupportFamily A 3 (u b) ∧
          u b ∉ k b ∧ Disjoint (k b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ k b) ∧
          (∀ d ∈ B, r d ∉ k b) ∧
          (∀ d ∈ B, s d ∉ k b) ∧
          ∀ d ∈ B, u d ∉ k b := by
  classical
  obtain ⟨B₀, hB₀A, hB₀, S, f, p, r, s, g, h, j,
      hzeroS, hwitness₀, hAvoid₀, hp₀, hr₀, hs₀,
      hjoint₀, hg₀, hh₀, hcrossS₀, hj₀⟩ :=
    counterexample_forces_quadruplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  have hpInj : Set.InjOn p B₀ := by
    intro b hb d hd hpd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hp₀ b hb).1).2⟩)
      (hpd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hp₀ d hd).1).2⟩)
  have hrInj : Set.InjOn r B₀ := by
    intro b hb d hd hrd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hr₀ b hb).1).2⟩)
      (hrd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hr₀ d hd).1).2⟩)
  have hsInj : Set.InjOn s B₀ := by
    intro b hb d hd hsd
    by_contra hbd
    apply hcrossS₀ b hb d hd hbd
    rw [← hsd]
    exact Finset.mem_union_right _ (hs₀ b hb).1
  let oldSupports : ℕ → Finset ℕ := fun b =>
    ((f b ∪ g b) ∪ h b) ∪ j b
  have holdCard : ∀ b ∈ B₀, (oldSupports b).card ≤ 13 := by
    intro b hb
    obtain ⟨w, hfw⟩ := hwitness₀ b hb
    have hfCard : (f b).card ≤ 4 := by
      rw [hfw]
      exact w.vertices_card_le_four
    have hgCard : (g b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (p b) (g b) (hg₀ b hb).1
    have hhCard : (h b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (r b) (h b) (hh₀ b hb).1
    have hjCard : (j b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (s b) (j b) (hj₀ b hb).1
    dsimp only [oldSupports]
    calc
      (((f b ∪ g b) ∪ h b) ∪ j b).card ≤
          ((f b ∪ g b) ∪ h b).card + (j b).card :=
        Finset.card_union_le _ _
      _ ≤ ((f b ∪ g b).card + (h b).card) + (j b).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (((f b).card + (g b).card) + (h b).card) +
          (j b).card := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ 13 := by omega
  have hbNotOld : ∀ b ∈ B₀, b ∉ oldSupports b := by
    intro b hb hbOld
    rcases Finset.mem_union.mp hbOld with hbFGH | hbJ
    · rcases Finset.mem_union.mp hbFGH with hbFG | hbH
      · rcases Finset.mem_union.mp hbFG with hbF | hbG
        · exact Set.disjoint_left.mp (hAvoid₀ b hb)
            (Finset.mem_coe.mpr hbF) hb
        · exact Set.disjoint_left.mp (hg₀ b hb).2.2.1
            (Finset.mem_coe.mpr hbG) hb
      · exact Set.disjoint_left.mp (hh₀ b hb).2.2.1
          (Finset.mem_coe.mpr hbH) hb
    · exact Set.disjoint_left.mp (hj₀ b hb).2.2.1
        (Finset.mem_coe.mpr hbJ) hb
  obtain ⟨L, hLB₀, hL, u, huInj, huData, hcrossU⟩ :=
    exists_infinite_crossAvoidingRepairPoint
      hB₀ s hsInj j (fun b hb => (hj₀ b hb).1)
        (fun b hb => (hj₀ b hb).2.1)
        oldSupports 13 holdCard hbNotOld
  let oldOption : Fin 4 → ℕ → ℕ := fun a b =>
    ![b, p b, r b, s b] a
  have holdInj : ∀ a, Set.InjOn (oldOption a) L := by
    intro a
    fin_cases a
    · intro b hb d hd hbd
      simpa [oldOption] using hbd
    · exact hpInj.mono hLB₀
    · exact hrInj.mono hLB₀
    · exact hsInj.mono hLB₀
  have hub : ∀ b ∈ L, u b < b := by
    intro b hb
    exact (huData b hb).2.2 |>.trans
      ((hs₀ b (hLB₀ hb)).2.2.trans
        ((hr₀ b (hLB₀ hb)).2.trans (hp₀ b (hLB₀ hb)).2))
  have huOld : ∀ b ∈ L, ∀ a, u b < oldOption a b := by
    intro b hb a
    have hus := (huData b hb).2.2
    have hsr := (hs₀ b (hLB₀ hb)).2.2
    have hrp := (hr₀ b (hLB₀ hb)).2
    have hpb := (hp₀ b (hLB₀ hb)).2
    fin_cases a <;> simp [oldOption] <;> omega
  obtain ⟨B, hBL, hB, k, hk⟩ :=
    exists_infinite_selfRepair_avoiding_finiteOptions
      hbasis hL u huInj hub 4 oldOption holdInj huOld
  have hBB₀ : B ⊆ B₀ := hBL.trans hLB₀
  refine ⟨B, hBB₀.trans hB₀A, hB, S, f, p, r, s, u,
    g, h, j, k, hzeroS, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact hwitness₀ b (hBB₀ hb)
  · intro b hb
    exact (hAvoid₀ b (hBB₀ hb)).mono_right hBB₀
  · intro b hb
    exact hp₀ b (hBB₀ hb)
  · intro b hb
    exact hr₀ b (hBB₀ hb)
  · intro b hb
    exact hs₀ b (hBB₀ hb)
  · intro b hb
    exact huData b (hBL hb)
  · intro b hb d hd hbd
    exact hjoint₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hgb := hg₀ b (hBB₀ hb)
    exact ⟨hgb.1, hgb.2.1, hgb.2.2.1.mono_right hBB₀,
      fun d hd => hgb.2.2.2 d (hBB₀ hd)⟩
  · intro b hb
    have hhb := hh₀ b (hBB₀ hb)
    exact ⟨hhb.1, hhb.2.1, hhb.2.2.1.mono_right hBB₀,
      fun d hd => hhb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hhb.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossS₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hjb := hj₀ b (hBB₀ hb)
    exact ⟨hjb.1, hjb.2.1, hjb.2.2.1.mono_right hBB₀,
      fun d hd => hjb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hjb.2.2.2.2.1 d (hBB₀ hd),
      fun d hd => hjb.2.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossU b (hBL hb) d (hBL hd) hbd
  · intro b hb
    have hkb := hk b hb
    refine ⟨hkb.1, hkb.2.1, hkb.2.2.1,
      ?_, ?_, ?_, hkb.2.2.2.1⟩
    · intro d hd
      simpa [oldOption] using hkb.2.2.2.2 (1 : Fin 4) d hd
    · intro d hd
      simpa [oldOption] using hkb.2.2.2.2 (2 : Fin 4) d hd
    · intro d hd
      simpa [oldOption] using hkb.2.2.2.2 (3 : Fin 4) d hd

/- The five-layer reservoir can be extended once more by exactly the same
finite-injury mechanism.  Choose `v b` from the terminal repair `k b`, thin
so that these choices avoid all five older support layers off the diagonal,
and then give `v b` a repair `l b` avoiding all six option images.  Keeping
this statement explicit is useful for testing that the repaired-option
tower really passes the first equality threshold of the finite-certificate
bound. -/
theorem counterexample_forces_sextuplySelfRepairedOptionReservoir
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      ∃ S : Finset ℕ, ∃ f : ℕ → Finset ℕ,
      ∃ p r s u v : ℕ → ℕ, ∃ g h j k l : ℕ → Finset ℕ,
        0 ∈ S ∧
        (∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
          f b = w.vertices) ∧
        (∀ b ∈ B, Disjoint (f b : Set ℕ) B) ∧
        (∀ b ∈ B, p b ∈ f b \ S ∧ p b < b) ∧
        (∀ b ∈ B, r b ∈ g b \ S ∧ r b < p b) ∧
        (∀ b ∈ B, s b ∈ h b ∧ 0 < s b ∧ s b < r b) ∧
        (∀ b ∈ B, u b ∈ j b ∧ 0 < u b ∧ u b < s b) ∧
        (∀ b ∈ B, v b ∈ k b ∧ 0 < v b ∧ v b < u b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          Disjoint ((f b ∪ g b) \ S) ((f d ∪ g d) \ S)) ∧
        (∀ b ∈ B,
          g b ∈ additiveSupportFamily A 3 (p b) ∧
          p b ∉ g b ∧ Disjoint (g b : Set ℕ) B ∧
          ∀ d ∈ B, p d ∉ g b) ∧
        (∀ b ∈ B,
          h b ∈ additiveSupportFamily A 3 (r b) ∧
          r b ∉ h b ∧ Disjoint (h b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ h b) ∧
          ∀ d ∈ B, r d ∉ h b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          s d ∉ (f b ∪ g b) ∪ h b) ∧
        (∀ b ∈ B,
          j b ∈ additiveSupportFamily A 3 (s b) ∧
          s b ∉ j b ∧ Disjoint (j b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ j b) ∧
          (∀ d ∈ B, r d ∉ j b) ∧
          ∀ d ∈ B, s d ∉ j b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          u d ∉ ((f b ∪ g b) ∪ h b) ∪ j b) ∧
        (∀ b ∈ B,
          k b ∈ additiveSupportFamily A 3 (u b) ∧
          u b ∉ k b ∧ Disjoint (k b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ k b) ∧
          (∀ d ∈ B, r d ∉ k b) ∧
          (∀ d ∈ B, s d ∉ k b) ∧
          ∀ d ∈ B, u d ∉ k b) ∧
        (∀ b ∈ B, ∀ d ∈ B, b ≠ d →
          v d ∉ (((f b ∪ g b) ∪ h b) ∪ j b) ∪ k b) ∧
        ∀ b ∈ B,
          l b ∈ additiveSupportFamily A 3 (v b) ∧
          v b ∉ l b ∧ Disjoint (l b : Set ℕ) B ∧
          (∀ d ∈ B, p d ∉ l b) ∧
          (∀ d ∈ B, r d ∉ l b) ∧
          (∀ d ∈ B, s d ∉ l b) ∧
          (∀ d ∈ B, u d ∉ l b) ∧
          ∀ d ∈ B, v d ∉ l b := by
  classical
  obtain ⟨B₀, hB₀A, hB₀, S, f, p, r, s, u, g, h, j, k,
      hzeroS, hwitness₀, hAvoid₀, hp₀, hr₀, hs₀, hu₀,
      hjoint₀, hg₀, hh₀, hcrossS₀, hj₀, hcrossU₀, hk₀⟩ :=
    counterexample_forces_quintuplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  have hpInj : Set.InjOn p B₀ := by
    intro b hb d hd hpd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hp₀ b hb).1).2⟩)
      (hpd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hp₀ d hd).1).2⟩)
  have hrInj : Set.InjOn r B₀ := by
    intro b hb d hd hrd
    by_contra hbd
    exact Finset.disjoint_left.mp
      (hjoint₀ b hb d hd hbd)
      (Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ b hb).1).1,
          (Finset.mem_sdiff.mp (hr₀ b hb).1).2⟩)
      (hrd ▸ Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr₀ d hd).1).1,
          (Finset.mem_sdiff.mp (hr₀ d hd).1).2⟩)
  have hsInj : Set.InjOn s B₀ := by
    intro b hb d hd hsd
    by_contra hbd
    apply hcrossS₀ b hb d hd hbd
    rw [← hsd]
    exact Finset.mem_union_right _ (hs₀ b hb).1
  have huInj : Set.InjOn u B₀ := by
    intro b hb d hd hud
    by_contra hbd
    apply hcrossU₀ b hb d hd hbd
    rw [← hud]
    exact Finset.mem_union_right _ (hu₀ b hb).1
  let oldSupports : ℕ → Finset ℕ := fun b =>
    (((f b ∪ g b) ∪ h b) ∪ j b) ∪ k b
  have holdCard : ∀ b ∈ B₀, (oldSupports b).card ≤ 16 := by
    intro b hb
    obtain ⟨w, hfw⟩ := hwitness₀ b hb
    have hfCard : (f b).card ≤ 4 := by
      rw [hfw]
      exact w.vertices_card_le_four
    have hgCard : (g b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (p b) (g b) (hg₀ b hb).1
    have hhCard : (h b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (r b) (h b) (hh₀ b hb).1
    have hjCard : (j b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (s b) (j b) (hj₀ b hb).1
    have hkCard : (k b).card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3
        (u b) (k b) (hk₀ b hb).1
    dsimp only [oldSupports]
    calc
      ((((f b ∪ g b) ∪ h b) ∪ j b) ∪ k b).card ≤
          (((f b ∪ g b) ∪ h b) ∪ j b).card + (k b).card :=
        Finset.card_union_le _ _
      _ ≤ (((f b ∪ g b) ∪ h b).card + (j b).card) +
          (k b).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (((f b ∪ g b).card + (h b).card) + (j b).card) +
          (k b).card := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ ((((f b).card + (g b).card) + (h b).card) +
          (j b).card) + (k b).card := by
        exact Nat.add_le_add_right
          (Nat.add_le_add_right
            (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _
      _ ≤ 16 := by omega
  have hbNotOld : ∀ b ∈ B₀, b ∉ oldSupports b := by
    intro b hb hbOld
    rcases Finset.mem_union.mp hbOld with hbFGHJ | hbK
    · rcases Finset.mem_union.mp hbFGHJ with hbFGH | hbJ
      · rcases Finset.mem_union.mp hbFGH with hbFG | hbH
        · rcases Finset.mem_union.mp hbFG with hbF | hbG
          · exact Set.disjoint_left.mp (hAvoid₀ b hb)
              (Finset.mem_coe.mpr hbF) hb
          · exact Set.disjoint_left.mp (hg₀ b hb).2.2.1
              (Finset.mem_coe.mpr hbG) hb
        · exact Set.disjoint_left.mp (hh₀ b hb).2.2.1
            (Finset.mem_coe.mpr hbH) hb
      · exact Set.disjoint_left.mp (hj₀ b hb).2.2.1
          (Finset.mem_coe.mpr hbJ) hb
    · exact Set.disjoint_left.mp (hk₀ b hb).2.2.1
        (Finset.mem_coe.mpr hbK) hb
  obtain ⟨L, hLB₀, hL, v, hvInj, hvData, hcrossV⟩ :=
    exists_infinite_crossAvoidingRepairPoint
      hB₀ u huInj k (fun b hb => (hk₀ b hb).1)
        (fun b hb => (hk₀ b hb).2.1)
        oldSupports 16 holdCard hbNotOld
  let oldOption : Fin 5 → ℕ → ℕ := fun a b =>
    ![b, p b, r b, s b, u b] a
  have holdInj : ∀ a, Set.InjOn (oldOption a) L := by
    intro a
    fin_cases a
    · intro b hb d hd hbd
      simpa [oldOption] using hbd
    · exact hpInj.mono hLB₀
    · exact hrInj.mono hLB₀
    · exact hsInj.mono hLB₀
    · exact huInj.mono hLB₀
  have hvb : ∀ b ∈ L, v b < b := by
    intro b hb
    exact (hvData b hb).2.2 |>.trans
      ((hu₀ b (hLB₀ hb)).2.2.trans
        ((hs₀ b (hLB₀ hb)).2.2.trans
          ((hr₀ b (hLB₀ hb)).2.trans
            (hp₀ b (hLB₀ hb)).2)))
  have hvOld : ∀ b ∈ L, ∀ a, v b < oldOption a b := by
    intro b hb a
    have hvu := (hvData b hb).2.2
    have hus := (hu₀ b (hLB₀ hb)).2.2
    have hsr := (hs₀ b (hLB₀ hb)).2.2
    have hrp := (hr₀ b (hLB₀ hb)).2
    have hpb := (hp₀ b (hLB₀ hb)).2
    fin_cases a <;> simp [oldOption] <;> omega
  obtain ⟨B, hBL, hB, l, hl⟩ :=
    exists_infinite_selfRepair_avoiding_finiteOptions
      hbasis hL v hvInj hvb 5 oldOption holdInj hvOld
  have hBB₀ : B ⊆ B₀ := hBL.trans hLB₀
  refine ⟨B, hBB₀.trans hB₀A, hB, S, f, p, r, s, u, v,
    g, h, j, k, l, hzeroS, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact hwitness₀ b (hBB₀ hb)
  · intro b hb
    exact (hAvoid₀ b (hBB₀ hb)).mono_right hBB₀
  · intro b hb
    exact hp₀ b (hBB₀ hb)
  · intro b hb
    exact hr₀ b (hBB₀ hb)
  · intro b hb
    exact hs₀ b (hBB₀ hb)
  · intro b hb
    exact hu₀ b (hBB₀ hb)
  · intro b hb
    exact hvData b (hBL hb)
  · intro b hb d hd hbd
    exact hjoint₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hgb := hg₀ b (hBB₀ hb)
    exact ⟨hgb.1, hgb.2.1, hgb.2.2.1.mono_right hBB₀,
      fun d hd => hgb.2.2.2 d (hBB₀ hd)⟩
  · intro b hb
    have hhb := hh₀ b (hBB₀ hb)
    exact ⟨hhb.1, hhb.2.1, hhb.2.2.1.mono_right hBB₀,
      fun d hd => hhb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hhb.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossS₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hjb := hj₀ b (hBB₀ hb)
    exact ⟨hjb.1, hjb.2.1, hjb.2.2.1.mono_right hBB₀,
      fun d hd => hjb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hjb.2.2.2.2.1 d (hBB₀ hd),
      fun d hd => hjb.2.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossU₀ b (hBB₀ hb) d (hBB₀ hd) hbd
  · intro b hb
    have hkb := hk₀ b (hBB₀ hb)
    exact ⟨hkb.1, hkb.2.1, hkb.2.2.1.mono_right hBB₀,
      fun d hd => hkb.2.2.2.1 d (hBB₀ hd),
      fun d hd => hkb.2.2.2.2.1 d (hBB₀ hd),
      fun d hd => hkb.2.2.2.2.2.1 d (hBB₀ hd),
      fun d hd => hkb.2.2.2.2.2.2 d (hBB₀ hd)⟩
  · intro b hb d hd hbd
    exact hcrossV b (hBL hb) d (hBL hd) hbd
  · intro b hb
    have hlb := hl b hb
    refine ⟨hlb.1, hlb.2.1, hlb.2.2.1,
      ?_, ?_, ?_, ?_, hlb.2.2.2.1⟩
    · intro d hd
      simpa [oldOption] using hlb.2.2.2.2 (1 : Fin 5) d hd
    · intro d hd
      simpa [oldOption] using hlb.2.2.2.2 (2 : Fin 5) d hd
    · intro d hd
      simpa [oldOption] using hlb.2.2.2.2 (3 : Fin 5) d hd
    · intro d hd
      simpa [oldOption] using hlb.2.2.2.2 (4 : Fin 5) d hd

/-- A finite menu of selector options attached to an atom.  This is the
cell interface used by the repaired-option tower: the atom is kept separate
from the finite set of non-atom options. -/
def atomOptionCell
    (optionSet : ℕ → Finset ℕ) (b : ℕ) : Finset ℕ :=
  insert b (optionSet b)

/-- Pairwise-disjoint finite option menus, all outside the atom reservoir,
extend to dedicated cores of a finite-block partition.  The construction is
independent of the number of options, so later repair layers only need to
verify the option-set interface. -/
theorem exists_finiteBlockPartition_for_atomOptionCells
    {A B : Set ℕ}
    (hBA : B ⊆ A) (hB : B.Infinite)
    (optionSet : ℕ → Finset ℕ)
    (hoptionA : ∀ b ∈ B, (optionSet b : Set ℕ) ⊆ A)
    (hoptionOut : ∀ b ∈ B,
      Disjoint (optionSet b : Set ℕ) B)
    (hoptionDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (optionSet b) (optionSet d)) :
    ∃ e : ℕ ≃ B, ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, atomOptionCell optionSet (e i).1 ⊆ F i) ∧
      ∀ i, (atomOptionCell optionSet (e i).1).card =
        (optionSet (e i).1).card + 1 := by
  classical
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let cell : ℕ → Finset ℕ := fun i =>
    atomOptionCell optionSet (e i).1
  have hcellA : ∀ i, (cell i : Set ℕ) ⊆ A := by
    intro i x hx
    rcases Finset.mem_insert.mp hx with hxb | hxOption
    · exact hxb ▸ hBA (e i).2
    · exact hoptionA (e i).1 (e i).2 hxOption
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
      exact Set.disjoint_left.mp
        (hoptionOut (e j).1 (e j).2)
        (Finset.mem_coe.mpr hxjOption) (e i).2
    · subst x
      exact Set.disjoint_left.mp
        (hoptionOut (e i).1 (e i).2)
        (Finset.mem_coe.mpr hxiOption) (e j).2
    · exact Finset.disjoint_left.mp
        (hoptionDisjoint (e i).1 (e i).2
          (e j).1 (e j).2 hbij)
        hxiOption hxjOption
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  refine ⟨e, F, P, hcore, ?_⟩
  intro i
  have hAtomOut : (e i).1 ∉ optionSet (e i).1 := by
    intro hmem
    exact Set.disjoint_left.mp
      (hoptionOut (e i).1 (e i).2)
      (Finset.mem_coe.mpr hmem) (e i).2
  rw [atomOptionCell, Finset.card_insert_of_notMem hAtomOut]

/-- The three non-atom options in the fourth repaired layer. -/
def threeRepairOptionSet
    (p r s : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  {p b, r b, s b}

/-- The exact four-point core supplied by the fourth repaired layer. -/
def fourRepairedOptionCell
    (p r s : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  atomOptionCell (threeRepairOptionSet p r s) b

/-- Strict descent through the three repaired non-atom options makes the
four-option core genuinely four-point. -/
theorem fourRepairedOptionCell_card
    {p r s : ℕ → ℕ} {b : ℕ}
    (hsr : s b < r b) (hrp : r b < p b) (hpb : p b < b) :
    (fourRepairedOptionCell p r s b).card = 4 := by
  have hbp : b ≠ p b := Nat.ne_of_gt hpb
  have hbr : b ≠ r b := Nat.ne_of_gt (hrp.trans hpb)
  have hbs : b ≠ s b := Nat.ne_of_gt (hsr.trans (hrp.trans hpb))
  have hpr : p b ≠ r b := Nat.ne_of_gt hrp
  have hps : p b ≠ s b := Nat.ne_of_gt (hsr.trans hrp)
  have hrs : r b ≠ s b := Nat.ne_of_gt hsr
  simp [fourRepairedOptionCell, atomOptionCell, threeRepairOptionSet,
    hbp, hbr, hbs, hpr, hps, hrs]

/-- Generic internal-survival lemma for a finite (or arbitrary indexed)
menu of repaired options in each block.  A selected internal target uses its
assigned repair.  An unselected target uses the zero-padded canonical pair.
The only same-block selected value is the target itself, while repairs are
assumed to avoid every option belonging to a different block. -/
theorem internalTarget_survives_repairedOptionSelector
    {A : Set ℕ} {F : ℕ → Finset ℕ} {ι : Type*}
    (hzeroA : 0 ∈ A)
    (option : ℕ → ι → ℕ)
    (repair : ℕ → ι → Finset ℕ)
    (hoptionZero : ∀ i a, option i a ≠ 0)
    (hrepair : ∀ i a,
      repair i a ∈ additiveSupportFamily A 3 (option i a))
    (hrepairSelf : ∀ i a, option i a ∉ repair i a)
    (hrepairCross : ∀ i j, i ≠ j → ∀ a b,
      option j b ∉ repair i a)
    (s : BlockSelector F)
    (hsOption : ∀ i, ∃ a, (s i).1 = option i a) :
    ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
      Disjoint (G : Set ℕ) (selectedSet s) := by
  classical
  have hzeroSelected : 0 ∉ selectedSet s := by
    rintro ⟨i, hi⟩
    obtain ⟨a, hsa⟩ := hsOption i
    have hzeroOption : option i a = 0 := by
      exact hsa.symm.trans hi
    exact hoptionZero i a hzeroOption
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
  · obtain ⟨i, hiq⟩ := hqSelected
    obtain ⟨a, hsa⟩ := hsOption i
    have hqOption : q = option i a := hiq.symm.trans hsa
    refine ⟨repair i a, hqOption ▸ hrepair i a, ?_⟩
    rw [Set.disjoint_left]
    intro x hxRepair hxSelected
    obtain ⟨j, hjx⟩ := hxSelected
    obtain ⟨b, hsb⟩ := hsOption j
    by_cases hij : i = j
    · subst j
      have hxOption : x = option i a := hjx.symm.trans hsa
      exact hrepairSelf i a
        (Finset.mem_coe.mp (hxOption ▸ hxRepair))
    · have hxOther : x = option j b := hjx.symm.trans hsb
      exact hrepairCross i j hij a b
        (Finset.mem_coe.mp (hxOther ▸ hxRepair))
  · exact htrivial q hqA hqSelected

/-- The finite-layer invariant suggested by the repaired-option tower.
Each block has `k` distinct internal options, options from different blocks
are disjoint, and every option owns an order-three repair which avoids itself
and every option in every other block. -/
structure RepairedOptionSystem (A : Set ℕ) (k : ℕ) where
  option : ℕ → Fin k → ℕ
  repair : ℕ → Fin k → Finset ℕ
  option_mem : ∀ i a, option i a ∈ A
  option_ne_zero : ∀ i a, option i a ≠ 0
  option_injective : ∀ i, Function.Injective (option i)
  option_cross : ∀ i j, i ≠ j → ∀ a b,
    option i a ≠ option j b
  repair_mem : ∀ i a,
    repair i a ∈ additiveSupportFamily A 3 (option i a)
  repair_self : ∀ i a, option i a ∉ repair i a
  repair_cross : ∀ i j, i ≠ j → ∀ a b,
    option j b ∉ repair i a

namespace RepairedOptionSystem

/-- The exact finite option cell of an abstract repaired-option system. -/
def cell {A : Set ℕ} {k : ℕ}
    (T : RepairedOptionSystem A k) (i : ℕ) : Finset ℕ :=
  Finset.univ.image (T.option i)

/- Restrict a repaired-option system to an injectively reindexed family of
blocks.  All within-block data are inherited, while cross-block conditions
follow from injectivity of the reindexing map. -/
def reindex {A : Set ℕ} {k : ℕ}
    (T : RepairedOptionSystem A k)
    (e : ℕ → ℕ) (he : Function.Injective e) :
    RepairedOptionSystem A k where
  option i a := T.option (e i) a
  repair i a := T.repair (e i) a
  option_mem i a := T.option_mem (e i) a
  option_ne_zero i a := T.option_ne_zero (e i) a
  option_injective i := T.option_injective (e i)
  option_cross i j hij a b :=
    T.option_cross (e i) (e j) (fun h => hij (he h)) a b
  repair_mem i a := T.repair_mem (e i) a
  repair_self i a := T.repair_self (e i) a
  repair_cross i j hij a b :=
    T.repair_cross (e i) (e j) (fun h => hij (he h)) a b

/-- Any nonempty repaired-option system gives exact `k`-point dedicated
cores of a finite-block partition, and every selector restricted to those
cores preserves every internal target.  Thus all finite-certificate work
after this point is independent of how the option tower was constructed. -/
theorem exists_finiteBlockPartition_and_internalSurvival
    {A : Set ℕ} {k : ℕ}
    (hzeroA : 0 ∈ A)
    (T : RepairedOptionSystem A k) (hk : 0 < k) :
    ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, T.cell i ⊆ F i) ∧
      (∀ i, (T.cell i).card = k) ∧
      ∀ sel : BlockSelector F,
        (∀ i, (sel i).1 ∈ T.cell i) →
        ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
          Disjoint (G : Set ℕ) (selectedSet sel) := by
  classical
  have hcellA : ∀ i, (T.cell i : Set ℕ) ⊆ A := by
    intro i x hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact T.option_mem i a
  have hcellNonempty : ∀ i, (T.cell i).Nonempty := by
    intro i
    let a : Fin k := ⟨0, hk⟩
    exact ⟨T.option i a, Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hcellDisjoint : Pairwise fun i j =>
      Disjoint (T.cell i) (T.cell j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hxi
    obtain ⟨b, _hb, hbx⟩ := Finset.mem_image.mp hxj
    exact T.option_cross i j hij a b (hax.trans hbx.symm)
  obtain ⟨F, P, hcore⟩ :=
    exists_finiteBlockPartition_extending_disjointCells
      hcellA hcellNonempty hcellDisjoint
  have hcellCard : ∀ i, (T.cell i).card = k := by
    intro i
    calc
      (T.cell i).card = (Finset.univ : Finset (Fin k)).card := by
        exact Finset.card_image_iff.mpr
          (T.option_injective i).injOn
      _ = k := Finset.card_fin k
  refine ⟨F, P, hcore, hcellCard, ?_⟩
  intro sel hsel
  have hselOption : ∀ i, ∃ a, (sel i).1 = T.option i a := by
    intro i
    obtain ⟨a, _ha, ha⟩ := Finset.mem_image.mp (hsel i)
    exact ⟨a, ha.symm⟩
  exact internalTarget_survives_repairedOptionSelector
    hzeroA
    T.option T.repair T.option_ne_zero T.repair_mem
      T.repair_self T.repair_cross sel hselOption

/-- Inductive interface for adding one new coherent option to every block.
The hypotheses list exactly the extension obligations: the new option must
be distinct from old options, old and new options must remain cross-block
disjoint, the new repair must avoid all other-block options, and every old
repair must avoid the new options of other blocks. -/
def prepend
    {A : Set ℕ} {k : ℕ}
    (T : RepairedOptionSystem A k)
    (newOption : ℕ → ℕ) (newRepair : ℕ → Finset ℕ)
    (hnewMem : ∀ i, newOption i ∈ A)
    (hnewZero : ∀ i, newOption i ≠ 0)
    (hnewOldSame : ∀ i a, newOption i ≠ T.option i a)
    (hnewCross : ∀ i j, i ≠ j → newOption i ≠ newOption j)
    (hnewOldCross : ∀ i j, i ≠ j → ∀ a,
      newOption i ≠ T.option j a)
    (hnewRepairMem : ∀ i,
      newRepair i ∈ additiveSupportFamily A 3 (newOption i))
    (hnewRepairSelf : ∀ i, newOption i ∉ newRepair i)
    (hnewRepairAvoidNew : ∀ i j, i ≠ j →
      newOption j ∉ newRepair i)
    (hnewRepairAvoidOld : ∀ i j, i ≠ j → ∀ a,
      T.option j a ∉ newRepair i)
    (holdRepairAvoidNew : ∀ i j, i ≠ j → ∀ a,
      newOption j ∉ T.repair i a) :
    RepairedOptionSystem A k.succ := by
  let option : ℕ → Fin k.succ → ℕ := fun i =>
    Fin.cases (newOption i) (T.option i)
  let repair : ℕ → Fin k.succ → Finset ℕ := fun i =>
    Fin.cases (newRepair i) (T.repair i)
  refine {
    option := option
    repair := repair
    option_mem := ?_
    option_ne_zero := ?_
    option_injective := ?_
    option_cross := ?_
    repair_mem := ?_
    repair_self := ?_
    repair_cross := ?_
  }
  · intro i a
    refine Fin.cases (hnewMem i) (fun a => T.option_mem i a) a
  · intro i a
    refine Fin.cases (hnewZero i) (fun a => T.option_ne_zero i a) a
  · intro i a b
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro _hab
        rfl
      · intro hab
        exact (hnewOldSame i b hab).elim
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro hab
        exact (hnewOldSame i a hab.symm).elim
      · intro hab
        exact congrArg Fin.succ (T.option_injective i hab)
  · intro i j hij a b
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact hnewCross i j hij
      · simpa [option] using hnewOldCross i j hij b
    · refine Fin.cases ?_ (fun b => ?_) b
      · intro hab
        exact hnewOldCross j i hij.symm a hab.symm
      · exact T.option_cross i j hij a b
  · intro i a
    refine Fin.cases (hnewRepairMem i) (fun a => T.repair_mem i a) a
  · intro i a
    refine Fin.cases (hnewRepairSelf i) (fun a => T.repair_self i a) a
  · intro i j hij a b
    refine Fin.cases ?_ (fun a => ?_) a
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact hnewRepairAvoidNew i j hij
      · simpa [option, repair] using hnewRepairAvoidOld i j hij b
    · refine Fin.cases ?_ (fun b => ?_) b
      · exact holdRepairAvoidNew i j hij a
      · exact T.repair_cross i j hij a b

set_option maxHeartbeats 5000000 in
/- An abstract repaired-option system with a pointwise least option can be
extended by one layer after passing to an infinite subsequence of blocks.
The new option is chosen from the least option's self-avoiding repair.  Two
bounded free-set thinnings make old repairs avoid the new option image and
make the new repairs avoid every old and new option image off the diagonal.
`prepend` then verifies the complete system invariant. -/
theorem exists_prepend_of_pointwiseMinimum
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (T : RepairedOptionSystem A k) (terminal : Fin k)
    (hminimum : ∀ i a,
      T.option i terminal ≤ T.option i a) :
    ∃ T' : RepairedOptionSystem A k.succ,
      ∀ i a, T'.option i 0 ≤ T'.option i a := by
  classical
  let target : ℕ → ℕ := fun i => T.option i terminal
  let parentRepair : ℕ → Finset ℕ := fun i => T.repair i terminal
  have htargetInj : Set.InjOn target Set.univ := by
    intro i _hi j _hj hij
    by_contra hne
    exact T.option_cross i j hne terminal terminal hij
  have hparentR : ∀ i ∈ (Set.univ : Set ℕ),
      parentRepair i ∈ additiveSupportFamily A 3 (target i) := by
    intro i _hi
    exact T.repair_mem i terminal
  have hparentSelf : ∀ i ∈ (Set.univ : Set ℕ),
      target i ∉ parentRepair i := by
    intro i _hi
    exact T.repair_self i terminal
  obtain ⟨K, _hKuniv, hK, newOption, hnewInj, hnewData⟩ :=
    exists_infinite_injectiveRepairPoint
      (A := A) Set.infinite_univ target htargetInj parentRepair
        hparentR hparentSelf
  let oldSupports : ℕ → Finset ℕ := fun i =>
    (Finset.univ : Finset (Fin k)).biUnion (T.repair i)
  have holdCard : ∀ i ∈ K, (oldSupports i).card ≤ 3 * k := by
    intro i hi
    calc
      (oldSupports i).card ≤
          ∑ a ∈ (Finset.univ : Finset (Fin k)),
            (T.repair i a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ (Finset.univ : Finset (Fin k)), 3 := by
        apply Finset.sum_le_sum
        intro a _ha
        exact additiveSupportFamily_cardAtMost A 3
          (T.option i a) (T.repair i a) (T.repair_mem i a)
      _ = 3 * k := by simp [Nat.mul_comm]
  obtain ⟨L, hLK, hL, holdAvoidNew⟩ :=
    exists_infinite_crossAvoiding_injectiveImage
      hK newOption hnewInj oldSupports (3 * k) holdCard
  obtain ⟨R, hselfAvoid⟩ :=
    eventually_selfAvoidingTripleSupport_of_orderTwoBasis
      (A := A) hbasis
  let Low : Set ℕ := {i | i ∈ L ∧ newOption i < R}
  have hLowFinite : Low.Finite := by
    apply Set.Finite.of_finite_image (f := newOption)
    · apply (Set.finite_Iio R).subset
      rintro y ⟨i, hiLow, rfl⟩
      exact hiLow.2
    · exact hnewInj.mono (fun _ hi => hLK hi.1)
  let K₁ : Set ℕ := L \ Low
  have hK₁L : K₁ ⊆ L := Set.diff_subset
  have hK₁ : K₁.Infinite := hL.diff hLowFinite
  have hnewLarge : ∀ i ∈ K₁, R ≤ newOption i := by
    intro i hi
    by_contra hnot
    exact hi.2 ⟨hi.1, Nat.lt_of_not_ge hnot⟩
  have hrepairExists : ∀ i : K₁, ∃ H,
      H ∈ additiveSupportFamily A 3 (newOption i.1) ∧
      newOption i.1 ∉ H := by
    intro i
    exact hselfAvoid (newOption i.1) (hnewLarge i.1 i.2)
  choose chosen hchosenMem hchosenSelf using hrepairExists
  let newRepair : ℕ → Finset ℕ := fun i =>
    if hi : i ∈ K₁ then chosen ⟨i, hi⟩ else ∅
  have hnewRepairMem₁ : ∀ i ∈ K₁,
      newRepair i ∈ additiveSupportFamily A 3 (newOption i) := by
    intro i hi
    simpa [newRepair, hi] using hchosenMem ⟨i, hi⟩
  have hnewRepairSelf₁ : ∀ i ∈ K₁,
      newOption i ∉ newRepair i := by
    intro i hi
    simpa [newRepair, hi] using hchosenSelf ⟨i, hi⟩
  have hnewRepairCard : ∀ i ∈ K₁, (newRepair i).card ≤ 3 := by
    intro i hi
    exact additiveSupportFamily_cardAtMost A 3
      (newOption i) (newRepair i) (hnewRepairMem₁ i hi)
  let allOption : Fin k.succ → ℕ → ℕ := fun a i =>
    Fin.cases (newOption i) (T.option i) a
  have hallInj : ∀ a, Set.InjOn (allOption a) K₁ := by
    intro a
    refine Fin.cases ?_ (fun a => ?_) a
    · exact hnewInj.mono (hK₁L.trans hLK)
    · intro i hi j hj hij
      by_contra hne
      exact T.option_cross i j hne a a hij
  obtain ⟨M, hMK₁, hM, hnewRepairAvoid⟩ :=
    exists_infinite_crossAvoiding_injectiveImages
      hK₁ k.succ allOption hallInj newRepair 3 hnewRepairCard
  letI : Infinite M := hM.to_subtype
  letI : Denumerable M := Denumerable.ofEncodableOfInfinite M
  let e : ℕ ≃ M := (Denumerable.eqv M).symm
  let idx : ℕ → ℕ := fun i => (e i).1
  have hidxInj : Function.Injective idx := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hidxM : ∀ i, idx i ∈ M := fun i => (e i).2
  have hidxK₁ : ∀ i, idx i ∈ K₁ := fun i => hMK₁ (hidxM i)
  have hidxL : ∀ i, idx i ∈ L := fun i => hK₁L (hidxK₁ i)
  have hidxK : ∀ i, idx i ∈ K := fun i => hLK (hidxL i)
  let Tsub : RepairedOptionSystem A k := T.reindex idx hidxInj
  let newOptionSub : ℕ → ℕ := fun i => newOption (idx i)
  let newRepairSub : ℕ → Finset ℕ := fun i => newRepair (idx i)
  have hnewMem : ∀ i, newOptionSub i ∈ A := by
    intro i
    exact additiveSupportFamily_supportsIn A 3
      (target (idx i)) (parentRepair (idx i))
      (hparentR (idx i) (Set.mem_univ _))
      (newOptionSub i) (hnewData (idx i) (hidxK i)).1
  have hnewZero : ∀ i, newOptionSub i ≠ 0 := by
    intro i
    exact Nat.ne_of_gt (hnewData (idx i) (hidxK i)).2.1
  have hnewOldLt : ∀ i a,
      newOptionSub i < Tsub.option i a := by
    intro i a
    exact (hnewData (idx i) (hidxK i)).2.2.trans_le
      (hminimum (idx i) a)
  have hnewOldSame : ∀ i a,
      newOptionSub i ≠ Tsub.option i a := by
    intro i a
    exact Nat.ne_of_lt (hnewOldLt i a)
  have hnewCross : ∀ i j, i ≠ j →
      newOptionSub i ≠ newOptionSub j := by
    intro i j hij hEq
    apply hij
    apply hidxInj
    exact hnewInj (hidxK i) (hidxK j) hEq
  have hnewOldCross : ∀ i j, i ≠ j → ∀ a,
      newOptionSub i ≠ Tsub.option j a := by
    intro i j hij a hEq
    have hidxne : idx i ≠ idx j := fun h => hij (hidxInj h)
    change newOption (idx i) = T.option (idx j) a at hEq
    apply T.repair_cross (idx i) (idx j) hidxne terminal a
    rw [← hEq]
    exact (hnewData (idx i) (hidxK i)).1
  have hnewRepairMem : ∀ i,
      newRepairSub i ∈ additiveSupportFamily A 3 (newOptionSub i) := by
    intro i
    exact hnewRepairMem₁ (idx i) (hidxK₁ i)
  have hnewRepairSelf : ∀ i,
      newOptionSub i ∉ newRepairSub i := by
    intro i
    exact hnewRepairSelf₁ (idx i) (hidxK₁ i)
  have hnewRepairAvoidNew : ∀ i j, i ≠ j →
      newOptionSub j ∉ newRepairSub i := by
    intro i j hij
    have hidxne : idx i ≠ idx j := fun h => hij (hidxInj h)
    exact hnewRepairAvoid 0 (idx i) (hidxM i)
      (idx j) (hidxM j) hidxne
  have hnewRepairAvoidOld : ∀ i j, i ≠ j → ∀ a,
      Tsub.option j a ∉ newRepairSub i := by
    intro i j hij a
    have hidxne : idx i ≠ idx j := fun h => hij (hidxInj h)
    exact hnewRepairAvoid a.succ (idx i) (hidxM i)
      (idx j) (hidxM j) hidxne
  have holdRepairAvoidNew : ∀ i j, i ≠ j → ∀ a,
      newOptionSub j ∉ Tsub.repair i a := by
    intro i j hij a hmem
    have hidxne : idx i ≠ idx j := fun h => hij (hidxInj h)
    apply holdAvoidNew (idx i) (hidxL i)
      (idx j) (hidxL j) hidxne
    exact Finset.mem_biUnion.mpr
      ⟨a, Finset.mem_univ a, hmem⟩
  let T' : RepairedOptionSystem A k.succ :=
    Tsub.prepend newOptionSub newRepairSub
      hnewMem hnewZero hnewOldSame hnewCross hnewOldCross
      hnewRepairMem hnewRepairSelf hnewRepairAvoidNew
      hnewRepairAvoidOld holdRepairAvoidNew
  refine ⟨T', ?_⟩
  intro i a
  refine Fin.cases ?_ (fun a => ?_) a
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (hnewOldLt i a)

end RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/-- A counterexample produces an abstract five-option system.  This packages
the quintuple repaired reservoir into the exact invariant consumed by the
generic partition and finite-certificate bridge. -/
theorem counterexample_forces_fiveRepairedOptionSystem_with_terminalMinimum
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ T : RepairedOptionSystem A 5,
      ∀ i a, T.option i 4 ≤ T.option i a := by
  classical
  obtain ⟨B, hBA, hB, S, f, p, r, s, u, g, h, j, k,
      hzeroS, hwitness, hAvoid, hp, hr, hs, hu,
      hjoint, hg, hh, hcrossS, hj, hcrossU, hk⟩ :=
    counterexample_forces_quintuplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let w : (i : ℕ) → ExternalFourCliqueWitness A (e i).1 :=
    fun i => Classical.choose (hwitness (e i).1 (e i).2)
  have hw : ∀ i, f (e i).1 = (w i).vertices := by
    intro i
    exact Classical.choose_spec (hwitness (e i).1 (e i).2)
  let atomRepair : ℕ → Finset ℕ := fun i =>
    insert (w i).x (pairSupport ((w i).y + (w i).z) (w i).y)
  let option : ℕ → Fin 5 → ℕ := fun i =>
    ![(e i).1, p (e i).1, r (e i).1, s (e i).1, u (e i).1]
  let repair : ℕ → Fin 5 → Finset ℕ := fun i =>
    ![atomRepair i, g (e i).1, h (e i).1, j (e i).1, k (e i).1]
  have hoptionMem : ∀ i a, option i a ∈ A := by
    intro i a
    fin_cases a
    · exact hBA (e i).2
    · obtain ⟨wi, hfwi⟩ := hwitness (e i).1 (e i).2
      apply wi.vertices_subset
      rw [← hfwi]
      exact Finset.sdiff_subset (hp (e i).1 (e i).2).1
    · exact additiveSupportFamily_supportsIn A 3
        (p (e i).1) (g (e i).1) (hg (e i).1 (e i).2).1
        (r (e i).1) (Finset.mem_sdiff.mp (hr (e i).1 (e i).2).1).1
    · exact additiveSupportFamily_supportsIn A 3
        (r (e i).1) (h (e i).1) (hh (e i).1 (e i).2).1
        (s (e i).1) (hs (e i).1 (e i).2).1
    · exact additiveSupportFamily_supportsIn A 3
        (s (e i).1) (j (e i).1) (hj (e i).1 (e i).2).1
        (u (e i).1) (hu (e i).1 (e i).2).1
  have hoptionZero : ∀ i a, option i a ≠ 0 := by
    intro i a
    fin_cases a
    · simpa [option] using Nat.ne_of_gt (w i).atom_pos
    · intro hpZero
      have hpZero' : p (e i).1 = 0 := by simpa [option] using hpZero
      exact (Finset.mem_sdiff.mp (hp (e i).1 (e i).2).1).2
        (hpZero' ▸ hzeroS)
    · intro hrZero
      have hrZero' : r (e i).1 = 0 := by simpa [option] using hrZero
      exact (Finset.mem_sdiff.mp (hr (e i).1 (e i).2).1).2
        (hrZero' ▸ hzeroS)
    · simpa [option] using Nat.ne_of_gt (hs (e i).1 (e i).2).2.1
    · simpa [option] using Nat.ne_of_gt (hu (e i).1 (e i).2).2.1
  have hoptionInj : ∀ i, Function.Injective (option i) := by
    intro i a c hac
    have hup := (hu (e i).1 (e i).2).2.2
    have hsr := (hs (e i).1 (e i).2).2.2
    have hrp := (hr (e i).1 (e i).2).2
    have hpb := (hp (e i).1 (e i).2).2
    fin_cases a <;> fin_cases c
    all_goals simp [option] at hac
    all_goals first | rfl | (exfalso; omega)
  let oldSupports : ℕ → Finset ℕ := fun b =>
    ((f b ∪ g b) ∪ h b) ∪ j b
  have holdAvoid : ∀ b ∈ B,
      Disjoint (oldSupports b : Set ℕ) B := by
    intro b hb
    rw [Set.disjoint_left]
    intro x hxOld hxB
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hxOld) with hxFGH | hxJ
    · rcases Finset.mem_union.mp hxFGH with hxFG | hxH
      · rcases Finset.mem_union.mp hxFG with hxF | hxG
        · exact Set.disjoint_left.mp (hAvoid b hb)
            (Finset.mem_coe.mpr hxF) hxB
        · exact Set.disjoint_left.mp (hg b hb).2.2.1
            (Finset.mem_coe.mpr hxG) hxB
      · exact Set.disjoint_left.mp (hh b hb).2.2.1
          (Finset.mem_coe.mpr hxH) hxB
    · exact Set.disjoint_left.mp (hj b hb).2.2.1
        (Finset.mem_coe.mpr hxJ) hxB
  have hoptionOld : ∀ b ∈ B, ∀ x,
      x = p b ∨ x = r b ∨ x = s b ∨ x = u b →
      x ∈ oldSupports b := by
    intro b hb x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp b hb).1).1))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr b hb).1).1))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (hs b hb).1)
    · exact Finset.mem_union_right _ (hu b hb).1
  have hoptionOldThree : ∀ b ∈ B, ∀ x,
      x = p b ∨ x = r b ∨ x = s b →
      x ∈ (f b ∪ g b) ∪ h b := by
    intro b hb x hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mp (hp b hb).1).1)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mp (hr b hb).1).1)
    · exact Finset.mem_union_right _ (hs b hb).1
  have hpetal : ∀ b ∈ B, ∀ x,
      x = p b ∨ x = r b → x ∈ (f b ∪ g b) \ S := by
    intro b hb x hx
    rcases hx with rfl | rfl
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp b hb).1).1,
          (Finset.mem_sdiff.mp (hp b hb).1).2⟩
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr b hb).1).1,
          (Finset.mem_sdiff.mp (hr b hb).1).2⟩
  have hoptionCross : ∀ i l, i ≠ l → ∀ a c,
      option i a ≠ option l c := by
    intro i l hil a c
    have hbil : (e i).1 ≠ (e l).1 := by
      intro h
      apply hil
      apply e.injective
      exact Subtype.ext h
    fin_cases a <;> fin_cases c
    all_goals simp [option]
    · exact hbil
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e l).1 (e l).2)
        (Finset.mem_coe.mpr (hoptionOld (e l).1 (e l).2 _
          (Or.inl rfl))) (hEq ▸ (e i).2)
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e l).1 (e l).2)
        (Finset.mem_coe.mpr (hoptionOld (e l).1 (e l).2 _
          (Or.inr (Or.inl rfl)))) (hEq ▸ (e i).2)
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e l).1 (e l).2)
        (Finset.mem_coe.mpr (hoptionOld (e l).1 (e l).2 _
          (Or.inr (Or.inr (Or.inl rfl))))) (hEq ▸ (e i).2)
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e l).1 (e l).2)
        (Finset.mem_coe.mpr (hoptionOld (e l).1 (e l).2 _
          (Or.inr (Or.inr (Or.inr rfl))))) (hEq ▸ (e i).2)
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hoptionOld (e i).1 (e i).2 _
          (Or.inl rfl))) (hEq.symm ▸ (e l).2)
    · intro hEq
      exact Finset.disjoint_left.mp
        (hjoint (e i).1 (e i).2 (e l).1 (e l).2 hbil)
        (hpetal (e i).1 (e i).2 _ (Or.inl rfl))
        (hEq ▸ hpetal (e l).1 (e l).2 _ (Or.inl rfl))
    · intro hEq
      exact Finset.disjoint_left.mp
        (hjoint (e i).1 (e i).2 (e l).1 (e l).2 hbil)
        (hpetal (e i).1 (e i).2 _ (Or.inl rfl))
        (hEq ▸ hpetal (e l).1 (e l).2 _ (Or.inr rfl))
    · intro hEq
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOldThree (e i).1 (e i).2 _ (Or.inl rfl))
    · intro hEq
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOld (e i).1 (e i).2 _ (Or.inl rfl))
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inl rfl)))) (hEq.symm ▸ (e l).2)
    · intro hEq
      exact Finset.disjoint_left.mp
        (hjoint (e i).1 (e i).2 (e l).1 (e l).2 hbil)
        (hpetal (e i).1 (e i).2 _ (Or.inr rfl))
        (hEq ▸ hpetal (e l).1 (e l).2 _ (Or.inl rfl))
    · intro hEq
      exact Finset.disjoint_left.mp
        (hjoint (e i).1 (e i).2 (e l).1 (e l).2 hbil)
        (hpetal (e i).1 (e i).2 _ (Or.inr rfl))
        (hEq ▸ hpetal (e l).1 (e l).2 _ (Or.inr rfl))
    · intro hEq
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOldThree (e i).1 (e i).2 _
          (Or.inr (Or.inl rfl)))
    · intro hEq
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inl rfl)))
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inr (Or.inl rfl))))) (hEq.symm ▸ (e l).2)
    · intro hEq
      exact hcrossS (e l).1 (e l).2 (e i).1 (e i).2 hbil.symm
        (hEq.symm ▸ hoptionOldThree (e l).1 (e l).2 _ (Or.inl rfl))
    · intro hEq
      exact hcrossS (e l).1 (e l).2 (e i).1 (e i).2 hbil.symm
        (hEq.symm ▸ hoptionOldThree (e l).1 (e l).2 _
          (Or.inr (Or.inl rfl)))
    · intro hEq
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOldThree (e i).1 (e i).2 _
          (Or.inr (Or.inr rfl)))
    · intro hEq
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inr (Or.inl rfl))))
    · intro hEq
      exact Set.disjoint_left.mp (holdAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inr (Or.inr rfl))))) (hEq.symm ▸ (e l).2)
    · intro hEq
      exact hcrossU (e l).1 (e l).2 (e i).1 (e i).2 hbil.symm
        (hEq.symm ▸ hoptionOld (e l).1 (e l).2 _ (Or.inl rfl))
    · intro hEq
      exact hcrossU (e l).1 (e l).2 (e i).1 (e i).2 hbil.symm
        (hEq.symm ▸ hoptionOld (e l).1 (e l).2 _
          (Or.inr (Or.inl rfl)))
    · intro hEq
      exact hcrossU (e l).1 (e l).2 (e i).1 (e i).2 hbil.symm
        (hEq.symm ▸ hoptionOld (e l).1 (e l).2 _
          (Or.inr (Or.inr (Or.inl rfl))))
    · intro hEq
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (hEq ▸ hoptionOld (e i).1 (e i).2 _
          (Or.inr (Or.inr (Or.inr rfl))))
  have hrepairMem : ∀ i a,
      repair i a ∈ additiveSupportFamily A 3 (option i a) := by
    intro i a
    fin_cases a
    · simpa [repair, option, atomRepair] using (w i).repairSupport_mem
    · simpa [repair, option] using (hg (e i).1 (e i).2).1
    · simpa [repair, option] using (hh (e i).1 (e i).2).1
    · simpa [repair, option] using (hj (e i).1 (e i).2).1
    · simpa [repair, option] using (hk (e i).1 (e i).2).1
  have hrepairSelf : ∀ i a, option i a ∉ repair i a := by
    intro i a
    fin_cases a
    · intro hbRepair
      apply (w i).atom_not_mem_vertices
      apply (w i).repairSupport_subset_vertices
      simpa [repair, option, atomRepair] using hbRepair
    · simpa [repair, option] using (hg (e i).1 (e i).2).2.1
    · simpa [repair, option] using (hh (e i).1 (e i).2).2.1
    · simpa [repair, option] using (hj (e i).1 (e i).2).2.1
    · simpa [repair, option] using (hk (e i).1 (e i).2).2.1
  have hpetalCross : ∀ b ∈ B, ∀ d ∈ B, b ≠ d → ∀ x,
      x ∈ f b ∪ g b → x ∉ S → x ∈ f d ∪ g d → False := by
    intro b hb d hd hbd x hxb hxS hxd
    exact Finset.disjoint_left.mp (hjoint b hb d hd hbd)
      (Finset.mem_sdiff.mpr ⟨hxb, hxS⟩)
      (Finset.mem_sdiff.mpr ⟨hxd, hxS⟩)
  have hrepairCross : ∀ i l, i ≠ l → ∀ a c,
      option l c ∉ repair i a := by
    intro i l hil a c
    have hbil : (e i).1 ≠ (e l).1 := by
      intro hEq
      apply hil
      apply e.injective
      exact Subtype.ext hEq
    have hAtomRepairF : atomRepair i ⊆ f (e i).1 := by
      intro x hx
      rw [hw i]
      apply (w i).repairSupport_subset_vertices
      simpa [atomRepair] using hx
    fin_cases a <;> fin_cases c
    · intro hx
      exact Set.disjoint_left.mp (hAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hAtomRepairF hx)) (e l).2
    · intro hx
      exact hpetalCross (e i).1 (e i).2 (e l).1 (e l).2 hbil _
        (Finset.mem_union_left _ (hAtomRepairF hx))
        (Finset.mem_sdiff.mp (hp (e l).1 (e l).2).1).2
        (Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp (e l).1 (e l).2).1).1)
    · intro hx
      exact hpetalCross (e i).1 (e i).2 (e l).1 (e l).2 hbil _
        (Finset.mem_union_left _ (hAtomRepairF hx))
        (Finset.mem_sdiff.mp (hr (e l).1 (e l).2).1).2
        (Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr (e l).1 (e l).2).1).1)
    · intro hx
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (hAtomRepairF hx)))
    · intro hx
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (hAtomRepairF hx))))
    · intro hx
      exact Set.disjoint_left.mp (hg (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e l).2
    · exact (hg (e i).1 (e i).2).2.2.2 (e l).1 (e l).2
    · intro hx
      exact hpetalCross (e i).1 (e i).2 (e l).1 (e l).2 hbil _
        (Finset.mem_union_right _ hx)
        (Finset.mem_sdiff.mp (hr (e l).1 (e l).2).1).2
        (Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr (e l).1 (e l).2).1).1)
    · intro hx
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
    · intro hx
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ hx)))
    · intro hx
      exact Set.disjoint_left.mp (hh (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e l).2
    · exact (hh (e i).1 (e i).2).2.2.2.1 (e l).1 (e l).2
    · exact (hh (e i).1 (e i).2).2.2.2.2 (e l).1 (e l).2
    · intro hx
      exact hcrossS (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_right _ hx)
    · intro hx
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
    · intro hx
      exact Set.disjoint_left.mp (hj (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e l).2
    · exact (hj (e i).1 (e i).2).2.2.2.1 (e l).1 (e l).2
    · exact (hj (e i).1 (e i).2).2.2.2.2.1 (e l).1 (e l).2
    · exact (hj (e i).1 (e i).2).2.2.2.2.2 (e l).1 (e l).2
    · intro hx
      exact hcrossU (e i).1 (e i).2 (e l).1 (e l).2 hbil
        (Finset.mem_union_right _ hx)
    · intro hx
      exact Set.disjoint_left.mp (hk (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e l).2
    · exact (hk (e i).1 (e i).2).2.2.2.1 (e l).1 (e l).2
    · exact (hk (e i).1 (e i).2).2.2.2.2.1 (e l).1 (e l).2
    · exact (hk (e i).1 (e i).2).2.2.2.2.2.1 (e l).1 (e l).2
    · exact (hk (e i).1 (e i).2).2.2.2.2.2.2 (e l).1 (e l).2
  let T : RepairedOptionSystem A 5 := {
    option := option
    repair := repair
    option_mem := hoptionMem
    option_ne_zero := hoptionZero
    option_injective := hoptionInj
    option_cross := hoptionCross
    repair_mem := hrepairMem
    repair_self := hrepairSelf
    repair_cross := hrepairCross
  }
  refine ⟨T, ?_⟩
  intro i a
  have hup := (hu (e i).1 (e i).2).2.2
  have hsr := (hs (e i).1 (e i).2).2.2
  have hrp := (hr (e i).1 (e i).2).2
  have hpb := (hp (e i).1 (e i).2).2
  fin_cases a <;> simp [T, option] <;> omega

/- Existential wrapper retaining the original public interface. -/
theorem counterexample_forces_fiveRepairedOptionSystem
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    Nonempty (RepairedOptionSystem A 5) := by
  obtain ⟨T, _hminimum⟩ :=
    counterexample_forces_fiveRepairedOptionSystem_with_terminalMinimum
      hbasis hzeroA hcounter
  exact ⟨T⟩

set_option maxHeartbeats 5000000 in
/- The generic one-step extension iterates.  Thus a counterexample would
force repaired-option systems of every finite height above five, with a
distinguished pointwise least option retained as the induction invariant. -/
theorem counterexample_forces_repairedOptionTower
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ n, ∃ T : RepairedOptionSystem A (5 + n),
      ∃ terminal : Fin (5 + n),
        ∀ i a, T.option i terminal ≤ T.option i a := by
  intro n
  induction n with
  | zero =>
      obtain ⟨T, hminimum⟩ :=
        counterexample_forces_fiveRepairedOptionSystem_with_terminalMinimum
          hbasis hzeroA hcounter
      exact ⟨T, 4, hminimum⟩
  | succ n ih =>
      obtain ⟨T, terminal, hminimum⟩ := ih
      obtain ⟨T', hminimum'⟩ :=
        T.exists_prepend_of_pointwiseMinimum hbasis terminal hminimum
      exact ⟨T', 0, hminimum'⟩

/- First concrete corollary of the tower induction: the sixth coherent
option system is obtained without replaying the thirty-six cross cases. -/
theorem counterexample_forces_sixRepairedOptionSystem
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    Nonempty (RepairedOptionSystem A 6) := by
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter 1
  exact ⟨T⟩

/-- Every selector restricted to the exact four-point repaired-option cores
preserves an order-three support for every internal target.  This is the
first use of the generic option-survival interface beyond three choices. -/
theorem internalTarget_survives_fourRepairedOptionSelector
    {A B : Set ℕ}
    (hzeroA : 0 ∈ A)
    {S : Finset ℕ} {f : ℕ → Finset ℕ}
    {p r s : ℕ → ℕ} {g h j : ℕ → Finset ℕ}
    {e : ℕ ≃ B} {F : ℕ → Finset ℕ}
    (hzeroS : 0 ∈ S)
    (hwitness : ∀ b ∈ B, ∃ w : ExternalFourCliqueWitness A b,
      f b = w.vertices)
    (hAvoid : ∀ b ∈ B, Disjoint (f b : Set ℕ) B)
    (hp : ∀ b ∈ B, p b ∈ f b \ S)
    (hr : ∀ b ∈ B, r b ∈ g b \ S)
    (hs : ∀ b ∈ B, s b ∈ h b ∧ 0 < s b)
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
    (hcrossS : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      s d ∉ (f b ∪ g b) ∪ h b)
    (hj : ∀ b ∈ B,
      j b ∈ additiveSupportFamily A 3 (s b) ∧
      s b ∉ j b ∧ Disjoint (j b : Set ℕ) B ∧
      (∀ d ∈ B, p d ∉ j b) ∧
      (∀ d ∈ B, r d ∉ j b) ∧
      ∀ d ∈ B, s d ∉ j b)
    (sel : BlockSelector F)
    (hselCore : ∀ i, (sel i).1 ∈
      fourRepairedOptionCell p r s (e i).1) :
    ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
      Disjoint (G : Set ℕ) (selectedSet sel) := by
  classical
  let w : (i : ℕ) → ExternalFourCliqueWitness A (e i).1 :=
    fun i => Classical.choose (hwitness (e i).1 (e i).2)
  have hw : ∀ i, f (e i).1 = (w i).vertices := by
    intro i
    exact Classical.choose_spec (hwitness (e i).1 (e i).2)
  let atomRepair : ℕ → Finset ℕ := fun i =>
    insert (w i).x (pairSupport ((w i).y + (w i).z) (w i).y)
  let option : ℕ → Fin 4 → ℕ := fun i =>
    ![(e i).1, p (e i).1, r (e i).1, s (e i).1]
  let repair : ℕ → Fin 4 → Finset ℕ := fun i =>
    ![atomRepair i, g (e i).1, h (e i).1, j (e i).1]
  have hoptionZero : ∀ i a, option i a ≠ 0 := by
    intro i a
    fin_cases a
    · simpa [option] using Nat.ne_of_gt (w i).atom_pos
    · intro hpZero
      have hpZero' : p (e i).1 = 0 := by
        simpa [option] using hpZero
      exact (Finset.mem_sdiff.mp (hp (e i).1 (e i).2)).2
        (hpZero' ▸ hzeroS)
    · intro hrZero
      have hrZero' : r (e i).1 = 0 := by
        simpa [option] using hrZero
      exact (Finset.mem_sdiff.mp (hr (e i).1 (e i).2)).2
        (hrZero' ▸ hzeroS)
    · simpa [option] using
        Nat.ne_of_gt (hs (e i).1 (e i).2).2
  have hrepair : ∀ i a,
      repair i a ∈ additiveSupportFamily A 3 (option i a) := by
    intro i a
    fin_cases a
    · simpa [repair, option, atomRepair] using (w i).repairSupport_mem
    · simpa [repair, option] using (hg (e i).1 (e i).2).1
    · simpa [repair, option] using (hh (e i).1 (e i).2).1
    · simpa [repair, option] using (hj (e i).1 (e i).2).1
  have hrepairSelf : ∀ i a, option i a ∉ repair i a := by
    intro i a
    fin_cases a
    · intro hbRepair
      apply (w i).atom_not_mem_vertices
      apply (w i).repairSupport_subset_vertices
      simpa [repair, option, atomRepair] using hbRepair
    · simpa [repair, option] using (hg (e i).1 (e i).2).2.1
    · simpa [repair, option] using (hh (e i).1 (e i).2).2.1
    · simpa [repair, option] using (hj (e i).1 (e i).2).2.1
  have hpetalCross : ∀ b ∈ B, ∀ d ∈ B, b ≠ d → ∀ x,
      x ∈ f b ∪ g b → x ∉ S → x ∈ f d ∪ g d → False := by
    intro b hb d hd hbd x hxb hxS hxd
    exact Finset.disjoint_left.mp
      (hjointDisjoint b hb d hd hbd)
      (Finset.mem_sdiff.mpr ⟨hxb, hxS⟩)
      (Finset.mem_sdiff.mpr ⟨hxd, hxS⟩)
  have hrepairCross : ∀ i k, i ≠ k → ∀ a c,
      option k c ∉ repair i a := by
    intro i k hik a c
    have hbne : (e i).1 ≠ (e k).1 := by
      intro h
      apply hik
      apply e.injective
      exact Subtype.ext h
    have hAtomRepairF : atomRepair i ⊆ f (e i).1 := by
      intro x hx
      rw [hw i]
      apply (w i).repairSupport_subset_vertices
      simpa [atomRepair] using hx
    have h00 : (e k).1 ∉ atomRepair i := by
      intro hx
      exact Set.disjoint_left.mp (hAvoid (e i).1 (e i).2)
        (Finset.mem_coe.mpr (hAtomRepairF hx)) (e k).2
    have h01 : p (e k).1 ∉ atomRepair i := by
      intro hx
      exact hpetalCross (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (p (e k).1)
        (Finset.mem_union_left _ (hAtomRepairF hx))
        (Finset.mem_sdiff.mp (hp (e k).1 (e k).2)).2
        (Finset.mem_union_left _
          (Finset.mem_sdiff.mp (hp (e k).1 (e k).2)).1)
    have h02 : r (e k).1 ∉ atomRepair i := by
      intro hx
      exact hpetalCross (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (r (e k).1)
        (Finset.mem_union_left _ (hAtomRepairF hx))
        (Finset.mem_sdiff.mp (hr (e k).1 (e k).2)).2
        (Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr (e k).1 (e k).2)).1)
    have h03 : s (e k).1 ∉ atomRepair i := by
      intro hx
      exact hcrossS (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (Finset.mem_union_left _
          (Finset.mem_union_left _ (hAtomRepairF hx)))
    have h10 : (e k).1 ∉ g (e i).1 := by
      intro hx
      exact Set.disjoint_left.mp (hg (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e k).2
    have h11 : p (e k).1 ∉ g (e i).1 :=
      (hg (e i).1 (e i).2).2.2.2 (e k).1 (e k).2
    have h12 : r (e k).1 ∉ g (e i).1 := by
      intro hx
      exact hpetalCross (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (r (e k).1) (Finset.mem_union_right _ hx)
        (Finset.mem_sdiff.mp (hr (e k).1 (e k).2)).2
        (Finset.mem_union_right _
          (Finset.mem_sdiff.mp (hr (e k).1 (e k).2)).1)
    have h13 : s (e k).1 ∉ g (e i).1 := by
      intro hx
      exact hcrossS (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (Finset.mem_union_left _ (Finset.mem_union_right _ hx))
    have h20 : (e k).1 ∉ h (e i).1 := by
      intro hx
      exact Set.disjoint_left.mp (hh (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e k).2
    have h21 : p (e k).1 ∉ h (e i).1 :=
      (hh (e i).1 (e i).2).2.2.2.1 (e k).1 (e k).2
    have h22 : r (e k).1 ∉ h (e i).1 :=
      (hh (e i).1 (e i).2).2.2.2.2 (e k).1 (e k).2
    have h23 : s (e k).1 ∉ h (e i).1 := by
      intro hx
      exact hcrossS (e i).1 (e i).2 (e k).1 (e k).2 hbne
        (Finset.mem_union_right _ hx)
    have h30 : (e k).1 ∉ j (e i).1 := by
      intro hx
      exact Set.disjoint_left.mp (hj (e i).1 (e i).2).2.2.1
        (Finset.mem_coe.mpr hx) (e k).2
    have h31 : p (e k).1 ∉ j (e i).1 :=
      (hj (e i).1 (e i).2).2.2.2.1 (e k).1 (e k).2
    have h32 : r (e k).1 ∉ j (e i).1 :=
      (hj (e i).1 (e i).2).2.2.2.2.1 (e k).1 (e k).2
    have h33 : s (e k).1 ∉ j (e i).1 :=
      (hj (e i).1 (e i).2).2.2.2.2.2 (e k).1 (e k).2
    fin_cases a <;> fin_cases c <;>
      simp [option, repair, h00, h01, h02, h03,
        h10, h11, h12, h13, h20, h21, h22, h23,
        h30, h31, h32, h33]
  have hselOption : ∀ i, ∃ a : Fin 4,
      (sel i).1 = option i a := by
    intro i
    have hmem := hselCore i
    simp only [fourRepairedOptionCell, atomOptionCell,
      threeRepairOptionSet, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hAtom | hpOption | hrOption | hsOption
    · exact ⟨0, by simpa [option] using hAtom⟩
    · exact ⟨1, by simpa [option] using hpOption⟩
    · exact ⟨2, by simpa [option] using hrOption⟩
    · exact ⟨3, by simpa [option] using hsOption⟩
  exact internalTarget_survives_repairedOptionSelector
    hzeroA option repair hoptionZero hrepair hrepairSelf
      hrepairCross sel hselOption

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

/-- The support-choice duality for a certificate restricted to dedicated
core selectors.  If no core cell were covered, choosing in every core a
point outside the finite support union would produce a selector avoiding the
support of the target certified against it. -/
theorem exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
    {R : SupportFamily} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q, DestroysAt R (selectedSet s) q)
    (c : FiniteSupportChoice R Q) :
    ∃ i, cell i ⊆ finiteSupportChoiceUnion c := by
  classical
  by_contra hnone
  have hchoice : ∀ i, ∃ x, x ∈ cell i ∧
      x ∉ finiteSupportChoiceUnion c := by
    intro i
    by_contra hi
    push Not at hi
    exact hnone ⟨i, hi⟩
  choose x hxCell hxNotUnion using hchoice
  let s : BlockSelector F := fun i =>
    ⟨x i, hcore i (hxCell i)⟩
  obtain ⟨q, hqQ, hqDestroy⟩ :=
    hcert s (fun i => hxCell i)
  have hsupportDisjoint : Disjoint ((c ⟨q, hqQ⟩).1 : Set ℕ)
      (selectedSet s) := by
    rw [Set.disjoint_left]
    intro y hySupport hySelected
    obtain ⟨i, hi⟩ := hySelected
    change (s i).1 = y at hi
    apply hxNotUnion i
    apply finiteSupportChoice_subset_union c ⟨q, hqQ⟩
    have hxy : x i = y := by simpa [s] using hi
    rw [hxy]
    exact Finset.mem_coe.mp hySupport
  exact (hqDestroy (c ⟨q, hqQ⟩).1
    (c ⟨q, hqQ⟩).2) hsupportDisjoint

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

/-- Large dedicated cores force large finite target certificates.  Choosing
one pair support for each represented target yields a union of at most
`2 * Q.card` points, while the selector certificate forces that union to
cover one whole zero-free core. -/
theorem coreSelectorCertificate_forces_targetCard_lower
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, k ≤ (cell i).card)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q) :
    k ≤ 2 * Q.card := by
  classical
  let c : FiniteSupportChoice (additiveSupportFamily A 2) Q := fun q =>
    ⟨(hrepresented q.1 q.2).choose,
      (hrepresented q.1 q.2).choose_spec⟩
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_coreSelectorCertificate_and_pairChoice
      hzeroA hcellZero hcore hcert c
  have hcellUnion : (cell i).card ≤
      (finiteSupportChoiceUnion c).card :=
    Finset.card_le_card hiCover
  have hunionCard : (finiteSupportChoiceUnion c).card ≤ 2 * Q.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 2) c
  exact (hcellLower i).trans (hcellUnion.trans hunionCard)

/-- Order-two form of the core-size lower bound.  No zero padding is needed:
the generic support-choice duality directly forces one dedicated core into
the union of one chosen pair support per certificate target. -/
theorem coreSelectorPairCertificate_forces_targetCard_lower
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, k ≤ (cell i).card)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q) :
    k ≤ 2 * Q.card := by
  classical
  let c : FiniteSupportChoice (additiveSupportFamily A 2) Q := fun q =>
    ⟨(hrepresented q.1 q.2).choose,
      (hrepresented q.1 q.2).choose_spec⟩
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
      hcore hcert c
  have hcellUnion : (cell i).card ≤
      (finiteSupportChoiceUnion c).card :=
    Finset.card_le_card hiCover
  have hunionCard : (finiteSupportChoiceUnion c).card ≤ 2 * Q.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 2) c
  exact (hcellLower i).trans (hcellUnion.trans hunionCard)

namespace RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/-- Abstract finite-certificate bridge for an arbitrary repaired-option
system.  Once `k ≥ 3` coherent options have been built, strong deletion
forces late external certificates satisfying the scalable inequality
`k ≤ 2 * Q.card`; the sharp pair-support bound is independent of `k`. -/
theorem exists_externalCoreCertificate
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (T : RepairedOptionSystem A k) (hk : 3 ≤ k) :
    ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, T.cell i ⊆ F i) ∧
      (∀ i, 0 ∉ T.cell i) ∧
      (∀ i, (T.cell i).card = k) ∧
      ∀ N, ∃ Q : Finset ℕ,
        Q.Nonempty ∧
        k ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ T.cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∃ q ∈ Q,
          (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  have hkPos : 0 < k := by omega
  obtain ⟨F, P, hcore, hcellCard, hsurvive⟩ :=
    T.exists_finiteBlockPartition_and_internalSurvival
      hzeroA hkPos
  have hcellZero : ∀ i, 0 ∉ T.cell i := by
    intro i hzeroCell
    obtain ⟨a, _ha, haZero⟩ := Finset.mem_image.mp hzeroCell
    exact T.option_ne_zero i a haZero
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q₀, hQ₀late, hcert₀⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      (strongOrderThreeDeletion_of_counterexample hcounter)
      F P (max N N₂)
  let Q : Finset ℕ := Q₀.filter fun q => q ∉ A
  have hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ T.cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ sel
    have hqA : q ∉ A := by
      intro hqA
      obtain ⟨G, hGR, hGdisjoint⟩ := hsurvive sel hsel q hqA
      exact (hqDestroy G hGR) hGdisjoint
    exact ⟨q, Finset.mem_filter.mpr ⟨hqQ₀, hqA⟩,
      hqDestroy⟩
  have hQlate : ∀ q ∈ Q, N ≤ q ∧ q ∉ A := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨(le_max_left N N₂).trans (hQ₀late q hq.1), hq.2⟩
  have hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ
    have hqQ₀ := (Finset.mem_filter.mp hqQ).1
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQ₀late q hqQ₀))
    exact ⟨E, hER⟩
  have hcellLowerK : ∀ i, k ≤ (T.cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : k ≤ 2 * Q.card :=
    coreSelectorCertificate_forces_targetCard_lower
      hzeroA hcellZero hcore hcellLowerK hrepresented hcert
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hcellLowerThree : ∀ i, 3 ≤ (T.cell i).card := by
    intro i
    rw [hcellCard i]
    exact hk
  obtain ⟨q, hqQ, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLowerThree hcert
  exact ⟨Q, hQ, htargetLower, hQlate, hcert,
    q, hqQ, hqBound⟩

end RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/-- Five-option external certificate residual.  The fifth repaired layer
crosses the first quantitative threshold unavailable to three- and
four-point cores: `5 ≤ 2 * Q.card` forces every late external certificate
to contain at least three targets. -/
theorem counterexample_forces_fiveOptionExternalCoreCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 5) ∧
      ∀ N, ∃ Q : Finset ℕ,
        3 ≤ Q.card ∧
        5 ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∃ q ∈ Q,
          (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨T⟩ := counterexample_forces_fiveRepairedOptionSystem
    hbasis hzeroA hcounter
  obtain ⟨F, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_externalCoreCertificate
      hbasis hzeroA hcounter (by omega)
  refine ⟨F, T.cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, htargetLower, hQlate, hcert,
      q, hqQ, hqBound⟩ := hresidual N
  have hQcard : 3 ≤ Q.card := by omega
  exact ⟨Q, hQcard, htargetLower, hQlate, hcert,
    q, hqQ, hqBound⟩

set_option maxHeartbeats 5000000 in
/- Scalable certificate consequence of the repaired-option tower.  For
every finite height `5 + n`, a counterexample supplies a block partition
with exact `(5 + n)`-point safe cores.  Strong deletion must answer it with
a late external target certificate satisfying
`5 + n ≤ 2 * Q.card`. -/
theorem counterexample_forces_arbitrarilyLargeExternalCoreCertificates
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ n, ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 5 + n) ∧
      ∀ N, ∃ Q : Finset ℕ,
        Q.Nonempty ∧
        5 + n ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        ∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q := by
  intro n
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter n
  obtain ⟨F, P, hcore, hcellZero, hcellCard, hcert⟩ :=
    T.exists_externalCoreCertificate
      hbasis hzeroA hcounter (by omega)
  refine ⟨F, T.cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, hQ, hQcard, hQlate, hselector, _hbounded⟩ := hcert N
  exact ⟨Q, hQ, hQcard, hQlate, hselector⟩

set_option maxHeartbeats 5000000 in
/-- Pointwise bound from a target-localized order-two core certificate.  For
one target `q`, use its private selector and choose, for every other target,
a pair support avoiding that selector.  Their union has at most
`2 * (Q.erase q).card` points and omits the selected point of every core.
Varying a support of `q`, core coverage assigns it to a cell touched by that
fixed union.  Two distinct supports cannot receive the same cell because
both would contain its selected point, contradicting the matching property
of pair supports. -/
theorem minimalCorePairCertificate_forces_pointwise_boundedPairFamilies
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) ∧
      DestroysAt (additiveSupportFamily A 2) (selectedSet s) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt (additiveSupportFamily A 2)
          (selectedSet s) q') :
    ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤
        2 * (Q.erase q).card := by
  classical
  intro q hqQ
  obtain ⟨s, hsCore, _hqDestroy, hprivate⟩ :=
    hlocalized q hqQ
  let Q' : Finset ℕ := Q.erase q
  have hsurvive : ∀ r : {n // n ∈ Q'},
      ∃ E ∈ additiveSupportFamily A 2 r.1,
        Disjoint (E : Set ℕ) (selectedSet s) := by
    intro r
    have hr := Finset.mem_erase.mp r.2
    exact not_destroysAt_iff.mp
      (hprivate r.1 hr.2 hr.1)
  choose chosen hchosenMem hchosenDisjoint using hsurvive
  let cOther : FiniteSupportChoice
      (additiveSupportFamily A 2) Q' := fun r =>
    ⟨chosen r, hchosenMem r⟩
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  have hUDisjoint : Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨r, _hrAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hchosenDisjoint r)
      (Finset.mem_coe.mpr hxSupport) hxSelected
  let I : Finset ℕ := U.image (blockIndex P)
  have hassign : ∀ E : {E // E ∈ additiveSupportFamily A 2 q},
      ∃ i, i ∈ I ∧ (s i).1 ∈ E.1 := by
    intro E
    let cFull : FiniteSupportChoice
        (additiveSupportFamily A 2) Q := fun r =>
      if hrq : r.1 = q then
        ⟨E.1, by simpa [hrq] using E.2⟩
      else
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        ⟨(cOther r').1, (cOther r').2⟩
    have hfullCases : ∀ x,
        x ∈ finiteSupportChoiceUnion cFull → x ∈ E.1 ∨ x ∈ U := by
      intro x hx
      obtain ⟨r, _hrAttach, hxr⟩ := Finset.mem_biUnion.mp hx
      by_cases hrq : r.1 = q
      · left
        simpa [cFull, hrq] using hxr
      · right
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        apply finiteSupportChoice_subset_union cOther r'
        simpa [cFull, hrq, r'] using hxr
    obtain ⟨i, hiCover⟩ :=
      exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
        hcore hcert cFull
    have hsE : (s i).1 ∈ E.1 := by
      rcases hfullCases (s i).1 (hiCover (hsCore i)) with hsE | hsU
      · exact hsE
      · exact (Set.disjoint_left.mp hUDisjoint
          (Finset.mem_coe.mpr hsU) ⟨i, rfl⟩).elim
    have hcellHitsU : ¬ Disjoint (cell i) U := by
      intro hdisjoint
      have hcellE : cell i ⊆ E.1 := by
        intro x hxCell
        rcases hfullCases x (hiCover hxCell) with hxE | hxU
        · exact hxE
        · exact (Finset.disjoint_left.mp hdisjoint hxCell hxU).elim
      have hcardLe := Finset.card_le_card hcellE
      have hEcard :=
        additiveSupportFamily_cardAtMost A 2 q E.1 E.2
      have hcellCard := hcellLower i
      omega
    obtain ⟨u, huCell, huU⟩ :=
      Finset.not_disjoint_iff.mp hcellHitsU
    have huIndex : blockIndex P u = i :=
      P.blockIndex_eq_of_mem (hcore i huCell)
    have hiI : i ∈ I :=
      Finset.mem_image.mpr ⟨u, huU, huIndex⟩
    exact ⟨i, hiI, hsE⟩
  choose assigned hassignedI hselectedMem using hassign
  let assignedSub : {E // E ∈ additiveSupportFamily A 2 q} →
      {i // i ∈ I} := fun E => ⟨assigned E, hassignedI E⟩
  have hassignedInj : Function.Injective assignedSub := by
    intro E E' hindex
    apply Subtype.ext
    by_contra hEE'
    have hindexVal : assigned E = assigned E' :=
      congrArg Subtype.val hindex
    have hxE := hselectedMem E
    have hxE' : (s (assigned E)).1 ∈ E'.1 := by
      rw [hindexVal]
      exact hselectedMem E'
    exact Finset.disjoint_left.mp
      (additiveSupportFamily_two_isMatching A q E.2 E'.2 hEE')
      hxE hxE'
  have hsupportCardI : (additiveSupportFamily A 2 q).card ≤ I.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective assignedSub hassignedInj
  have hIcardU : I.card ≤ U.card := Finset.card_image_le
  have hUcard : U.card ≤ 2 * Q'.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 2) cOther
  exact hsupportCardI.trans (hIcardU.trans hUcard)

set_option maxHeartbeats 5000000 in
/-- Core occupancy sharpens the pointwise minimal-certificate bound.  For a
support `E` of the private target, the covered `k`-point core lies in
`E ∪ U`, where `E` has at most two points and `U` is the union of one pair
support for every other target.  Hence that core contains at least `k - 2`
points of `U`.  Assigned cores are distinct and disjoint, giving
`(k - 2) * |R₂(q)| ≤ 2 * |Q.erase q|`. -/
theorem minimalCorePairCertificate_forces_scaledPointwiseBound
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, k ≤ (cell i).card)
    (hk : 3 ≤ k)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q)
    (hlocalized : ∀ q ∈ Q, ∃ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) ∧
      DestroysAt (additiveSupportFamily A 2)
        (selectedSet sel) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q') :
    ∀ q ∈ Q,
      (k - 2) * (additiveSupportFamily A 2 q).card ≤
        2 * (Q.erase q).card := by
  classical
  intro q hqQ
  obtain ⟨sel, hselCore, _hqDestroy, hprivate⟩ :=
    hlocalized q hqQ
  let Q' : Finset ℕ := Q.erase q
  have hsurvive : ∀ r : {n // n ∈ Q'},
      ∃ E ∈ additiveSupportFamily A 2 r.1,
        Disjoint (E : Set ℕ) (selectedSet sel) := by
    intro r
    have hr := Finset.mem_erase.mp r.2
    exact not_destroysAt_iff.mp
      (hprivate r.1 hr.2 hr.1)
  choose chosen hchosenMem hchosenDisjoint using hsurvive
  let cOther : FiniteSupportChoice
      (additiveSupportFamily A 2) Q' := fun r =>
    ⟨chosen r, hchosenMem r⟩
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  have hUDisjoint : Disjoint (U : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨r, _hrAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hchosenDisjoint r)
      (Finset.mem_coe.mpr hxSupport) hxSelected
  let I : Finset ℕ := U.image (blockIndex P)
  have hassign : ∀ E : {E // E ∈ additiveSupportFamily A 2 q},
      ∃ i, i ∈ I ∧ (sel i).1 ∈ E.1 ∧
        cell i ⊆ E.1 ∪ U := by
    intro E
    let cFull : FiniteSupportChoice
        (additiveSupportFamily A 2) Q := fun r =>
      if hrq : r.1 = q then
        ⟨E.1, by simpa [hrq] using E.2⟩
      else
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        ⟨(cOther r').1, (cOther r').2⟩
    have hfullCases : ∀ x,
        x ∈ finiteSupportChoiceUnion cFull → x ∈ E.1 ∨ x ∈ U := by
      intro x hx
      obtain ⟨r, _hrAttach, hxr⟩ := Finset.mem_biUnion.mp hx
      by_cases hrq : r.1 = q
      · left
        simpa [cFull, hrq] using hxr
      · right
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        apply finiteSupportChoice_subset_union cOther r'
        simpa [cFull, hrq, r'] using hxr
    obtain ⟨i, hiCover⟩ :=
      exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
        hcore hcert cFull
    have hcellUE : cell i ⊆ E.1 ∪ U := by
      intro x hxCell
      exact Finset.mem_union.mpr (hfullCases x (hiCover hxCell))
    have hselE : (sel i).1 ∈ E.1 := by
      rcases Finset.mem_union.mp (hcellUE (hselCore i)) with hselE | hselU
      · exact hselE
      · exact (Set.disjoint_left.mp hUDisjoint
          (Finset.mem_coe.mpr hselU) ⟨i, rfl⟩).elim
    have hcellHitsU : ¬ Disjoint (cell i) U := by
      intro hdisjoint
      have hcellE : cell i ⊆ E.1 := by
        intro x hxCell
        rcases Finset.mem_union.mp (hcellUE hxCell) with hxE | hxU
        · exact hxE
        · exact (Finset.disjoint_left.mp hdisjoint hxCell hxU).elim
      have hcardLe := Finset.card_le_card hcellE
      have hEcard :=
        additiveSupportFamily_cardAtMost A 2 q E.1 E.2
      have hcellCard := hcellLower i
      omega
    obtain ⟨v, hvCell, hvU⟩ :=
      Finset.not_disjoint_iff.mp hcellHitsU
    have hvIndex : blockIndex P v = i :=
      P.blockIndex_eq_of_mem (hcore i hvCell)
    have hiI : i ∈ I :=
      Finset.mem_image.mpr ⟨v, hvU, hvIndex⟩
    exact ⟨i, hiI, hselE, hcellUE⟩
  choose assigned hassignedI hselectedMem hcellCover using hassign
  have hassignInj : Function.Injective assigned := by
    intro E E' hindex
    apply Subtype.ext
    by_contra hEE'
    have hxE := hselectedMem E
    have hxE' : (sel (assigned E)).1 ∈ E'.1 := by
      rw [hindex]
      exact hselectedMem E'
    exact Finset.disjoint_left.mp
      (additiveSupportFamily_two_isMatching A q E.2 E'.2 hEE')
      hxE hxE'
  let J : Finset ℕ :=
    (additiveSupportFamily A 2 q).attach.image assigned
  have hJcard : J.card =
      (additiveSupportFamily A 2 q).card := by
    dsimp only [J]
    rw [Finset.card_image_iff.mpr hassignInj.injOn]
    simp
  have hoccupancy : ∀ i ∈ J, k - 2 ≤ (cell i ∩ U).card := by
    intro i hiJ
    obtain ⟨E, _hEattach, hEi⟩ := Finset.mem_image.mp hiJ
    have hcover : cell i ⊆ E.1 ∪ U := by
      simpa [hEi] using hcellCover E
    have hdiffSub : cell i \ U ⊆ E.1 := by
      intro x hxDiff
      have hx := Finset.mem_sdiff.mp hxDiff
      rcases Finset.mem_union.mp (hcover hx.1) with hxE | hxU
      · exact hxE
      · exact (hx.2 hxU).elim
    have hdiffCard : (cell i \ U).card ≤ 2 :=
      (Finset.card_le_card hdiffSub).trans
        (additiveSupportFamily_cardAtMost A 2 q E.1 E.2)
    have hdecomp := Finset.card_sdiff_add_card_inter (cell i) U
    have hcellCard := hcellLower i
    omega
  let V : Finset ℕ := J.biUnion fun i => cell i ∩ U
  have hpairwise : (J : Set ℕ).PairwiseDisjoint
      (fun i => cell i ∩ U) := by
    intro i hi j hj hij
    exact ((P.disjoint hij).mono (hcore i) (hcore j)).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hVLower : (k - 2) * J.card ≤ V.card := by
    dsimp only [V]
    rw [Finset.card_biUnion hpairwise]
    calc
      (k - 2) * J.card = ∑ i ∈ J, (k - 2) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ J, (cell i ∩ U).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact hoccupancy i hi
  have hVsub : V ⊆ U := by
    intro x hxV
    obtain ⟨i, _hiJ, hxInter⟩ := Finset.mem_biUnion.mp hxV
    exact (Finset.mem_inter.mp hxInter).2
  have hVUpper : V.card ≤ U.card := Finset.card_le_card hVsub
  have hUcard : U.card ≤ 2 * Q'.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 2) cOther
  rw [hJcard] at hVLower
  exact hVLower.trans (hVUpper.trans hUcard)

namespace RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/- Generic minimal order-two residual for a repaired-option system.  It
retains the exact core size, late externality, target localization, and the
scaled occupancy inequality.  This is the reusable form of the five-option
calculation and applies at every height of the tower. -/
theorem exists_minimalExternalCorePairCertificate
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (T : RepairedOptionSystem A k) (hk : 3 ≤ k) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = k) ∧
      ∀ N, ∃ Q : Finset ℕ,
        Q.Nonempty ∧
        k ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q) ∧
        (∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 2)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q') ∧
        ∀ q ∈ Q,
          (k - 2) * (additiveSupportFamily A 2 q).card ≤
            2 * (Q.erase q).card := by
  classical
  obtain ⟨F, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_externalCoreCertificate hbasis hzeroA hcounter hk
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, T.cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, _hQlower, hQlate, hcert₃, _hbounded⟩ :=
    hresidual (max N N₂)
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ T.cell i
  have hcert₂ : ∀ sel : BlockSelector F, Good sel →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert₃ sel hsel
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hsel i
    exact ⟨q, hqQ,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy⟩
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₂
  have hQ₀late : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hrepresented : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLower : ∀ i, k ≤ (T.cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : k ≤ 2 * Q₀.card :=
    coreSelectorPairCertificate_forces_targetCard_lower
      hcore hcellLower hrepresented hcert₀
  have hQ₀ : Q₀.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hscaled : ∀ q ∈ Q₀,
      (k - 2) * (additiveSupportFamily A 2 q).card ≤
        2 * (Q₀.erase q).card :=
    minimalCorePairCertificate_forces_scaledPointwiseBound
      P hcore hcellLower hk hcert₀ hlocalized
  exact ⟨Q₀, hQ₀, htargetLower, hQ₀late,
    hrepresented, hcert₀, hlocalized, hscaled⟩

end RepairedOptionSystem

namespace RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/- Generic minimal order-three residual.  Unlike the pair residual, this
keeps the genuine strong-deletion certificate while minimizing its target
set.  Late pair representations are retained so sharp even-core equality
cases can subsequently be classified. -/
theorem exists_minimalExternalCoreTripleCertificate
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (T : RepairedOptionSystem A k) (hk : 3 ≤ k) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = k) ∧
      ∀ N, ∃ Q : Finset ℕ,
        Q.Nonempty ∧
        k ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q' := by
  classical
  obtain ⟨F, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_externalCoreCertificate hbasis hzeroA hcounter hk
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, T.cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, _hQlower, hQlate, hcert₃, _hbounded⟩ :=
    hresidual (max N N₂)
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ T.cell i
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized₀⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₃
  have hQ₀late : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hrepresented₀ : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLower : ∀ i, k ≤ (T.cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : k ≤ 2 * Q₀.card :=
    coreSelectorCertificate_forces_targetCard_lower
      hzeroA hcellZero hcore hcellLower hrepresented₀ hcert₀
  have hQ₀ : Q₀.Nonempty := by
    apply Finset.card_pos.mp
    omega
  exact ⟨Q₀, hQ₀, htargetLower, hQ₀late,
    hrepresented₀, hcert₀, hlocalized₀⟩

end RepairedOptionSystem

set_option maxHeartbeats 5000000 in
/- Force one prescribed core point while avoiding an arbitrary finite set
which is smaller than every core. -/
theorem exists_coreSelector_forcedPoint_avoiding_finset
    {F cell : ℕ → Finset ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    {i x : ℕ} (hxCell : x ∈ cell i)
    (H : Finset ℕ) (hHsmall : ∀ j, H.card < (cell j).card)
    (hxH : x ∉ H) :
    ∃ sel : BlockSelector F,
      (∀ j, (sel j).1 ∈ cell j) ∧
      (sel i).1 = x ∧
      Disjoint (H : Set ℕ) (selectedSet sel) := by
  classical
  have houtside : ∀ j, ∃ y, y ∈ cell j ∧ y ∉ H := by
    intro j
    have hnsub : ¬ cell j ⊆ H := by
      intro hsub
      exact (not_le_of_gt (hHsmall j)) (Finset.card_le_card hsub)
    exact Finset.not_subset.mp hnsub
  choose picked hpickedCell hpickedH using houtside
  let value : ℕ → ℕ := fun j => if hj : j = i then x else picked j
  have hvalueCell : ∀ j, value j ∈ cell j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxCell
    · simpa [value, hj] using hpickedCell j
  have hvalueH : ∀ j, value j ∉ H := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxH
    · simpa [value, hj] using hpickedH j
  let sel : BlockSelector F := fun j =>
    ⟨value j, hcore j (hvalueCell j)⟩
  have hselCore : ∀ j, (sel j).1 ∈ cell j := by
    intro j
    exact hvalueCell j
  have hselForced : (sel i).1 = x := by
    simp [sel, value]
  have hdisjoint : Disjoint (H : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro y hyH hySelected
    obtain ⟨j, hjy⟩ := hySelected
    apply hvalueH j
    have hjy' : (sel j).1 = y := hjy
    have hselH : (sel j).1 ∈ H := by
      rw [hjy']
      exact Finset.mem_coe.mp hyH
    simpa [sel] using hselH
  exact ⟨sel, hselCore, hselForced, hdisjoint⟩

set_option maxHeartbeats 5000000 in
/- Force one prescribed core point while avoiding a fixed small set in all
other blocks.  Since every core has at least four points and `H` has at most
three, each non-prescribed block offers a core point outside `H`. -/
theorem exists_coreSelector_forcedPoint_avoiding_threePointSet
    {F cell : ℕ → Finset ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 4 ≤ (cell i).card)
    {i x : ℕ} (hxCell : x ∈ cell i)
    (H : Finset ℕ) (hHcard : H.card ≤ 3) (hxH : x ∉ H) :
    ∃ sel : BlockSelector F,
      (∀ j, (sel j).1 ∈ cell j) ∧
      (sel i).1 = x ∧
      Disjoint (H : Set ℕ) (selectedSet sel) := by
  classical
  have houtside : ∀ j, ∃ y, y ∈ cell j ∧ y ∉ H := by
    intro j
    have hnsub : ¬ cell j ⊆ H := by
      intro hsub
      have hcard := Finset.card_le_card hsub
      have hjcard := hcellLower j
      omega
    exact Finset.not_subset.mp hnsub
  choose picked hpickedCell hpickedH using houtside
  let value : ℕ → ℕ := fun j => if hj : j = i then x else picked j
  have hvalueCell : ∀ j, value j ∈ cell j := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxCell
    · simpa [value, hj] using hpickedCell j
  have hvalueH : ∀ j, value j ∉ H := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa [value] using hxH
    · simpa [value, hj] using hpickedH j
  let sel : BlockSelector F := fun j =>
    ⟨value j, hcore j (hvalueCell j)⟩
  have hselCore : ∀ j, (sel j).1 ∈ cell j := by
    intro j
    exact hvalueCell j
  have hselForced : (sel i).1 = x := by
    simp [sel, value]
  have hdisjoint : Disjoint (H : Set ℕ) (selectedSet sel) := by
    rw [Set.disjoint_left]
    intro y hyH hySelected
    obtain ⟨j, hjy⟩ := hySelected
    apply hvalueH j
    have hjy' : (sel j).1 = y := hjy
    have hselH : (sel j).1 ∈ H := by
      rw [hjy']
      exact Finset.mem_coe.mp hyH
    simpa [sel] using hselH
  exact ⟨sel, hselCore, hselForced, hdisjoint⟩

set_option maxHeartbeats 5000000 in
/- A pair-support family covering a core substantially larger than its
target set contains a clean pair: both endpoints lie in the core and occur
in no other chosen support.  The threshold is the double-counting bound
`3 * |Q| < 2 * |cell|`. -/
theorem exists_cleanPairSupport_of_threeTargetCard_lt_twoCoreCard
    {A : Set ℕ} {cell : Finset ℕ} {Q : Finset ℕ}
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q)
    (hcover : cell ⊆ finiteSupportChoiceUnion c)
    (hsmall : 3 * Q.card < 2 * cell.card) :
    ∃ q : {n // n ∈ Q},
      (c q).1.card = 2 ∧
      (c q).1 ⊆ cell ∧
      ∀ r : {n // n ∈ Q}, r ≠ q →
        Disjoint (c q).1 (c r).1 := by
  classical
  let rel : ℕ → {n // n ∈ Q} → Prop := fun x q => x ∈ (c q).1
  let incident : ℕ → Finset {n // n ∈ Q} := fun x =>
    Q.attach.bipartiteAbove rel x
  let Private : Finset ℕ := cell.filter fun x => (incident x).card = 1
  let Shared : Finset ℕ := cell \ Private
  have hPrivateCell : Private ⊆ cell := Finset.filter_subset _ _
  have hdegreePos : ∀ x ∈ cell, 0 < (incident x).card := by
    intro x hxCell
    have hxUnion := hcover hxCell
    obtain ⟨q, hqAttach, hxq⟩ := Finset.mem_biUnion.mp hxUnion
    apply Finset.card_pos.mpr
    refine ⟨q, ?_⟩
    exact Finset.mem_filter.mpr ⟨hqAttach, hxq⟩
  by_contra hclean
  have hPrivatePerSupport : ∀ q : {n // n ∈ Q},
      ((c q).1 ∩ Private).card ≤ 1 := by
    intro q
    by_contra hnot
    have hinterTwo : 2 ≤ ((c q).1 ∩ Private).card := by omega
    have hchosenUpper : (c q).1.card ≤ 2 :=
      additiveSupportFamily_cardAtMost A 2 q.1 (c q).1 (c q).2
    have hchosenTwo : (c q).1.card = 2 := by
      have hinterSub : (c q).1 ∩ Private ⊆ (c q).1 :=
        Finset.inter_subset_left
      have := Finset.card_le_card hinterSub
      omega
    have hinterEq : (c q).1 ∩ Private = (c q).1 := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hchosenTwo]
      exact hinterTwo
    have hchosenPrivate : (c q).1 ⊆ Private := by
      intro x hx
      have : x ∈ (c q).1 ∩ Private := by
        rw [hinterEq]
        exact hx
      exact (Finset.mem_inter.mp this).2
    have hchosenCell : (c q).1 ⊆ cell :=
      hchosenPrivate.trans hPrivateCell
    have hchosenDisjoint : ∀ r : {n // n ∈ Q}, r ≠ q →
        Disjoint (c q).1 (c r).1 := by
      intro r hrq
      rw [Finset.disjoint_left]
      intro x hxq hxr
      have hxPrivate := hchosenPrivate hxq
      have hdegreeOne : (incident x).card = 1 :=
        (Finset.mem_filter.mp hxPrivate).2
      have hqIncident : q ∈ incident x :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_attach Q q, hxq⟩
      have hrIncident : r ∈ incident x :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_attach Q r, hxr⟩
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hdegreeOne
      have hqu : q = u := by simpa [hu] using hqIncident
      have hru : r = u := by simpa [hu] using hrIncident
      exact hrq (hru.trans hqu.symm)
    exact hclean ⟨q, hchosenTwo, hchosenCell, hchosenDisjoint⟩
  have hPrivateCover : Private ⊆
      Q.attach.biUnion fun q => (c q).1 ∩ Private := by
    intro x hxPrivate
    have hxCell : x ∈ cell := hPrivateCell hxPrivate
    have hxUnion := hcover hxCell
    obtain ⟨q, hqAttach, hxq⟩ := Finset.mem_biUnion.mp hxUnion
    apply Finset.mem_biUnion.mpr
    exact ⟨q, hqAttach, Finset.mem_inter.mpr ⟨hxq, hxPrivate⟩⟩
  have hPrivateCard : Private.card ≤ Q.card := by
    calc
      Private.card ≤
          (Q.attach.biUnion fun q => (c q).1 ∩ Private).card :=
        Finset.card_le_card hPrivateCover
      _ ≤ ∑ q ∈ Q.attach, ((c q).1 ∩ Private).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ Q.attach, 1 := by
        apply Finset.sum_le_sum
        intro q hq
        exact hPrivatePerSupport q
      _ = Q.card := by simp
  have hSharedDegree : ∀ x ∈ Shared, 2 ≤ (incident x).card := by
    intro x hxShared
    have hxParts := Finset.mem_sdiff.mp hxShared
    have hpos := hdegreePos x hxParts.1
    have hne : (incident x).card ≠ 1 := by
      intro hone
      exact hxParts.2 (Finset.mem_filter.mpr ⟨hxParts.1, hone⟩)
    omega
  have hdoubleCount :
      (∑ x ∈ cell, (incident x).card) =
        ∑ q ∈ Q.attach,
          (cell.bipartiteBelow rel q).card := by
    simpa [incident] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := rel) (s := cell) (t := Q.attach))
  have htotalUpper :
      (∑ x ∈ cell, (incident x).card) ≤ 2 * Q.card := by
    rw [hdoubleCount]
    calc
      (∑ q ∈ Q.attach, (cell.bipartiteBelow rel q).card) ≤
          ∑ _q ∈ Q.attach, 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hsub : cell.bipartiteBelow rel q ⊆ (c q).1 := by
          intro x hx
          exact (Finset.mem_filter.mp hx).2
        exact (Finset.card_le_card hsub).trans
          (additiveSupportFamily_cardAtMost A 2 q.1 (c q).1 (c q).2)
      _ = 2 * Q.card := by simp [Nat.mul_comm]
  have hPrivateSum :
      (∑ x ∈ Private, (incident x).card) = Private.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro x hxPrivate
    exact (Finset.mem_filter.mp hxPrivate).2
  have hSharedSum :
      2 * Shared.card ≤ ∑ x ∈ Shared, (incident x).card := by
    calc
      2 * Shared.card = ∑ _x ∈ Shared, 2 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ Shared, (incident x).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hSharedDegree x hx
  have htotalLower :
      Private.card + 2 * Shared.card ≤
        ∑ x ∈ cell, (incident x).card := by
    calc
      Private.card + 2 * Shared.card ≤
          (∑ x ∈ Private, (incident x).card) +
            ∑ x ∈ Shared, (incident x).card := by
        rw [hPrivateSum]
        exact Nat.add_le_add_left hSharedSum Private.card
      _ = ∑ x ∈ cell, (incident x).card := by
        rw [Nat.add_comm]
        exact Finset.sum_sdiff hPrivateCell
  have hcardPartition : Shared.card + Private.card = cell.card := by
    exact Finset.card_sdiff_add_card_eq_card hPrivateCell
  omega

set_option maxHeartbeats 5000000 in
/- An even core certificate at the sharp counting threshold is an exact
pair-support cover.  If the core has `2 * m` points and there are exactly
`m` uniquely represented targets, core duality forces the union of their
chosen pair supports to have the full `2 * m` points.  Consequently every
chosen support has two points and the supports are pairwise disjoint. -/
theorem evenCoreUniquePairCertificate_forces_exactSupportCover
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {m : ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = 2 * m)
    (hQcard : Q.card = m)
    (hunique : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card = 1)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∃ i,
        cell i = finiteSupportChoiceUnion c ∧
        (finiteSupportChoiceUnion c).card = 2 * m ∧
        (∀ q : {n // n ∈ Q}, ∀ E,
          E ∈ additiveSupportFamily A 2 q.1 → E = (c q).1) ∧
        (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
        ∀ q r : {n // n ∈ Q}, q ≠ r →
          Disjoint (c q).1 (c r).1 := by
  classical
  have hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ
    apply Finset.card_pos.mp
    rw [hunique q hqQ]
    omega
  let c : FiniteSupportChoice (additiveSupportFamily A 2) Q := fun q =>
    ⟨(hrepresented q.1 q.2).choose,
      (hrepresented q.1 q.2).choose_spec⟩
  obtain ⟨i, hiCover⟩ :=
    exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
      hcore hcert c
  have hUupper : (finiteSupportChoiceUnion c).card ≤ 2 * m := by
    calc
      (finiteSupportChoiceUnion c).card ≤ 2 * Q.card :=
        finiteSupportChoiceUnion_card_le
          (additiveSupportFamily_cardAtMost A 2) c
      _ = 2 * m := by omega
  have hUlower : 2 * m ≤ (finiteSupportChoiceUnion c).card := by
    rw [← hcellCard i]
    exact Finset.card_le_card hiCover
  have hUcard : (finiteSupportChoiceUnion c).card = 2 * m := by omega
  have hcellEq : cell i = finiteSupportChoiceUnion c :=
    Finset.eq_of_subset_of_card_le hiCover (by
      rw [hUcard, hcellCard i])
  have hchosenUnique : ∀ q : {n // n ∈ Q}, ∀ E,
      E ∈ additiveSupportFamily A 2 q.1 → E = (c q).1 := by
    intro q E hER
    obtain ⟨S, hfamily⟩ :=
      Finset.card_eq_one.mp (hunique q.1 q.2)
    have hES : E = S := by
      simpa [hfamily] using hER
    have hcS : (c q).1 = S := by
      simpa [hfamily] using (c q).2
    exact hES.trans hcS.symm
  have hsupportCard : ∀ q : {n // n ∈ Q},
      (c q).1.card = 2 := by
    intro q
    have hmPos : 0 < m := by
      rw [← hQcard]
      exact Finset.card_pos.mpr ⟨q.1, q.2⟩
    let Q' : Finset ℕ := Q.erase q.1
    let cOther : FiniteSupportChoice
        (additiveSupportFamily A 2) Q' := fun r =>
      c ⟨r.1, Finset.mem_of_mem_erase r.2⟩
    let U' : Finset ℕ := finiteSupportChoiceUnion cOther
    have hcases : ∀ x, x ∈ finiteSupportChoiceUnion c →
        x ∈ (c q).1 ∨ x ∈ U' := by
      intro x hx
      obtain ⟨r, _hrAttach, hxr⟩ := Finset.mem_biUnion.mp hx
      by_cases hrq : r.1 = q.1
      · left
        have hrEq : r = q := Subtype.ext hrq
        exact hrEq ▸ hxr
      · right
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        apply finiteSupportChoice_subset_union cOther r'
        simpa [cOther, r'] using hxr
    have hUsub : finiteSupportChoiceUnion c ⊆ (c q).1 ∪ U' := by
      intro x hx
      exact Finset.mem_union.mpr (hcases x hx)
    have hU'card : U'.card ≤ 2 * (m - 1) := by
      calc
        U'.card ≤ 2 * Q'.card :=
          finiteSupportChoiceUnion_card_le
            (additiveSupportFamily_cardAtMost A 2) cOther
        _ = 2 * (m - 1) := by
          rw [Finset.card_erase_of_mem q.2, hQcard]
    have hchosenCard : (c q).1.card ≤ 2 :=
      additiveSupportFamily_cardAtMost A 2 q.1 (c q).1 (c q).2
    have hcardSub := Finset.card_le_card hUsub
    have hunionCard := Finset.card_union_le (c q).1 U'
    rw [hUcard] at hcardSub
    omega
  have hsupportDisjoint : ∀ q r : {n // n ∈ Q}, q ≠ r →
      Disjoint (c q).1 (c r).1 := by
    intro q r hqr
    have hmPos : 0 < m := by
      rw [← hQcard]
      exact Finset.card_pos.mpr ⟨q.1, q.2⟩
    let Q' : Finset ℕ := Q.erase q.1
    have hrqVal : r.1 ≠ q.1 := by
      intro hEq
      exact hqr (Subtype.ext hEq.symm)
    have hrQ' : r.1 ∈ Q' :=
      Finset.mem_erase.mpr ⟨hrqVal, r.2⟩
    let cOther : FiniteSupportChoice
        (additiveSupportFamily A 2) Q' := fun t =>
      c ⟨t.1, Finset.mem_of_mem_erase t.2⟩
    let U' : Finset ℕ := finiteSupportChoiceUnion cOther
    have hcases : ∀ x, x ∈ finiteSupportChoiceUnion c →
        x ∈ (c q).1 ∨ x ∈ U' := by
      intro x hx
      obtain ⟨t, _htAttach, hxt⟩ := Finset.mem_biUnion.mp hx
      by_cases htq : t.1 = q.1
      · left
        have htEq : t = q := Subtype.ext htq
        exact htEq ▸ hxt
      · right
        let t' : {n // n ∈ Q'} :=
          ⟨t.1, Finset.mem_erase.mpr ⟨htq, t.2⟩⟩
        apply finiteSupportChoice_subset_union cOther t'
        simpa [cOther, t'] using hxt
    have hUsub : finiteSupportChoiceUnion c ⊆ (c q).1 ∪ U' := by
      intro x hx
      exact Finset.mem_union.mpr (hcases x hx)
    have hrSub : (c r).1 ⊆ U' := by
      let r' : {n // n ∈ Q'} := ⟨r.1, hrQ'⟩
      intro x hxr
      apply finiteSupportChoice_subset_union cOther r'
      simpa [cOther, r'] using hxr
    rw [Finset.disjoint_left]
    intro x hxq hxr
    have hxU' : x ∈ U' := hrSub hxr
    have hinterPos : 0 < ((c q).1 ∩ U').card :=
      Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxq, hxU'⟩⟩
    have hU'card : U'.card ≤ 2 * (m - 1) := by
      calc
        U'.card ≤ 2 * Q'.card :=
          finiteSupportChoiceUnion_card_le
            (additiveSupportFamily_cardAtMost A 2) cOther
        _ = 2 * (m - 1) := by
          rw [Finset.card_erase_of_mem q.2, hQcard]
    have hcardSub := Finset.card_le_card hUsub
    have hunionInter :=
      Finset.card_union_add_card_inter (c q).1 U'
    rw [hUcard] at hcardSub
    have hqCard := hsupportCard q
    omega
  exact ⟨c, i, hcellEq, hUcard, hchosenUnique,
    hsupportCard, hsupportDisjoint⟩

set_option maxHeartbeats 5000000 in
/- The six-core, three-target instance retained as a convenient named
interface for the first nontrivial equality case. -/
theorem sixCoreThreeUniquePairCertificate_forces_exactSupportCover
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = 6)
    (hQcard : Q.card = 3)
    (hunique : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card = 1)
    (hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∃ i,
        cell i = finiteSupportChoiceUnion c ∧
        (finiteSupportChoiceUnion c).card = 6 ∧
        (∀ q : {n // n ∈ Q}, ∀ E,
          E ∈ additiveSupportFamily A 2 q.1 → E = (c q).1) ∧
        (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
        ∀ q r : {n // n ∈ Q}, q ≠ r →
          Disjoint (c q).1 (c r).1 := by
  simpa using
    (evenCoreUniquePairCertificate_forces_exactSupportCover
      (m := 3) hcore hcellCard hQcard hunique hcert)

set_option maxHeartbeats 5000000 in
/- If an order-three support contains a genuine two-point order-two support
of the same target, its third summand is forced to be zero. -/
theorem orderThreeSupport_eq_insert_zero_of_twoPointPairSupport_subset
    {A : Set ℕ} {q : ℕ} {E G : Finset ℕ}
    (hER : E ∈ additiveSupportFamily A 2 q)
    (hEcard : E.card = 2)
    (hGR : G ∈ additiveSupportFamily A 3 q)
    (hEG : E ⊆ G) :
    G = insert 0 E := by
  classical
  obtain ⟨x, y, hxy, hEeq⟩ := Finset.card_eq_two.mp hEcard
  have hxE : x ∈ E := by simp [hEeq]
  have hyE : y ∈ E := by simp [hEeq]
  have hxG : x ∈ G := hEG hxE
  have hyG : y ∈ G := hEG hyE
  have hxle : x ≤ q :=
    additiveSupportFamily_supportsBounded A 2 q E hER x hxE
  have hpairEq : E = pairSupport q x :=
    additiveSupportFamily_two_eq_pairSupport_of_mem hER hxE
  have hyComp : y = q - x := by
    have hyPair : y ∈ pairSupport q x := by
      rw [← hpairEq]
      exact hyE
    simp only [pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hyPair
    exact hyPair.resolve_left hxy.symm
  have hxySum : x + y = q := by omega
  obtain ⟨u, _huA, huG, hxyu⟩ :=
    OrderThreeUniqueHitRepairChoice.exists_thirdSummand
      hGR hxG hyG hxy
  have huZero : u = 0 := by omega
  have hzeroG : 0 ∈ G := huZero ▸ huG
  apply Finset.Subset.antisymm
  · intro z hzG
    by_cases hzx : z = x
    · subst z
      simp [hEeq]
    by_cases hzy : z = y
    · subst z
      simp [hEeq]
    have hxyz :=
      OrderThreeUniqueHitRepairChoice.sum_eq_of_three_distinct_mem
        hGR hxG hyG hzG hxy (fun h => hzx h.symm)
          (fun h => hzy h.symm)
    have hzZero : z = 0 := by omega
    simp [hzZero]
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzE
    · exact hzeroG
    · exact hEG hzE

set_option maxHeartbeats 5000000 in
/- In an exact perfect-matching core certificate, every order-three support
of a certificate target is rigid: it is precisely the zero-padding of that
target's matched pair support.  Otherwise force an endpoint missing from
the proposed support, choose all other blocks away from it, and route the
certificate destroyer. -/
theorem orderThreePerfectMatchingCore_forces_zeroPaddedSupports
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 4 ≤ (cell i).card)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q)
    (i : ℕ) (hcellEq : cell i = finiteSupportChoiceUnion c)
    (hsupportCard : ∀ q : {n // n ∈ Q}, (c q).1.card = 2)
    (hsupportDisjoint : ∀ q r : {n // n ∈ Q}, q ≠ r →
      Disjoint (c q).1 (c r).1)
    (hcert₃ : ∀ sel : BlockSelector F,
      (∀ j, (sel j).1 ∈ cell j) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q) :
    ∀ q : {n // n ∈ Q}, ∀ G,
      G ∈ additiveSupportFamily A 3 q.1 →
      G = insert 0 (c q).1 := by
  classical
  intro q G hGR
  have hpairSub : (c q).1 ⊆ G := by
    by_contra hnsub
    obtain ⟨x, hxq, hxG⟩ := Finset.not_subset.mp hnsub
    have hxUnion : x ∈ finiteSupportChoiceUnion c :=
      finiteSupportChoice_subset_union c q hxq
    have hxCell : x ∈ cell i := by
      rw [hcellEq]
      exact hxUnion
    have hGcard : G.card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3 q.1 G hGR
    obtain ⟨sel, hselCore, hselForced, hGdisjoint⟩ :=
      exists_coreSelector_forcedPoint_avoiding_threePointSet
        hcore hcellLower hxCell G hGcard hxG
    have hxSelected : x ∈ selectedSet sel := ⟨i, hselForced⟩
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨j, hj⟩
      apply hcellZero j
      rw [← hj]
      exact hselCore j
    have hselectedUnion : ∀ z,
        z ∈ finiteSupportChoiceUnion c →
        z ∈ selectedSet sel → z = x := by
      intro z hzUnion hzSelected
      have hzCell : z ∈ cell i := by
        rw [hcellEq]
        exact hzUnion
      exact P.eq_of_mem_sameBlock_of_mem_selectedSet sel
        (hcore i hzCell) (hcore i hxCell) hzSelected hxSelected
    obtain ⟨r, hrQ, hrDestroy⟩ := hcert₃ sel hselCore
    let rQ : {n // n ∈ Q} := ⟨r, hrQ⟩
    by_cases hrq : rQ = q
    · have hrVal : r = q.1 := congrArg Subtype.val hrq
      have hqDestroy : DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q.1 := by
        simpa [hrVal] using hrDestroy
      exact (hqDestroy G hGR) hGdisjoint
    · have hcrDisjoint : Disjoint ((c rQ).1 : Set ℕ)
          (selectedSet sel) := by
        rw [Set.disjoint_left]
        intro z hzr hzSelected
        have hzUnion : z ∈ finiteSupportChoiceUnion c :=
          finiteSupportChoice_subset_union c rQ
            (Finset.mem_coe.mp hzr)
        have hzx : z = x := hselectedUnion z hzUnion hzSelected
        have hxcr : x ∈ (c rQ).1 := hzx ▸ Finset.mem_coe.mp hzr
        exact Finset.disjoint_left.mp
          (hsupportDisjoint q rQ (fun h => hrq h.symm)) hxq hxcr
      let H : Finset ℕ := insert 0 (c rQ).1
      have hHR : H ∈ additiveSupportFamily A 3 r := by
        simpa [H, rQ] using
          (insert_mem_additiveSupportFamily_succ hzeroA (c rQ).2)
      have hHdisjoint : Disjoint (H : Set ℕ) (selectedSet sel) := by
        rw [Set.disjoint_left]
        intro z hzH hzSelected
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hzH) with rfl | hzr
        · exact hzeroSelected hzSelected
        · exact Set.disjoint_left.mp hcrDisjoint
            (Finset.mem_coe.mpr hzr) hzSelected
      exact (hrDestroy H hHR) hHdisjoint
  exact orderThreeSupport_eq_insert_zero_of_twoPointPairSupport_subset
    (c q).2 (hsupportCard q) hGR hpairSub

set_option maxHeartbeats 5000000 in
/- A clean pair in a low-slack core cover is enough for the same rigidity
routing as an exact perfect matching.  The selector additionally avoids the
small part of the support union outside the covered core. -/
theorem orderThreeCleanPairCore_forces_zeroPaddedSupport
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {k : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = k)
    (hk : 5 ≤ k)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q)
    (i : ℕ) (hcover : cell i ⊆ finiteSupportChoiceUnion c)
    (hsmall : 3 * Q.card < 2 * k)
    (q : {n // n ∈ Q})
    (hqCard : (c q).1.card = 2)
    (hqCore : (c q).1 ⊆ cell i)
    (hqDisjoint : ∀ r : {n // n ∈ Q}, r ≠ q →
      Disjoint (c q).1 (c r).1)
    (hcert₃ : ∀ sel : BlockSelector F,
      (∀ j, (sel j).1 ∈ cell j) →
      ∃ r ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) r) :
    ∀ G ∈ additiveSupportFamily A 3 q.1,
      G = insert 0 (c q).1 := by
  classical
  intro G hGR
  have hpairSub : (c q).1 ⊆ G := by
    by_contra hnsub
    obtain ⟨x, hxq, hxG⟩ := Finset.not_subset.mp hnsub
    have hxCell : x ∈ cell i := hqCore hxq
    let U : Finset ℕ := finiteSupportChoiceUnion c
    let slack : Finset ℕ := U \ cell i
    let H : Finset ℕ := G ∪ slack
    have hUupper : U.card ≤ 2 * Q.card :=
      finiteSupportChoiceUnion_card_le
        (additiveSupportFamily_cardAtMost A 2) c
    have hslackCard : slack.card = U.card - (cell i).card := by
      exact Finset.card_sdiff_of_subset hcover
    have hGcard : G.card ≤ 3 :=
      additiveSupportFamily_cardAtMost A 3 q.1 G hGR
    have hHcard : H.card ≤ G.card + slack.card :=
      Finset.card_union_le G slack
    have hHsmall : ∀ j, H.card < (cell j).card := by
      intro j
      rw [hcellCard j]
      have hiCard := hcellCard i
      omega
    have hxH : x ∉ H := by
      intro hxMem
      rcases Finset.mem_union.mp hxMem with hxG' | hxSlack
      · exact hxG hxG'
      · exact (Finset.mem_sdiff.mp hxSlack).2 hxCell
    obtain ⟨sel, hselCore, hselForced, hHdisjoint⟩ :=
      exists_coreSelector_forcedPoint_avoiding_finset
        hcore hxCell H hHsmall hxH
    have hxSelected : x ∈ selectedSet sel := ⟨i, hselForced⟩
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨j, hj⟩
      apply hcellZero j
      rw [← hj]
      exact hselCore j
    have hselectedUnion : ∀ z,
        z ∈ U → z ∈ selectedSet sel → z = x := by
      intro z hzU hzSelected
      by_cases hzCell : z ∈ cell i
      · exact P.eq_of_mem_sameBlock_of_mem_selectedSet sel
          (hcore i hzCell) (hcore i hxCell) hzSelected hxSelected
      · have hzSlack : z ∈ slack :=
          Finset.mem_sdiff.mpr ⟨hzU, hzCell⟩
        have hzH : z ∈ H := Finset.mem_union_right G hzSlack
        exact (Set.disjoint_left.mp hHdisjoint
          (Finset.mem_coe.mpr hzH) hzSelected).elim
    obtain ⟨r, hrQ, hrDestroy⟩ := hcert₃ sel hselCore
    let rQ : {n // n ∈ Q} := ⟨r, hrQ⟩
    by_cases hrq : rQ = q
    · have hrVal : r = q.1 := congrArg Subtype.val hrq
      have hqDestroy : DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q.1 := by
        simpa [hrVal] using hrDestroy
      have hGdisjoint : Disjoint (G : Set ℕ) (selectedSet sel) :=
        hHdisjoint.mono_left (by
          intro z hzG
          exact Finset.mem_coe.mpr (Finset.mem_union_left slack
            (Finset.mem_coe.mp hzG)))
      exact (hqDestroy G hGR) hGdisjoint
    · have hcrDisjoint : Disjoint ((c rQ).1 : Set ℕ)
          (selectedSet sel) := by
        rw [Set.disjoint_left]
        intro z hzr hzSelected
        have hzU : z ∈ U :=
          finiteSupportChoice_subset_union c rQ
            (Finset.mem_coe.mp hzr)
        have hzx : z = x := hselectedUnion z hzU hzSelected
        have hxcr : x ∈ (c rQ).1 := hzx ▸ Finset.mem_coe.mp hzr
        exact Finset.disjoint_left.mp
          (hqDisjoint rQ hrq) hxq hxcr
      let K : Finset ℕ := insert 0 (c rQ).1
      have hKR : K ∈ additiveSupportFamily A 3 r := by
        simpa [K, rQ] using
          (insert_mem_additiveSupportFamily_succ hzeroA (c rQ).2)
      have hKdisjoint : Disjoint (K : Set ℕ) (selectedSet sel) := by
        rw [Set.disjoint_left]
        intro z hzK hzSelected
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hzK) with rfl | hzr
        · exact hzeroSelected hzSelected
        · exact Set.disjoint_left.mp hcrDisjoint
            (Finset.mem_coe.mpr hzr) hzSelected
      exact (hrDestroy K hKR) hKdisjoint
  exact orderThreeSupport_eq_insert_zero_of_twoPointPairSupport_subset
    (c q).2 hqCard hGR hpairSub

set_option maxHeartbeats 5000000 in
/- An order-two asymptotic basis forbids arbitrarily late targets whose
entire order-three support family is the zero-padding of one fixed pair.
Choose three distinct positive basis elements `a < b < d`.  For a late
target `q`, represent each of `q-a`, `q-b`, and `q-d` by two terms and
adjoin the translated element.  Rigidity would put all three translated
elements into the same two-point support. -/
theorem eventually_no_zeroPaddedRigidPairTargets
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ N, ∀ Q : Finset ℕ,
      ∀ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        Q.Nonempty →
        (∀ q ∈ Q, N ≤ q) →
        (∀ q : {n // n ∈ Q}, (c q).1.card = 2) →
        (∀ q : {n // n ∈ Q}, ∀ G,
          G ∈ additiveSupportFamily A 3 q.1 →
          G = insert 0 (c q).1) →
        False := by
  classical
  obtain ⟨R, hR⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  obtain ⟨a, haA, haPos⟩ := hbasis.infinite.exists_gt 0
  obtain ⟨b, hbA, hab⟩ := hbasis.infinite.exists_gt a
  obtain ⟨d, hdA, hbd⟩ := hbasis.infinite.exists_gt b
  refine ⟨R + d, ?_⟩
  intro Q c hQ hQlate hsupportCard hrigid
  obtain ⟨q, hqQ⟩ := hQ
  let qQ : {n // n ∈ Q} := ⟨q, hqQ⟩
  have hRq : R + d ≤ q := hQlate q hqQ
  have htranslated : ∀ t, t ∈ A → 0 < t → t ≤ d →
      t ∈ (c qQ).1 := by
    intro t htA htPos htd
    have htq : t ≤ q := by omega
    have hRsub : R ≤ q - t := by omega
    obtain ⟨E, hER, _hEempty⟩ := hR (q - t) hRsub
    let G : Finset ℕ := insert t E
    have hGR : G ∈ additiveSupportFamily A 3 q := by
      have hlift := insert_mem_additiveSupportFamily_succ htA hER
      have hsum : t + (q - t) = q := Nat.add_sub_of_le htq
      simpa [G, hsum] using hlift
    have htG : t ∈ G := by simp [G]
    have hGEq : G = insert 0 (c qQ).1 := hrigid qQ G hGR
    have htZeroOrPair : t = 0 ∨ t ∈ (c qQ).1 := by
      simpa [hGEq] using htG
    exact htZeroOrPair.resolve_left (Nat.ne_of_gt htPos)
  have haPair : a ∈ (c qQ).1 :=
    htranslated a haA haPos (by omega)
  have hbPos : 0 < b := by omega
  have hbPair : b ∈ (c qQ).1 :=
    htranslated b hbA hbPos (by omega)
  have hdPos : 0 < d := by omega
  have hdPair : d ∈ (c qQ).1 :=
    htranslated d hdA hdPos le_rfl
  have hthreeSub : ({a, b, d} : Finset ℕ) ⊆ (c qQ).1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact haPair
    · exact hbPair
    · exact hdPair
  have hthreeCard : ({a, b, d} : Finset ℕ).card = 3 := by
    simp [Nat.ne_of_lt hab, Nat.ne_of_lt hbd,
      Nat.ne_of_lt (hab.trans hbd)]
  have hcard := Finset.card_le_card hthreeSub
  rw [hthreeCard, hsupportCard qQ] at hcard
  omega

set_option maxHeartbeats 5000000 in
/- Single-target interface to the preceding eventual obstruction. -/
theorem eventually_no_zeroPaddedRigidPairTarget
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ N, ∀ q E,
      N ≤ q →
      E ∈ additiveSupportFamily A 2 q →
      E.card = 2 →
      (∀ G ∈ additiveSupportFamily A 3 q,
        G = insert 0 E) →
      False := by
  classical
  obtain ⟨N, hN⟩ := eventually_no_zeroPaddedRigidPairTargets hbasis
  refine ⟨N, ?_⟩
  intro q E hqLate hER hEcard hrigid
  let Q : Finset ℕ := {q}
  let c : FiniteSupportChoice (additiveSupportFamily A 2) Q := fun r =>
    ⟨E, by
      have hrmem : r.1 ∈ ({q} : Finset ℕ) := by
        simpa only [Q] using r.2
      have hrq : r.1 = q := Finset.mem_singleton.mp hrmem
      simpa only [hrq] using hER⟩
  have hQ : Q.Nonempty := by simp [Q]
  have hQlate : ∀ r ∈ Q, N ≤ r := by
    intro r hrQ
    have hrmem : r ∈ ({q} : Finset ℕ) := by
      simpa only [Q] using hrQ
    have hrq : r = q := Finset.mem_singleton.mp hrmem
    simpa only [hrq] using hqLate
  have hsupportCard : ∀ r : {n // n ∈ Q}, (c r).1.card = 2 := by
    intro r
    exact hEcard
  have hrigid' : ∀ r : {n // n ∈ Q}, ∀ G,
      G ∈ additiveSupportFamily A 3 r.1 →
      G = insert 0 (c r).1 := by
    intro r G hGR
    have hrmem : r.1 ∈ ({q} : Finset ℕ) := by
      simpa only [Q] using r.2
    have hrq : r.1 = q := Finset.mem_singleton.mp hrmem
    have hGRq : G ∈ additiveSupportFamily A 3 q := by
      simpa only [hrq] using hGR
    simpa only [c] using hrigid G hGRq
  exact hN Q c hQ hQlate hsupportCard hrigid'

set_option maxHeartbeats 5000000 in
/- Reconnecting the exact order-two cover to genuine order-three
destruction forces every endpoint of the covered core to be pair-atomic.
If an endpoint `x` split through a pair support avoiding `x`, adjoin the
other endpoint `y` of its matching edge to obtain a three-term support of
the external target.  A core selector can be forced to choose `x` while
avoiding that support.  It meets no other matching edge, so zero-padding
shows that no other target can be the order-three destroyer; the designated
target also survives by construction, a contradiction. -/
theorem orderThreePerfectMatchingCore_forces_pairAtomic
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 4 ≤ (cell i).card)
    (c : FiniteSupportChoice (additiveSupportFamily A 2) Q)
    (i : ℕ) (hcellEq : cell i = finiteSupportChoiceUnion c)
    (hsupportCard : ∀ q : {n // n ∈ Q}, (c q).1.card = 2)
    (hsupportDisjoint : ∀ q r : {n // n ∈ Q}, q ≠ r →
      Disjoint (c q).1 (c r).1)
    (hcert₃ : ∀ sel : BlockSelector F,
      (∀ j, (sel j).1 ∈ cell j) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q) :
    ∀ x ∈ cell i, ¬ PairSplittableAwayFromSelf A x := by
  classical
  intro x hxCell hxSplit
  obtain ⟨E, hER, hxE⟩ := hxSplit
  have hxUnion : x ∈ finiteSupportChoiceUnion c := by
    rw [← hcellEq]
    exact hxCell
  obtain ⟨q, _hqAttach, hxq⟩ :=
    Finset.mem_biUnion.mp hxUnion
  obtain ⟨y, hyq, hyx⟩ :=
    Finset.exists_mem_ne (by rw [hsupportCard q]; omega) x
  have hxA : x ∈ A :=
    additiveSupportFamily_supportsIn A 2 q.1 (c q).1 (c q).2 x hxq
  have hyA : y ∈ A :=
    additiveSupportFamily_supportsIn A 2 q.1 (c q).1 (c q).2 y hyq
  have hpairEq : (c q).1 = pairSupport q.1 x :=
    additiveSupportFamily_two_eq_pairSupport_of_mem (c q).2 hxq
  have hyPair : y ∈ pairSupport q.1 x := by
    rw [← hpairEq]
    exact hyq
  have hyComp : y = q.1 - x := by
    simp only [pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hyPair
    exact hyPair.resolve_left hyx
  have hxle : x ≤ q.1 :=
    additiveSupportFamily_supportsBounded A 2 q.1
      (c q).1 (c q).2 x hxq
  have hyxSum : y + x = q.1 := by omega
  let H : Finset ℕ := insert y E
  have hHR : H ∈ additiveSupportFamily A 3 q.1 := by
    have hlift := insert_mem_additiveSupportFamily_succ hyA hER
    simpa [H, hyxSum] using hlift
  have hxH : x ∉ H := by
    intro hxMem
    rcases Finset.mem_insert.mp hxMem with hxy | hxE'
    · exact hyx hxy.symm
    · exact hxE hxE'
  have hEcard : E.card ≤ 2 :=
    additiveSupportFamily_cardAtMost A 2 x E hER
  have hHcard : H.card ≤ 3 := by
    exact (Finset.card_insert_le y E).trans (by omega)
  obtain ⟨sel, hselCore, hselForced, hHdisjoint⟩ :=
    exists_coreSelector_forcedPoint_avoiding_threePointSet
      hcore hcellLower hxCell H hHcard hxH
  have hxSelected : x ∈ selectedSet sel := ⟨i, hselForced⟩
  have hzeroSelected : 0 ∉ selectedSet sel := by
    rintro ⟨j, hj⟩
    apply hcellZero j
    rw [← hj]
    exact hselCore j
  have hselectedUnion : ∀ z,
      z ∈ finiteSupportChoiceUnion c →
      z ∈ selectedSet sel → z = x := by
    intro z hzUnion hzSelected
    have hzCell : z ∈ cell i := by
      rw [hcellEq]
      exact hzUnion
    exact P.eq_of_mem_sameBlock_of_mem_selectedSet sel
      (hcore i hzCell) (hcore i hxCell) hzSelected hxSelected
  obtain ⟨r, hrQ, hrDestroy⟩ := hcert₃ sel hselCore
  let rQ : {n // n ∈ Q} := ⟨r, hrQ⟩
  have hrEq : rQ = q := by
    by_contra hrq
    have hcrDisjoint : Disjoint ((c rQ).1 : Set ℕ)
        (selectedSet sel) := by
      rw [Set.disjoint_left]
      intro z hzr hzSelected
      have hzUnion : z ∈ finiteSupportChoiceUnion c :=
        finiteSupportChoice_subset_union c rQ
          (Finset.mem_coe.mp hzr)
      have hzx : z = x := hselectedUnion z hzUnion hzSelected
      have hxcr : x ∈ (c rQ).1 := hzx ▸ Finset.mem_coe.mp hzr
      exact Finset.disjoint_left.mp
        (hsupportDisjoint q rQ (fun h => hrq h.symm)) hxq hxcr
    let G : Finset ℕ := insert 0 (c rQ).1
    have hGR : G ∈ additiveSupportFamily A 3 r := by
      simpa [G, rQ] using
        (insert_mem_additiveSupportFamily_succ hzeroA (c rQ).2)
    have hGdisjoint : Disjoint (G : Set ℕ) (selectedSet sel) := by
      rw [Set.disjoint_left]
      intro z hzG hzSelected
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hzG) with rfl | hzr
      · exact hzeroSelected hzSelected
      · exact Set.disjoint_left.mp hcrDisjoint
          (Finset.mem_coe.mpr hzr) hzSelected
    exact (hrDestroy G hGR) hGdisjoint
  have hrVal : r = q.1 := congrArg Subtype.val hrEq
  have hqDestroy : DestroysAt (additiveSupportFamily A 3)
      (selectedSet sel) q.1 := by
    simpa [hrVal] using hrDestroy
  exact (hqDestroy H hHR) hHdisjoint

set_option maxHeartbeats 5000000 in
/- Complete classification at every even sharp threshold.  An order-three
certificate with `m` targets on `2 * m`-point cores descends to order two.
Minimalization cannot remove a target, and the scaled occupancy inequality
forces every target to have a unique pair support.  The supports therefore
form a perfect matching on one core; genuine order-three destruction then
makes every endpoint pair-atomic. -/
theorem extremalOrderThreeEvenCoreCertificate_forces_atomicPerfectMatching
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ} {m : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = 2 * m)
    (hm : 2 ≤ m)
    (hQcard : Q.card = m)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty)
    (hcert₃ : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∃ i,
        cell i = finiteSupportChoiceUnion c ∧
        (finiteSupportChoiceUnion c).card = 2 * m ∧
        (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
        (∀ q r : {n // n ∈ Q}, q ≠ r →
          Disjoint (c q).1 (c r).1) ∧
        ∀ x ∈ cell i, ¬ PairSplittableAwayFromSelf A x := by
  classical
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ cell i
  have hcert₂ : ∀ sel : BlockSelector F, Good sel →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert₃ sel hsel
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hsel i
    exact ⟨q, hqQ,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy⟩
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized₀⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₂
  have hrepresented₀ : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    exact hrepresented q (hQ₀Q hqQ₀)
  have hcellLower : ∀ i, 2 * m ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have hQ₀lower : 2 * m ≤ 2 * Q₀.card :=
    coreSelectorPairCertificate_forces_targetCard_lower
      hcore hcellLower hrepresented₀ hcert₀
  have hQ₀cardLower : m ≤ Q₀.card := by omega
  have hQ₀cardUpper : Q₀.card ≤ m := by
    rw [← hQcard]
    exact Finset.card_le_card hQ₀Q
  have hQ₀eq : Q₀ = Q :=
    Finset.eq_of_subset_of_card_le hQ₀Q (by omega)
  subst Q₀
  have hscaled : ∀ q ∈ Q,
      (2 * m - 2) * (additiveSupportFamily A 2 q).card ≤
        2 * (Q.erase q).card := by
    simpa using
      (minimalCorePairCertificate_forces_scaledPointwiseBound
        P hcore hcellLower (by omega) hcert₀ hlocalized₀)
  have hunique : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card = 1 := by
    intro q hqQ
    have heraseCard : (Q.erase q).card = m - 1 := by
      rw [Finset.card_erase_of_mem hqQ, hQcard]
    have hpos : 0 < (additiveSupportFamily A 2 q).card :=
      Finset.card_pos.mpr (hrepresented q hqQ)
    have hbound := hscaled q hqQ
    rw [heraseCard] at hbound
    have hfactorEq : 2 * m - 2 = 2 * (m - 1) := by omega
    rw [hfactorEq] at hbound
    have hbound' :
        (2 * (m - 1)) * (additiveSupportFamily A 2 q).card ≤
          (2 * (m - 1)) * 1 := by
      simpa using hbound
    have hfactorPos : 0 < 2 * (m - 1) := by omega
    have hle : (additiveSupportFamily A 2 q).card ≤ 1 :=
      Nat.le_of_mul_le_mul_left hbound' hfactorPos
    omega
  obtain ⟨c, i, hcellEq, hUcard, _hchosenUnique,
      hsupportCard, hsupportDisjoint⟩ :=
    evenCoreUniquePairCertificate_forces_exactSupportCover
      hcore hcellCard hQcard hunique hcert₀
  have hcellLowerFour : ∀ j, 4 ≤ (cell j).card := by
    intro j
    rw [hcellCard j]
    omega
  have hatomic : ∀ x ∈ cell i,
      ¬ PairSplittableAwayFromSelf A x :=
    orderThreePerfectMatchingCore_forces_pairAtomic
      P hzeroA hcellZero hcore hcellLowerFour c i hcellEq
        hsupportCard hsupportDisjoint hcert₃
  exact ⟨c, i, hcellEq, hUcard,
    hsupportCard, hsupportDisjoint, hatomic⟩

set_option maxHeartbeats 5000000 in
/- Scalable counterexample-level sharp residual.  For every `m ≥ 3`, the
repaired-option tower supplies `2 * m`-point cores and minimal late genuine
order-three certificates with at least `m` targets.  Equality at `m`
targets is completely rigid: one core is their pair-support perfect
matching and consists entirely of pair-atoms. -/
theorem counterexample_forces_minimalEvenOptionExternalCoreTripleCertificate
    {A : Set ℕ} {m : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (hm : 3 ≤ m) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 2 * m) ∧
      ∀ N, ∃ Q : Finset ℕ,
        m ≤ Q.card ∧
        2 * m ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        (∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q') ∧
        (Q.card = m →
          ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
            ∃ i,
              cell i = finiteSupportChoiceUnion c ∧
              (finiteSupportChoiceUnion c).card = 2 * m ∧
              (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
              (∀ q r : {n // n ∈ Q}, q ≠ r →
                Disjoint (c q).1 (c r).1) ∧
              ∀ x ∈ cell i,
                ¬ PairSplittableAwayFromSelf A x) := by
  classical
  have hsize : 5 + (2 * m - 5) = 2 * m := by omega
  have htower :
      ∃ T : RepairedOptionSystem A (2 * m),
        ∃ terminal : Fin (2 * m),
          ∀ i a, T.option i terminal ≤ T.option i a := by
    have htower₀ :=
      counterexample_forces_repairedOptionTower
        hbasis hzeroA hcounter (2 * m - 5)
    rw [hsize] at htower₀
    exact htower₀
  obtain ⟨T, _terminal, _hminimum⟩ := htower
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_minimalExternalCoreTripleCertificate
      hbasis hzeroA hcounter (by omega)
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, htargetLower, hQlate, hrepresented,
      hcert, hlocalized⟩ := hresidual N
  have hQcard : m ≤ Q.card := by omega
  have hatomicIfSharp : Q.card = m →
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ i,
          cell i = finiteSupportChoiceUnion c ∧
          (finiteSupportChoiceUnion c).card = 2 * m ∧
          (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
          (∀ q r : {n // n ∈ Q}, q ≠ r →
            Disjoint (c q).1 (c r).1) ∧
          ∀ x ∈ cell i,
            ¬ PairSplittableAwayFromSelf A x := by
    intro hQeq
    exact
      extremalOrderThreeEvenCoreCertificate_forces_atomicPerfectMatching
        P hzeroA hcellZero hcore hcellCard (by omega)
          hQeq hrepresented hcert
  exact ⟨Q, hQcard, htargetLower, hQlate, hrepresented,
    hcert, hlocalized, hatomicIfSharp⟩

set_option maxHeartbeats 5000000 in
/- Recurrent sharp-threshold dichotomy at every tower height.  Either late
minimal certificates eventually have strictly more than the counting
minimum `m`, or sharp `m`-target certificates recur arbitrarily late.  The
latter cores escape every finite set through their late pair supports and
therefore yield infinitely many pair-atoms. -/
theorem counterexample_forces_aboveSharpEvenCertificateTail_or_infinitePairAtomic
    {A : Set ℕ} {m : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (hm : 3 ≤ m) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 2 * m) ∧
      ((∃ N₀, ∀ N, N₀ ≤ N → ∃ Q : Finset ℕ,
          m + 1 ≤ Q.card ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ q ∈ Q,
            (additiveSupportFamily A 2 q).Nonempty) ∧
          (∀ sel : BlockSelector F,
            (∀ i, (sel i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q) ∧
          ∀ q ∈ Q, ∃ sel : BlockSelector F,
            (∀ i, (sel i).1 ∈ cell i) ∧
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q') ∨
        {x | x ∈ A ∧
          ¬ PairSplittableAwayFromSelf A x}.Infinite) := by
  classical
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    counterexample_forces_minimalEvenOptionExternalCoreTripleCertificate
      hbasis hzeroA hcounter hm
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard, ?_⟩
  let SharpAt : ℕ → Prop := fun N =>
    ∃ Q : Finset ℕ,
      Q.card = m ∧
      (∀ q ∈ Q, N ≤ q) ∧
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ i,
          cell i = finiteSupportChoiceUnion c ∧
          ∀ x ∈ cell i,
            ¬ PairSplittableAwayFromSelf A x
  by_cases heventual : ∃ N₀, ∀ N, N₀ ≤ N → ¬ SharpAt N
  · left
    obtain ⟨N₀, hN₀⟩ := heventual
    refine ⟨N₀, ?_⟩
    intro N hN₀N
    obtain ⟨Q, hQcard, _hQlower, hQlate, hrepresented,
        hcert, hlocalized, hatomicIfSharp⟩ := hresidual N
    have hQne : Q.card ≠ m := by
      intro hQeq
      apply hN₀ N hN₀N
      obtain ⟨c, i, hcellEq, _hUcard, _hsupportCard,
          _hsupportDisjoint, hatomic⟩ := hatomicIfSharp hQeq
      exact ⟨Q, hQeq, fun q hqQ => (hQlate q hqQ).1,
        c, i, hcellEq, hatomic⟩
    have hQabove : m + 1 ≤ Q.card := by omega
    exact ⟨Q, hQabove, hQlate, hrepresented, hcert, hlocalized⟩
  · right
    have hrecurrent : ∀ M, ∃ N, M ≤ N ∧ SharpAt N := by
      intro M
      by_contra hnot
      apply heventual
      refine ⟨M, ?_⟩
      intro N hMN hSharp
      exact hnot ⟨N, hMN, hSharp⟩
    let Atomic : Set ℕ :=
      {x | x ∈ A ∧ ¬ PairSplittableAwayFromSelf A x}
    show Atomic.Infinite
    by_contra hnot
    have hfinite : Atomic.Finite := Set.not_infinite.mp hnot
    let H : Finset ℕ := hfinite.toFinset
    obtain ⟨M, hM⟩ :=
      additiveSupportFamily_eventuallyEscapesFiniteCores A 2 H
    obtain ⟨N, hMN, Q, hQcard, hQlate,
        c, i, hcellEq, hatomic⟩ := hrecurrent M
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨q, hqQ⟩ := hQ
    let qQ : {n // n ∈ Q} := ⟨q, hqQ⟩
    have hMq : M ≤ q := hMN.trans (hQlate q hqQ)
    have hescape : ((c qQ).1 \ H).Nonempty :=
      hM q hMq (c qQ).1 (c qQ).2
    obtain ⟨x, hxDiff⟩ := hescape
    obtain ⟨hxSupport, hxH⟩ := Finset.mem_sdiff.mp hxDiff
    have hxUnion : x ∈ finiteSupportChoiceUnion c :=
      finiteSupportChoice_subset_union c qQ hxSupport
    have hxCell : x ∈ cell i := by
      rw [hcellEq]
      exact hxUnion
    have hxA : x ∈ A :=
      (P.mem_iff x).2 ⟨i, hcore i hxCell⟩
    have hxAtomic : ¬ PairSplittableAwayFromSelf A x :=
      hatomic x hxCell
    have hxInAtomic : x ∈ Atomic := ⟨hxA, hxAtomic⟩
    have hxInH : x ∈ H := by
      simpa [H] using hxInAtomic
    exact hxH hxInH

set_option maxHeartbeats 5000000 in
/- Strict scalable certificate bound.  The sharp equality case from the
preceding even-core residual would be an atomic perfect matching, hence by
routing every order-three support of every target would be its zero-padded
matched pair.  The eventual rigidity obstruction rules this out.  Thus for
each `m ≥ 3`, all sufficiently late minimal certificates on `2 * m`-point
cores have at least `m + 1` targets. -/
theorem counterexample_forces_eventuallyAboveSharpEvenCoreCertificates
    {A : Set ℕ} {m : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3)
    (hm : 3 ≤ m) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 2 * m) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q : Finset ℕ,
        m + 1 ≤ Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q' := by
  classical
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    counterexample_forces_minimalEvenOptionExternalCoreTripleCertificate
      hbasis hzeroA hcounter hm
  obtain ⟨N₀, hnoRigid⟩ :=
    eventually_no_zeroPaddedRigidPairTargets hbasis
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard,
    N₀, ?_⟩
  intro N hN₀N
  obtain ⟨Q, hQcard, _hQlower, hQlate, hrepresented,
      hcert, hlocalized, hatomicIfSharp⟩ := hresidual N
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hQne : Q.card ≠ m := by
    intro hQeq
    obtain ⟨c, i, hcellEq, _hUcard, hsupportCard,
        hsupportDisjoint, _hatomic⟩ := hatomicIfSharp hQeq
    have hcellLowerFour : ∀ j, 4 ≤ (cell j).card := by
      intro j
      rw [hcellCard j]
      omega
    have hrigid : ∀ q : {n // n ∈ Q}, ∀ G,
        G ∈ additiveSupportFamily A 3 q.1 →
        G = insert 0 (c q).1 :=
      orderThreePerfectMatchingCore_forces_zeroPaddedSupports
        P hzeroA hcellZero hcore hcellLowerFour c i hcellEq
          hsupportCard hsupportDisjoint hcert
    exact hnoRigid Q c hQ
      (fun q hqQ => hN₀N.trans (hQlate q hqQ).1)
      hsupportCard hrigid
  have hQabove : m + 1 ≤ Q.card := by omega
  exact ⟨Q, hQabove, hQlate, hrepresented, hcert, hlocalized⟩

set_option maxHeartbeats 5000000 in
/- Tower-wide strict certificate inequality.  At every repaired-option
height `k = 5 + n`, the generic core bound gives `k ≤ 2 * |Q|`.  Equality
would make `k` even and put the certificate in the extremal perfect-matching
case, whose zero-padded order-three rigidity is eventually impossible.
Hence sufficiently late minimal certificates satisfy the strict bound
`k < 2 * |Q|`. -/
theorem counterexample_forces_eventuallyStrictExternalCoreTripleCertificates
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ n, ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 5 + n) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q : Finset ℕ,
        5 + n < 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q' := by
  classical
  intro n
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter n
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_minimalExternalCoreTripleCertificate
      hbasis hzeroA hcounter (by omega)
  obtain ⟨N₀, hnoRigid⟩ :=
    eventually_no_zeroPaddedRigidPairTargets hbasis
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard,
    N₀, ?_⟩
  intro N hN₀N
  obtain ⟨Q, hQ, htargetLower, hQlate, hrepresented,
      hcert, hlocalized⟩ := hresidual N
  have hstrict : 5 + n < 2 * Q.card := by
    have hne : 5 + n ≠ 2 * Q.card := by
      intro heq
      have hQthree : 3 ≤ Q.card := by omega
      have hcellEven : ∀ i, (cell i).card = 2 * Q.card := by
        intro i
        rw [hcellCard i, heq]
      obtain ⟨c, i, hcellEq, _hUcard, hsupportCard,
          hsupportDisjoint, _hatomic⟩ :=
        extremalOrderThreeEvenCoreCertificate_forces_atomicPerfectMatching
          P hzeroA hcellZero hcore hcellEven (by omega)
            rfl hrepresented hcert
      have hcellLowerFour : ∀ j, 4 ≤ (cell j).card := by
        intro j
        rw [hcellCard j]
        omega
      have hrigid : ∀ q : {r // r ∈ Q}, ∀ G,
          G ∈ additiveSupportFamily A 3 q.1 →
          G = insert 0 (c q).1 :=
        orderThreePerfectMatchingCore_forces_zeroPaddedSupports
          P hzeroA hcellZero hcore hcellLowerFour c i hcellEq
            hsupportCard hsupportDisjoint hcert
      exact hnoRigid Q c hQ
        (fun q hqQ => hN₀N.trans (hQlate q hqQ).1)
        hsupportCard hrigid
    omega
  exact ⟨Q, hstrict, hQlate, hrepresented, hcert, hlocalized⟩

set_option maxHeartbeats 5000000 in
/- Quantitative `2/3` certificate bound.  If `3 * |Q| < 2 * k`, choose one
pair support at every target.  Core duality covers a `k`-point core, and the
clean-pair double count supplies a pair wholly inside that core with private
endpoints.  Low-slack routing makes its target zero-padded rigid, contrary
to the eventual single-target obstruction. -/
theorem counterexample_forces_eventuallyTwoThirdExternalCoreTripleCertificates
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∀ n, ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 5 + n) ∧
      ∃ N₀, ∀ N, N₀ ≤ N → ∃ Q : Finset ℕ,
        2 * (5 + n) ≤ 3 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        ∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q' := by
  classical
  intro n
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter n
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_minimalExternalCoreTripleCertificate
      hbasis hzeroA hcounter (by omega)
  obtain ⟨N₀, hnoRigid⟩ :=
    eventually_no_zeroPaddedRigidPairTarget hbasis
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard,
    N₀, ?_⟩
  intro N hN₀N
  obtain ⟨Q, _hQ, _htargetLower, hQlate, hrepresented,
      hcert, hlocalized⟩ := hresidual N
  have htwoThird : 2 * (5 + n) ≤ 3 * Q.card := by
    by_contra hnot
    have hsmall : 3 * Q.card < 2 * (5 + n) := by omega
    let c : FiniteSupportChoice (additiveSupportFamily A 2) Q := fun q =>
      ⟨(hrepresented q.1 q.2).choose,
        (hrepresented q.1 q.2).choose_spec⟩
    obtain ⟨i, hcover⟩ :=
      exists_coveredCell_of_coreSelectorCertificate_and_pairChoice
        hzeroA hcellZero hcore hcert c
    have hsmallCell : 3 * Q.card < 2 * (cell i).card := by
      rw [hcellCard i]
      exact hsmall
    obtain ⟨q, hqCard, hqCore, hqDisjoint⟩ :=
      exists_cleanPairSupport_of_threeTargetCard_lt_twoCoreCard
        c hcover hsmallCell
    have hrigid : ∀ G ∈ additiveSupportFamily A 3 q.1,
        G = insert 0 (c q).1 :=
      orderThreeCleanPairCore_forces_zeroPaddedSupport
        P hzeroA hcellZero hcore hcellCard (by omega)
          c i hcover hsmall q hqCard hqCore hqDisjoint hcert
    exact hnoRigid q.1 (c q).1
      (hN₀N.trans (hQlate q.1 q.2).1)
      (c q).2 hqCard hrigid
  exact ⟨Q, htwoThird, hQlate, hrepresented, hcert, hlocalized⟩

set_option maxHeartbeats 5000000 in
/- Complete classification of a three-target order-three certificate on
six-point cores.  Descend it to order two, minimize, and use the six-core
lower bound: the minimal subcertificate still has at least three targets,
so it is the whole three-target set.  The scaled occupancy inequality then
forces unique pair supports.  Those supports form a perfect matching on one
core, and the preceding routing theorem makes every endpoint pair-atomic. -/
theorem threeTargetOrderThreeSixCoreCertificate_forces_atomicPerfectMatching
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellCard : ∀ i, (cell i).card = 6)
    (hQcard : Q.card = 3)
    (hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty)
    (hcert₃ : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
      ∃ i,
        cell i = finiteSupportChoiceUnion c ∧
        (finiteSupportChoiceUnion c).card = 6 ∧
        (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
        (∀ q r : {n // n ∈ Q}, q ≠ r →
          Disjoint (c q).1 (c r).1) ∧
        ∀ x ∈ cell i, ¬ PairSplittableAwayFromSelf A x := by
  classical
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ cell i
  have hcert₂ : ∀ sel : BlockSelector F, Good sel →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert₃ sel hsel
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hsel i
    exact ⟨q, hqQ,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy⟩
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized₀⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₂
  have hrepresented₀ : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    exact hrepresented q (hQ₀Q hqQ₀)
  have hcellLower : ∀ i, 6 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have hQ₀lower : 6 ≤ 2 * Q₀.card :=
    coreSelectorPairCertificate_forces_targetCard_lower
      hcore hcellLower hrepresented₀ hcert₀
  have hQ₀cardLower : 3 ≤ Q₀.card := by omega
  have hQ₀cardUpper : Q₀.card ≤ 3 := by
    rw [← hQcard]
    exact Finset.card_le_card hQ₀Q
  have hQ₀eq : Q₀ = Q :=
    Finset.eq_of_subset_of_card_le hQ₀Q (by omega)
  subst Q₀
  have hscaled : ∀ q ∈ Q,
      4 * (additiveSupportFamily A 2 q).card ≤
        2 * (Q.erase q).card := by
    simpa using
      (minimalCorePairCertificate_forces_scaledPointwiseBound
        P hcore hcellLower (by omega) hcert₀ hlocalized₀)
  have hunique : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card = 1 := by
    intro q hqQ
    have heraseCard : (Q.erase q).card = 2 := by
      rw [Finset.card_erase_of_mem hqQ, hQcard]
    have hpos : 0 < (additiveSupportFamily A 2 q).card :=
      Finset.card_pos.mpr (hrepresented q hqQ)
    have hbound := hscaled q hqQ
    rw [heraseCard] at hbound
    omega
  obtain ⟨c, i, hcellEq, hUcard, _hchosenUnique,
      hsupportCard, hsupportDisjoint⟩ :=
    sixCoreThreeUniquePairCertificate_forces_exactSupportCover
      hcore hcellCard hQcard hunique hcert₀
  have hcellLowerFour : ∀ j, 4 ≤ (cell j).card := by
    intro j
    rw [hcellCard j]
    omega
  have hatomic : ∀ x ∈ cell i,
      ¬ PairSplittableAwayFromSelf A x :=
    orderThreePerfectMatchingCore_forces_pairAtomic
      P hzeroA hcellZero hcore hcellLowerFour c i hcellEq
        hsupportCard hsupportDisjoint hcert₃
  exact ⟨c, i, hcellEq, hUcard,
    hsupportCard, hsupportDisjoint, hatomic⟩

set_option maxHeartbeats 5000000 in
/- Counterexample-level order-three residual on six-point cores.  Minimize
the late strong-deletion certificate before descending its order.  Thus, if
the extremal target count is three, the preceding classification applies to
the genuine order-three certificate itself: one core is a perfect matching
of its three pair supports and all six endpoints are pair-atomic. -/
theorem counterexample_forces_minimalSixOptionExternalCoreTripleCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 6) ∧
      ∀ N, ∃ Q : Finset ℕ,
        3 ≤ Q.card ∧
        6 ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q) ∧
        (∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 3)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q') ∧
        (Q.card = 3 →
          ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
            ∃ i,
              cell i = finiteSupportChoiceUnion c ∧
              (finiteSupportChoiceUnion c).card = 6 ∧
              (∀ q : {n // n ∈ Q}, (c q).1.card = 2) ∧
              (∀ q r : {n // n ∈ Q}, q ≠ r →
                Disjoint (c q).1 (c r).1) ∧
              ∀ x ∈ cell i,
                ¬ PairSplittableAwayFromSelf A x) := by
  classical
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter 1
  obtain ⟨F, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_externalCoreCertificate
      hbasis hzeroA hcounter (by omega)
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, T.cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, _hQlower, hQlate, hcert₃, _hbounded⟩ :=
    hresidual (max N N₂)
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ T.cell i
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized₀⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₃
  have hQ₀late : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hrepresented₀ : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLower : ∀ i, 6 ≤ (T.cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : 6 ≤ 2 * Q₀.card :=
    coreSelectorCertificate_forces_targetCard_lower
      hzeroA hcellZero hcore hcellLower hrepresented₀ hcert₀
  have hQ₀card : 3 ≤ Q₀.card := by omega
  have hatomicIfThree : Q₀.card = 3 →
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q₀,
        ∃ i,
          T.cell i = finiteSupportChoiceUnion c ∧
          (finiteSupportChoiceUnion c).card = 6 ∧
          (∀ q : {n // n ∈ Q₀}, (c q).1.card = 2) ∧
          (∀ q r : {n // n ∈ Q₀}, q ≠ r →
            Disjoint (c q).1 (c r).1) ∧
          ∀ x ∈ T.cell i,
            ¬ PairSplittableAwayFromSelf A x := by
    intro hQ₀eq
    exact threeTargetOrderThreeSixCoreCertificate_forces_atomicPerfectMatching
      P hzeroA hcellZero hcore hcellCard hQ₀eq hrepresented₀ hcert₀
  exact ⟨Q₀, hQ₀card, htargetLower, hQ₀late,
    hrepresented₀, hcert₀, hlocalized₀, hatomicIfThree⟩

set_option maxHeartbeats 5000000 in
/- The recurrent consequence of the preceding residual.  Either all
sufficiently late minimal certificates have left the extremal three-target
case, or those extremal certificates recur arbitrarily late.  In the latter
case their atomic matched cores escape every finite set, yielding infinitely
many pair-atomic elements of `A`. -/
theorem counterexample_forces_fourTargetTail_or_infinitePairAtomic
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 6) ∧
      ((∃ N₀, ∀ N, N₀ ≤ N → ∃ Q : Finset ℕ,
          4 ≤ Q.card ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ q ∈ Q,
            (additiveSupportFamily A 2 q).Nonempty) ∧
          (∀ sel : BlockSelector F,
            (∀ i, (sel i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q) ∧
          ∀ q ∈ Q, ∃ sel : BlockSelector F,
            (∀ i, (sel i).1 ∈ cell i) ∧
            DestroysAt (additiveSupportFamily A 3)
              (selectedSet sel) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q') ∨
        {x | x ∈ A ∧
          ¬ PairSplittableAwayFromSelf A x}.Infinite) := by
  classical
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    counterexample_forces_minimalSixOptionExternalCoreTripleCertificate
      hbasis hzeroA hcounter
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard, ?_⟩
  let ThreeAt : ℕ → Prop := fun N =>
    ∃ Q : Finset ℕ,
      Q.card = 3 ∧
      (∀ q ∈ Q, N ≤ q) ∧
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ i,
          cell i = finiteSupportChoiceUnion c ∧
          ∀ x ∈ cell i,
            ¬ PairSplittableAwayFromSelf A x
  by_cases heventual : ∃ N₀, ∀ N, N₀ ≤ N → ¬ ThreeAt N
  · left
    obtain ⟨N₀, hN₀⟩ := heventual
    refine ⟨N₀, ?_⟩
    intro N hN₀N
    obtain ⟨Q, hQcard, _hQlower, hQlate, hrepresented,
        hcert, hlocalized, hatomicIfThree⟩ := hresidual N
    have hQne : Q.card ≠ 3 := by
      intro hQeq
      apply hN₀ N hN₀N
      obtain ⟨c, i, hcellEq, _hUcard, _hsupportCard,
          _hsupportDisjoint, hatomic⟩ := hatomicIfThree hQeq
      exact ⟨Q, hQeq, fun q hqQ => (hQlate q hqQ).1,
        c, i, hcellEq, hatomic⟩
    have hQfour : 4 ≤ Q.card := by omega
    exact ⟨Q, hQfour, hQlate, hrepresented, hcert, hlocalized⟩
  · right
    have hrecurrent : ∀ M, ∃ N, M ≤ N ∧ ThreeAt N := by
      intro M
      by_contra hnot
      apply heventual
      refine ⟨M, ?_⟩
      intro N hMN hThree
      exact hnot ⟨N, hMN, hThree⟩
    let Atomic : Set ℕ :=
      {x | x ∈ A ∧ ¬ PairSplittableAwayFromSelf A x}
    show Atomic.Infinite
    by_contra hnot
    have hfinite : Atomic.Finite := Set.not_infinite.mp hnot
    let H : Finset ℕ := hfinite.toFinset
    obtain ⟨M, hM⟩ :=
      additiveSupportFamily_eventuallyEscapesFiniteCores A 2 H
    obtain ⟨N, hMN, Q, hQcard, hQlate,
        c, i, hcellEq, hatomic⟩ := hrecurrent M
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨q, hqQ⟩ := hQ
    let qQ : {n // n ∈ Q} := ⟨q, hqQ⟩
    have hMq : M ≤ q := hMN.trans (hQlate q hqQ)
    have hescape : ((c qQ).1 \ H).Nonempty :=
      hM q hMq (c qQ).1 (c qQ).2
    obtain ⟨x, hxDiff⟩ := hescape
    obtain ⟨hxSupport, hxH⟩ := Finset.mem_sdiff.mp hxDiff
    have hxUnion : x ∈ finiteSupportChoiceUnion c :=
      finiteSupportChoice_subset_union c qQ hxSupport
    have hxCell : x ∈ cell i := by
      rw [hcellEq]
      exact hxUnion
    have hxA : x ∈ A :=
      (P.mem_iff x).2 ⟨i, hcore i hxCell⟩
    have hxAtomic : ¬ PairSplittableAwayFromSelf A x :=
      hatomic x hxCell
    have hxInAtomic : x ∈ Atomic := ⟨hxA, hxAtomic⟩
    have hxInH : x ∈ H := by
      simpa [H] using hxInAtomic
    exact hxH hxInH

set_option maxHeartbeats 5000000 in
/- Six-option minimal residual.  At the smallest permitted certificate size
`Q.card = 3`, the generic scaled inequality is tight and every external
target has exactly one order-two support. -/
theorem counterexample_forces_minimalSixOptionExternalCorePairCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 6) ∧
      ∀ N, ∃ Q : Finset ℕ,
        3 ≤ Q.card ∧
        6 ≤ 2 * Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ q ∈ Q,
          (additiveSupportFamily A 2 q).Nonempty) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q) ∧
        (∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 2)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q') ∧
        (∀ q ∈ Q,
          4 * (additiveSupportFamily A 2 q).card ≤
            2 * (Q.erase q).card) ∧
        (Q.card = 3 → ∀ q ∈ Q,
          (additiveSupportFamily A 2 q).card = 1) ∧
        (Q.card = 3 →
          ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
            ∃ i, cell i = finiteSupportChoiceUnion c ∧
              (finiteSupportChoiceUnion c).card = 6) := by
  classical
  obtain ⟨T, _terminal, _hminimum⟩ :=
    counterexample_forces_repairedOptionTower
      hbasis hzeroA hcounter 1
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    T.exists_minimalExternalCorePairCertificate
      hbasis hzeroA hcounter (by omega)
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, hQlower, hQlate, hrepresented,
      hcert, hlocalized, hscaled⟩ := hresidual N
  have hQcard : 3 ≤ Q.card := by omega
  have hscaled' : ∀ q ∈ Q,
      4 * (additiveSupportFamily A 2 q).card ≤
        2 * (Q.erase q).card := by
    simpa using hscaled
  have huniqueIfThree : Q.card = 3 → ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card = 1 := by
    intro hQcardEq q hqQ
    have heraseCard : (Q.erase q).card = 2 := by
      rw [Finset.card_erase_of_mem hqQ, hQcardEq]
    have hpos : 0 < (additiveSupportFamily A 2 q).card :=
      Finset.card_pos.mpr (hrepresented q hqQ)
    have hbound := hscaled' q hqQ
    rw [heraseCard] at hbound
    omega
  have hexactIfThree : Q.card = 3 →
      ∃ c : FiniteSupportChoice (additiveSupportFamily A 2) Q,
        ∃ i, cell i = finiteSupportChoiceUnion c ∧
          (finiteSupportChoiceUnion c).card = 6 := by
    intro hQcardEq
    obtain ⟨c, i, hcellEq, hUcard, _hchosenUnique⟩ :=
      sixCoreThreeUniquePairCertificate_forces_exactSupportCover
        hcore hcellCard hQcardEq (huniqueIfThree hQcardEq) hcert
    exact ⟨c, i, hcellEq, hUcard⟩
  exact ⟨Q, hQcard, hQlower, hQlate, hrepresented,
    hcert, hlocalized, hscaled', huniqueIfThree, hexactIfThree⟩

set_option maxHeartbeats 5000000 in
/-- Minimal order-two form of the five-option residual.  Minimalization
retains the five-core lower bound, so at least three external targets remain;
every remaining target has a private core selector and satisfies the sharper
occupancy bound `3 * |R₂(q)| ≤ 2 * |Q.erase q|`.  In particular, a
three-target certificate would give every target a unique pair support. -/
theorem counterexample_forces_minimalFiveOptionExternalCorePairCertificate
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hzeroA : 0 ∈ A)
    (hcounter : ∀ D, D ⊆ A → D.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ D) 3) :
    ∃ F cell : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      (∀ i, cell i ⊆ F i) ∧
      (∀ i, 0 ∉ cell i) ∧
      (∀ i, (cell i).card = 5) ∧
      ∀ N, ∃ Q : Finset ℕ,
        3 ≤ Q.card ∧
        (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
        (∀ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) →
          ∃ q ∈ Q,
            DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q) ∧
        (∀ q ∈ Q, ∃ sel : BlockSelector F,
          (∀ i, (sel i).1 ∈ cell i) ∧
          DestroysAt (additiveSupportFamily A 2)
            (selectedSet sel) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A 2)
              (selectedSet sel) q') ∧
        (∀ q ∈ Q,
          3 * (additiveSupportFamily A 2 q).card ≤
            2 * (Q.erase q).card) ∧
        (Q.card = 3 → ∀ q ∈ Q,
          (additiveSupportFamily A 2 q).card = 1) := by
  classical
  obtain ⟨F, cell, P, hcore, hcellZero, hcellCard, hresidual⟩ :=
    counterexample_forces_fiveOptionExternalCoreCertificate
      hbasis hzeroA hcounter
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, cell, P, hcore, hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQcard, _htargetLower, hQlate,
      hcert₃, _hqBound⟩ := hresidual (max N N₂)
  let Good : BlockSelector F → Prop := fun sel =>
    ∀ i, (sel i).1 ∈ cell i
  have hcert₂ : ∀ sel : BlockSelector F, Good sel →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert₃ sel hsel
    have hzeroSelected : 0 ∉ selectedSet sel := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hsel i
    exact ⟨q, hqQ,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy⟩
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₂
  have hQ₀late : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hrepresented : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLowerFive : ∀ i, 5 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : 5 ≤ 2 * Q₀.card :=
    coreSelectorPairCertificate_forces_targetCard_lower
      hcore hcellLowerFive hrepresented hcert₀
  have hQ₀card : 3 ≤ Q₀.card := by omega
  have hscaled : ∀ q ∈ Q₀,
      3 * (additiveSupportFamily A 2 q).card ≤
        2 * (Q₀.erase q).card :=
    by
      simpa using
        (minimalCorePairCertificate_forces_scaledPointwiseBound
          P hcore hcellLowerFive (by omega) hcert₀ hlocalized)
  have huniqueIfThree : Q₀.card = 3 → ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).card = 1 := by
    intro hQcard q hqQ₀
    have heraseCard : (Q₀.erase q).card = 2 := by
      rw [Finset.card_erase_of_mem hqQ₀, hQcard]
    have hpos : 0 < (additiveSupportFamily A 2 q).card :=
      Finset.card_pos.mpr (hrepresented q hqQ₀)
    have hbound := hscaled q hqQ₀
    rw [heraseCard] at hbound
    omega
  exact ⟨Q₀, hQ₀card, hQ₀late, hcert₀,
    hlocalized, hscaled, huniqueIfThree⟩

set_option maxHeartbeats 5000000 in
/-- Pointwise pair-support bound retaining genuine order-three target
localization.  For the other targets use the triple supports supplied by the
private selector, and for `q` use a zero-padded pair support.  The fixed
triple-support union has at most `3 * (Q.erase q).card` vertices, giving the
corresponding pointwise bound while preserving the original order-three
certificate. -/
theorem minimalCoreTripleCertificate_forces_pointwise_boundedPairFamilies
    {A : Set ℕ} {F cell : ℕ → Finset ℕ} {Q : Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hzeroA : 0 ∈ A)
    (hcellZero : ∀ i, 0 ∉ cell i)
    (hcore : ∀ i, cell i ⊆ F i)
    (hcellLower : ∀ i, 3 ≤ (cell i).card)
    (hcert : ∀ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ s : BlockSelector F,
      (∀ i, (s i).1 ∈ cell i) ∧
      DestroysAt (additiveSupportFamily A 3) (selectedSet s) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt (additiveSupportFamily A 3)
          (selectedSet s) q') :
    ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).card ≤
        3 * (Q.erase q).card := by
  classical
  intro q hqQ
  obtain ⟨s, hsCore, _hqDestroy, hprivate⟩ :=
    hlocalized q hqQ
  let Q' : Finset ℕ := Q.erase q
  have hsurvive : ∀ r : {n // n ∈ Q'},
      ∃ H ∈ additiveSupportFamily A 3 r.1,
        Disjoint (H : Set ℕ) (selectedSet s) := by
    intro r
    have hr := Finset.mem_erase.mp r.2
    exact not_destroysAt_iff.mp
      (hprivate r.1 hr.2 hr.1)
  choose chosen hchosenMem hchosenDisjoint using hsurvive
  let cOther : FiniteSupportChoice
      (additiveSupportFamily A 3) Q' := fun r =>
    ⟨chosen r, hchosenMem r⟩
  let U : Finset ℕ := finiteSupportChoiceUnion cOther
  have hUDisjoint : Disjoint (U : Set ℕ) (selectedSet s) := by
    rw [Set.disjoint_left]
    intro x hxU hxSelected
    obtain ⟨r, _hrAttach, hxSupport⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
    exact Set.disjoint_left.mp (hchosenDisjoint r)
      (Finset.mem_coe.mpr hxSupport) hxSelected
  let I : Finset ℕ := U.image (blockIndex P)
  have hassign : ∀ E : {E // E ∈ additiveSupportFamily A 2 q},
      ∃ i, i ∈ I ∧ (s i).1 ∈ E.1 := by
    intro E
    let cFull : FiniteSupportChoice
        (additiveSupportFamily A 3) Q := fun r =>
      if hrq : r.1 = q then
        ⟨insert 0 E.1, by simpa [hrq] using
          (insert_mem_additiveSupportFamily_succ hzeroA E.2)⟩
      else
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        ⟨(cOther r').1, (cOther r').2⟩
    have hfullCases : ∀ x,
        x ∈ finiteSupportChoiceUnion cFull →
          x ∈ insert 0 E.1 ∨ x ∈ U := by
      intro x hx
      obtain ⟨r, _hrAttach, hxr⟩ := Finset.mem_biUnion.mp hx
      by_cases hrq : r.1 = q
      · left
        simpa [cFull, hrq] using hxr
      · right
        let r' : {n // n ∈ Q'} :=
          ⟨r.1, Finset.mem_erase.mpr ⟨hrq, r.2⟩⟩
        apply finiteSupportChoice_subset_union cOther r'
        simpa [cFull, hrq, r'] using hxr
    obtain ⟨i, hiCover⟩ :=
      exists_coveredCell_of_coreSelectorCertificate_and_supportChoice
        hcore hcert cFull
    have hsE : (s i).1 ∈ E.1 := by
      rcases hfullCases (s i).1 (hiCover (hsCore i)) with hsPad | hsU
      · rcases Finset.mem_insert.mp hsPad with hsZero | hsE
        · exact (hcellZero i (hsZero ▸ hsCore i)).elim
        · exact hsE
      · exact (Set.disjoint_left.mp hUDisjoint
          (Finset.mem_coe.mpr hsU) ⟨i, rfl⟩).elim
    have hcellHitsU : ¬ Disjoint (cell i) U := by
      intro hdisjoint
      have hcellE : cell i ⊆ E.1 := by
        intro x hxCell
        rcases hfullCases x (hiCover hxCell) with hxPad | hxU
        · rcases Finset.mem_insert.mp hxPad with hxZero | hxE
          · exact (hcellZero i (hxZero ▸ hxCell)).elim
          · exact hxE
        · exact (Finset.disjoint_left.mp hdisjoint hxCell hxU).elim
      have hcardLe := Finset.card_le_card hcellE
      have hEcard :=
        additiveSupportFamily_cardAtMost A 2 q E.1 E.2
      have hcellCard := hcellLower i
      omega
    obtain ⟨u, huCell, huU⟩ :=
      Finset.not_disjoint_iff.mp hcellHitsU
    have huIndex : blockIndex P u = i :=
      P.blockIndex_eq_of_mem (hcore i huCell)
    have hiI : i ∈ I :=
      Finset.mem_image.mpr ⟨u, huU, huIndex⟩
    exact ⟨i, hiI, hsE⟩
  choose assigned hassignedI hselectedMem using hassign
  let assignedSub : {E // E ∈ additiveSupportFamily A 2 q} →
      {i // i ∈ I} := fun E => ⟨assigned E, hassignedI E⟩
  have hassignedInj : Function.Injective assignedSub := by
    intro E E' hindex
    apply Subtype.ext
    by_contra hEE'
    have hindexVal : assigned E = assigned E' :=
      congrArg Subtype.val hindex
    have hxE := hselectedMem E
    have hxE' : (s (assigned E)).1 ∈ E'.1 := by
      rw [hindexVal]
      exact hselectedMem E'
    exact Finset.disjoint_left.mp
      (additiveSupportFamily_two_isMatching A q E.2 E'.2 hEE')
      hxE hxE'
  have hsupportCardI : (additiveSupportFamily A 2 q).card ≤ I.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective assignedSub hassignedInj
  have hIcardU : I.card ≤ U.card := Finset.card_image_le
  have hUcard : U.card ≤ 3 * Q'.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A 3) cOther
  exact hsupportCardI.trans (hIcardU.trans hUcard)

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
/-- Four-option finite-certificate bridge.  The fourth repaired layer gives
one fixed partition into exact four-point cores.  Every selector restricted
to those cores preserves all internal targets, so strong deletion produces
only external certificate targets.  Eventual order-two representability and
the four-point core force at least two certificate targets, while the sharp
pair-family bound remains available. -/
theorem counterexample_forces_fourOptionExternalCoreCertificate
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
        (∀ i, (cell i).card = 4) ∧
        ∀ N, ∃ Q : Finset ℕ,
          2 ≤ Q.card ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ sel : BlockSelector F,
            (∀ i, (sel i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 3)
                (selectedSet sel) q) ∧
          ∃ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨B, hBA, hB, S, f, p, r, s, g, h, j,
      hzeroS, hwitness, hAvoid, hpData, hrData, hsData,
      hjointDisjoint, hg, hh, hcrossS, hj⟩ :=
    counterexample_forces_quadruplySelfRepairedOptionReservoir
      hbasis hzeroA hcounter
  let optionSet : ℕ → Finset ℕ := threeRepairOptionSet p r s
  have hoptionA : ∀ b ∈ B, (optionSet b : Set ℕ) ⊆ A := by
    intro b hb x hx
    simp only [optionSet, threeRepairOptionSet, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hxp | hxr | hxs
    · subst x
      obtain ⟨w, hfw⟩ := hwitness b hb
      apply w.vertices_subset
      rw [← hfw]
      exact Finset.sdiff_subset (hpData b hb).1
    · subst x
      exact additiveSupportFamily_supportsIn A 3 (p b) (g b)
        (hg b hb).1 (r b)
          (Finset.mem_sdiff.mp (hrData b hb).1).1
    · subst x
      exact additiveSupportFamily_supportsIn A 3 (r b) (h b)
        (hh b hb).1 (s b) (hsData b hb).1
  have hoptionOut : ∀ b ∈ B,
      Disjoint (optionSet b : Set ℕ) B := by
    intro b hb
    rw [Set.disjoint_left]
    intro x hxOption hxB
    simp only [optionSet, threeRepairOptionSet, Finset.mem_coe,
      Finset.mem_insert, Finset.mem_singleton] at hxOption
    rcases hxOption with hxp | hxr | hxs
    · exact Set.disjoint_left.mp (hAvoid b hb)
        (Finset.mem_coe.mpr
          (hxp ▸ Finset.sdiff_subset (hpData b hb).1)) hxB
    · exact Set.disjoint_left.mp (hg b hb).2.2.1
        (Finset.mem_coe.mpr
          (hxr ▸ (Finset.mem_sdiff.mp (hrData b hb).1).1)) hxB
    · exact Set.disjoint_left.mp (hh b hb).2.2.1
        (Finset.mem_coe.mpr (hxs ▸ (hsData b hb).1)) hxB
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
  have hoptionOld : ∀ b ∈ B, ∀ x ∈ optionSet b,
      x ∈ (f b ∪ g b) ∪ h b := by
    intro b hb x hx
    simp only [optionSet, threeRepairOptionSet, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mp (hpData b hb).1).1)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_sdiff.mp (hrData b hb).1).1)
    · exact Finset.mem_union_right _ (hsData b hb).1
  have hoptionCases : ∀ b ∈ B, ∀ x ∈ optionSet b,
      x ∈ ({p b, r b} : Finset ℕ) ∨ x = s b := by
    intro b hb x hx
    simp only [optionSet, threeRepairOptionSet, Finset.mem_insert,
      Finset.mem_singleton] at hx ⊢
    tauto
  have hoptionDisjoint : ∀ b ∈ B, ∀ d ∈ B, b ≠ d →
      Disjoint (optionSet b) (optionSet d) := by
    intro b hb d hd hbd
    rw [Finset.disjoint_left]
    intro x hxb hxd
    rcases hoptionCases b hb x hxb with hxbPetal | hxbS <;>
      rcases hoptionCases d hd x hxd with hxdPetal | hxdS
    · exact Finset.disjoint_left.mp
        (hjointDisjoint b hb d hd hbd)
        (hoptionPetal b hb x hxbPetal)
        (hoptionPetal d hd x hxdPetal)
    · exact hcrossS b hb d hd hbd
        (hxdS ▸ hoptionOld b hb x hxb)
    · exact hcrossS d hd b hb hbd.symm
        (hxbS ▸ hoptionOld d hd x hxd)
    · exact hcrossS b hb d hd hbd
        (hxdS ▸ hoptionOld b hb x hxb)
  obtain ⟨e, F, P, hcore₀, _hcardStep⟩ :=
    exists_finiteBlockPartition_for_atomOptionCells
      hBA hB optionSet hoptionA hoptionOut hoptionDisjoint
  let cell : ℕ → Finset ℕ := fun i =>
    fourRepairedOptionCell p r s (e i).1
  have hcellEq : ∀ i,
      atomOptionCell optionSet (e i).1 = cell i := by
    intro i
    rfl
  have hcore : ∀ i, cell i ⊆ F i := by
    intro i
    rw [← hcellEq i]
    exact hcore₀ i
  have hcellCard : ∀ i, (cell i).card = 4 := by
    intro i
    exact fourRepairedOptionCell_card
      (hsData (e i).1 (e i).2).2.2
      (hrData (e i).1 (e i).2).2
      (hpData (e i).1 (e i).2).2
  have hcellZero : ∀ i, 0 ∉ cell i := by
    intro i hzeroCell
    have hspos := (hsData (e i).1 (e i).2).2.1
    have hsr := (hsData (e i).1 (e i).2).2.2
    have hrp := (hrData (e i).1 (e i).2).2
    have hpb := (hpData (e i).1 (e i).2).2
    simp only [cell, fourRepairedOptionCell, atomOptionCell,
      threeRepairOptionSet, Finset.mem_insert,
      Finset.mem_singleton] at hzeroCell
    rcases hzeroCell with hzeroB | hzeroP | hzeroR | hzeroS'
    <;> omega
  have hsurviveCore : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∀ q ∈ A, ∃ G ∈ additiveSupportFamily A 3 q,
        Disjoint (G : Set ℕ) (selectedSet sel) := by
    intro sel hsel
    exact internalTarget_survives_fourRepairedOptionSelector
      hzeroA hzeroS hwitness hAvoid
      (fun b hb => (hpData b hb).1)
      (fun b hb => (hrData b hb).1)
      (fun b hb => ⟨(hsData b hb).1, (hsData b hb).2.1⟩)
      hjointDisjoint hg hh hcrossS hj sel hsel
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨B, hBA, hB, F, cell, P, hcore,
    hcellZero, hcellCard, ?_⟩
  intro N
  obtain ⟨Q₀, hQ₀late, hcert₀⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      (strongOrderThreeDeletion_of_counterexample hcounter)
      F P (max N N₂)
  let Q : Finset ℕ := Q₀.filter fun q => q ∉ A
  have hcert : ∀ sel : BlockSelector F,
      (∀ i, (sel i).1 ∈ cell i) →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 3)
          (selectedSet sel) q := by
    intro sel hsel
    obtain ⟨q, hqQ₀, hqDestroy⟩ := hcert₀ sel
    have hqA : q ∉ A := by
      intro hqA
      obtain ⟨G, hGR, hGdisjoint⟩ :=
        hsurviveCore sel hsel q hqA
      exact (hqDestroy G hGR) hGdisjoint
    exact ⟨q, Finset.mem_filter.mpr ⟨hqQ₀, hqA⟩,
      hqDestroy⟩
  let atomSelector : BlockSelector F := fun i =>
    ⟨(e i).1, hcore i (by
      simp [cell, fourRepairedOptionCell, atomOptionCell])⟩
  have hatomCore : ∀ i, (atomSelector i).1 ∈ cell i := by
    intro i
    simp [atomSelector, cell, fourRepairedOptionCell, atomOptionCell]
  obtain ⟨q₀, hq₀Q, _hq₀Destroy⟩ :=
    hcert atomSelector hatomCore
  have hQ : Q.Nonempty := ⟨q₀, hq₀Q⟩
  have hQlate : ∀ q ∈ Q, N ≤ q ∧ q ∉ A := by
    intro q hqQ
    have hq := Finset.mem_filter.mp hqQ
    exact ⟨(le_max_left N N₂).trans (hQ₀late q hq.1), hq.2⟩
  have hrepresented : ∀ q ∈ Q,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ
    have hqQ₀ := (Finset.mem_filter.mp hqQ).1
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans (hQ₀late q hqQ₀))
    exact ⟨E, hER⟩
  have hcellLowerFour : ∀ i, 4 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have htargetLower : 4 ≤ 2 * Q.card :=
    coreSelectorCertificate_forces_targetCard_lower
      hzeroA hcellZero hcore hcellLowerFour hrepresented hcert
  have hQcard : 2 ≤ Q.card := by omega
  have hcellLowerThree : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
    omega
  obtain ⟨q, hqQ, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLowerThree hcert
  exact ⟨Q, hQcard, hQlate, hcert, q, hqQ, hqBound⟩

set_option maxHeartbeats 5000000 in
/-- Minimal external-core residual.  In addition to excluding every target
in `A`, shrink the restricted three-option certificate until every remaining
external target has a private core selector: that selector destroys the
chosen target and no other target in the same certificate.  The sharp
`2 * Q.card` pair-support bound is retained after shrinking, while every
target satisfies the pointwise bound `3 * (Q.erase q).card`. -/
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
          2 ≤ Q.card ∧
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
          (∀ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤
              3 * (Q.erase q).card) ∧
          ∃ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤ 2 * Q.card := by
  classical
  obtain ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
      hcellCard, hresidual⟩ :=
    counterexample_forces_externalCoreCertificate_boundedPairFamily
      hbasis hzeroA hcounter
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
    hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, hQN, hcert, _hqBound⟩ :=
    hresidual (max N N₂)
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
    have hqLate := hQN q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hQ₀represented : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQN q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLower : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  obtain ⟨q, hqQ₀, hqBound⟩ :=
    coreSelectorCertificate_forces_boundedPairFamily_sharp
      P hzeroA hcellZero hcore hcellLower hcert₀
  have hpointwise : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).card ≤
        3 * (Q₀.erase q).card :=
    minimalCoreTripleCertificate_forces_pointwise_boundedPairFamilies
      P hzeroA hcellZero hcore hcellLower hcert₀ hlocalized
  have hQ₀card : 2 ≤ Q₀.card := by
    by_contra hcard
    have hcardLe : Q₀.card ≤ 1 := by omega
    have hcardPos : 0 < Q₀.card := Finset.card_pos.mpr hQ₀
    have hcardEq : Q₀.card = 1 := by omega
    have heraseCard : (Q₀.erase q₀).card = 0 := by
      rw [Finset.card_erase_of_mem hq₀Q₀, hcardEq]
    have hsupportPos : 0 < (additiveSupportFamily A 2 q₀).card :=
      Finset.card_pos.mpr (hQ₀represented q₀ hq₀Q₀)
    have hsupportBound := hpointwise q₀ hq₀Q₀
    rw [heraseCard] at hsupportBound
    omega
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
  refine ⟨Q₀, hQ₀card, hQ₀N, hcert₀, hlocalized₂,
    hpointwise, q, hqQ₀, ?_⟩
  simpa using hqBound

set_option maxHeartbeats 5000000 in
/-- Order-two minimalization of the external-core obstruction.  Because zero
is retained, the restricted order-three certificate is also an order-two
certificate.  After minimizing at order two, every external target has a
private core selector and every one of its pair-support families—not merely
one family—has size at most `2 * (Q.erase q).card`.  Eventual order-two
representability also rules out singleton certificates. -/
theorem counterexample_forces_minimalExternalCorePairCertificate
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
          2 ≤ Q.card ∧
          (∀ q ∈ Q, N ≤ q ∧ q ∉ A) ∧
          (∀ s : BlockSelector F,
            (∀ i, (s i).1 ∈ cell i) →
            ∃ q ∈ Q,
              DestroysAt (additiveSupportFamily A 2)
                (selectedSet s) q) ∧
          (∀ q ∈ Q, ∃ s : BlockSelector F,
            (∀ i, (s i).1 ∈ cell i) ∧
            DestroysAt (additiveSupportFamily A 2)
              (selectedSet s) q ∧
            ∀ q' ∈ Q, q' ≠ q →
              ¬ DestroysAt (additiveSupportFamily A 2)
                (selectedSet s) q') ∧
          ∀ q ∈ Q,
            (additiveSupportFamily A 2 q).card ≤
              2 * (Q.erase q).card := by
  classical
  obtain ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
      hcellCard, hresidual⟩ :=
    counterexample_forces_externalCoreCertificate_boundedPairFamily
      hbasis hzeroA hcounter
  obtain ⟨N₂, hN₂⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨B, hBA, hB, F, cell, P, hcore, hcellZero,
    hcellCard, ?_⟩
  intro N
  obtain ⟨Q, _hQ, hQlate, hcert₃, _hqBound⟩ :=
    hresidual (max N N₂)
  let Good : BlockSelector F → Prop := fun s =>
    ∀ i, (s i).1 ∈ cell i
  have hcert₂ : ∀ s : BlockSelector F, Good s →
      ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A 2) (selectedSet s) q := by
    intro s hs
    obtain ⟨q, hqQ, hqDestroy⟩ := hcert₃ s hs
    have hzeroSelected : 0 ∉ selectedSet s := by
      rintro ⟨i, hi⟩
      apply hcellZero i
      rw [← hi]
      exact hs i
    exact ⟨q, hqQ,
      orderThree_destroyer_descends_to_orderTwo_of_zero_retained
        hzeroA hzeroSelected hqDestroy⟩
  obtain ⟨Q₀, hQ₀Q, hcert₀, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate_on Good hcert₂
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
  have hQ₀late : ∀ q ∈ Q₀, N ≤ q ∧ q ∉ A := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    exact ⟨(le_max_left N N₂).trans hqLate.1, hqLate.2⟩
  have hQ₀represented : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).Nonempty := by
    intro q hqQ₀
    have hqLate := hQlate q (hQ₀Q hqQ₀)
    obtain ⟨E, hER, _hEempty⟩ :=
      hN₂ q ((le_max_right N N₂).trans hqLate.1)
    exact ⟨E, hER⟩
  have hcellLower : ∀ i, 3 ≤ (cell i).card := by
    intro i
    rw [hcellCard i]
  have hpointwise : ∀ q ∈ Q₀,
      (additiveSupportFamily A 2 q).card ≤
        2 * (Q₀.erase q).card :=
    minimalCorePairCertificate_forces_pointwise_boundedPairFamilies
      P hcore hcellLower hcert₀ hlocalized
  have hQ₀card : 2 ≤ Q₀.card := by
    by_contra hcard
    have hcardLe : Q₀.card ≤ 1 := by omega
    have hcardPos : 0 < Q₀.card := Finset.card_pos.mpr hQ₀
    have hcardEq : Q₀.card = 1 := by omega
    have heraseCard : (Q₀.erase q₀).card = 0 := by
      rw [Finset.card_erase_of_mem hq₀Q₀, hcardEq]
    have hsupportPos : 0 < (additiveSupportFamily A 2 q₀).card :=
      Finset.card_pos.mpr (hQ₀represented q₀ hq₀Q₀)
    have hsupportBound := hpointwise q₀ hq₀Q₀
    rw [heraseCard] at hsupportBound
    omega
  exact ⟨Q₀, hQ₀card, hQ₀late, hcert₀, hlocalized,
    hpointwise⟩

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
