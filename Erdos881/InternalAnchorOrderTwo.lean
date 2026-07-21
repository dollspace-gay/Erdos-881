import Erdos881.AdditiveSupports

/-!
# The order-two external-anchor counting lemma

This file isolates the additive information supplied by an internal-anchor
successor destroyer.  If a finite set `T` destroys all three-term
representations of `n`, then every external `b ∈ A \ T` turns an order-two
support of `n - b` into a hit of `T`.  Swapping the hit and the external
anchor produces an order-two support of the common target `n - x`.

The resulting incidence count is the sharp quantitative fact available from
the order-two matching property: more than `2 * |T| * r` external anchors
force more than `r` pair supports at one target `n - x`, with `x ∈ T`.
-/

open scoped BigOperators

namespace Erdos881

/-- Swap an external summand `b` with a chosen vertex `x` of a two-term
representation of `n - b`.  The complementary summand is unchanged, so the
new pair represents `n - x`. -/
theorem pairSupport_swap_external
    {A : Set ℕ} {n b x : ℕ} {E : Finset ℕ}
    (hbA : b ∈ A)
    (hbn : b ≤ n)
    (hER : E ∈ additiveSupportFamily A 2 (n - b))
    (hxE : x ∈ E) :
    pairSupport (n - x) b ∈ additiveSupportFamily A 2 (n - x) := by
  have hxle : x ≤ n - b :=
    additiveSupportFamily_supportsBounded A 2 (n - b) E hER x hxE
  have hbx : b + x ≤ n := by omega
  have hcompE : n - b - x ∈ E := by
    rw [additiveSupportFamily_two_eq_pairSupport_of_mem hER hxE]
    simp [pairSupport]
  have hcompA : n - b - x ∈ A :=
    additiveSupportFamily_supportsIn A 2 (n - b) E hER
      (n - b - x) hcompE
  have hbnx : b ≤ n - x := by omega
  apply pairSupport_mem_additiveSupportFamily hbnx hbA
  have heq : n - x - b = n - b - x := by omega
  simpa [heq] using hcompA

/-- An order-three destroyer hit by many usable external anchors forces
order-two representation growth at one of the translated targets `n - x`,
where `x` is a vertex of the destroyer.

The factor `2` is unavoidable in this incidence argument: after swapping,
an order-two support can contain at most two of the external anchors. -/
theorem large_externalAnchorSet_forces_pairSupportGrowth
    {A : Set ℕ} {n r : ℕ} {T B : Finset ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) (T : Set ℕ) n)
    (hBA : ∀ b ∈ B, b ∈ A)
    (hBT : Disjoint B T)
    (hble : ∀ b ∈ B, b ≤ n)
    (hrep : ∀ b ∈ B,
      (additiveSupportFamily A 2 (n - b)).Nonempty)
    (hlarge : 2 * T.card * r < B.card) :
    ∃ x ∈ T, x ≤ n ∧
      r < (additiveSupportFamily A 2 (n - x)).card := by
  classical
  let chosenSupport : ∀ b : {b // b ∈ B}, Finset ℕ := fun b =>
    (hrep b.1 b.2).choose
  have hchosenSupport : ∀ b : {b // b ∈ B},
      chosenSupport b ∈ additiveSupportFamily A 2 (n - b.1) := by
    intro b
    exact (hrep b.1 b.2).choose_spec
  have hdescend : ∀ b : {b // b ∈ B},
      DestroysAt (additiveSupportFamily A 2) (T : Set ℕ) (n - b.1) := by
    intro b
    exact additiveSuccessorTransversalsDescend A 2
      T n hdestroy b.1 (hBA b.1 b.2)
      (fun hbT => Finset.disjoint_left.mp hBT b.2
        (Finset.mem_coe.mp hbT))
      (hble b.1 b.2)
  let hit : ∀ b : {b // b ∈ B}, {x // x ∈ T} := fun b =>
    let w := Set.not_disjoint_iff.mp
      (hdescend b (chosenSupport b) (hchosenSupport b))
    ⟨w.choose, Finset.mem_coe.mp w.choose_spec.2⟩
  have hhitSupport : ∀ b : {b // b ∈ B},
      (hit b).1 ∈ chosenSupport b := by
    intro b
    exact Finset.mem_coe.mp
      (Set.not_disjoint_iff.mp
        (hdescend b (chosenSupport b) (hchosenSupport b))).choose_spec.1
  have hhitBounded : ∀ b : {b // b ∈ B}, (hit b).1 ≤ n := by
    intro b
    exact le_trans
      (additiveSupportFamily_supportsBounded A 2 (n - b.1)
        (chosenSupport b) (hchosenSupport b) (hit b).1 (hhitSupport b))
      (Nat.sub_le n b.1)
  let boundedT : Finset ℕ := T.filter fun x => x ≤ n
  let boundedHit : ∀ b : {b // b ∈ B}, {x // x ∈ boundedT} := fun b =>
    ⟨(hit b).1, Finset.mem_filter.mpr ⟨(hit b).2, hhitBounded b⟩⟩
  let swappedSupport (b : {b // b ∈ B}) : Finset ℕ :=
    pairSupport (n - (hit b).1) b.1
  have hswappedSupport : ∀ b : {b // b ∈ B},
      swappedSupport b ∈
        additiveSupportFamily A 2 (n - (hit b).1) := by
    intro b
    exact pairSupport_swap_external
      (hBA b.1 b.2) (hble b.1 b.2)
      (hchosenSupport b) (hhitSupport b)
  have hbSwapped : ∀ b : {b // b ∈ B}, b.1 ∈ swappedSupport b := by
    intro b
    simp [swappedSupport, pairSupport]
  let Target := Σ x : {x // x ∈ boundedT},
    {y // y ∈
      (additiveSupportFamily A 2 (n - x.1)).biUnion id}
  let encode : {b // b ∈ B} → Target := fun b =>
    ⟨boundedHit b, ⟨b.1, Finset.mem_biUnion.mpr
      ⟨swappedSupport b, hswappedSupport b, hbSwapped b⟩⟩⟩
  have hencode : Function.Injective encode := by
    intro b c hbc
    apply Subtype.ext
    exact congrArg (fun z : Target => z.2.1) hbc
  have hdomainTarget : B.card ≤ Fintype.card Target := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective encode hencode
  by_contra hnone
  push Not at hnone
  have hunionBound : ∀ x : {x // x ∈ boundedT},
      ((additiveSupportFamily A 2 (n - x.1)).biUnion id).card ≤
        2 * r := by
    intro x
    calc
      ((additiveSupportFamily A 2 (n - x.1)).biUnion id).card ≤
          ∑ E ∈ additiveSupportFamily A 2 (n - x.1), E.card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _E ∈ additiveSupportFamily A 2 (n - x.1), 2 := by
        gcongr with E hER
        exact additiveSupportFamily_cardAtMost A 2 (n - x.1) E hER
      _ = 2 * (additiveSupportFamily A 2 (n - x.1)).card := by
        simp [Nat.mul_comm]
      _ ≤ 2 * r := Nat.mul_le_mul_left 2 <|
        hnone x.1 (Finset.mem_filter.mp x.2).1
          (Finset.mem_filter.mp x.2).2
  have htargetBound : Fintype.card Target ≤ T.card * (2 * r) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    calc
      (∑ x : {x // x ∈ boundedT},
          ((additiveSupportFamily A 2 (n - x.1)).biUnion id).card) ≤
          ∑ _x : {x // x ∈ boundedT}, 2 * r := by
        gcongr with x
        exact hunionBound x
      _ = boundedT.card * (2 * r) := by simp
      _ ≤ T.card * (2 * r) := by
        exact Nat.mul_le_mul_right (2 * r) <|
          Finset.card_le_card (Finset.filter_subset _ _)
  have hupper : B.card ≤ 2 * T.card * r := by
    calc
      B.card ≤ Fintype.card Target := hdomainTarget
      _ ≤ T.card * (2 * r) := htargetBound
      _ = 2 * T.card * r := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
  omega

/-- Basis-specialized form.  Once all translated predecessors `n - b` lie
past the order-two basis threshold, the existence assumption in
`large_externalAnchorSet_forces_pairSupportGrowth` is automatic. -/
theorem IsExactTupleAsymptoticBasis.large_externalAnchorSet_forces_pairSupportGrowth
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ N, ∀ {n r : ℕ} {T B : Finset ℕ},
      DestroysAt (additiveSupportFamily A 3) (T : Set ℕ) n →
      (∀ b ∈ B, b ∈ A) →
      Disjoint B T →
      (∀ b ∈ B, N + b ≤ n) →
      2 * T.card * r < B.card →
      ∃ x ∈ T, x ≤ n ∧
        r < (additiveSupportFamily A 2 (n - x)).card := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro n r T B hdestroy hBA hBT hlate hlarge
  apply Erdos881.large_externalAnchorSet_forces_pairSupportGrowth
    hdestroy hBA hBT
  · intro b hbB
    have := hlate b hbB
    omega
  · intro b hbB
    obtain ⟨E, hER, _hEempty⟩ := hN (n - b) (by
      have := hlate b hbB
      omega)
    exact ⟨E, hER⟩
  · exact hlarge

/-! ## From bounded moving transversals to moving pair stars -/

/-- Full translate destroyers with the cardinal bound retained.  The earlier
`HasFullTranslateDestroyersByAnchor` deliberately discarded this bound when
building disjoint rows; the order-two incidence argument needs it. -/
def HasBoundedFullTranslateDestroyersByAnchor
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ L, ∃ n T q a,
      L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
      T.card ≤ m ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/-- Relative bounded moving recurrence already gives bounded *full*
destroyers.  Eventual escape from the protected core upgrades the outside
transversal without changing its cardinality. -/
theorem boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 1)) A Q) :
    HasBoundedFullTranslateDestroyersByAnchor A k Q := by
  have hmovingAnchor :=
    (boundedMovingOnFiniteTranslates_iff_byAnchor hQ).mp hmoving
  intro F hFA
  obtain ⟨m, hm⟩ := hmovingAnchor F hFA
  obtain ⟨K, hK⟩ :=
    additiveSupportFamily_eventuallyEscapesFiniteCores A (k + 1) F
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis.succ
  refine ⟨m, ?_⟩
  intro L
  obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩ := hm (max L (max K N))
  have hLa : L ≤ a := le_trans (le_max_left L (max K N)) haLower
  have hKn : K ≤ n := by
    have hKa : K ≤ a :=
      le_trans (le_trans (le_max_left K N)
        (le_max_right L (max K N))) haLower
    omega
  have hNn : N ≤ n := by
    have hNa : N ≤ a :=
      le_trans (le_trans (le_max_right K N)
        (le_max_right L (max K N))) haLower
    omega
  have hdestroy :
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
    intro E hER
    have hEF : (E \ F).Nonempty := hK n hKn E hER
    have hDmem :
        E \ F ∈ outsideSupportHypergraph
          (additiveSupportFamily A (k + 1)) F n := by
      apply Finset.mem_erase.mpr
      exact ⟨Finset.nonempty_iff_ne_empty.mp hEF,
        Finset.mem_image.mpr ⟨E, hER, rfl⟩⟩
    obtain ⟨x, hx⟩ := htrans (E \ F) hDmem
    obtain ⟨hxEF, hxT⟩ := Finset.mem_inter.mp hx
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, (Finset.mem_sdiff.mp hxEF).1,
      Finset.mem_coe.mpr hxT⟩
  obtain ⟨E, hER, _hEempty⟩ := hN n hNn
  have hTnonempty : T.Nonempty := by
    obtain ⟨x, _hxE, hxT⟩ :=
      Set.not_disjoint_iff.mp (hdestroy E hER)
    exact ⟨x, Finset.mem_coe.mp hxT⟩
  exact ⟨n, T, q, a, hLa, hqQ, haA, hnqa,
    hTA, hTF, hTnonempty, hTcard, hdestroy⟩

/-- A bounded full destroyer recurring arbitrarily late over `Q + A`
forces an arbitrarily large order-two representation star.  No density or
bounded-gap hypothesis is used: after learning the bound `m`, choose a
finite set of more than `2*m*r + m` elements of the infinite basis and then
move the successor target beyond all of them. -/
theorem recurrentLargePairStars_of_boundedFullTranslateDestroyers
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hfull : HasBoundedFullTranslateDestroyersByAnchor A 2 Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt (additiveSupportFamily A 3) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        r < (additiveSupportFamily A 2 (n - x)).card := by
  classical
  obtain ⟨N, hforce⟩ :=
    hbasis.large_externalAnchorSet_forces_pairSupportGrowth
  intro F hFA r L
  obtain ⟨m, hm⟩ := hfull F hFA
  let s := 2 * m * r + m + 1
  obtain ⟨B₀, hB₀A, hB₀card⟩ :=
    hbasis.infinite.exists_subset_card_eq s
  have hB₀nonempty : B₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [hB₀card]
    simp [s]
  obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
      hTA, hTF, hTnonempty, hTcard, hdestroy⟩ :=
    hm (max L (N + B₀.max' hB₀nonempty))
  let B := B₀ \ T
  have hBA : ∀ b ∈ B, b ∈ A := by
    intro b hbB
    exact hB₀A (Finset.mem_sdiff.mp hbB).1
  have hBT : Disjoint B T := by
    exact Finset.sdiff_disjoint
  have hlate : ∀ b ∈ B, N + b ≤ n := by
    intro b hbB
    have hbB₀ : b ∈ B₀ := (Finset.mem_sdiff.mp hbB).1
    have hbmax : b ≤ B₀.max' hB₀nonempty :=
      Finset.le_max' B₀ b hbB₀
    have hNa : N + B₀.max' hB₀nonempty ≤ a :=
      le_trans (le_max_right L (N + B₀.max' hB₀nonempty))
        haLower
    omega
  have hinterCard : (B₀ ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hBcardSum : B.card + (B₀ ∩ T).card = B₀.card := by
    exact Finset.card_sdiff_add_card_inter B₀ T
  have hBlarge : 2 * T.card * r < B.card := by
    rw [hB₀card] at hBcardSum
    dsimp only [s] at hBcardSum
    have hbase : 2 * m * r < B.card := by omega
    have hmul : 2 * T.card * r ≤ 2 * m * r :=
      Nat.mul_le_mul_right r (Nat.mul_le_mul_left 2 hTcard)
    exact lt_of_le_of_lt hmul hbase
  obtain ⟨x, hxT, hxn, hxlarge⟩ :=
    hforce hdestroy hBA hBT hlate hBlarge
  exact ⟨n, T, q, a, x,
    le_trans (le_max_left L (N + B₀.max' hB₀nonempty)) haLower,
    hqQ, haA, hnqa, hTA, hTF, hTnonempty, hdestroy,
    hxT, hxn, hxlarge⟩

/-- The bounded moving branch itself therefore produces recurrent large
pair stars. -/
theorem recurrentLargePairStars_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A 3) A Q) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ r L,
      ∃ n T q a x,
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        (∀ y ∈ T, y ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
        DestroysAt (additiveSupportFamily A 3) (T : Set ℕ) n ∧
        x ∈ T ∧ x ≤ n ∧
        r < (additiveSupportFamily A 2 (n - x)).card :=
  recurrentLargePairStars_of_boundedFullTranslateDestroyers hbasis <|
    boundedFullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ hmoving

/-! ## A pair star is a successor matching outside its center -/

/-- Adjoining one summand to every tuple support gives the corresponding
successor-order support. -/
theorem insert_mem_additiveSupportFamily_succ
    {A : Set ℕ} {k m a : ℕ} {E : Finset ℕ}
    (haA : a ∈ A)
    (hER : E ∈ additiveSupportFamily A k m) :
    insert a E ∈ additiveSupportFamily A (k + 1) (a + m) := by
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  let w : Fin (k + 1) → Fin (a + m + 1) :=
    Fin.cons ⟨a, by omega⟩ fun i =>
      ⟨(v i).1, by
        have hvi : (v i).1 ≤ m := Nat.le_of_lt_succ (v i).2
        omega⟩
  apply mem_additiveSupportFamily_iff.mpr
  refine ⟨w, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [w] using haA
    · simpa [w] using hvA j
  · rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    rw [hvsum]
  · ext y
    simp only [mem_tupleSupport_iff, Finset.mem_insert]
    constructor
    · rintro ⟨i, hi⟩
      refine Fin.cases
        (motive := fun i => (w i).1 = y →
          y = a ∨ ∃ j, (v j).1 = y) ?_ ?_ i hi
      · intro hi0
        exact Or.inl (by simpa [w] using hi0.symm)
      · intro j hij
        exact Or.inr ⟨j, by simpa [w] using hij⟩
    · rintro (rfl | ⟨j, hj⟩)
      · refine ⟨0, ?_⟩
        rfl
      · refine ⟨Fin.succ j, ?_⟩
        exact hj

/-- If the order-two support family at `n - x` is larger than the deletion
prefix with `x` erased, one pair support avoids that erased prefix.  Adjoining
`x` lifts it to an order-three support whose unique hit on the full prefix is
`x`.  This is the local engine for an old-core finite injury. -/
theorem exists_successorSupport_uniqueHit_of_manyPairSupports
    {A : Set ℕ} {D : Finset ℕ} {n x : ℕ}
    (hxA : x ∈ A) (hxD : x ∈ D) (hxn : x ≤ n)
    (hlarge : (D.erase x).card <
      (additiveSupportFamily A 2 (n - x)).card) :
    ∃ G ∈ additiveSupportFamily A 3 n, G ∩ D = {x} := by
  classical
  have hnotDestroy : ¬ DestroysAt
      (additiveSupportFamily A 2) ((D.erase x : Finset ℕ) : Set ℕ)
        (n - x) := by
    intro hdestroy
    have hcard := card_supports_le_card_of_matching_of_destroysAt
      (R := additiveSupportFamily A 2)
      (n := n - x) (T := D.erase x)
      (fun E hER =>
        additiveSupportFamily_supportsNonempty A (by omega)
          (n - x) E hER)
      (additiveSupportFamily_two_isMatching A (n - x)) hdestroy
    omega
  obtain ⟨E, hER, hEdisjoint⟩ := not_destroysAt_iff.mp hnotDestroy
  let G : Finset ℕ := insert x E
  have hGR : G ∈ additiveSupportFamily A 3 n := by
    have hlift := insert_mem_additiveSupportFamily_succ hxA hER
    have hsum : x + (n - x) = n := Nat.add_sub_of_le hxn
    simpa [G, hsum] using hlift
  refine ⟨G, hGR, ?_⟩
  ext y
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hyG, hyD⟩
    rcases Finset.mem_insert.mp hyG with rfl | hyE
    · rfl
    · by_contra hyx
      have hyErase : y ∈ D.erase x := Finset.mem_erase.mpr ⟨hyx, hyD⟩
      exact Set.disjoint_left.mp hEdisjoint hyE hyErase
  · rintro rfl
    exact ⟨Finset.mem_insert_self _ _, hxD⟩

/-- More than `r + 1` pair supports of `n - x` yield more than `r`
order-three supports of `n` whose portions outside the singleton core `{x}`
form a matching.  At most one pair support is lost because order-two
supports of a fixed target already form a matching. -/
theorem largePairSupportFamily_gives_successorMatchingOutsideSingleton
    {A : Set ℕ} {n x r : ℕ}
    (hxA : x ∈ A) (hxn : x ≤ n)
    (hlarge : r + 1 < (additiveSupportFamily A 2 (n - x)).card) :
    ∃ M : Finset (Finset ℕ),
      M ⊆ additiveSupportFamily A 3 n ∧ r < M.card ∧
      (∀ E ∈ M, (E \ {x}).Nonempty) ∧
      ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
        Disjoint (E \ {x}) (E' \ {x}) := by
  classical
  let H := additiveSupportFamily A 2 (n - x)
  let hitCenter := H.filter fun E => x ∈ E
  let avoidCenter := H.filter fun E => x ∉ E
  have hhitCard : hitCenter.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro E hE E' hE'
    have hEdata := Finset.mem_filter.mp hE
    have hE'data := Finset.mem_filter.mp hE'
    by_contra hEE'
    have hdisj := additiveSupportFamily_two_isMatching A (n - x)
      hEdata.1 hE'data.1 hEE'
    exact Finset.disjoint_left.mp hdisj hEdata.2 hE'data.2
  have hsplit : hitCenter.card + avoidCenter.card = H.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := H) (p := fun E => x ∈ E)
  have havoidLarge : r < avoidCenter.card := by
    change r + 1 < H.card at hlarge
    omega
  let liftSupport (E : Finset ℕ) : Finset ℕ := insert x E
  have hliftInjective : Set.InjOn liftSupport (avoidCenter : Set (Finset ℕ)) := by
    intro E hE E' hE' hEq
    have hxE : x ∉ E := (Finset.mem_filter.mp hE).2
    have hxE' : x ∉ E' := (Finset.mem_filter.mp hE').2
    have herase := congrArg (fun D : Finset ℕ => D.erase x) hEq
    simpa [liftSupport, hxE, hxE'] using herase
  let M := avoidCenter.image liftSupport
  have hMcard : M.card = avoidCenter.card := by
    exact Finset.card_image_iff.mpr hliftInjective
  have hMsub : M ⊆ additiveSupportFamily A 3 n := by
    intro D hDM
    obtain ⟨E, hEavoid, rfl⟩ := Finset.mem_image.mp hDM
    have hER : E ∈ additiveSupportFamily A 2 (n - x) :=
      (Finset.mem_filter.mp hEavoid).1
    have hlift := insert_mem_additiveSupportFamily_succ hxA hER
    have hsum : x + (n - x) = n := Nat.add_sub_of_le hxn
    simpa [liftSupport, hsum] using hlift
  refine ⟨M, hMsub, hMcard.symm ▸ havoidLarge, ?_, ?_⟩
  · intro D hDM
    obtain ⟨E, hEavoid, rfl⟩ := Finset.mem_image.mp hDM
    have hER : E ∈ additiveSupportFamily A 2 (n - x) :=
      (Finset.mem_filter.mp hEavoid).1
    have hxE : x ∉ E := (Finset.mem_filter.mp hEavoid).2
    have hEnonempty :=
      additiveSupportFamily_supportsNonempty A (by omega) (n - x) E hER
    have hdiff : insert x E \ {x} = E := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hyx⟩
        rcases hy with rfl | hy
        · exact (hyx rfl).elim
        · exact hy
      · intro hy
        refine ⟨Or.inr hy, ?_⟩
        intro hyx
        exact hxE (hyx ▸ hy)
    change (insert x E \ {x}).Nonempty
    rw [hdiff]
    exact hEnonempty
  · intro D hDM D' hD'M hDD'
    obtain ⟨E, hEavoid, rfl⟩ := Finset.mem_image.mp hDM
    obtain ⟨E', hE'avoid, rfl⟩ := Finset.mem_image.mp hD'M
    have hER : E ∈ additiveSupportFamily A 2 (n - x) :=
      (Finset.mem_filter.mp hEavoid).1
    have hE'R : E' ∈ additiveSupportFamily A 2 (n - x) :=
      (Finset.mem_filter.mp hE'avoid).1
    have hxE : x ∉ E := (Finset.mem_filter.mp hEavoid).2
    have hxE' : x ∉ E' := (Finset.mem_filter.mp hE'avoid).2
    have hEE' : E ≠ E' := by
      intro hEq
      exact hDD' (by simp [hEq])
    have hdisj := additiveSupportFamily_two_isMatching A (n - x)
      hER hE'R hEE'
    have hdiff : insert x E \ {x} = E := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hyx⟩
        rcases hy with rfl | hy
        · exact (hyx rfl).elim
        · exact hy
      · intro hy
        refine ⟨Or.inr hy, ?_⟩
        intro hyx
        exact hxE (hyx ▸ hy)
    have hdiff' : insert x E' \ {x} = E' := by
      ext y
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy, hyx⟩
        rcases hy with rfl | hy
        · exact (hyx rfl).elim
        · exact hy
      · intro hy
        refine ⟨Or.inr hy, ?_⟩
        intro hyx
        exact hxE' (hyx ▸ hy)
    change Disjoint (insert x E \ {x}) (insert x E' \ {x})
    rw [hdiff, hdiff']
    exact hdisj

/-- Exact recurrent output of the order-two bad branch: after every finite
protected prefix and at every requested level, there is a fresh singleton
core outside which one late successor target has a large matching. -/
theorem recurrentFreshSingletonCoreSuccessorMatchings_of_boundedMoving
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A 3) A Q) :
    ∀ D : Finset ℕ, (D : Set ℕ) ⊆ A → ∀ r L,
      ∃ n q a x, ∃ M : Finset (Finset ℕ),
        L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
        x ∈ A ∧ x ∉ D ∧
        M ⊆ additiveSupportFamily A 3 n ∧ r < M.card ∧
        (∀ E ∈ M, (E \ {x}).Nonempty) ∧
        ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
          Disjoint (E \ {x}) (E' \ {x}) := by
  intro D hDA r L
  obtain ⟨n, T, q, a, x, haLower, hqQ, haA, hnqa,
      hTA, hTD, _hTnonempty, _hdestroy, hxT, hxn, hxlarge⟩ :=
    recurrentLargePairStars_of_boundedMovingOnFiniteTranslates
      hbasis hQ hmoving D hDA (r + 1) L
  obtain ⟨M, hMsub, hMcard, hMnonempty, hMmatching⟩ :=
    largePairSupportFamily_gives_successorMatchingOutsideSingleton
      (hTA x hxT) hxn hxlarge
  refine ⟨n, q, a, x, M, haLower, hqQ, haA, hnqa,
    hTA x hxT, ?_, hMsub, hMcard, hMnonempty, hMmatching⟩
  intro hxD
  exact Finset.disjoint_left.mp hTD hxT hxD

/-- Abstract quantifier package for the recurrent singleton-core conclusion.
Unlike adaptive growth, the center may depend on the one good target `n`;
there is no eventual `∀ n` assertion. -/
def HasRecurrentFreshSingletonCoreMatchingAlong
    (R : SupportFamily) (A S : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, (D : Set ℕ) ⊆ A → ∀ r N,
    ∃ n, N ≤ n ∧ n ∈ S ∧
      ∃ x ∈ A, x ∉ D ∧
        ∃ M : Finset (Finset ℕ),
          M ⊆ R n ∧ r < M.card ∧
          (∀ E ∈ M, (E \ {x}).Nonempty) ∧
          ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
            Disjoint (E \ {x}) (E' \ {x})

theorem recurrentFreshSingletonCoreMatchingAlong_of_boundedMoving
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A 3) A Q) :
    HasRecurrentFreshSingletonCoreMatchingAlong
      (additiveSupportFamily A 3) A (finiteTargetTranslates A Q) := by
  intro D hDA r N
  obtain ⟨n, q, a, x, M, haLower, hqQ, haA, hnqa,
      hxA, hxD, hMsub, hMcard, hMnonempty, hMmatching⟩ :=
    recurrentFreshSingletonCoreSuccessorMatchings_of_boundedMoving
      hbasis hQ hmoving D hDA r N
  refine ⟨n, by omega, ⟨q, hqQ, a, haA, hnqa⟩,
    x, hxA, hxD, M, hMsub, hMcard, hMnonempty, hMmatching⟩

/-- Sharp order-two relative dichotomy after retaining the cardinal
information in the bad branch.  Either one fixed finite core has genuine
eventual outside matching growth on `Q + A`, or arbitrarily large matchings
recur outside fresh singleton cores. -/
theorem finiteCoreTranslateGrowth_or_recurrentFreshSingletonCoreMatching
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hQ : Q.Nonempty) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A 3) F (finiteTargetTranslates A Q)) ∨
      HasRecurrentFreshSingletonCoreMatchingAlong
        (additiveSupportFamily A 3) A (finiteTargetTranslates A Q) := by
  obtain hgrowth | hmoving :=
    finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
      (A := A) (Q := Q)
      (R := additiveSupportFamily A 3)
      (additiveSupportFamily_supportsIn A 3)
      (additiveSupportFamily_cardAtMost A 3)
  · exact Or.inl hgrowth
  · exact Or.inr <|
      recurrentFreshSingletonCoreMatchingAlong_of_boundedMoving
        hbasis hQ hmoving

/-- If `Q + A` is cofinite, the first side of the sharp dichotomy already
gives the desired infinite deletion.  Hence only the recurrent moving-center
side remains in that setting. -/
theorem infiniteDeletionThreeBasis_or_recurrentFreshSingletonCoreMatching
    {A : Set ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hQ : Q.Nonempty)
    (hcofinite : ∃ M, ∀ n, M ≤ n →
      n ∈ finiteTargetTranslates A Q) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3) ∨
      HasRecurrentFreshSingletonCoreMatchingAlong
        (additiveSupportFamily A 3) A (finiteTargetTranslates A Q) := by
  obtain ⟨F, _hFA, hgrowth⟩ | hrecur :=
    finiteCoreTranslateGrowth_or_recurrentFreshSingletonCoreMatching
      hbasis hQ
  · exact Or.inl <|
      exists_infiniteDeletion_succBasis_of_finiteTranslateGrowth
        hbasis hgrowth hcofinite
  · exact Or.inr hrecur

/- The following alternating family is a quantifier countercheck.  Even
targets carry all singleton supports below the target; odd targets carry
only `{0}`. -/
private noncomputable def alternatingSingletonSupportFamily : SupportFamily :=
  fun n => if Even n then
    (Finset.range (n + 1)).image fun x => ({x} : Finset ℕ)
  else {{0}}

/-- Recurrent fresh singleton cores do not, as a matter of logic, imply
adaptive eventual growth.  Strong deletion or additional additive structure
must perform a genuine quantifier upgrade; it cannot be supplied by the
recurrent star theorem alone. -/
theorem recurrentFreshSingletonCoreMatching_need_not_be_adaptive :
    HasRecurrentFreshSingletonCoreMatchingAlong
        alternatingSingletonSupportFamily Set.univ Set.univ ∧
      ¬ AdaptiveCoreMatchingTendsToInfinityOutsideAlong
        alternatingSingletonSupportFamily Set.univ := by
  classical
  constructor
  · intro D _hD r N
    let u := max N (r + 1)
    let n := 2 * u
    let x := max n (D.sum id) + 1
    let M : Finset (Finset ℕ) :=
      (Finset.range (r + 1)).image fun y => ({y} : Finset ℕ)
    have hEven : Even n := by
      refine ⟨u, ?_⟩
      dsimp only [n]
      omega
    have hMcard : M.card = r + 1 := by
      dsimp only [M]
      rw [Finset.card_image_of_injective]
      · simp
      · intro y z hyz
        simpa only [Finset.singleton_inj] using hyz
    have hxD : x ∉ D := by
      intro hxD
      have hxle : x ≤ D.sum id :=
        Finset.single_le_sum (s := D) (f := id)
          (fun _ _ => Nat.zero_le _) hxD
      omega
    refine ⟨n, by dsimp [n, u]; omega, Set.mem_univ n,
      x, Set.mem_univ x, hxD, M, ?_, by omega, ?_, ?_⟩
    · intro E hEM
      obtain ⟨y, hyrange, rfl⟩ := Finset.mem_image.mp hEM
      rw [alternatingSingletonSupportFamily, if_pos hEven]
      apply Finset.mem_image.mpr
      refine ⟨y, Finset.mem_range.mpr ?_, rfl⟩
      have hy : y < r + 1 := Finset.mem_range.mp hyrange
      dsimp only [n, u]
      omega
    · intro E hEM
      obtain ⟨y, hyrange, rfl⟩ := Finset.mem_image.mp hEM
      have hy : y < r + 1 := Finset.mem_range.mp hyrange
      refine ⟨y, ?_⟩
      simp only [Finset.mem_sdiff, Finset.mem_singleton, true_and]
      dsimp only [x, n, u]
      omega
    · intro E hEM E' hE'M hEE'
      obtain ⟨y, hyrange, rfl⟩ := Finset.mem_image.mp hEM
      obtain ⟨z, hzrange, rfl⟩ := Finset.mem_image.mp hE'M
      have hy : y < r + 1 := Finset.mem_range.mp hyrange
      have hz : z < r + 1 := Finset.mem_range.mp hzrange
      have hyz : y ≠ z := by
        intro hyz
        exact hEE' (by simp [hyz])
      have hyx : y ≠ x := by
        dsimp only [x, n, u]
        omega
      have hzx : z ≠ x := by
        dsimp only [x, n, u]
        omega
      have hdiffy : ({y} : Finset ℕ) \ {x} = {y} :=
        Finset.sdiff_eq_self_of_disjoint
          (Finset.disjoint_singleton.mpr hyx)
      have hdiffz : ({z} : Finset ℕ) \ {x} = {z} :=
        Finset.sdiff_eq_self_of_disjoint
          (Finset.disjoint_singleton.mpr hzx)
      rw [hdiffy, hdiffz]
      exact Finset.disjoint_singleton.mpr hyz
  · intro hadaptive
    obtain ⟨F, _hFD, threshold, hmatching⟩ :=
      hadaptive {0} 1
    let n := 2 * threshold + 1
    have hOdd : ¬ Even n := by
      rintro ⟨t, ht⟩
      dsimp only [n] at ht
      omega
    obtain ⟨M, hMsub, hMcard, _hMnonempty, _hMmatching⟩ :=
      hmatching n (by dsimp [n]; omega) (Set.mem_univ n)
    have hMle : M.card ≤ 1 := by
      calc
        M.card ≤ (alternatingSingletonSupportFamily n).card :=
          Finset.card_le_card hMsub
        _ = 1 := by
          simp [alternatingSingletonSupportFamily, hOdd]
    omega

/-! ## Sharpness of purely finite internal-anchor arguments -/

/-- A cofinite order-two basis containing `r` designated anchors.  Below the
cofinite tail its only elements are `1` and the multiples
`4, 8, ..., 4r`. -/
def finiteInternalAnchorBasis (r : ℕ) : Set ℕ :=
  {x | x = 1 ∨ (∃ i < r, x = 4 * (i + 1)) ∨ 4 * (r + 2) ≤ x}

def finiteInternalAnchor (i : ℕ) : ℕ := 4 * (i + 1)

theorem finiteInternalAnchorBasis_isExactOrderTwoBasis (r : ℕ) :
    IsExactTupleAsymptoticBasis (finiteInternalAnchorBasis r) 2 := by
  let H := 4 * (r + 2)
  refine ⟨2 * H, ?_⟩
  intro n hn
  let v : Fin 2 → ℕ := ![H, n - H]
  refine ⟨v, ?_, ?_⟩
  · intro i
    fin_cases i
    · change H ∈ finiteInternalAnchorBasis r
      exact Or.inr (Or.inr (by simp [H]))
    · change n - H ∈ finiteInternalAnchorBasis r
      exact Or.inr (Or.inr (by dsimp [H]; omega))
  · simp [v]
    omega

theorem finiteInternalAnchor_mem (r i : ℕ) (hi : i < r) :
    finiteInternalAnchor i ∈ finiteInternalAnchorBasis r := by
  exact Or.inr (Or.inl ⟨i, hi, rfl⟩)

/-- At the exceptional target `finiteInternalAnchor i + 2`, every
three-term representation uses the designated anchor.  The elementary
reason is reduction modulo four: exactly two of the three summands must be
the element `1`. -/
theorem singleton_finiteInternalAnchor_destroys_orderThree
    {r i : ℕ} (hi : i < r) :
    DestroysAt
      (additiveSupportFamily (finiteInternalAnchorBasis r) 3)
      ({finiteInternalAnchor i} : Finset ℕ)
      (finiteInternalAnchor i + 2) := by
  rw [destroysAt_additiveSupportFamily_iff]
  rintro ⟨v, hv, hvsum⟩
  have hsum : v 0 + (v 1 + v 2) = finiteInternalAnchor i + 2 := by
    simpa [Fin.sum_univ_succ] using hvsum
  have htargetTail : finiteInternalAnchor i + 2 < 4 * (r + 2) := by
    simp [finiteInternalAnchor]
    omega
  have hvle : ∀ j : Fin 3, v j ≤ finiteInternalAnchor i + 2 := by
    intro j
    rw [← hvsum]
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hvform : ∀ j : Fin 3,
      v j = 1 ∨ ∃ t < r, v j = 4 * (t + 1) := by
    intro j
    rcases (hv j).1 with hone | hanchor | htail
    · exact Or.inl hone
    · exact Or.inr hanchor
    · have := hvle j
      omega
  have hvne : ∀ j : Fin 3, v j ≠ finiteInternalAnchor i := by
    intro j hEq
    exact (hv j).2 (by simp [hEq])
  have hne0 := hvne 0
  have hne1 := hvne 1
  have hne2 := hvne 2
  rcases hvform 0 with h0 | ⟨t0, ht0, h0⟩ <;>
    rcases hvform 1 with h1 | ⟨t1, ht1, h1⟩ <;>
      rcases hvform 2 with h2 | ⟨t2, ht2, h2⟩ <;>
        simp only [h0, h1, h2, finiteInternalAnchor] at hsum hne0 hne1 hne2 <;>
        omega

/-- All designated cells have the same surviving predecessor support
`{1}` at target `2`, disjoint from their internal anchors. -/
theorem finiteInternalAnchor_has_common_surviving_pairSupport
    (r i : ℕ) :
    ∃ E ∈ additiveSupportFamily (finiteInternalAnchorBasis r) 2 2,
      Disjoint (E : Set ℕ) ({finiteInternalAnchor i} : Set ℕ) := by
  let E := pairSupport 2 1
  have hEA : E ∈ additiveSupportFamily (finiteInternalAnchorBasis r) 2 2 := by
    apply pairSupport_mem_additiveSupportFamily (by omega)
    · exact Or.inl rfl
    · simpa using (show (1 : ℕ) ∈ finiteInternalAnchorBasis r from Or.inl rfl)
  refine ⟨E, hEA, ?_⟩
  simp [E, pairSupport, finiteInternalAnchor]
  omega

theorem finiteInternalAnchor_singletons_pairwiseDisjoint
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint ({finiteInternalAnchor i} : Finset ℕ)
      ({finiteInternalAnchor j} : Finset ℕ) := by
  simp [finiteInternalAnchor]
  omega

def finiteInternalAnchorCells (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.range r).image fun i => {finiteInternalAnchor i}

theorem finiteInternalAnchorCells_card (r : ℕ) :
    (finiteInternalAnchorCells r).card = r := by
  rw [finiteInternalAnchorCells,
    Finset.card_image_of_injective (Finset.range r)]
  · simp
  · intro i j hij
    simp only [Finset.singleton_inj] at hij
    simp [finiteInternalAnchor] at hij
    omega

theorem finiteInternalAnchorCells_isMatching (r : ℕ) :
    IsMatching (finiteInternalAnchorCells r) := by
  intro C hC D hD hCD
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hD
  apply finiteInternalAnchor_singletons_pairwiseDisjoint
  intro hij
  subst j
  exact hCD rfl

/-- There are arbitrarily large finite internal-anchor rows even inside a
genuine order-two asymptotic basis.  Thus neither the common predecessor,
the matching property at that predecessor, nor finite row size alone can
contradict the internal-anchor branch. -/
theorem exists_arbitrarilyLarge_internalAnchorRow_in_orderTwoBasis (r : ℕ) :
    ∃ A : Set ℕ, ∃ 𝓇 : Finset (Finset ℕ),
      IsExactTupleAsymptoticBasis A 2 ∧
      𝓇.card = r ∧ IsMatching 𝓇 ∧
      ∀ C ∈ 𝓇, ∃ a,
        C = {a} ∧ 2 < a ∧ a ∈ A ∧
        DestroysAt (additiveSupportFamily A 3) (C : Set ℕ) (2 + a) ∧
        a ∈ C ∧
        ∃ E ∈ additiveSupportFamily A 2 2,
          Disjoint (E : Set ℕ) (C : Set ℕ) := by
  refine ⟨finiteInternalAnchorBasis r, finiteInternalAnchorCells r,
    finiteInternalAnchorBasis_isExactOrderTwoBasis r,
    finiteInternalAnchorCells_card r,
    finiteInternalAnchorCells_isMatching r, ?_⟩
  intro C hC
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
  have hir : i < r := Finset.mem_range.mp hi
  refine ⟨finiteInternalAnchor i, rfl, ?_,
    finiteInternalAnchor_mem r i hir, ?_, by simp, ?_⟩
  · simp [finiteInternalAnchor]
    omega
  · simpa [Nat.add_comm] using
      singleton_finiteInternalAnchor_destroys_orderThree hir
  · simpa using finiteInternalAnchor_has_common_surviving_pairSupport r i

end Erdos881
