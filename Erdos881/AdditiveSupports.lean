import Erdos881.MovingTransversals

/-!
# Finite support hypergraphs for exact additive representations

This file connects the abstract compactness and moving-transversal development
to exact additive representations by `h` natural-number summands.
-/

open scoped BigOperators

namespace Erdos881

/-- The support of an ordered tuple whose entries are bounded by `n`. -/
def tupleSupport {h n : ℕ} (v : Fin h → Fin (n + 1)) : Finset ℕ :=
  Finset.univ.image fun i => (v i).1

/-- The finite hypergraph of distinct supports of exact `h`-term
representations of `n` from `A`. -/
noncomputable def additiveSupportFamily (A : Set ℕ) (h : ℕ) :
    SupportFamily := by
  classical
  intro n
  exact
    ((Finset.univ : Finset (Fin h → Fin (n + 1))).filter fun v =>
      (∀ i, (v i).1 ∈ A) ∧ ∑ i, (v i).1 = n).image tupleSupport

theorem mem_additiveSupportFamily_iff
    {A : Set ℕ} {h n : ℕ} {E : Finset ℕ} :
    E ∈ additiveSupportFamily A h n ↔
      ∃ v : Fin h → Fin (n + 1),
        (∀ i, (v i).1 ∈ A) ∧
        (∑ i, (v i).1 = n) ∧
        tupleSupport v = E := by
  classical
  simp only [additiveSupportFamily, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  aesop

theorem mem_tupleSupport_iff
    {h n : ℕ} {v : Fin h → Fin (n + 1)} {x : ℕ} :
    x ∈ tupleSupport v ↔ ∃ i, (v i).1 = x := by
  classical
  simp [tupleSupport]

/-- The two-element support arising from `n = a + (n - a)`. -/
def pairSupport (n a : ℕ) : Finset ℕ :=
  {a, n - a}

/-- Every valid complementary pair gives an order-two additive support. -/
theorem pairSupport_mem_additiveSupportFamily
    {A : Set ℕ} {n a : ℕ}
    (han : a ≤ n) (haA : a ∈ A) (hnaA : n - a ∈ A) :
    pairSupport n a ∈ additiveSupportFamily A 2 n := by
  let v : Fin 2 → Fin (n + 1) :=
    ![⟨a, Nat.lt_succ_of_le han⟩,
      ⟨n - a, Nat.lt_succ_of_le (Nat.sub_le n a)⟩]
  apply mem_additiveSupportFamily_iff.mpr
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v, haA, hnaA]
  · simp [v, Nat.add_sub_of_le han]
  · ext x
    simp [tupleSupport, pairSupport, v]
    aesop

/-- For an order-two representation, either vertex of its support determines
the entire complementary-pair support. -/
theorem additiveSupportFamily_two_eq_pairSupport_of_mem
    {A : Set ℕ} {n : ℕ} {E : Finset ℕ} {x : ℕ}
    (hER : E ∈ additiveSupportFamily A 2 n) (hxE : x ∈ E) :
    E = pairSupport n x := by
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxE
  have hsum :
      (v 0).1 + (v 1).1 = n := by
    simpa using hvsum
  fin_cases i
  · have hcomp : n - (v 0).1 = (v 1).1 := by omega
    rw [← hi]
    ext y
    simp [tupleSupport, pairSupport, hcomp]
    aesop
  · have hcomp : n - (v 1).1 = (v 0).1 := by omega
    rw [← hi]
    ext y
    simp [tupleSupport, pairSupport, hcomp]
    aesop

/-- Distinct two-term representation supports of one target are pairwise
disjoint. -/
theorem additiveSupportFamily_two_isMatching
    (A : Set ℕ) (n : ℕ) :
    IsMatching (additiveSupportFamily A 2 n) := by
  intro E hER E' hE'R hEE'
  change Disjoint E E'
  rw [Finset.disjoint_left]
  intro x hxE hxE'
  apply hEE'
  exact
    (additiveSupportFamily_two_eq_pairSupport_of_mem hER hxE).trans
      (additiveSupportFamily_two_eq_pairSupport_of_mem hE'R hxE').symm

theorem additiveSupportFamily_supportsIn
    (A : Set ℕ) (h : ℕ) :
    SupportsIn (additiveSupportFamily A h) A := by
  intro n E hER x hxE
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxE
  exact hi ▸ hvA i

theorem additiveSupportFamily_supportsBounded
    (A : Set ℕ) (h : ℕ) :
    SupportsBounded (additiveSupportFamily A h) := by
  intro n E hER x hxE
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, rfl⟩ := mem_tupleSupport_iff.mp hxE
  exact Nat.le_of_lt_succ (v i).2

/-- A support for a sufficiently large additive target cannot be contained in
a fixed finite core. -/
theorem additiveSupportFamily_eventuallyEscapesFiniteCores
  (A : Set ℕ) (h : ℕ) :
    SupportsEventuallyEscapeFiniteCores
      (additiveSupportFamily A h) := by
  intro F
  refine ⟨h * F.sum id + 1, ?_⟩
  intro n hn E hER
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  rw [Finset.sdiff_nonempty]
  intro hsub
  have hvle : ∀ i, (v i).1 ≤ F.sum id := by
    intro i
    exact Finset.single_le_sum (s := F) (f := id)
      (fun _ _ => Nat.zero_le _)
      (hsub (mem_tupleSupport_iff.mpr ⟨i, rfl⟩))
  have hsumle :
      ∑ i, (v i).1 ≤ ∑ _i : Fin h, F.sum id := by
    apply Finset.sum_le_sum
    intro i hi
    exact hvle i
  have hnle : n ≤ h * F.sum id := by
    rw [hvsum] at hsumle
    simpa using hsumle
  exact (not_lt_of_ge hnle)
    (lt_of_lt_of_le (Nat.lt_succ_self (h * F.sum id)) hn)

theorem additiveSupportFamily_supportsNonempty
    (A : Set ℕ) {h : ℕ} (hh : 0 < h) :
    SupportsNonempty (additiveSupportFamily A h) := by
  intro n E hER
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  let i : Fin h := ⟨0, hh⟩
  exact ⟨(v i).1, mem_tupleSupport_iff.mpr ⟨i, rfl⟩⟩

theorem additiveSupportFamily_cardAtMost
    (A : Set ℕ) (h : ℕ) :
    SupportsCardAtMost (additiveSupportFamily A h) h := by
  intro n E hER
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  simpa [tupleSupport] using
    (Finset.card_image_le :
      (Finset.univ.image fun i : Fin h => (v i).1).card ≤
        (Finset.univ : Finset (Fin h)).card)

/- At a represented order-`h` target, at most `h` pairwise-disjoint finite
deletion sets can all destroy that same target.  Indeed, each deletion set
must use a different point of any fixed representation support. -/
theorem card_pairwiseDisjoint_additiveDestroyers_le
    {A : Set ℕ} {h n : ℕ} {𝒯 : Finset (Finset ℕ)}
    (hnonempty : (additiveSupportFamily A h n).Nonempty)
    (hpair : IsMatching 𝒯)
    (hdestroy : ∀ T ∈ 𝒯,
      DestroysAt (additiveSupportFamily A h) (T : Set ℕ) n) :
    𝒯.card ≤ h := by
  obtain ⟨E, hER⟩ := hnonempty
  have htrans :
      ∀ T ∈ 𝒯, IsTransversal (additiveSupportFamily A h n) T := by
    intro T hT E' hE'R
    obtain ⟨x, hxE', hxT⟩ :=
      Set.not_disjoint_iff.mp (hdestroy T hT E' hE'R)
    exact ⟨x, Finset.mem_inter.mpr
      ⟨hxE', Finset.mem_coe.mp hxT⟩⟩
  exact le_trans
    (card_le_edge_card_of_pairwiseDisjoint_transversals
      hER hpair htrans)
    (additiveSupportFamily_cardAtMost A h n E hER)

/- The finite union of translates `Q + A`, retained as a target set for the
relative matching dichotomy. -/
def finiteTargetTranslates (A : Set ℕ) (Q : Finset ℕ) : Set ℕ :=
  {n | ∃ q ∈ Q, ∃ a ∈ A, n = q + a}

theorem mem_finiteTargetTranslates_iff
    {A : Set ℕ} {Q : Finset ℕ} {n : ℕ} :
    n ∈ finiteTargetTranslates A Q ↔
      ∃ q ∈ Q, ∃ a ∈ A, n = q + a :=
  Iff.rfl

/- Eventual syndeticity in a form convenient on `ℕ`: every sufficiently
large `n` has an element of `A` in the interval `[n - L, n]`. -/
def IsEventuallySyndetic (A : Set ℕ) : Prop :=
  ∃ L N, ∀ n, N ≤ n → ∃ a ∈ A, a ≤ n ∧ n ≤ a + L

/-- Removing finitely many points does not affect eventual syndeticity. -/
theorem IsEventuallySyndetic.diff_finset
    {A : Set ℕ} (hA : IsEventuallySyndetic A) (D : Finset ℕ) :
    IsEventuallySyndetic (A \ (D : Set ℕ)) := by
  obtain ⟨L, N, hsyndetic⟩ := hA
  refine ⟨L, max N (D.sup id + L + 1), ?_⟩
  intro n hn
  obtain ⟨a, haA, han, hna⟩ :=
    hsyndetic n (le_trans (le_max_left _ _) hn)
  have haD : a ∉ D := by
    intro haD
    have hale : a ≤ D.sup id := by
      simpa using (Finset.le_sup (f := fun x : ℕ => x) haD)
    have hlower : D.sup id + L + 1 ≤ n :=
      le_trans (le_max_right _ _) hn
    omega
  exact ⟨a, ⟨haA, by simpa using haD⟩, han, hna⟩

/- Iterating the bounded-gap condition downward produces any prescribed
finite number of distinct elements below a sufficiently large endpoint, all
within one uniformly bounded interval. -/
private theorem eventuallySyndetic_many_below
    {A : Set ℕ} {L N : ℕ}
    (hsyndetic : ∀ n, N ≤ n →
      ∃ a ∈ A, a ≤ n ∧ n ≤ a + L) :
    ∀ r a, N + r * (L + 1) ≤ a →
      ∃ B : Finset ℕ, B.card = r ∧
        ∀ b ∈ B, b ∈ A ∧ b < a ∧
          a ≤ b + r * (L + 1) := by
  intro r
  induction r with
  | zero =>
      intro a _ha
      exact ⟨∅, by simp, by simp⟩
  | succ r ih =>
      intro a ha
      have haPos : 0 < a := by
        simp only [Nat.succ_mul] at ha
        omega
      have hNa : N ≤ a - 1 := by
        simp only [Nat.succ_mul] at ha
        omega
      obtain ⟨b, hbA, hba, hab⟩ := hsyndetic (a - 1) hNa
      have hba' : b < a := by omega
      have hNb : N + r * (L + 1) ≤ b := by
        simp only [Nat.succ_mul] at ha
        omega
      obtain ⟨B, hBcard, hB⟩ := ih b hNb
      have hbB : b ∉ B := by
        intro hbmem
        exact (not_lt_of_ge le_rfl) (hB b hbmem).2.1
      refine ⟨insert b B, ?_, ?_⟩
      · simp [hbB, hBcard]
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxB
        · refine ⟨hbA, hba', ?_⟩
          simp only [Nat.succ_mul]
          omega
        · obtain ⟨hxA, hxb, hbx⟩ := hB x hxB
          refine ⟨hxA, lt_trans hxb hba', ?_⟩
          simp only [Nat.succ_mul]
          omega

theorem IsEventuallySyndetic.exists_many_below
    {A : Set ℕ} (hA : IsEventuallySyndetic A) :
    ∀ r, ∃ D N, ∀ a, N ≤ a →
      ∃ B : Finset ℕ, B.card = r ∧
        ∀ b ∈ B, b ∈ A ∧ b < a ∧ a ≤ b + D := by
  obtain ⟨L, N₀, hsyndetic⟩ := hA
  intro r
  refine ⟨r * (L + 1), N₀ + r * (L + 1), ?_⟩
  intro a ha
  exact eventuallySyndetic_many_below hsyndetic r a ha

/- In particular, a bounded finite set cannot contain all nearby elements of
an eventually syndetic set. -/
theorem IsEventuallySyndetic.exists_nearby_not_mem_finset
    {A : Set ℕ} (hA : IsEventuallySyndetic A) :
    ∀ m, ∃ D N, ∀ a (T : Finset ℕ), N ≤ a → T.card ≤ m →
      ∃ b ∈ A, b ∉ T ∧ b < a ∧ a ≤ b + D := by
  intro m
  obtain ⟨D, N, hmany⟩ := hA.exists_many_below (m + 1)
  refine ⟨D, N, ?_⟩
  intro a T ha hTcard
  obtain ⟨B, hBcard, hB⟩ := hmany a ha
  have hnotSubset : ¬ B ⊆ T := by
    intro hBT
    have hcardle := Finset.card_le_card hBT
    omega
  obtain ⟨b, hbB, hbT⟩ := Finset.not_subset.mp hnotSubset
  exact ⟨b, (hB b hbB).1, hbT, (hB b hbB).2.1,
    (hB b hbB).2.2⟩

/- A finite union of translates `Q + A` covers a tail exactly when `A` is
eventually syndetic.  Thus a finite/cofinite translate cover is a genuine
bounded-gap hypothesis, not a consequence of merely being an additive basis. -/
theorem exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic
    {A : Set ℕ} :
    (∃ Q : Finset ℕ, ∃ N, ∀ n, N ≤ n →
      n ∈ finiteTargetTranslates A Q) ↔
      IsEventuallySyndetic A := by
  classical
  constructor
  · rintro ⟨Q, N, hcover⟩
    obtain ⟨q₀, hq₀Q, _a₀, _ha₀A, _hN⟩ := hcover N le_rfl
    have hQ : Q.Nonempty := ⟨q₀, hq₀Q⟩
    refine ⟨Q.max' hQ, N, ?_⟩
    intro n hn
    obtain ⟨q, hqQ, a, haA, hnqa⟩ := hcover n hn
    have hqmax : q ≤ Q.max' hQ := Finset.le_max' Q q hqQ
    exact ⟨a, haA, by omega, by omega⟩
  · rintro ⟨L, N, hsyndetic⟩
    refine ⟨Finset.range (L + 1), N, ?_⟩
    intro n hn
    obtain ⟨a, haA, han, hnaL⟩ := hsyndetic n hn
    let q := n - a
    have hqL : q ≤ L := by omega
    exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le hqL),
      a, haA, (Nat.sub_add_cancel han).symm⟩

/- A finite/cofinite translate cover may be shifted arbitrarily far to the
right.  This lets every translate label lie beyond any eventual
representation threshold needed by a later support count. -/
theorem IsEventuallySyndetic.exists_late_finiteTargetTranslates_cofinite
    {A : Set ℕ} (hA : IsEventuallySyndetic A) (L₀ : ℕ) :
    ∃ Q : Finset ℕ, Q.Nonempty ∧
      (∀ q ∈ Q, L₀ ≤ q) ∧
      ∃ N, ∀ n, N ≤ n → n ∈ finiteTargetTranslates A Q := by
  classical
  obtain ⟨L, N, hsyndetic⟩ := hA
  let Q : Finset ℕ := (Finset.range (L + 1)).image fun d => L₀ + d
  have hQ : Q.Nonempty := by
    refine ⟨L₀, Finset.mem_image.mpr ⟨0, by simp, by simp⟩⟩
  refine ⟨Q, hQ, ?_, N + L₀, ?_⟩
  · intro q hqQ
    obtain ⟨d, _hd, rfl⟩ := Finset.mem_image.mp hqQ
    exact Nat.le_add_right L₀ d
  · intro n hn
    have hNsub : N ≤ n - L₀ := by omega
    obtain ⟨a, haA, han, hna⟩ := hsyndetic (n - L₀) hNsub
    let d := n - L₀ - a
    have hdL : d < L + 1 := by
      dsimp [d]
      omega
    refine ⟨L₀ + d, Finset.mem_image.mpr
      ⟨d, Finset.mem_range.mpr hdL, rfl⟩, a, haA, ?_⟩
    dsimp [d]
    omega

/- The recurrent moving branch over `Q + A`, with the translate witnesses
unpacked explicitly. -/
def HasBoundedMovingOutsideTransversalsOnFiniteTranslates
    (R : SupportFamily) (A : Set ℕ) (Q : Finset ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T q a,
      N ≤ n ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧ T.card ≤ m ∧
      IsTransversal (outsideSupportHypergraph R F n) T

/- Equivalent recurrence formulation measured by the translate anchor rather
than by the target `n = q + a`. -/
def HasBoundedMovingOutsideTransversalsOnFiniteTranslatesByAnchor
    (R : SupportFamily) (A : Set ℕ) (Q : Finset ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ L, ∃ n T q a,
      L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧ T.card ≤ m ∧
      IsTransversal (outsideSupportHypergraph R F n) T

/- For nonempty finite `Q`, recurrence in the targets `Q + A` is exactly
recurrence with anchors tending to infinity. -/
theorem boundedMovingOnFiniteTranslates_iff_byAnchor
    {A : Set ℕ} {Q : Finset ℕ} {R : SupportFamily}
    (hQ : Q.Nonempty) :
    HasBoundedMovingOutsideTransversalsOnFiniteTranslates R A Q ↔
      HasBoundedMovingOutsideTransversalsOnFiniteTranslatesByAnchor
        R A Q := by
  constructor
  · intro hmoving F hFA
    obtain ⟨m, hm⟩ := hmoving F hFA
    refine ⟨m, ?_⟩
    intro L
    obtain ⟨n, T, q, a, hn, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩ := hm (L + Q.max' hQ)
    have hqmax : q ≤ Q.max' hQ := Finset.le_max' Q q hqQ
    have hLa : L ≤ a := by omega
    exact ⟨n, T, q, a, hLa, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩
  · intro hmoving F hFA
    obtain ⟨m, hm⟩ := hmoving F hFA
    refine ⟨m, ?_⟩
    intro N
    obtain ⟨n, T, q, a, ha, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩ := hm N
    have hn : N ≤ n := by omega
    exact ⟨n, T, q, a, hn, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩

/- The row-building form of recurrence along `Q + A`.  It discards the
uniform cardinality bound after retaining the features needed by the
diagonal construction: an arbitrarily late translate anchor, a new nonempty
finite core outside every protected finite set, and full successor
destruction by that core alone. -/
def HasFullTranslateDestroyersByAnchor
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
    ∃ n T q a,
      L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧ T.Nonempty ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/- A finite row of full successor destroyers aligned with targets in `Q`.
The anchors are required to lie beyond `L`, but may lie inside their
destroyers; retaining that distinction is essential for the later audit. -/
def IsFullAlignedTranslateDestroyerFamily
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ) (L : ℕ)
    (𝒯 : Finset (Finset ℕ)) : Prop :=
  IsMatching 𝒯 ∧
    (∀ T ∈ 𝒯, T.Nonempty) ∧
    (∀ T ∈ 𝒯, ∀ x ∈ T, x ∈ A) ∧
    ∀ T ∈ 𝒯, ∃ q : {m // m ∈ Q}, ∃ n a,
      L ≤ a ∧ a ∈ A ∧ n = q.1 + a ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/- Full translate recurrence constructs a row of any prescribed finite size,
disjoint from an arbitrary protected finite set.  This is the finite engine
used at every stage of the diagonal construction. -/
theorem exists_fullAlignedTranslateDestroyerFamily_card_disjoint
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hrecur : HasFullTranslateDestroyersByAnchor A k Q)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (L r : ℕ) :
    ∃ 𝒯 : Finset (Finset ℕ),
      IsFullAlignedTranslateDestroyerFamily A k Q L 𝒯 ∧
      𝒯.card = r ∧
      ∀ T ∈ 𝒯, Disjoint T F := by
  classical
  induction r with
  | zero =>
      refine ⟨∅, ?_, by simp, by simp⟩
      simp [IsFullAlignedTranslateDestroyerFamily, IsMatching]
  | succ r ih =>
      obtain ⟨𝒯, hfamily, hcard, hdisjointF⟩ := ih
      let U : Finset ℕ := 𝒯.biUnion id
      let F' : Finset ℕ := F ∪ U
      have hF'A : (F' : Set ℕ) ⊆ A := by
        intro x hxF'
        rcases Finset.mem_union.mp hxF' with hxF | hxU
        · exact hFA hxF
        · obtain ⟨T, hT𝒯, hxT⟩ := Finset.mem_biUnion.mp hxU
          exact hfamily.2.2.1 T hT𝒯 x hxT
      obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
          hTA, hTF', hTnonempty, hdestroy⟩ := hrecur F' hF'A L
      have hTnot : T ∉ 𝒯 := by
        intro hT𝒯
        obtain ⟨x, hxT⟩ := hTnonempty
        apply Finset.disjoint_left.mp hTF' hxT
        apply Finset.mem_union_right F
        exact Finset.mem_biUnion.mpr ⟨T, hT𝒯, hxT⟩
      have hmatching : IsMatching (insert T 𝒯) := by
        rw [IsMatching, Finset.coe_insert, Set.pairwiseDisjoint_insert]
        refine ⟨hfamily.1, ?_⟩
        intro D hD𝒯 hTD
        rw [Finset.disjoint_left]
        intro x hxT hxD
        apply Finset.disjoint_left.mp hTF' hxT
        apply Finset.mem_union_right F
        exact Finset.mem_biUnion.mpr ⟨D, hD𝒯, hxD⟩
      have hnewfamily :
          IsFullAlignedTranslateDestroyerFamily
            A k Q L (insert T 𝒯) := by
        refine ⟨hmatching, ?_, ?_, ?_⟩
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact hTnonempty
          · exact hfamily.2.1 D hD𝒯
        · intro D hD x hxD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact hTA x hxD
          · exact hfamily.2.2.1 D hD𝒯 x hxD
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact ⟨⟨q, hqQ⟩, n, a,
              haLower, haA, hnqa, hdestroy⟩
          · exact hfamily.2.2.2 D hD𝒯
      refine ⟨insert T 𝒯, hnewfamily, ?_, ?_⟩
      · simp [hTnot, hcard]
      · intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD𝒯
        · exact Finset.disjoint_of_subset_right
            (Finset.subset_union_left) hTF'
        · exact hdisjointF D hD𝒯

/- An anchored cell stores the translate anchor in the same finite block as
its moving core.  Erasing that distinguished anchor will therefore be
disjoint from a selector which chooses the anchor from the cell's block. -/
def IsAnchoredAlignedTranslateCellFamily
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ) (L : ℕ)
    (𝒞 : Finset (Finset ℕ)) : Prop :=
  IsMatching 𝒞 ∧
    (∀ C ∈ 𝒞, C.Nonempty) ∧
    (∀ C ∈ 𝒞, ∀ x ∈ C, x ∈ A) ∧
    ∀ C ∈ 𝒞, ∃ T : Finset ℕ, ∃ q : {m // m ∈ Q}, ∃ n a,
      C = insert a T ∧ L ≤ a ∧ a ∈ A ∧ n = q.1 + a ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/- Build an anchored row of arbitrary finite size.  At each extension the
anchor threshold is raised above the sum of every protected vertex; hence
both the moving core and its anchor are disjoint from all earlier cells. -/
theorem exists_anchoredAlignedTranslateCellFamily_card_disjoint
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hrecur : HasFullTranslateDestroyersByAnchor A k Q)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (L r : ℕ) :
    ∃ 𝒞 : Finset (Finset ℕ),
      IsAnchoredAlignedTranslateCellFamily A k Q L 𝒞 ∧
      𝒞.card = r ∧
      ∀ C ∈ 𝒞, Disjoint C F := by
  classical
  induction r with
  | zero =>
      refine ⟨∅, ?_, by simp, by simp⟩
      simp [IsAnchoredAlignedTranslateCellFamily, IsMatching]
  | succ r ih =>
      obtain ⟨𝒞, hfamily, hcard, hdisjointF⟩ := ih
      let U : Finset ℕ := 𝒞.biUnion id
      let F' : Finset ℕ := F ∪ U
      have hF'A : (F' : Set ℕ) ⊆ A := by
        intro x hxF'
        rcases Finset.mem_union.mp hxF' with hxF | hxU
        · exact hFA hxF
        · obtain ⟨C, hC𝒞, hxC⟩ := Finset.mem_biUnion.mp hxU
          exact hfamily.2.2.1 C hC𝒞 x hxC
      obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
          hTA, hTF', _hTnonempty, hdestroy⟩ :=
        hrecur F' hF'A (max L (F'.sum id + 1))
      have hLa : L ≤ a :=
        le_trans (le_max_left L (F'.sum id + 1)) haLower
      have haF' : a ∉ F' := by
        intro haF'
        have hale : a ≤ F'.sum id :=
          Finset.single_le_sum (s := F') (f := id)
            (fun _ _ => Nat.zero_le _) haF'
        have hsumlt : F'.sum id < a := by
          have := le_trans (le_max_right L (F'.sum id + 1)) haLower
          omega
        exact (not_lt_of_ge hale) hsumlt
      let C : Finset ℕ := insert a T
      have hCF' : Disjoint C F' := by
        rw [Finset.disjoint_left]
        intro x hxC hxF'
        rcases Finset.mem_insert.mp hxC with rfl | hxT
        · exact haF' hxF'
        · exact Finset.disjoint_left.mp hTF' hxT hxF'
      have hCnonempty : C.Nonempty :=
        ⟨a, Finset.mem_insert_self a T⟩
      have hCA : ∀ x ∈ C, x ∈ A := by
        intro x hxC
        rcases Finset.mem_insert.mp hxC with rfl | hxT
        · exact haA
        · exact hTA x hxT
      have hCnot : C ∉ 𝒞 := by
        intro hC𝒞
        obtain ⟨x, hxC⟩ := hCnonempty
        apply Finset.disjoint_left.mp hCF' hxC
        apply Finset.mem_union_right F
        exact Finset.mem_biUnion.mpr ⟨C, hC𝒞, hxC⟩
      have hmatching : IsMatching (insert C 𝒞) := by
        rw [IsMatching, Finset.coe_insert, Set.pairwiseDisjoint_insert]
        refine ⟨hfamily.1, ?_⟩
        intro D hD𝒞 hCD
        rw [Finset.disjoint_left]
        intro x hxC hxD
        apply Finset.disjoint_left.mp hCF' hxC
        apply Finset.mem_union_right F
        exact Finset.mem_biUnion.mpr ⟨D, hD𝒞, hxD⟩
      have hnewfamily :
          IsAnchoredAlignedTranslateCellFamily
            A k Q L (insert C 𝒞) := by
        refine ⟨hmatching, ?_, ?_, ?_⟩
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒞
          · exact hCnonempty
          · exact hfamily.2.1 D hD𝒞
        · intro D hD x hxD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒞
          · exact hCA x hxD
          · exact hfamily.2.2.1 D hD𝒞 x hxD
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒞
          · exact ⟨T, ⟨q, hqQ⟩, n, a,
              rfl, hLa, haA, hnqa, hdestroy⟩
          · exact hfamily.2.2.2 D hD𝒞
      refine ⟨insert C 𝒞, hnewfamily, ?_, ?_⟩
      · simp [hCnot, hcard]
      · intro D hD
        rcases Finset.mem_insert.mp hD with rfl | hD𝒞
        · exact Finset.disjoint_of_subset_right
            Finset.subset_union_left hCF'
        · exact hdisjointF D hD𝒞

/- Forgetting the internal moving core turns an anchored cell row into the
earlier full-destroyer row: destruction is monotone from `T` to
`insert a T = C`. -/
theorem IsAnchoredAlignedTranslateCellFamily.toFullFamily
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} {L : ℕ}
    {𝒞 : Finset (Finset ℕ)}
    (hfamily : IsAnchoredAlignedTranslateCellFamily A k Q L 𝒞) :
    IsFullAlignedTranslateDestroyerFamily A k Q L 𝒞 := by
  refine ⟨hfamily.1, hfamily.2.1, hfamily.2.2.1, ?_⟩
  intro C hC
  obtain ⟨T, q, n, a, hCeq, haLower, haA, hnqa, hdestroy⟩ :=
    hfamily.2.2.2 C hC
  refine ⟨q, n, a, haLower, haA, hnqa, ?_⟩
  apply hdestroy.mono
  intro x hxT
  rw [hCeq]
  exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem hxT)

/- Override an arbitrary base selector on the dedicated cell blocks by the
distinguished anchors.  The new selector is disjoint from every anchor-erased
cell, and every newly introduced selected vertex is one of the anchors. -/
theorem exists_blockSelector_overriding_dedicatedAnchors
    {A : Set ℕ} {F : ℕ → Finset ℕ} {𝒞 : Finset (Finset ℕ)}
    (P : IsFiniteBlockPartition A F)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hanchor : ∀ C, anchor C ∈ C.1)
    (base : BlockSelector F) :
    ∃ s : BlockSelector F,
      (∀ C : {C : Finset ℕ // C ∈ 𝒞},
        Disjoint
          (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
          (selectedSet s)) ∧
      ∀ x ∈ selectedSet s,
        x ∈ selectedSet base ∨ ∃ C, x = anchor C := by
  classical
  let s : BlockSelector F := fun i =>
    if hi : ∃ C : {C : Finset ℕ // C ∈ 𝒞}, locate C = i then
      let C := Classical.choose hi
      ⟨anchor C, by
        have hloc : locate C = i := Classical.choose_spec hi
        rw [← hloc]
        exact hcell C (hanchor C)⟩
    else base i
  refine ⟨s, ?_, ?_⟩
  · intro C
    rw [Set.disjoint_left]
    intro x hxErase hxs
    obtain ⟨i, hi⟩ := hxs
    change (s i).1 = x at hi
    have hxC : x ∈ C.1 :=
      Finset.erase_subset (anchor C) C.1
        (Finset.mem_coe.mp hxErase)
    have hiloc : i = locate C := by
      by_contra hne
      apply Finset.disjoint_left.mp (P.disjoint hne)
        (show x ∈ F i by rw [← hi]; exact (s i).2)
        (hcell C hxC)
    subst i
    have hsanchor : (s (locate C)).1 = anchor C := by
      dsimp only [s]
      split
      next h =>
        let D : {D : Finset ℕ // D ∈ 𝒞} := Classical.choose h
        change anchor D = anchor C
        have hDC : D = C := hlocate (Classical.choose_spec h)
        rw [hDC]
      next h => exact (h ⟨C, rfl⟩).elim
    have hxa : x = anchor C := hi.symm.trans hsanchor
    exact (Finset.mem_erase.mp (Finset.mem_coe.mp hxErase)).1 hxa
  · intro x hxs
    obtain ⟨i, hi⟩ := hxs
    change (s i).1 = x at hi
    dsimp only [s] at hi
    split at hi
    next h =>
      let C : {C : Finset ℕ // C ∈ 𝒞} := Classical.choose h
      exact Or.inr ⟨C, hi.symm⟩
    next _h =>
      exact Or.inl ⟨i, hi⟩

/- For a target-localized minimal certificate, overriding each private
selector by the large dedicated anchors preserves all the other targets.
The certificate then forces the overridden selector to destroy its own target
again.  All resulting target-indexed selectors are simultaneously disjoint
from every anchor-erased dedicated cell. -/
theorem exists_targetLocalized_anchorSelectors_of_minimalCertificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} (hQ : Q.Nonempty)
    {F : ℕ → Finset ℕ} {𝒞 : Finset (Finset ℕ)}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (additiveSupportFamily A k) (selectedSet base) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A k) (selectedSet base) q')
    (hfamily : IsAnchoredAlignedTranslateCellFamily
      A k Q (Q.max' hQ + 1) 𝒞)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C)) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      (∀ C, ∃ T : Finset ℕ, ∃ q : {m // m ∈ Q}, ∃ n,
        C.1 = insert (anchor C) T ∧
        Q.max' hQ + 1 ≤ anchor C ∧ anchor C ∈ A ∧
        n = q.1 + anchor C ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
      ∃ selectors : {q // q ∈ Q} → BlockSelector F,
        ∀ q,
          DestroysAt (additiveSupportFamily A k)
            (selectedSet (selectors q)) q.1 ∧
          (∀ q' : {q // q ∈ Q}, q' ≠ q →
            ¬ DestroysAt (additiveSupportFamily A k)
              (selectedSet (selectors q)) q'.1) ∧
          ∀ C : {C : Finset ℕ // C ∈ 𝒞}, Disjoint
            (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
            (selectedSet (selectors q)) := by
  classical
  have hwitness : ∀ C : {C // C ∈ 𝒞},
      ∃ T : Finset ℕ, ∃ q : {m // m ∈ Q}, ∃ n a,
        C.1 = insert a T ∧ Q.max' hQ + 1 ≤ a ∧ a ∈ A ∧
        n = q.1 + a ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
    intro C
    exact hfamily.2.2.2 C.1 C.2
  choose core cellTarget successor anchor hCeq haLower
    haA hnqa hdestroy using hwitness
  have hanchorMem : ∀ C, anchor C ∈ C.1 := by
    intro C
    rw [hCeq C]
    exact Finset.mem_insert_self (anchor C) (core C)
  have hbase : ∀ q : {q // q ∈ Q}, ∃ base : BlockSelector F,
      DestroysAt (additiveSupportFamily A k) (selectedSet base) q.1 ∧
      ∀ q' : {q // q ∈ Q}, q' ≠ q →
        ¬ DestroysAt (additiveSupportFamily A k)
          (selectedSet base) q'.1 := by
    intro q
    obtain ⟨base, hdestroyq, hother⟩ := hlocalized q.1 q.2
    exact ⟨base, hdestroyq, fun q' hne =>
      hother q'.1 q'.2 (fun heq => hne (Subtype.ext heq))⟩
  choose base hbaseDestroy hbaseOther using hbase
  have hoverride : ∀ q : {q // q ∈ Q}, ∃ s : BlockSelector F,
      (∀ C : {C : Finset ℕ // C ∈ 𝒞},
        Disjoint
          (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
          (selectedSet s)) ∧
      ∀ x ∈ selectedSet s,
        x ∈ selectedSet (base q) ∨ ∃ C, x = anchor C := by
    intro q
    exact exists_blockSelector_overriding_dedicatedAnchors
      P locate hlocate hcell anchor hanchorMem (base q)
  choose selectors hselectorDisjoint hselectorRange using hoverride
  have hotherSurvives : ∀ q q' : {q // q ∈ Q}, q' ≠ q →
      ¬ DestroysAt (additiveSupportFamily A k)
        (selectedSet (selectors q)) q'.1 := by
    intro q q' hne
    obtain ⟨E, hER, hEbase⟩ :=
      not_destroysAt_iff.mp (hbaseOther q q' hne)
    apply not_destroysAt_iff.mpr
    refine ⟨E, hER, ?_⟩
    rw [Set.disjoint_left]
    intro x hxE hxs
    rcases hselectorRange q x hxs with
      hxbase | ⟨C, hxanchor⟩
    · exact Set.disjoint_left.mp hEbase hxE hxbase
    · have hxleq : x ≤ q'.1 :=
        additiveSupportFamily_supportsBounded
          A k q'.1 E hER x hxE
      have hq'max : q'.1 ≤ Q.max' hQ :=
        Finset.le_max' Q q'.1 q'.2
      have halower := haLower C
      rw [hxanchor] at hxleq
      omega
  refine ⟨anchor, fun C =>
    ⟨core C, cellTarget C, successor C, hCeq C,
      haLower C, haA C, hnqa C, hdestroy C⟩,
    selectors, ?_⟩
  intro q
  have hdestroyq : DestroysAt (additiveSupportFamily A k)
      (selectedSet (selectors q)) q.1 := by
    obtain ⟨r, hrQ, hrdestroy⟩ := hcert (selectors q)
    let r' : {r // r ∈ Q} := ⟨r, hrQ⟩
    have hrq : r' = q := by
      by_contra hne
      exact hotherSurvives q r' hne hrdestroy
    simpa [r'] using hrq ▸ hrdestroy
  exact ⟨hdestroyq, hotherSurvives q, hselectorDisjoint q⟩

/- If distinct anchored cells lie in distinct partition blocks, choose their
distinguished anchors in those blocks and choose arbitrary elements elsewhere.
The resulting global selector is disjoint from every anchor-erased cell. -/
theorem exists_blockSelector_disjoint_anchoredCellErasures
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} {L : ℕ}
    {𝒞 : Finset (Finset ℕ)}
    {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hfamily : IsAnchoredAlignedTranslateCellFamily A k Q L 𝒞)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C)) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      (∀ C : {C : Finset ℕ // C ∈ 𝒞},
        ∃ T : Finset ℕ, ∃ q : {m // m ∈ Q}, ∃ n,
        C.1 = insert (anchor C) T ∧ L ≤ anchor C ∧
        anchor C ∈ A ∧ n = q.1 + anchor C ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
      ∃ s : BlockSelector F,
        ∀ C : {C : Finset ℕ // C ∈ 𝒞}, Disjoint
          (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
          (selectedSet s) := by
  classical
  have hwitness : ∀ C : {C // C ∈ 𝒞},
      ∃ T : Finset ℕ, ∃ q : {m // m ∈ Q}, ∃ n a,
        C.1 = insert a T ∧ L ≤ a ∧ a ∈ A ∧ n = q.1 + a ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
    intro C
    exact hfamily.2.2.2 C.1 C.2
  choose core target successor anchor hCeq haLower haA hnqa hdestroy using
    hwitness
  let s : BlockSelector F := fun i =>
    if hi : ∃ C : {C : Finset ℕ // C ∈ 𝒞}, locate C = i then
      let C := Classical.choose hi
      ⟨anchor C, by
        have hloc : locate C = i := Classical.choose_spec hi
        rw [← hloc]
        apply hcell C
        rw [hCeq C]
        exact Finset.mem_insert_self (anchor C) (core C)⟩
    else
      ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  refine ⟨anchor, ?_, s, ?_⟩
  · intro C
    exact ⟨core C, target C, successor C,
      hCeq C, haLower C, haA C, hnqa C, hdestroy C⟩
  · intro C
    rw [Set.disjoint_left]
    intro x hxErase hxs
    obtain ⟨i, hi⟩ := hxs
    change (s i).1 = x at hi
    have hxC : x ∈ C.1 :=
      Finset.erase_subset (anchor C) C.1 (Finset.mem_coe.mp hxErase)
    have hiloc : i = locate C := by
      by_contra hne
      apply Finset.disjoint_left.mp (P.disjoint hne)
        (show x ∈ F i by rw [← hi]; exact (s i).2)
        (hcell C hxC)
    subst i
    have hsanchor : (s (locate C)).1 = anchor C := by
      dsimp only [s]
      split
      next h =>
        let D : {D : Finset ℕ // D ∈ 𝒞} := Classical.choose h
        change anchor D = anchor C
        have hDC : D = C := hlocate (Classical.choose_spec h)
        rw [hDC]
      next h => exact (h ⟨C, rfl⟩).elim
    have hxa : x = anchor C := hi.symm.trans hsanchor
    exact (Finset.mem_erase.mp (Finset.mem_coe.mp hxErase)).1 hxa

/- Distinct rows of a diagonal family use pairwise-disjoint cores.  Matching
inside each individual row remains part of
`IsFullAlignedTranslateDestroyerFamily`. -/
def ArePairwiseDisjointDestroyerRows
    (rows : ℕ → Finset (Finset ℕ)) : Prop :=
  ∀ i j, i ≠ j → ∀ T ∈ rows i, ∀ D ∈ rows j, Disjoint T D

/- A countable certificate-aligned diagonal: every nonempty finite target set
occurs as a row label, its row has `2 * k * |Q| + 1` cores, and distinct rows
are globally disjoint. -/
def HasDiagonalFullAlignedTranslateDestroyerRows
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ enumerate : ℕ → {Q : Finset ℕ // Q.Nonempty},
    Function.Surjective enumerate ∧
    ∃ rows : ℕ → Finset (Finset ℕ),
      (∀ j,
        IsFullAlignedTranslateDestroyerFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1) ∧
      ArePairwiseDisjointDestroyerRows rows

/- The strengthened diagonal whose finite blocks are the anchored cells
`C = insert a T`, not merely the moving cores `T`. -/
def HasDiagonalAnchoredAlignedTranslateCellRows
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ enumerate : ℕ → {Q : Finset ℕ // Q.Nonempty},
    Function.Surjective enumerate ∧
    ∃ rows : ℕ → Finset (Finset ℕ),
      (∀ j,
        IsAnchoredAlignedTranslateCellFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1) ∧
      ArePairwiseDisjointDestroyerRows rows

/- The same diagonal together with one finite-block partition containing
every row core in its own dedicated block.  The injective locator prevents
two distinct row cores from being assigned to the same block. -/
def HasCertificateAlignedDestroyerRowPartition
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ enumerate : ℕ → {Q : Finset ℕ // Q.Nonempty},
    Function.Surjective enumerate ∧
    ∃ rows : ℕ → Finset (Finset ℕ),
      (∀ j,
        IsFullAlignedTranslateDestroyerFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1) ∧
      ArePairwiseDisjointDestroyerRows rows ∧
      ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
        ∃ locate : (Σ j, {T : Finset ℕ // T ∈ rows j}) → ℕ,
          Function.Injective locate ∧
          ∀ c, c.2.1 ⊆ F (locate c)

/- Enumerate every nonempty finite target set and recursively protect all
vertices used by earlier rows.  The row dedicated to `Q` has
`2 * k * |Q| + 1` cores and all of its translate anchors exceed `max Q`.

This theorem is deliberately conditional on full recurrence for every
nonempty `Q`: the relative-growth alternative is handled separately by the
finite-translate dichotomy. -/
theorem exists_diagonalFullAlignedTranslateDestroyerRows
    {A : Set ℕ} {k : ℕ}
    (hrecur : ∀ Q : Finset ℕ, Q.Nonempty →
      HasFullTranslateDestroyersByAnchor A k Q) :
    HasDiagonalFullAlignedTranslateDestroyerRows A k := by
  classical
  letI : Nonempty {Q : Finset ℕ // Q.Nonempty} :=
    ⟨⟨{0}, by simp⟩⟩
  obtain ⟨enumerate, henumerate⟩ :=
    exists_surjective_nat {Q : Finset ℕ // Q.Nonempty}
  let State := {F : Finset ℕ // (F : Set ℕ) ⊆ A}
  let initial : State := ⟨∅, by simp⟩
  let chooseRow : (j : ℕ) → (s : State) → Finset (Finset ℕ) :=
    fun j s => Classical.choose
      (exists_fullAlignedTranslateDestroyerFamily_card_disjoint
        (hrecur (enumerate j).1 (enumerate j).2)
        s.1 s.2 ((enumerate j).1.max' (enumerate j).2 + 1)
        (2 * k * (enumerate j).1.card + 1))
  have chooseRow_spec : ∀ j s,
      IsFullAlignedTranslateDestroyerFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (chooseRow j s) ∧
        (chooseRow j s).card = 2 * k * (enumerate j).1.card + 1 ∧
        ∀ T ∈ chooseRow j s, Disjoint T s.1 := by
    intro j s
    exact Classical.choose_spec
      (exists_fullAlignedTranslateDestroyerFamily_card_disjoint
        (hrecur (enumerate j).1 (enumerate j).2)
        s.1 s.2 ((enumerate j).1.max' (enumerate j).2 + 1)
        (2 * k * (enumerate j).1.card + 1))
  let advance : ℕ → State → State := fun j s =>
    ⟨s.1 ∪ (chooseRow j s).biUnion id, by
      intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxRows
      · exact s.2 hxS
      · obtain ⟨T, hTRow, hxT⟩ := Finset.mem_biUnion.mp hxRows
        exact (chooseRow_spec j s).1.2.2.1 T hTRow x hxT⟩
  let state : ℕ → State := fun j =>
    Nat.rec initial (fun i s => advance i s) j
  let used (j : ℕ) : Finset ℕ := (state j).1
  let rows (j : ℕ) : Finset (Finset ℕ) := chooseRow j (state j)
  have hstate_succ : ∀ j, state (j + 1) = advance j (state j) := by
    intro j
    simp [state]
  have hused_succ : ∀ j,
      used (j + 1) = used j ∪ (rows j).biUnion id := by
    intro j
    change (state (j + 1)).1 =
      (state j).1 ∪ (chooseRow j (state j)).biUnion id
    rw [hstate_succ]
  have hused_step : ∀ j, used j ⊆ used (j + 1) := by
    intro j
    rw [hused_succ]
    exact Finset.subset_union_left
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hrow_into_next : ∀ j, ∀ T ∈ rows j, T ⊆ used (j + 1) := by
    intro j T hTRow x hxT
    rw [hused_succ]
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨T, hTRow, hxT⟩
  have hrowspec : ∀ j,
      IsFullAlignedTranslateDestroyerFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1 ∧
        ∀ T ∈ rows j, Disjoint T (used j) := by
    intro j
    exact chooseRow_spec j (state j)
  refine ⟨enumerate, henumerate, rows, ?_, ?_⟩
  · intro j
    exact ⟨(hrowspec j).1, (hrowspec j).2.1⟩
  · intro i j hij T hTi D hDj
    by_cases hijlt : i < j
    · have hTused : T ⊆ used j :=
        fun x hx => hused_mono (Nat.succ_le_of_lt hijlt)
          (hrow_into_next i T hTi hx)
      rw [Finset.disjoint_left]
      intro x hxT hxD
      exact Finset.disjoint_left.mp ((hrowspec j).2.2 D hDj)
        hxD (hTused hxT)
    · have hjilt : j < i := by omega
      have hDused : D ⊆ used i :=
        fun x hx => hused_mono (Nat.succ_le_of_lt hjilt)
          (hrow_into_next j D hDj hx)
      rw [Finset.disjoint_left]
      intro x hxT hxD
      exact Finset.disjoint_left.mp ((hrowspec i).2.2 T hTi)
        hxT (hDused hxD)

/- Global anchored diagonal.  Every nonempty finite `Q` receives an
oversized row, and entire anchored cells (not only their moving cores) are
disjoint across all rows. -/
theorem exists_diagonalAnchoredAlignedTranslateCellRows
    {A : Set ℕ} {k : ℕ}
    (hrecur : ∀ Q : Finset ℕ, Q.Nonempty →
      HasFullTranslateDestroyersByAnchor A k Q) :
    HasDiagonalAnchoredAlignedTranslateCellRows A k := by
  classical
  letI : Nonempty {Q : Finset ℕ // Q.Nonempty} :=
    ⟨⟨{0}, by simp⟩⟩
  obtain ⟨enumerate, henumerate⟩ :=
    exists_surjective_nat {Q : Finset ℕ // Q.Nonempty}
  let State := {F : Finset ℕ // (F : Set ℕ) ⊆ A}
  let initial : State := ⟨∅, by simp⟩
  let chooseRow : (j : ℕ) → (s : State) → Finset (Finset ℕ) :=
    fun j s => Classical.choose
      (exists_anchoredAlignedTranslateCellFamily_card_disjoint
        (hrecur (enumerate j).1 (enumerate j).2)
        s.1 s.2 ((enumerate j).1.max' (enumerate j).2 + 1)
        (2 * k * (enumerate j).1.card + 1))
  have chooseRow_spec : ∀ j s,
      IsAnchoredAlignedTranslateCellFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (chooseRow j s) ∧
        (chooseRow j s).card = 2 * k * (enumerate j).1.card + 1 ∧
        ∀ C ∈ chooseRow j s, Disjoint C s.1 := by
    intro j s
    exact Classical.choose_spec
      (exists_anchoredAlignedTranslateCellFamily_card_disjoint
        (hrecur (enumerate j).1 (enumerate j).2)
        s.1 s.2 ((enumerate j).1.max' (enumerate j).2 + 1)
        (2 * k * (enumerate j).1.card + 1))
  let advance : ℕ → State → State := fun j s =>
    ⟨s.1 ∪ (chooseRow j s).biUnion id, by
      intro x hx
      rcases Finset.mem_union.mp hx with hxS | hxRows
      · exact s.2 hxS
      · obtain ⟨C, hCRow, hxC⟩ := Finset.mem_biUnion.mp hxRows
        exact (chooseRow_spec j s).1.2.2.1 C hCRow x hxC⟩
  let state : ℕ → State := fun j =>
    Nat.rec initial (fun i s => advance i s) j
  let used (j : ℕ) : Finset ℕ := (state j).1
  let rows (j : ℕ) : Finset (Finset ℕ) := chooseRow j (state j)
  have hstate_succ : ∀ j, state (j + 1) = advance j (state j) := by
    intro j
    simp [state]
  have hused_succ : ∀ j,
      used (j + 1) = used j ∪ (rows j).biUnion id := by
    intro j
    change (state (j + 1)).1 =
      (state j).1 ∪ (chooseRow j (state j)).biUnion id
    rw [hstate_succ]
  have hused_step : ∀ j, used j ⊆ used (j + 1) := by
    intro j
    rw [hused_succ]
    exact Finset.subset_union_left
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hrow_into_next : ∀ j, ∀ C ∈ rows j, C ⊆ used (j + 1) := by
    intro j C hCRow x hxC
    rw [hused_succ]
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨C, hCRow, hxC⟩
  have hrowspec : ∀ j,
      IsAnchoredAlignedTranslateCellFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1 ∧
        ∀ C ∈ rows j, Disjoint C (used j) := by
    intro j
    exact chooseRow_spec j (state j)
  refine ⟨enumerate, henumerate, rows, ?_, ?_⟩
  · intro j
    exact ⟨(hrowspec j).1, (hrowspec j).2.1⟩
  · intro i j hij C hCi D hDj
    by_cases hijlt : i < j
    · have hCused : C ⊆ used j :=
        fun x hx => hused_mono (Nat.succ_le_of_lt hijlt)
          (hrow_into_next i C hCi hx)
      rw [Finset.disjoint_left]
      intro x hxC hxD
      exact Finset.disjoint_left.mp ((hrowspec j).2.2 D hDj)
        hxD (hCused hxC)
    · have hjilt : j < i := by omega
      have hDused : D ⊆ used i :=
        fun x hx => hused_mono (Nat.succ_le_of_lt hjilt)
          (hrow_into_next j D hDj hx)
      rw [Finset.disjoint_left]
      intro x hxC hxD
      exact Finset.disjoint_left.mp ((hrowspec i).2.2 C hCi)
        hxC (hDused hxD)

/- Forgetting the internal cores of every anchored cell yields the previous
full-row diagonal, so the generic row-partition construction applies without
duplication. -/
theorem HasDiagonalAnchoredAlignedTranslateCellRows.toFullRows
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k) :
    HasDiagonalFullAlignedTranslateDestroyerRows A k := by
  obtain ⟨enumerate, henumerate, rows, hrows, hdisjoint⟩ := hdiag
  refine ⟨enumerate, henumerate, rows, ?_, hdisjoint⟩
  intro j
  exact ⟨(hrows j).1.toFullFamily, (hrows j).2⟩

/- Generic partition completion for a countable family of finite rows.  It
retains an injective locator from every row cell to the block containing it. -/
theorem exists_finiteBlockPartition_for_disjointRows
    {A : Set ℕ} {rows : ℕ → Finset (Finset ℕ)}
    (hrowsNonempty : ∀ j, (rows j).Nonempty)
    (hmatching : ∀ j, IsMatching (rows j))
    (hcellNonempty : ∀ j, ∀ C ∈ rows j, C.Nonempty)
    (hcellA : ∀ j, ∀ C ∈ rows j, ∀ x ∈ C, x ∈ A)
    (hcross : ArePairwiseDisjointDestroyerRows rows) :
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      ∃ locate : (Σ j, {C : Finset ℕ // C ∈ rows j}) → ℕ,
        Function.Injective locate ∧
        ∀ c, c.2.1 ⊆ F (locate c) := by
  classical
  let CellIndex := Σ j, {C : Finset ℕ // C ∈ rows j}
  let chooseCell : ∀ j, {C : Finset ℕ // C ∈ rows j} := fun j =>
    ⟨(hrowsNonempty j).choose, (hrowsNonempty j).choose_spec⟩
  let embed : ℕ → CellIndex := fun j => ⟨j, chooseCell j⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Sigma.fst hij
  letI : Countable CellIndex := inferInstance
  letI : Infinite CellIndex := Infinite.of_injective embed hembed
  letI : Denumerable CellIndex :=
    Classical.choice (nonempty_denumerable CellIndex)
  let e : ℕ ≃ CellIndex := (Denumerable.eqv CellIndex).symm
  let cells : ℕ → Finset ℕ := fun i => (e i).2.1
  have hcellsA : ∀ i x, x ∈ cells i → x ∈ A := by
    intro i x hx
    exact hcellA (e i).1 (e i).2.1 (e i).2.2 x hx
  have hcells_nonempty : ∀ i, (cells i).Nonempty := by
    intro i
    exact hcellNonempty (e i).1 (e i).2.1 (e i).2.2
  have hcells_disjoint : Pairwise fun i j => Disjoint (cells i) (cells j) := by
    intro i j hij
    cases hi : e i with
    | mk ri Ci =>
      cases hj : e j with
      | mk rj Cj =>
        change Disjoint (e i).2.1 (e j).2.1
        rw [hi, hj]
        by_cases hrij : ri = rj
        · subst rj
          apply hmatching ri Ci.2 Cj.2
          intro hCC
          apply hij
          apply e.injective
          rw [hi, hj]
          congr
          exact Subtype.ext hCC
        · exact hcross ri rj hrij Ci.1 Ci.2 Cj.1 Cj.2
  let R : SupportFamily := fun i => {cells i}
  let S : EscapingTransversalSequence R A :=
    { n := id
      T := cells
      n_strictMono := strictMono_id
      subset := hcellsA
      disjoint := hcells_disjoint
      nonempty := hcells_nonempty
      destroys := by
        intro i E hER
        have hE : E = cells i := by simpa [R] using hER
        subst E
        obtain ⟨x, hx⟩ := hcells_nonempty i
        apply Set.not_disjoint_iff.mpr
        exact ⟨x, Finset.mem_coe.mpr hx, Finset.mem_coe.mpr hx⟩ }
  obtain ⟨F, P, hcore⟩ := S.exists_finiteBlockPartition
  let locate : CellIndex → ℕ := fun c => e.symm c
  have hlocate : Function.Injective locate := e.symm.injective
  refine ⟨F, P, locate, hlocate, ?_⟩
  intro c
  have hc := hcore (locate c)
  change (e (e.symm c)).2.1 ⊆ F (e.symm c) at hc
  rw [e.apply_symm_apply] at hc
  exact hc

/- Anchored diagonal plus its own certificate-ready partition. -/
def HasCertificateAlignedAnchoredCellRowPartition
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ enumerate : ℕ → {Q : Finset ℕ // Q.Nonempty},
    Function.Surjective enumerate ∧
    ∃ rows : ℕ → Finset (Finset ℕ),
      (∀ j,
        IsAnchoredAlignedTranslateCellFamily
          A k (enumerate j).1 ((enumerate j).1.max' (enumerate j).2 + 1)
            (rows j) ∧
        (rows j).card = 2 * k * (enumerate j).1.card + 1) ∧
      ArePairwiseDisjointDestroyerRows rows ∧
      ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
        ∃ locate : (Σ j, {C : Finset ℕ // C ∈ rows j}) → ℕ,
          Function.Injective locate ∧
          ∀ c, c.2.1 ⊆ F (locate c)

theorem HasDiagonalAnchoredAlignedTranslateCellRows.exists_rowPartition
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k) :
    HasCertificateAlignedAnchoredCellRowPartition A k := by
  obtain ⟨enumerate, henumerate, rows, hrows, hcross⟩ := hdiag
  have hrowsNonempty : ∀ j, (rows j).Nonempty := by
    intro j
    rw [← Finset.card_pos, (hrows j).2]
    omega
  obtain ⟨F, P, locate, hlocate, hcell⟩ :=
    exists_finiteBlockPartition_for_disjointRows
      hrowsNonempty
      (fun j => (hrows j).1.1)
      (fun j => (hrows j).1.2.1)
      (fun j => (hrows j).1.2.2.1)
      hcross
  exact ⟨enumerate, henumerate, rows, hrows, hcross,
    F, P, locate, hlocate, hcell⟩

/- Flatten the globally disjoint rows into a countable core sequence and use
the existing partition-completion construction.  This is the literal bridge
from the diagonal rows to a partition on which strong deletion can return a
finite certificate. -/
theorem HasDiagonalFullAlignedTranslateDestroyerRows.exists_rowPartition
    {A : Set ℕ} {k : ℕ}
    (hdiag : HasDiagonalFullAlignedTranslateDestroyerRows A k) :
    HasCertificateAlignedDestroyerRowPartition A k := by
  classical
  obtain ⟨enumerate, henumerate, rows, hrows, hrowdisjoint⟩ := hdiag
  have hrows_nonempty : ∀ j, (rows j).Nonempty := by
    intro j
    rw [← Finset.card_pos]
    rw [(hrows j).2]
    omega
  let CoreIndex := Σ j, {T : Finset ℕ // T ∈ rows j}
  let chooseCore : ∀ j, {T : Finset ℕ // T ∈ rows j} := fun j =>
    ⟨(hrows_nonempty j).choose, (hrows_nonempty j).choose_spec⟩
  let embed : ℕ → CoreIndex := fun j => ⟨j, chooseCore j⟩
  have hembed : Function.Injective embed := by
    intro i j hij
    exact congrArg Sigma.fst hij
  letI : Countable CoreIndex := inferInstance
  letI : Infinite CoreIndex := Infinite.of_injective embed hembed
  letI : Denumerable CoreIndex :=
    Classical.choice (nonempty_denumerable CoreIndex)
  let e : ℕ ≃ CoreIndex := (Denumerable.eqv CoreIndex).symm
  let cores : ℕ → Finset ℕ := fun i => (e i).2.1
  have hcoresA : ∀ i x, x ∈ cores i → x ∈ A := by
    intro i x hx
    exact (hrows (e i).1).1.2.2.1
      (e i).2.1 (e i).2.2 x hx
  have hcores_nonempty : ∀ i, (cores i).Nonempty := by
    intro i
    exact (hrows (e i).1).1.2.1 (e i).2.1 (e i).2.2
  have hcores_disjoint : Pairwise fun i j => Disjoint (cores i) (cores j) := by
    intro i j hij
    cases hi : e i with
    | mk ri Ti =>
      cases hj : e j with
      | mk rj Tj =>
        change Disjoint (e i).2.1 (e j).2.1
        rw [hi, hj]
        by_cases hrij : ri = rj
        · subst rj
          apply (hrows ri).1.1 Ti.2 Tj.2
          intro hTT
          apply hij
          apply e.injective
          rw [hi, hj]
          congr
          exact Subtype.ext hTT
        · exact hrowdisjoint ri rj hrij
            Ti.1 Ti.2 Tj.1 Tj.2
  let R : SupportFamily := fun i => {cores i}
  let S : EscapingTransversalSequence R A :=
    { n := id
      T := cores
      n_strictMono := strictMono_id
      subset := hcoresA
      disjoint := hcores_disjoint
      nonempty := hcores_nonempty
      destroys := by
        intro i E hER
        have hE : E = cores i := by simpa [R] using hER
        subst E
        obtain ⟨x, hx⟩ := hcores_nonempty i
        apply Set.not_disjoint_iff.mpr
        exact ⟨x, Finset.mem_coe.mpr hx, Finset.mem_coe.mpr hx⟩ }
  obtain ⟨F, P, hcore⟩ := S.exists_finiteBlockPartition
  let locate : CoreIndex → ℕ := fun c => e.symm c
  have hlocate : Function.Injective locate := e.symm.injective
  refine ⟨enumerate, henumerate, rows, hrows, hrowdisjoint,
    F, P, locate, hlocate, ?_⟩
  intro c
  have hc := hcore (locate c)
  change (e (e.symm c)).2.1 ⊆ F (e.symm c) at hc
  rw [e.apply_symm_apply] at hc
  exact hc

/- The finite package obtained after strong deletion chooses a certificate:
the certificate target set `Q`, its dedicated oversized diagonal row, and an
injective assignment of every core in that row to a distinct block of the
same certified partition. -/
def HasFiniteCertificateWithDedicatedLargeRow
    (A : Set ℕ) (k N : ℕ) : Prop :=
  ∃ Q : Finset ℕ, ∃ hQ : Q.Nonempty,
    (∀ q ∈ Q, N ≤ q) ∧
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A k) (selectedSet s) q) ∧
      ∃ 𝒯 : Finset (Finset ℕ),
        IsFullAlignedTranslateDestroyerFamily
          A k Q (Q.max' hQ + 1) 𝒯 ∧
        𝒯.card = 2 * k * Q.card + 1 ∧
        ∃ locate : {T : Finset ℕ // T ∈ 𝒯} → ℕ,
          Function.Injective locate ∧
          ∀ T, T.1 ⊆ F (locate T)

/- Anchored version of the finite certificate package. -/
def HasFiniteCertificateWithDedicatedAnchoredRow
    (A : Set ℕ) (k N : ℕ) : Prop :=
  ∃ Q : Finset ℕ, ∃ hQ : Q.Nonempty,
    (∀ q ∈ Q, N ≤ q) ∧
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A k) (selectedSet s) q) ∧
      ∃ 𝒞 : Finset (Finset ℕ),
        IsAnchoredAlignedTranslateCellFamily
          A k Q (Q.max' hQ + 1) 𝒞 ∧
        𝒞.card = 2 * k * Q.card + 1 ∧
        ∃ locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
          Function.Injective locate ∧
          ∀ C, C.1 ⊆ F (locate C)

/- The same package after shrinking the strong-deletion certificate to a
cardinal-minimal subcertificate.  The additional localization clause says
that each remaining target has a selector which destroys exactly that target
among the certificate targets. -/
def HasFiniteMinimalCertificateWithDedicatedAnchoredRow
    (A : Set ℕ) (k N : ℕ) : Prop :=
  ∃ Q : Finset ℕ, ∃ hQ : Q.Nonempty,
    (∀ q ∈ Q, N ≤ q) ∧
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A k) (selectedSet s) q) ∧
      (∀ q ∈ Q, ∃ s : BlockSelector F,
        DestroysAt
            (additiveSupportFamily A k) (selectedSet s) q ∧
          ∀ q' ∈ Q, q' ≠ q →
            ¬ DestroysAt
              (additiveSupportFamily A k) (selectedSet s) q') ∧
      ∃ 𝒞 : Finset (Finset ℕ),
        IsAnchoredAlignedTranslateCellFamily
          A k Q (Q.max' hQ + 1) 𝒞 ∧
        𝒞.card = 2 * k * Q.card + 1 ∧
        ∃ locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
          Function.Injective locate ∧
          ∀ C, C.1 ⊆ F (locate C)

/- Strong deletion applied to the diagonal row partition returns a finite
certificate, and surjectivity of the row enumeration supplies the dedicated
row for exactly that certificate `Q`. -/
theorem HasCertificateAlignedDestroyerRowPartition.finiteCertificateWithDedicatedRow
    {A : Set ℕ} {k : ℕ}
    (hpartition : HasCertificateAlignedDestroyerRowPartition A k)
    (hstrong : StrongInfiniteDeletion (additiveSupportFamily A k) A) :
    ∀ N, HasFiniteCertificateWithDedicatedLargeRow A k N := by
  classical
  intro N
  obtain ⟨enumerate, henumerate, rows, hrows, hrowdisjoint,
      F, P, locate, hlocate, hcore⟩ := hpartition
  obtain ⟨Q, hQN, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hstrong) F P N
  let s : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q, hqQ, _hdestroy⟩ := hcert s
  have hQ : Q.Nonempty := ⟨q, hqQ⟩
  obtain ⟨j, hj⟩ := henumerate ⟨Q, hQ⟩
  have hQeq : (enumerate j).1 = Q := congrArg Subtype.val hj
  have hfamily :
      IsFullAlignedTranslateDestroyerFamily
        A k Q (Q.max' hQ + 1) (rows j) := by
    simpa [hQeq] using (hrows j).1
  have hcard : (rows j).card = 2 * k * Q.card + 1 := by
    simpa [hQeq] using (hrows j).2
  let locateRow : {T : Finset ℕ // T ∈ rows j} → ℕ := fun T =>
    locate ⟨j, T⟩
  have hlocateRow : Function.Injective locateRow := by
    intro T D hTD
    apply Subtype.ext
    have hcoreIndex :
        (⟨j, T⟩ : (Σ i, {E : Finset ℕ // E ∈ rows i})) = ⟨j, D⟩ :=
      hlocate hTD
    exact congrArg (fun c => c.2.1) hcoreIndex
  have hrowCore : ∀ T : {T : Finset ℕ // T ∈ rows j},
      T.1 ⊆ F (locateRow T) := by
    intro T
    exact hcore ⟨j, T⟩
  exact ⟨Q, hQ, hQN, F, P, hcert, rows j,
    hfamily, hcard, locateRow, hlocateRow, hrowCore⟩

theorem HasCertificateAlignedAnchoredCellRowPartition.finiteCertificateWithDedicatedRow
    {A : Set ℕ} {k : ℕ}
    (hpartition : HasCertificateAlignedAnchoredCellRowPartition A k)
    (hstrong : StrongInfiniteDeletion (additiveSupportFamily A k) A) :
    ∀ N, HasFiniteCertificateWithDedicatedAnchoredRow A k N := by
  classical
  intro N
  obtain ⟨enumerate, henumerate, rows, hrows, hrowdisjoint,
      F, P, locate, hlocate, hcell⟩ := hpartition
  obtain ⟨Q, hQN, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hstrong) F P N
  let s : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q, hqQ, _hdestroy⟩ := hcert s
  have hQ : Q.Nonempty := ⟨q, hqQ⟩
  obtain ⟨j, hj⟩ := henumerate ⟨Q, hQ⟩
  have hQeq : (enumerate j).1 = Q := congrArg Subtype.val hj
  have hfamily :
      IsAnchoredAlignedTranslateCellFamily
        A k Q (Q.max' hQ + 1) (rows j) := by
    simpa [hQeq] using (hrows j).1
  have hcard : (rows j).card = 2 * k * Q.card + 1 := by
    simpa [hQeq] using (hrows j).2
  let locateRow : {C : Finset ℕ // C ∈ rows j} → ℕ := fun C =>
    locate ⟨j, C⟩
  have hlocateRow : Function.Injective locateRow := by
    intro C D hCD
    apply Subtype.ext
    have hcellIndex :
        (⟨j, C⟩ : (Σ i, {E : Finset ℕ // E ∈ rows i})) = ⟨j, D⟩ :=
      hlocate hCD
    exact congrArg (fun c => c.2.1) hcellIndex
  have hrowCell : ∀ C : {C : Finset ℕ // C ∈ rows j},
      C.1 ⊆ F (locateRow C) := by
    intro C
    exact hcell ⟨j, C⟩
  exact ⟨Q, hQ, hQN, F, P, hcert, rows j,
    hfamily, hcard, locateRow, hlocateRow, hrowCell⟩

/- Strong deletion first supplies a finite certificate on the aligned row
partition.  Shrinking it to a cardinal-minimal subcertificate preserves its
late lower bound; the diagonal enumeration then supplies the dedicated row
for the smaller, target-localized certificate itself. -/
theorem HasCertificateAlignedAnchoredCellRowPartition.finiteMinimalCertificateWithDedicatedRow
    {A : Set ℕ} {k : ℕ}
    (hpartition : HasCertificateAlignedAnchoredCellRowPartition A k)
    (hstrong : StrongInfiniteDeletion (additiveSupportFamily A k) A) :
    ∀ N, HasFiniteMinimalCertificateWithDedicatedAnchoredRow A k N := by
  classical
  intro N
  obtain ⟨enumerate, henumerate, rows, hrows, _hrowdisjoint,
      F, P, locate, hlocate, hcell⟩ := hpartition
  obtain ⟨Qraw, hQrawN, hcertRaw⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hstrong) F P N
  obtain ⟨Q, hQQraw, hcert, hlocalized⟩ :=
    exists_minimal_targetLocalized_subcertificate hcertRaw
  let s : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  obtain ⟨q, hqQ, _hdestroy⟩ := hcert s
  have hQ : Q.Nonempty := ⟨q, hqQ⟩
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hqQ
    exact hQrawN q (hQQraw hqQ)
  obtain ⟨j, hj⟩ := henumerate ⟨Q, hQ⟩
  have hQeq : (enumerate j).1 = Q := congrArg Subtype.val hj
  have hfamily :
      IsAnchoredAlignedTranslateCellFamily
        A k Q (Q.max' hQ + 1) (rows j) := by
    simpa [hQeq] using (hrows j).1
  have hcard : (rows j).card = 2 * k * Q.card + 1 := by
    simpa [hQeq] using (hrows j).2
  let locateRow : {C : Finset ℕ // C ∈ rows j} → ℕ := fun C =>
    locate ⟨j, C⟩
  have hlocateRow : Function.Injective locateRow := by
    intro C D hCD
    apply Subtype.ext
    have hcellIndex :
        (⟨j, C⟩ : (Σ i, {E : Finset ℕ // E ∈ rows i})) = ⟨j, D⟩ :=
      hlocate hCD
    exact congrArg (fun c => c.2.1) hcellIndex
  have hrowCell : ∀ C : {C : Finset ℕ // C ∈ rows j},
      C.1 ⊆ F (locateRow C) := by
    intro C
    exact hcell ⟨j, C⟩
  exact ⟨Q, hQ, hQN, F, P, hcert, hlocalized, rows j,
    hfamily, hcard, locateRow, hlocateRow, hrowCell⟩

/- The global relative-growth alternative: matching growth holds outside one
finite core along `Q + A` for at least one nonempty finite target set `Q`. -/
def HasSomeFiniteTranslateMatchingGrowth
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ Q : Finset ℕ, Q.Nonempty ∧
    ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 1)) F
        (finiteTargetTranslates A Q)

/- A target whose single translate `q + A` has successor matching growth
outside some finite core. -/
def HasSingletonTranslateMatchingGrowth
    (A : Set ℕ) (k q : ℕ) : Prop :=
  ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
    OutsideMatchingTendsToInfinityAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A {q})

/- Growth on a finite union `Q + A` is equivalent to growth on every one of
its singleton translates, with possibly different initial cores.  For the
reverse implication, union the finitely many cores and take the maximum of
the finitely many matching thresholds. -/
theorem finiteTargetTranslateGrowth_iff_singletonTranslateGrowth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 1)) F
        (finiteTargetTranslates A Q)) ↔
      ∀ q ∈ Q, HasSingletonTranslateMatchingGrowth A k q := by
  classical
  constructor
  · rintro ⟨F, hFA, hgrowth⟩ q hqQ
    refine ⟨F, hFA, ?_⟩
    intro j
    obtain ⟨N, hN⟩ := hgrowth j
    refine ⟨N, ?_⟩
    intro n hn hnq
    obtain ⟨q', hq'singleton, a, haA, hnqa⟩ := hnq
    have hq'eq : q' = q := by simpa using hq'singleton
    exact hN n hn ⟨q, hqQ, a, haA, hq'eq ▸ hnqa⟩
  · intro hsingle
    have hindexed : ∀ q : {q // q ∈ Q},
        ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
          OutsideMatchingTendsToInfinityAlong
            (additiveSupportFamily A (k + 1)) F
            (finiteTargetTranslates A {q.1}) := by
      intro q
      exact hsingle q.1 q.2
    choose core hcoreA hcoreGrowth using hindexed
    let F : Finset ℕ := Q.attach.biUnion core
    have hFA : (F : Set ℕ) ⊆ A := by
      intro x hxF
      obtain ⟨q, _hqattach, hxcore⟩ :=
        Finset.mem_biUnion.mp hxF
      exact hcoreA q hxcore
    have hcommon : ∀ q : {q // q ∈ Q},
        OutsideMatchingTendsToInfinityAlong
          (additiveSupportFamily A (k + 1)) F
          (finiteTargetTranslates A {q.1}) := by
      intro q
      apply outsideMatchingTendsToInfinityAlong_mono_core
        (F := core q)
      · intro x hx
        exact Finset.mem_biUnion.mpr ⟨q, by simp, hx⟩
      · exact hcoreGrowth q
    refine ⟨F, hFA, ?_⟩
    intro j
    have hthreshold : ∀ q : {q // q ∈ Q}, ∃ N,
        ∀ n, N ≤ n → n ∈ finiteTargetTranslates A {q.1} →
          j < matchingNumber
            (outsideSupportHypergraph
              (additiveSupportFamily A (k + 1)) F n) := by
      intro q
      exact hcommon q j
    choose threshold hthresholdSpec using hthreshold
    let N := Q.attach.sup threshold
    refine ⟨N, ?_⟩
    intro n hn hnQ
    obtain ⟨q, hqQ, a, haA, hnqa⟩ := hnQ
    let q' : {q // q ∈ Q} := ⟨q, hqQ⟩
    have hq'attach : q' ∈ Q.attach := by simp [q']
    have hthresholdq : threshold q' ≤ N :=
      Finset.le_sup hq'attach
    apply hthresholdSpec q' n (le_trans hthresholdq hn)
    exact ⟨q'.1, by simp, a, haA,
      by simpa [q'] using hnqa⟩

/- Thus the apparently finite-set growth branch is already witnessed by one
singleton translate. -/
theorem hasSomeFiniteTranslateMatchingGrowth_iff_exists_singleton
    {A : Set ℕ} {k : ℕ} :
    HasSomeFiniteTranslateMatchingGrowth A k ↔
      ∃ q, HasSingletonTranslateMatchingGrowth A k q := by
  constructor
  · rintro ⟨Q, hQ, hgrowth⟩
    obtain ⟨q, hqQ⟩ := hQ
    exact ⟨q,
      (finiteTargetTranslateGrowth_iff_singletonTranslateGrowth.mp
        hgrowth) q hqQ⟩
  · rintro ⟨q, hq⟩
    refine ⟨{q}, by simp, ?_⟩
    apply finiteTargetTranslateGrowth_iff_singletonTranslateGrowth.mpr
    simpa using hq

/- The exact strengthened growth alternative which would close the relative
route: finitely many growth-bearing singleton translates cover a tail. -/
def HasFiniteCofiniteGrowthTranslateCover
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ Q : Finset ℕ,
    (∀ q ∈ Q, HasSingletonTranslateMatchingGrowth A k q) ∧
    ∃ N, ∀ n, N ≤ n → n ∈ finiteTargetTranslates A Q

/- Relative moving transversals along `Q + A` are exactly the explicit
translate-recurrent formulation. -/
theorem boundedMovingOutsideTransversalsAlong_finiteTargetTranslates_iff
    {A : Set ℕ} {Q : Finset ℕ} {R : SupportFamily} :
    HasBoundedMovingOutsideTransversalsAlong
        R A (finiteTargetTranslates A Q) ↔
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates R A Q := by
  constructor
  · intro hmoving F hFA
    obtain ⟨m, hm⟩ := hmoving F hFA
    refine ⟨m, ?_⟩
    intro N
    obtain ⟨n, T, hn, hnQA, hTA, hTF, hTcard, htrans⟩ := hm N
    obtain ⟨q, hqQ, a, haA, hnqa⟩ := hnQA
    exact ⟨n, T, q, a, hn, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩
  · intro hmoving F hFA
    obtain ⟨m, hm⟩ := hmoving F hFA
    refine ⟨m, ?_⟩
    intro N
    obtain ⟨n, T, q, a, hn, hqQ, haA, hnqa,
      hTA, hTF, hTcard, htrans⟩ := hm N
    exact ⟨n, T, hn, ⟨q, hqQ, a, haA, hnqa⟩,
      hTA, hTF, hTcard, htrans⟩

/- The strengthened/reformulated matching dichotomy on `Q + A`: its bad
branch now returns arbitrarily large targets with explicit equations
`n = q + a`, instead of an unrelated cofinal sequence. -/
theorem failsFiniteCoreMatchingAlong_finiteTargetTranslates_iff
    {A : Set ℕ} {Q : Finset ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r) :
    FailsFiniteCoreMatchingAlong R A (finiteTargetTranslates A Q) ↔
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates R A Q :=
  (failsFiniteCoreMatchingAlong_iff_boundedMovingOutsideTransversalsAlong
      hRA hcard).trans
    boundedMovingOutsideTransversalsAlong_finiteTargetTranslates_iff

/- Exhaustive matching dichotomy on the finite union `Q + A`.  In the bad
branch the returned targets carry explicit translate witnesses. -/
theorem finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
    {A : Set ℕ} {Q : Finset ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        R F (finiteTargetTranslates A Q)) ∨
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates R A Q := by
  obtain hgrowth | hmoving :=
    exists_finiteCore_outsideMatchingAlong_or_boundedMovingAlong
      (S := finiteTargetTranslates A Q) hRA hcard
  · exact Or.inl hgrowth
  · exact Or.inr <|
      boundedMovingOutsideTransversalsAlong_finiteTargetTranslates_iff.mp
        hmoving

/- Multi-target version of the disjoint-destroyer bound.  After choosing one
support for each `q ∈ Q`, every pairwise-disjoint destroyer assigned to a
target in `Q` consumes a distinct point of the finite support union. -/
theorem card_pairwiseDisjoint_additiveDestroyers_over_finiteTargets_le
    {A : Set ℕ} {h : ℕ} {Q : Finset ℕ}
    {𝒯 : Finset (Finset ℕ)}
    (c : FiniteSupportChoice (additiveSupportFamily A h) Q)
    (hpair : IsMatching 𝒯)
    (hdestroy : ∀ T ∈ 𝒯, ∃ q : {n // n ∈ Q},
      DestroysAt (additiveSupportFamily A h) (T : Set ℕ) q.1) :
    𝒯.card ≤ h * Q.card := by
  classical
  have hdestroy' : ∀ T : {T // T ∈ 𝒯},
      ∃ q : {n // n ∈ Q},
        DestroysAt (additiveSupportFamily A h) (T.1 : Set ℕ) q.1 :=
    fun T => hdestroy T.1 T.2
  choose target htarget using hdestroy'
  let U := finiteSupportChoiceUnion c
  let pick : ∀ T : {T // T ∈ 𝒯}, {x // x ∈ U} := fun T =>
    let w := Set.not_disjoint_iff.mp
      (htarget T (c (target T)).1 (c (target T)).2)
    ⟨w.choose,
      finiteSupportChoice_subset_union c (target T) w.choose_spec.1⟩
  have hpick_mem : ∀ T : {T // T ∈ 𝒯}, (pick T).1 ∈ T.1 := by
    intro T
    change
      (Set.not_disjoint_iff.mp
        (htarget T (c (target T)).1 (c (target T)).2)).choose ∈ T.1
    exact Finset.mem_coe.mp
      (Set.not_disjoint_iff.mp
        (htarget T (c (target T)).1 (c (target T)).2)).choose_spec.2
  have hpick_injective : Function.Injective pick := by
    intro T T' hpick
    apply Subtype.ext
    by_contra hTT'
    have hdisj : Disjoint T.1 T'.1 := hpair T.2 T'.2 hTT'
    have hx : (pick T).1 = (pick T').1 :=
      congrArg Subtype.val hpick
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick T).1, hpick_mem T, hx ▸ hpick_mem T'⟩) hdisj
  have hcardU : 𝒯.card ≤ U.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  exact le_trans hcardU <|
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A h) c

/- One additional (possibly infinite) destroyer can be counted together with
a finite matching whenever it is disjoint from every member of that matching.
Only one intersection point with its assigned support is used, so the same
finite support-union injection applies. -/
theorem card_pairwiseDisjoint_additiveDestroyers_with_disjoint_extra_le
    {A B : Set ℕ} {h : ℕ} {Q : Finset ℕ}
    {𝒟 : Finset (Finset ℕ)}
    (c : FiniteSupportChoice (additiveSupportFamily A h) Q)
    (hpair : IsMatching 𝒟)
    (hdestroy : ∀ D ∈ 𝒟, ∃ q : {n // n ∈ Q},
      DestroysAt (additiveSupportFamily A h) (D : Set ℕ) q.1)
    (hextra : ∃ q : {n // n ∈ Q},
      DestroysAt (additiveSupportFamily A h) B q.1)
    (hdisjoint : ∀ D ∈ 𝒟, Disjoint (D : Set ℕ) B) :
    𝒟.card + 1 ≤ h * Q.card := by
  classical
  have hdestroy' : ∀ D : {D // D ∈ 𝒟},
      ∃ q : {n // n ∈ Q},
        DestroysAt (additiveSupportFamily A h) (D.1 : Set ℕ) q.1 :=
    fun D => hdestroy D.1 D.2
  choose target htarget using hdestroy'
  obtain ⟨extraTarget, hExtraDestroy⟩ := hextra
  let U := finiteSupportChoiceUnion c
  let pickD : ∀ D : {D // D ∈ 𝒟}, {x // x ∈ U} := fun D =>
    let w := Set.not_disjoint_iff.mp
      (htarget D (c (target D)).1 (c (target D)).2)
    ⟨w.choose,
      finiteSupportChoice_subset_union c (target D) w.choose_spec.1⟩
  have hpickD_mem : ∀ D : {D // D ∈ 𝒟}, (pickD D).1 ∈ D.1 := by
    intro D
    change
      (Set.not_disjoint_iff.mp
        (htarget D (c (target D)).1 (c (target D)).2)).choose ∈ D.1
    exact Finset.mem_coe.mp
      (Set.not_disjoint_iff.mp
        (htarget D (c (target D)).1 (c (target D)).2)).choose_spec.2
  let extraHit := Set.not_disjoint_iff.mp
    (hExtraDestroy (c extraTarget).1 (c extraTarget).2)
  let pickExtra : {x // x ∈ U} :=
    ⟨extraHit.choose,
      finiteSupportChoice_subset_union c extraTarget extraHit.choose_spec.1⟩
  have hpickExtra_mem : (pickExtra : ℕ) ∈ B := extraHit.choose_spec.2
  let pick : Option {D // D ∈ 𝒟} → {x // x ∈ U}
    | none => pickExtra
    | some D => pickD D
  have hpick_injective : Function.Injective pick := by
    intro X Y hXY
    cases X with
    | none =>
      cases Y with
      | none => rfl
      | some D =>
        exfalso
        have hx : (pickExtra : ℕ) = (pickD D).1 :=
          congrArg Subtype.val hXY
        exact Set.disjoint_left.mp (hdisjoint D.1 D.2)
          (hpickD_mem D) (hx ▸ hpickExtra_mem)
    | some D =>
      cases Y with
      | none =>
        exfalso
        have hx : (pickD D).1 = (pickExtra : ℕ) :=
          congrArg Subtype.val hXY
        exact Set.disjoint_left.mp (hdisjoint D.1 D.2)
          (hpickD_mem D) (hx ▸ hpickExtra_mem)
      | some D' =>
        congr 1
        apply Subtype.ext
        by_contra hDD'
        have hx : (pickD D).1 = (pickD D').1 :=
          congrArg Subtype.val hXY
        exact (Finset.not_disjoint_iff.mpr
          ⟨(pickD D).1, hpickD_mem D, hx ▸ hpickD_mem D'⟩)
          (hpair D.2 D'.2 hDD')
  have hcardU : 𝒟.card + 1 ≤ U.card := by
    simpa only [Fintype.card_option, Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  exact hcardU.trans <|
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A h) c

/- If every certified target has its own extra destroyer, and each ordinary
destroyer is disjoint from the extra destroyer for its assigned target, count
fiberwise over the target map.  Each target fiber plus its private extra uses
at most `h` vertices of the chosen support for that target. -/
theorem card_additiveDestroyers_with_targetwise_disjoint_extras_le
    {A : Set ℕ} {h : ℕ} {Q : Finset ℕ}
    {𝒟 : Finset (Finset ℕ)}
    (c : FiniteSupportChoice (additiveSupportFamily A h) Q)
    (hpair : IsMatching 𝒟)
    (target : Finset ℕ → ℕ)
    (htarget : ∀ D ∈ 𝒟, target D ∈ Q)
    (hdestroy : ∀ D ∈ 𝒟,
      DestroysAt
        (additiveSupportFamily A h) (D : Set ℕ) (target D))
    (extra : {q // q ∈ Q} → Set ℕ)
    (hextra : ∀ q, DestroysAt
      (additiveSupportFamily A h) (extra q) q.1)
    (hdisjoint : ∀ D, ∀ hD : D ∈ 𝒟,
      Disjoint (D : Set ℕ) (extra ⟨target D, htarget D hD⟩)) :
    𝒟.card + Q.card ≤ h * Q.card := by
  classical
  have hfiberBound : ∀ q ∈ Q,
      (𝒟.filter fun D => target D = q).card + 1 ≤ h := by
    intro q hqQ
    let qsub : {q // q ∈ Q} := ⟨q, hqQ⟩
    let Dq := 𝒟.filter fun D => target D = q
    let cSingle :
        FiniteSupportChoice (additiveSupportFamily A h) {q} :=
      fun r =>
        have hrq : r.1 = q := Finset.mem_singleton.mp r.2
        ⟨(c qsub).1, by
          rw [hrq]
          exact (c qsub).2⟩
    have hDqPair : IsMatching Dq := by
      intro D hD D' hD' hDD'
      exact hpair (Finset.mem_filter.mp hD).1
        (Finset.mem_filter.mp hD').1 hDD'
    have hDqDestroy : ∀ D ∈ Dq,
        ∃ r : {n // n ∈ ({q} : Finset ℕ)},
          DestroysAt
            (additiveSupportFamily A h) (D : Set ℕ) r.1 := by
      intro D hD
      have hD𝒟 := (Finset.mem_filter.mp hD).1
      have htq := (Finset.mem_filter.mp hD).2
      refine ⟨⟨q, by simp⟩, ?_⟩
      simpa [htq] using hdestroy D hD𝒟
    have hDqDisjoint : ∀ D ∈ Dq,
        Disjoint (D : Set ℕ) (extra qsub) := by
      intro D hD
      have hD𝒟 := (Finset.mem_filter.mp hD).1
      have htq := (Finset.mem_filter.mp hD).2
      have hd := hdisjoint D hD𝒟
      simpa [qsub, htq] using hd
    have hbound :=
      card_pairwiseDisjoint_additiveDestroyers_with_disjoint_extra_le
        cSingle hDqPair hDqDestroy
        ⟨⟨q, by simp⟩, by simpa [qsub] using hextra qsub⟩
        hDqDisjoint
    simpa [Dq] using hbound
  have hmaps :
      Set.MapsTo target (𝒟 : Set (Finset ℕ)) (Q : Set ℕ) := by
    intro D hD
    exact htarget D hD
  have hfibers : 𝒟.card =
      ∑ q ∈ Q, (𝒟.filter fun D => target D = q).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    𝒟.card + Q.card =
        ∑ q ∈ Q,
          ((𝒟.filter fun D => target D = q).card + 1) := by
      rw [hfibers]
      simp only [Finset.sum_add_distrib]
      simp
    _ ≤ ∑ _q ∈ Q, h := by
      gcongr with q hq
      exact hfiberBound q hq
    _ = h * Q.card := by simp [Nat.mul_comm]

/- Subtype-indexed version, convenient when the target assignment is only
defined for members of the destroyer family. -/
theorem card_additiveDestroyers_with_targetwise_disjoint_extras_subtype
    {A : Set ℕ} {h : ℕ} {Q : Finset ℕ}
    {𝒟 : Finset (Finset ℕ)}
    (c : FiniteSupportChoice (additiveSupportFamily A h) Q)
    (hpair : IsMatching 𝒟)
    (target : {D // D ∈ 𝒟} → {q // q ∈ Q})
    (hdestroy : ∀ D : {D // D ∈ 𝒟},
      DestroysAt
        (additiveSupportFamily A h) (D.1 : Set ℕ) (target D).1)
    (extra : {q // q ∈ Q} → Set ℕ)
    (hextra : ∀ q, DestroysAt
      (additiveSupportFamily A h) (extra q) q.1)
    (hdisjoint : ∀ D : {D // D ∈ 𝒟},
      Disjoint (D.1 : Set ℕ) (extra (target D))) :
    𝒟.card + Q.card ≤ h * Q.card := by
  classical
  let targetTotal : Finset ℕ → ℕ := fun D =>
    if hD : D ∈ 𝒟 then (target ⟨D, hD⟩).1 else 0
  have htargetTotal : ∀ D ∈ 𝒟, targetTotal D ∈ Q := by
    intro D hD
    simp only [targetTotal, dif_pos hD]
    exact (target ⟨D, hD⟩).2
  have hdestroyTotal : ∀ D ∈ 𝒟,
      DestroysAt
        (additiveSupportFamily A h) (D : Set ℕ) (targetTotal D) := by
    intro D hD
    simpa only [targetTotal, dif_pos hD] using
      hdestroy ⟨D, hD⟩
  have hdisjointTotal : ∀ D, ∀ hD : D ∈ 𝒟,
      Disjoint (D : Set ℕ)
        (extra ⟨targetTotal D, htargetTotal D hD⟩) := by
    intro D hD
    have heq :
        (⟨targetTotal D, htargetTotal D hD⟩ : {q // q ∈ Q}) =
          target ⟨D, hD⟩ := by
      apply Subtype.ext
      simp [targetTotal, hD]
    rw [heq]
    exact hdisjoint ⟨D, hD⟩
  exact card_additiveDestroyers_with_targetwise_disjoint_extras_le
    c hpair targetTotal htargetTotal hdestroyTotal extra hextra
      hdisjointTotal

/- Every selector in one finite certificate destroys some target in the same
finite set `Q`.  Therefore any pairwise-disjoint family of such selectors is
bounded by the usual `k * |Q|` support-union count.  This is the exact
quantitative payoff available from trying several disjoint certificate
selectors. -/
theorem card_pairwiseDisjoint_additiveCertificateSelectors_le
    {A : Set ℕ} {k r : ℕ} {Q : Finset ℕ} {F : ℕ → Finset ℕ}
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q)
    (selectors : Fin r → BlockSelector F)
    (hpair : Pairwise fun i j =>
      Disjoint (selectedSet (selectors i)) (selectedSet (selectors j))) :
    r ≤ k * Q.card := by
  classical
  have hdestroy : ∀ i : Fin r, ∃ q : {n // n ∈ Q},
      DestroysAt
        (additiveSupportFamily A k) (selectedSet (selectors i)) q.1 := by
    intro i
    obtain ⟨q, hqQ, hq⟩ := hcert (selectors i)
    exact ⟨⟨q, hqQ⟩, hq⟩
  choose target htarget using hdestroy
  let U := finiteSupportChoiceUnion c
  let pick : Fin r → {x // x ∈ U} := fun i =>
    let w := Set.not_disjoint_iff.mp
      (htarget i (c (target i)).1 (c (target i)).2)
    ⟨w.choose,
      finiteSupportChoice_subset_union c (target i) w.choose_spec.1⟩
  have hpick_mem : ∀ i, (pick i).1 ∈ selectedSet (selectors i) := by
    intro i
    change
      (Set.not_disjoint_iff.mp
        (htarget i (c (target i)).1 (c (target i)).2)).choose ∈
          selectedSet (selectors i)
    exact
      (Set.not_disjoint_iff.mp
        (htarget i (c (target i)).1 (c (target i)).2)).choose_spec.2
  have hpick_injective : Function.Injective pick := by
    intro i j hij
    by_contra hne
    have hx : (pick i).1 = (pick j).1 :=
      congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hpair hne)
      (hpick_mem i) (hx ▸ hpick_mem j)
  have hcardU : r ≤ U.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  exact hcardU.trans <|
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A k) c

/- The certificate-selector bound is sharp already at order one.  Partition
`ℕ` into adjacent pairs.  Every selector chooses either `0` or `1` from block
zero, so `{0,1}` is a certificate; the all-even and all-odd selectors are
disjoint and attain `k * |Q| = 2`. -/
private def sharpPairBlocks (i : ℕ) : Finset ℕ :=
  {2 * i, 2 * i + 1}

private theorem sharpPairBlocks_partition :
    IsFiniteBlockPartition (Set.univ : Set ℕ) sharpPairBlocks := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨2 * i, by simp [sharpPairBlocks]⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [sharpPairBlocks, Finset.mem_insert,
      Finset.mem_singleton] at hxi hxj
    rcases hxi with hxi | hxi <;>
      rcases hxj with hxj | hxj <;> omega
  · intro x
    constructor
    · intro _hx
      refine ⟨x / 2, ?_⟩
      simp only [sharpPairBlocks, Finset.mem_insert,
        Finset.mem_singleton]
      have hdecomp := Nat.mod_add_div x 2
      rcases Nat.mod_two_eq_zero_or_one x with hmod | hmod
      · left
        omega
      · right
        omega
    · intro _hx
      exact Set.mem_univ x

private def sharpEvenSelector : BlockSelector sharpPairBlocks := fun i =>
  ⟨2 * i, by simp [sharpPairBlocks]⟩

private def sharpOddSelector : BlockSelector sharpPairBlocks := fun i =>
  ⟨2 * i + 1, by simp [sharpPairBlocks]⟩

private theorem sharpEvenOddSelectors_disjoint :
    Disjoint (selectedSet sharpEvenSelector)
      (selectedSet sharpOddSelector) := by
  rw [Set.disjoint_left]
  rintro x ⟨i, hi⟩ ⟨j, hj⟩
  change 2 * i = x at hi
  change 2 * j + 1 = x at hj
  omega

theorem pairwiseDisjoint_certificateSelector_bound_sharp_univ_one :
    ∃ F : ℕ → Finset ℕ, ∃ Q : Finset ℕ,
      IsFiniteBlockPartition (Set.univ : Set ℕ) F ∧
      Q.card = 2 ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily (Set.univ : Set ℕ) 1)
          (selectedSet s) q) ∧
      ∃ selectors : Fin 2 → BlockSelector F,
        Pairwise fun i j =>
          Disjoint (selectedSet (selectors i))
            (selectedSet (selectors j)) := by
  classical
  let Q : Finset ℕ := {0, 1}
  let selectors : Fin 2 → BlockSelector sharpPairBlocks := fun t =>
    if t.1 = 0 then sharpEvenSelector else sharpOddSelector
  refine ⟨sharpPairBlocks, Q, sharpPairBlocks_partition, by simp [Q], ?_,
    selectors, ?_⟩
  · intro s
    let q := (s 0).1
    have hqQ : q ∈ Q := by
      have hqBlock := (s 0).2
      simp only [sharpPairBlocks, Nat.mul_zero, zero_add,
        Finset.mem_insert, Finset.mem_singleton] at hqBlock
      simpa [Q] using hqBlock
    refine ⟨q, hqQ, ?_⟩
    intro E hER
    obtain ⟨v, _hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    have hv0 : (v 0).1 = q := by simpa [q] using hvsum
    apply Set.not_disjoint_iff.mpr
    exact ⟨q, mem_tupleSupport_iff.mpr ⟨0, hv0⟩, ⟨0, rfl⟩⟩
  · intro t u htu
    fin_cases t <;> fin_cases u
    · exact (htu rfl).elim
    · simpa [selectors] using sharpEvenOddSelectors_disjoint
    · simpa [selectors] using sharpEvenOddSelectors_disjoint.symm
    · exact (htu rfl).elim

/- A finite-block partition has `r` pairwise-disjoint global selectors as
soon as every block has at least `r` vertices.  Choose an `r`-element subset
inside each block and use its finite order equivalence. -/
theorem exists_pairwiseDisjoint_blockSelectors_of_card
    {A : Set ℕ} {F : ℕ → Finset ℕ} {r : ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcard : ∀ i, r ≤ (F i).card) :
    ∃ selectors : Fin r → BlockSelector F,
      Pairwise fun t u =>
        Disjoint (selectedSet (selectors t))
          (selectedSet (selectors u)) := by
  classical
  have hsub : ∀ i, ∃ G : Finset ℕ, G ⊆ F i ∧ G.card = r := by
    intro i
    obtain ⟨G, hGF, hGcard⟩ :=
      Finset.exists_subset_card_eq (hcard i)
    exact ⟨G, hGF, hGcard⟩
  choose G hGF hGcard using hsub
  let e : ∀ i, Fin r ≃ {x // x ∈ G i} := fun i =>
    (Finset.orderIsoOfFin (G i) (hGcard i)).toEquiv
  let selectors : Fin r → BlockSelector F := fun t i =>
    ⟨(e i t).1, hGF i (e i t).2⟩
  refine ⟨selectors, ?_⟩
  intro t u htu
  rw [Set.disjoint_left]
  intro x hxt hxu
  obtain ⟨i, hi⟩ := hxt
  obtain ⟨j, hj⟩ := hxu
  change (selectors t i).1 = x at hi
  change (selectors u j).1 = x at hj
  have hij : i = j := by
    by_contra hij
    exact Finset.disjoint_left.mp (P.disjoint hij)
      (selectors t i).2
      (hi.trans hj.symm ▸ (selectors u j).2)
  subst j
  have heq : (e i t).1 = (e i u).1 := hi.trans hj.symm
  apply htu
  exact (e i).injective (Subtype.ext heq)

/- Consequently a certificate `Q` localizes a concrete obstruction to
building more than `k * |Q|` disjoint selectors: at least one partition block
has at most that many vertices. -/
theorem exists_smallBlock_of_additiveSelectorCertificate
    {A C : Set ℕ} {k : ℕ} {Q : Finset ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition C F)
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q) :
    ∃ i, (F i).card ≤ k * Q.card := by
  by_contra hnone
  have hlarge : ∀ i, k * Q.card + 1 ≤ (F i).card := by
    intro i
    apply Nat.succ_le_iff.mpr
    exact Nat.lt_of_not_ge (fun hi => hnone ⟨i, hi⟩)
  obtain ⟨selectors, hpair⟩ :=
    exists_pairwiseDisjoint_blockSelectors_of_card P hlarge
  have hle := card_pairwiseDisjoint_additiveCertificateSelectors_le
    c hcert selectors hpair
  omega

/- Minimal target localization gives one anchor-overridden extra destroyer
for every `q ∈ Q`.  Counting the predecessor-destroying erasures separately
over their assigned targets improves the bad-erasure bound from
`k * |Q| - 1` to `(k - 1) * |Q|`.  Hence at least `|Q| + 1` dedicated cells
have non-destroying anchor erasures. -/
theorem exists_many_nonDestroyingErasures_of_minimalCertificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} (hQ : Q.Nonempty)
    {𝒞 : Finset (Finset ℕ)} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (additiveSupportFamily A k) (selectedSet base) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A k) (selectedSet base) q')
    (hfamily : IsAnchoredAlignedTranslateCellFamily
      A k Q (Q.max' hQ + 1) 𝒞)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      ∃ target : {C : Finset ℕ // C ∈ 𝒞} → {q // q ∈ Q},
        (∀ C : {C : Finset ℕ // C ∈ 𝒞},
          ∃ T : Finset ℕ, ∃ n,
            C.1 = insert (anchor C) T ∧
            Q.max' hQ + 1 ≤ anchor C ∧ anchor C ∈ A ∧
            n = (target C).1 + anchor C ∧
            DestroysAt
              (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
        ∃ repair : Finset {C : Finset ℕ // C ∈ 𝒞},
          𝒞.card + Q.card ≤ repair.card + k * Q.card ∧
          ∀ C ∈ repair,
            ¬ DestroysAt (additiveSupportFamily A k)
              (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
              (target C).1 := by
  classical
  obtain ⟨anchor, hdata, selectors, hselectors⟩ :=
    exists_targetLocalized_anchorSelectors_of_minimalCertificate
      hQ P hcert hlocalized hfamily locate hlocate hcell
  choose core target successor hCeq haLower haA hnqa hdestroy using hdata
  let destroysPred : {C : Finset ℕ // C ∈ 𝒞} → Prop := fun C =>
    DestroysAt (additiveSupportFamily A k)
      (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
      (target C).1
  let bad := 𝒞.attach.filter destroysPred
  let repair := 𝒞.attach.filter fun C => ¬ destroysPred C
  let eraseCell : {C : Finset ℕ // C ∈ 𝒞} → Finset ℕ := fun C =>
    C.1.erase (anchor C)
  have heraseNonempty : ∀ C : {C // C ∈ bad},
      (eraseCell C.1).Nonempty := by
    intro C
    have hbad : destroysPred C.1 :=
      (Finset.mem_filter.mp C.2).2
    obtain ⟨x, _hxE, hxD⟩ := Set.not_disjoint_iff.mp
      (hbad (c (target C.1)).1 (c (target C.1)).2)
    exact ⟨x, Finset.mem_coe.mp hxD⟩
  have herase_injective : Function.Injective
      (fun C : {C // C ∈ bad} => eraseCell C.1) := by
    intro C D hCD
    apply Subtype.ext
    apply Subtype.ext
    by_contra hcellne
    have hdisj : Disjoint C.1.1 D.1.1 :=
      hfamily.1 C.1.2 D.1.2 hcellne
    obtain ⟨x, hxC⟩ := heraseNonempty C
    have hCD' : eraseCell C.1 = eraseCell D.1 := hCD
    have hxD : x ∈ eraseCell D.1 := by
      rw [← hCD']
      exact hxC
    exact Finset.disjoint_left.mp hdisj
      (Finset.erase_subset (anchor C.1) C.1.1 hxC)
      (Finset.erase_subset (anchor D.1) D.1.1 hxD)
  let 𝒟 : Finset (Finset ℕ) :=
    bad.attach.image fun C => eraseCell C.1
  have h𝒟card : 𝒟.card = bad.card := by
    change
      (bad.attach.image fun C => eraseCell C.1).card = bad.card
    rw [Finset.card_image_iff.mpr herase_injective.injOn,
      Finset.card_attach]
  have h𝒟matching : IsMatching 𝒟 := by
    intro D hD D' hD' hDD'
    obtain ⟨C, hCbad, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨C', hC'bad, rfl⟩ := Finset.mem_image.mp hD'
    have hCC' : C.1.1 ≠ C'.1.1 := by
      intro hEq
      apply hDD'
      have hSubtype : C.1 = C'.1 := Subtype.ext hEq
      exact congrArg eraseCell hSubtype
    exact Disjoint.mono
      (Finset.erase_subset (anchor C.1) C.1.1)
      (Finset.erase_subset (anchor C'.1) C'.1.1)
      (hfamily.1 C.1.2 C'.1.2 hCC')
  have hsource : ∀ D : {D // D ∈ 𝒟},
      ∃ C : {C // C ∈ bad}, eraseCell C.1 = D.1 := by
    intro D
    obtain ⟨C, _hCattach, hCD⟩ := Finset.mem_image.mp D.2
    exact ⟨C, hCD⟩
  choose source hsourceEq using hsource
  let targetD : {D // D ∈ 𝒟} → {q // q ∈ Q} := fun D =>
    target (source D).1
  have h𝒟destroy : ∀ D : {D // D ∈ 𝒟},
      DestroysAt
        (additiveSupportFamily A k) (D.1 : Set ℕ) (targetD D).1 := by
    intro D
    rw [← hsourceEq D]
    exact (Finset.mem_filter.mp (source D).2).2
  let extra : {q // q ∈ Q} → Set ℕ := fun q =>
    selectedSet (selectors q)
  have hextra : ∀ q, DestroysAt
      (additiveSupportFamily A k) (extra q) q.1 := by
    intro q
    exact (hselectors q).1
  have h𝒟disjoint : ∀ D : {D // D ∈ 𝒟},
      Disjoint (D.1 : Set ℕ) (extra (targetD D)) := by
    intro D
    rw [← hsourceEq D]
    exact (hselectors (targetD D)).2.2 (source D).1
  have hbadBound : bad.card + Q.card ≤ k * Q.card := by
    rw [← h𝒟card]
    exact
      card_additiveDestroyers_with_targetwise_disjoint_extras_subtype
        c h𝒟matching targetD h𝒟destroy extra hextra h𝒟disjoint
  have hsplit : bad.card + repair.card = 𝒞.card := by
    simpa [bad, repair, destroysPred] using
      (Finset.card_filter_add_card_filter_not
        (s := 𝒞.attach) destroysPred)
  have hrepair : 𝒞.card + Q.card ≤ repair.card + k * Q.card := by
    omega
  refine ⟨anchor, target, ?_, repair, hrepair, ?_⟩
  · intro C
    exact ⟨core C, successor C,
      hCeq C, haLower C, haA C, hnqa C, hdestroy C⟩
  · intro C hCrepair
    exact (Finset.mem_filter.mp hCrepair).2

/- There are more repair cells than targets, so two distinct repair cells
have the same assigned predecessor target.  This is the finite pigeonhole
form of the localized-certificate gain. -/
theorem exists_commonTarget_pair_nonDestroyingErasures_of_minimalCertificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} (hQ : Q.Nonempty)
    {𝒞 : Finset (Finset ℕ)} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (additiveSupportFamily A k) (selectedSet base) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A k) (selectedSet base) q')
    (hfamily : IsAnchoredAlignedTranslateCellFamily
      A k Q (Q.max' hQ + 1) 𝒞)
    (hcard : k * Q.card + 1 ≤ 𝒞.card)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      ∃ target : {C : Finset ℕ // C ∈ 𝒞} → {q // q ∈ Q},
        (∀ C : {C : Finset ℕ // C ∈ 𝒞},
          ∃ T : Finset ℕ, ∃ n,
            C.1 = insert (anchor C) T ∧
            Q.max' hQ + 1 ≤ anchor C ∧ anchor C ∈ A ∧
            n = (target C).1 + anchor C ∧
            DestroysAt
              (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
        ∃ C D : {C : Finset ℕ // C ∈ 𝒞},
          C ≠ D ∧ target C = target D ∧
          ¬ DestroysAt (additiveSupportFamily A k)
              (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
              (target C).1 ∧
          ¬ DestroysAt (additiveSupportFamily A k)
              (((D.1.erase (anchor D) : Finset ℕ) : Set ℕ))
              (target D).1 := by
  classical
  obtain ⟨anchor, target, hdata, repair, hrepair, hnot⟩ :=
    exists_many_nonDestroyingErasures_of_minimalCertificate
      hQ P hcert hlocalized hfamily locate hlocate hcell c
  have hrepairLarge : Q.card + 1 ≤ repair.card := by omega
  let targetRepair : {C // C ∈ repair} → {q // q ∈ Q} := fun C =>
    target C.1
  have hnotInjective : ¬ Function.Injective targetRepair := by
    intro hinjective
    have hle := Fintype.card_le_of_injective targetRepair hinjective
    rw [Fintype.card_coe repair, Fintype.card_coe Q] at hle
    omega
  obtain ⟨C, D, htarget, hCD⟩ :=
    Function.not_injective_iff.mp hnotInjective
  have hCDrow : C.1 ≠ D.1 := by
    intro hrow
    exact hCD (Subtype.ext hrow)
  refine ⟨anchor, target, hdata, C.1, D.1, hCDrow, htarget, ?_, ?_⟩
  · exact hnot C.1 C.2
  · exact hnot D.1 D.2

/- Doubling the row size upgrades the pigeonhole conclusion from a pair to
more than `k` repair cells with one common predecessor target. -/
theorem exists_commonTarget_many_nonDestroyingErasures_of_minimalCertificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} (hQ : Q.Nonempty)
    {𝒞 : Finset (Finset ℕ)} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt (additiveSupportFamily A k) (selectedSet s) q)
    (hlocalized : ∀ q ∈ Q, ∃ base : BlockSelector F,
      DestroysAt (additiveSupportFamily A k) (selectedSet base) q ∧
      ∀ q' ∈ Q, q' ≠ q →
        ¬ DestroysAt
          (additiveSupportFamily A k) (selectedSet base) q')
    (hfamily : IsAnchoredAlignedTranslateCellFamily
      A k Q (Q.max' hQ + 1) 𝒞)
    (hcard : 𝒞.card = 2 * k * Q.card + 1)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      ∃ target : {C : Finset ℕ // C ∈ 𝒞} → {q // q ∈ Q},
        (∀ C : {C : Finset ℕ // C ∈ 𝒞},
          ∃ T : Finset ℕ, ∃ n,
            C.1 = insert (anchor C) T ∧
            Q.max' hQ + 1 ≤ anchor C ∧ anchor C ∈ A ∧
            n = (target C).1 + anchor C ∧
            DestroysAt
              (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
        ∃ q : {q // q ∈ Q},
          ∃ I : Finset {C : Finset ℕ // C ∈ 𝒞},
            k < I.card ∧
            ∀ C ∈ I, target C = q ∧
              ¬ DestroysAt (additiveSupportFamily A k)
                (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ)) q.1 := by
  classical
  obtain ⟨anchor, target, hdata, repair, hrepair, hnot⟩ :=
    exists_many_nonDestroyingErasures_of_minimalCertificate
      hQ P hcert hlocalized hfamily locate hlocate hcell c
  have hcard' : 𝒞.card =
      k * Q.card + k * Q.card + 1 := by
    simpa [Nat.mul_assoc, two_mul, Nat.add_mul] using hcard
  have hrepairLarge : k * Q.card < repair.card := by omega
  have hlargeFiber : ∃ q ∈ Q,
      k < (repair.filter fun C => (target C).1 = q).card := by
    by_contra hnone
    push Not at hnone
    have hmaps : Set.MapsTo (fun C => (target C).1)
        (repair : Set {C : Finset ℕ // C ∈ 𝒞}) (Q : Set ℕ) := by
      intro C _hC
      exact (target C).2
    have hfibers : repair.card =
        ∑ q ∈ Q,
          (repair.filter fun C => (target C).1 = q).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have hle : repair.card ≤ k * Q.card := by
      rw [hfibers]
      calc
        (∑ q ∈ Q,
            (repair.filter fun C => (target C).1 = q).card) ≤
            ∑ _q ∈ Q, k := by
          gcongr with q hq
          exact hnone q hq
        _ = k * Q.card := by simp [Nat.mul_comm]
    omega
  obtain ⟨q, hqQ, hqLarge⟩ := hlargeFiber
  let I := repair.filter fun C => (target C).1 = q
  let qsub : {q // q ∈ Q} := ⟨q, hqQ⟩
  refine ⟨anchor, target, hdata, qsub, I, hqLarge, ?_⟩
  intro C hCI
  have hCrepair := (Finset.mem_filter.mp hCI).1
  have htargetVal := (Finset.mem_filter.mp hCI).2
  have htarget : target C = qsub := Subtype.ext htargetVal
  exact ⟨htarget, by simpa [htarget] using hnot C hCrepair⟩

/- Quantitative payoff of putting anchors in their cells.  For the selector
which chooses all row anchors, the certificate contributes one destroyer
disjoint from every anchor-erased predecessor destroyer.  Therefore an
oversized row of `k * |Q| + 1` cells has at least two erasures which fail to
destroy their assigned predecessor targets. -/
theorem exists_anchorData_two_nonDestroyingErasures_of_certificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} {L : ℕ}
    {𝒞 : Finset (Finset ℕ)} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt
        (additiveSupportFamily A k) (selectedSet s) q)
    (hfamily : IsAnchoredAlignedTranslateCellFamily A k Q L 𝒞)
    (hcard : k * Q.card + 1 ≤ 𝒞.card)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hlocate : Function.Injective locate)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ anchor : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
      ∃ target : {C : Finset ℕ // C ∈ 𝒞} → {q // q ∈ Q},
        (∀ C : {C : Finset ℕ // C ∈ 𝒞},
          ∃ T : Finset ℕ, ∃ n,
          C.1 = insert (anchor C) T ∧ L ≤ anchor C ∧
          anchor C ∈ A ∧ n = (target C).1 + anchor C ∧
          DestroysAt
            (additiveSupportFamily A (k + 1)) (T : Set ℕ) n) ∧
        ∃ C D : {C : Finset ℕ // C ∈ 𝒞}, C ≠ D ∧
          ¬ DestroysAt
              (additiveSupportFamily A k)
              (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ))
              (target C).1 ∧
          ¬ DestroysAt
              (additiveSupportFamily A k)
              (((D.1.erase (anchor D) : Finset ℕ) : Set ℕ))
              (target D).1 := by
  classical
  obtain ⟨anchor, hdata, s, hselectorDisjoint⟩ :=
    exists_blockSelector_disjoint_anchoredCellErasures
      P hfamily locate hlocate hcell
  choose core target successor hCeq haLower haA hnqa hdestroy using hdata
  let destroysPred : {C : Finset ℕ // C ∈ 𝒞} → Prop := fun C =>
    DestroysAt
      (additiveSupportFamily A k)
      (((C.1.erase (anchor C) : Finset ℕ) : Set ℕ)) (target C).1
  let bad := 𝒞.attach.filter destroysPred
  let repair := 𝒞.attach.filter fun C => ¬ destroysPred C
  let eraseCell : {C : Finset ℕ // C ∈ 𝒞} → Finset ℕ := fun C =>
    C.1.erase (anchor C)
  have heraseNonempty : ∀ C : {C // C ∈ bad},
      (eraseCell C.1).Nonempty := by
    intro C
    have hbad : destroysPred C.1 := (Finset.mem_filter.mp C.2).2
    obtain ⟨x, _hxE, hxD⟩ :=
      Set.not_disjoint_iff.mp
        (hbad (c (target C.1)).1 (c (target C.1)).2)
    exact ⟨x, Finset.mem_coe.mp hxD⟩
  have herase_injective : Function.Injective
      (fun C : {C // C ∈ bad} => eraseCell C.1) := by
    intro C D hCD
    apply Subtype.ext
    apply Subtype.ext
    by_contra hcellne
    have hdisj : Disjoint C.1.1 D.1.1 :=
      hfamily.1 C.1.2 D.1.2 hcellne
    obtain ⟨x, hxC⟩ := heraseNonempty C
    have hCD' : eraseCell C.1 = eraseCell D.1 := hCD
    have hxD : x ∈ eraseCell D.1 := by
      rw [← hCD']
      exact hxC
    exact Finset.disjoint_left.mp hdisj
      (Finset.erase_subset (anchor C.1) C.1.1 hxC)
      (Finset.erase_subset (anchor D.1) D.1.1 hxD)
  let 𝒟 : Finset (Finset ℕ) := bad.attach.image fun C => eraseCell C.1
  have h𝒟card : 𝒟.card = bad.card := by
    change (bad.attach.image fun C => eraseCell C.1).card = bad.card
    rw [Finset.card_image_iff.mpr herase_injective.injOn,
      Finset.card_attach]
  have h𝒟matching : IsMatching 𝒟 := by
    intro D hD D' hD' hDD'
    obtain ⟨C, hCbad, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨C', hC'bad, rfl⟩ := Finset.mem_image.mp hD'
    have hCC' : C.1.1 ≠ C'.1.1 := by
      intro hEq
      apply hDD'
      have hSubtype : C.1 = C'.1 := Subtype.ext hEq
      exact congrArg eraseCell hSubtype
    exact Disjoint.mono
      (Finset.erase_subset (anchor C.1) C.1.1)
      (Finset.erase_subset (anchor C'.1) C'.1.1)
      (hfamily.1 C.1.2 C'.1.2 hCC')
  have h𝒟destroy : ∀ D ∈ 𝒟, ∃ q : {n // n ∈ Q},
      DestroysAt (additiveSupportFamily A k) (D : Set ℕ) q.1 := by
    intro D hD
    obtain ⟨C, hCbad, rfl⟩ := Finset.mem_image.mp hD
    exact ⟨target C.1, (Finset.mem_filter.mp C.2).2⟩
  obtain ⟨qextra, hqextraQ, hextra⟩ := hcert s
  have h𝒟disjoint : ∀ D ∈ 𝒟, Disjoint (D : Set ℕ) (selectedSet s) := by
    intro D hD
    obtain ⟨C, hCbad, rfl⟩ := Finset.mem_image.mp hD
    exact hselectorDisjoint C.1
  have hbadBound : bad.card + 1 ≤ k * Q.card := by
    rw [← h𝒟card]
    exact card_pairwiseDisjoint_additiveDestroyers_with_disjoint_extra_le
      c h𝒟matching h𝒟destroy ⟨⟨qextra, hqextraQ⟩, hextra⟩ h𝒟disjoint
  have hsplit : bad.card + repair.card = 𝒞.card := by
    simpa [bad, repair, destroysPred] using
      (Finset.card_filter_add_card_filter_not
        (s := 𝒞.attach) destroysPred)
  have hrepair : 2 ≤ repair.card := by omega
  refine ⟨anchor, target, ?_, ?_⟩
  · intro C
    exact ⟨core C, successor C,
      hCeq C, haLower C, haA C, hnqa C, hdestroy C⟩
  · obtain ⟨C, hCrepair, D, hDrepair, hCD⟩ :=
      Finset.one_lt_card.mp (show 1 < repair.card by omega)
    refine ⟨C, D, hCD, ?_, ?_⟩
    · exact (Finset.mem_filter.mp hCrepair).2
    · exact (Finset.mem_filter.mp hDrepair).2

/-- Surviving support is equivalent to an actual exact tuple representation
whose entries avoid the deleted set. -/
theorem exists_surviving_additiveSupport_iff
    {A B : Set ℕ} {h n : ℕ} :
    (∃ E ∈ additiveSupportFamily A h n,
        Disjoint (E : Set ℕ) B) ↔
      ∃ v : Fin h → ℕ,
        (∀ i, v i ∈ A \ B) ∧
        ∑ i, v i = n := by
  constructor
  · rintro ⟨E, hER, hdisj⟩
    obtain ⟨v, hvA, hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp hER
    refine ⟨fun i => (v i).1, ?_, hvsum⟩
    intro i
    refine ⟨hvA i, ?_⟩
    intro hviB
    apply Set.disjoint_left.mp hdisj
      (mem_tupleSupport_iff.mpr ⟨i, rfl⟩) hviB
  · rintro ⟨v, hvAB, hvsum⟩
    have hvle : ∀ i, v i ≤ n := by
      intro i
      rw [← hvsum]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    let w : Fin h → Fin (n + 1) :=
      fun i => ⟨v i, Nat.lt_succ_of_le (hvle i)⟩
    refine ⟨tupleSupport w, ?_, ?_⟩
    · apply mem_additiveSupportFamily_iff.mpr
      refine ⟨w, ?_, ?_, rfl⟩
      · intro i
        exact (hvAB i).1
      · simpa [w] using hvsum
    · rw [Set.disjoint_left]
      intro x hxw hxB
      obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxw
      apply (hvAB i).2
      have hi' : v i = x := by simpa [w] using hi
      rw [hi']
      exact hxB

theorem destroysAt_additiveSupportFamily_iff
    {A B : Set ℕ} {h n : ℕ} :
    DestroysAt (additiveSupportFamily A h) B n ↔
      ¬ ∃ v : Fin h → ℕ,
        (∀ i, v i ∈ A \ B) ∧
        ∑ i, v i = n := by
  constructor
  · intro hdestroy htuple
    have hsurvive :=
      exists_surviving_additiveSupport_iff.mpr htuple
    exact (not_destroysAt_iff.mpr hsurvive) hdestroy
  · intro hnotuple
    by_contra hnotdestroy
    have hsurvive := not_destroysAt_iff.mp hnotdestroy
    exact hnotuple (exists_surviving_additiveSupport_iff.mp hsurvive)

/-- The support-hypergraph strong deletion condition is precisely the usual
quantifier statement for exact additive tuples. -/
theorem strongInfiniteDeletion_additiveSupportFamily_iff
    {A : Set ℕ} {h : ℕ} :
    StrongInfiniteDeletion (additiveSupportFamily A h) A ↔
      ∀ B, B ⊆ A → B.Infinite →
        ∀ N, ∃ n, N ≤ n ∧
          ¬ ∃ v : Fin h → ℕ,
            (∀ i, v i ∈ A \ B) ∧
            ∑ i, v i = n := by
  simp only [StrongInfiniteDeletion,
    destroysAt_additiveSupportFamily_iff]

/-- Exact asymptotic basis, expressed with fixed-length tuples.  This is the
form naturally matched by `additiveSupportFamily`. -/
def IsExactTupleAsymptoticBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n →
    ∃ v : Fin h → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = n

/-- Every finite deletion preserves the exact order-`h` basis property.  This
is the finite half of the classical `ℵ₀`-minimal basis condition. -/
def IsFiniteDeletionStableExactBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∀ D : Finset ℕ,
    IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) h

/-- Failure after deleting a finite set is exactly arbitrarily late
destruction by that set in the original support family. -/
theorem not_exactTupleAsymptoticBasis_diff_finset_iff
    {A : Set ℕ} {h : ℕ} {D : Finset ℕ} :
    ¬ IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) h ↔
      ∀ N, ∃ n, N ≤ n ∧
        DestroysAt
          (additiveSupportFamily A h) (D : Set ℕ) n := by
  constructor
  · intro hnot N
    simp only [IsExactTupleAsymptoticBasis,
      not_exists, not_forall] at hnot
    obtain ⟨n, hn, hnrep⟩ := hnot N
    refine ⟨n, hn, ?_⟩
    rw [destroysAt_additiveSupportFamily_iff]
    rintro ⟨v, hv⟩
    exact hnrep v hv
  · intro hlate hbasis
    obtain ⟨N, hN⟩ := hbasis
    obtain ⟨n, hn, hdestroy⟩ := hlate N
    rw [destroysAt_additiveSupportFamily_iff] at hdestroy
    exact hdestroy (hN n hn)

/- Exact tuple representability eventually along a prescribed target set. -/
def IsExactTupleAsymptoticBasisAlong
    (A : Set ℕ) (h : ℕ) (S : Set ℕ) : Prop :=
  ∃ N, ∀ n, N ≤ n → n ∈ S →
    ∃ v : Fin h → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = n

/- Along-set representability is an ordinary asymptotic basis whenever the
target set itself is eventually all naturals. -/
theorem IsExactTupleAsymptoticBasisAlong.of_eventually_mem
    {A S : Set ℕ} {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasisAlong A h S)
    (hS : ∃ M, ∀ n, M ≤ n → n ∈ S) :
    IsExactTupleAsymptoticBasis A h := by
  obtain ⟨N, hN⟩ := hbasis
  obtain ⟨M, hM⟩ := hS
  refine ⟨max N M, ?_⟩
  intro n hn
  exact hN n (le_trans (le_max_left N M) hn)
    (hM n (le_trans (le_max_right N M) hn))

/-- The tuple formulation agrees with the original list-based definition of
an exact asymptotic basis. -/
theorem isAsymptoticBasis_iff_exactTuple
    {A : Set ℕ} {h : ℕ} :
    IsAsymptoticBasis A h ↔
      IsExactTupleAsymptoticBasis A h := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨xs, hlen, hmem, hsum⟩ := hN n hn
    let w : List.Vector ℕ h := ⟨xs, hlen⟩
    let v : Fin h → ℕ := List.Vector.get w
    have hlist : List.ofFn v = xs := by
      calc
        List.ofFn v =
            List.Vector.toList (List.Vector.ofFn v) :=
          (List.Vector.toList_ofFn v).symm
        _ = List.Vector.toList w :=
          congrArg List.Vector.toList (List.Vector.ofFn_get w)
        _ = xs := rfl
    refine ⟨v, ?_, ?_⟩
    · intro i
      apply hmem (v i)
      rw [← hlist]
      simp
    · calc
        ∑ i, v i = (List.ofFn v).sum := by
          simp [List.sum_ofFn]
        _ = xs.sum := congrArg List.sum hlist
        _ = n := hsum
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨v, hvA, hvsum⟩ := hN n hn
    refine ⟨List.ofFn v, ?_, ?_, ?_⟩
    · simp
    · intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hvA i
    · simpa [List.sum_ofFn] using hvsum

/- Ordinary minimality supplies arbitrarily late singleton destruction
witnesses in the support-hypergraph formulation. -/
theorem singletonDestruction_of_ordinarilyMinimal
    {A : Set ℕ} {h : ℕ}
    (hminimal : IsOrdinarilyMinimal A h) :
    HasArbitrarilyLateSingletonDestruction
      (additiveSupportFamily A h) A := by
  intro a haA N
  obtain ⟨n, hn, hprivate⟩ :=
    (ordinarilyMinimal_iff_privateWitnesses.mp hminimal).2 a haA N
  refine ⟨n, hn, ?_⟩
  rw [destroysAt_additiveSupportFamily_iff]
  intro htuple
  apply hprivate.2
  obtain ⟨v, hv, hvsum⟩ := htuple
  refine ⟨List.ofFn v, by simp, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hv i
  · simpa [List.sum_ofFn] using hvsum

/- Cofinitely many vertices with private order-`h` witnesses already prevent
every infinite deletion from preserving an exact order-`h` basis.  A finite
exceptional set may contain arbitrary "booster" vertices. -/
theorem noInfiniteDeletionPreservesExactBasis_of_cofiniteSingletonDestruction
    {A : Set ℕ} {h : ℕ}
    (hsingle : HasCofiniteSingletonDestruction
      (additiveSupportFamily A h) A) :
    ∀ B, B ⊆ A → B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) h := by
  have hstrong :=
    strongInfiniteDeletion_of_cofiniteSingletonDestruction hsingle
  intro B hBA hB hbasis
  obtain ⟨N, hN⟩ := hbasis
  obtain ⟨n, hn, hdestroy⟩ := hstrong B hBA hB N
  rw [destroysAt_additiveSupportFamily_iff] at hdestroy
  exact hdestroy (hN n hn)

/- Consequently the finite certificates available for an ordinarily minimal
exact basis may always be chosen to depend on block zero alone. -/
theorem ordinarilyMinimal_has_localizedFiniteBlockCertificates
    {A : Set ℕ} {h : ℕ}
    (hminimal : IsOrdinarilyMinimal A h) :
    FiniteBlockCertificateProperty (additiveSupportFamily A h) A :=
  finiteBlockCertificates_localized_of_singletonDestruction
    (singletonDestruction_of_ordinarilyMinimal hminimal)

/-- An exact basis of order one is simply a cofinite subset of the naturals. -/
theorem exactTupleAsymptoticBasis_one_iff
    {A : Set ℕ} :
    IsExactTupleAsymptoticBasis A 1 ↔
      ∃ N, ∀ n, N ≤ n → n ∈ A := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨v, hvA, hvsum⟩ := hN n hn
    have hv0 : v 0 = n := by simpa using hvsum
    exact hv0 ▸ hvA 0
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    let v : Fin 1 → ℕ := fun _ => n
    refine ⟨v, ?_, ?_⟩
    · intro i
      exact hN n hn
    · simp [v]

/-- A cofinite set has arbitrarily large matchings of complementary
two-term representation supports. -/
theorem outsideMatchingTendsToInfinity_pair_of_eventually_mem
    {A : Set ℕ}
    (hcofinite : ∃ L, ∀ n, L ≤ n → n ∈ A) :
    OutsideMatchingTendsToInfinity
      (additiveSupportFamily A 2) ∅ := by
  classical
  obtain ⟨L, hL⟩ := hcofinite
  intro j
  refine ⟨2 * (L + j + 1), ?_⟩
  intro n hn
  let edge : ℕ → Finset ℕ :=
    fun i => pairSupport n (L + i)
  let I : Finset ℕ := Finset.range (j + 1)
  let M : Finset (Finset ℕ) := I.image edge
  have hedge_disjoint :
      ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' →
        Disjoint (edge i) (edge i') := by
    intro i hi i' hi' hii'
    have hi_le : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hi'_le : i' ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [edge, pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hx hx'
    rcases hx with (rfl | rfl) <;>
      rcases hx' with (h | h) <;> omega
  have hedge_injective : Set.InjOn edge I := by
    intro i hi i' hi' heq
    by_contra hii'
    have hdisj := hedge_disjoint i hi i' hi' hii'
    have hmem : L + i ∈ edge i := by
      simp [edge, pairSupport]
    have hmem' : L + i ∈ edge i' := by
      rw [← heq]
      exact hmem
    exact (Finset.disjoint_left.mp hdisj) hmem hmem'
  have hMcard : M.card = j + 1 := by
    change (I.image edge).card = j + 1
    rw [Finset.card_image_iff.mpr hedge_injective]
    simp [I]
  have hMsub :
      M ⊆ outsideSupportHypergraph
        (additiveSupportFamily A 2) ∅ n := by
    intro E hEM
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hEM
    have hi_le : i ≤ j :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hai_le : L + i ≤ n := by omega
    have hbi_ge : L ≤ n - (L + i) := by omega
    have hER :
        edge i ∈ additiveSupportFamily A 2 n := by
      apply pairSupport_mem_additiveSupportFamily
      · exact hai_le
      · exact hL (L + i) (by omega)
      · exact hL (n - (L + i)) hbi_ge
    apply Finset.mem_erase.mpr
    refine ⟨?_, ?_⟩
    · simp [edge, pairSupport]
    · apply Finset.mem_image.mpr
      exact ⟨edge i, hER, by simp⟩
  have hMmatching : IsMatching M := by
    intro E hEM E' hE'M hEE'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hEM
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hE'M
    apply hedge_disjoint i hi i' hi'
    intro hii'
    subst i'
    exact hEE' rfl
  calc
    j < j + 1 := Nat.lt_succ_self j
    _ = M.card := hMcard.symm
    _ ≤ matchingNumber
        (outsideSupportHypergraph
          (additiveSupportFamily A 2) ∅ n) :=
      card_le_matchingNumber hMsub hMmatching

/-- Surviving supports after deleting `B` are precisely exact tuple
representations by `A \ B`. -/
theorem hasEventuallySurvivingSupport_additive_iff
    {A B : Set ℕ} {h : ℕ} :
    HasEventuallySurvivingSupport (additiveSupportFamily A h) B ↔
      IsExactTupleAsymptoticBasis (A \ B) h := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨v, hv, hvsum⟩ :=
      exists_surviving_additiveSupport_iff.mp (hN n hn)
    exact ⟨v, hv, hvsum⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨v, hvAB, hvsum⟩ := hN n hn
    apply exists_surviving_additiveSupport_iff.mpr
    exact ⟨v, hvAB, hvsum⟩

/- Relative version of the support/tuple equivalence. -/
theorem hasEventuallySurvivingSupportAlong_additive_iff
    {A B S : Set ℕ} {h : ℕ} :
    HasEventuallySurvivingSupportAlong
        (additiveSupportFamily A h) B S ↔
      IsExactTupleAsymptoticBasisAlong (A \ B) h S := by
  constructor
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn hnS
    obtain ⟨v, hv, hvsum⟩ :=
      exists_surviving_additiveSupport_iff.mp (hN n hn hnS)
    exact ⟨v, hv, hvsum⟩
  · rintro ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn hnS
    obtain ⟨v, hvAB, hvsum⟩ := hN n hn hnS
    apply exists_surviving_additiveSupport_iff.mpr
    exact ⟨v, hvAB, hvsum⟩

/-- Eventual nonemptiness of the additive support hypergraphs is precisely
the exact tuple formulation of being an asymptotic basis. -/
theorem hasEventuallySurvivingSupport_empty_additive_iff
    {A : Set ℕ} {h : ℕ} :
    HasEventuallySurvivingSupport (additiveSupportFamily A h) ∅ ↔
      IsExactTupleAsymptoticBasis A h := by
  simpa using
    (hasEventuallySurvivingSupport_additive_iff
      (A := A) (B := (∅ : Set ℕ)) (h := h))

/-- An exact asymptotic basis is necessarily infinite. -/
theorem IsExactTupleAsymptoticBasis.infinite
    {A : Set ℕ} {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h) :
    A.Infinite := by
  by_contra hnot
  have hAfin : A.Finite := Set.not_infinite.mp hnot
  obtain ⟨U, hU⟩ := hAfin.bddAbove
  obtain ⟨N, hN⟩ := hbasis
  let n := max N (h * U + 1)
  obtain ⟨v, hvA, hvsum⟩ :=
    hN n (le_max_left N (h * U + 1))
  have hsumle : ∑ i, v i ≤ ∑ _i : Fin h, U := by
    apply Finset.sum_le_sum
    intro i hi
    exact hU (hvA i)
  have hnle : n ≤ h * U := by
    rw [hvsum] at hsumle
    simpa using hsumle
  have hlt : h * U < n :=
    lt_of_lt_of_le (Nat.lt_succ_self (h * U))
      (le_max_right N (h * U + 1))
  exact (not_lt_of_ge hnle) hlt

/-- With repetitions allowed, an exact asymptotic basis of order `h` is also
an exact asymptotic basis of order `h + 1`: append one fixed element of `A`
and translate the target. -/
theorem IsExactTupleAsymptoticBasis.succ
    {A : Set ℕ} {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h) :
    IsExactTupleAsymptoticBasis A (h + 1) := by
  obtain ⟨a, haA⟩ := hbasis.infinite.nonempty
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N + a, ?_⟩
  intro n hn
  have han : a ≤ n := by omega
  have hNsub : N ≤ n - a := by omega
  obtain ⟨v, hvA, hvsum⟩ := hN (n - a) hNsub
  let w : Fin (h + 1) → ℕ := Fin.cons a v
  refine ⟨w, ?_, ?_⟩
  · intro i
    refine Fin.cases haA (fun j => ?_) i
    exact hvA j
  · rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    rw [hvsum]
    exact Nat.add_sub_of_le han

/- Cofinitely many private witnesses at order `k + 1` imply strong infinite
deletion at the preceding order.  If a deletion left an exact order-`k`
basis, the preceding padding theorem would leave an exact order-`k + 1`
basis, contradicting one of the arbitrarily late private witnesses. -/
theorem strongInfiniteDeletion_predecessor_of_cofiniteSingletonDestruction
    {A : Set ℕ} {k : ℕ}
    (hsingle : HasCofiniteSingletonDestruction
      (additiveSupportFamily A (k + 1)) A) :
    StrongInfiniteDeletion (additiveSupportFamily A k) A := by
  have hnoSucc :=
    noInfiniteDeletionPreservesExactBasis_of_cofiniteSingletonDestruction
      hsingle
  rw [strongInfiniteDeletion_additiveSupportFamily_iff]
  intro B hBA hB N
  have hnot : ¬ IsExactTupleAsymptoticBasis (A \ B) k := by
    intro hbasis
    exact hnoSucc B hBA hB hbasis.succ
  simp only [IsExactTupleAsymptoticBasis,
    not_exists, not_forall] at hnot
  obtain ⟨n, hn, hnrep⟩ := hnot N
  refine ⟨n, hn, ?_⟩
  rintro ⟨v, hv⟩
  exact hnrep v hv

/-- Consequently an exact asymptotic basis remains unbounded after any finite
set is excluded. -/
theorem IsExactTupleAsymptoticBasis.unboundedOutside
    {A : Set ℕ} {h : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A h)
    (F : Finset ℕ) :
    ∀ T, ∃ b ∈ A, b ∉ F ∧ T ≤ b := by
  intro T
  have hinfinite : (A \ (F : Set ℕ)).Infinite :=
    hbasis.infinite.diff F.finite_toSet
  obtain ⟨b, hb, hTb⟩ := hinfinite.exists_gt T
  exact ⟨b, hb.1, by simpa using hb.2, hTb.le⟩

/- Eventually, a finite target set `Q` supports at most `k * |Q|`
pairwise-disjoint deletion sets when each is assigned some target it
destroys. -/
theorem IsExactTupleAsymptoticBasis.eventually_card_disjointDestroyers_over_targets_le
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ Q : Finset ℕ, (∀ q ∈ Q, N ≤ q) →
      ∀ 𝒯 : Finset (Finset ℕ), IsMatching 𝒯 →
        (∀ T ∈ 𝒯, ∃ q : {n // n ∈ Q},
          DestroysAt (additiveSupportFamily A k) (T : Set ℕ) q.1) →
        𝒯.card ≤ k * Q.card := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro Q hQN 𝒯 hpair hdestroy
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q =>
      let w := hN q.1 (hQN q.1 q.2)
      ⟨w.choose, w.choose_spec.1⟩
  exact card_pairwiseDisjoint_additiveDestroyers_over_finiteTargets_le
    c hpair hdestroy

/- Reservoir-relative two repairs suffice for an infinite deletion from an
arbitrary unbounded reservoir `C ⊆ A`.  The repairs may share retained
vertices in `A \ C`; only their intersections with `C` must be disjoint. -/
theorem exists_infiniteDeletion_succBasisAlong_of_twoRepairsDisjointOnReservoir
    {A C S : Set ℕ} {k : ℕ}
    (hCunbounded : ∀ T, ∃ b ∈ C, T ≤ b)
    (hrepairs : HasTwoRepairsDisjointOnDeletionReservoirAlong
      (additiveSupportFamily A (k + 1)) C S) :
    ∃ B, B ⊆ C ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasisAlong (A \ B) (k + 1) S := by
  obtain ⟨B, hBC, hB, hsurvive⟩ :=
    sparseDeletion_of_twoRepairsDisjointOnDeletionReservoirAlong
      (C := C) (S := S)
      (R := additiveSupportFamily A (k + 1))
      (additiveSupportFamily_supportsBounded A (k + 1))
      hrepairs hCunbounded
  exact ⟨B, hBC, hB,
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive⟩

/- Global reservoir-relative form when the prescribed target set contains a
tail. -/
theorem exists_infiniteDeletion_succBasis_of_twoRepairsDisjointOnReservoir
    {A C S : Set ℕ} {k : ℕ}
    (hCunbounded : ∀ T, ∃ b ∈ C, T ≤ b)
    (hrepairs : HasTwoRepairsDisjointOnDeletionReservoirAlong
      (additiveSupportFamily A (k + 1)) C S)
    (hcofinite : ∃ N, ∀ n, N ≤ n → n ∈ S) :
    ∃ B, B ⊆ C ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBC, hB, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_of_twoRepairsDisjointOnReservoir
      hCunbounded hrepairs
  exact ⟨B, hBC, hB, halong.of_eventually_mem hcofinite⟩

/- Finite retained-core form.  If the reservoir-relative two-repair property
holds on `A \ F`, then the infinite deletion can be chosen to avoid `F`
entirely. -/
theorem exists_infiniteDeletion_succBasis_of_finiteRetainedCore_twoRepairs
    {A S : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (F : Finset ℕ)
    (hrepairs : HasTwoRepairsDisjointOnDeletionReservoirAlong
      (additiveSupportFamily A (k + 1)) (A \ (F : Set ℕ)) S)
    (hcofinite : ∃ N, ∀ n, N ≤ n → n ∈ S) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  have hreservoirUnbounded :
      ∀ T, ∃ b ∈ A \ (F : Set ℕ), T ≤ b := by
    intro T
    obtain ⟨b, hbA, hbF, hbT⟩ := hbasis.unboundedOutside F T
    exact ⟨b, ⟨hbA, by simpa using hbF⟩, hbT⟩
  obtain ⟨B, hBreservoir, hB, hsucc⟩ :=
    exists_infiniteDeletion_succBasis_of_twoRepairsDisjointOnReservoir
      (C := A \ (F : Set ℕ))
      hreservoirUnbounded hrepairs hcofinite
  refine ⟨B, fun x hx => (hBreservoir hx).1, hB, ?_, hsucc⟩
  exact Set.disjoint_left.mpr fun x hxB hxF =>
    (hBreservoir hxB).2 hxF

/- The finite-core absorption property which would close the two-repair
route: after retaining one finite subset of `A`, the exact
reservoir-relative repair condition holds on everything left available for
deletion. -/
def HasFiniteRetainedCoreTwoRepairsAlong
    (A : Set ℕ) (k : ℕ) (S : Set ℕ) : Prop :=
  ∃ F : Finset ℕ,
    HasTwoRepairsDisjointOnDeletionReservoirAlong
      (additiveSupportFamily A (k + 1)) (A \ (F : Set ℕ)) S

theorem HasFiniteRetainedCoreTwoRepairsAlong.of_eventually_mem
    {A S : Set ℕ} {k : ℕ}
    (hcore : HasFiniteRetainedCoreTwoRepairsAlong A k S)
    (hS : ∃ M, ∀ n, M ≤ n → n ∈ S) :
    HasFiniteRetainedCoreTwoRepairsAlong A k Set.univ := by
  obtain ⟨F, hrepairs⟩ := hcore
  exact ⟨F, hrepairs.of_eventually_mem hS⟩

theorem not_hasFiniteRetainedCoreTwoRepairsAlong_of_global_failure
    {A S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasFiniteRetainedCoreTwoRepairsAlong A k Set.univ)
    (hS : ∃ M, ∀ n, M ≤ n → n ∈ S) :
    ¬ HasFiniteRetainedCoreTwoRepairsAlong A k S := by
  intro hcore
  exact hnot (hcore.of_eventually_mem hS)

/- Once finite-core absorption is established, the desired infinite
successor-order deletion follows immediately. -/
theorem exists_infiniteDeletion_succBasis_of_finiteRetainedCoreTwoRepairs
    {A S : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcore : HasFiniteRetainedCoreTwoRepairsAlong A k S)
    (hcofinite : ∃ N, ∀ n, N ≤ n → n ∈ S) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨F, hrepairs⟩ := hcore
  obtain ⟨B, hBA, hB, _hBF, hsucc⟩ :=
    exists_infiniteDeletion_succBasis_of_finiteRetainedCore_twoRepairs
      hbasis F hrepairs hcofinite
  exact ⟨B, hBA, hB, hsucc⟩

theorem not_hasFiniteRetainedCoreTwoRepairsAlong_iff
    {A S : Set ℕ} {k : ℕ} :
    ¬ HasFiniteRetainedCoreTwoRepairsAlong A k S ↔
      ∀ F : Finset ℕ,
        ¬ HasTwoRepairsDisjointOnDeletionReservoirAlong
          (additiveSupportFamily A (k + 1))
          (A \ (F : Set ℕ)) S := by
  simp [HasFiniteRetainedCoreTwoRepairsAlong]

/- Two disjoint successor repairs after every finite prefix suffice for an
infinite deletion preserving the successor basis along `S`. -/
theorem exists_infiniteDeletion_succBasisAlong_of_twoDisjointRepairs
    {A S : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hrepairs : HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
      (additiveSupportFamily A (k + 1)) A S) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasisAlong (A \ B) (k + 1) S := by
  have hAunbounded : ∀ T, ∃ b ∈ A, T ≤ b := by
    intro T
    obtain ⟨b, hbA, _hbEmpty, hbT⟩ := hbasis.unboundedOutside ∅ T
    exact ⟨b, hbA, hbT⟩
  obtain ⟨B, hBA, hB, hsurvive⟩ :=
    sparseDeletion_of_twoDisjointRepairsAvoidingFinitePrefixesAlong
      (C := A) (S := S)
      (R := additiveSupportFamily A (k + 1))
      (additiveSupportFamily_supportsBounded A (k + 1))
      hrepairs hAunbounded
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive⟩

/- The global form when the target set covers a tail. -/
theorem exists_infiniteDeletion_succBasis_of_twoDisjointRepairs
    {A S : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hrepairs : HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
      (additiveSupportFamily A (k + 1)) A S)
    (hcofinite : ∃ N, ∀ n, N ≤ n → n ∈ S) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hB, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_of_twoDisjointRepairs
      hbasis hrepairs
  exact ⟨B, hBA, hB, halong.of_eventually_mem hcofinite⟩

/- Exact complementary obstruction to the two-repair route.  One fixed
finite prefix `D` recurs, and at every bad target it can be extended by a
moving set of at most `k+1` vertices to destroy all successor supports. -/
theorem exists_recurrentBoundedPrefixExtension_of_not_twoDisjointRepairs
    {A S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
      (additiveSupportFamily A (k + 1)) A S) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ A ∧
      ∀ N, ∃ n T,
        N ≤ n ∧ n ∈ S ∧
        (∀ x ∈ T, x ∈ A) ∧ Disjoint T D ∧
        T.card ≤ k + 1 ∧
        DestroysAt (additiveSupportFamily A (k + 1))
          (((D ∪ T : Finset ℕ) : Set ℕ)) n := by
  obtain ⟨D, hDA, hbad⟩ :=
    not_hasTwoDisjointRepairsAvoidingFinitePrefixesAlong_iff.mp hnot
  refine ⟨D, hDA, ?_⟩
  intro N
  obtain ⟨n, hn, hnS, hno⟩ := hbad N
  obtain ⟨T, hTA, hTD, hTcard, hdestroy⟩ :=
    exists_bounded_extensionTransversal_of_no_twoDisjointRepairs
      (A := A) (R := additiveSupportFamily A (k + 1))
      (D := D) (n := n) (r := k + 1)
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1)) hno
  exact ⟨n, T, hn, hnS, hTA, hTD, hTcard, hdestroy⟩

/- Protected recursive form of the two-repair obstruction.  The same fixed
prefix `D` works after protecting any additional finite set `F`: arbitrarily
late, either the accumulated set `D ∪ F` already destroys the target, or a
single successor support `T`, disjoint from all of `D ∪ F`, extends `D` to
a destroyer. -/
theorem exists_recurrentProtectedExtensionDichotomy_of_not_twoDisjointRepairs
    {A S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
      (additiveSupportFamily A (k + 1)) A S) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ A ∧
      ∀ F : Finset ℕ, ∀ N, ∃ n,
        N ≤ n ∧ n ∈ S ∧
          (DestroysAt (additiveSupportFamily A (k + 1))
              ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
            ∃ T : Finset ℕ,
              T ∈ additiveSupportFamily A (k + 1) n ∧
                (∀ x ∈ T, x ∈ A) ∧ Disjoint T (D ∪ F) ∧
                T.card ≤ k + 1 ∧
                DestroysAt (additiveSupportFamily A (k + 1))
                  (((D ∪ T : Finset ℕ) : Set ℕ)) n) := by
  obtain ⟨D, hDA, hbad⟩ :=
    not_hasTwoDisjointRepairsAvoidingFinitePrefixesAlong_iff.mp hnot
  refine ⟨D, hDA, ?_⟩
  intro F N
  obtain ⟨n, hn, hnS, hno⟩ := hbad N
  have hdichotomy :=
    destroysAt_union_or_exists_protectedBoundedExtension_of_no_twoDisjointRepairs
      (A := A) (R := additiveSupportFamily A (k + 1))
      (D := D) (F := F) (n := n) (r := k + 1)
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1)) hno
  exact ⟨n, hn, hnS, hdichotomy⟩

/- Iterated finite normal form of the same obstruction.  For every requested
depth `r`, either `r` pairwise-disjoint successor supports have been built,
each becoming a destroyer after adjoining the same prefix `D`, or the
iteration stops at a smaller matching because `D` together with everything
built so far already destroys a late successor target. -/
theorem exists_recursiveExtensionFamily_or_accumulatedDestroyer_of_not_twoDisjointRepairs
    {A S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
      (additiveSupportFamily A (k + 1)) A S) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ A ∧
      ∀ r N, ∃ 𝒯 : Finset (Finset ℕ),
        IsProtectedBoundedExtensionFamily
          (additiveSupportFamily A (k + 1)) A S D (k + 1) N 𝒯 ∧
          (𝒯.card = r ∨
            (𝒯.card < r ∧ ∃ n,
              N ≤ n ∧ n ∈ S ∧
                DestroysAt (additiveSupportFamily A (k + 1))
                  (((D ∪ 𝒯.biUnion id : Finset ℕ) : Set ℕ)) n)) := by
  obtain ⟨D, hDA, hrecur⟩ :=
    exists_recurrentProtectedExtensionDichotomy_of_not_twoDisjointRepairs
      hnot
  refine ⟨D, hDA, ?_⟩
  exact
    exists_protectedBoundedExtensionFamily_or_accumulatedDestroyer
      (additiveSupportFamily_supportsNonempty A (by omega)) hrecur

/- Exact failure branch for the reservoir-relative criterion.  The fixed
prefix lies inside the deletion reservoir, and every moving extension can
also be chosen entirely inside that reservoir.  Vertices retained outside
`C` never enter the moving transversal. -/
theorem exists_recurrentBoundedReservoirExtension_of_not_twoRepairs
    {A C S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasTwoRepairsDisjointOnDeletionReservoirAlong
      (additiveSupportFamily A (k + 1)) C S) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ C ∧
      ∀ F : Finset ℕ, ∀ N, ∃ n,
        N ≤ n ∧ n ∈ S ∧
          (DestroysAt (additiveSupportFamily A (k + 1))
              ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
            ∃ T : Finset ℕ,
              (∀ x ∈ T, x ∈ A ∧ x ∈ C) ∧
                Disjoint T (D ∪ F) ∧ T.Nonempty ∧
                T.card ≤ k + 1 ∧
                DestroysAt (additiveSupportFamily A (k + 1))
                  (((D ∪ T : Finset ℕ) : Set ℕ)) n) := by
  obtain ⟨D, hDC, hbad⟩ :=
    not_hasTwoRepairsDisjointOnDeletionReservoirAlong_iff.mp hnot
  refine ⟨D, hDC, ?_⟩
  intro F N
  obtain ⟨n, hn, hnS, hno⟩ := hbad N
  have hdichotomy :=
    destroysAt_union_or_exists_protectedBoundedReservoirExtension_of_no_twoRepairs
      (A := A) (C := C) (R := additiveSupportFamily A (k + 1))
      (D := D) (F := F) (n := n) (r := k + 1)
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1)) hno
  exact ⟨n, hn, hnS, hdichotomy⟩

/- Exact negation of finite-core absorption, expressed as recurrent data.
No matter which finite core `F₀` is retained, a new finite prefix appears in
the remaining reservoir and gives the protected bounded-extension
dichotomy arbitrarily late. -/
theorem recurrentReservoirExtensions_of_noFiniteRetainedCoreTwoRepairs
    {A S : Set ℕ} {k : ℕ}
    (hnot : ¬ HasFiniteRetainedCoreTwoRepairsAlong A k S) :
    ∀ F₀ : Finset ℕ,
      ∃ D : Finset ℕ, (D : Set ℕ) ⊆ A \ (F₀ : Set ℕ) ∧
        ∀ F : Finset ℕ, ∀ N, ∃ n,
          N ≤ n ∧ n ∈ S ∧
            (DestroysAt (additiveSupportFamily A (k + 1))
                ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
              ∃ T : Finset ℕ,
                (∀ x ∈ T, x ∈ A ∧ x ∈ A \ (F₀ : Set ℕ)) ∧
                  Disjoint T (D ∪ F) ∧ T.Nonempty ∧
                  T.card ≤ k + 1 ∧
                  DestroysAt (additiveSupportFamily A (k + 1))
                    (((D ∪ T : Finset ℕ) : Set ℕ)) n) := by
  intro F₀
  apply exists_recurrentBoundedReservoirExtension_of_not_twoRepairs
  exact (not_hasFiniteRetainedCoreTwoRepairsAlong_iff.mp hnot) F₀

/- Failure after every finite retained core produces a genuinely fresh full
successor destroyer.  Retain the arbitrary protected set `F₀`, take the
recurrent obstruction in its complement, and invoke its inner dichotomy with
no additional protected vertices.  The resulting `D` or `D ∪ T` is wholly
outside `F₀`; eventual successor representability rules out an empty
destroyer. -/
theorem exists_freshFullDestroyerAlong_of_noFiniteRetainedCoreTwoRepairs
    {A S : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hnot : ¬ HasFiniteRetainedCoreTwoRepairsAlong A k S)
    (F₀ : Finset ℕ) (N : ℕ) :
    ∃ n T,
      N ≤ n ∧ n ∈ S ∧ T.Nonempty ∧
        (∀ x ∈ T, x ∈ A) ∧ Disjoint T F₀ ∧
        DestroysAt (additiveSupportFamily A (k + 1)) (T : Set ℕ) n := by
  obtain ⟨K, hK⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis.succ
  obtain ⟨D, hDreservoir, hrecur⟩ :=
    recurrentReservoirExtensions_of_noFiniteRetainedCoreTwoRepairs
      hnot F₀
  obtain ⟨n, hn, hnS, hDdestroy | hT⟩ := hrecur ∅ (max N K)
  · have hnN : N ≤ n := le_trans (le_max_left N K) hn
    have hnK : K ≤ n := le_trans (le_max_right N K) hn
    obtain ⟨E, hER, _hEempty⟩ := hK n hnK
    have hDnonempty : D.Nonempty := by
      obtain ⟨x, _hxE, hxD⟩ :=
        Set.not_disjoint_iff.mp (hDdestroy E hER)
      exact ⟨x, by simpa using hxD⟩
    have hDA : ∀ x ∈ D, x ∈ A := by
      intro x hxD
      exact (hDreservoir hxD).1
    have hDF₀ : Disjoint D F₀ := by
      rw [Finset.disjoint_left]
      intro x hxD hxF₀
      exact (hDreservoir hxD).2 (by simpa using hxF₀)
    exact ⟨n, D, hnN, hnS, hDnonempty, hDA, hDF₀,
      by simpa using hDdestroy⟩
  · obtain ⟨T, hTAreservoir, hTD, hTnonempty, _hTcard,
      hDTdestroy⟩ := hT
    let C : Finset ℕ := D ∪ T
    have hCnonempty : C.Nonempty := by
      obtain ⟨x, hxT⟩ := hTnonempty
      exact ⟨x, Finset.mem_union_right D hxT⟩
    have hCA : ∀ x ∈ C, x ∈ A := by
      intro x hxC
      rcases Finset.mem_union.mp hxC with hxD | hxT
      · exact (hDreservoir hxD).1
      · exact (hTAreservoir x hxT).1
    have hCF₀ : Disjoint C F₀ := by
      rw [Finset.disjoint_left]
      intro x hxC hxF₀
      rcases Finset.mem_union.mp hxC with hxD | hxT
      · exact (hDreservoir hxD).2 (by simpa using hxF₀)
      · exact (hTAreservoir x hxT).2.2 (by simpa using hxF₀)
    exact ⟨n, C, le_trans (le_max_left N K) hn, hnS,
      hCnonempty, hCA, hCF₀, by simpa [C] using hDTdestroy⟩

/- On a finite union of translates, the preceding fresh destroyer carries
the explicit translate data required by the certificate-row construction.
The target threshold is raised by `Q.max' hQ` so that the recovered anchor is
at least the requested lower bound. -/
theorem fullTranslateDestroyersByAnchor_of_noFiniteRetainedCoreTwoRepairs
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hQ : Q.Nonempty)
    (hnot : ¬ HasFiniteRetainedCoreTwoRepairsAlong
      A k (finiteTargetTranslates A Q)) :
    HasFullTranslateDestroyersByAnchor A k Q := by
  intro F hFA L
  obtain ⟨n, T, hn, hnS, hTnonempty, hTA, hTF, hdestroy⟩ :=
    exists_freshFullDestroyerAlong_of_noFiniteRetainedCoreTwoRepairs
      hbasis hnot F (L + Q.max' hQ)
  obtain ⟨q, hqQ, a, haA, hnqa⟩ := hnS
  have hqmax : q ≤ Q.max' hQ := Finset.le_max' Q q hqQ
  have hLa : L ≤ a := by omega
  exact ⟨n, T, q, a, hLa, hqQ, haA, hnqa,
    hTA, hTF, hTnonempty, hdestroy⟩

/- Finite/cofinite translate-cover bridge.  If `Q + A` contains a tail, then
global failure of finite-core absorption restricts to that translate set and
therefore produces the full aligned destroyers used by the certificate-row
construction. -/
theorem fullTranslateDestroyersByAnchor_of_cofiniteTranslates_globalNoFiniteCore
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hQ : Q.Nonempty)
    (hcofinite : ∃ M, ∀ n, M ≤ n →
      n ∈ finiteTargetTranslates A Q)
    (hnot : ¬ HasFiniteRetainedCoreTwoRepairsAlong A k Set.univ) :
    HasFullTranslateDestroyersByAnchor A k Q := by
  apply fullTranslateDestroyersByAnchor_of_noFiniteRetainedCoreTwoRepairs
    hbasis hQ
  exact not_hasFiniteRetainedCoreTwoRepairsAlong_of_global_failure
    hnot hcofinite

/- Exhaustive bounded-gap decision boundary.  Either finite-core absorption
already gives the desired infinite successor-order deletion, or one can
choose a cofinite translate cover whose labels are all beyond the order-`k`
representation threshold and on which fresh full destroyers recur. -/
theorem IsEventuallySyndetic.infiniteDeletion_or_lateCofiniteTranslateDestroyers
    {A : Set ℕ} {k : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    (∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1)) ∨
      ∃ Q : Finset ℕ, Q.Nonempty ∧
        (∀ q ∈ Q, hbasis.choose ≤ q) ∧
        (∃ M, ∀ n, M ≤ n →
          n ∈ finiteTargetTranslates A Q) ∧
        HasFullTranslateDestroyersByAnchor A k Q := by
  classical
  by_cases hcore :
      HasFiniteRetainedCoreTwoRepairsAlong A k Set.univ
  · left
    exact exists_infiniteDeletion_succBasis_of_finiteRetainedCoreTwoRepairs
      hbasis hcore ⟨0, by simp⟩
  · right
    obtain ⟨Q, hQ, hQN, hcofinite⟩ :=
      hsyndetic.exists_late_finiteTargetTranslates_cofinite hbasis.choose
    refine ⟨Q, hQ, hQN, hcofinite, ?_⟩
    exact
      fullTranslateDestroyersByAnchor_of_cofiniteTranslates_globalNoFiniteCore
        hbasis hQ hcofinite hcore

/- Matching growth along `Q + A` suffices for an infinite sparse deletion
which preserves all sufficiently large successor representations on precisely
that target set. -/
theorem exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_growth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : OutsideMatchingTendsToInfinityAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A Q)) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      IsExactTupleAsymptoticBasisAlong
        (A \ B) (k + 1) (finiteTargetTranslates A Q) := by
  obtain ⟨B, hBA, hB, hBF, hsurvive⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutsideAlong
      (C := A)
      (R := additiveSupportFamily A (k + 1))
      (S := finiteTargetTranslates A Q)
      (F := F)
      (additiveSupportFamily_supportsBounded A (k + 1))
      (matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong hgrowth)
      (hbasis.unboundedOutside F)
  exact ⟨B, hBA, hB, hBF,
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive⟩

/- A common protected core is not required.  It is enough that, after every
finite deletion prefix and at every requested matching level, a fresh core
can be chosen disjoint from that prefix.  The adaptive sparse-deletion
recursion in `Lemmas` then selects its next point outside the fresh core. -/
theorem exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_adaptiveGrowth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : AdaptiveCoreMatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A Q)) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasisAlong
        (A \ B) (k + 1) (finiteTargetTranslates A Q) := by
  obtain ⟨B, hBA, hB, hsurvive⟩ :=
    sparseDeletion_of_adaptiveCoreMatchingTendsToInfinityOutsideAlong
      (C := A)
      (R := additiveSupportFamily A (k + 1))
      (S := finiteTargetTranslates A Q)
      (additiveSupportFamily_supportsBounded A (k + 1))
      hgrowth (fun F => hbasis.unboundedOutside F)
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive⟩

/- Adaptive finite-core growth plus a cofinite finite-translate target set
already gives the desired global successor basis. -/
theorem exists_infiniteDeletion_succBasis_of_adaptiveFiniteTranslateGrowth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : AdaptiveCoreMatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A Q))
    (hcofinite : ∃ M, ∀ n, M ≤ n →
      n ∈ finiteTargetTranslates A Q) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hB, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_adaptiveGrowth
      hbasis hgrowth
  exact ⟨B, hBA, hB, halong.of_eventually_mem hcofinite⟩

/- Countable common-core fusion for finite translate target sets.  A single
sparse infinite deletion simultaneously preserves successor representations
eventually along every `Q i + A`.  The thresholds may depend on `i`; this is
why an additional uniform-cover argument is required to obtain a global
successor basis from an infinite family of non-cofinite translate sets. -/
theorem exists_infiniteDeletion_succBasisAlong_countableFiniteTargetTranslates_of_commonGrowth
    {A : Set ℕ} {k : ℕ} {Q : ℕ → Finset ℕ} {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : ∀ i, OutsideMatchingTendsToInfinityAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A (Q i))) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      ∀ i, IsExactTupleAsymptoticBasisAlong
        (A \ B) (k + 1) (finiteTargetTranslates A (Q i)) := by
  obtain ⟨B, hBA, hB, hBF, hsurvive⟩ :=
    sparseDeletion_of_countable_matchingTendsToInfinityOutsideAlong
      (C := A)
      (R := additiveSupportFamily A (k + 1))
      (S := fun i => finiteTargetTranslates A (Q i))
      (F := F)
      (additiveSupportFamily_supportsBounded A (k + 1))
      (fun i =>
        matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong
          (hgrowth i))
      (hbasis.unboundedOutside F)
  refine ⟨B, hBA, hB, hBF, ?_⟩
  intro i
  exact hasEventuallySurvivingSupportAlong_additive_iff.mp (hsurvive i)

/- For finite-translate target sets, the abstract uniform-threshold condition
is exactly a finite/cofinite translate cover: finitely many of the `Q i` can
be merged into one finite target set whose translates cover a tail. -/
theorem uniformThresholdCover_finiteTargetTranslates_iff
    {A : Set ℕ} {Q : ℕ → Finset ℕ} :
    UniformThresholdCover (fun i => finiteTargetTranslates A (Q i)) ↔
      ∃ I : Finset ℕ, ∃ N, ∀ n, N ≤ n →
        n ∈ finiteTargetTranslates A (I.biUnion Q) := by
  classical
  rw [uniformThresholdCover_iff_finiteCofiniteSubcover]
  constructor
  · rintro ⟨I, N, hcover⟩
    refine ⟨I, N, ?_⟩
    intro n hn
    obtain ⟨i, hiI, q, hqQi, a, haA, hnqa⟩ := hcover n hn
    exact ⟨q, Finset.mem_biUnion.mpr ⟨i, hiI, hqQi⟩,
      a, haA, hnqa⟩
  · rintro ⟨I, N, hcover⟩
    refine ⟨I, N, ?_⟩
    intro n hn
    obtain ⟨q, hqUnion, a, haA, hnqa⟩ := hcover n hn
    obtain ⟨i, hiI, hqQi⟩ := Finset.mem_biUnion.mp hqUnion
    exact ⟨i, hiI, q, hqQi, a, haA, hnqa⟩

/- Even when the countable family contains a translate `q + A` for every
label `q`, resistance to arbitrary memberwise thresholds is exactly eventual
syndeticity of `A`.  Thus enumerating more and more finite translate sets
does not bypass the bounded-gap obstruction. -/
theorem uniformThresholdCover_allFiniteTargetLabels_iff_eventuallySyndetic
    {A : Set ℕ} {Q : ℕ → Finset ℕ}
    (hlabels : ∀ q, ∃ i, q ∈ Q i) :
    UniformThresholdCover (fun i => finiteTargetTranslates A (Q i)) ↔
      IsEventuallySyndetic A := by
  classical
  constructor
  · intro huniform
    obtain ⟨I, N, hcover⟩ :=
      uniformThresholdCover_finiteTargetTranslates_iff.mp huniform
    apply exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic.mp
    exact ⟨I.biUnion Q, N, hcover⟩
  · intro hsyndetic
    obtain ⟨L, N, hA⟩ := hsyndetic
    have hindex : ∀ q : {q // q ∈ Finset.range (L + 1)},
        ∃ i, q.1 ∈ Q i := by
      intro q
      exact hlabels q.1
    choose index hindex using hindex
    let I : Finset ℕ :=
      (Finset.range (L + 1)).attach.image index
    apply uniformThresholdCover_finiteTargetTranslates_iff.mpr
    refine ⟨I, N, ?_⟩
    intro n hn
    obtain ⟨a, haA, han, hna⟩ := hA n hn
    let q := n - a
    have hqL : q < L + 1 := by
      dsimp only [q]
      omega
    let qsub : {q // q ∈ Finset.range (L + 1)} :=
      ⟨q, Finset.mem_range.mpr hqL⟩
    refine ⟨q, ?_, a, haA, ?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨index qsub, ?_, hindex qsub⟩
      exact Finset.mem_image.mpr ⟨qsub, by simp, rfl⟩
    · exact (Nat.sub_add_cancel han).symm

/- A common finite core plus countable relative matching growth closes the
global successor-basis argument exactly when the translate family has the
uniform-threshold property (equivalently, by the theorem above, a finite
cofinite subcover). -/
theorem exists_infiniteDeletion_succBasis_of_countableFiniteTargetTranslates_of_commonGrowth_of_uniformCover
    {A : Set ℕ} {k : ℕ} {Q : ℕ → Finset ℕ} {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : ∀ i, OutsideMatchingTendsToInfinityAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A (Q i)))
    (hcover : UniformThresholdCover
      (fun i => finiteTargetTranslates A (Q i))) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hB, _hBF, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_countableFiniteTargetTranslates_of_commonGrowth
      hbasis hgrowth
  have hsurviveAlong : ∀ i,
      HasEventuallySurvivingSupportAlong
        (additiveSupportFamily A (k + 1)) B
        (finiteTargetTranslates A (Q i)) := by
    intro i
    exact
      hasEventuallySurvivingSupportAlong_additive_iff.mpr (halong i)
  have hsurvive : HasEventuallySurvivingSupport
      (additiveSupportFamily A (k + 1)) B :=
    hasEventuallySurvivingSupport_of_countableAlong_of_uniformThresholdCover
      hsurviveAlong hcover
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupport_additive_iff.mp hsurvive⟩

/- The common-core assumption can be dropped once uniform threshold coverage
is available.  Uniformity first yields a finite cofinite subcover; the union
of the finitely many corresponding cores is then a common finite core, since
relative matching growth survives enlarging a finite core. -/
theorem exists_infiniteDeletion_succBasis_of_pointwiseFiniteTranslateGrowth_of_uniformCover
    {A : Set ℕ} {k : ℕ} {Q : ℕ → Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : ∀ i, ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 1)) F
        (finiteTargetTranslates A (Q i)))
    (hcover : UniformThresholdCover
      (fun i => finiteTargetTranslates A (Q i))) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  classical
  obtain ⟨I, N, hcofinite⟩ :=
    uniformThresholdCover_finiteTargetTranslates_iff.mp hcover
  choose core hcoreA hcoreGrowth using hgrowth
  let F : Finset ℕ := I.biUnion core
  have hmatchesF : ∀ i ∈ I,
      MatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A (k + 1)) F
        (finiteTargetTranslates A (Q i)) := by
    intro i hiI
    apply matchingTendsToInfinityOutsideAlong_mono_core
      (F := core i)
    · intro x hx
      exact Finset.mem_biUnion.mpr ⟨i, hiI, hx⟩
    · exact
        matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong
          (hcoreGrowth i)
  have hmatchesUnion : MatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A (I.biUnion Q)) := by
    intro j
    have hthreshold : ∀ i : {i // i ∈ I}, ∃ T,
        ∀ n ≥ T, n ∈ finiteTargetTranslates A (Q i.1) →
          ∃ M : Finset (Finset ℕ),
            M ⊆ additiveSupportFamily A (k + 1) n ∧
            j < M.card ∧
            (∀ E ∈ M, (E \ F).Nonempty) ∧
            ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
              Disjoint (E \ F) (E' \ F) := by
      intro i
      exact hmatchesF i.1 i.2 j
    choose T hT using hthreshold
    let Tstar := I.attach.sup T
    refine ⟨Tstar, ?_⟩
    intro n hn hnUnion
    obtain ⟨q, hqUnion, a, haA, hnqa⟩ := hnUnion
    obtain ⟨i, hiI, hqQi⟩ := Finset.mem_biUnion.mp hqUnion
    let ii : {i // i ∈ I} := ⟨i, hiI⟩
    have hii : ii ∈ I.attach := by simp [ii]
    have hTi : T ii ≤ Tstar := Finset.le_sup hii
    exact hT ii n (le_trans hTi hn)
      ⟨q, hqQi, a, haA, hnqa⟩
  have hFA : (F : Set ℕ) ⊆ A := by
    intro x hxF
    obtain ⟨i, _hiI, hxcore⟩ := Finset.mem_biUnion.mp hxF
    exact hcoreA i hxcore
  obtain ⟨B, hBA, hB, _hBF, hsurvive⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutsideAlong
      (C := A)
      (R := additiveSupportFamily A (k + 1))
      (S := finiteTargetTranslates A (I.biUnion Q))
      (F := F)
      (additiveSupportFamily_supportsBounded A (k + 1))
      hmatchesUnion (hbasis.unboundedOutside F)
  have halong : IsExactTupleAsymptoticBasisAlong
      (A \ B) (k + 1)
      (finiteTargetTranslates A (I.biUnion Q)) :=
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive
  exact ⟨B, hBA, hB,
    halong.of_eventually_mem ⟨N, hcofinite⟩⟩

/- The relative-growth branch already closes the original successor-deletion
goal when its finite translate set `Q + A` is cofinite.  The remaining growth
case is exactly the possibility that matching growth is available only on a
non-cofinite collection of translates. -/
theorem exists_infiniteDeletion_succBasis_of_finiteTranslateGrowth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ} {F : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : OutsideMatchingTendsToInfinityAlong
      (additiveSupportFamily A (k + 1)) F
      (finiteTargetTranslates A Q))
    (hcofinite : ∃ M, ∀ n, M ≤ n →
      n ∈ finiteTargetTranslates A Q) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hB, _hBF, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_growth
      hbasis hgrowth
  exact ⟨B, hBA, hB, halong.of_eventually_mem hcofinite⟩

/- A finite cofinite cover by growth-bearing singleton translates is
therefore exactly the remaining sufficient arithmetic statement. -/
theorem exists_infiniteDeletion_succBasis_of_finiteCofiniteGrowthTranslateCover
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hcover : HasFiniteCofiniteGrowthTranslateCover A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨Q, hgrowthSingleton, hcofinite⟩ := hcover
  have hgrowth : ∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong
        (additiveSupportFamily A (k + 1)) F
        (finiteTargetTranslates A Q) :=
    finiteTargetTranslateGrowth_iff_singletonTranslateGrowth.mpr
      hgrowthSingleton
  obtain ⟨F, _hFA, hgrowthF⟩ := hgrowth
  exact exists_infiniteDeletion_succBasis_of_finiteTranslateGrowth
    hbasis hgrowthF hcofinite

/- Complete relative additive dichotomy on `Q + A`: either a sparse infinite
deletion preserves the successor basis along those translates, or bounded bad
targets recur there with explicit `n = q + a` witnesses. -/
theorem infiniteDeletion_succBasisAlong_or_recurrentBoundedMoving
    {A : Set ℕ} {k : ℕ} (Q : Finset ℕ)
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      ∃ B, B ⊆ A ∧ B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
        IsExactTupleAsymptoticBasisAlong
          (A \ B) (k + 1) (finiteTargetTranslates A Q)) ∨
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 1)) A Q := by
  obtain ⟨F, hFA, hgrowth⟩ | hmoving :=
    finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
      (Q := Q)
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1))
  · left
    exact ⟨F, hFA,
      exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_growth
        hbasis hgrowth⟩
  · exact Or.inr hmoving

/- Relative moving recurrence on `Q + A` supplies the full destroyers needed
for a diagonal row.  Additive supports eventually escape the protected core,
so a transversal of the outside hypergraph becomes a full transversal. -/
theorem fullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hQ : Q.Nonempty)
    (hmoving :
      HasBoundedMovingOutsideTransversalsOnFiniteTranslates
        (additiveSupportFamily A (k + 1)) A Q) :
    HasFullTranslateDestroyersByAnchor A k Q := by
  have hmovingAnchor :=
    (boundedMovingOnFiniteTranslates_iff_byAnchor hQ).mp hmoving
  intro F hFA L
  obtain ⟨m, hm⟩ := hmovingAnchor F hFA
  obtain ⟨K, hK⟩ :=
    additiveSupportFamily_eventuallyEscapesFiniteCores A (k + 1) F
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis.succ
  obtain ⟨n, T, q, a, haLower, hqQ, haA, hnqa,
      hTA, hTF, _hTcard, htrans⟩ := hm (max L (max K N))
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
    hTA, hTF, hTnonempty, hdestroy⟩

/- Exhaustive certificate-aligned diagonal dichotomy.  If no nonempty
finite `Q` has the relative matching-growth branch, the relative moving
branch holds for every `Q`; the preceding construction then builds all rows
simultaneously with global disjointness. -/
theorem finiteTranslateMatchingGrowth_or_diagonalDestroyerRows
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    HasSomeFiniteTranslateMatchingGrowth A k ∨
      HasDiagonalFullAlignedTranslateDestroyerRows A k := by
  classical
  by_cases hgrowth : HasSomeFiniteTranslateMatchingGrowth A k
  · exact Or.inl hgrowth
  · right
    apply exists_diagonalFullAlignedTranslateDestroyerRows
    intro Q hQ
    apply fullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ
    obtain hrelative | hmoving :=
      finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
        (A := A) (Q := Q)
        (R := additiveSupportFamily A (k + 1))
        (additiveSupportFamily_supportsIn A (k + 1))
        (additiveSupportFamily_cardAtMost A (k + 1))
    · exact (hgrowth ⟨Q, hQ, hrelative⟩).elim
    · exact hmoving

/- Strengthened exhaustive dichotomy retaining every translate anchor inside
its row cell.  This is the version used by the certificate-selector count. -/
theorem finiteTranslateMatchingGrowth_or_diagonalAnchoredCellRows
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    HasSomeFiniteTranslateMatchingGrowth A k ∨
      HasDiagonalAnchoredAlignedTranslateCellRows A k := by
  classical
  by_cases hgrowth : HasSomeFiniteTranslateMatchingGrowth A k
  · exact Or.inl hgrowth
  · right
    apply exists_diagonalAnchoredAlignedTranslateCellRows
    intro Q hQ
    apply fullTranslateDestroyersByAnchor_of_boundedMovingOnFiniteTranslates
      hbasis hQ
    obtain hrelative | hmoving :=
      finiteCore_translateMatchingGrowth_or_recurrentBoundedMoving
        (A := A) (Q := Q)
        (R := additiveSupportFamily A (k + 1))
        (additiveSupportFamily_supportsIn A (k + 1))
        (additiveSupportFamily_cardAtMost A (k + 1))
    · exact (hgrowth ⟨Q, hQ, hrelative⟩).elim
    · exact hmoving

/-- The strong-minimality hypotheses relevant to Problem 881: `A` is already
an exact basis of order `k`, and deleting any infinite subset destroys
arbitrarily large targets at that order. -/
def IsStronglyMinimalExactBasis (A : Set ℕ) (k : ℕ) : Prop :=
  IsExactTupleAsymptoticBasis A k ∧
    StrongInfiniteDeletion (additiveSupportFamily A k) A

/-- The exact finite-booster counterexample criterion.  To obtain a negative
instance of Problem 881 at order `k`, it suffices to construct an exact
order-`k` basis for which all but finitely many elements have arbitrarily late
private witnesses at order `k + 1`.

The first conclusion is the problem's strong-deletion hypothesis at order
`k`; the second says that no infinite deletion preserves the successor-order
basis property. -/
theorem finiteBoosterCounterexampleCriterion
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hsingle : HasCofiniteSingletonDestruction
      (additiveSupportFamily A (k + 1)) A) :
    IsStronglyMinimalExactBasis A k ∧
      ∀ B, B ⊆ A → B.Infinite →
        ¬ IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  refine ⟨⟨hbasis, ?_⟩, ?_⟩
  · exact
      strongInfiniteDeletion_predecessor_of_cofiniteSingletonDestruction
        hsingle
  · exact
      noInfiniteDeletionPreservesExactBasis_of_cofiniteSingletonDestruction
        hsingle

/- Applying the disjoint-selector count to the certificate returned by strong
deletion localizes a small partition block.  This uses the order-`k` basis to
choose one support for every late certified target. -/
theorem IsStronglyMinimalExactBasis.exists_lateCertificate_with_smallBlock
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (F : ℕ → Finset ℕ) (P : IsFiniteBlockPartition A F) (N : ℕ) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A k) (selectedSet s) q) ∧
      ∃ i, (F i).card ≤ k * Q.card := by
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  obtain ⟨Q, hQlower, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hminimal.2)
      F P (max N N₀)
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hq
    exact le_trans (le_max_left _ _) (hQlower q hq)
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q =>
      let w := hN₀ q.1
        (le_trans (le_max_right _ _) (hQlower q.1 q.2))
      ⟨w.choose, w.choose_spec.1⟩
  exact ⟨Q, hQN, hcert,
    exists_smallBlock_of_additiveSelectorCertificate P c hcert⟩

/-- The late-certificate/small-block consequence remains valid on any
deletion reservoir `C ⊆ A`.  In particular, taking `C = A \ D` makes every
certificate selector avoid a prescribed finite retained core `D`. -/
theorem IsStronglyMinimalExactBasis.exists_lateCertificate_on_reservoir_with_smallBlock
    {A C : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hCA : C ⊆ A)
    (F : ℕ → Finset ℕ) (P : IsFiniteBlockPartition C F) (N : ℕ) :
    ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt (additiveSupportFamily A k) (selectedSet s) q) ∧
      ∃ i, (F i).card ≤ k * Q.card := by
  obtain ⟨N₀, hN₀⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  obtain ⟨Q, hQlower, hcert⟩ :=
    finiteBlockCertificates_on_subset_of_strongInfiniteDeletion
      hminimal.2 hCA F P (max N N₀)
  have hQN : ∀ q ∈ Q, N ≤ q := by
    intro q hq
    exact le_trans (le_max_left _ _) (hQlower q hq)
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q =>
      let w := hN₀ q.1
        (le_trans (le_max_right _ _) (hQlower q.1 q.2))
      ⟨w.choose, w.choose_spec.1⟩
  exact ⟨Q, hQN, hcert,
    exists_smallBlock_of_additiveSelectorCertificate P c hcert⟩

/-- The finite-block compactness characterization specialized to exact
additive representations. -/
theorem additiveStrongDeletion_iff_finiteBlockCertificates
    {A : Set ℕ} {h : ℕ} :
    (∀ B, B ⊆ A → B.Infinite →
      ∀ N, ∃ n, N ≤ n ∧
        ¬ ∃ v : Fin h → ℕ,
          (∀ i, v i ∈ A \ B) ∧
          ∑ i, v i = n) ↔
      FiniteBlockCertificateProperty (additiveSupportFamily A h) A :=
  strongInfiniteDeletion_additiveSupportFamily_iff.symm.trans <|
    strongInfiniteDeletion_iff_finiteBlockCertificates

/-- The abstract successor-transversal descent property holds for exact
additive representation supports. -/
theorem additiveSuccessorTransversalsDescend
    (A : Set ℕ) (k : ℕ) :
    SuccessorTransversalsDescend
      (additiveSupportFamily A k)
      (additiveSupportFamily A (k + 1)) A := by
  intro S n hdestroy a haA haS han E hER
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  let w : Fin (k + 1) → Fin (n + 1) :=
    Fin.cons ⟨a, Nat.lt_succ_iff.mpr han⟩ fun i =>
      ⟨(v i).1, by
        have hvi : (v i).1 ≤ n - a := Nat.le_of_lt_succ (v i).2
        exact Nat.lt_succ_of_le (le_trans hvi (Nat.sub_le n a))⟩
  have hwA : ∀ i, (w i).1 ∈ A := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [w] using haA
    · simpa [w] using hvA j
  have hwsum : ∑ i, (w i).1 = n := by
    rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    rw [hvsum]
    exact Nat.add_sub_of_le han
  have hwrep : tupleSupport w ∈ additiveSupportFamily A (k + 1) n := by
    apply mem_additiveSupportFamily_iff.mpr
    exact ⟨w, hwA, hwsum, rfl⟩
  have hhit := hdestroy (tupleSupport w) hwrep
  apply Set.not_disjoint_iff.mpr
  obtain ⟨x, hxw, hxS⟩ := Set.not_disjoint_iff.mp hhit
  refine ⟨x, ?_, hxS⟩
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxw
  have hsource :
      ∀ i : Fin (k + 1), (w i).1 = x → x ∈ tupleSupport v := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hzero
      have hxa : x = a := by simpa [w] using hzero.symm
      exact (haS (hxa ▸ hxS)).elim
    · intro hsucc
      apply mem_tupleSupport_iff.mpr
      refine ⟨j, ?_⟩
      simpa [w] using hsucc
  exact hsource i hi

/-- With `1` retained, a private successor-order witness for `c ≠ 1`
forces its predecessor to be a private witness at the preceding order.  Thus
a finite-booster construction cannot cover `p - 1` by a representation that
avoids the scheduled element `c`. -/
theorem singletonSuccessorDestruction_descends_by_booster_one
    {A : Set ℕ} {k c p : ℕ}
    (hone : 1 ∈ A)
    (hc : c ≠ 1)
    (hp : 1 ≤ p)
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 1)) ({c} : Set ℕ) p) :
    DestroysAt
      (additiveSupportFamily A k) ({c} : Set ℕ) (p - 1) := by
  have honeNot : 1 ∉ ({c} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using hc.symm
  have hdestroy' : DestroysAt
      (additiveSupportFamily A (k + 1))
      ((({c} : Finset ℕ) : Set ℕ)) p := by
    simpa using hdestroy
  simpa using
    (additiveSuccessorTransversalsDescend A k
      ({c} : Finset ℕ) p hdestroy' 1 hone honeNot hp)

/-- Anchor exclusion for a finite predecessor defect.  If `S` destroys every
order-`k` support of `m`, then an order-`k+1` support of `m+a` which avoids
`S` cannot contain `a`: deleting one occurrence of `a` would give a forbidden
order-`k` support of `m` still avoiding `S`. -/
theorem anchor_not_mem_successorSupport_of_predecessorDestroyed
    {A S : Set ℕ} {k m a : ℕ} {E : Finset ℕ}
    (hdestroy : DestroysAt (additiveSupportFamily A k) S m)
    (hER : E ∈ additiveSupportFamily A (k + 1) (m + a))
    (hES : Disjoint (E : Set ℕ) S) :
    a ∉ E := by
  classical
  intro haE
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp haE
  let u : Fin k → ℕ := fun j => (v (i.succAbove j)).1
  have husum : ∑ j, u j = m := by
    have hsplit := Fin.sum_univ_succAbove (fun t => (v t).1) i
    rw [hvsum, hi] at hsplit
    dsimp only [u]
    omega
  have hule : ∀ j, u j ≤ m := by
    intro j
    rw [← husum]
    exact Finset.single_le_sum
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  let w : Fin k → Fin (m + 1) := fun j =>
    ⟨u j, Nat.lt_succ_of_le (hule j)⟩
  have hwR : tupleSupport w ∈ additiveSupportFamily A k m := by
    apply mem_additiveSupportFamily_iff.mpr
    refine ⟨w, ?_, ?_, rfl⟩
    · intro j
      exact hvA (i.succAbove j)
    · simpa [w] using husum
  have hwsubset : tupleSupport w ⊆ tupleSupport v := by
    intro x hxw
    obtain ⟨j, hj⟩ := mem_tupleSupport_iff.mp hxw
    apply mem_tupleSupport_iff.mpr
    exact ⟨i.succAbove j, by simpa [w, u] using hj⟩
  have hwS : Disjoint (tupleSupport w : Set ℕ) S :=
    Set.disjoint_of_subset_left
      (fun x hx => Finset.mem_coe.mpr
        (hwsubset (Finset.mem_coe.mp hx))) hES
  exact (hdestroy (tupleSupport w) hwR) hwS

/-- Both members of a two-repair pair are anchor-free whenever they avoid a
set destroying the common predecessor. -/
theorem twoRepairs_anchorFree_of_predecessorDestroyed
    {A S : Set ℕ} {k m a : ℕ} {E E' : Finset ℕ}
    (hdestroy : DestroysAt (additiveSupportFamily A k) S m)
    (hER : E ∈ additiveSupportFamily A (k + 1) (m + a))
    (hE'R : E' ∈ additiveSupportFamily A (k + 1) (m + a))
    (hES : Disjoint (E : Set ℕ) S)
    (hE'S : Disjoint (E' : Set ℕ) S) :
    a ∉ E ∧ a ∉ E' :=
  ⟨anchor_not_mem_successorSupport_of_predecessorDestroyed
      hdestroy hER hES,
    anchor_not_mem_successorSupport_of_predecessorDestroyed
      hdestroy hE'R hE'S⟩

/- A fixed singleton translate has uniformly bounded full moving
transversals if one cardinal bound works after protecting every finite core.
This is stronger than the recurrent bad branch currently obtained from
failure of relative matching, whose bound may depend on the protected core. -/
def HasUniformlyBoundedFullTransversalsOnSingletonTranslate
    (A : Set ℕ) (k q : ℕ) : Prop :=
  ∃ m, ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
    ∃ n T a,
      L ≤ a ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧ T.card ≤ m ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/- Bounded gaps exclude the uniformly bounded internal-anchor obstruction.
Protect one order-`k` support for every bounded predecessor shift.  A large
anchor has more nearby predecessors in `A` than the transversal has vertices,
so one nearby `b ∈ A \ T` descends the successor transversal to a protected
support, a contradiction. -/
theorem IsEventuallySyndetic.not_uniformlyBoundedFullTransversalsOnSingletonTranslate
    {A : Set ℕ} {k : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∀ q, ¬ HasUniformlyBoundedFullTransversalsOnSingletonTranslate A k q := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  intro q hrecur
  obtain ⟨m, hm⟩ := hrecur
  obtain ⟨D, L, hnear⟩ :=
    hsyndetic.exists_nearby_not_mem_finset m
  let Dtotal := D + N + 1
  let shifts := Finset.Icc N Dtotal
  have hsupport : ∀ d : {d // d ∈ shifts},
      ∃ E ∈ additiveSupportFamily A k (q + d.1), True := by
    intro d
    obtain ⟨E, hER, _⟩ :=
      hN (q + d.1) (le_trans (Finset.mem_Icc.mp d.2).1
        (Nat.le_add_left d.1 q))
    exact ⟨E, hER, trivial⟩
  choose support hsupportMem _ using hsupport
  let U : Finset ℕ :=
    shifts.attach.biUnion support
  have hUA : (U : Set ℕ) ⊆ A := by
    intro x hxU
    obtain ⟨d, _hd, hxsupport⟩ := Finset.mem_biUnion.mp hxU
    exact additiveSupportFamily_supportsIn A k
      (q + d.1) (support d) (hsupportMem d) x hxsupport
  obtain ⟨n, T, a, haLower, haA, hnqa, _hTA,
      hTU, hTcard, hdestroy⟩ := hm U hUA (L + N + 1)
  let x := a - (N + 1)
  have hLx : L ≤ x := by
    dsimp only [x]
    omega
  obtain ⟨b, hbA, hbT, hba, habD⟩ :=
    hnear x T hLx hTcard
  have hxa : x < a := by
    dsimp only [x]
    omega
  have hba' : b < a := lt_trans hba hxa
  let d := a - b
  have hdLower : N ≤ d := by
    dsimp only [d]
    omega
  have hdUpper : d ≤ Dtotal := by
    dsimp only [d, Dtotal, x] at *
    omega
  have hdShifts : d ∈ shifts :=
    Finset.mem_Icc.mpr ⟨hdLower, hdUpper⟩
  let dsub : {d // d ∈ shifts} := ⟨d, hdShifts⟩
  have hsupportU : support dsub ⊆ U := by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨dsub, by simp [dsub], hx⟩
  have hsupportT :
      Disjoint (support dsub : Set ℕ) (T : Set ℕ) := by
    exact Set.disjoint_of_subset_left
      (fun x hx =>
        Finset.mem_coe.mpr (hsupportU (Finset.mem_coe.mp hx)))
      (by simpa using hTU.symm)
  have hbn : b ≤ n := by omega
  have hdescend : DestroysAt
      (additiveSupportFamily A k) (T : Set ℕ) (n - b) :=
    additiveSuccessorTransversalsDescend A k
      T n hdestroy b hbA (by simpa using hbT) hbn
  have hnsub : n - b = q + d := by
    dsimp only [d]
    omega
  rw [hnsub] at hdescend
  exact (hdescend (support dsub) (hsupportMem dsub)) hsupportT

/-- If the exact finite prefix returned by failure of adaptive growth can be
deleted while retaining the order-`k` basis property, its fixed matching
bound produces a uniform bounded-transversal obstruction on `A \ D`.  The
bounded-gap shift argument excludes that obstruction. -/
theorem IsEventuallySyndetic.not_adaptiveCoreMatchingObstructionAt_of_diff_basis
    {A : Set ℕ} {k q j : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (D : Finset ℕ)
    (hbasisD : IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) k)
    (hbad : IsAdaptiveCoreMatchingObstructionAt
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A {q}) D j) : False := by
  classical
  let A' : Set ℕ := A \ (D : Set ℕ)
  have hsyndetic' : IsEventuallySyndetic A' := by
    simpa [A'] using hsyndetic.diff_finset D
  have hbasis' : IsExactTupleAsymptoticBasis A' k := by
    simpa [A'] using hbasisD
  apply
    (hsyndetic'.not_uniformlyBoundedFullTransversalsOnSingletonTranslate
      hbasis' q)
  refine ⟨(k + 1) * j, ?_⟩
  intro G hGA' L
  have hGD : Disjoint G D := by
    rw [Finset.disjoint_left]
    intro x hxG hxD
    exact (hGA' hxG).2 (by simpa using hxD)
  obtain ⟨Kescape, hescape⟩ :=
    additiveSupportFamily_eventuallyEscapesFiniteCores A' (k + 1) G
  let K := max (q + L) (max (q + D.sup id + 1) Kescape)
  obtain ⟨n, hnK, hnTranslate, hnoMatching⟩ := hbad G hGD K
  obtain ⟨q', hq', a, haA, hnqa'⟩ := hnTranslate
  have hq'eq : q' = q := by simpa using hq'
  subst q'
  have hnLower : q + L ≤ n :=
    le_trans (le_max_left _ _) hnK
  have hnAboveD : q + D.sup id + 1 ≤ n :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hnK)
  have hnEscape : Kescape ≤ n :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) hnK)
  have haLower : L ≤ a := by omega
  have haD : a ∉ D := by
    intro haD
    have hale : a ≤ D.sup id := by
      simpa using (Finset.le_sup (f := fun x : ℕ => x) haD)
    omega
  have haA' : a ∈ A' := ⟨haA, by simpa using haD⟩
  have hmatchingNumber :
      matchingNumber
        (outsideSupportHypergraph
          (additiveSupportFamily A' (k + 1)) G n) ≤ j := by
    apply Nat.le_of_not_gt
    intro hlarge
    apply hnoMatching
    obtain ⟨M, hMR, hMlarge, hMnonempty, hMdisjoint⟩ :=
      lt_matchingNumber_outsideSupportHypergraph_iff.mp hlarge
    refine ⟨M, ?_, hMlarge, hMnonempty, hMdisjoint⟩
    intro E hEM
    obtain ⟨v, hvA', hvsum, rfl⟩ :=
      mem_additiveSupportFamily_iff.mp (hMR hEM)
    apply mem_additiveSupportFamily_iff.mpr
    exact ⟨v, fun i => (hvA' i).1, hvsum, rfl⟩
  obtain ⟨T, hTA', hTG, hTcard, hTtrans⟩ :=
    exists_small_outsideTransversal_of_matchingNumber_le
      (A := A')
      (R := additiveSupportFamily A' (k + 1))
      (F := G) (n := n) (r := k + 1) (m := j)
      (additiveSupportFamily_supportsIn A' (k + 1))
      (additiveSupportFamily_cardAtMost A' (k + 1))
      hmatchingNumber
  have hdestroy : DestroysAt
      (additiveSupportFamily A' (k + 1)) (T : Set ℕ) n := by
    intro E hER
    have hEG : (E \ G).Nonempty := hescape n hnEscape E hER
    have hEGmem : E \ G ∈ outsideSupportHypergraph
        (additiveSupportFamily A' (k + 1)) G n := by
      apply Finset.mem_erase.mpr
      exact ⟨Finset.nonempty_iff_ne_empty.mp hEG,
        Finset.mem_image.mpr ⟨E, hER, rfl⟩⟩
    obtain ⟨x, hx⟩ := hTtrans (E \ G) hEGmem
    obtain ⟨hxEG, hxT⟩ := Finset.mem_inter.mp hx
    exact Set.not_disjoint_iff.mpr
      ⟨x, (Finset.mem_sdiff.mp hxEG).1,
        Finset.mem_coe.mpr hxT⟩
  exact ⟨n, T, a, haLower, haA', hnqa', hTA', hTG,
    hTcard, hdestroy⟩

/- In the finite-deletion-stable case, the adaptive core condition is not an
extra dichotomy hypothesis.  If it failed at a prefix `D` and level `j`, its
exact negation would give the same matching-number bound `j` outside every
core disjoint from `D`. -/
theorem IsEventuallySyndetic.adaptiveCoreMatchingOnSingletonTranslate_of_finiteDeletionStable
    {A : Set ℕ} {k : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (hstable : IsFiniteDeletionStableExactBasis A k) :
    ∀ q, AdaptiveCoreMatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A {q}) := by
  intro q
  by_contra hnot
  obtain ⟨D, j, hbad⟩ :=
    not_adaptiveCoreMatchingTendsToInfinityOutsideAlong_iff.mp hnot
  exact hsyndetic.not_adaptiveCoreMatchingObstructionAt_of_diff_basis
    D (hstable D) hbad

/-- Therefore the exact prefix occurring in a bounded-gap adaptive-matching
obstruction is already a same-order finite deletion obstruction. -/
theorem IsEventuallySyndetic.not_diff_basis_of_adaptiveCoreMatchingObstructionAt
    {A : Set ℕ} {k q j : ℕ}
    (hsyndetic : IsEventuallySyndetic A) (D : Finset ℕ)
    (hbad : IsAdaptiveCoreMatchingObstructionAt
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A {q}) D j) :
    ¬ IsExactTupleAsymptoticBasis (A \ (D : Set ℕ)) k := by
  intro hbasisD
  exact hsyndetic.not_adaptiveCoreMatchingObstructionAt_of_diff_basis
    D hbasisD hbad

/-- Fully unpacked residual branch for one singleton translate: failure of
adaptive successor matching returns one fixed finite prefix `D`, one matching
bound `j`, and arbitrarily late order-`k` targets destroyed by that same `D`.
This is the finite defect that the `k+1` argument must repair. -/
theorem IsEventuallySyndetic.exists_finiteDestroyer_of_not_adaptiveSingletonGrowth
    {A : Set ℕ} {k q : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (hnot : ¬ AdaptiveCoreMatchingTendsToInfinityOutsideAlong
      (additiveSupportFamily A (k + 1))
      (finiteTargetTranslates A {q})) :
    ∃ D : Finset ℕ, ∃ j,
      IsAdaptiveCoreMatchingObstructionAt
        (additiveSupportFamily A (k + 1))
        (finiteTargetTranslates A {q}) D j ∧
      ∀ N, ∃ n, N ≤ n ∧
        DestroysAt
          (additiveSupportFamily A k) (D : Set ℕ) n := by
  obtain ⟨D, j, hbad⟩ :=
    not_adaptiveCoreMatchingTendsToInfinityOutsideAlong_iff.mp hnot
  refine ⟨D, j, hbad, ?_⟩
  exact not_exactTupleAsymptoticBasis_diff_finset_iff.mp
    (hsyndetic.not_diff_basis_of_adaptiveCoreMatchingObstructionAt D hbad)

/- Finitely many singleton translates may use different adaptive cores at a
stage.  The finite-menu sparse recursion avoids their union and preserves all
of the translate classes simultaneously. -/
theorem exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_finiteMenuAdaptiveGrowth
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hgrowth : ∀ q ∈ Q,
      AdaptiveCoreMatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A (k + 1))
        (finiteTargetTranslates A {q})) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasisAlong
        (A \ B) (k + 1) (finiteTargetTranslates A Q) := by
  classical
  let S : {q // q ∈ Q} → Set ℕ := fun q =>
    finiteTargetTranslates A {q.1}
  have hmenu :
      FiniteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A (k + 1)) S := by
    intro D j
    have hchoice : ∀ q : {q // q ∈ Q},
        ∃ core : Finset ℕ, Disjoint core D ∧
          ∃ threshold, ∀ n ≥ threshold, n ∈ S q →
            ∃ M : Finset (Finset ℕ),
              M ⊆ additiveSupportFamily A (k + 1) n ∧
                j < M.card ∧
                (∀ E ∈ M, (E \ core).Nonempty) ∧
                ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
                  Disjoint (E \ core) (E' \ core) := by
      intro q
      exact hgrowth q.1 q.2 D j
    choose core hcoreD threshold hmatching using hchoice
    exact ⟨core, hcoreD, threshold, hmatching⟩
  obtain ⟨B, hBA, hB, hsurvive⟩ :=
    sparseDeletion_of_finiteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong
      (C := A) (S := S)
      (R := additiveSupportFamily A (k + 1))
      (additiveSupportFamily_supportsBounded A (k + 1))
      hmenu (fun F => hbasis.unboundedOutside F)
  have htargets : {n | ∃ i, n ∈ S i} = finiteTargetTranslates A Q := by
    ext n
    constructor
    · rintro ⟨i, q, hq, a, haA, hnqa⟩
      have hqi : q = i.1 := by simpa using hq
      subst q
      exact ⟨i.1, i.2, a, haA, hnqa⟩
    · rintro ⟨q, hqQ, a, haA, hnqa⟩
      exact ⟨⟨q, hqQ⟩, q, by simp, a, haA, hnqa⟩
  rw [htargets] at hsurvive
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupportAlong_additive_iff.mp hsurvive⟩

/- A genuine positive subclass of Problem 881.  If bounded gaps hold and
every finite deletion remains an order-`k` basis, then an infinite deletion
can be chosen which remains a basis at order `k+1`.  No uniform-core or
uniform-moving dichotomy is assumed. -/
theorem exists_infiniteDeletion_succBasis_of_eventuallySyndetic_of_finiteDeletionStable
    {A : Set ℕ} {k : ℕ}
    (hsyndetic : IsEventuallySyndetic A)
    (hstable : IsFiniteDeletionStableExactBasis A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  have hbasis : IsExactTupleAsymptoticBasis A k := by
    simpa using hstable ∅
  obtain ⟨Q, N, hcover⟩ :=
    exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic.mpr
      hsyndetic
  have hgrowth : ∀ q ∈ Q,
      AdaptiveCoreMatchingTendsToInfinityOutsideAlong
        (additiveSupportFamily A (k + 1))
        (finiteTargetTranslates A {q}) := by
    intro q _hqQ
    exact
      hsyndetic.adaptiveCoreMatchingOnSingletonTranslate_of_finiteDeletionStable
        hstable q
  obtain ⟨B, hBA, hB, halong⟩ :=
    exists_infiniteDeletion_succBasisAlong_finiteTargetTranslates_of_finiteMenuAdaptiveGrowth
      hbasis hgrowth
  exact ⟨B, hBA, hB, halong.of_eventually_mem ⟨N, hcover⟩⟩

/- The precise remaining quantifier-strengthening for the bounded-gap route:
on every singleton translate, either relative matching grows outside some
finite core, or one cardinal bound works uniformly over all protected cores. -/
def HasSingletonTranslateGrowthOrUniformMovingDichotomy
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ q,
    HasSingletonTranslateMatchingGrowth A k q ∨
      HasUniformlyBoundedFullTransversalsOnSingletonTranslate A k q

/- Under that uniform-core dichotomy, eventual syndeticity closes Problem
881.  Uniform moving is excluded by the preceding shift argument, so every
member of a finite cofinite translate cover has relative matching growth. -/
theorem exists_infiniteDeletion_succBasis_of_eventuallySyndetic_of_singletonUniformDichotomy
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hsyndetic : IsEventuallySyndetic A)
    (hdichotomy :
      HasSingletonTranslateGrowthOrUniformMovingDichotomy A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨Q, N, hcover⟩ :=
    exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic.mpr
      hsyndetic
  have hgrowth : ∀ q ∈ Q,
      HasSingletonTranslateMatchingGrowth A k q := by
    intro q _hqQ
    obtain hqGrowth | hqUniform := hdichotomy q
    · exact hqGrowth
    · exact
        (hsyndetic.not_uniformlyBoundedFullTransversalsOnSingletonTranslate
          hbasis q hqUniform).elim
  exact exists_infiniteDeletion_succBasis_of_finiteCofiniteGrowthTranslateCover
    hbasis ⟨Q, hgrowth, N, hcover⟩

/- The common-target version of the moving-transversal contradiction.  If a
pairwise-disjoint family of successor destroyers can all be translated to one
represented order-`k` target `q`, then the family has at most `k` members. -/
theorem card_aligned_pairwiseDisjoint_successorDestroyers_le
    {A : Set ℕ} {k q : ℕ} {𝒯 : Finset (Finset ℕ)}
    (hq : (additiveSupportFamily A k q).Nonempty)
    (hpair : IsMatching 𝒯)
    (halign : ∀ T ∈ 𝒯, ∃ n a,
      DestroysAt (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
      a ∈ A ∧ a ∉ T ∧ a ≤ n ∧ n - a = q) :
    𝒯.card ≤ k := by
  apply card_pairwiseDisjoint_additiveDestroyers_le hq hpair
  intro T hT
  obtain ⟨n, a, hdestroy, haA, haT, han, hnq⟩ := halign T hT
  rw [← hnq]
  exact additiveSuccessorTransversalsDescend A k
    T n hdestroy a haA (by simpa using haT) han

/- For an asymptotic basis, the represented-target premise in the preceding
theorem is automatic beyond one threshold.  Thus common-target alignment of
more than `k` disjoint successor destroyers is eventually impossible. -/
theorem IsExactTupleAsymptoticBasis.eventually_card_alignedDestroyers_le
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ q, N ≤ q → ∀ 𝒯 : Finset (Finset ℕ),
      IsMatching 𝒯 →
      (∀ T ∈ 𝒯, ∃ n a,
        DestroysAt (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
        a ∈ A ∧ a ∉ T ∧ a ≤ n ∧ n - a = q) →
      𝒯.card ≤ k := by
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro q hNq 𝒯 hpair halign
  obtain ⟨E, hER, _hEempty⟩ := hN q hNq
  exact card_aligned_pairwiseDisjoint_successorDestroyers_le
    ⟨E, hER⟩ hpair halign

/- Multi-target aligned successor version.  More than `k * |Q|` disjoint
successor destroyers cannot carry anchor-avoiding translations into a finite
late target set `Q`. -/
theorem IsExactTupleAsymptoticBasis.eventually_card_alignedSuccessorDestroyers_over_targets_le
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ Q : Finset ℕ, (∀ q ∈ Q, N ≤ q) →
      ∀ 𝒯 : Finset (Finset ℕ), IsMatching 𝒯 →
        (∀ T ∈ 𝒯, ∃ q : {m // m ∈ Q}, ∃ n a,
          DestroysAt
            (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
          a ∈ A ∧ a ∉ T ∧ a ≤ n ∧ n - a = q.1) →
        𝒯.card ≤ k * Q.card := by
  obtain ⟨N, hN⟩ :=
    hbasis.eventually_card_disjointDestroyers_over_targets_le
  refine ⟨N, ?_⟩
  intro Q hQN 𝒯 hpair halign
  apply hN Q hQN 𝒯 hpair
  intro T hT
  obtain ⟨q, n, a, hdestroy, haA, haT, han, hnq⟩ :=
    halign T hT
  refine ⟨q, ?_⟩
  rw [← hnq]
  exact additiveSuccessorTransversalsDescend A k
    T n hdestroy a haA (by simpa using haT) han

/- The strengthened recurrent bad branch requested by the conditional
argument: after every protected finite core and anchor threshold, it returns a
new nonempty full successor destroyer, disjoint from both the old core and its
translate anchor. -/
def HasAnchorAvoidingFullTransversalsOnFiniteTranslates
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A → ∀ L,
    ∃ n T q a,
      L ≤ a ∧ q ∈ Q ∧ a ∈ A ∧ n = q + a ∧
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧
      T.Nonempty ∧ a ∉ T ∧
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n

/- A finite family carrying exactly the data needed by the multi-target
counting theorem. -/
def IsAnchorAvoidingAlignedDestroyerFamily
    (A : Set ℕ) (k : ℕ) (Q : Finset ℕ)
    (𝒯 : Finset (Finset ℕ)) : Prop :=
  IsMatching 𝒯 ∧
    (∀ T ∈ 𝒯, T.Nonempty) ∧
    (∀ T ∈ 𝒯, ∀ x ∈ T, x ∈ A) ∧
    ∀ T ∈ 𝒯, ∃ q : {m // m ∈ Q}, ∃ n a,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
      a ∈ A ∧ a ∉ T ∧ n = q.1 + a

/- Anchor-avoiding full recurrence constructs arbitrarily large finite
families of pairwise-disjoint aligned successor destroyers. -/
theorem exists_anchorAvoidingAlignedDestroyerFamily_card
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hrecur : HasAnchorAvoidingFullTransversalsOnFiniteTranslates A k Q) :
    ∀ r, ∃ 𝒯 : Finset (Finset ℕ),
      IsAnchorAvoidingAlignedDestroyerFamily A k Q 𝒯 ∧
      𝒯.card = r := by
  classical
  intro r
  induction r with
  | zero =>
      refine ⟨∅, ?_, by simp⟩
      simp [IsAnchorAvoidingAlignedDestroyerFamily, IsMatching]
  | succ r ih =>
      obtain ⟨𝒯, hfamily, hcard⟩ := ih
      let F : Finset ℕ := 𝒯.biUnion id
      have hFA : (F : Set ℕ) ⊆ A := by
        intro x hxF
        obtain ⟨T, hT𝒯, hxT⟩ := Finset.mem_biUnion.mp hxF
        exact hfamily.2.2.1 T hT𝒯 x hxT
      obtain ⟨n, T, q, a, _haLower, hqQ, haA, hnqa,
        hTA, hTF, hTnonempty, haT, hdestroy⟩ :=
        hrecur F hFA 0
      have hTnot : T ∉ 𝒯 := by
        intro hT𝒯
        obtain ⟨x, hxT⟩ := hTnonempty
        apply Finset.disjoint_left.mp hTF hxT
        exact Finset.mem_biUnion.mpr ⟨T, hT𝒯, hxT⟩
      have hmatching : IsMatching (insert T 𝒯) := by
        rw [IsMatching, Finset.coe_insert, Set.pairwiseDisjoint_insert]
        refine ⟨hfamily.1, ?_⟩
        intro D hD𝒯 hTD
        rw [Finset.disjoint_left]
        intro x hxT hxD
        apply Finset.disjoint_left.mp hTF hxT
        exact Finset.mem_biUnion.mpr ⟨D, hD𝒯, hxD⟩
      have hnewfamily :
          IsAnchorAvoidingAlignedDestroyerFamily A k Q (insert T 𝒯) := by
        refine ⟨hmatching, ?_, ?_, ?_⟩
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact hTnonempty
          · exact hfamily.2.1 D hD𝒯
        · intro D hD x hxD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact hTA x hxD
          · exact hfamily.2.2.1 D hD𝒯 x hxD
        · intro D hD
          rcases Finset.mem_insert.mp hD with rfl | hD𝒯
          · exact ⟨⟨q, hqQ⟩, n, a,
              hdestroy, haA, haT, hnqa⟩
          · exact hfamily.2.2.2 D hD𝒯
      refine ⟨insert T 𝒯, hnewfamily, ?_⟩
      simp [hTnot, hcard]

/- Conditional closure of the recurrent bad branch.  For a finite late target
set `Q`, anchor-avoiding full translate recurrence is impossible. -/
theorem IsExactTupleAsymptoticBasis.eventually_not_anchorAvoidingFullTransversalsOnFiniteTranslates
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ Q : Finset ℕ, (∀ q ∈ Q, N ≤ q) →
      ¬ HasAnchorAvoidingFullTransversalsOnFiniteTranslates A k Q := by
  obtain ⟨N, hbound⟩ :=
    hbasis.eventually_card_alignedSuccessorDestroyers_over_targets_le
  refine ⟨N, ?_⟩
  intro Q hQN hrecur
  obtain ⟨𝒯, hfamily, hcard⟩ :=
    exists_anchorAvoidingAlignedDestroyerFamily_card hrecur
      (k * Q.card + 1)
  have hle : 𝒯.card ≤ k * Q.card := by
    apply hbound Q hQN 𝒯 hfamily.1
    intro T hT𝒯
    obtain ⟨q, n, a, hdestroy, haA, haT, hnqa⟩ :=
      hfamily.2.2.2 T hT𝒯
    refine ⟨q, n, a, hdestroy, haA, haT, ?_, ?_⟩
    · omega
    · omega
  omega

/- If the translate anchor is larger than the predecessor target, every
order-`k` support avoids the anchor.  Hence failure of `T.erase a` to destroy
`q` supplies a support disjoint from the whole of `T`. -/
theorem additiveAnchorContaining_predecessorDestroyer_or_survivingSupport
    {A : Set ℕ} {k q a : ℕ} {T : Finset ℕ}
    (hqa : q < a) :
    DestroysAt
        (additiveSupportFamily A k) ((T.erase a : Finset ℕ) : Set ℕ) q ∨
      ∃ E ∈ additiveSupportFamily A k q,
        Disjoint (E : Set ℕ) (T : Set ℕ) := by
  by_cases hdestroy :
      DestroysAt
        (additiveSupportFamily A k) ((T.erase a : Finset ℕ) : Set ℕ) q
  · exact Or.inl hdestroy
  · right
    obtain ⟨E, hER, hEerase⟩ := not_destroysAt_iff.mp hdestroy
    refine ⟨E, hER, ?_⟩
    rw [Set.disjoint_left]
    intro x hxE hxT
    by_cases hxa : x = a
    · subst x
      have haq : a ≤ q :=
        additiveSupportFamily_supportsBounded A k q E hER a hxE
      omega
    · apply Set.disjoint_left.mp hEerase hxE
      exact Finset.mem_coe.mpr <|
        Finset.mem_erase.mpr ⟨hxa, Finset.mem_coe.mp hxT⟩

/- Cell form of the same boundedness argument: if erasing a point larger than
the target does not destroy that target, the surviving support avoids the
entire original cell, because no support vertex can equal the large point. -/
theorem additiveErasedLargePoint_survivingSupport
    {A : Set ℕ} {k q a : ℕ} {C : Finset ℕ}
    (hqa : q < a)
    (hnot : ¬ DestroysAt
      (additiveSupportFamily A k)
      ((C.erase a : Finset ℕ) : Set ℕ) q) :
    ∃ E ∈ additiveSupportFamily A k q,
      Disjoint (E : Set ℕ) (C : Set ℕ) := by
  obtain ⟨E, hER, hEerase⟩ := not_destroysAt_iff.mp hnot
  refine ⟨E, hER, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxC
  by_cases hxa : x = a
  · subst x
    have haq : a ≤ q :=
      additiveSupportFamily_supportsBounded A k q E hER a hxE
    omega
  · apply Set.disjoint_left.mp hEerase hxE
    exact Finset.mem_coe.mpr <|
      Finset.mem_erase.mpr ⟨hxa, Finset.mem_coe.mp hxC⟩

/- A late finite certificate with two distinct blocks carrying supports which
avoid their dedicated anchored row cells. -/
def HasLateCertificateWithTwoDedicatedRepairBlocks
    (A : Set ℕ) (k : ℕ) : Prop :=
    ∃ N, ∃ Q : Finset ℕ, Q.Nonempty ∧
      (∀ q ∈ Q, N ≤ q) ∧
      ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
        (∀ s : BlockSelector F, ∃ q ∈ Q,
          DestroysAt
            (additiveSupportFamily A k) (selectedSet s) q) ∧
        ∃ i j, i ≠ j ∧
          ∃ C D : Finset ℕ, C ⊆ F i ∧ D ⊆ F j ∧
            ∃ qC qD : {q // q ∈ Q},
              ∃ E ∈ additiveSupportFamily A k qC.1,
                Disjoint (E : Set ℕ) (C : Set ℕ) ∧
              ∃ G ∈ additiveSupportFamily A k qD.1,
                Disjoint (G : Set ℕ) (D : Set ℕ)

/- The complete consequence presently obtainable from the anchored diagonal
and strong deletion: the returned late certificate has two distinct
dedicated row blocks, each carrying a support of its assigned target which
avoids the entire anchored cell in that block. -/
theorem IsStronglyMinimalExactBasis.exists_certificate_two_dedicatedRepairBlocks_of_anchoredDiagonal
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k) :
    HasLateCertificateWithTwoDedicatedRepairBlocks A k := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  have hpartition : HasCertificateAlignedAnchoredCellRowPartition A k :=
    hdiag.exists_rowPartition
  obtain ⟨Q, hQ, hQN, F, P, hcert, 𝒞,
      hfamily, hcard, locate, hlocate, hcell⟩ :=
    hpartition.finiteCertificateWithDedicatedRow hminimal.2 N
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q := fun q =>
    let w := hN q.1 (hQN q.1 q.2)
    ⟨w.choose, w.choose_spec.1⟩
  have hcardLower : k * Q.card + 1 ≤ 𝒞.card := by
    rw [hcard]
    simp only [two_mul, Nat.add_mul]
    omega
  obtain ⟨anchor, target, hdata, C, D, hCD, hCnot, hDnot⟩ :=
    exists_anchorData_two_nonDestroyingErasures_of_certificate
      P hcert hfamily hcardLower locate hlocate hcell c
  obtain ⟨TC, nC, hCeq, hCaLower, _hCaA, _hnC, _hTCdestroy⟩ :=
    hdata C
  obtain ⟨TD, nD, hDeq, hDaLower, _hDaA, _hnD, _hTDdestroy⟩ :=
    hdata D
  have hqCa : (target C).1 < anchor C := by
    have hqmax : (target C).1 ≤ Q.max' hQ :=
      Finset.le_max' Q (target C).1 (target C).2
    omega
  have hqDa : (target D).1 < anchor D := by
    have hqmax : (target D).1 ≤ Q.max' hQ :=
      Finset.le_max' Q (target D).1 (target D).2
    omega
  obtain ⟨E, hER, hEC⟩ :=
    additiveErasedLargePoint_survivingSupport hqCa hCnot
  obtain ⟨G, hGR, hGD⟩ :=
    additiveErasedLargePoint_survivingSupport hqDa hDnot
  have hlocne : locate C ≠ locate D := by
    intro hloc
    exact hCD (hlocate hloc)
  exact ⟨N, Q, hQ, hQN, F, P, hcert,
    locate C, locate D, hlocne, C.1, D.1,
    hcell C, hcell D, target C, target D,
    E, hER, hEC, G, hGR, hGD⟩

/- Exhaustive strong-minimality consequence of the relative analysis.  The
growth branch remains relative to one `Q + A`; otherwise the anchored
diagonal and certificate count produce two dedicated repair blocks. -/
theorem IsStronglyMinimalExactBasis.finiteTranslateGrowth_or_twoDedicatedRepairBlocks
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k) :
    HasSomeFiniteTranslateMatchingGrowth A k ∨
      HasLateCertificateWithTwoDedicatedRepairBlocks A k := by
  obtain hgrowth | hdiag :=
    finiteTranslateMatchingGrowth_or_diagonalAnchoredCellRows hminimal.1
  · exact Or.inl hgrowth
  · exact Or.inr <|
      hminimal.exists_certificate_two_dedicatedRepairBlocks_of_anchoredDiagonal
        hdiag

/- Full additive successor destruction at `n = q + a` has an exact anchor
dichotomy.  If the anchor is absent, the original transversal descends.  If
the anchor is present and `q < a`, then either erasing it still destroys `q`,
or an order-`k` support of `q` survives the entire transversal. -/
theorem additiveFullTranslateTransversal_anchorDichotomy
    {A : Set ℕ} {k q a n : ℕ} {T : Finset ℕ}
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 1)) (T : Set ℕ) n)
    (haA : a ∈ A) (hnqa : n = q + a) (hqa : q < a) :
    (a ∉ T ∧
      DestroysAt (additiveSupportFamily A k) (T : Set ℕ) q) ∨
      (a ∈ T ∧
        (DestroysAt
            (additiveSupportFamily A k)
            ((T.erase a : Finset ℕ) : Set ℕ) q ∨
          ∃ E ∈ additiveSupportFamily A k q,
            Disjoint (E : Set ℕ) (T : Set ℕ))) := by
  by_cases haT : a ∈ T
  · exact Or.inr ⟨haT,
      additiveAnchorContaining_predecessorDestroyer_or_survivingSupport
        hqa⟩
  · left
    refine ⟨haT, ?_⟩
    have han : a ≤ n := by omega
    have hnsub : n - a = q := by omega
    rw [← hnsub]
    exact additiveSuccessorTransversalsDescend A k
      T n hdestroy a haA (by simpa using haT) han

/- A repair cell necessarily lies in the internal-anchor branch.  If its
anchor were absent from the moving core, successor descent would say that the
anchor erasure destroys the predecessor, contradicting the repair property. -/
theorem anchor_mem_core_of_nonDestroying_cellErasure
    {A : Set ℕ} {k q a n : ℕ} {C T : Finset ℕ}
    (hCeq : C = insert a T)
    (hdestroy : DestroysAt
      (additiveSupportFamily A (k + 1)) (T : Set ℕ) n)
    (haA : a ∈ A) (hnqa : n = q + a) (hqa : q < a)
    (hnot : ¬ DestroysAt
      (additiveSupportFamily A k)
      ((C.erase a : Finset ℕ) : Set ℕ) q) :
    a ∈ T := by
  obtain houtside | hins :=
    additiveFullTranslateTransversal_anchorDichotomy
      hdestroy haA hnqa hqa
  · apply (hnot ?_).elim
    simpa [hCeq, houtside.1] using houtside.2
  · exact hins.1

/- The exact outcome of combining a minimal strong-deletion certificate with
an oversized dedicated row: more than `k` pairwise-disjoint cells share one
predecessor target and have surviving predecessor supports.  Crucially, every
one of their translate anchors is forced to lie inside its moving successor
destroyer. -/
def HasLateCertificateWithManyCommonTargetInternalAnchorCells
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N, ∃ Q : Finset ℕ, ∃ hQ : Q.Nonempty,
    (∀ q ∈ Q, N ≤ q) ∧
    ∃ F : ℕ → Finset ℕ, ∃ _P : IsFiniteBlockPartition A F,
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A k) (selectedSet s) q) ∧
      ∃ 𝒞 : Finset (Finset ℕ),
        IsAnchoredAlignedTranslateCellFamily
            A k Q (Q.max' hQ + 1) 𝒞 ∧
        𝒞.card = 2 * k * Q.card + 1 ∧
        ∃ locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ,
          Function.Injective locate ∧
          (∀ C, C.1 ⊆ F (locate C)) ∧
          ∃ q : {q // q ∈ Q},
            ∃ I : Finset {C : Finset ℕ // C ∈ 𝒞},
              k < I.card ∧
              ∀ C ∈ I, ∃ T : Finset ℕ, ∃ n a,
                C.1 = insert a T ∧
                Q.max' hQ + 1 ≤ a ∧ a ∈ A ∧
                n = q.1 + a ∧
                DestroysAt
                  (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
                a ∈ T ∧
                ∃ E ∈ additiveSupportFamily A k q.1,
                  Disjoint (E : Set ℕ) (C.1 : Set ℕ)

theorem IsStronglyMinimalExactBasis.exists_manyCommonTarget_internalAnchorCells_of_anchoredDiagonal
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hdiag : HasDiagonalAnchoredAlignedTranslateCellRows A k) :
    HasLateCertificateWithManyCommonTargetInternalAnchorCells A k := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hminimal.1
  have hpartition : HasCertificateAlignedAnchoredCellRowPartition A k :=
    hdiag.exists_rowPartition
  obtain ⟨Q, hQ, hQN, F, P, hcert, hlocalized, 𝒞,
      hfamily, hcard, locate, hlocate, hcell⟩ :=
    hpartition.finiteMinimalCertificateWithDedicatedRow hminimal.2 N
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q := fun q =>
    let w := hN q.1 (hQN q.1 q.2)
    ⟨w.choose, w.choose_spec.1⟩
  obtain ⟨anchor, target, hdata, q, I, hIcard, hI⟩ :=
    exists_commonTarget_many_nonDestroyingErasures_of_minimalCertificate
      hQ P hcert hlocalized hfamily hcard locate hlocate hcell c
  refine ⟨N, Q, hQ, hQN, F, P, hcert, 𝒞, hfamily, hcard,
    locate, hlocate, hcell, q, I, hIcard, ?_⟩
  intro C hCI
  obtain ⟨htarget, hnot⟩ := hI C hCI
  obtain ⟨T, n, hCeq, haLower, haA, hnqa, hdestroy⟩ := hdata C
  have hnqa' : n = q.1 + anchor C := by
    rw [← htarget]
    exact hnqa
  have hqmax : q.1 ≤ Q.max' hQ :=
    Finset.le_max' Q q.1 q.2
  have hqa : q.1 < anchor C := by omega
  have haT : anchor C ∈ T :=
    anchor_mem_core_of_nonDestroying_cellErasure
      hCeq hdestroy haA hnqa' hqa hnot
  obtain ⟨E, hER, hEC⟩ :=
    additiveErasedLargePoint_survivingSupport hqa hnot
  exact ⟨T, n, anchor C, hCeq, haLower, haA, hnqa',
    hdestroy, haT, E, hER, hEC⟩

/- Strengthened exhaustive conclusion.  The non-growth branch now has more
than `k` cells over one common target, but the anchors are internal; this is
exactly the polarity opposite to the common-predecessor bridge. -/
theorem IsStronglyMinimalExactBasis.finiteTranslateGrowth_or_manyCommonTarget_internalAnchorCells
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k) :
    HasSomeFiniteTranslateMatchingGrowth A k ∨
      HasLateCertificateWithManyCommonTargetInternalAnchorCells A k := by
  obtain hgrowth | hdiag :=
    finiteTranslateMatchingGrowth_or_diagonalAnchoredCellRows hminimal.1
  · exact Or.inl hgrowth
  · exact Or.inr <|
      hminimal.exists_manyCommonTarget_internalAnchorCells_of_anchoredDiagonal
        hdiag

/- An oversized certificate-aligned row cannot consist entirely of
predecessor destroyers.  After choosing one order-`k` support for each late
target in `Q`, the usual `k * |Q|` injection bounds all cores for which either
the anchor is absent or erasing the anchor still destroys the predecessor.
Thus one core has an internal large anchor, its erasure is not a predecessor
destroyer, and an order-`k` support survives the whole core. -/
theorem IsExactTupleAsymptoticBasis.exists_anchorContainingRepairCase_of_largeRow
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ (Q : Finset ℕ) (hQ : Q.Nonempty),
      (∀ q ∈ Q, N ≤ q) →
      ∀ 𝒯 : Finset (Finset ℕ),
        IsFullAlignedTranslateDestroyerFamily
          A k Q (Q.max' hQ + 1) 𝒯 →
        k * Q.card < 𝒯.card →
        ∃ T ∈ 𝒯, ∃ q : {m // m ∈ Q}, ∃ n a,
          Q.max' hQ + 1 ≤ a ∧ a ∈ A ∧ n = q.1 + a ∧
          DestroysAt
            (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
          a ∈ T ∧
          ¬ DestroysAt
            (additiveSupportFamily A k)
            ((T.erase a : Finset ℕ) : Set ℕ) q.1 ∧
          ∃ E ∈ additiveSupportFamily A k q.1,
            Disjoint (E : Set ℕ) (T : Set ℕ) := by
  classical
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨N, ?_⟩
  intro Q hQ hQN 𝒯 hfamily hlarge
  have hwitness : ∀ T : {T // T ∈ 𝒯},
      ∃ q : {m // m ∈ Q}, ∃ n a,
        Q.max' hQ + 1 ≤ a ∧ a ∈ A ∧ n = q.1 + a ∧
        DestroysAt
          (additiveSupportFamily A (k + 1)) (T.1 : Set ℕ) n := by
    intro T
    exact hfamily.2.2.2 T.1 T.2
  choose target successor anchor haLower haA hnqa hdestroySucc using hwitness
  have hqa : ∀ T : {T // T ∈ 𝒯}, (target T).1 < anchor T := by
    intro T
    have hqmax : (target T).1 ≤ Q.max' hQ :=
      Finset.le_max' Q (target T).1 (target T).2
    have halower := haLower T
    omega
  let D : {T // T ∈ 𝒯} → Finset ℕ := fun T =>
    if anchor T ∈ T.1 then T.1.erase (anchor T) else T.1
  by_contra hrepair
  have hdestroyD : ∀ T : {T // T ∈ 𝒯},
      DestroysAt
        (additiveSupportFamily A k) (D T : Set ℕ) (target T).1 := by
    intro T
    by_cases haT : anchor T ∈ T.1
    · by_cases herase :
          DestroysAt
            (additiveSupportFamily A k)
            ((T.1.erase (anchor T) : Finset ℕ) : Set ℕ) (target T).1
      · simpa [D, haT] using herase
      · obtain hdestroy | hsurvive :=
          additiveAnchorContaining_predecessorDestroyer_or_survivingSupport
            (A := A) (k := k) (T := T.1) (hqa T)
        · exact (herase hdestroy).elim
        · exfalso
          apply hrepair
          exact ⟨T.1, T.2, target T, successor T, anchor T,
            haLower T, haA T, hnqa T, hdestroySucc T,
            haT, herase, hsurvive⟩
    · have heq := hnqa T
      have han : anchor T ≤ successor T := by omega
      have hnsub : successor T - anchor T = (target T).1 := by omega
      have hdescend :
          DestroysAt
            (additiveSupportFamily A k) (T.1 : Set ℕ) (target T).1 := by
        rw [← hnsub]
        exact additiveSuccessorTransversalsDescend A k
          T.1 (successor T) (hdestroySucc T) (anchor T)
          (haA T) (by simpa using haT) han
      simpa [D, haT] using hdescend
  have hDsubset : ∀ T : {T // T ∈ 𝒯}, D T ⊆ T.1 := by
    intro T
    by_cases haT : anchor T ∈ T.1
    · simpa [D, haT] using Finset.erase_subset (anchor T) T.1
    · simp [D, haT]
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q =>
      let w := hN q.1 (hQN q.1 q.2)
      ⟨w.choose, w.choose_spec.1⟩
  let U := finiteSupportChoiceUnion c
  have hhit : ∀ T : {T // T ∈ 𝒯},
      ∃ x, x ∈ (c (target T)).1 ∧ x ∈ D T := by
    intro T
    obtain ⟨x, hxE, hxD⟩ :=
      Set.not_disjoint_iff.mp
        (hdestroyD T (c (target T)).1 (c (target T)).2)
    exact ⟨x, hxE, Finset.mem_coe.mp hxD⟩
  choose pick hpickE hpickD using hhit
  let pickU : ∀ T : {T // T ∈ 𝒯}, {x // x ∈ U} := fun T =>
    ⟨pick T, finiteSupportChoice_subset_union c (target T) (hpickE T)⟩
  have hpickT : ∀ T : {T // T ∈ 𝒯}, (pickU T).1 ∈ T.1 := by
    intro T
    exact hDsubset T (hpickD T)
  have hpick_injective : Function.Injective pickU := by
    intro T T' hpick
    apply Subtype.ext
    by_contra hTT'
    have hdisj : Disjoint T.1 T'.1 := hfamily.1 T.2 T'.2 hTT'
    have hx : (pickU T).1 = (pickU T').1 :=
      congrArg Subtype.val hpick
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pickU T).1, hpickT T, hx ▸ hpickT T'⟩) hdisj
  have hcardU : 𝒯.card ≤ U.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pickU hpick_injective
  have hUbound : U.card ≤ k * Q.card :=
    finiteSupportChoiceUnion_card_le
      (additiveSupportFamily_cardAtMost A k) c
  exact (not_lt_of_ge (hcardU.trans hUbound)) hlarge

/- If the favorable anchor-containing alternative occurs simultaneously for
every `q ∈ Q` relative to one nonempty block core `T`, the resulting supports
form a finite support choice whose union does not cover that block. -/
theorem exists_supportChoice_repairingBlock_of_anchorContainingCases
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    {F : ℕ → Finset ℕ} {i : ℕ} {T : Finset ℕ}
    (hcore : T ⊆ F i) (hT : T.Nonempty)
    (hanchor : ∀ q : {m // m ∈ Q}, ∃ a,
      q.1 < a ∧ a ∈ T ∧
        ¬ DestroysAt
          (additiveSupportFamily A k)
          ((T.erase a : Finset ℕ) : Set ℕ) q.1) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A k) Q,
      (F i \ finiteSupportChoiceUnion c).Nonempty := by
  classical
  have hsupport : ∀ q : {m // m ∈ Q},
      ∃ E, E ∈ additiveSupportFamily A k q.1 ∧
        Disjoint (E : Set ℕ) (T : Set ℕ) := by
    intro q
    obtain ⟨a, hqa, _haT, hnotdestroy⟩ := hanchor q
    rcases
        additiveAnchorContaining_predecessorDestroyer_or_survivingSupport
          (A := A) (k := k) (T := T) hqa with
      hdestroy | hsurvive
    · exact (hnotdestroy hdestroy).elim
    · exact hsurvive
  choose support hsupportR hsupportDisjoint using hsupport
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q => ⟨support q, hsupportR q⟩
  refine ⟨c, ?_⟩
  exact block_difference_supportChoiceUnion_nonempty_of_coreDisjoint
    c hcore hT (fun q => hsupportDisjoint q)

/- The apparently stronger simultaneous repair problem has a simple additive
solution when every core has an anchor for every certified target.  Use the
anchor belonging to the largest target in `Q`: it is larger than every target
in `Q`, whereas every vertex of a support of `q` is at most `q`.  Consequently
that anchor is omitted by the union of *any* chosen supports, simultaneously
for all cores. -/
theorem exists_supportChoice_repairingAllBlocks_of_anchorContainingCases
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    {F T : ℕ → Finset ℕ}
    (hQ : Q.Nonempty)
    (hcore : ∀ i, T i ⊆ F i)
    (hanchor : ∀ i, ∀ q : {m // m ∈ Q}, ∃ a,
      q.1 < a ∧ a ∈ T i ∧
        ¬ DestroysAt
          (additiveSupportFamily A k)
          (((T i).erase a : Finset ℕ) : Set ℕ) q.1) :
    ∃ c : FiniteSupportChoice (additiveSupportFamily A k) Q,
      ∀ i, (F i \ finiteSupportChoiceUnion c).Nonempty := by
  classical
  have hsupport : ∀ q : {m // m ∈ Q},
      ∃ E, E ∈ additiveSupportFamily A k q.1 := by
    intro q
    obtain ⟨a, _hqa, _haT, hnotdestroy⟩ := hanchor 0 q
    obtain ⟨E, hER, _hdisjoint⟩ :=
      not_destroysAt_iff.mp hnotdestroy
    exact ⟨E, hER⟩
  choose support hsupportR using hsupport
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q => ⟨support q, hsupportR q⟩
  refine ⟨c, ?_⟩
  intro i
  let qmax : {m // m ∈ Q} := ⟨Q.max' hQ, Q.max'_mem hQ⟩
  obtain ⟨a, hmaxa, haT, _hnotdestroy⟩ := hanchor i qmax
  refine ⟨a, Finset.mem_sdiff.mpr ⟨hcore i haT, ?_⟩⟩
  intro haU
  obtain ⟨q, _hqattach, haE⟩ := Finset.mem_biUnion.mp haU
  have haq : a ≤ q.1 :=
    additiveSupportFamily_supportsBounded A k q.1
      (c q).1 (c q).2 a haE
  have hqmax : q.1 ≤ Q.max' hQ := Finset.le_max' Q q.1 q.2
  exact (not_lt_of_ge (haq.trans hqmax)) hmaxa

/- Additive boundedness localizes every block covered by a finite support
choice: all of its vertices lie below the largest chosen target. -/
theorem block_vertices_le_max_of_subset_supportChoiceUnion
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hQ : Q.Nonempty)
    {F : ℕ → Finset ℕ}
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q)
    {i : ℕ} (hi : F i ⊆ finiteSupportChoiceUnion c) :
    ∀ x ∈ F i, x ≤ Q.max' hQ := by
  intro x hxF
  obtain ⟨q, _hqattach, hxE⟩ :=
    Finset.mem_biUnion.mp (hi hxF)
  exact
    (additiveSupportFamily_supportsBounded A k q.1
      (c q).1 (c q).2 x hxE).trans
      (Finset.le_max' Q q.1 q.2)

/- Hence a finite selector certificate can only be witnessed, for any fixed
support choice, by a block wholly contained in the initial interval ending at
`max Q`.  This is the precise finite-exception localization left after the
large-anchor repair. -/
theorem exists_boundedBlock_of_additiveSelectorCertificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hQ : Q.Nonempty)
    {F : ℕ → Finset ℕ}
    (hcert : ∀ s : BlockSelector F,
      ∃ q ∈ Q,
        DestroysAt
          (additiveSupportFamily A k) (selectedSet s) q)
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ i, ∀ x ∈ F i, x ≤ Q.max' hQ := by
  obtain ⟨i, hi⟩ :=
    exists_block_subset_supportChoiceUnion_of_certificate hcert c
  exact ⟨i,
    block_vertices_le_max_of_subset_supportChoiceUnion hQ c hi⟩

/- Certificate localization is excluded not only on the row indexed by the
certificate itself, but on every anchored row starting above `max Q`, even
when that row represents an unrelated finite target set `P`. -/
theorem exists_boundedBlock_outside_lateAnchoredRow_of_certificate
    {A : Set ℕ} {k : ℕ} {Q P : Finset ℕ}
    (hQ : Q.Nonempty)
    {F : ℕ → Finset ℕ} {𝒞 : Finset (Finset ℕ)} {L : ℕ}
    (hcert : ∀ s : BlockSelector F,
      ∃ q ∈ Q, DestroysAt
        (additiveSupportFamily A k) (selectedSet s) q)
    (hfamily : IsAnchoredAlignedTranslateCellFamily A k P L 𝒞)
    (hLate : Q.max' hQ < L)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ i, (∀ x ∈ F i, x ≤ Q.max' hQ) ∧
      ∀ C : {C : Finset ℕ // C ∈ 𝒞}, locate C ≠ i := by
  obtain ⟨i, hi⟩ :=
    exists_boundedBlock_of_additiveSelectorCertificate hQ hcert c
  refine ⟨i, hi, ?_⟩
  intro C hloc
  obtain ⟨T, _q, _n, a, hCeq, haLower,
      _haA, _hnqa, _hdestroy⟩ :=
    hfamily.2.2.2 C.1 C.2
  have haC : a ∈ C.1 := by
    rw [hCeq]
    exact Finset.mem_insert_self a T
  have haF : a ∈ F i := by
    rw [← hloc]
    exact hcell C haC
  exact (not_lt_of_ge (hi a haF)) (lt_of_lt_of_le hLate haLower)

/- The support-union witness supplied by a certificate cannot lie on its
dedicated anchored row.  Every support selected for a target in `Q` is
bounded by `max Q`, whereas every dedicated cell contains an anchor strictly
above `max Q`.  Thus localization onto the dedicated row is not merely
unproved in this formulation; it is excluded by additive boundedness. -/
theorem exists_boundedBlock_outside_dedicatedAnchoredRow_of_certificate
    {A : Set ℕ} {k : ℕ} {Q : Finset ℕ}
    (hQ : Q.Nonempty)
    {F : ℕ → Finset ℕ} {𝒞 : Finset (Finset ℕ)}
    (hcert : ∀ s : BlockSelector F,
      ∃ q ∈ Q, DestroysAt
        (additiveSupportFamily A k) (selectedSet s) q)
    (hfamily : IsAnchoredAlignedTranslateCellFamily
      A k Q (Q.max' hQ + 1) 𝒞)
    (locate : {C : Finset ℕ // C ∈ 𝒞} → ℕ)
    (hcell : ∀ C : {C : Finset ℕ // C ∈ 𝒞},
      C.1 ⊆ F (locate C))
    (c : FiniteSupportChoice (additiveSupportFamily A k) Q) :
    ∃ i, (∀ x ∈ F i, x ≤ Q.max' hQ) ∧
      ∀ C : {C : Finset ℕ // C ∈ 𝒞}, locate C ≠ i := by
  obtain ⟨i, hi⟩ :=
    exists_boundedBlock_of_additiveSelectorCertificate hQ hcert c
  refine ⟨i, hi, ?_⟩
  intro C hloc
  obtain ⟨T, _q, _n, a, hCeq, haLower,
      _haA, _hnqa, _hdestroy⟩ :=
    hfamily.2.2.2 C.1 C.2
  have haC : a ∈ C.1 := by
    rw [hCeq]
    exact Finset.mem_insert_self a T
  have haF : a ∈ F i := by
    rw [← hloc]
    exact hcell C haC
  have hale := hi a haF
  omega

/- In the moving sequence, write the predecessor cloud of index `i` as the
targets `S.n i - a` with `a ∈ A \ S.T i`.  Beyond the basis threshold, a
single target belongs to the clouds of at most `k` indices. -/
theorem EscapingTransversalSequence.eventually_card_commonPredecessorIndices_le
    {A : Set ℕ} {k : ℕ}
    (S : EscapingTransversalSequence
      (additiveSupportFamily A (k + 1)) A)
    (hbasis : IsExactTupleAsymptoticBasis A k) :
    ∃ N, ∀ q, N ≤ q → ∀ I : Finset ℕ,
      (∀ i ∈ I, ∃ a,
        a ∈ A ∧ a ∉ S.T i ∧ a ≤ S.n i ∧ S.n i - a = q) →
      I.card ≤ k := by
  classical
  obtain ⟨N, hN⟩ := hbasis.eventually_card_alignedDestroyers_le
  refine ⟨N, ?_⟩
  intro q hNq I halign
  have hT_injective : Function.Injective S.T := by
    intro i j hT
    by_contra hij
    obtain ⟨x, hxi⟩ := S.nonempty i
    have hxj : x ∈ S.T j := by
      rw [← hT]
      exact hxi
    exact Finset.disjoint_left.mp (S.disjoint hij) hxi hxj
  let 𝒯 : Finset (Finset ℕ) := I.image S.T
  have hpair : IsMatching 𝒯 := by
    intro T hT T' hT' hTT'
    change Disjoint T T'
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨j, hjI, rfl⟩ := Finset.mem_image.mp hT'
    apply S.disjoint
    intro hij
    subst j
    exact hTT' rfl
  have h𝒯align : ∀ T ∈ 𝒯, ∃ n a,
      DestroysAt
        (additiveSupportFamily A (k + 1)) (T : Set ℕ) n ∧
      a ∈ A ∧ a ∉ T ∧ a ≤ n ∧ n - a = q := by
    intro T hT
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨a, haA, haT, han, hq⟩ := halign i hiI
    exact ⟨S.n i, a, S.destroys i, haA, haT, han, hq⟩
  have hle : 𝒯.card ≤ k := hN q hNq 𝒯 hpair h𝒯align
  change (I.image S.T).card ≤ k at hle
  rwa [Finset.card_image_iff.mpr hT_injective.injOn] at hle

/- This is the exact finite-certificate bridge needed by the common-target
strategy.  It is deliberately stated separately: the selector certificate
and the fact that the blocks contain the moving cores do not syntactically
provide the arithmetic equations `S.n i - a = q`. -/
def AdditiveFiniteCertificateCommonPredecessorBridge
    (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ (S : EscapingTransversalSequence
      (additiveSupportFamily A (k + 1)) A)
    (F : ℕ → Finset ℕ)
    (_P : IsFiniteBlockPartition A F),
    (∀ i, S.T i ⊆ F i) →
    ∀ N (Q : Finset ℕ),
      (∀ q ∈ Q, N ≤ q) →
      (∀ s : BlockSelector F,
        ∃ q ∈ Q,
          DestroysAt
            (additiveSupportFamily A k) (selectedSet s) q) →
      ∃ q ∈ Q, ∃ I : Finset ℕ,
        k < I.card ∧
        ∀ i ∈ I, ∃ a,
          a ∈ A ∧ a ∉ S.T i ∧
          a ≤ S.n i ∧ S.n i - a = q

/- The bridge above is false as stated, already at order one.  The following
explicit sequence uses adjacent exponentially growing blocks.  Its
successor transversals are the upper halves of those blocks; every external
anchor therefore has a predecessor in that same upper half.  Since the upper
halves are pairwise disjoint, a predecessor can belong to only one cloud. -/
private def bridgeCounterB : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * bridgeCounterB i + 2

private def bridgeCounterN (i : ℕ) : ℕ :=
  2 * bridgeCounterB i + 1

private def bridgeCounterT (i : ℕ) : Finset ℕ :=
  Finset.Icc (bridgeCounterB i + 1) (bridgeCounterN i)

private theorem bridgeCounterB_succ (i : ℕ) :
    bridgeCounterB (i + 1) = 2 * bridgeCounterB i + 2 := by
  simp [bridgeCounterB]

private theorem bridgeCounterB_strict : StrictMono bridgeCounterB := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [bridgeCounterB_succ]
  omega

private theorem bridgeCounterN_strict : StrictMono bridgeCounterN := by
  apply strictMono_nat_of_lt_succ
  intro i
  simp only [bridgeCounterN, bridgeCounterB_succ]
  omega

private theorem bridgeCounterT_nonempty (i : ℕ) :
    (bridgeCounterT i).Nonempty := by
  rw [bridgeCounterT, Finset.nonempty_Icc]
  simp only [bridgeCounterN]
  omega

private theorem bridgeCounterT_pairwise :
    Pairwise fun i j =>
      Disjoint (bridgeCounterT i) (bridgeCounterT j) := by
  intro i j hij
  by_cases hijlt : i < j
  · rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' := Finset.mem_Icc.mp hxi
    have hxj' := Finset.mem_Icc.mp hxj
    have hbij : bridgeCounterB (i + 1) ≤ bridgeCounterB j :=
      bridgeCounterB_strict.monotone (Nat.succ_le_of_lt hijlt)
    rw [bridgeCounterB_succ] at hbij
    simp only [bridgeCounterN] at hxi' hxj'
    omega
  · have hjilt : j < i := by omega
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hxi' := Finset.mem_Icc.mp hxi
    have hxj' := Finset.mem_Icc.mp hxj
    have hbji : bridgeCounterB (j + 1) ≤ bridgeCounterB i :=
      bridgeCounterB_strict.monotone (Nat.succ_le_of_lt hjilt)
    rw [bridgeCounterB_succ] at hbji
    simp only [bridgeCounterN] at hxi' hxj'
    omega

private theorem bridgeCounterT_destroys (i : ℕ) :
    DestroysAt
      (additiveSupportFamily (Set.univ : Set ℕ) 2)
      (bridgeCounterT i : Set ℕ) (bridgeCounterN i) := by
  intro E hER
  obtain ⟨v, _hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have hsum : (v 0).1 + (v 1).1 = bridgeCounterN i := by
    simpa [Fin.sum_univ_two] using hvsum
  simp only [bridgeCounterN] at hsum
  by_cases hv0 : bridgeCounterB i < (v 0).1
  · apply Set.not_disjoint_iff.mpr
    refine ⟨(v 0).1, mem_tupleSupport_iff.mpr ⟨0, rfl⟩, ?_⟩
    apply Finset.mem_coe.mpr
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, Nat.le_of_lt_succ (v 0).2⟩
  · apply Set.not_disjoint_iff.mpr
    refine ⟨(v 1).1, mem_tupleSupport_iff.mpr ⟨1, rfl⟩, ?_⟩
    apply Finset.mem_coe.mpr
    apply Finset.mem_Icc.mpr
    exact ⟨by omega, Nat.le_of_lt_succ (v 1).2⟩

private def bridgeCounterSequence : EscapingTransversalSequence
    (additiveSupportFamily (Set.univ : Set ℕ) 2) Set.univ where
  n := bridgeCounterN
  T := bridgeCounterT
  n_strictMono := bridgeCounterN_strict
  subset := by simp
  disjoint := bridgeCounterT_pairwise
  nonempty := bridgeCounterT_nonempty
  destroys := bridgeCounterT_destroys

private theorem bridgeCounterSequence_cloud_unique
    (q i j : ℕ)
    (hi : ∃ a,
      a ∈ (Set.univ : Set ℕ) ∧ a ∉ bridgeCounterSequence.T i ∧
      a ≤ bridgeCounterSequence.n i ∧
      bridgeCounterSequence.n i - a = q)
    (hj : ∃ a,
      a ∈ (Set.univ : Set ℕ) ∧ a ∉ bridgeCounterSequence.T j ∧
      a ≤ bridgeCounterSequence.n j ∧
      bridgeCounterSequence.n j - a = q) :
    i = j := by
  obtain ⟨a, _ha, haT, han, hq⟩ := hi
  obtain ⟨a', _ha', ha'T, ha'n, hq'⟩ := hj
  change a ∉ bridgeCounterT i at haT
  change a ≤ bridgeCounterN i at han
  change bridgeCounterN i - a = q at hq
  change a' ∉ bridgeCounterT j at ha'T
  change a' ≤ bridgeCounterN j at ha'n
  change bridgeCounterN j - a' = q at hq'
  have haSmall : a ≤ bridgeCounterB i := by
    by_contra h
    have haLower : bridgeCounterB i + 1 ≤ a := by omega
    exact haT (Finset.mem_Icc.mpr ⟨haLower, han⟩)
  have ha'Small : a' ≤ bridgeCounterB j := by
    by_contra h
    have ha'Lower : bridgeCounterB j + 1 ≤ a' := by omega
    exact ha'T (Finset.mem_Icc.mpr ⟨ha'Lower, ha'n⟩)
  have hqTi : q ∈ bridgeCounterT i := by
    rw [bridgeCounterT, Finset.mem_Icc]
    simp only [bridgeCounterN] at hq ⊢
    omega
  have hqTj : q ∈ bridgeCounterT j := by
    rw [bridgeCounterT, Finset.mem_Icc]
    simp only [bridgeCounterN] at hq' ⊢
    omega
  by_contra hij
  exact Finset.disjoint_left.mp
    (bridgeCounterT_pairwise hij) hqTi hqTj

private theorem destroysAt_additiveOrderOne_of_mem
    {A B : Set ℕ} {q : ℕ} (hqB : q ∈ B) :
    DestroysAt (additiveSupportFamily A 1) B q := by
  intro E hER
  obtain ⟨v, _hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have hv0 : (v 0).1 = q := by simpa using hvsum
  apply Set.not_disjoint_iff.mpr
  exact ⟨q, mem_tupleSupport_iff.mpr ⟨0, hv0⟩, hqB⟩

/- For the partition generated from the explicit sequence, block zero itself
is an order-one selector certificate: every selector chooses some `q` in
that block, and `{q}` is the unique order-one support of `q`.  The bridge
would make one `q` occur in two predecessor clouds, contradicting their
uniqueness. -/
theorem not_additiveFiniteCertificateCommonPredecessorBridge_univ_one :
    ¬ AdditiveFiniteCertificateCommonPredecessorBridge
      (Set.univ : Set ℕ) 1 := by
  intro hbridge
  obtain ⟨F, P, hcore⟩ :=
    bridgeCounterSequence.exists_finiteBlockPartition
  let Q := F 0
  have hcert : ∀ s : BlockSelector F, ∃ q ∈ Q,
      DestroysAt
        (additiveSupportFamily (Set.univ : Set ℕ) 1)
        (selectedSet s) q := by
    intro s
    let q := (s 0).1
    have hqQ : q ∈ Q := (s 0).2
    refine ⟨q, hqQ, destroysAt_additiveOrderOne_of_mem ?_⟩
    exact ⟨0, rfl⟩
  obtain ⟨q, _hqQ, I, hIlarge, halign⟩ :=
    hbridge bridgeCounterSequence F P hcore 0 Q (by omega) hcert
  have hIle : I.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact bridgeCounterSequence_cloud_unique
      q i j (halign i hi) (halign j hj)
  omega

/- The counterexample is not excluded by strong deletion.  At order one,
deleting an infinite `B ⊆ ℕ` destroys every target belonging to `B`, so there
are arbitrarily late destruction witnesses. -/
theorem strongInfiniteDeletion_additive_univ_one :
    StrongInfiniteDeletion
      (additiveSupportFamily (Set.univ : Set ℕ) 1) Set.univ := by
  intro B _hB hBinfinite N
  obtain ⟨n, hnB, hnN⟩ := hBinfinite.exists_gt N
  exact ⟨n, Nat.le_of_lt hnN,
    destroysAt_additiveOrderOne_of_mem hnB⟩

theorem strongDeletion_and_not_finiteCertificateCommonPredecessorBridge_univ_one :
    StrongInfiniteDeletion
        (additiveSupportFamily (Set.univ : Set ℕ) 1) Set.univ ∧
      ¬ AdditiveFiniteCertificateCommonPredecessorBridge
        (Set.univ : Set ℕ) 1 :=
  ⟨strongInfiniteDeletion_additive_univ_one,
    not_additiveFiniteCertificateCommonPredecessorBridge_univ_one⟩

/- If the bridge above were proved, the finite certificate supplied by strong
deletion would contradict the cloud-multiplicity bound immediately. -/
theorem not_strongInfiniteDeletion_of_finiteCertificateCommonPredecessorBridge
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (S : EscapingTransversalSequence
      (additiveSupportFamily A (k + 1)) A)
    (hbridge : AdditiveFiniteCertificateCommonPredecessorBridge A k) :
    ¬ StrongInfiniteDeletion (additiveSupportFamily A k) A := by
  intro hstrong
  obtain ⟨N, hcloud⟩ :=
    S.eventually_card_commonPredecessorIndices_le hbasis
  obtain ⟨F, P, hcore⟩ := S.exists_finiteBlockPartition
  obtain ⟨Q, hQN, hcert⟩ :=
    (finiteBlockCertificates_of_strongInfiniteDeletion hstrong) F P N
  obtain ⟨q, hqQ, I, hkI, halign⟩ :=
    hbridge S F P hcore N Q hQN hcert
  exact (not_lt_of_ge (hcloud q (hQN q hqQ) I halign)) hkI

/-- Bounded moving transversals at order `k + 1` therefore yield the precise
moving predecessor obstruction at order `k`. -/
theorem additiveBoundedMovingPredecessorTransversals
    {A : Set ℕ} {k : ℕ}
    (hmoving :
      HasBoundedMovingTransversals
        (additiveSupportFamily A (k + 1)) A) :
    HasBoundedMovingPredecessorTransversals
      (additiveSupportFamily A k) A :=
  boundedMovingPredecessorTransversals hmoving
    (additiveSuccessorTransversalsDescend A k)

/-- Thus failure of finite-core matching at order `k + 1` yields all of the
bounded moving predecessor structure recorded in the investigation. -/
theorem additiveBoundedMovingPredecessorTransversals_of_failsFiniteCoreMatching
    {A : Set ℕ} {k : ℕ}
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    HasBoundedMovingPredecessorTransversals
      (additiveSupportFamily A k) A := by
  apply additiveBoundedMovingPredecessorTransversals
  exact boundedMovingTransversals_of_failsFiniteCoreMatching
    (additiveSupportFamily_supportsIn A (k + 1))
    (additiveSupportFamily_supportsNonempty A (Nat.zero_lt_succ k))
    (additiveSupportFamily_cardAtMost A (k + 1))
    hfail

/-- In the additive setting the finite core is only needed to force the
moving transversal to escape old vertices: at a large enough target the
moving part alone hits every successor representation. -/
theorem additiveBoundedEscapingTransversals_of_failsFiniteCoreMatching
    {A : Set ℕ} {k : ℕ}
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    HasBoundedEscapingTransversals
      (additiveSupportFamily A (k + 1)) A :=
  boundedEscapingTransversals_of_outsideTransversals
    (additiveSupportFamily_eventuallyEscapesFiniteCores A (k + 1))
    (boundedMovingOutsideTransversals_of_failsFiniteCoreMatching
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1))
      hfail)

/-- A basis together with failure of finite-core matching yields an infinite
sequence of pairwise-disjoint nonempty successor transversals at increasing
targets. -/
theorem additiveEscapingTransversalSequence_of_failsFiniteCoreMatching
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    Nonempty
      (EscapingTransversalSequence
        (additiveSupportFamily A (k + 1)) A) :=
  exists_escapingTransversalSequence
    (hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis.succ)
    (additiveBoundedEscapingTransversals_of_failsFiniteCoreMatching hfail)

/-- Thus the moving-transversal alternative really does produce a
finite-block partition: every block contains one member of an infinite
pairwise-disjoint sequence of successor transversals.  What is not yet known
is how to select from these blocks while preserving all late order-`k`
targets. -/
theorem additiveExistsFiniteBlockPartitionWithTransversalCores
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    ∃ S : EscapingTransversalSequence
        (additiveSupportFamily A (k + 1)) A,
      ∃ F : ℕ → Finset ℕ,
        IsFiniteBlockPartition A F ∧
        ∀ i, S.T i ⊆ F i := by
  obtain ⟨S⟩ :=
    additiveEscapingTransversalSequence_of_failsFiniteCoreMatching
      hbasis hfail
  obtain ⟨F, P, hcore⟩ := S.exists_finiteBlockPartition
  exact ⟨S, F, P, hcore⟩

/-- For the partition produced from moving transversals, arbitrary finite
late target sets admit chosen order-`k` supports whose union covers only
finitely many whole blocks.  The unresolved selector step is exactly the
strengthening from finitely many exceptional blocks to no exceptional block. -/
theorem additiveMovingProducesAlmostAvoidableBlockPartition
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    ∃ F, ∃ _P : IsFiniteBlockPartition A F, ∃ N,
      ∀ Q : Finset ℕ, (∀ n ∈ Q, N ≤ n) →
        ∃ c : FiniteSupportChoice
            (additiveSupportFamily A k) Q,
          Set.Finite
            {i | F i ⊆ finiteSupportChoiceUnion c} := by
  classical
  obtain ⟨S, F, P, hcore⟩ :=
    additiveExistsFiniteBlockPartitionWithTransversalCores hbasis hfail
  obtain ⟨N, hN⟩ :=
    hasEventuallySurvivingSupport_empty_additive_iff.mpr hbasis
  refine ⟨F, P, N, ?_⟩
  intro Q hQN
  let c : FiniteSupportChoice (additiveSupportFamily A k) Q :=
    fun q =>
      let w := hN q.1 (hQN q.1 q.2)
      ⟨w.choose, w.choose_spec.1⟩
  exact ⟨c, finite_indices_blocks_covered_by_supportChoice P c⟩

/-- These escaping successor transversals descend to escaping transversals
for the translated order-`k` targets `n - a`. -/
theorem additiveBoundedEscapingPredecessorTransversals_of_failsFiniteCoreMatching
    {A : Set ℕ} {k : ℕ}
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A) :
    HasBoundedEscapingPredecessorTransversals
      (additiveSupportFamily A k) A :=
  boundedEscapingPredecessorTransversals
    (additiveBoundedEscapingTransversals_of_failsFiniteCoreMatching hfail)
    (additiveSuccessorTransversalsDescend A k)

/-- The concrete `k = 2` concentration forced by failure of finite-core
matching at order three.  Across each translated cloud `n - a`, the number
of distinct pair supports is uniformly bounded by the size bound for the
escaping transversal. -/
theorem additiveBoundedTranslatedPairSupportCounts_of_failsFiniteCoreMatching
    {A : Set ℕ}
    (hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A 3) A) :
    ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
      ∃ m, ∀ N, ∃ n T,
        N ≤ n ∧
        (∀ x ∈ T, x ∈ A) ∧
        Disjoint T F ∧
        T.card ≤ m ∧
        ∀ a ∈ A, a ∉ T → a ≤ n →
          (additiveSupportFamily A 2 (n - a)).card ≤ m := by
  have hpred :
      HasBoundedEscapingPredecessorTransversals
        (additiveSupportFamily A 2) A :=
    additiveBoundedEscapingPredecessorTransversals_of_failsFiniteCoreMatching
      (k := 2) hfail
  intro F hFA
  obtain ⟨m, hm⟩ := hpred F hFA
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hTA, hTF, hTcard, hdestroy⟩ := hm N
  refine ⟨n, T, hn, hTA, hTF, hTcard, ?_⟩
  intro a haA haT han
  exact le_trans
    (card_supports_le_card_of_matching_of_destroysAt
      (fun E hER =>
        additiveSupportFamily_supportsNonempty A (by omega)
          (n - a) E hER)
      (additiveSupportFamily_two_isMatching A (n - a))
      (hdestroy a haA haT han))
    hTcard

/-- This is the remaining additive combinatorial implication in its shortest
exact form.  The basis premise is necessary: moving transversals alone cannot
produce surviving order-`k` representations if there are none to begin with.
The compactness part is already proved; what remains is to derive finite
selector avoidability from the basis and the bounded moving transversals. -/
def AdditiveMovingTransversalsYieldFiniteAvoidability
    (A : Set ℕ) (k : ℕ) : Prop :=
  IsExactTupleAsymptoticBasis A k →
    HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A (k + 1)) A →
    HasFiniteSelectorAvoidability
      (additiveSupportFamily A k) A

/-- The same missing implication in its concrete block-support-union form. -/
def AdditiveMovingTransversalsYieldBlockSupportUnionAvoidance
    (A : Set ℕ) (k : ℕ) : Prop :=
  IsExactTupleAsymptoticBasis A k →
    HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A (k + 1)) A →
    HasFiniteBlockSupportUnionAvoidance
      (additiveSupportFamily A k) A

/-- The block-support-union conjecture and the finite-selector conjecture are
logically identical; only their presentation differs. -/
theorem additiveMovingBlockSupportUnionKey_iff_finiteAvoidabilityKey
    {A : Set ℕ} {k : ℕ} :
    AdditiveMovingTransversalsYieldBlockSupportUnionAvoidance A k ↔
      AdditiveMovingTransversalsYieldFiniteAvoidability A k := by
  constructor
  · intro hblock hbasis hmoving
    apply finiteSelectorAvoidability_of_blockSupportUnionAvoidance
    exact hblock hbasis hmoving
  · intro hselector hbasis hmoving
    apply blockSupportUnionAvoidance_of_finiteSelectorAvoidability
    exact hselector hbasis hmoving

/-- At order one the moving-transversal alternative cannot occur: cofiniteness
of `A` supplies arbitrarily large disjoint complementary-pair matchings. -/
theorem not_boundedMovingOutsideTransversals_two_of_oneBasis
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 1) :
    ¬ HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A 2) A := by
  intro hmoving
  have hfail :
      FailsFiniteCoreMatching
        (additiveSupportFamily A 2) A :=
    failsFiniteCoreMatching_of_boundedMovingOutsideTransversals hmoving
  exact hfail ∅ (by simp)
    (outsideMatchingTendsToInfinity_pair_of_eventually_mem
      (exactTupleAsymptoticBasis_one_iff.mp hbasis))

/-- Thus the missing moving-transversal implication is verified for `k = 1`
(vacuously, because its moving-transversal hypothesis is impossible). -/
theorem additiveMovingTransversalsYieldFiniteAvoidability_one
    (A : Set ℕ) :
    AdditiveMovingTransversalsYieldFiniteAvoidability A 1 := by
  intro hbasis hmoving
  exact
    (not_boundedMovingOutsideTransversals_two_of_oneBasis
      hbasis hmoving).elim

/-- A proof of the remaining additive implication would immediately produce
the required infinite removable selector. -/
theorem additiveRemovableSelector_of_movingTransversals
    {A : Set ℕ} {k : ℕ}
    (hkey : AdditiveMovingTransversalsYieldFiniteAvoidability A k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hmoving :
      HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A (k + 1)) A) :
    AdmitsRemovableBlockSelector (additiveSupportFamily A k) A :=
  removableBlockSelector_of_finiteSelectorAvoidability
    (hkey hbasis hmoving)

/-- In the block-union presentation, the hypothesized implication produces
the requested partition and removable selector directly. -/
theorem additiveRemovableSelector_of_movingBlockSupportUnionKey
    {A : Set ℕ} {k : ℕ}
    (hkey :
      AdditiveMovingTransversalsYieldBlockSupportUnionAvoidance A k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hmoving :
      HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A (k + 1)) A) :
    AdmitsRemovableBlockSelector (additiveSupportFamily A k) A :=
  removableBlockSelector_of_blockSupportUnionAvoidance
    (hkey hbasis hmoving)

/-- The proposed moving-transversal lemma would rule out failure of
finite-core matching for every strongly minimal exact basis.  This is the
formal contrapositive reduction in the investigation. -/
theorem not_failsFiniteCoreMatching_of_strongMinimal_of_movingKey
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hkey : AdditiveMovingTransversalsYieldFiniteAvoidability A k) :
    ¬ FailsFiniteCoreMatching
        (additiveSupportFamily A (k + 1)) A := by
  intro hfail
  have hmoving :
      HasBoundedMovingOutsideTransversals
        (additiveSupportFamily A (k + 1)) A :=
    boundedMovingOutsideTransversals_of_failsFiniteCoreMatching
      (additiveSupportFamily_supportsIn A (k + 1))
      (additiveSupportFamily_cardAtMost A (k + 1))
      hfail
  have havoid :
      HasFiniteSelectorAvoidability
        (additiveSupportFamily A k) A :=
    hkey hminimal.1 hmoving
  exact
    (finiteSelectorAvoidability_iff_not_strongInfiniteDeletion.mp havoid)
      hminimal.2

/-- Equivalently, the unresolved moving-transversal lemma would force
matching growth outside at least one finite core. -/
theorem exists_finiteCore_outsideMatching_of_strongMinimal_of_movingKey
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hkey : AdditiveMovingTransversalsYieldFiniteAvoidability A k) :
    ∃ F : Finset ℕ,
      (F : Set ℕ) ⊆ A ∧
        OutsideMatchingTendsToInfinity
          (additiveSupportFamily A (k + 1)) F := by
  have hnot :=
    not_failsFiniteCoreMatching_of_strongMinimal_of_movingKey
      hminimal hkey
  unfold FailsFiniteCoreMatching at hnot
  push Not at hnot
  obtain ⟨F, hFA, hgrowth⟩ := hnot
  exact ⟨F, hFA, hgrowth⟩

/-- Supplying the one unresolved moving-transversal-to-selector lemma closes
the complete positive argument: an infinite subset can be deleted while
preserving the exact basis property at order `k + 1`. -/
theorem exists_infiniteDeletion_succBasis_of_strongMinimal_of_movingKey
    {A : Set ℕ} {k : ℕ}
    (hminimal : IsStronglyMinimalExactBasis A k)
    (hkey : AdditiveMovingTransversalsYieldFiniteAvoidability A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨F, _hFA, hgrowth⟩ :=
    exists_finiteCore_outsideMatching_of_strongMinimal_of_movingKey
      hminimal hkey
  obtain ⟨B, hBA, hB, _hBF, hsurvive⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutside
      (C := A)
      (R := additiveSupportFamily A (k + 1))
      (F := F)
      (additiveSupportFamily_supportsBounded A (k + 1))
      (matchingTendsToInfinityOutside_of_outsideMatching hgrowth)
      (hminimal.1.unboundedOutside F)
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupport_additive_iff.mp hsurvive⟩

/-- The resulting unconditional `k = 1` case: every exact order-one basis
admits an infinite deletion that remains an exact order-two basis. -/
theorem exists_infiniteDeletion_twoBasis_of_oneBasis
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 1) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 2 := by
  have hgrowth :
      OutsideMatchingTendsToInfinity
        (additiveSupportFamily A 2) ∅ :=
    outsideMatchingTendsToInfinity_pair_of_eventually_mem
      (exactTupleAsymptoticBasis_one_iff.mp hbasis)
  obtain ⟨B, hBA, hB, _hdisj, hsurvive⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutside
      (C := A)
      (R := additiveSupportFamily A 2)
      (F := ∅)
      (additiveSupportFamily_supportsBounded A 2)
      (matchingTendsToInfinityOutside_of_outsideMatching hgrowth)
      (hbasis.unboundedOutside ∅)
  exact ⟨B, hBA, hB,
    hasEventuallySurvivingSupport_additive_iff.mp hsurvive⟩

/-- The complete conditional reduction, stated with the original list-based
asymptotic-basis definition. -/
theorem exists_infiniteDeletion_succBasis_of_originalHypotheses_of_movingKey
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsAsymptoticBasis A k)
    (hstrong :
      StrongInfiniteDeletion (additiveSupportFamily A k) A)
    (hkey : AdditiveMovingTransversalsYieldFiniteAvoidability A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsAsymptoticBasis (A \ B) (k + 1) := by
  obtain ⟨B, hBA, hB, hsucc⟩ :=
    exists_infiniteDeletion_succBasis_of_strongMinimal_of_movingKey
      (A := A) (k := k)
      ⟨isAsymptoticBasis_iff_exactTuple.mp hbasis, hstrong⟩
      hkey
  exact ⟨B, hBA, hB,
    isAsymptoticBasis_iff_exactTuple.mpr hsucc⟩

/-- The same complete conditional proof when the hypothesized implication is
stated as blockwise support-union avoidance. -/
theorem exists_infiniteDeletion_succBasis_of_originalHypotheses_of_blockKey
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsAsymptoticBasis A k)
    (hstrong :
      StrongInfiniteDeletion (additiveSupportFamily A k) A)
    (hkey :
      AdditiveMovingTransversalsYieldBlockSupportUnionAvoidance A k) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsAsymptoticBasis (A \ B) (k + 1) :=
  exists_infiniteDeletion_succBasis_of_originalHypotheses_of_movingKey
    hbasis hstrong
    (additiveMovingBlockSupportUnionKey_iff_finiteAvoidabilityKey.mp hkey)

/-- The unconditional `k = 1` result in the original list-based API. -/
theorem exists_infiniteDeletion_twoBasis_of_orderOneBasis
    {A : Set ℕ}
    (hbasis : IsAsymptoticBasis A 1) :
    ∃ B, B ⊆ A ∧ B.Infinite ∧
      IsAsymptoticBasis (A \ B) 2 := by
  obtain ⟨B, hBA, hB, htwo⟩ :=
    exists_infiniteDeletion_twoBasis_of_oneBasis
      (isAsymptoticBasis_iff_exactTuple.mp hbasis)
  exact ⟨B, hBA, hB,
    isAsymptoticBasis_iff_exactTuple.mpr htwo⟩

end Erdos881
