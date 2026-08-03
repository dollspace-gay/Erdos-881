import Erdos881.DirectTripleRepairs
import Erdos881.InternalAnchorOrderTwo

namespace Erdos881

/-- Every red-red pair sum has either an order-two support not wholly red,
or a direct order-three support wholly blue. -/
def HasHybridPairTripleRepairs (A B : Set ℕ) : Prop :=
  ∀ x ∈ B, ∀ y ∈ B,
    (∃ E ∈ additiveSupportFamily A 2 (x + y),
      ¬ (E : Set ℕ) ⊆ B) ∨
    ∃ G ∈ additiveSupportFamily A 3 (x + y),
      Disjoint (G : Set ℕ) B

/-- Hybrid repairs supply the mixed pair-or-blue-triple bridge. -/
theorem eventuallyPairIndependentOrBlueTriple_of_hybridRepairs
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hrepair : HasHybridPairTripleRepairs A B) :
    IsEventuallyPairIndependentOrBlueTriple A B := by
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨v, hvA, hvsum⟩ := hN n hn
  have hsum : v 0 + v 1 = n := by
    simpa [Fin.sum_univ_two] using hvsum
  by_cases hboth : v 0 ∈ B ∧ v 1 ∈ B
  · obtain hpair | htriple :=
      hrepair (v 0) hboth.1 (v 1) hboth.2
    · obtain ⟨E, hER, hEnotSub⟩ := hpair
      obtain ⟨w, hwA, hwsum, rfl⟩ :=
        mem_additiveSupportFamily_iff.mp hER
      left
      refine ⟨(w 0).1, (w 1).1, hwA 0, hwA 1, ?_, ?_⟩
      · have hw : (w 0).1 + (w 1).1 = v 0 + v 1 := by
          simpa [Fin.sum_univ_two] using hwsum
        exact hw.trans hsum
      · rintro ⟨hw0B, hw1B⟩
        apply hEnotSub
        intro z hz
        obtain ⟨i, rfl⟩ := mem_tupleSupport_iff.mp hz
        fin_cases i
        · exact hw0B
        · exact hw1B
    · right
      have hsum' : v 0 + v 1 = n := hsum
      rw [hsum'] at htriple
      exact htriple
  · left
    exact ⟨v 0, v 1, hvA 0, hvA 1, hsum, hboth⟩

/-- Hybrid repairs are preserved when the deletion is thinned. -/
theorem HasHybridPairTripleRepairs.mono
    {A B B' : Set ℕ}
    (h : HasHybridPairTripleRepairs A B)
    (hB'B : B' ⊆ B) :
    HasHybridPairTripleRepairs A B' := by
  intro x hx y hy
  obtain hpair | htriple := h x (hB'B hx) y (hB'B hy)
  · left
    obtain ⟨E, hER, hEnotSub⟩ := hpair
    refine ⟨E, hER, ?_⟩
    intro hEB'
    exact hEnotSub (fun z hz => hB'B (hEB' hz))
  · right
    obtain ⟨G, hGR, hGB⟩ := htriple
    exact ⟨G, hGR, hGB.mono_right hB'B⟩

/-- A self-basis deletion with hybrid repairs yields the desired infinite
tail deletion. -/
theorem exists_infiniteDeletion_threeBasis_of_hybridRepairs
    {A B : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hBA : B ⊆ A) (hB : B.Infinite)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A)
    (hrepair : HasHybridPairTripleRepairs A B) :
    ∃ B', B' ⊆ B ∧ B'.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B') 3 := by
  obtain ⟨B', hB'B, hB', hsplitB', hsplitC'⟩ :=
    exists_tail_with_splitting_of_selfBasis hBA hB hself
  have hrepair' := hrepair.mono hB'B
  have hmixed :=
    eventuallyPairIndependentOrBlueTriple_of_hybridRepairs
      hbasis hrepair'
  exact ⟨B', hB'B, hB',
    exactThreeBasis_of_splittableIndependentOrBlueTriple
      hmixed hsplitB' hsplitC'⟩

/-! ## Finite hybrid repairs and their exact obstruction -/

/-- A finite-prefix repair is either an alternative pair with a witness
outside the prefix, or a triple disjoint from the whole prefix. -/
inductive FiniteHybridRepair
    (A : Set ℕ) (D : Finset ℕ) (n : ℕ) : Type
  | pair (E : Finset ℕ)
      (support_mem : E ∈ additiveSupportFamily A 2 n)
      (witness : ℕ) (witness_mem : witness ∈ E)
      (witness_fresh : witness ∉ D)
  | triple (G : Finset ℕ)
      (support_mem : G ∈ additiveSupportFamily A 3 n)
      (support_disjoint : Disjoint (G : Set ℕ) (D : Set ℕ))

namespace FiniteHybridRepair

/-- Only the fresh witness of a pair repair must be permanently reserved.
A triple repair is protected from future deletion points by growth. -/
def reserved {A : Set ℕ} {D : Finset ℕ} {n : ℕ} :
    FiniteHybridRepair A D n → Finset ℕ
  | .pair _ _ z _ _ => {z}
  | .triple _ _ _ => ∅

theorem reserved_disjoint_prefix
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (r : FiniteHybridRepair A D n) :
    Disjoint r.reserved D := by
  cases r with
  | pair E hER z hzE hzD =>
      simp [reserved, hzD]
  | triple G hGR hGD => simp [reserved]

end FiniteHybridRepair

/-- A finite hybrid repair exists exactly when one of its two advertised
modes exists. -/
theorem finiteHybridRepair_nonempty_iff
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ} :
    Nonempty (FiniteHybridRepair A D n) ↔
      (∃ E ∈ additiveSupportFamily A 2 n, ¬ E ⊆ D) ∨
      ∃ G ∈ additiveSupportFamily A 3 n,
        Disjoint (G : Set ℕ) (D : Set ℕ) := by
  constructor
  · rintro ⟨r⟩
    cases r with
    | pair E hER z hzE hzD =>
        exact Or.inl ⟨E, hER, fun hsub => hzD (hsub hzE)⟩
    | triple G hGR hGD =>
        exact Or.inr ⟨G, hGR, hGD⟩
  · rintro (hpair | htriple)
    · obtain ⟨E, hER, hEnotSub⟩ := hpair
      obtain ⟨z, hzE, hzD⟩ := Finset.not_subset.mp hEnotSub
      exact ⟨FiniteHybridRepair.pair E hER z hzE hzD⟩
    · obtain ⟨G, hGR, hGD⟩ := htriple
      exact ⟨FiniteHybridRepair.triple G hGR hGD⟩

/-- Nonexistence means simultaneously that every pair support is trapped in
the prefix and that the prefix destroys the order-three target. -/
theorem not_finiteHybridRepair_nonempty_iff
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ} :
    ¬ Nonempty (FiniteHybridRepair A D n) ↔
      (∀ E ∈ additiveSupportFamily A 2 n, E ⊆ D) ∧
      DestroysAt (additiveSupportFamily A 3) (D : Set ℕ) n := by
  rw [finiteHybridRepair_nonempty_iff]
  simp only [DestroysAt]
  push Not
  rfl

/-- A fresh point has a hybrid repair for every sum with the enlarged
finite prefix, including its double. -/
def HasFreshHybridRepairExtension
    (A K : Set ℕ) (D P : Finset ℕ) (T : ℕ) : Prop :=
  ∃ b, b ∈ K ∧ b ∉ D ∧ b ∉ P ∧ T ≤ b ∧
    ∀ d ∈ insert b D,
      Nonempty (FiniteHybridRepair A (insert b D) (b + d))

theorem not_hasFreshHybridRepairExtension_iff
    {A K : Set ℕ} {D P : Finset ℕ} {T : ℕ} :
    ¬ HasFreshHybridRepairExtension A K D P T ↔
      ∀ b, b ∈ K → b ∉ D → b ∉ P → T ≤ b →
        ∃ d ∈ insert b D,
          (∀ E ∈ additiveSupportFamily A 2 (b + d),
            E ⊆ insert b D) ∧
          DestroysAt (additiveSupportFamily A 3)
            ((insert b D : Finset ℕ) : Set ℕ) (b + d) := by
  classical
  simp only [HasFreshHybridRepairExtension]
  push Not
  constructor
  · intro h b hbK hbD hbP hbT
    obtain ⟨d, hd, hnoRepair⟩ := h b hbK hbD hbP hbT
    have hnot : ¬ Nonempty
        (FiniteHybridRepair A (insert b D) (b + d)) := by
      rintro ⟨r⟩
      exact hnoRepair.false r
    exact ⟨d, hd, not_finiteHybridRepair_nonempty_iff.mp hnot⟩
  · intro h b hbK hbD hbP hbT
    obtain ⟨d, hd, htrap, hdestroy⟩ := h b hbK hbD hbP hbT
    have hnot : ¬ Nonempty
        (FiniteHybridRepair A (insert b D) (b + d)) :=
      not_finiteHybridRepair_nonempty_iff.mpr ⟨htrap, hdestroy⟩
    exact ⟨d, hd, ⟨fun r => hnot ⟨r⟩⟩⟩

def HasFiniteHybridRepairObstruction
    (A K : Set ℕ) (D P : Finset ℕ) (T : ℕ) : Prop :=
  ∀ b, b ∈ K → b ∉ D → b ∉ P → T ≤ b →
    ∃ d ∈ insert b D,
      (∀ E ∈ additiveSupportFamily A 2 (b + d),
        E ⊆ insert b D) ∧
      DestroysAt (additiveSupportFamily A 3)
        ((insert b D : Finset ℕ) : Set ℕ) (b + d)

theorem not_hasFreshHybridRepairExtension_iff_obstruction
    {A K : Set ℕ} {D P : Finset ℕ} {T : ℕ} :
    ¬ HasFreshHybridRepairExtension A K D P T ↔
      HasFiniteHybridRepairObstruction A K D P T :=
  not_hasFreshHybridRepairExtension_iff

theorem HasFiniteHybridRepairObstruction.eventually_fixed
    {A K : Set ℕ} {D P : Finset ℕ} {T : ℕ}
    (h : HasFiniteHybridRepairObstruction A K D P T)
    (hdouble : HasNoRigidDoubles A K) :
    ∀ b, b ∈ K → b ∉ D → b ∉ P →
      max T (2 * D.sum id + 1) ≤ b →
      ∃ d ∈ D,
        (∀ E ∈ additiveSupportFamily A 2 (b + d),
          E ⊆ insert b D) ∧
        DestroysAt (additiveSupportFamily A 3)
          ((insert b D : Finset ℕ) : Set ℕ) (b + d) := by
  intro b hbK hbD hbP hbLarge
  have hbT : T ≤ b := le_trans (le_max_left _ _) hbLarge
  have hsumLarge : 2 * D.sum id < b := by
    have : 2 * D.sum id + 1 ≤ b :=
      le_trans (le_max_right _ _) hbLarge
    omega
  obtain ⟨d, hd, htrap, hdestroy⟩ := h b hbK hbD hbP hbT
  rcases Finset.mem_insert.mp hd with hdb | hdD
  · subst d
    have hrigid : IsRigidPairSum A b b :=
      rigidPairSum_of_supports_subset_insert hsumLarge htrap
    exact (hdouble b hbK hrigid).elim
  · exact ⟨d, hdD, htrap, hdestroy⟩

/-- On an infinite reservoir, finite pigeonhole now leaves only one fixed
translate.  The diagonal family present in the direct-triple-only recursion
has disappeared. -/
theorem HasFiniteHybridRepairObstruction.infinite_fixed
    {A K : Set ℕ} {D P : Finset ℕ} {T : ℕ}
    (h : HasFiniteHybridRepairObstruction A K D P T)
    (hK : K.Infinite)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ d ∈ D, {b | b ∈ K ∧
      (∀ E ∈ additiveSupportFamily A 2 (b + d),
        E ⊆ insert b D) ∧
      DestroysAt (additiveSupportFamily A 3)
        ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Infinite := by
  classical
  let L := max T (2 * D.sum id + 1)
  let X : Set ℕ := K \
    ((D : Set ℕ) ∪ (P : Set ℕ) ∪ Set.Iio L)
  have hExcluded :
      ((D : Set ℕ) ∪ (P : Set ℕ) ∪ Set.Iio L).Finite :=
    (D.finite_toSet.union P.finite_toSet).union (Set.finite_Iio L)
  have hX : X.Infinite := hK.diff hExcluded
  by_contra hnofixed
  push Not at hnofixed
  have hfixedFinite : ∀ d ∈ (D : Set ℕ),
      {b | b ∈ K ∧
        (∀ E ∈ additiveSupportFamily A 2 (b + d),
          E ⊆ insert b D) ∧
        DestroysAt (additiveSupportFamily A 3)
          ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Finite := by
    intro d hdD
    exact hnofixed d hdD
  have hunionFinite :
      (⋃ d ∈ (D : Set ℕ),
        {b | b ∈ K ∧
          (∀ E ∈ additiveSupportFamily A 2 (b + d),
            E ⊆ insert b D) ∧
          DestroysAt (additiveSupportFamily A 3)
            ((insert b D : Finset ℕ) : Set ℕ) (b + d)}).Finite :=
    D.finite_toSet.biUnion hfixedFinite
  apply hX
  apply hunionFinite.subset
  intro b hbX
  have hbK : b ∈ K := hbX.1
  have hbD : b ∉ D := by
    intro hbD
    exact hbX.2 (Or.inl (Or.inl hbD))
  have hbP : b ∉ P := by
    intro hbP
    exact hbX.2 (Or.inl (Or.inr hbP))
  have hbL : L ≤ b := Nat.le_of_not_gt fun hbLt =>
    hbX.2 (Or.inr hbLt)
  obtain ⟨d, hdD, htrap, hdestroy⟩ :=
    h.eventually_fixed hdouble b hbK hbD hbP hbL
  exact Set.mem_iUnion₂.mpr
    ⟨d, hdD, hbK, htrap, hdestroy⟩

/-! ## Normalizing the fixed-translate obstruction -/

/-- At a fixed translate `b+d`, self-splitting of `d` forces `b` into every
minimal destroyer, while self-splitting of `b` forces `d` into it.  Hence a
minimal destroyer inside `D ∪ {b}` has the normalized form `S ∪ {b}`
with one fixed old point `d ∈ S ⊆ D`. -/
theorem exists_normalizedMinimalDestroyer_of_fixedTranslate
    {A B₀ K : Set ℕ} {D : Finset ℕ} {b d : ℕ}
    (hB₀A : B₀ ⊆ A)
    (hKB₀ : K ⊆ B₀)
    (hDK : (D : Set ℕ) ⊆ K)
    (hdD : d ∈ D)
    (hbK : b ∈ K) (hbD : b ∉ D)
    (hsplit : ∀ x ∈ K, SplitsIntoTwo (A \ B₀) x)
    (hdestroy : DestroysAt (additiveSupportFamily A 3)
      ((insert b D : Finset ℕ) : Set ℕ) (b + d)) :
    ∃ S : Finset ℕ, S ⊆ D ∧ d ∈ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) := by
  obtain ⟨D₀, hD₀sub, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hdestroy
  have hD₀B₀ : (D₀ : Set ℕ) ⊆ B₀ := by
    intro x hxD₀
    rcases Finset.mem_insert.mp (hD₀sub hxD₀) with rfl | hxD
    · exact hKB₀ hbK
    · exact hKB₀ (hDK hxD)
  have hbD₀ : b ∈ D₀ := by
    by_contra hbD₀
    obtain ⟨u, v, huC, hvC, huv⟩ := hsplit d (hDK hdD)
    have hnotuple :=
      destroysAt_additiveSupportFamily_iff.mp hminimal.1
    apply hnotuple
    refine ⟨![b, u, v], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hB₀A (hKB₀ hbK), hbD₀⟩
      · exact ⟨huC.1, fun huD₀ => huC.2 (hD₀B₀ huD₀)⟩
      · exact ⟨hvC.1, fun hvD₀ => hvC.2 (hD₀B₀ hvD₀)⟩
    · simp [Fin.sum_univ_succ]
      omega
  have hdD₀ : d ∈ D₀ := by
    by_contra hdD₀
    obtain ⟨u, v, huC, hvC, huv⟩ := hsplit b hbK
    have hnotuple :=
      destroysAt_additiveSupportFamily_iff.mp hminimal.1
    apply hnotuple
    refine ⟨![d, u, v], ?_, ?_⟩
    · intro i
      fin_cases i
      · exact ⟨hB₀A (hKB₀ (hDK hdD)), hdD₀⟩
      · exact ⟨huC.1, fun huD₀ => huC.2 (hD₀B₀ huD₀)⟩
      · exact ⟨hvC.1, fun hvD₀ => hvC.2 (hD₀B₀ hvD₀)⟩
    · simp [Fin.sum_univ_succ]
      omega
  let S := D₀.erase b
  have hSD : S ⊆ D := by
    intro x hxS
    have hxD₀ : x ∈ D₀ := (Finset.mem_erase.mp hxS).2
    have hxb : x ≠ b := (Finset.mem_erase.mp hxS).1
    rcases Finset.mem_insert.mp (hD₀sub hxD₀) with hxb' | hxD
    · exact (hxb hxb').elim
    · exact hxD
  have hdS : d ∈ S := by
    apply Finset.mem_erase.mpr
    exact ⟨fun hdb => hbD (hdb ▸ hdD), hdD₀⟩
  have hinsert : insert b S = D₀ := Finset.insert_erase hbD₀
  refine ⟨S, hSD, hdS, ?_⟩
  rw [hinsert]
  exact hminimal

/-- Since `D` has only finitely many subsets, an infinite fixed-translate
family contains an infinite subfamily with one and the same normalized old
core `S`. -/
theorem infinite_normalizedMinimalDestroyers_of_fixedTranslate
    {A B₀ K : Set ℕ} {D : Finset ℕ} {d : ℕ}
    (hB₀A : B₀ ⊆ A)
    (hKB₀ : K ⊆ B₀)
    (hDK : (D : Set ℕ) ⊆ K)
    (hdD : d ∈ D)
    (hsplit : ∀ x ∈ K, SplitsIntoTwo (A \ B₀) x)
    (hfamily : {b | b ∈ K ∧
      DestroysAt (additiveSupportFamily A 3)
        ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Infinite) :
    ∃ S : Finset ℕ, S ⊆ D ∧ d ∈ S ∧
      {b | b ∈ K ∧ b ∉ D ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A 3) (insert b S) (b + d)}.Infinite := by
  classical
  let X : Set ℕ := {b | b ∈ K ∧
    DestroysAt (additiveSupportFamily A 3)
      ((insert b D : Finset ℕ) : Set ℕ) (b + d)} \ (D : Set ℕ)
  have hX : X.Infinite := hfamily.diff D.finite_toSet
  let candidates : Finset (Finset ℕ) :=
    D.powerset.filter fun S => d ∈ S
  let fiber (S : Finset ℕ) : Set ℕ :=
    {b | b ∈ K ∧ b ∉ D ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d)}
  by_contra hnone
  have hfiberFinite : ∀ S ∈ (candidates : Set (Finset ℕ)),
      (fiber S).Finite := by
    intro S hScandidates
    apply Set.not_infinite.mp
    intro hSinfinite
    apply hnone
    have hSmem := Finset.mem_filter.mp hScandidates
    exact ⟨S, Finset.mem_powerset.mp hSmem.1, hSmem.2, hSinfinite⟩
  have hunionFinite :
      (⋃ S ∈ (candidates : Set (Finset ℕ)), fiber S).Finite :=
    candidates.finite_toSet.biUnion hfiberFinite
  apply hX
  apply hunionFinite.subset
  intro b hbX
  have hbK : b ∈ K := hbX.1.1
  have hbD : b ∉ D := hbX.2
  have hdestroy := hbX.1.2
  obtain ⟨S, hSD, hdS, hminimal⟩ :=
    exists_normalizedMinimalDestroyer_of_fixedTranslate
      hB₀A hKB₀ hDK hdD hbK hbD hsplit hdestroy
  have hScandidates : S ∈ candidates :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hSD, hdS⟩
  exact Set.mem_iUnion₂.mpr
    ⟨S, hScandidates, hbK, hbD, hminimal⟩

/-! ## The hybrid finite-obstruction recursion -/

structure HybridRepairRecursionStep
    (A K : Set ℕ) (D P : Finset ℕ) (last : ℕ) where
  point : ℕ
  point_mem : point ∈ K
  point_not_chosen : point ∉ D
  point_not_reserved : point ∉ P
  point_lower : 2 * last + 1 ≤ point
  repair : (d : {d // d ∈ insert point D}) →
    FiniteHybridRepair A (insert point D) (point + d.1)

theorem hybridRepairRecursionStep_nonempty
    {A K : Set ℕ} {D P : Finset ℕ} {last : ℕ}
    (hext : HasFreshHybridRepairExtension
      A K D P (2 * last + 1)) :
    Nonempty (HybridRepairRecursionStep A K D P last) := by
  classical
  obtain ⟨b, hbK, hbD, hbP, hbLower, hrepair⟩ := hext
  let repair : (d : {d // d ∈ insert b D}) →
      FiniteHybridRepair A (insert b D) (b + d.1) :=
    fun d => Classical.choice (hrepair d.1 d.2)
  exact ⟨{
    point := b
    point_mem := hbK
    point_not_chosen := hbD
    point_not_reserved := hbP
    point_lower := hbLower
    repair := repair
  }⟩

/-- Finite state of the hybrid recursion. -/
structure HybridRepairRecursionState (K : Set ℕ) where
  chosen : Finset ℕ
  reserved : Finset ℕ
  last : ℕ
  chosen_subset : (chosen : Set ℕ) ⊆ K
  chosen_disjoint_reserved : Disjoint chosen reserved

set_option maxHeartbeats 800000 in
/-- Fresh hybrid extensions construct an infinite deletion with a hybrid
repair for every red-red pair sum. -/
theorem exists_hybridRepairDeletion_of_freshExtensions
    {A K : Set ℕ}
    (hext : ∀ (D P : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshHybridRepairExtension A K D P T) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasHybridPairTripleRepairs A B := by
  classical
  let State := HybridRepairRecursionState K
  let initial : State := {
    chosen := ∅
    reserved := ∅
    last := 0
    chosen_subset := by simp
    chosen_disjoint_reserved := by simp
  }
  let chooseStep : (s : State) →
      HybridRepairRecursionStep A K s.chosen s.reserved s.last :=
    fun s => Classical.choice <|
      hybridRepairRecursionStep_nonempty
        (hext s.chosen s.reserved s.chosen_subset
          (2 * s.last + 1))
  let newReserved (s : State) : Finset ℕ :=
    (insert (chooseStep s).point s.chosen).attach.biUnion
      fun d => ((chooseStep s).repair d).reserved
  let advance (s : State) : State := {
    chosen := insert (chooseStep s).point s.chosen
    reserved := s.reserved ∪ newReserved s
    last := (chooseStep s).point
    chosen_subset := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxOld
      · exact (chooseStep s).point_mem
      · exact s.chosen_subset hxOld
    chosen_disjoint_reserved := by
      rw [Finset.disjoint_left]
      intro x hxChosen hxReserved
      rcases Finset.mem_union.mp hxReserved with hxOld | hxNew
      · rcases Finset.mem_insert.mp hxChosen with rfl | hxChosenOld
        · exact (chooseStep s).point_not_reserved hxOld
        · exact Finset.disjoint_left.mp s.chosen_disjoint_reserved
            hxChosenOld hxOld
      · obtain ⟨d, _hdAttach, hxd⟩ := Finset.mem_biUnion.mp hxNew
        exact Finset.disjoint_left.mp
          ((chooseStep s).repair d).reserved_disjoint_prefix
            hxd hxChosen
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
  have hreserved_succ : ∀ i,
      (state (i + 1)).reserved =
        (state i).reserved ∪ newReserved (state i) := by
    intro i
    change (state (i + 1)).reserved =
      (state i).reserved ∪ newReserved (state i)
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
  have hreserved_step : ∀ i,
      (state i).reserved ⊆ (state (i + 1)).reserved := by
    intro i
    rw [hreserved_succ]
    exact Finset.subset_union_left
  have hchosen_mono : Monotone fun i => (state i).chosen :=
    monotone_nat_of_le_succ hchosen_step
  have hreserved_mono : Monotone fun i => (state i).reserved :=
    monotone_nat_of_le_succ hreserved_step
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
  have reserved_not_range : ∀ (j : ℕ)
      (d : {d // d ∈ insert (b j) (state j).chosen})
      {z : ℕ}, z ∈ ((step j).repair d).reserved →
      z ∉ Set.range b := by
    intro j d z hzReserved hzRange
    obtain ⟨i, hi⟩ := hzRange
    by_cases hij : i ≤ j
    · have hbiCurrent : b i ∈ insert (b j) (state j).chosen := by
        by_cases hijEq : i = j
        · subst i
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hprior_chosen (lt_of_le_of_ne hij hijEq))
      have hzFresh := Finset.disjoint_left.mp
        ((step j).repair d).reserved_disjoint_prefix hzReserved
      apply hzFresh
      rw [← hi]
      simpa only [b] using hbiCurrent
    · have hji : j < i := Nat.lt_of_not_ge hij
      have hzNew : z ∈ newReserved (state j) := by
        apply Finset.mem_biUnion.mpr
        exact ⟨d, Finset.mem_attach _ d, hzReserved⟩
      have hzReservedNext : z ∈ (state (j + 1)).reserved := by
        rw [hreserved_succ]
        exact Finset.mem_union_right _ hzNew
      have hzReservedFuture : z ∈ (state i).reserved :=
        hreserved_mono (Nat.succ_le_of_lt hji) hzReservedNext
      apply (step i).point_not_reserved
      change b i ∈ (state i).reserved
      rw [hi]
      exact hzReservedFuture
  let B : Set ℕ := Set.range b
  have repair_of_le : ∀ {i j}, i ≤ j →
      ((∃ E ∈ additiveSupportFamily A 2 (b i + b j),
          ¬ (E : Set ℕ) ⊆ B) ∨
        ∃ G ∈ additiveSupportFamily A 3 (b i + b j),
          Disjoint (G : Set ℕ) B) := by
    intro i j hij
    have hbi : b i ∈ insert (b j) (state j).chosen := by
      by_cases hijEq : i = j
      · subst i
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem
          (hprior_chosen (lt_of_le_of_ne hij hijEq))
    let d : {d // d ∈ insert (b j) (state j).chosen} := ⟨b i, hbi⟩
    cases hrepairEq : (step j).repair d with
    | pair E hER z hzE hzFresh =>
        left
        refine ⟨E, ?_, ?_⟩
        · change E ∈ additiveSupportFamily A 2 (b j + b i) at hER
          rw [Nat.add_comm] at hER
          exact hER
        · intro hEB
          have hzReserved : z ∈ ((step j).repair d).reserved := by
            rw [hrepairEq]
            simp [FiniteHybridRepair.reserved]
          exact reserved_not_range j d hzReserved (hEB hzE)
    | triple G hGR hGD =>
        right
        refine ⟨G, ?_, ?_⟩
        · change G ∈ additiveSupportFamily A 3 (b j + b i) at hGR
          rw [Nat.add_comm] at hGR
          exact hGR
        · rw [Set.disjoint_left]
          intro z hzG hzB
          obtain ⟨k, hk⟩ := hzB
          by_cases hkj : k ≤ j
          · have hbkCurrent : b k ∈ insert (b j) (state j).chosen := by
              by_cases hkjEq : k = j
              · subst k
                exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem
                  (hprior_chosen (lt_of_le_of_ne hkj hkjEq))
            apply Set.disjoint_left.mp hGD hzG
            have hzCurrent :
                z ∈ (insert (step j).point (state j).chosen : Finset ℕ) := by
              rw [← hk]
              simpa only [b] using hbkCurrent
            simpa using hzCurrent
          · have hjk : j < k := Nat.lt_of_not_ge hkj
            have hzle : z ≤ b j + b i :=
              additiveSupportFamily_supportsBounded A 3
                (b j + b i) G hGR z hzG
            have hbile : b i ≤ b j := hbmono.monotone hij
            have htarget : b j + b i ≤ 2 * b j := by omega
            have hlate := hfuture hjk
            omega
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbK i
  · intro x hxB y hyB
    obtain ⟨i, rfl⟩ := hxB
    obtain ⟨j, rfl⟩ := hyB
    rcases le_total i j with hij | hji
    · exact repair_of_le hij
    · have hrepair := repair_of_le hji
      rcases hrepair with hpair | htriple
      · left
        obtain ⟨E, hER, hEnotSub⟩ := hpair
        rw [Nat.add_comm] at hER
        exact ⟨E, hER, hEnotSub⟩
      · right
        obtain ⟨G, hGR, hGdisjoint⟩ := htriple
        rw [Nat.add_comm] at hGR
        exact ⟨G, hGR, hGdisjoint⟩

/-- The complete constructive hybrid bridge from finite extensions to the
desired successor-order deletion. -/
theorem exists_infiniteDeletion_threeBasis_of_freshHybridExtensions
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hext : ∀ (D P : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshHybridRepairExtension A K D P T) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hBK, hB, hrepair⟩ :=
    exists_hybridRepairDeletion_of_freshExtensions hext
  have hBA : B ⊆ A := fun x hx => hB₀A (hKB₀ (hBK hx))
  have hself' : IsExactTupleAsymptoticBasisAlong (A \ B) 2 A :=
    exactTwoBasisAlong_self_of_deletion_subset
      (fun x hx => hKB₀ (hBK hx)) hself
  obtain ⟨B', hB'B, hB', hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_hybridRepairs
      hbasis hBA hB hself' hrepair
  exact ⟨B', fun x hx => hBK (hB'B hx), hB', hthree⟩

theorem strongDeletion_forces_failedHybridRepairStage
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀) :
    ∃ D P : Finset ℕ, (D : Set ℕ) ⊆ K ∧
      ∃ T, ¬ HasFreshHybridRepairExtension A K D P T := by
  by_contra hnoFailure
  push Not at hnoFailure
  have hext : ∀ (D P : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshHybridRepairExtension A K D P T := by
    intro D P hDK T
    exact hnoFailure D P hDK T
  obtain ⟨B, hBK, hB, hthree⟩ :=
    exists_infiniteDeletion_threeBasis_of_freshHybridExtensions
      hbasis hB₀A hself hKB₀ hext
  have hBA : B ⊆ A := fun x hx => hB₀A (hKB₀ (hBK hx))
  obtain ⟨N, hN⟩ := hthree
  obtain ⟨n, hn, hdestroy⟩ := hstrong B hBA hB N
  obtain ⟨v, hvC, hvsum⟩ := hN n hn
  have hsurvive : ∃ E ∈ additiveSupportFamily A 3 n,
      Disjoint (E : Set ℕ) B :=
    exists_surviving_additiveSupport_iff.mpr ⟨v, hvC, hvsum⟩
  exact (not_destroysAt_iff.mpr hsurvive) hdestroy

/-- With nonrigid doubles, strong deletion now forces only a fixed-translate
family; the diagonal alternative is absent from the final reduction. -/
theorem strongDeletion_forces_fixedTripleDestroyerFamily_of_noRigidDoubles
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ K ∧
      ∃ d ∈ D, {b | b ∈ K ∧
        (∀ E ∈ additiveSupportFamily A 2 (b + d),
          E ⊆ insert b D) ∧
        DestroysAt (additiveSupportFamily A 3)
          ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Infinite := by
  obtain ⟨D, P, hDK, T, hfail⟩ :=
    strongDeletion_forces_failedHybridRepairStage
      hstrong hbasis hB₀A hself hKB₀
  have hobstruction : HasFiniteHybridRepairObstruction A K D P T :=
    not_hasFreshHybridRepairExtension_iff_obstruction.mp hfail
  obtain ⟨d, hdD, hinfinite⟩ :=
    hobstruction.infinite_fixed hK hdouble
  exact ⟨D, hDK, d, hdD, hinfinite⟩

/-- On the pairwise-rigid Ramsey branch, strong deletion therefore produces
one infinite normalized moving family `insert b S` with fixed `S` and fixed
translate label `d ∈ S`. -/
theorem strongDeletion_forces_infinite_normalizedFixedTranslateDestroyers
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ K' : Set ℕ, ∃ S : Finset ℕ, ∃ d : ℕ,
      K' ⊆ K ∧ K'.Infinite ∧
      IsPairwiseRigidSet A K' ∧
      HasNoRigidDoubles A K' ∧
      (S : Set ℕ) ⊆ K' ∧ d ∈ S ∧
      {b | b ∈ K' ∧ b ∉ S ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A 3) (insert b S) (b + d)}.Infinite := by
  obtain ⟨L, hL⟩ := hself
  let K' : Set ℕ := K \ Set.Iio L
  have hK'K : K' ⊆ K := Set.diff_subset
  have hK' : K'.Infinite := hK.diff (Set.finite_Iio L)
  have hK'B₀ : K' ⊆ B₀ := fun x hx => hKB₀ (hK'K hx)
  have hrigid' : IsPairwiseRigidSet A K' := by
    intro x hx y hy hxy
    exact hrigid x (hK'K hx) y (hK'K hy) hxy
  have hdouble' : HasNoRigidDoubles A K' := by
    intro x hx
    exact hdouble x (hK'K hx)
  have hsplit : ∀ x ∈ K', SplitsIntoTwo (A \ B₀) x := by
    intro x hx
    have hLx : L ≤ x := Nat.le_of_not_gt hx.2
    obtain ⟨v, hvC, hvsum⟩ := hL x hLx (hB₀A (hK'B₀ hx))
    exact ⟨v 0, v 1, hvC 0, hvC 1,
      by simpa [Fin.sum_univ_two] using hvsum⟩
  obtain ⟨D, hDK', d, hdD, hfamily⟩ :=
    strongDeletion_forces_fixedTripleDestroyerFamily_of_noRigidDoubles
      hstrong hbasis hB₀A ⟨L, hL⟩ hK'B₀ hK' hdouble'
  have hdestroyFamily : {b | b ∈ K' ∧
      DestroysAt (additiveSupportFamily A 3)
        ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Infinite := by
    apply hfamily.mono
    intro b hb
    exact ⟨hb.1, hb.2.2⟩
  obtain ⟨S, hSD, hdS, hminimalFamily⟩ :=
    infinite_normalizedMinimalDestroyers_of_fixedTranslate
      hB₀A hK'B₀ hDK' hdD hsplit hdestroyFamily
  have hSK' : (S : Set ℕ) ⊆ K' :=
    fun x hx => hDK' (hSD hx)
  have hminimalFamily' : {b | b ∈ K' ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d)}.Infinite := by
    apply hminimalFamily.mono
    intro b hb
    exact ⟨hb.1, fun hbS => hb.2.1 (hSD hbS), hb.2.2⟩
  exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
    hSK', hdS, hminimalFamily'⟩

/-! ## Full-prefix old-core obstructions -/

theorem infinite_fullPrefixUniqueHitRepairs_of_normalizedDestroyers
    {A X : Set ℕ} {D S : Finset ℕ} {d : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hDA : (D : Set ℕ) ⊆ A)
    (hSD : S ⊆ D)
    (hX : X.Infinite)
    (hXS : ∀ b ∈ X, b ∉ S)
    (hdestroy : ∀ b ∈ X,
      DestroysAt (additiveSupportFamily A 3)
        ((insert b S : Finset ℕ) : Set ℕ) (b + d)) :
    {b | b ∈ X ∧ b ∉ D ∧
      ∃ x ∈ S, ∃ G ∈ additiveSupportFamily A 3 (b + d),
        G ∩ insert b D = {x}}.Infinite := by
  classical
  obtain ⟨N, hforce⟩ :=
    hbasis.large_externalAnchorSet_forces_pairSupportGrowth
  let m := S.card + 1
  let r := max (additiveSupportFamily A 2 d).card (D.card + 1)
  let s := 2 * m * r + m + 1
  obtain ⟨B₀, hB₀A, hB₀card⟩ :=
    hbasis.infinite.exists_subset_card_eq s
  have hB₀nonempty : B₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [hB₀card]
    simp [s]
  let L := N + B₀.max' hB₀nonempty
  let X' : Set ℕ := X \ ((D : Set ℕ) ∪ Set.Iio L)
  have hX' : X'.Infinite := by
    exact hX.diff (D.finite_toSet.union (Set.finite_Iio L))
  apply hX'.mono
  intro b hbX'
  have hbX : b ∈ X := hbX'.1
  have hbExcluded : b ∉ (D : Set ℕ) ∪ Set.Iio L := hbX'.2
  have hbD : b ∉ D := fun hb => hbExcluded (Or.inl hb)
  have hbL : L ≤ b := Nat.le_of_not_gt fun hb =>
    hbExcluded (Or.inr hb)
  have hbS : b ∉ S := hXS b hbX
  let T : Finset ℕ := insert b S
  let B : Finset ℕ := B₀ \ T
  have hTcard : T.card = m := by
    simp [T, m, hbS]
  have hBA : ∀ a ∈ B, a ∈ A := by
    intro a haB
    exact hB₀A (Finset.mem_sdiff.mp haB).1
  have hBT : Disjoint B T := Finset.sdiff_disjoint
  have hlate : ∀ a ∈ B, N + a ≤ b + d := by
    intro a haB
    have haB₀ : a ∈ B₀ := (Finset.mem_sdiff.mp haB).1
    have hamax : a ≤ B₀.max' hB₀nonempty :=
      Finset.le_max' B₀ a haB₀
    dsimp only [L] at hbL
    omega
  have hinterCard : (B₀ ∩ T).card ≤ T.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hBcardSum : B.card + (B₀ ∩ T).card = B₀.card := by
    exact Finset.card_sdiff_add_card_inter B₀ T
  have hBlarge : 2 * T.card * r < B.card := by
    rw [hB₀card] at hBcardSum
    rw [hTcard] at hinterCard ⊢
    dsimp only [s] at hBcardSum
    omega
  obtain ⟨x, hxT, hxn, hxlarge⟩ :=
    hforce (hdestroy b hbX) hBA hBT hlate hBlarge
  have hxb : x ≠ b := by
    intro hxb
    subst x
    have htarget : b + d - b = d := by omega
    rw [htarget] at hxlarge
    have hfixed : (additiveSupportFamily A 2 d).card ≤ r :=
      le_max_left _ _
    omega
  have hxS : x ∈ S := by
    exact (Finset.mem_insert.mp hxT).resolve_left hxb
  have hxA : x ∈ A := hDA (hSD hxS)
  have hxPrefix : x ∈ insert b D :=
    Finset.mem_insert_of_mem (hSD hxS)
  have heraseCard : ((insert b D).erase x).card ≤ r := by
    calc
      ((insert b D).erase x).card ≤ (insert b D).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      _ ≤ D.card + 1 := Finset.card_insert_le _ _
      _ ≤ r := le_max_right _ _
  obtain ⟨G, hGR, hGhit⟩ :=
    exists_successorSupport_uniqueHit_of_manyPairSupports
      (D := insert b D) (n := b + d) (x := x)
      hxA hxPrefix hxn (lt_of_le_of_lt heraseCard hxlarge)
  exact ⟨hbX, hbD, x, hxS, G, hGR, hGhit⟩

/-- Because the normalized old core is finite, the full-prefix obstruction point
can be made independent of the moving candidate on an infinite subfamily.
One recoloring of this fixed `x` therefore repairs the distinguished target
`b + d` for infinitely many candidates `b`. -/
theorem exists_fixedFullPrefixObstruction_of_normalizedDestroyers
    {A X : Set ℕ} {D S : Finset ℕ} {d : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hDA : (D : Set ℕ) ⊆ A)
    (hSD : S ⊆ D)
    (hX : X.Infinite)
    (hXS : ∀ b ∈ X, b ∉ S)
    (hdestroy : ∀ b ∈ X,
      DestroysAt (additiveSupportFamily A 3)
        ((insert b S : Finset ℕ) : Set ℕ) (b + d)) :
    ∃ x ∈ S, {b | b ∈ X ∧ b ∉ D ∧
      ∃ G ∈ additiveSupportFamily A 3 (b + d),
        G ∩ insert b D = {x}}.Infinite := by
  classical
  have hgood :=
    infinite_fullPrefixUniqueHitRepairs_of_normalizedDestroyers
      hbasis hDA hSD hX hXS hdestroy
  let fiber (x : ℕ) : Set ℕ := {b | b ∈ X ∧ b ∉ D ∧
    ∃ G ∈ additiveSupportFamily A 3 (b + d),
      G ∩ insert b D = {x}}
  by_contra hnone
  push Not at hnone
  have hfiberFinite : ∀ x ∈ (S : Set ℕ), (fiber x).Finite := by
    intro x hxS
    simpa [fiber] using hnone x hxS
  have hunionFinite :
      (⋃ x ∈ (S : Set ℕ), fiber x).Finite :=
    S.finite_toSet.biUnion hfiberFinite
  apply hgood
  apply hunionFinite.subset
  intro b hb
  obtain ⟨hbX, hbD, x, hxS, G, hGR, hGhit⟩ := hb
  exact Set.mem_iUnion₂.mpr ⟨x, hxS, hbX, hbD, G, hGR, hGhit⟩

/-- Strong deletion on the rigid self-basis branch forces an amortizable
finite obstruction.  The original failed-extension prefix `D` is retained, and
there is one fixed old point `x ∈ S ⊆ D` such that infinitely many moving
candidates have a triple repair meeting `insert b D` exactly at `x`.

Keeping `x` instead of deleting it therefore repairs all of those
distinguished failed-extension targets simultaneously. -/
theorem strongDeletion_forces_fixedFullPrefixObstructionFamily
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ K' : Set ℕ, ∃ D S : Finset ℕ, ∃ d x : ℕ,
      K' ⊆ K ∧ K'.Infinite ∧
      IsPairwiseRigidSet A K' ∧
      HasNoRigidDoubles A K' ∧
      (D : Set ℕ) ⊆ K' ∧ S ⊆ D ∧ d ∈ S ∧ x ∈ S ∧
      {b | b ∈ K' ∧ b ∉ D ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A 3) (insert b S) (b + d) ∧
        ∃ G ∈ additiveSupportFamily A 3 (b + d),
          G ∩ insert b D = {x}}.Infinite := by
  classical
  obtain ⟨L, hL⟩ := hself
  let K' : Set ℕ := K \ Set.Iio L
  have hK'K : K' ⊆ K := Set.diff_subset
  have hK' : K'.Infinite := hK.diff (Set.finite_Iio L)
  have hK'B₀ : K' ⊆ B₀ := fun y hy => hKB₀ (hK'K hy)
  have hK'A : K' ⊆ A := fun y hy => hB₀A (hK'B₀ hy)
  have hrigid' : IsPairwiseRigidSet A K' := by
    intro y hy z hz hyz
    exact hrigid y (hK'K hy) z (hK'K hz) hyz
  have hdouble' : HasNoRigidDoubles A K' := by
    intro y hy
    exact hdouble y (hK'K hy)
  have hsplit : ∀ y ∈ K', SplitsIntoTwo (A \ B₀) y := by
    intro y hy
    have hLy : L ≤ y := Nat.le_of_not_gt hy.2
    obtain ⟨v, hvC, hvsum⟩ := hL y hLy (hK'A hy)
    exact ⟨v 0, v 1, hvC 0, hvC 1,
      by simpa [Fin.sum_univ_two] using hvsum⟩
  obtain ⟨D, hDK', d, hdD, hfamily⟩ :=
    strongDeletion_forces_fixedTripleDestroyerFamily_of_noRigidDoubles
      hstrong hbasis hB₀A ⟨L, hL⟩ hK'B₀ hK' hdouble'
  have hdestroyFamily : {b | b ∈ K' ∧
      DestroysAt (additiveSupportFamily A 3)
        ((insert b D : Finset ℕ) : Set ℕ) (b + d)}.Infinite := by
    apply hfamily.mono
    intro b hb
    exact ⟨hb.1, hb.2.2⟩
  obtain ⟨S, hSD, hdS, hminimalFamily⟩ :=
    infinite_normalizedMinimalDestroyers_of_fixedTranslate
      hB₀A hK'B₀ hDK' hdD hsplit hdestroyFamily
  let X : Set ℕ := {b | b ∈ K' ∧ b ∉ D ∧
    IsInclusionMinimalDestroyer
      (additiveSupportFamily A 3) (insert b S) (b + d)}
  have hX : X.Infinite := by
    simpa [X] using hminimalFamily
  have hXS : ∀ b ∈ X, b ∉ S := by
    intro b hb hbS
    exact hb.2.1 (hSD hbS)
  have hdestroyX : ∀ b ∈ X,
      DestroysAt (additiveSupportFamily A 3)
        ((insert b S : Finset ℕ) : Set ℕ) (b + d) := by
    intro b hb
    exact hb.2.2.1
  have hDA : (D : Set ℕ) ⊆ A := fun y hy => hK'A (hDK' hy)
  obtain ⟨x, hxS, hfixed⟩ :=
    exists_fixedFullPrefixObstruction_of_normalizedDestroyers
      hbasis hDA hSD hX hXS hdestroyX
  have hfixed' : {b | b ∈ K' ∧ b ∉ D ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      ∃ G ∈ additiveSupportFamily A 3 (b + d),
        G ∩ insert b D = {x}}.Infinite := by
    apply hfixed.mono
    intro b hb
    change b ∈ X ∧ b ∉ D ∧
      ∃ G ∈ additiveSupportFamily A 3 (b + d),
        G ∩ insert b D = {x} at hb
    exact ⟨hb.1.1, hb.1.2.1, hb.1.2.2, hb.2.2⟩
  exact ⟨K', D, S, d, x, hK'K, hK', hrigid', hdouble',
    hDK', hSD, hdS, hxS, hfixed'⟩

/-- An infinite normalized family has one of three uniform forms: the fixed
old core has size at most two, or infinitely many members have disjoint
unique-hit repairs, or infinitely many have a common-anchor repair system. -/
theorem infinite_normalizedMinimalDestroyers_trichotomy
    {A K : Set ℕ} {S : Finset ℕ} {d : ℕ}
    (hfamily : {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d)}.Infinite) :
    S.card ≤ 2 ∨
      (3 ≤ S.card ∧
        ({b | b ∈ K ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasTwoDisjointUniqueHitRepairs
            (additiveSupportFamily A 3) (insert b S) (b + d)}.Infinite ∨
        {b | b ∈ K ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasCommonAnchorOrderThreeRepairs
            A (insert b S) (b + d)}.Infinite)) := by
  classical
  by_cases hsmall : S.card ≤ 2
  · exact Or.inl hsmall
  · right
    refine ⟨by omega, ?_⟩
    let X₁ : Set ℕ := {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasTwoDisjointUniqueHitRepairs
        (additiveSupportFamily A 3) (insert b S) (b + d)}
    let X₂ : Set ℕ := {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasCommonAnchorOrderThreeRepairs A (insert b S) (b + d)}
    by_cases hX₁ : X₁.Infinite
    · exact Or.inl hX₁
    · right
      by_cases hX₂ : X₂.Infinite
      · exact hX₂
      · have hfinite : (X₁ ∪ X₂).Finite :=
          (Set.not_infinite.mp hX₁).union (Set.not_infinite.mp hX₂)
        exfalso
        apply hfamily
        apply hfinite.subset
        intro b hb
        have hcard : 4 ≤ (insert b S).card := by
          rw [Finset.card_insert_of_notMem hb.2.1]
          omega
        obtain hrepairs | hanchor :=
          minimalOrderThreeDestroyer_disjointRepairs_or_commonAnchor
            hb.2.2 hcard
        · exact Or.inl ⟨hb.1, hb.2.1, hb.2.2, hrepairs⟩
        · exact Or.inr ⟨hb.1, hb.2.1, hb.2.2, hanchor⟩

/-- Named form of the repair exposed by a common anchor on a rigid
reservoir: its only possible reservoir vertices are its unique hit and the
anchor, and an external anchor leaves exactly the unique hit. -/
def HasAlmostGlobalUniqueHitRepair
    (A K : Set ℕ) (D : Finset ℕ) (n : ℕ) : Prop :=
  ∃ z, ∃ x : {x // x ∈ D},
    ∃ E ∈ additiveSupportFamily A 3 n,
      x.1 ∈ E ∧
      (((E : Set ℕ) ∩ K) ⊆ ({x.1, z} : Set ℕ)) ∧
      (z ∉ K → ((E : Set ℕ) ∩ K) = ({x.1} : Set ℕ))

/-- With five destroyer vertices, the common-anchor counting proof can
avoid one prescribed vertex while choosing an external reflected partner. -/
theorem commonAnchor_exists_externalPartner_ne_of_five_le_card
    {A K : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x)
    (hDcard : 5 ≤ D.card)
    (hDK : (D : Set ℕ) ⊆ K)
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K)
    (avoid : {x // x ∈ D}) :
    ∃ x : {x // x ∈ D}, x ≠ avoid ∧ ∃ u,
      u ∈ A ∧ u ∉ K ∧ u ∈ c.support x ∧
        c.support x ⊆ {x.1, z, u} ∧
        x.1 + z + u = n := by
  classical
  obtain ⟨partner, hpartnerA, hpartnerSupport,
      _hpartnerOutside, hpartnerSum, _hpartnerInjective,
      hfixed, internal, hinternal, hinternalCard⟩ :=
    commonAnchor_partnersIn_pairwiseRigidSet_le_two
      c hz hDK hKA hrigid
  let fixed : Finset {x // x ∈ D} :=
    Finset.univ.filter fun x => partner x = x.1
  have hfixedCard : fixed.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro x y hx hy
    apply hfixed x y
    · exact (Finset.mem_filter.mp hx).2
    · exact (Finset.mem_filter.mp hy).2
  let forbidden : Finset {x // x ∈ D} :=
    internal ∪ fixed ∪ {avoid}
  have hforbiddenCard : forbidden.card ≤ 4 := by
    calc
      forbidden.card ≤ (internal ∪ fixed).card + 1 := by
        dsimp only [forbidden]
        exact Finset.card_union_le _ _
      _ ≤ (internal.card + fixed.card) + 1 := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ (2 + 1) + 1 := by omega
      _ = 4 := by omega
  have hexternal : ∃ x : {x // x ∈ D}, x ∉ forbidden := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset {x // x ∈ D}) ⊆ forbidden :=
      fun x _hx => hno x
    have hcardle : D.card ≤ forbidden.card := by
      simpa using Finset.card_le_card hsub
    omega
  obtain ⟨x, hxForbidden⟩ := hexternal
  have hxAvoid : x ≠ avoid := by
    intro hxa
    apply hxForbidden
    simp [forbidden, hxa]
  have hxNotFixed : partner x ≠ x.1 := by
    intro hpx
    apply hxForbidden
    apply Finset.mem_union_left
    exact Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpx⟩)
  have hxExternal : partner x ∉ K := by
    intro hxK
    have hxInternal : x ∈ internal :=
      (hinternal x).mpr ⟨hxK, hxNotFixed⟩
    apply hxForbidden
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hxInternal)
  have hxSupport : x.1 ∈ c.support x := by
    have hxInter : x.1 ∈ c.support x ∩ D := by
      rw [c.unique_hit x]
      simp
    exact (Finset.mem_inter.mp hxInter).1
  have hzSupport : z ∈ c.support x := (Finset.mem_sdiff.mp (hz x)).1
  have hxz : x.1 ≠ z := fun hxz =>
    (Finset.mem_sdiff.mp (hz x)).2 (hxz ▸ x.2)
  exact ⟨x, hxAvoid, partner x, hpartnerA x, hxExternal,
    hpartnerSupport x,
    OrderThreeUniqueHitRepairChoice.support_subset_triple_of_sum
      (c.support_mem x) hxSupport hzSupport hxz (hpartnerSum x),
    hpartnerSum x⟩

/-- Almost-global repair whose unique hit lies in the fixed old core, rather
than at the moving point. -/
def HasAlmostGlobalOldCoreRepair
    (A K : Set ℕ) (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ z, ∃ x : {x // x ∈ S},
    ∃ E ∈ additiveSupportFamily A 3 n,
      x.1 ∈ E ∧
      (((E : Set ℕ) ∩ K) ⊆ ({x.1, z} : Set ℕ)) ∧
      (z ∉ K → ((E : Set ℕ) ∩ K) = ({x.1} : Set ℕ))

/-- For normalized common-anchor systems with at least four old vertices,
the almost-global repair can be chosen to hit the old core. -/
theorem commonAnchor_exists_almostGlobalOldCoreRepair
    {A K : Set ℕ} {S : Finset ℕ} {b d : ℕ}
    (hKA : K ⊆ A)
    (hSK : (S : Set ℕ) ⊆ K)
    (hbK : b ∈ K) (hbS : b ∉ S)
    (hrigid : IsPairwiseRigidSet A K)
    (hSlarge : 4 ≤ S.card)
    (hcommon : HasCommonAnchorOrderThreeRepairs
      A (insert b S) (b + d)) :
    HasAlmostGlobalOldCoreRepair A K S (b + d) := by
  obtain ⟨c, z, hz⟩ := hcommon
  have hDcard : 5 ≤ (insert b S).card := by
    rw [Finset.card_insert_of_notMem hbS]
    omega
  have hinsertK : ((insert b S : Finset ℕ) : Set ℕ) ⊆ K := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact hbK
    · exact hSK hxS
  let avoid : {x // x ∈ insert b S} :=
    ⟨b, Finset.mem_insert_self _ _⟩
  obtain ⟨x, hxAvoid, u, _huA, huK, huSupport,
      hsupport, _hsum⟩ :=
    commonAnchor_exists_externalPartner_ne_of_five_le_card
      c hz hDcard hinsertK hKA hrigid avoid
  have hxS : x.1 ∈ S := by
    rcases Finset.mem_insert.mp x.2 with hxb | hxS
    · exact (hxAvoid (Subtype.ext hxb)).elim
    · exact hxS
  let xS : {x // x ∈ S} := ⟨x.1, hxS⟩
  have hxSupport : x.1 ∈ c.support x := by
    have hxInter : x.1 ∈ c.support x ∩ insert b S := by
      rw [c.unique_hit x]
      simp
    exact (Finset.mem_inter.mp hxInter).1
  refine ⟨z, xS, c.support x, c.support_mem x, hxSupport, ?_, ?_⟩
  · rintro w ⟨hwSupport, hwK⟩
    have hw := hsupport hwSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simp [xS]
    · simp [xS]
    · exact (huK hwK).elim
  · intro hzK
    apply Set.Subset.antisymm
    · rintro w ⟨hwSupport, hwK⟩
      have hw := hsupport hwSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · simp [xS]
      · exact (hzK hwK).elim
      · exact (huK hwK).elim
    · intro w hw
      have hwx : w = x.1 := by simpa [xS] using hw
      subst w
      exact ⟨hxSupport, hinsertK x.2⟩

/-- The preceding old-core choice applies pointwise to an infinite
normalized common-anchor family. -/
theorem infinite_oldCoreRepairs_of_normalizedCommonAnchors
    {A K : Set ℕ} {S : Finset ℕ} {d : ℕ}
    (hKA : K ⊆ A)
    (hSK : (S : Set ℕ) ⊆ K)
    (hrigid : IsPairwiseRigidSet A K)
    (hSlarge : 4 ≤ S.card)
    (hfamily : {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasCommonAnchorOrderThreeRepairs
        A (insert b S) (b + d)}.Infinite) :
    {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasAlmostGlobalOldCoreRepair A K S (b + d)}.Infinite := by
  apply hfamily.mono
  intro b hb
  exact ⟨hb.1, hb.2.1, hb.2.2.1,
    commonAnchor_exists_almostGlobalOldCoreRepair
      hKA hSK hb.1 hb.2.1 hrigid hSlarge hb.2.2.2⟩

/-- Uniform common-anchor families on a rigid reservoir give an infinite
family of almost-global unique-hit repairs. -/
theorem infinite_almostGlobalRepairs_of_normalizedCommonAnchors
    {A K : Set ℕ} {S : Finset ℕ} {d : ℕ}
    (hKA : K ⊆ A)
    (hSK : (S : Set ℕ) ⊆ K)
    (hrigid : IsPairwiseRigidSet A K)
    (hSlarge : 3 ≤ S.card)
    (hfamily : {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasCommonAnchorOrderThreeRepairs
        A (insert b S) (b + d)}.Infinite) :
    {b | b ∈ K ∧ b ∉ S ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) (insert b S) (b + d) ∧
      HasAlmostGlobalUniqueHitRepair
        A K (insert b S) (b + d)}.Infinite := by
  apply hfamily.mono
  intro b hb
  obtain ⟨c, z, hz⟩ := hb.2.2.2
  have hcard : 4 ≤ (insert b S).card := by
    rw [Finset.card_insert_of_notMem hb.2.1]
    omega
  have hinsertK : ((insert b S : Finset ℕ) : Set ℕ) ⊆ K := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact hb.1
    · exact hSK hxS
  obtain ⟨x, E, hER, hxE, hEK, hunique⟩ :=
    commonAnchor_exists_almostGlobalUniqueHit
      c hz hcard hinsertK hKA hrigid
  exact ⟨hb.1, hb.2.1, hb.2.2.1,
    z, x, E, hER, hxE, hEK, hunique⟩

/-- Final verified reduction of the rigid self-basis branch.  Strong
deletion forces one fixed normalized core and then exactly one of: a core of
size at most two, infinitely many disjoint-repair systems, or infinitely
many almost-global anchor repairs. -/
theorem strongDeletion_rigidSelfBasis_normalizedRepairTrichotomy
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ K' : Set ℕ, ∃ S : Finset ℕ, ∃ d : ℕ,
      K' ⊆ K ∧ K'.Infinite ∧
      IsPairwiseRigidSet A K' ∧
      HasNoRigidDoubles A K' ∧
      (S : Set ℕ) ⊆ K' ∧ d ∈ S ∧
      (S.card ≤ 2 ∨
        {b | b ∈ K' ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasTwoDisjointUniqueHitRepairs
            (additiveSupportFamily A 3)
              (insert b S) (b + d)}.Infinite ∨
        {b | b ∈ K' ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasAlmostGlobalUniqueHitRepair
            A K' (insert b S) (b + d)}.Infinite) := by
  obtain ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, hfamily⟩ :=
    strongDeletion_forces_infinite_normalizedFixedTranslateDestroyers
      hstrong hbasis hB₀A hself hKB₀ hK hrigid hdouble
  obtain hsmall | ⟨hSlarge, hdisjoint | hcommon⟩ :=
    infinite_normalizedMinimalDestroyers_trichotomy hfamily
  · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, Or.inl hsmall⟩
  · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, Or.inr (Or.inl hdisjoint)⟩
  · have hKA' : K' ⊆ A := fun x hx =>
      hB₀A (hKB₀ (hK'K hx))
    have halmost := infinite_almostGlobalRepairs_of_normalizedCommonAnchors
      hKA' hSK' hrigid' hSlarge hcommon
    exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, Or.inr (Or.inr halmost)⟩

/-- Strengthened finite-obstruction form.  Once the fixed old core has at least
four vertices, a common-anchor repair can be forced to hit that old core,
not the moving point.  Thus the only bounded exceptional cores have size at
most three. -/
theorem strongDeletion_rigidSelfBasis_oldCoreRepairTrichotomy
    {A B₀ K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ K' : Set ℕ, ∃ S : Finset ℕ, ∃ d : ℕ,
      K' ⊆ K ∧ K'.Infinite ∧
      IsPairwiseRigidSet A K' ∧
      HasNoRigidDoubles A K' ∧
      (S : Set ℕ) ⊆ K' ∧ d ∈ S ∧
      (S.card ≤ 3 ∨
        {b | b ∈ K' ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasTwoDisjointUniqueHitRepairs
            (additiveSupportFamily A 3)
              (insert b S) (b + d)}.Infinite ∨
        {b | b ∈ K' ∧ b ∉ S ∧
          IsInclusionMinimalDestroyer
            (additiveSupportFamily A 3) (insert b S) (b + d) ∧
          HasAlmostGlobalOldCoreRepair
            A K' S (b + d)}.Infinite) := by
  obtain ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, hfamily⟩ :=
    strongDeletion_forces_infinite_normalizedFixedTranslateDestroyers
      hstrong hbasis hB₀A hself hKB₀ hK hrigid hdouble
  obtain hsmall | ⟨hSthree, hdisjoint | hcommon⟩ :=
    infinite_normalizedMinimalDestroyers_trichotomy hfamily
  · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
      hSK', hdS, Or.inl (by omega)⟩
  · by_cases hSsmall : S.card ≤ 3
    · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
        hSK', hdS, Or.inl hSsmall⟩
    · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
        hSK', hdS, Or.inr (Or.inl hdisjoint)⟩
  · by_cases hSsmall : S.card ≤ 3
    · exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
        hSK', hdS, Or.inl hSsmall⟩
    · have hSfour : 4 ≤ S.card := by omega
      have hKA' : K' ⊆ A := fun x hx =>
        hB₀A (hKB₀ (hK'K hx))
      have hold := infinite_oldCoreRepairs_of_normalizedCommonAnchors
        hKA' hSK' hrigid' hSfour hcommon
      exact ⟨K', S, d, hK'K, hK', hrigid', hdouble',
        hSK', hdS, Or.inr (Or.inr hold)⟩

end Erdos881
