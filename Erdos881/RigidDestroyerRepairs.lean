import Erdos881.SplittableIndependentDeletion

/-!
# Repair tails in the rigid branch

The outside part of a unique-hit support for an order-three destroyer has at
most two vertices.  This file isolates the exact structure of a pairwise
intersecting family of such tails: it is a star, apart from the three-edge
triangle.
-/

namespace Erdos881

private theorem finset_eq_pair_of_card_le_two
    {α : Type*} [DecidableEq α] {E : Finset α} {x y : α}
    (hxy : x ≠ y) (hxE : x ∈ E) (hyE : y ∈ E)
    (hcard : E.card ≤ 2) :
    E = {x, y} := by
  have hsubset : ({x, y} : Finset α) ⊆ E := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxE
    · exact hyE
  apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
  simpa [hxy] using hcard

/-- A nonempty pairwise-intersecting family of nonempty sets of size at most
two either has a common vertex, or consists of the three edges of a triangle
(some of those three edges may be absent). -/
theorem pairwiseIntersecting_card_le_two_star_or_triangle
    {α : Type*} [DecidableEq α] (𝒯 : Set (Finset α))
    (h𝒯 : 𝒯.Nonempty)
    (hnonempty : ∀ E ∈ 𝒯, E.Nonempty)
    (hcard : ∀ E ∈ 𝒯, E.card ≤ 2)
    (hinter : ∀ E ∈ 𝒯, ∀ F ∈ 𝒯, ¬ Disjoint E F) :
    (∃ z, ∀ E ∈ 𝒯, z ∈ E) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        ∀ E ∈ 𝒯,
          E = {a, b} ∨ E = {a, c} ∨ E = {b, c} := by
  classical
  obtain ⟨E, hE𝒯⟩ := h𝒯
  obtain ⟨a, haE⟩ := hnonempty E hE𝒯
  by_cases haCommon : ∀ F ∈ 𝒯, a ∈ F
  · exact Or.inl ⟨a, haCommon⟩
  · push Not at haCommon
    obtain ⟨F, hF𝒯, haF⟩ := haCommon
    obtain ⟨b, hbE, hbF⟩ :=
      Finset.not_disjoint_iff.mp (hinter E hE𝒯 F hF𝒯)
    have hab : a ≠ b := by
      intro hab
      exact haF (hab ▸ hbF)
    have hEeq : E = {a, b} :=
      finset_eq_pair_of_card_le_two hab haE hbE (hcard E hE𝒯)
    by_cases hbCommon : ∀ G ∈ 𝒯, b ∈ G
    · exact Or.inl ⟨b, hbCommon⟩
    · push Not at hbCommon
      obtain ⟨G, hG𝒯, hbG⟩ := hbCommon
      obtain ⟨x, hxE, hxG⟩ :=
        Finset.not_disjoint_iff.mp (hinter E hE𝒯 G hG𝒯)
      have hxa : x = a := by
        rw [hEeq] at hxE
        simp only [Finset.mem_insert, Finset.mem_singleton] at hxE
        rcases hxE with hxa | hxb
        · exact hxa
        · exact (hbG (hxb ▸ hxG)).elim
      have haG : a ∈ G := hxa ▸ hxG
      obtain ⟨c, hcF, hcG⟩ :=
        Finset.not_disjoint_iff.mp (hinter F hF𝒯 G hG𝒯)
      have hac : a ≠ c := by
        intro hac
        exact haF (hac ▸ hcF)
      have hbc : b ≠ c := by
        intro hbc
        exact hbG (hbc ▸ hcG)
      have hFeq : F = {b, c} :=
        finset_eq_pair_of_card_le_two hbc hbF hcF (hcard F hF𝒯)
      have hGeq : G = {a, c} :=
        finset_eq_pair_of_card_le_two hac haG hcG (hcard G hG𝒯)
      apply Or.inr
      refine ⟨a, b, c, hab, hac, hbc, ?_⟩
      intro H hH𝒯
      by_cases haH : a ∈ H
      · obtain ⟨z, hzH, hzF⟩ :=
          Finset.not_disjoint_iff.mp (hinter H hH𝒯 F hF𝒯)
        rw [hFeq] at hzF
        simp only [Finset.mem_insert, Finset.mem_singleton] at hzF
        rcases hzF with hzb | hzc
        · left
          apply finset_eq_pair_of_card_le_two hab haH (hzb ▸ hzH)
          exact hcard H hH𝒯
        · right; left
          apply finset_eq_pair_of_card_le_two hac haH (hzc ▸ hzH)
          exact hcard H hH𝒯
      · obtain ⟨z, hzH, hzE⟩ :=
          Finset.not_disjoint_iff.mp (hinter H hH𝒯 E hE𝒯)
        have hzb : z = b := by
          rw [hEeq] at hzE
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzE
          rcases hzE with hza | hzb
          · exact (haH (hza ▸ hzH)).elim
          · exact hzb
        have hbH : b ∈ H := hzb ▸ hzH
        obtain ⟨w, hwH, hwG⟩ :=
          Finset.not_disjoint_iff.mp (hinter H hH𝒯 G hG𝒯)
        have hwc : w = c := by
          rw [hGeq] at hwG
          simp only [Finset.mem_insert, Finset.mem_singleton] at hwG
          rcases hwG with hwa | hwc
          · exact (haH (hwa ▸ hwH)).elim
          · exact hwc
        right; right
        apply finset_eq_pair_of_card_le_two hbc hbH (hwc ▸ hwH)
        exact hcard H hH𝒯

/-! ## Unique-hit repair tails -/

/-- A simultaneous choice of one unique-hit order-three repair support for
every vertex of a finite destroyer. -/
structure OrderThreeUniqueHitRepairChoice
    (A : Set ℕ) (D : Finset ℕ) (n : ℕ) where
  support : {x // x ∈ D} → Finset ℕ
  support_mem : ∀ x,
    support x ∈ additiveSupportFamily A 3 n
  unique_hit : ∀ x, support x ∩ D = {x.1}

namespace OrderThreeUniqueHitRepairChoice

/-- If two distinct vertices occur in an order-three support, the remaining
tuple entry is another basis element and completes their sum to the target. -/
theorem exists_thirdSummand
    {A : Set ℕ} {n : ℕ} {E : Finset ℕ} {x z : ℕ}
    (hER : E ∈ additiveSupportFamily A 3 n)
    (hxE : x ∈ E) (hzE : z ∈ E) (hxz : x ≠ z) :
    ∃ u, u ∈ A ∧ u ∈ E ∧ x + z + u = n := by
  obtain ⟨v, hvA, hvsum, rfl⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  obtain ⟨i, hi⟩ := mem_tupleSupport_iff.mp hxE
  obtain ⟨j, hj⟩ := mem_tupleSupport_iff.mp hzE
  have hsum : (v 0).1 + ((v 1).1 + (v 2).1) = n := by
    simpa [Fin.sum_univ_succ] using hvsum
  fin_cases i <;> fin_cases j
  · exact (hxz (hi.symm.trans hj)).elim
  · refine ⟨(v 2).1, hvA 2,
      mem_tupleSupport_iff.mpr ⟨2, rfl⟩, ?_⟩
    change (v 0).1 = x at hi
    change (v 1).1 = z at hj
    rw [← hi, ← hj]
    omega
  · refine ⟨(v 1).1, hvA 1,
      mem_tupleSupport_iff.mpr ⟨1, rfl⟩, ?_⟩
    change (v 0).1 = x at hi
    change (v 2).1 = z at hj
    rw [← hi, ← hj]
    omega
  · refine ⟨(v 2).1, hvA 2,
      mem_tupleSupport_iff.mpr ⟨2, rfl⟩, ?_⟩
    change (v 1).1 = x at hi
    change (v 0).1 = z at hj
    rw [← hi, ← hj]
    omega
  · exact (hxz (hi.symm.trans hj)).elim
  · refine ⟨(v 0).1, hvA 0,
      mem_tupleSupport_iff.mpr ⟨0, rfl⟩, ?_⟩
    change (v 1).1 = x at hi
    change (v 2).1 = z at hj
    rw [← hi, ← hj]
    omega
  · refine ⟨(v 1).1, hvA 1,
      mem_tupleSupport_iff.mpr ⟨1, rfl⟩, ?_⟩
    change (v 2).1 = x at hi
    change (v 0).1 = z at hj
    rw [← hi, ← hj]
    omega
  · refine ⟨(v 0).1, hvA 0,
      mem_tupleSupport_iff.mpr ⟨0, rfl⟩, ?_⟩
    change (v 2).1 = x at hi
    change (v 1).1 = z at hj
    rw [← hi, ← hj]
    omega
  · exact (hxz (hi.symm.trans hj)).elim

/-- Three distinct vertices in an order-three support occur exactly once
each, so their sum is the represented target. -/
theorem sum_eq_of_three_distinct_mem
    {A : Set ℕ} {n : ℕ} {E : Finset ℕ} {x y z : ℕ}
    (hER : E ∈ additiveSupportFamily A 3 n)
    (hxE : x ∈ E) (hyE : y ∈ E) (hzE : z ∈ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    x + y + z = n := by
  classical
  let S : Finset ℕ := {x, y, z}
  have hSsub : S ⊆ E := by
    intro w hw
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxE
    · exact hyE
    · exact hzE
  have hScard : S.card = 3 := by
    simp [S, hxy, hxz, hyz]
  have hEcardLe : E.card ≤ 3 :=
    additiveSupportFamily_cardAtMost A 3 n E hER
  have hSE : S = E := by
    apply Finset.eq_of_subset_of_card_le hSsub
    simpa [hScard] using hEcardLe
  obtain ⟨v, _hvA, hvsum, hvSupport⟩ :=
    mem_additiveSupportFamily_iff.mp hER
  have himageCard :
      (Finset.univ.image fun i : Fin 3 => (v i).1).card =
        (Finset.univ : Finset (Fin 3)).card := by
    rw [← tupleSupport]
    rw [hvSupport, ← hSE, hScard]
    simp
  have hinj : Set.InjOn (fun i : Fin 3 => (v i).1)
      ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) :=
    Finset.card_image_iff.mp himageCard
  have hsupportSum : E.sum id = n := by
    rw [← hvSupport, tupleSupport, Finset.sum_image]
    · simpa using hvsum
    · exact hinj
  rw [← hSE] at hsupportSum
  simp [S, hxy, hxz, hyz] at hsupportSum
  omega

/-- If two distinct support vertices and a third basis element already sum
to the target, those three values contain the entire order-three support. -/
theorem support_subset_triple_of_sum
    {A : Set ℕ} {n : ℕ} {E : Finset ℕ} {x z u : ℕ}
    (hER : E ∈ additiveSupportFamily A 3 n)
    (hxE : x ∈ E) (hzE : z ∈ E) (hxz : x ≠ z)
    (hsum : x + z + u = n) :
    E ⊆ {x, z, u} := by
  intro w hwE
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_cases hwx : w = x
  · exact Or.inl hwx
  by_cases hwz : w = z
  · exact Or.inr (Or.inl hwz)
  have hsumW : x + z + w = n :=
    sum_eq_of_three_distinct_mem hER hxE hzE hwE
      hxz (fun h => hwx h.symm) (fun h => hwz h.symm)
  exact Or.inr (Or.inr (by omega))

/-- The part of the chosen repair support outside the destroyer. -/
def tail {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (x : {x // x ∈ D}) : Finset ℕ :=
  c.support x \ D

/-- Every order-three repair tail has at most two distinct vertices. -/
theorem tail_card_le_two
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (x : {x // x ∈ D}) :
    (c.tail x).card ≤ 2 := by
  have hsupportCard : (c.support x).card ≤ 3 :=
    additiveSupportFamily_cardAtMost A 3 n
      (c.support x) (c.support_mem x)
  rw [tail, Finset.card_sdiff]
  have hinter : D ∩ c.support x = {x.1} := by
    rw [Finset.inter_comm, c.unique_hit x]
  rw [hinter]
  simp only [Finset.card_singleton]
  omega

/-- Beyond the finite-core escape threshold, every chosen repair tail is
nonempty. -/
theorem tail_nonempty_of_large
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hn : 3 * D.sum id + 1 ≤ n)
    (x : {x // x ∈ D}) :
    (c.tail x).Nonempty := by
  rw [tail, Finset.sdiff_nonempty]
  intro hsubset
  obtain ⟨v, _hvA, hvsum, hvSupport⟩ :=
    mem_additiveSupportFamily_iff.mp (c.support_mem x)
  have hvle : ∀ i, (v i).1 ≤ D.sum id := by
    intro i
    apply Finset.single_le_sum (s := D) (f := id)
      (fun _ _ => Nat.zero_le _)
    apply hsubset
    rw [← hvSupport]
    exact mem_tupleSupport_iff.mpr ⟨i, rfl⟩
  have hsumle :
      ∑ i, (v i).1 ≤ ∑ _i : Fin 3, D.sum id := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hvle i
  have hsumle' :
      (v 0).1 + ((v 1).1 + (v 2).1) ≤ 3 * D.sum id := by
    simpa [Fin.sum_univ_succ] using hsumle
  have hvsum' : (v 0).1 + ((v 1).1 + (v 2).1) = n := by
    simpa [Fin.sum_univ_succ] using hvsum
  omega

/-- A common repair anchor reflects each destroyer vertex through the fixed
center `n - z`.  The third summand is either the destroyer vertex itself or
lies outside the destroyer. -/
theorem commonAnchor_reflection
    {A : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x) :
    ∀ x : {x // x ∈ D},
      ∃ u, u ∈ A ∧ u ∈ c.support x ∧
        (u = x.1 ∨ u ∉ D) ∧ x.1 + z + u = n := by
  intro x
  have hxSupport : x.1 ∈ c.support x := by
    have hxInter : x.1 ∈ c.support x ∩ D := by
      rw [c.unique_hit x]
      simp
    exact (Finset.mem_inter.mp hxInter).1
  have hzSupport : z ∈ c.support x := (Finset.mem_sdiff.mp (hz x)).1
  have hzD : z ∉ D := (Finset.mem_sdiff.mp (hz x)).2
  have hxz : x.1 ≠ z := fun hxz => hzD (hxz ▸ x.2)
  obtain ⟨u, huA, huSupport, hsum⟩ :=
    exists_thirdSummand (c.support_mem x) hxSupport hzSupport hxz
  have huOutside : u = x.1 ∨ u ∉ D := by
    by_cases huD : u ∈ D
    · left
      have huInter : u ∈ c.support x ∩ D :=
        Finset.mem_inter.mpr ⟨huSupport, huD⟩
      rw [c.unique_hit x] at huInter
      simpa using huInter
    · exact Or.inr huD
  exact ⟨u, huA, huSupport, huOutside, hsum⟩

/-- Equal two-point tails can only belong to the same destroyer vertex. -/
theorem eq_of_tail_eq_pair
    {A : Set ℕ} {D : Finset ℕ} {n a b : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hab : a ≠ b)
    {x y : {x // x ∈ D}}
    (hx : c.tail x = {a, b})
    (hy : c.tail y = {a, b}) :
    x = y := by
  have haTailX : a ∈ c.tail x := by simp [hx]
  have hbTailX : b ∈ c.tail x := by simp [hx]
  have haTailY : a ∈ c.tail y := by simp [hy]
  have hbTailY : b ∈ c.tail y := by simp [hy]
  have hxa : x.1 ≠ a := fun h =>
    (Finset.mem_sdiff.mp haTailX).2 (h ▸ x.2)
  have hxb : x.1 ≠ b := fun h =>
    (Finset.mem_sdiff.mp hbTailX).2 (h ▸ x.2)
  have hya : y.1 ≠ a := fun h =>
    (Finset.mem_sdiff.mp haTailY).2 (h ▸ y.2)
  have hyb : y.1 ≠ b := fun h =>
    (Finset.mem_sdiff.mp hbTailY).2 (h ▸ y.2)
  have hxsum : x.1 + a + b = n :=
    sum_eq_of_three_distinct_mem (c.support_mem x)
      (by
        have hxInter : x.1 ∈ c.support x ∩ D := by
          rw [c.unique_hit x]
          simp
        exact (Finset.mem_inter.mp hxInter).1)
      (Finset.mem_sdiff.mp haTailX).1
      (Finset.mem_sdiff.mp hbTailX).1 hxa hxb hab
  have hysum : y.1 + a + b = n :=
    sum_eq_of_three_distinct_mem (c.support_mem y)
      (by
        have hyInter : y.1 ∈ c.support y ∩ D := by
          rw [c.unique_hit y]
          simp
        exact (Finset.mem_inter.mp hyInter).1)
      (Finset.mem_sdiff.mp haTailY).1
      (Finset.mem_sdiff.mp hbTailY).1 hya hyb hab
  apply Subtype.ext
  omega

/-- An inclusion-minimal order-three destroyer supplies a simultaneous
choice of unique-hit repairs. -/
theorem nonempty_of_minimal
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A 3) D n) :
    Nonempty (OrderThreeUniqueHitRepairChoice A D n) := by
  classical
  let witness (x : {x // x ∈ D}) :=
    Classical.choose (hminimal.exists_uniqueHitSupport x.2)
  have hwitness (x : {x // x ∈ D}) :
      witness x ∈ additiveSupportFamily A 3 n ∧
        witness x ∩ D = {x.1} :=
    Classical.choose_spec (hminimal.exists_uniqueHitSupport x.2)
  exact ⟨{
    support := witness
    support_mem := fun x => (hwitness x).1
    unique_hit := fun x => (hwitness x).2
  }⟩

/-- Complete classification of the chosen repair tails at a sufficiently
large target.  Either two tails are disjoint, all tails share one common
anchor, or every tail is one of the three edges of a triangle. -/
theorem disjoint_or_commonAnchor_or_triangle
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hD : D.Nonempty)
    (htailNonempty : ∀ x : {x // x ∈ D}, (c.tail x).Nonempty) :
    (∃ x y : {x // x ∈ D}, Disjoint (c.tail x) (c.tail y)) ∨
      (∃ z, ∀ x : {x // x ∈ D}, z ∈ c.tail x) ∨
      ∃ a b d, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
        ∀ x : {x // x ∈ D},
          c.tail x = {a, b} ∨ c.tail x = {a, d} ∨
            c.tail x = {b, d} := by
  classical
  by_cases hdisjoint :
      ∃ x y : {x // x ∈ D}, Disjoint (c.tail x) (c.tail y)
  · exact Or.inl hdisjoint
  · have hinter : ∀ x y : {x // x ∈ D},
        ¬ Disjoint (c.tail x) (c.tail y) := by
      push Not at hdisjoint
      exact hdisjoint
    let 𝒯 : Set (Finset ℕ) := Set.range c.tail
    have h𝒯 : 𝒯.Nonempty := by
      obtain ⟨x, hxD⟩ := hD
      exact ⟨c.tail ⟨x, hxD⟩, ⟨⟨x, hxD⟩, rfl⟩⟩
    have hnonempty : ∀ E ∈ 𝒯, E.Nonempty := by
      rintro E ⟨x, rfl⟩
      exact htailNonempty x
    have hcard : ∀ E ∈ 𝒯, E.card ≤ 2 := by
      rintro E ⟨x, rfl⟩
      exact c.tail_card_le_two x
    have hfamilyIntersect : ∀ E ∈ 𝒯, ∀ F ∈ 𝒯,
        ¬ Disjoint E F := by
      rintro E ⟨x, rfl⟩ F ⟨y, rfl⟩
      exact hinter x y
    obtain hstar | htriangle :=
      pairwiseIntersecting_card_le_two_star_or_triangle
        𝒯 h𝒯 hnonempty hcard hfamilyIntersect
    · right; left
      obtain ⟨z, hz⟩ := hstar
      exact ⟨z, fun x => hz (c.tail x) ⟨x, rfl⟩⟩
    · right; right
      obtain ⟨a, b, d, hab, had, hbd, htriangle⟩ := htriangle
      exact ⟨a, b, d, hab, had, hbd,
        fun x => htriangle (c.tail x) ⟨x, rfl⟩⟩

/-- For a destroyer with at least four vertices the triangle exception is
impossible.  Thus either two distinct repair tails are disjoint, or every
chosen repair tail contains one common anchor. -/
theorem disjoint_or_commonAnchor_of_four_le_card
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hDcard : 4 ≤ D.card) :
    (∃ x y : {x // x ∈ D}, x ≠ y ∧
      Disjoint (c.tail x) (c.tail y)) ∨
      ∃ z, ∀ x : {x // x ∈ D}, z ∈ c.tail x := by
  classical
  have hD : D.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hdistinctDisjoint :
      ∃ x y : {x // x ∈ D}, x ≠ y ∧
        Disjoint (c.tail x) (c.tail y)
  · exact Or.inl hdistinctDisjoint
  · have htailNonempty :
        ∀ x : {x // x ∈ D}, (c.tail x).Nonempty := by
      intro x
      obtain ⟨y, hyD, hyx⟩ :=
        Finset.exists_mem_ne (s := D) (by omega) x.1
      let y' : {y // y ∈ D} := ⟨y, hyD⟩
      have hxy : x ≠ y' := by
        intro hxy
        exact hyx (congrArg Subtype.val hxy).symm
      have hnotDisjoint : ¬ Disjoint (c.tail x) (c.tail y') := by
        intro hdisj
        exact hdistinctDisjoint ⟨x, y', hxy, hdisj⟩
      obtain ⟨z, hz, _hz'⟩ := Finset.not_disjoint_iff.mp hnotDisjoint
      exact ⟨z, hz⟩
    obtain hdisjoint | hcommon | htriangle :=
      c.disjoint_or_commonAnchor_or_triangle hD htailNonempty
    · left
      obtain ⟨x, y, hxyDisjoint⟩ := hdisjoint
      have hxy : x ≠ y := by
        intro hxy
        subst y
        obtain ⟨z, hz⟩ := htailNonempty x
        exact (Finset.not_disjoint_iff.mpr ⟨z, hz, hz⟩) hxyDisjoint
      exact ⟨x, y, hxy, hxyDisjoint⟩
    · exact Or.inr hcommon
    · obtain ⟨a, b, d, hab, had, hbd, htails⟩ := htriangle
      have htailInjective : Function.Injective c.tail := by
        intro x y hxy
        rcases htails x with hx | hx | hx
        · exact c.eq_of_tail_eq_pair hab hx (hxy.symm.trans hx)
        · exact c.eq_of_tail_eq_pair had hx (hxy.symm.trans hx)
        · exact c.eq_of_tail_eq_pair hbd hx (hxy.symm.trans hx)
      let imageTails : Finset (Finset ℕ) :=
        (Finset.univ : Finset {x // x ∈ D}).image c.tail
      let triangle : Finset (Finset ℕ) :=
        {{a, b}, {a, d}, {b, d}}
      have himageCard : imageTails.card = D.card := by
        change ((Finset.univ : Finset {x // x ∈ D}).image c.tail).card =
          D.card
        rw [Finset.card_image_iff.mpr htailInjective.injOn]
        simp
      have himageSubset : imageTails ⊆ triangle := by
        intro E hE
        change E ∈ (Finset.univ : Finset {x // x ∈ D}).image c.tail at hE
        obtain ⟨x, _hx, rfl⟩ := Finset.mem_image.mp hE
        rcases htails x with hx | hx | hx
        · simp [triangle, hx]
        · simp [triangle, hx]
        · simp [triangle, hx]
      have htriangleCard : triangle.card ≤ 3 := by
        exact Finset.card_insert_le _ _ |>.trans <|
          Nat.succ_le_succ <| Finset.card_le_two
      have himageLe : imageTails.card ≤ 3 :=
        (Finset.card_le_card himageSubset).trans htriangleCard
      omega

/-- In a common-anchor repair system the reflected third summand is an
injective function of the destroyer vertex.  At most one vertex is reflected
to itself; every other partner lies outside the destroyer. -/
theorem commonAnchor_injectivePartners
    {A : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x) :
    ∃ partner : {x // x ∈ D} → ℕ,
      (∀ x, partner x ∈ A) ∧
      (∀ x, partner x ∈ c.support x) ∧
      (∀ x, partner x = x.1 ∨ partner x ∉ D) ∧
      (∀ x, x.1 + z + partner x = n) ∧
      Function.Injective partner ∧
      ∀ x y, partner x = x.1 → partner y = y.1 → x = y := by
  classical
  have hreflect := c.commonAnchor_reflection hz
  choose partner hpartnerA hpartnerSupport hpartnerOutside hpartnerSum
    using hreflect
  refine ⟨partner, hpartnerA, hpartnerSupport,
    hpartnerOutside, hpartnerSum, ?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    have hxsum := hpartnerSum x
    have hysum := hpartnerSum y
    omega
  · intro x y hxx hyy
    apply Subtype.ext
    have hxsum := hpartnerSum x
    have hysum := hpartnerSum y
    omega

end OrderThreeUniqueHitRepairChoice

/-! ## Minimal-destroyer consequence -/

/-- Every sum of two distinct points of `K` has only its canonical pair
support in the ambient order-two basis. -/
def IsPairwiseRigidSet (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y → IsRigidPairSum A x y

/-- No distinct pair in `K` has a rigid pair sum. -/
def IsPairwiseNonrigidSet (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ¬ IsRigidPairSum A x y

/-- No double `2x` with `x ∈ K` has only its canonical singleton support. -/
def HasNoRigidDoubles (A K : Set ℕ) : Prop :=
  ∀ x ∈ K, ¬ IsRigidPairSum A x x

/-- On an infinite nonrigid set, every finite reservation stage extends.
Choosing the new point above twice the sum of the old deletion prefix turns
any support trapped in `D ∪ {b}` into a genuinely rigid pair, contradicting
the hypotheses. -/
theorem hasFreshPairRepairExtension_of_pairwiseNonrigid
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hnonrigid : IsPairwiseNonrigidSet A K)
    (hdouble : HasNoRigidDoubles A K)
    (D P : Finset ℕ) (hDK : (D : Set ℕ) ⊆ K) (T : ℕ) :
    HasFreshPairRepairExtension A K D P T := by
  classical
  let excluded : Set ℕ :=
    (D : Set ℕ) ∪ (P : Set ℕ) ∪
      Set.Iio (max T (2 * D.sum id + 1))
  have hexcluded : excluded.Finite :=
    (D.finite_toSet.union P.finite_toSet).union
      (Set.finite_Iio (max T (2 * D.sum id + 1)))
  obtain ⟨b, hbK, hbExcluded⟩ := hK.exists_notMem_finite hexcluded
  have hbD : b ∉ D := by
    intro hbD
    exact hbExcluded (Or.inl (Or.inl hbD))
  have hbP : b ∉ P := by
    intro hbP
    exact hbExcluded (Or.inl (Or.inr hbP))
  have hbLower : max T (2 * D.sum id + 1) ≤ b := by
    exact Nat.le_of_not_gt fun hbLt => hbExcluded (Or.inr hbLt)
  have hbT : T ≤ b := le_trans (le_max_left _ _) hbLower
  have hbLarge : 2 * D.sum id < b := by
    have : 2 * D.sum id + 1 ≤ b :=
      le_trans (le_max_right _ _) hbLower
    omega
  refine ⟨b, hbK, hbD, hbP, hbT, ?_⟩
  intro d hd
  by_contra hnoSupport
  push Not at hnoSupport
  have hrigid : IsRigidPairSum A b d :=
    rigidPairSum_of_supports_subset_insert hbLarge hnoSupport
  rcases Finset.mem_insert.mp hd with hdb | hdD
  · subst d
    exact hdouble b hbK hrigid
  · exact hnonrigid b hbK d (hDK hdD)
      (fun hbd => hbD (hbd ▸ hdD)) hrigid

/-- Data selected at one stage of the reserved-pair recursion. -/
structure ReservedPairRecursionStep
    (A K : Set ℕ) (D P : Finset ℕ) (last : ℕ) where
  point : ℕ
  point_mem : point ∈ K
  point_not_chosen : point ∉ D
  point_not_reserved : point ∉ P
  point_lower : last + 1 ≤ point
  support : {d // d ∈ insert point D} → Finset ℕ
  support_mem : ∀ d,
    support d ∈ additiveSupportFamily A 2 (point + d.1)
  witness : {d // d ∈ insert point D} → ℕ
  witness_mem : ∀ d, witness d ∈ support d
  witness_fresh : ∀ d, witness d ∉ insert point D

/-- A fresh-extension witness supplies a recursion step. -/
theorem reservedPairRecursionStep_nonempty
    {A K : Set ℕ} {D P : Finset ℕ} {last : ℕ}
    (hext : HasFreshPairRepairExtension A K D P (last + 1)) :
    Nonempty (ReservedPairRecursionStep A K D P last) := by
  classical
  obtain ⟨b, hbK, hbD, hbP, hbLower, hrepair⟩ := hext
  have hsupport : ∀ d : {d // d ∈ insert b D},
      ∃ E ∈ additiveSupportFamily A 2 (b + d.1),
        ¬ E ⊆ insert b D := fun d => hrepair d.1 d.2
  choose support hsupportMem hsupportFresh using hsupport
  have hwitness : ∀ d : {d // d ∈ insert b D},
      ∃ z ∈ support d, z ∉ insert b D := by
    intro d
    exact Finset.not_subset.mp (hsupportFresh d)
  choose witness hwitnessMem hwitnessFresh using hwitness
  exact ⟨{
    point := b
    point_mem := hbK
    point_not_chosen := hbD
    point_not_reserved := hbP
    point_lower := hbLower
    support := support
    support_mem := hsupportMem
    witness := witness
    witness_mem := hwitnessMem
    witness_fresh := hwitnessFresh
  }⟩

/-- Finite state of the reserved-pair recursion. -/
structure ReservedPairRecursionState (K : Set ℕ) where
  chosen : Finset ℕ
  reserved : Finset ℕ
  last : ℕ
  chosen_subset : (chosen : Set ℕ) ⊆ K
  chosen_disjoint_reserved : Disjoint chosen reserved

/-- Iterating fresh repair extensions constructs an infinite deletion with a
permanently blue witness in an alternative support of every red-red sum. -/
theorem exists_reservedPairDeletion_of_freshExtensions
    {A K : Set ℕ}
    (hext : ∀ (D P : Finset ℕ), (D : Set ℕ) ⊆ K → ∀ T,
      HasFreshPairRepairExtension A K D P T) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasReservedAlternativePairSupports A B Bᶜ := by
  classical
  let State := ReservedPairRecursionState K
  let initial : State := {
    chosen := ∅
    reserved := ∅
    last := 0
    chosen_subset := by simp
    chosen_disjoint_reserved := by simp
  }
  let chooseStep : (s : State) →
      ReservedPairRecursionStep A K s.chosen s.reserved s.last :=
    fun s => Classical.choice <|
      reservedPairRecursionStep_nonempty
        (hext s.chosen s.reserved s.chosen_subset (s.last + 1))
  let newReserved (s : State) : Finset ℕ :=
    (insert (chooseStep s).point s.chosen).attach.image
      (chooseStep s).witness
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
      · obtain ⟨d, _hdAttach, hxd⟩ := Finset.mem_image.mp hxNew
        have hxFresh := (chooseStep s).witness_fresh d
        apply hxFresh
        rw [hxd]
        exact hxChosen
  }
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let step (i : ℕ) := chooseStep (state i)
  let b (i : ℕ) := (step i).point
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
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
    change (state (i + 1)).last + 1 ≤ b (i + 1) at hlower
    rw [hlast_succ] at hlower
    exact Nat.lt_of_succ_le hlower
  have hprior_chosen : ∀ {i j}, i < j → b i ∈ (state j).chosen := by
    intro i j hij
    exact hchosen_mono (Nat.succ_le_of_lt hij) (hb_chosen_next i)
  have witness_not_range : ∀ (j : ℕ)
      (d : {d // d ∈ insert (b j) (state j).chosen}),
      (step j).witness d ∉ Set.range b := by
    intro j d hwRange
    obtain ⟨i, hi⟩ := hwRange
    have hwFresh := (step j).witness_fresh d
    by_cases hij : i ≤ j
    · apply hwFresh
      rw [← hi]
      by_cases hijEq : i = j
      · subst i
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hprior_chosen (lt_of_le_of_ne hij hijEq))
    · have hji : j < i := Nat.lt_of_not_ge hij
      have hwNew : (step j).witness d ∈ newReserved (state j) := by
        apply Finset.mem_image.mpr
        exact ⟨d, Finset.mem_attach _ d, rfl⟩
      have hwReservedNext :
          (step j).witness d ∈ (state (j + 1)).reserved := by
        rw [hreserved_succ]
        exact Finset.mem_union_right _ hwNew
      have hwReserved : (step j).witness d ∈ (state i).reserved :=
        hreserved_mono (Nat.succ_le_of_lt hji) hwReservedNext
      have hbNotReserved := (step i).point_not_reserved
      apply hbNotReserved
      change b i ∈ (state i).reserved
      rw [hi]
      exact hwReserved
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbK i
  · refine ⟨disjoint_compl_right, ?_⟩
    intro x hxB y hyB
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
        change E ∈ additiveSupportFamily A 2 (b j + b i) at hmem
        rw [Nat.add_comm] at hmem
        exact hmem
      · apply Set.not_disjoint_iff.mpr
        refine ⟨(step j).witness d, (step j).witness_mem d, ?_⟩
        exact witness_not_range j d
    · have hbj : b j ∈ insert (b i) (state i).chosen := by
        by_cases hjiEq : j = i
        · subst j
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hprior_chosen (lt_of_le_of_ne hji hjiEq))
      let d : {d // d ∈ insert (b i) (state i).chosen} := ⟨b j, hbj⟩
      let E := (step i).support d
      refine ⟨E, ?_, ?_⟩
      · have hmem := (step i).support_mem d
        change E ∈ additiveSupportFamily A 2 (b i + b j) at hmem
        exact hmem
      · apply Set.not_disjoint_iff.mpr
        refine ⟨(step i).witness d, (step i).witness_mem d, ?_⟩
        exact witness_not_range i d

/-- The nonrigid Ramsey branch therefore always produces a reserved-pair
deletion. -/
theorem exists_reservedPairDeletion_of_pairwiseNonrigid
    {A K : Set ℕ}
    (hK : K.Infinite)
    (hnonrigid : IsPairwiseNonrigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      HasReservedAlternativePairSupports A B Bᶜ := by
  apply exists_reservedPairDeletion_of_freshExtensions
  intro D P hDK T
  exact hasFreshPairRepairExtension_of_pairwiseNonrigid
    hK hnonrigid hdouble D P hDK T

/-- Complete closure of the nonrigid branch of the splittable-independent
strategy.  If an infinite pairwise-nonrigid set with nonrigid doubles lies in
a self-basis deletion reservoir, then an infinite subset can be deleted while
the complement remains an exact order-three basis. -/
theorem exists_infiniteDeletion_threeBasis_of_nonrigidSelfBasisReservoir
    {A B₀ K : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hB₀A : B₀ ⊆ A)
    (hself : IsExactTupleAsymptoticBasisAlong (A \ B₀) 2 A)
    (hKB₀ : K ⊆ B₀)
    (hK : K.Infinite)
    (hnonrigid : IsPairwiseNonrigidSet A K)
    (hdouble : HasNoRigidDoubles A K) :
    ∃ B, B ⊆ K ∧ B.Infinite ∧
      IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨B, hBK, hB, hrepair⟩ :=
    exists_reservedPairDeletion_of_pairwiseNonrigid
      hK hnonrigid hdouble
  have hselection : IsRedBluePairSupportSelection A B :=
    redBluePairSupportSelection_of_reserved_thinning
      hbasis hB₀A (fun x hx => hKB₀ (hBK hx)) hB hself hrepair
  have hclean := redBluePairSupportSelection_iff.mp hselection
  obtain ⟨B', hB'B, hsplittable⟩ := hclean.exists_tail_splittable
  exact ⟨B', fun x hx => hBK (hB'B hx), hsplittable.2.1,
    hsplittable.exactThreeBasis⟩

/-- In a common-anchor system supported on a pairwise-rigid reservoir `K`,
at most two reflected partners can remain in `K`.  All other partners lie in
the blue complement of `K`. -/
theorem commonAnchor_partnersIn_pairwiseRigidSet_le_two
    {A K : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x)
    (hDK : (D : Set ℕ) ⊆ K)
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K) :
    ∃ partner : {x // x ∈ D} → ℕ,
      (∀ x, partner x ∈ A) ∧
      (∀ x, partner x ∈ c.support x) ∧
      (∀ x, partner x = x.1 ∨ partner x ∉ D) ∧
      (∀ x, x.1 + z + partner x = n) ∧
      Function.Injective partner ∧
      (∀ x y, partner x = x.1 → partner y = y.1 → x = y) ∧
      ∃ internal : Finset {x // x ∈ D},
        (∀ x, x ∈ internal ↔
          partner x ∈ K ∧ partner x ≠ x.1) ∧
        internal.card ≤ 2 := by
  classical
  obtain ⟨partner, hpartnerA, hpartnerSupport,
      hpartnerOutside, hpartnerSum,
      hpartnerInjective, hfixed⟩ :=
    c.commonAnchor_injectivePartners hz
  let internal : Finset {x // x ∈ D} :=
    Finset.univ.filter fun x => partner x ∈ K ∧ partner x ≠ x.1
  have pair_forces_other
      {x y : {x // x ∈ D}}
      (hxInternal : x ∈ internal) (hyInternal : y ∈ internal)
      (hxy : x ≠ y) :
      y.1 = partner x := by
    have hxData := (Finset.mem_filter.mp hxInternal).2
    have hyData := (Finset.mem_filter.mp hyInternal).2
    have hxK : x.1 ∈ K := hDK x.2
    have hyK : y.1 ∈ K := hDK y.2
    have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hsum : x.1 + partner x = y.1 + partner y := by
      have hxsum := hpartnerSum x
      have hysum := hpartnerSum y
      omega
    have hyLe : y.1 ≤ x.1 + partner x := by omega
    have hcomp : x.1 + partner x - y.1 = partner y := by omega
    have hpairY : pairSupport (x.1 + partner x) y.1 ∈
        additiveSupportFamily A 2 (x.1 + partner x) := by
      apply pairSupport_mem_additiveSupportFamily hyLe
      · exact hKA hyK
      · rw [hcomp]
        exact hKA hyData.1
    have hpairEq :=
      hrigid x.1 hxK (partner x) hxData.1 hxData.2.symm
        (pairSupport (x.1 + partner x) y.1) hpairY
    have hyMem : y.1 ∈ pairSupport (x.1 + partner x) y.1 := by
      simp [pairSupport]
    rw [hpairEq] at hyMem
    simp only [pairSupport, Finset.mem_insert,
      Finset.mem_singleton] at hyMem
    have hcanonicalComp : x.1 + partner x - x.1 = partner x := by
      omega
    rw [hcanonicalComp] at hyMem
    exact hyMem.resolve_left hxyVal.symm
  have hinternalCard : internal.card ≤ 2 := by
    by_contra hnot
    have hthree : 2 < internal.card := Nat.lt_of_not_ge hnot
    obtain ⟨x, y, w, hx, hy, hw, hxy, hxw, hyw⟩ :=
      Finset.two_lt_card_iff.mp hthree
    have hyEq := pair_forces_other hx hy hxy
    have hwEq := pair_forces_other hx hw hxw
    have hywVal : y.1 = w.1 := hyEq.trans hwEq.symm
    exact hyw (Subtype.ext hywVal)
  refine ⟨partner, hpartnerA, hpartnerSupport,
    hpartnerOutside, hpartnerSum,
    hpartnerInjective, hfixed, internal, ?_, hinternalCard⟩
  intro x
  simp [internal]

/-- With at least four destroyer vertices, the preceding `2 + 1` bound
forces one reflected repair partner outside the rigid reservoir. -/
theorem commonAnchor_exists_externalPartner_of_four_le_card
    {A K : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x)
    (hDcard : 4 ≤ D.card)
    (hDK : (D : Set ℕ) ⊆ K)
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K) :
    ∃ x : {x // x ∈ D}, ∃ u,
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
  have hexternal : ∃ x : {x // x ∈ D}, partner x ∉ K := by
    by_contra hno
    push Not at hno
    have hcover : (Finset.univ : Finset {x // x ∈ D}) ⊆
        internal ∪ fixed := by
      intro x _hx
      by_cases hpx : partner x = x.1
      · exact Finset.mem_union_right _ <|
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpx⟩
      · exact Finset.mem_union_left _ <|
          (hinternal x).mpr ⟨hno x, hpx⟩
    have hcardCover : D.card ≤ (internal ∪ fixed).card := by
      simpa using Finset.card_le_card hcover
    have hunionCard : (internal ∪ fixed).card ≤ 3 := by
      calc
        (internal ∪ fixed).card ≤ internal.card + fixed.card :=
          Finset.card_union_le internal fixed
        _ ≤ 2 + 1 := Nat.add_le_add hinternalCard hfixedCard
        _ = 3 := by omega
    omega
  obtain ⟨x, hxExternal⟩ := hexternal
  have hxSupport : x.1 ∈ c.support x := by
    have hxInter : x.1 ∈ c.support x ∩ D := by
      rw [c.unique_hit x]
      simp
    exact (Finset.mem_inter.mp hxInter).1
  have hzSupport : z ∈ c.support x := (Finset.mem_sdiff.mp (hz x)).1
  have hxz : x.1 ≠ z := fun hxz =>
    (Finset.mem_sdiff.mp (hz x)).2 (hxz ▸ x.2)
  exact ⟨x, partner x, hpartnerA x, hxExternal,
    hpartnerSupport x,
    OrderThreeUniqueHitRepairChoice.support_subset_triple_of_sum
      (c.support_mem x)
      hxSupport hzSupport hxz (hpartnerSum x),
    hpartnerSum x⟩

/-- Hence a common-anchor destroyer inside a rigid reservoir has a repair
support whose only possible red vertices are its unique hit `x` and the
common anchor `z`.  If the anchor is reserved blue, the support meets the
entire reservoir exactly at `x`. -/
theorem commonAnchor_exists_almostGlobalUniqueHit
    {A K : Set ℕ} {D : Finset ℕ} {n z : ℕ}
    (c : OrderThreeUniqueHitRepairChoice A D n)
    (hz : ∀ x : {x // x ∈ D}, z ∈ c.tail x)
    (hDcard : 4 ≤ D.card)
    (hDK : (D : Set ℕ) ⊆ K)
    (hKA : K ⊆ A)
    (hrigid : IsPairwiseRigidSet A K) :
    ∃ x : {x // x ∈ D}, ∃ E ∈ additiveSupportFamily A 3 n,
      x.1 ∈ E ∧
      (((E : Set ℕ) ∩ K) ⊆ ({x.1, z} : Set ℕ)) ∧
      (z ∉ K → ((E : Set ℕ) ∩ K) = ({x.1} : Set ℕ)) := by
  obtain ⟨x, u, _huA, huK, huSupport, hsupport, _hsum⟩ :=
    commonAnchor_exists_externalPartner_of_four_le_card
      c hz hDcard hDK hKA hrigid
  have hxSupport : x.1 ∈ c.support x := by
    have hxInter : x.1 ∈ c.support x ∩ D := by
      rw [c.unique_hit x]
      simp
    exact (Finset.mem_inter.mp hxInter).1
  refine ⟨x, c.support x, c.support_mem x, hxSupport, ?_, ?_⟩
  · rintro w ⟨hwSupport, hwK⟩
    have hw := hsupport hwSupport
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simp
    · simp
    · exact (huK hwK).elim
  · intro hzK
    apply Set.Subset.antisymm
    · rintro w ⟨hwSupport, hwK⟩
      have hw := hsupport hwSupport
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · simp
      · exact (hzK hwK).elim
      · exact (huK hwK).elim
    · intro w hw
      have hwx : w = x.1 := by simpa using hw
      subst w
      exact ⟨hxSupport, hDK x.2⟩

/-- A common-anchor system of unique-hit repairs for all vertices of `D`. -/
def HasCommonAnchorOrderThreeRepairs
    (A : Set ℕ) (D : Finset ℕ) (n : ℕ) : Prop :=
  ∃ c : OrderThreeUniqueHitRepairChoice A D n,
    ∃ z, ∀ x : {x // x ∈ D}, z ∈ c.tail x

/-- A sufficiently late inclusion-minimal order-three destroyer of size at
least four either supplies the desired pair of disjoint repairs, or has the
rigid common-anchor reflection form. -/
theorem minimalOrderThreeDestroyer_disjointRepairs_or_commonAnchor
    {A : Set ℕ} {D : Finset ℕ} {n : ℕ}
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A 3) D n)
    (hDcard : 4 ≤ D.card) :
    HasTwoDisjointUniqueHitRepairs
        (additiveSupportFamily A 3) D n ∨
      HasCommonAnchorOrderThreeRepairs A D n := by
  classical
  obtain ⟨c⟩ :=
    OrderThreeUniqueHitRepairChoice.nonempty_of_minimal hminimal
  obtain hdisjoint | hcommon :=
    c.disjoint_or_commonAnchor_of_four_le_card hDcard
  · left
    obtain ⟨x, y, hxy, htails⟩ := hdisjoint
    exact ⟨x.1, x.2, y.1, y.2,
      fun h => hxy (Subtype.ext h),
      c.support x, c.support_mem x,
      c.support y, c.support_mem y,
      c.unique_hit x, c.unique_hit y, htails⟩
  · right
    exact ⟨c, hcommon⟩

/-! ## Strong-deletion output -/

/-- Any (possibly infinite) destroyer contains a finite destroyer: choose one
hit from each support in the finite target hypergraph. -/
theorem exists_finiteDestroyer_subset
    {R : SupportFamily} {B : Set ℕ} {n : ℕ}
    (hdestroy : DestroysAt R B n) :
    ∃ D : Finset ℕ, (D : Set ℕ) ⊆ B ∧
      DestroysAt R (D : Set ℕ) n := by
  classical
  have hhit : ∀ E : {E // E ∈ R n},
      ∃ x, x ∈ E.1 ∧ x ∈ B := by
    intro E
    exact Set.not_disjoint_iff.mp (hdestroy E.1 E.2)
  choose hit hhitE hhitB using hhit
  let D : Finset ℕ := (R n).attach.image hit
  refine ⟨D, ?_, ?_⟩
  · intro x hxD
    obtain ⟨E, _hEattach, rfl⟩ := Finset.mem_image.mp hxD
    exact hhitB E
  · intro E hER
    let e : {E // E ∈ R n} := ⟨E, hER⟩
    apply Set.not_disjoint_iff.mpr
    refine ⟨hit e, hhitE e, ?_⟩
    apply Finset.mem_coe.mpr
    apply Finset.mem_image.mpr
    exact ⟨e, by simp [e], rfl⟩

/-- Every finite destroyer contains an inclusion-minimal destroyer. -/
theorem exists_inclusionMinimalDestroyer_subset
    {R : SupportFamily} {D : Finset ℕ} {n : ℕ}
    (hdestroy : DestroysAt R (D : Set ℕ) n) :
    ∃ D₀ : Finset ℕ, D₀ ⊆ D ∧
      IsInclusionMinimalDestroyer R D₀ n := by
  classical
  let candidates : Finset (Finset ℕ) :=
    D.powerset.filter fun C => DestroysAt R (C : Set ℕ) n
  have hDcandidate : D ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hdestroy⟩
  have hcandidates : candidates.Nonempty := ⟨D, hDcandidate⟩
  obtain ⟨D₀, hD₀candidate, hminimalCard⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hD₀D : D₀ ⊆ D :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hD₀candidate).1
  have hD₀destroy : DestroysAt R (D₀ : Set ℕ) n :=
    (Finset.mem_filter.mp hD₀candidate).2
  refine ⟨D₀, hD₀D, hD₀destroy, ?_⟩
  intro x hxD₀ hEraseDestroy
  have hEraseD : D₀.erase x ⊆ D :=
    (Finset.erase_subset x D₀).trans hD₀D
  have hEraseCandidate : D₀.erase x ∈ candidates :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hEraseD, hEraseDestroy⟩
  have hcardMin : D₀.card ≤ (D₀.erase x).card :=
    hminimalCard (D₀.erase x) hEraseCandidate
  have hcardEq := Finset.card_erase_add_one hxD₀
  rw [← hcardEq] at hcardMin
  exact (Nat.not_succ_le_self _ hcardMin).elim

/-- Every infinite deletion under strong order-three deletion has arbitrarily
late finite minimal witnesses of one of exactly three forms: bounded size,
two disjoint unique-hit repairs, or a common-anchor reflection system. -/
theorem strongOrderThreeDeletion_late_minimalDestroyer_trichotomy
    {A B : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hBA : B ⊆ A) (hB : B.Infinite) :
    ∀ N, ∃ n, ∃ D : Finset ℕ,
      N ≤ n ∧ (D : Set ℕ) ⊆ B ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) D n ∧
      (D.card ≤ 3 ∨
        HasTwoDisjointUniqueHitRepairs
          (additiveSupportFamily A 3) D n ∨
        HasCommonAnchorOrderThreeRepairs A D n) := by
  intro N
  obtain ⟨n, hn, hBdestroy⟩ := hstrong B hBA hB N
  obtain ⟨D, hDB, hDdestroy⟩ :=
    exists_finiteDestroyer_subset hBdestroy
  obtain ⟨D₀, hD₀D, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hDdestroy
  refine ⟨n, D₀, hn, fun x hx => hDB (hD₀D hx), hminimal, ?_⟩
  by_cases hsmall : D₀.card ≤ 3
  · exact Or.inl hsmall
  · have hfour : 4 ≤ D₀.card := by omega
    obtain hrepairs | hanchor :=
      minimalOrderThreeDestroyer_disjointRepairs_or_commonAnchor
        hminimal hfour
    · exact Or.inr (Or.inl hrepairs)
    · exact Or.inr (Or.inr hanchor)

/-- Specialized strong-deletion output on an infinite pairwise-rigid
reservoir.  The common-anchor branch is sharpened to an order-three support
which meets the whole reservoir in at most the pair `{x,z}`. -/
theorem strongOrderThreeDeletion_on_pairwiseRigidSet_late_trichotomy
    {A K : Set ℕ}
    (hstrong : StrongInfiniteDeletion
      (additiveSupportFamily A 3) A)
    (hKA : K ⊆ A) (hK : K.Infinite)
    (hrigid : IsPairwiseRigidSet A K) :
    ∀ N, ∃ n, ∃ D : Finset ℕ,
      N ≤ n ∧ (D : Set ℕ) ⊆ K ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A 3) D n ∧
      (D.card ≤ 3 ∨
        HasTwoDisjointUniqueHitRepairs
          (additiveSupportFamily A 3) D n ∨
        ∃ z, ∃ x : {x // x ∈ D},
          ∃ E ∈ additiveSupportFamily A 3 n,
            x.1 ∈ E ∧
            (((E : Set ℕ) ∩ K) ⊆ ({x.1, z} : Set ℕ)) ∧
            (z ∉ K →
              ((E : Set ℕ) ∩ K) = ({x.1} : Set ℕ))) := by
  intro N
  obtain ⟨n, hn, hKdestroy⟩ := hstrong K hKA hK N
  obtain ⟨D, hDK, hDdestroy⟩ :=
    exists_finiteDestroyer_subset hKdestroy
  obtain ⟨D₀, hD₀D, hminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset hDdestroy
  have hD₀K : (D₀ : Set ℕ) ⊆ K := fun x hx => hDK (hD₀D hx)
  refine ⟨n, D₀, hn, hD₀K, hminimal, ?_⟩
  by_cases hsmall : D₀.card ≤ 3
  · exact Or.inl hsmall
  · have hfour : 4 ≤ D₀.card := by omega
    obtain hrepairs | hanchor :=
      minimalOrderThreeDestroyer_disjointRepairs_or_commonAnchor
        hminimal hfour
    · exact Or.inr (Or.inl hrepairs)
    · right; right
      obtain ⟨c, z, hz⟩ := hanchor
      obtain ⟨x, E, hER, hxE, hEK, hunique⟩ :=
        commonAnchor_exists_almostGlobalUniqueHit
          c hz hfour hD₀K hKA hrigid
      exact ⟨z, x, E, hER, hxE, hEK, hunique⟩

end Erdos881
