import Erdos881.AdditiveSupports
import Erdos881.MirrorPeriodicity
import Erdos881.TeamGuardianRigidity

/-!
# Bridging guardian rigidity to the support-family vocabulary

`GuardianRigidity`, `TeamGuardianRigidity`, and `MirrorPeriodicity` speak
`PairCovers` / `IsPrivateTriple`; the main development speaks
`IsExactTupleAsymptoticBasis` / `DestroysAt` / `additiveSupportFamily`.
This file makes the two vocabularies interchangeable:

* an exact order-two tuple basis gives `PairCovers`;
* a singleton destroyer at order three gives `IsPrivateTriple`, so a
  failed singleton deletion yields arbitrarily late private pairs — the
  raw material for `no_big_guardian_stacking` and the reflection stream;
* a surviving deletion in the guardian vocabulary is an exact order-three
  tuple basis of `A \ B`;
* consequently the master chain lands in repo vocabulary:
  `exactTupleBasis_orderThree_deletion_of_boundedGap_reflectionLevels`
  is the positive answer to the order-two instance of Erdős 881 under
  the bounded-gap mirror hypothesis.
-/

namespace Erdos881

/-- An exact order-two tuple basis pair-covers from its threshold on. -/
theorem pairCovers_of_exactTupleBasis {A : Set ℕ}
    (h : IsExactTupleAsymptoticBasis A 2) :
    ∃ N₀, PairCovers A N₀ := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨v, hvA, hvsum⟩ := hN n hn
  exact ⟨v 0, hvA 0, v 1, hvA 1, by simpa [Fin.sum_univ_two] using hvsum⟩

/-- A singleton destroyer at order three is a private guardian. -/
theorem isPrivateTriple_of_destroysAt {A : Set ℕ} {a m : ℕ}
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hdes : DestroysAt (additiveSupportFamily A 3) ({a} : Set ℕ) m) :
    IsPrivateTriple A a m := by
  refine ⟨hrep, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  rw [destroysAt_additiveSupportFamily_iff] at hdes
  refine hdes ⟨![x, y, z], ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp_all [Set.mem_diff, Set.mem_singleton_iff]
  · simpa [Fin.sum_univ_three] using hsum

/-- If deleting the single guardian `a` destroys the exact order-three
basis property of a covering set with zero, then `a` owns arbitrarily
late order-three private targets. -/
theorem exists_late_privateTriple_of_singletonDeletion
    {A : Set ℕ} {N₀ a : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ¬ IsExactTupleAsymptoticBasis
      (A \ (({a} : Finset ℕ) : Set ℕ)) 3) :
    ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A a m := by
  intro N
  obtain ⟨m, hm, hdes⟩ :=
    not_exactTupleAsymptoticBasis_diff_finset_iff.mp hfail (max N N₀)
  refine ⟨m, le_trans (le_max_left _ _) hm, ?_⟩
  have hdes' : DestroysAt (additiveSupportFamily A 3) ({a} : Set ℕ) m := by
    simpa using hdes
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    hcov m (le_trans (le_max_right _ _) hm)
  exact isPrivateTriple_of_destroysAt
    ⟨x, hx, y, hy, 0, h0, by omega⟩ hdes'

/-- A surviving deletion in guardian vocabulary is an exact order-three
tuple basis of the difference set. -/
theorem exactTupleBasis_diff_of_survival {A B : Set ℕ} {N₁ : ℕ}
    (h : ∀ n, N₁ ≤ n → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) :
    IsExactTupleAsymptoticBasis (A \ B) 3 := by
  refine ⟨N₁, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := h n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all [Set.mem_diff]
  · simpa [Fin.sum_univ_three] using hsum

/-- **Repo-vocabulary master chain.**  An exact order-two tuple basis
containing zero whose reflection levels recur with bounded gaps admits an
infinite deletion leaving an exact order-three tuple basis: the positive
answer to the order-two instance of Erdős 881 under the bounded-gap
mirror hypothesis. -/
theorem exactTupleBasis_orderThree_deletion_of_boundedGap_reflectionLevels
    {A : Set ℕ} {C : ℕ}
    (h0 : 0 ∈ A) (h2 : IsExactTupleAsymptoticBasis A 2)
    (L : ℕ → ℕ) (hmono : StrictMono L)
    (hlev : ∀ k, IsReflectionLevel A (L k))
    (hgap : ∀ k, L (k + 1) ≤ L k + C) :
    ∃ B ⊆ A, B.Infinite ∧ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨N₀, hcov⟩ := pairCovers_of_exactTupleBasis h2
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_boundedGap_reflectionLevels h0 hcov L hmono hlev hgap
  exact ⟨B, hBA, hBinf, exactTupleBasis_diff_of_survival hsurv⟩

end Erdos881
