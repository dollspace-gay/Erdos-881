import Erdos881.ConstructionAudit

/-!
# Reflection structure forced by private successor targets

For an exact order-two basis, a singleton destroyer at order three forces a
long reflected copy of the basis.  Two well-separated private targets for the
same singleton then compose to a local translation of the basis.

These statements isolate the arithmetic content of the reflection--defect
route.  They do not assume syndeticity or any density estimate.
-/

open scoped BigOperators

namespace Erdos881

/-- Threshold-explicit form of the reflection lemma. -/
theorem privateOrderThree_implies_longReflection_of_threshold
    {A : Set ℕ} {a n N : ℕ}
    (hN : ∀ q, N ≤ q →
      ∃ v : Fin 2 → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = q)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) n) :
    ∀ b ∈ A, b ≠ a → N + b ≤ n →
      a + b ≤ n ∧ n - a - b ∈ A := by
  intro b hbA hba hNb
  have hb_le_n : b ≤ n := by omega
  have hNsub : N ≤ n - b := by omega
  obtain ⟨v, hvA, hvsum⟩ := hN (n - b) hNsub
  have hva : ∃ i, v i = a := by
    by_contra hnone
    push Not at hnone
    have hnoRep := destroysAt_additiveSupportFamily_iff.mp hdestroy
    apply hnoRep
    let w : Fin 3 → ℕ := Fin.cons b v
    refine ⟨w, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hbA, by simpa using hba⟩
      · exact ⟨hvA j, by simpa using hnone j⟩
    · rw [Fin.sum_univ_succ]
      simp only [w, Fin.cons_zero, Fin.cons_succ]
      rw [hvsum]
      omega
  obtain ⟨i, hi⟩ := hva
  fin_cases i
  · have hvsum' : v 0 + v 1 = n - b := by
      simpa [Fin.sum_univ_two] using hvsum
    have hi' : v 0 = a := by simpa using hi
    constructor
    · omega
    · have hcomp : n - a - b = v 1 := by omega
      exact hcomp ▸ hvA 1
  · have hvsum' : v 0 + v 1 = n - b := by
      simpa [Fin.sum_univ_two] using hvsum
    have hi' : v 1 = a := by simpa using hi
    constructor
    · omega
    · have hcomp : n - a - b = v 0 := by omega
      exact hcomp ▸ hvA 0

/-- If deleting `a` destroys the order-three target `n`, every basis element
`b ≠ a` for which `n - b` is beyond the order-two basis threshold has its
reflection `n - a - b` back in `A`.

The inequality `a + b ≤ n` is included explicitly: it is forced by the
order-two representation of `n - b` which must use `a`, and makes the
natural-number subtraction in later compositions honest. -/
theorem privateOrderThree_implies_longReflection
    {A : Set ℕ} {a n : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hdestroy : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) n) :
    ∃ N, ∀ b ∈ A, b ≠ a → N + b ≤ n →
      a + b ≤ n ∧ n - a - b ∈ A := by
  obtain ⟨N, hN⟩ := hbasis
  exact ⟨N,
    privateOrderThree_implies_longReflection_of_threshold hN hdestroy⟩

/-- Threshold-explicit form of the two-reflection composition. -/
theorem two_privateOrderThreeTargets_imply_localTranslation_of_threshold
    {A : Set ℕ} {a n m N : ℕ}
    (hN : ∀ q, N ≤ q →
      ∃ v : Fin 2 → ℕ, (∀ i, v i ∈ A) ∧ ∑ i, v i = q)
    (hdestroy_n : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) n)
    (hdestroy_m : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) m)
    {b : ℕ} (hbA : b ∈ A) (hba : b ≠ a)
    (hNb : N + b ≤ n) (hfixed : n - a - b ≠ a)
    (hsep : n + N ≤ m) :
    b + (m - n) ∈ A := by
  obtain ⟨habn, hcA⟩ :=
    privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n b hbA hba hNb
  let c := n - a - b
  have hc_le_n : c ≤ n := by
    exact le_trans (Nat.sub_le (n - a) b) (Nat.sub_le n a)
  have hNc : N + c ≤ m := by omega
  have hca : c ≠ a := by simpa [c] using hfixed
  obtain ⟨_hacm, htranslated⟩ :=
    privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_m c (by simpa [c] using hcA) hca hNc
  have hmn : n ≤ m := by omega
  have heq : m - a - c = b + (m - n) := by
    dsimp only [c]
    omega
  exact heq ▸ htranslated

/-- Reflections about two private order-three targets for the same `a`
compose to translation by their difference.  Apart from the single possible
fixed point of the first reflection, a sufficiently long initial segment of
`A` is carried into `A` by `b ↦ b + (m - n)`.

The separation `n + N ≤ m` ensures that the reflected point from the first
target lies inside the valid reflection interval for the second target. -/
theorem two_privateOrderThreeTargets_imply_localTranslation
    {A : Set ℕ} {a n m : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hdestroy_n : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) n)
    (hdestroy_m : DestroysAt
      (additiveSupportFamily A 3) ({a} : Set ℕ) m) :
    ∃ N, ∀ b ∈ A, b ≠ a → N + b ≤ n →
      n - a - b ≠ a → n + N ≤ m →
      b + (m - n) ∈ A := by
  obtain ⟨N, hreflect_n⟩ :=
    privateOrderThree_implies_longReflection hbasis hdestroy_n
  obtain ⟨M, hreflect_m⟩ :=
    privateOrderThree_implies_longReflection hbasis hdestroy_m
  let L := max N M
  refine ⟨L, ?_⟩
  intro b hbA hba hLb hfixed hsep
  have hNb : N + b ≤ n := by
    exact le_trans (Nat.add_le_add_right (le_max_left N M) b) hLb
  obtain ⟨habn, hcA⟩ := hreflect_n b hbA hba hNb
  let c := n - a - b
  have hc_le_n : c ≤ n := by
    exact le_trans (Nat.sub_le (n - a) b) (Nat.sub_le n a)
  have hMc : M + c ≤ m := by
    have hML : M ≤ L := le_max_right N M
    omega
  have hca : c ≠ a := by simpa [c] using hfixed
  obtain ⟨_hacm, htranslated⟩ :=
    hreflect_m c (by simpa [c] using hcA) hca hMc
  have hmn : n ≤ m := by omega
  have heq : m - a - c = b + (m - n) := by
    dsimp only [c]
    omega
  exact heq ▸ htranslated

/-- An exact order-two basis cannot have arbitrarily late private
order-three witnesses for all but finitely many of its elements.

Indeed, pair-sum rigidity makes the cofinite tail Sidon, while two private
targets for one element reflect two tail elements to a translated copy.  The
resulting parallelogram gives two different representations of one pair sum.
-/
theorem not_cofiniteSingletonDestruction_orderThree_of_orderTwoBasis
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ¬ HasCofiniteSingletonDestruction
      (additiveSupportFamily A 3) A := by
  intro hsingle
  obtain ⟨G, hrigid⟩ :=
    cofinitePrivateOrderThree_pairSumsRigid hbasis hsingle
  obtain ⟨F, hF⟩ := hsingle
  let H := F ∪ G
  obtain ⟨a, haA, haH⟩ := hbasis.infinite.exists_notMem_finset H
  obtain ⟨b, hbA, hbH⟩ :=
    hbasis.infinite.exists_notMem_finset (insert a H)
  obtain ⟨c, hcA, hcH⟩ :=
    hbasis.infinite.exists_notMem_finset (insert b (insert a H))
  obtain ⟨e, heA, heH⟩ :=
    hbasis.infinite.exists_notMem_finset
      (insert c (insert b (insert a H)))
  have haF : a ∉ F := by
    intro ha
    exact haH (Finset.mem_union_left G ha)
  have hbG : b ∉ G := by
    intro hb
    exact hbH (Finset.mem_insert_of_mem
      (Finset.mem_union_right F hb))
  have hcG : c ∉ G := by
    intro hc
    exact hcH (Finset.mem_insert_of_mem <|
      Finset.mem_insert_of_mem <| Finset.mem_union_right F hc)
  have heG : e ∉ G := by
    intro he
    exact heH (Finset.mem_insert_of_mem <|
      Finset.mem_insert_of_mem <| Finset.mem_insert_of_mem <|
        Finset.mem_union_right F he)
  have hba : b ≠ a := by
    intro h
    exact hbH (by simp [h])
  have hca : c ≠ a := by
    intro h
    exact hcH (by simp [h])
  have hea : e ≠ a := by
    intro h
    exact heH (by simp [h])
  have hcb : c ≠ b := by
    intro h
    exact hcH (by simp [h])
  have heb : e ≠ b := by
    intro h
    exact heH (by simp [h])
  have hec : e ≠ c := by
    intro h
    exact heH (by simp [h])
  obtain ⟨N, hN⟩ := hbasis
  let K := max b (max c e)
  obtain ⟨n, hn, hdestroy_n⟩ := hF a haA haF (N + K)
  let R := N + b + c + e + G.sum id + 1
  obtain ⟨m, hm, hdestroy_m⟩ := hF a haA haF (n + R)
  have hNb : N + b ≤ n := by
    have hbK : b ≤ K := le_max_left b (max c e)
    omega
  have hNc : N + c ≤ n := by
    have hcK : c ≤ K :=
      le_trans (le_max_left c e) (le_max_right b (max c e))
    omega
  have hNe : N + e ≤ n := by
    have heK : e ≤ K :=
      le_trans (le_max_right c e) (le_max_right b (max c e))
    omega
  have hsep : n + N ≤ m := by
    dsimp only [R] at hm
    omega
  have hmn : n ≤ m := by omega
  let d := m - n
  have hdlarge : b + c + e + G.sum id < d := by
    dsimp only [d, R]
    omega
  have translate
      {x : ℕ} (hxA : x ∈ A) (hxa : x ≠ a)
      (hNx : N + x ≤ n) (hfixed : n - a - x ≠ a) :
      x + d ∈ A := by
    exact two_privateOrderThreeTargets_imply_localTranslation_of_threshold
      hN hdestroy_n hdestroy_m hxA hxa hNx hfixed hsep
  have contradiction_from_pair
      {x y : ℕ} (hxA : x ∈ A) (hyA : y ∈ A)
      (hxG : x ∉ G) (hyG : y ∉ G) (hxy : x ≠ y)
      (hyd : y < d)
      (hxdA : x + d ∈ A) (hydA : y + d ∈ A) : False := by
    have hxdG : x + d ∉ G := by
      intro hmem
      have hle : x + d ≤ G.sum id := by
        exact Finset.single_le_sum (fun z _hz => Nat.zero_le z) hmem
      omega
    have hxd_y : x + d ≠ y := by omega
    let v : Fin 2 → ℕ := ![x, y + d]
    have hvA : ∀ i, v i ∈ A := by
      intro i
      fin_cases i <;> simp [v, hxA, hydA]
    have hvsum : ∑ i, v i = (x + d) + y := by
      simp [v, Fin.sum_univ_two]
      omega
    obtain ⟨i, hi⟩ :=
      (hrigid (x + d) hxdA hxdG y hyA hyG hxd_y v hvA hvsum).1
    fin_cases i
    · have hi' : x = x + d := by simpa [v] using hi
      omega
    · have hi' : y + d = x + d := by simpa [v] using hi
      omega
  by_cases hbfix : n - a - b = a
  · have hcfix : n - a - c ≠ a := by
      intro h
      obtain ⟨habn, _⟩ :=
        privateOrderThree_implies_longReflection_of_threshold
          hN hdestroy_n b hbA hba hNb
      obtain ⟨hacn, _⟩ :=
        privateOrderThree_implies_longReflection_of_threshold
          hN hdestroy_n c hcA hca hNc
      omega
    have hefix : n - a - e ≠ a := by
      intro h
      obtain ⟨habn, _⟩ :=
        privateOrderThree_implies_longReflection_of_threshold
          hN hdestroy_n b hbA hba hNb
      obtain ⟨haen, _⟩ :=
        privateOrderThree_implies_longReflection_of_threshold
          hN hdestroy_n e heA hea hNe
      omega
    exact contradiction_from_pair hcA heA hcG heG hec.symm (by omega)
      (translate hcA hca hNc hcfix) (translate heA hea hNe hefix)
  · by_cases hcfix : n - a - c = a
    · have hefix : n - a - e ≠ a := by
        intro h
        obtain ⟨hacn, _⟩ :=
          privateOrderThree_implies_longReflection_of_threshold
            hN hdestroy_n c hcA hca hNc
        obtain ⟨haen, _⟩ :=
          privateOrderThree_implies_longReflection_of_threshold
            hN hdestroy_n e heA hea hNe
        omega
      exact contradiction_from_pair hbA heA hbG heG heb.symm (by omega)
        (translate hbA hba hNb hbfix) (translate heA hea hNe hefix)
    · exact contradiction_from_pair hbA hcA hbG hcG hcb.symm (by omega)
        (translate hbA hba hNb hbfix) (translate hcA hca hNc hcfix)

/-- Consequently, every exact order-two basis contains infinitely many
elements whose individual deletion still leaves an exact order-three basis.

This is stronger than merely ruling out a particular finite-booster
construction.  It is still a one-point-at-a-time statement; passing from it
to one infinite simultaneous deletion is the remaining compactness issue.
-/
theorem infinitelyMany_singletonDeletions_preserve_orderThree
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    {a | a ∈ A ∧
      IsExactTupleAsymptoticBasis (A \ ({a} : Set ℕ)) 3}.Infinite := by
  let good : Set ℕ := {a | a ∈ A ∧
    IsExactTupleAsymptoticBasis (A \ ({a} : Set ℕ)) 3}
  by_contra hnot
  have hgoodFinite : good.Finite := Set.not_infinite.mp hnot
  let F := hgoodFinite.toFinset
  have hsingle : HasCofiniteSingletonDestruction
      (additiveSupportFamily A 3) A := by
    refine ⟨F, ?_⟩
    intro a haA haF
    have hnotBasis :
        ¬ IsExactTupleAsymptoticBasis (A \ ({a} : Set ℕ)) 3 := by
      intro haBasis
      have hagood : a ∈ good := ⟨haA, haBasis⟩
      exact haF (hgoodFinite.mem_toFinset.mpr hagood)
    have hlate :=
      (not_exactTupleAsymptoticBasis_diff_finset_iff
        (A := A) (h := 3) (D := ({a} : Finset ℕ))).mp
          (by simpa using hnotBasis)
    intro N
    obtain ⟨n, hn, hdestroy⟩ := hlate N
    exact ⟨n, hn, by simpa using hdestroy⟩
  exact
    (not_cofiniteSingletonDestruction_orderThree_of_orderTwoBasis hbasis)
      hsingle

end Erdos881
