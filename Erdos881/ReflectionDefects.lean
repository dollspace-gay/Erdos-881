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

/-- Four distinct basis elements cannot all have arbitrarily late private
order-three targets.  This is the finite combinatorial core of the
reflection argument below. -/
theorem not_four_arbitrarilyLateSingletonDestroyers
    {A : Set ℕ} {x y z w : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hx : x ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({x} : Set ℕ) n)
    (hy : y ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({y} : Set ℕ) n)
    (hz : z ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({z} : Set ℕ) n)
    (hw : w ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({w} : Set ℕ) n)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : False := by
  have hbasis' := hbasis
  obtain ⟨N, hN⟩ := hbasis
  let L := max y (max z w)
  obtain ⟨n, hn, hdestroy_n⟩ := hx.2 (N + L)
  have hNy : N + y ≤ n := by
    exact le_trans (Nat.add_le_add_left (le_max_left y (max z w)) N) hn
  have hNz : N + z ≤ n := by
    have hzL : z ≤ L :=
      le_trans (le_max_left z w) (le_max_right y (max z w))
    exact le_trans (Nat.add_le_add_left hzL N) hn
  have hNw : N + w ≤ n := by
    have hwL : w ≤ L :=
      le_trans (le_max_right z w) (le_max_right y (max z w))
    exact le_trans (Nat.add_le_add_left hwL N) hn
  have hxyLe : x + y ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n y hy.1 hxy.symm hNy).1
  have hxzLe : x + z ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n z hz.1 hxz.symm hNz).1
  have hxwLe : x + w ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n w hw.1 hxw.symm hNw).1
  have hfixedUnique {u v : ℕ}
      (hxu : x + u ≤ n) (hxv : x + v ≤ n)
      (huv : u ≠ v)
      (hufixed : n - x - u = x)
      (hvfixed : n - x - v = x) : False := by
    omega
  have htranslatedPair : ∃ u v,
      (u = y ∨ u = z ∨ u = w) ∧
      (v = y ∨ v = z ∨ v = w) ∧
      u ≠ v ∧ u ≤ L ∧ v ≤ L ∧
      u ∈ A ∧ v ∈ A ∧
      (∀ T, ∃ r, T ≤ r ∧
        DestroysAt (additiveSupportFamily A 3) ({u} : Set ℕ) r) ∧
      n - x - u ≠ x ∧ n - x - v ≠ x := by
    by_cases hyfixed : n - x - y = x
    · have hzfixed : n - x - z ≠ x := by
        intro h
        exact hfixedUnique hxyLe hxzLe hyz hyfixed h
      have hwfixed : n - x - w ≠ x := by
        intro h
        exact hfixedUnique hxyLe hxwLe hyw hyfixed h
      exact ⟨z, w, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
        hzw, le_trans (le_max_left z w) (le_max_right y (max z w)),
        le_trans (le_max_right z w) (le_max_right y (max z w)),
        hz.1, hw.1, hz.2, hzfixed, hwfixed⟩
    · by_cases hzfixed : n - x - z = x
      · have hwfixed : n - x - w ≠ x := by
          intro h
          exact hfixedUnique hxzLe hxwLe hzw hzfixed h
        exact ⟨y, w, Or.inl rfl, Or.inr (Or.inr rfl),
          hyw, le_max_left y (max z w),
          le_trans (le_max_right z w) (le_max_right y (max z w)),
          hy.1, hw.1, hy.2, hyfixed, hwfixed⟩
      · exact ⟨y, z, Or.inl rfl, Or.inr (Or.inl rfl),
          hyz, le_max_left y (max z w),
          le_trans (le_max_left z w) (le_max_right y (max z w)),
          hy.1, hz.1, hy.2, hyfixed, hzfixed⟩
  obtain ⟨u, v, _huCases, _hvCases, huv, huL, hvL,
      huA, hvA, huLate, hufixed, hvfixed⟩ := htranslatedPair
  have hux : u ≠ x := by
    rcases _huCases with rfl | rfl | rfl
    · exact hxy.symm
    · exact hxz.symm
    · exact hxw.symm
  have hvx : v ≠ x := by
    rcases _hvCases with rfl | rfl | rfl
    · exact hxy.symm
    · exact hxz.symm
    · exact hxw.symm
  obtain ⟨m, hm, hdestroy_m⟩ := hx.2 (n + N + L + 1)
  have hsep : n + N ≤ m := by omega
  let d := m - n
  have hdL : L < d := by
    dsimp only [d]
    omega
  have huD : u < d := huL.trans_lt hdL
  have hNu : N + u ≤ n :=
    le_trans (Nat.add_le_add_left huL N) hn
  have hNv : N + v ≤ n :=
    le_trans (Nat.add_le_add_left hvL N) hn
  have hudA : u + d ∈ A :=
    two_privateOrderThreeTargets_imply_localTranslation_of_threshold
      hN hdestroy_n hdestroy_m huA hux hNu hufixed hsep
  have hvdA : v + d ∈ A :=
    two_privateOrderThreeTargets_imply_localTranslation_of_threshold
      hN hdestroy_n hdestroy_m hvA hvx hNv hvfixed hsep
  have huPartner : u ≠ v + d := by omega
  let pair : Fin 2 → ℕ := ![u + d, v]
  have hpairA : ∀ i, pair i ∈ A := by
    intro i
    fin_cases i
    · simpa [pair] using hudA
    · simpa [pair] using hvA
  have hpairSum : ∑ i, pair i = u + (v + d) := by
    simp [pair, Fin.sum_univ_two]
    omega
  obtain ⟨i, hi⟩ :=
    orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis' hvdA huPartner huLate pair hpairA hpairSum
  fin_cases i
  · have heq : u + d = u := by simpa [pair] using hi
    omega
  · have heq : v = u := by simpa [pair] using hi
    exact huv heq.symm

/-- Only finitely many elements of an exact order-two basis can have
arbitrarily late private order-three targets.

Indeed, suppose there were infinitely many.  Choose one private point `x`
and three further private points.  Two sufficiently separated private
targets for `x` translate at least two of the three further points by the
same positive amount (only one point can be fixed by the first reflection).
One of those translated points and the other original point then give a
noncanonical representation of a pair sum involving a private point,
contradicting `orderTwoBasis_privateOrderThree_forces_pair_use`. -/
theorem finite_arbitrarilyLateSingletonDestruction_orderThree
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3)
        ({a} : Set ℕ) n}.Finite := by
  classical
  let K : Set ℕ := {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
    DestroysAt (additiveSupportFamily A 3)
      ({a} : Set ℕ) n}
  apply Set.not_infinite.mp
  intro hK
  obtain ⟨x, hxK⟩ := hK.nonempty
  obtain ⟨y, hyK, hyx⟩ :=
    hK.exists_notMem_finset ({x} : Finset ℕ)
  obtain ⟨z, hzK, hzxy⟩ :=
    hK.exists_notMem_finset ({x, y} : Finset ℕ)
  obtain ⟨w, hwK, hwxyz⟩ :=
    hK.exists_notMem_finset ({x, y, z} : Finset ℕ)
  have hyx' : y ≠ x := by simpa using hyx
  have hzx : z ≠ x := by
    intro h
    exact hzxy (by simp [h])
  have hzy : z ≠ y := by
    intro h
    exact hzxy (by simp [h])
  have hwx : w ≠ x := by
    intro h
    exact hwxyz (by simp [h])
  have hwy : w ≠ y := by
    intro h
    exact hwxyz (by simp [h])
  have hwz : w ≠ z := by
    intro h
    exact hwxyz (by simp [h])
  have hbasis' := hbasis
  obtain ⟨N, hN⟩ := hbasis
  let L := max y (max z w)
  obtain ⟨n, hn, hdestroy_n⟩ := hxK.2 (N + L)
  have hNy : N + y ≤ n := by
    exact le_trans (Nat.add_le_add_left (le_max_left y (max z w)) N) hn
  have hNz : N + z ≤ n := by
    have hzL : z ≤ L :=
      le_trans (le_max_left z w) (le_max_right y (max z w))
    exact le_trans (Nat.add_le_add_left hzL N) hn
  have hNw : N + w ≤ n := by
    have hwL : w ≤ L :=
      le_trans (le_max_right z w) (le_max_right y (max z w))
    exact le_trans (Nat.add_le_add_left hwL N) hn
  have hxyLe : x + y ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n y hyK.1 hyx' hNy).1
  have hxzLe : x + z ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n z hzK.1 hzx hNz).1
  have hxwLe : x + w ≤ n :=
    (privateOrderThree_implies_longReflection_of_threshold
      hN hdestroy_n w hwK.1 hwx hNw).1
  have hfixedUnique {u v : ℕ}
      (hxu : x + u ≤ n) (hxv : x + v ≤ n)
      (huv : u ≠ v)
      (hufixed : n - x - u = x)
      (hvfixed : n - x - v = x) : False := by
    omega
  have htranslatedPair : ∃ u v,
      u ∈ K ∧ v ∈ K ∧ u ≠ v ∧
      u ≤ L ∧ v ≤ L ∧
      u ≠ x ∧ v ≠ x ∧
      n - x - u ≠ x ∧ n - x - v ≠ x := by
    by_cases hyfixed : n - x - y = x
    · have hzfixed : n - x - z ≠ x := by
        intro h
        exact hfixedUnique hxyLe hxzLe hzy.symm
          hyfixed h
      have hwfixed : n - x - w ≠ x := by
        intro h
        exact hfixedUnique hxyLe hxwLe hwy.symm
          hyfixed h
      exact ⟨z, w, hzK, hwK, hwz.symm,
        le_trans (le_max_left z w) (le_max_right y (max z w)),
        le_trans (le_max_right z w) (le_max_right y (max z w)),
        hzx, hwx, hzfixed, hwfixed⟩
    · by_cases hzfixed : n - x - z = x
      · have hwfixed : n - x - w ≠ x := by
          intro h
          exact hfixedUnique hxzLe hxwLe hwz.symm
            hzfixed h
        exact ⟨y, w, hyK, hwK, hwy.symm,
          le_max_left y (max z w),
          le_trans (le_max_right z w) (le_max_right y (max z w)),
          hyx', hwx, hyfixed, hwfixed⟩
      · exact ⟨y, z, hyK, hzK, hzy.symm,
          le_max_left y (max z w),
          le_trans (le_max_left z w) (le_max_right y (max z w)),
          hyx', hzx, hyfixed, hzfixed⟩
  obtain ⟨u, v, huK, hvK, huv, huL, hvL,
      hux, hvx, hufixed, hvfixed⟩ := htranslatedPair
  obtain ⟨m, hm, hdestroy_m⟩ :=
    hxK.2 (n + N + L + 1)
  have hsep : n + N ≤ m := by omega
  have hnm : n < m := by omega
  let d := m - n
  have hdL : L < d := by
    dsimp only [d]
    omega
  have huD : u < d := huL.trans_lt hdL
  have hvD : v < d := hvL.trans_lt hdL
  have hNu : N + u ≤ n := by
    exact le_trans (Nat.add_le_add_left huL N) hn
  have hNv : N + v ≤ n := by
    exact le_trans (Nat.add_le_add_left hvL N) hn
  have hudA : u + d ∈ A := by
    exact two_privateOrderThreeTargets_imply_localTranslation_of_threshold
      hN hdestroy_n hdestroy_m huK.1 hux hNu hufixed hsep
  have hvdA : v + d ∈ A := by
    exact two_privateOrderThreeTargets_imply_localTranslation_of_threshold
      hN hdestroy_n hdestroy_m hvK.1 hvx hNv hvfixed hsep
  have huPartner : u ≠ v + d := by omega
  let pair : Fin 2 → ℕ := ![u + d, v]
  have hpairA : ∀ i, pair i ∈ A := by
    intro i
    fin_cases i
    · simpa [pair] using hudA
    · simpa [pair] using hvK.1
  have hpairSum : ∑ i, pair i = u + (v + d) := by
    simp [pair, Fin.sum_univ_two]
    omega
  obtain ⟨i, hi⟩ :=
    orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis' hvdA huPartner huK.2 pair hpairA hpairSum
  fin_cases i
  · have heq : u + d = u := by simpa [pair] using hi
    omega
  · have heq : v = u := by simpa [pair] using hi
    exact huv heq.symm

/-- In fact the exceptional set above has at most three elements. -/
theorem ncard_arbitrarilyLateSingletonDestruction_orderThree_le_three
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3)
        ({a} : Set ℕ) n}.ncard ≤ 3 := by
  let Bad : Set ℕ := {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
    DestroysAt (additiveSupportFamily A 3)
      ({a} : Set ℕ) n}
  have hBad : Bad.Finite :=
    finite_arbitrarilyLateSingletonDestruction_orderThree hbasis
  change Bad.ncard ≤ 3
  by_contra hnot
  have hfour : 3 < Bad.ncard := by omega
  obtain ⟨x, y, z, w, hx, hy, hz, hw,
      hxy, hxz, hxw, hyz, hyw, hzw⟩ :=
    (Set.three_lt_ncard_iff hBad).mp hfour
  apply not_four_arbitrarilyLateSingletonDestroyers hbasis
      (x := x) (y := y) (z := z) (w := w)
  · simpa [Bad] using hx
  · simpa [Bad] using hy
  · simpa [Bad] using hz
  · simpa [Bad] using hw
  · exact hxy
  · exact hxz
  · exact hxw
  · exact hyz
  · exact hyw
  · exact hzw

/-- Equivalently, outside a finite exceptional set every basis element has
its own threshold beyond which it is never a singleton order-three
destroyer. -/
theorem eventually_no_singletonDestruction_outsideFinite
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
      ∃ N, ∀ n, N ≤ n →
        ¬ DestroysAt (additiveSupportFamily A 3)
          ({a} : Set ℕ) n := by
  classical
  let Bad : Set ℕ := {a | a ∈ A ∧ ∀ N, ∃ n, N ≤ n ∧
    DestroysAt (additiveSupportFamily A 3)
      ({a} : Set ℕ) n}
  have hBad : Bad.Finite :=
    finite_arbitrarilyLateSingletonDestruction_orderThree hbasis
  refine ⟨hBad.toFinset, ?_⟩
  intro a haA haF
  have haNotBad : a ∉ Bad := by
    intro haBad
    exact haF (hBad.mem_toFinset.mpr haBad)
  have hnotLate : ¬ (∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3)
        ({a} : Set ℕ) n) := by
    intro hlate
    exact haNotBad ⟨haA, hlate⟩
  push Not at hnotLate
  exact hnotLate

/-- Consequently only finitely many individual elements have deletion that
fails to leave an exact order-three basis. -/
theorem finite_singletonDeletions_not_orderThreeBasis
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2) :
    {a | a ∈ A ∧
      ¬ IsExactTupleAsymptoticBasis
        (A \ ({a} : Set ℕ)) 3}.Finite := by
  apply
    (finite_arbitrarilyLateSingletonDestruction_orderThree hbasis).subset
  intro a ha
  refine ⟨ha.1, ?_⟩
  have hlate :=
    (not_exactTupleAsymptoticBasis_diff_finset_iff
      (A := A) (h := 3) (D := ({a} : Finset ℕ))).mp
        (by simpa using ha.2)
  intro N
  obtain ⟨n, hn, hdestroy⟩ := hlate N
  exact ⟨n, hn, by simpa using hdestroy⟩

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
