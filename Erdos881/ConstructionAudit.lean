import Erdos881.AdditiveSupports

open scoped BigOperators

namespace Erdos881

/-- At order `21`, the proposed booster step asks for a private target `p`
above `T / (200 * 21)`, twenty new summands strictly above `p`, and their
boosted sum `q` below `T / (10 * 21)`.  These requirements are inconsistent.

The proof deliberately retains the floor divisions appearing in the stated
construction, so this is not an artifact of replacing its inequalities by
real-valued approximations. -/
theorem claimedBoosterWindow_order21_impossible
    (T p q : ℕ) (u : Fin 20 → ℕ)
    (hp : T / 4200 < p)
    (hu : ∀ i, p < u i)
    (hqeq : q = 1 + ∑ i, u i)
    (hq : q < T / 210) :
    False := by
  have hu' : ∀ i, p + 1 ≤ u i := by
    intro i
    exact hu i
  have hsum : 20 * (p + 1) ≤ ∑ i, u i := by
    calc
      20 * (p + 1) = ∑ _i : Fin 20, (p + 1) := by simp
      _ ≤ ∑ i, u i := by
        apply Finset.sum_le_sum
        intro i _hi
        exact hu' i
  have hsum' : 20 * p + 20 ≤ ∑ i, u i := by
    omega
  omega

theorem claimedPrivateWindow_orderTwo_predecessor_mem_priorInterval
    (Tprev T p : ℕ)
    (hscale : 8000 * Tprev ≤ T)
    (hlower : T / 400 < p)
    (hupper : p < T / 20) :
    Tprev ≤ p - 1 ∧ p - 1 ≤ T - 1 := by
  omega

/-- Any order-`k` representation of `p - 1` becomes an order-`k + 1`
representation of `p` after adjoining the booster `1`. -/
theorem predecessorRepresentation_with_booster_one
    {S : Set ℕ} {k p : ℕ}
    (hp : 1 ≤ p)
    (hrep : ∃ v : Fin k → ℕ,
      (∀ i, v i ∈ S) ∧ ∑ i, v i = p - 1) :
    ∃ w : Fin (k + 1) → ℕ,
      (∀ i, w i ∈ Set.insert 1 S) ∧ ∑ i, w i = p := by
  obtain ⟨v, hvS, hvsum⟩ := hrep
  let w : Fin (k + 1) → ℕ := Fin.cons 1 v
  refine ⟨w, ?_, ?_⟩
  · intro i
    refine Fin.cases (Set.mem_insert 1 S) (fun j => ?_) i
    exact Set.mem_insert_of_mem 1 (hvS j)
  · rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    rw [hvsum]
    omega

theorem claimedOrderTwoPrivateStage_has_boosterRepresentation
    (D : Set ℕ) (Tprev T p : ℕ)
    (hscale : 8000 * Tprev ≤ T)
    (hlower : T / 400 < p)
    (hupper : p < T / 20)
    (hcover : ∀ n, Tprev ≤ n → n ≤ T - 1 →
      ∃ v : Fin 2 → ℕ,
        (∀ i, v i ∈ D) ∧ ∑ i, v i = n) :
    ∃ w : Fin 3 → ℕ,
      (∀ i, w i ∈ Set.insert 1 D) ∧ ∑ i, w i = p := by
  obtain ⟨hpredLower, hpredUpper⟩ :=
    claimedPrivateWindow_orderTwo_predecessor_mem_priorInterval
      Tprev T p hscale hlower hupper
  apply predecessorRepresentation_with_booster_one
  · omega
  · exact hcover (p - 1) hpredLower hpredUpper

/- The finite-deletion tree argument used in the proposed "finite-booster
normal form" is not a valid compactness principle.  The simplest exact-basis
model already has every finite deletion good at order one. -/
theorem univ_orderOne_finiteDeletionStable :
    IsFiniteDeletionStableExactBasis (Set.univ : Set ℕ) 1 := by
  intro D
  rw [exactTupleAsymptoticBasis_one_iff]
  refine ⟨(∑ x ∈ D, x) + 1, ?_⟩
  intro n hn
  refine ⟨Set.mem_univ n, ?_⟩
  intro hnD
  have hnle : n ≤ ∑ x ∈ D, x := by
    exact Finset.single_le_sum (fun x _hx => Nat.zero_le x) hnD
  omega

/- Yet no infinite deletion from `ℕ` preserves an exact order-one basis.
Thus an infinite branch through the finite-deletion tree need not have a
diagonal thinning whose union remains a basis. -/
theorem univ_orderOne_noInfiniteDeletionPreserves
    (B : Set ℕ) (hB : B.Infinite) :
    ¬ IsExactTupleAsymptoticBasis ((Set.univ : Set ℕ) \ B) 1 := by
  intro hbasis
  obtain ⟨N, hN⟩ := exactTupleAsymptoticBasis_one_iff.mp hbasis
  have hBsub : B ⊆ Set.Iio N := by
    intro b hbB
    by_contra hbNotSmall
    have hNb : N ≤ b := Nat.le_of_not_gt hbNotSmall
    exact (hN b hNb).2 hbB
  exact hB (Set.finite_Iio N |>.subset hBsub)

/- In particular, the corresponding finite-deletion tree has no terminal
node even though no infinite deletion is good. -/
theorem univ_orderOne_finiteDeletionTree_noTerminal
    (D : Finset ℕ) :
    ∃ a, a ∉ D ∧
      IsExactTupleAsymptoticBasis
        ((Set.univ : Set ℕ) \ ((insert a D : Finset ℕ) : Set ℕ)) 1 := by
  let a := (∑ x ∈ D, x) + 1
  have haD : a ∉ D := by
    intro ha
    have hale : a ≤ ∑ x ∈ D, x := by
      exact Finset.single_le_sum (fun x _hx => Nat.zero_le x) ha
    simp only [a] at hale
    omega
  exact ⟨a, haD, univ_orderOne_finiteDeletionStable (insert a D)⟩

/- A private order-three witness for `a`, together with eventual two-term
representability, forces every two-term representation of `a + b` to use
`a`.  This is the local engine of the Sidon obstruction. -/
theorem orderTwoBasis_privateOrderThree_forces_pair_use
    {A : Set ℕ} {a b : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hbA : b ∈ A) (hab : a ≠ b)
    (hlate : ∀ N, ∃ n, N ≤ n ∧
      DestroysAt (additiveSupportFamily A 3) ({a} : Set ℕ) n)
    (v : Fin 2 → ℕ) (hvA : ∀ i, v i ∈ A)
    (hvsum : ∑ i, v i = a + b) :
    ∃ i, v i = a := by
  obtain ⟨N, hN⟩ := hbasis
  obtain ⟨n, hn, hdestroy⟩ :=
    hlate (max (N + b) (b + 2 * a + 1))
  have hbn : b ≤ n := by omega
  have hNsub : N ≤ n - b := by omega
  obtain ⟨u, huA, husum⟩ := hN (n - b) hNsub
  have hnoRep : ¬ ∃ w : Fin 3 → ℕ,
      (∀ i, w i ∈ A \ ({a} : Set ℕ)) ∧ ∑ i, w i = n :=
    destroysAt_additiveSupportFamily_iff.mp hdestroy
  have hua : ∃ i, u i = a := by
    by_contra hnone
    push Not at hnone
    apply hnoRep
    let w : Fin 3 → ℕ := Fin.cons b u
    refine ⟨w, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hbA, by simpa using hab.symm⟩
      · exact ⟨huA j, by simpa using hnone j⟩
    · rw [Fin.sum_univ_succ]
      simp only [w, Fin.cons_zero, Fin.cons_succ]
      rw [husum]
      omega
  obtain ⟨i, hui⟩ := hua
  have hc : ∃ c, c ∈ A ∧ n = a + b + c ∧ c ≠ a := by
    fin_cases i
    · refine ⟨u 1, huA 1, ?_, ?_⟩
      · have husum' : u 0 + u 1 = n - b := by
          simpa [Fin.sum_univ_two] using husum
        have hui' : u 0 = a := by simpa using hui
        omega
      · intro hca
        have husum' : u 0 + u 1 = n - b := by
          simpa [Fin.sum_univ_two] using husum
        have hui' : u 0 = a := by simpa using hui
        omega
    · refine ⟨u 0, huA 0, ?_, ?_⟩
      · have husum' : u 0 + u 1 = n - b := by
          simpa [Fin.sum_univ_two] using husum
        have hui' : u 1 = a := by simpa using hui
        omega
      · intro hca
        have husum' : u 0 + u 1 = n - b := by
          simpa [Fin.sum_univ_two] using husum
        have hui' : u 1 = a := by simpa using hui
        omega
  obtain ⟨c, hcA, hnabc, hca⟩ := hc
  by_contra hnone
  push Not at hnone
  apply hnoRep
  let w : Fin 3 → ℕ := Fin.cons c v
  refine ⟨w, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hcA, hca⟩
    · exact ⟨hvA j, by simpa using hnone j⟩
  · rw [Fin.sum_univ_succ]
    simp only [w, Fin.cons_zero, Fin.cons_succ]
    rw [hvsum]
    omega

theorem cofinitePrivateOrderThree_pairSumsRigid
    {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hsingle : HasCofiniteSingletonDestruction
      (additiveSupportFamily A 3) A) :
    ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
      ∀ b ∈ A, b ∉ F → a ≠ b →
        ∀ v : Fin 2 → ℕ, (∀ i, v i ∈ A) →
          ∑ i, v i = a + b →
            (∃ i, v i = a) ∧ (∃ i, v i = b) := by
  obtain ⟨F, hF⟩ := hsingle
  refine ⟨F, ?_⟩
  intro a haA haF b hbA hbF hab v hvA hvsum
  constructor
  · exact orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis hbA hab (hF a haA haF) v hvA hvsum
  · exact orderTwoBasis_privateOrderThree_forces_pair_use
      hbasis haA hab.symm (hF b hbA hbF) v hvA (by omega)

/- The finite/cofinite translate-cover route cannot be obtained from the
basis hypothesis alone.  Natural squares give a concrete exact order-four
basis with unbounded gaps. -/
def naturalSquares : Set ℕ := {n | ∃ a : ℕ, a ^ 2 = n}

theorem naturalSquares_exactOrderFourBasis :
    IsExactTupleAsymptoticBasis naturalSquares 4 := by
  refine ⟨0, ?_⟩
  intro n _hn
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
  let v : Fin 4 → ℕ := ![a ^ 2, b ^ 2, c ^ 2, d ^ 2]
  refine ⟨v, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [v, naturalSquares]
  · simpa [v, Fin.sum_univ_four] using habcd

theorem naturalSquares_not_eventuallySyndetic :
    ¬ IsEventuallySyndetic naturalSquares := by
  rintro ⟨L, N, hsyndetic⟩
  let m := N + L + 1
  let n := m ^ 2 + m
  have hNn : N ≤ n := by
    dsimp only [m, n]
    nlinarith
  obtain ⟨x2, ⟨x, rfl⟩, hxle, hnear⟩ := hsyndetic n hNn
  have hxsq : x ^ 2 < (m + 1) ^ 2 := by
    dsimp only [n] at hxle
    nlinarith
  have hx : x ≤ m := by
    nlinarith
  dsimp only [n, m] at hnear hx
  nlinarith

theorem exactBasis_does_not_imply_finiteCofiniteTranslateCover :
    IsExactTupleAsymptoticBasis naturalSquares 4 ∧
      ¬ ∃ Q : Finset ℕ, ∃ N, ∀ n, N ≤ n →
        n ∈ finiteTargetTranslates naturalSquares Q := by
  refine ⟨naturalSquares_exactOrderFourBasis, ?_⟩
  intro hcover
  exact naturalSquares_not_eventuallySyndetic
    (exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic.mp hcover)

/-- The growth decoration cannot weaken the arithmetic obstruction: every
finite cofinite cover by growth-bearing translates already forces eventual
syndeticity of the underlying set. -/
theorem finiteCofiniteGrowthTranslateCover_implies_eventuallySyndetic
    {A : Set ℕ} {k : ℕ}
    (hcover : HasFiniteCofiniteGrowthTranslateCover A k) :
    IsEventuallySyndetic A := by
  obtain ⟨Q, _hgrowth, N, hcofinite⟩ := hcover
  apply exists_finiteTargetTranslates_cofinite_iff_eventuallySyndetic.mp
  exact ⟨Q, N, hcofinite⟩

/-- Thus the proposed finite/cofinite growth-translate bridge is unavailable
for every non-syndetic basis, independently of its deletion properties. -/
theorem not_finiteCofiniteGrowthTranslateCover_of_not_eventuallySyndetic
    {A : Set ℕ} {k : ℕ}
    (hnot : ¬ IsEventuallySyndetic A) :
    ¬ HasFiniteCofiniteGrowthTranslateCover A k := by
  intro hcover
  exact hnot
    (finiteCofiniteGrowthTranslateCover_implies_eventuallySyndetic hcover)

/-- Unified audit of both translate-cover proposals.  On a non-syndetic
set, neither a finite cofinite growth cover nor a uniform threshold cover by
a countable family containing every translate label can hold. -/
theorem nonSyndetic_excludes_finiteAndUniformTranslateCoverRoutes
    {A : Set ℕ} {k : ℕ}
    (hnot : ¬ IsEventuallySyndetic A)
    (Q : ℕ → Finset ℕ)
    (hlabels : ∀ q, ∃ i, q ∈ Q i) :
    ¬ HasFiniteCofiniteGrowthTranslateCover A k ∧
      ¬ UniformThresholdCover
        (fun i => finiteTargetTranslates A (Q i)) := by
  refine ⟨
    not_finiteCofiniteGrowthTranslateCover_of_not_eventuallySyndetic hnot,
    ?_⟩
  intro huniform
  exact hnot <|
    (uniformThresholdCover_allFiniteTargetLabels_iff_eventuallySyndetic
      hlabels).mp huniform

theorem naturalSquares_no_uniformThresholdCover_of_allTranslateLabels
    (Q : ℕ → Finset ℕ)
    (hlabels : ∀ q, ∃ i, q ∈ Q i) :
    ¬ UniformThresholdCover
      (fun i => finiteTargetTranslates naturalSquares (Q i)) := by
  intro huniform
  exact naturalSquares_not_eventuallySyndetic
    ((uniformThresholdCover_allFiniteTargetLabels_iff_eventuallySyndetic
      hlabels).mp huniform)

end Erdos881
