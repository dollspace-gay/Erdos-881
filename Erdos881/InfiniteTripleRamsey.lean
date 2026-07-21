import Erdos881.InfinitePairRamsey

/-!
# Infinite Ramsey reduction for ordered triples

This file derives the countable two-colour Ramsey theorem for increasing
triples from the pair theorem already used in the rigid/nonrigid reduction.
At one stage, pair Ramsey makes the colour of every pair in the remaining
reservoir uniform relative to the newly chosen first point.  A final infinite
pigeonhole argument makes those stage colours constant.
-/

namespace Erdos881

/-- One thinning step for the increasing-triple Ramsey construction. -/
structure InfiniteTripleRamseyStep
    (R : ℕ → ℕ → ℕ → Prop) (S : Set ℕ) (last : ℕ) where
  point : ℕ
  point_mem : point ∈ S
  point_lower : last < point
  color : Bool
  next : Set ℕ
  next_infinite : next.Infinite
  next_subset : next ⊆ S
  next_above : ∀ x ∈ next, point < x
  uniform_true : color = true →
    ∀ y ∈ next, ∀ z ∈ next, y ≠ z → R point y z
  uniform_false : color = false →
    ∀ y ∈ next, ∀ z ∈ next, y ≠ z → ¬ R point y z

/-- Pair Ramsey on the tail supplies one triple-homogeneous thinning step. -/
theorem infiniteTripleRamseyStep_nonempty
    {R : ℕ → ℕ → ℕ → Prop} {S : Set ℕ} {last : ℕ}
    (hS : S.Infinite)
    (hsymm : ∀ x, Symmetric (R x)) :
    Nonempty (InfiniteTripleRamseyStep R S last) := by
  classical
  obtain ⟨p, hpS, hpLast⟩ := hS.exists_gt last
  let rest : Set ℕ := S \ Set.Iic p
  have hrest : rest.Infinite := hS.diff (Set.finite_Iic p)
  obtain ⟨L, hLrest, hL, htrue⟩ | ⟨L, hLrest, hL, hfalse⟩ :=
    infinite_pairRamsey_nat hrest (R p) (hsymm p)
  · exact ⟨{
      point := p
      point_mem := hpS
      point_lower := hpLast
      color := true
      next := L
      next_infinite := hL
      next_subset := hLrest.trans Set.diff_subset
      next_above := by
        intro x hx
        exact Nat.lt_of_not_ge (hLrest hx).2
      uniform_true := by
        intro _h y hy z hz hyz
        exact htrue hy hz hyz
      uniform_false := by simp
    }⟩
  · exact ⟨{
      point := p
      point_mem := hpS
      point_lower := hpLast
      color := false
      next := L
      next_infinite := hL
      next_subset := hLrest.trans Set.diff_subset
      next_above := by
        intro x hx
        exact Nat.lt_of_not_ge (hLrest hx).2
      uniform_true := by simp
      uniform_false := by
        intro _h y hy z hz hyz
        exact hfalse hy hz hyz
    }⟩

/-- Recursive state for the countable increasing-triple Ramsey argument. -/
structure InfiniteTripleRamseyState (K : Set ℕ) where
  candidates : Set ℕ
  candidates_infinite : candidates.Infinite
  candidates_subset : candidates ⊆ K
  last : ℕ

/-- Infinite two-colour Ramsey theorem for increasing triples of naturals.
Only symmetry in the last two arguments is needed by the stagewise pair
thinning. -/
theorem infinite_tripleRamsey_nat
    {K : Set ℕ} (hK : K.Infinite)
    (R : ℕ → ℕ → ℕ → Prop)
    (hsymm : ∀ x, Symmetric (R x)) :
    (∃ L, L ⊆ K ∧ L.Infinite ∧
      ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
        x < y → y < z → R x y z) ∨
      ∃ L, L ⊆ K ∧ L.Infinite ∧
        ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
          x < y → y < z → ¬ R x y z := by
  classical
  let State := InfiniteTripleRamseyState K
  let initial : State := {
    candidates := K
    candidates_infinite := hK
    candidates_subset := Set.Subset.rfl
    last := 0
  }
  let chooseStep : (s : State) →
      InfiniteTripleRamseyStep R s.candidates s.last :=
    fun s => Classical.choice <|
      infiniteTripleRamseyStep_nonempty s.candidates_infinite hsymm
  let advance (s : State) : State := {
    candidates := (chooseStep s).next
    candidates_infinite := (chooseStep s).next_infinite
    candidates_subset :=
      (chooseStep s).next_subset.trans s.candidates_subset
    last := (chooseStep s).point
  }
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let step (i : ℕ) := chooseStep (state i)
  let a (i : ℕ) := (step i).point
  let color (i : ℕ) := (step i).color
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hcandidates_succ : ∀ i,
      (state (i + 1)).candidates = (step i).next := by
    intro i
    change (state (i + 1)).candidates =
      (chooseStep (state i)).next
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).last = a i := by
    intro i
    change (state (i + 1)).last = (chooseStep (state i)).point
    rw [hstate_succ]
  have hcandidates_step : ∀ i,
      (state (i + 1)).candidates ⊆ (state i).candidates := by
    intro i
    rw [hcandidates_succ]
    exact (step i).next_subset
  have hcandidates_antitone :
      Antitone fun i => (state i).candidates :=
    antitone_nat_of_succ_le hcandidates_step
  have haK : ∀ i, a i ∈ K := by
    intro i
    exact (state i).candidates_subset (step i).point_mem
  have haMono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower := (step (i + 1)).point_lower
    change (state (i + 1)).last < a (i + 1) at hlower
    rw [hlast_succ] at hlower
    exact hlower
  have hfuture : ∀ {i j}, i < j → a j ∈ (step i).next := by
    intro i j hij
    rw [← hcandidates_succ]
    exact hcandidates_antitone (Nat.succ_le_of_lt hij)
      (step j).point_mem
  obtain ⟨q, hqFiber⟩ := Finite.exists_infinite_fiber color
  let I : Set ℕ := {i | color i = q}
  have hI : I.Infinite := by
    apply Set.infinite_coe_iff.mp
    simpa [I] using hqFiber
  let L : Set ℕ := a '' I
  have hLinf : L.Infinite := by
    apply (Set.infinite_image_iff haMono.injective.injOn).mpr hI
  have hLK : L ⊆ K := by
    rintro _ ⟨i, _hiI, rfl⟩
    exact haK i
  cases q with
  | false =>
      right
      refine ⟨L, hLK, hLinf, ?_⟩
      rintro _ ⟨i, hiI, rfl⟩ _ ⟨j, hjI, rfl⟩ _ ⟨k, hkI, rfl⟩
        hij hjk
      have hij' : i < j := haMono.lt_iff_lt.mp hij
      have hjk' : j < k := haMono.lt_iff_lt.mp hjk
      have hik' : i < k := lt_trans hij' hjk'
      have hci : color i = false := hiI
      exact (step i).uniform_false hci
        (a j) (hfuture hij') (a k) (hfuture hik')
        (haMono.injective.ne (Nat.ne_of_lt hjk'))
  | true =>
      left
      refine ⟨L, hLK, hLinf, ?_⟩
      rintro _ ⟨i, hiI, rfl⟩ _ ⟨j, hjI, rfl⟩ _ ⟨k, hkI, rfl⟩
        hij hjk
      have hij' : i < j := haMono.lt_iff_lt.mp hij
      have hjk' : j < k := haMono.lt_iff_lt.mp hjk
      have hik' : i < k := lt_trans hij' hjk'
      have hci : color i = true := hiI
      exact (step i).uniform_true hci
        (a j) (hfuture hij') (a k) (hfuture hik')
        (haMono.injective.ne (Nat.ne_of_lt hjk'))

end Erdos881
