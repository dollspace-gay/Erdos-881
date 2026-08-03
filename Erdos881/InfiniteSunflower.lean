import Erdos881.InfinitePairRamsey

namespace Erdos881

/-- A uniformly bounded point-indexed family of finite sets has an infinite
subfamily whose pairwise intersections are one fixed root. -/
theorem exists_infinite_deltaSystem_of_bounded_pointMap
    {K : Set ℕ} (hK : K.Infinite)
    (f : ℕ → Finset ℕ) (r : ℕ)
    (hcard : ∀ x ∈ K, (f x).card ≤ r) :
    ∃ L, L ⊆ K ∧ L.Infinite ∧
      ∃ R : Finset ℕ, ∀ x ∈ L, ∀ y ∈ L, x ≠ y →
        f x ∩ f y = R := by
  classical
  induction r generalizing K f with
  | zero =>
      refine ⟨K, Set.Subset.rfl, hK, ∅, ?_⟩
      intro x hx y hy _hxy
      have hfx : f x = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hcard x hx))
      have hfy : f y = ∅ :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hcard y hy))
      simp [hfx, hfy]
  | succ r ih =>
      by_cases hfiber :
          ∃ a, {x | x ∈ K ∧ a ∈ f x}.Infinite
      · obtain ⟨a, ha⟩ := hfiber
        let K' : Set ℕ := {x | x ∈ K ∧ a ∈ f x}
        let g : ℕ → Finset ℕ := fun x => (f x).erase a
        have hcardg : ∀ x ∈ K', (g x).card ≤ r := by
          intro x hx
          have hle := hcard x hx.1
          change ((f x).erase a).card ≤ r
          rw [Finset.card_erase_of_mem hx.2]
          omega
        obtain ⟨L, hLK', hL, R, hdelta⟩ :=
          ih ha g hcardg
        refine ⟨L, hLK'.trans (fun x hx => hx.1), hL,
          insert a R, ?_⟩
        intro x hxL y hyL hxy
        have hax : a ∈ f x := (hLK' hxL).2
        have hay : a ∈ f y := (hLK' hyL).2
        have hxyDelta := hdelta x hxL y hyL hxy
        ext z
        by_cases hza : z = a
        · subst z
          simp [hax, hay]
        · have hzR :
              z ∈ R ↔ z ∈ g x ∧ z ∈ g y := by
            rw [← hxyDelta]
            simp
          simp only [g, Finset.mem_erase] at hzR
          simp [hza, hzR]
      · have hfiniteFiber : ∀ a,
            {x | x ∈ K ∧ a ∈ f x}.Finite := by
          intro a
          apply Set.not_infinite.mp
          intro ha
          exact hfiber ⟨a, ha⟩
        let R : ℕ → ℕ → Prop := fun x y =>
          ¬ Disjoint (f x) (f y)
        have hRcomm : Symmetric R := by
          intro x y hxy
          exact fun hyx => hxy hyx.symm
        obtain ⟨L, hLK, hL, hclique⟩ |
            ⟨L, hLK, hL, hindependent⟩ :=
          infinite_pairRamsey_nat hK R hRcomm
        · exfalso
          obtain ⟨x, hxL⟩ := hL.nonempty
          let T : Set ℕ := L \ ({x} : Set ℕ)
          have hT : T.Infinite :=
            hL.diff (Set.finite_singleton x)
          have hunion :
              (⋃ a ∈ (f x : Set ℕ),
                {y | y ∈ K ∧ a ∈ f y}).Finite :=
            (f x).finite_toSet.biUnion
              (fun a _ha => hfiniteFiber a)
          apply hT
          apply hunion.subset
          intro y hyT
          have hyL : y ∈ L := hyT.1
          have hyx : y ≠ x := by simpa using hyT.2
          have hhit : ¬ Disjoint (f x) (f y) :=
            hclique hxL hyL hyx.symm
          obtain ⟨a, hax, hay⟩ :=
            Finset.not_disjoint_iff.mp hhit
          exact Set.mem_iUnion₂.mpr
            ⟨a, Finset.mem_coe.mpr hax, hLK hyL, hay⟩
        · refine ⟨L, hLK, hL, ∅, ?_⟩
          intro x hxL y hyL hxy
          have hd : Disjoint (f x) (f y) := by
            by_contra hnot
            exact (hindependent hxL hyL hxy) hnot
          exact Finset.disjoint_iff_inter_eq_empty.mp hd

end Erdos881
