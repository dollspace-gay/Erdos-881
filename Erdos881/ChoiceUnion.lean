import Erdos881.FiniteBlocks

/-!
# A dual choice-union characterization

Strong infinite deletion can also be read as a statement about coherent choices
of one surviving support for every sufficiently large integer.
-/

namespace Erdos881

/-- A choice of one support for every integer at least `N`. -/
abbrev TailSupportChoice (R : SupportFamily) (N : ℕ) :=
  ∀ q : {n : ℕ // N ≤ n}, {E // E ∈ R q.1}

/-- The union of all supports selected by a tail choice. -/
def tailChoiceUnion
    {R : SupportFamily} {N : ℕ} (c : TailSupportChoice R N) : Set ℕ :=
  ⋃ q, ((c q).1 : Set ℕ)

/-- Every support chosen by `c` lies in its tail union. -/
theorem tailChoice_subset_union
    {R : SupportFamily} {N : ℕ} (c : TailSupportChoice R N)
    (q : {n : ℕ // N ≤ n}) :
    ((c q).1 : Set ℕ) ⊆ tailChoiceUnion c := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨q, hx⟩

/-- Strong infinite deletion is equivalent to every coherent tail choice
covering all but finitely many elements of `A`. -/
theorem strongInfiniteDeletion_iff_every_tailChoice_cofiniteUnion
    {A : Set ℕ} {R : SupportFamily} :
    StrongInfiniteDeletion R A ↔
      ∀ N, ∀ c : TailSupportChoice R N,
        (A \ tailChoiceUnion c).Finite := by
  constructor
  · intro hstrong N c
    by_contra hinfinite
    have hB : (A \ tailChoiceUnion c).Infinite := hinfinite
    obtain ⟨n, hn, hdestroy⟩ :=
      hstrong (A \ tailChoiceUnion c) (Set.diff_subset) hB N
    let q : {m : ℕ // N ≤ m} := ⟨n, hn⟩
    have hdisj :
        Disjoint (((c q).1 : Finset ℕ) : Set ℕ)
          (A \ tailChoiceUnion c) := by
      rw [Set.disjoint_left]
      intro x hxE hxB
      exact hxB.2 (tailChoice_subset_union c q hxE)
    exact (hdestroy (c q).1 (c q).2) hdisj
  · intro hchoices
    by_contra hnotstrong
    unfold StrongInfiniteDeletion at hnotstrong
    push Not at hnotstrong
    obtain ⟨B, hBA, hB, N, hsurvive⟩ := hnotstrong
    let c : TailSupportChoice R N := fun q =>
      let w := not_destroysAt_iff.mp (hsurvive q.1 q.2)
      ⟨w.choose, w.choose_spec.1⟩
    have hcdisj :
        ∀ q, Disjoint (((c q).1 : Finset ℕ) : Set ℕ) B := by
      intro q
      change Disjoint
        (((not_destroysAt_iff.mp (hsurvive q.1 q.2)).choose : Finset ℕ) : Set ℕ) B
      exact (not_destroysAt_iff.mp
        (hsurvive q.1 q.2)).choose_spec.2
    have hBdiff : B ⊆ A \ tailChoiceUnion c := by
      intro x hxB
      refine ⟨hBA hxB, ?_⟩
      intro hxunion
      obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxunion
      exact Set.disjoint_left.mp (hcdisj q) hxq hxB
    exact hB ((hchoices N c).subset hBdiff)

/-- The fully existential contrapositive: failure of strong deletion is a
coherent tail choice whose supports omit infinitely many elements of `A`. -/
theorem exists_tailChoice_noncofiniteUnion_iff_not_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily} :
    (∃ N, ∃ c : TailSupportChoice R N,
      (A \ tailChoiceUnion c).Infinite) ↔
        ¬ StrongInfiniteDeletion R A := by
  constructor
  · rintro ⟨N, c, hinfinite⟩ hstrong
    exact hinfinite
      (strongInfiniteDeletion_iff_every_tailChoice_cofiniteUnion.mp
        hstrong N c)
  · intro hnot
    have hnotall :
        ¬ ∀ N, ∀ c : TailSupportChoice R N,
          (A \ tailChoiceUnion c).Finite := by
      intro hall
      exact hnot
        (strongInfiniteDeletion_iff_every_tailChoice_cofiniteUnion.mpr hall)
    push Not at hnotall
    exact hnotall

end Erdos881
