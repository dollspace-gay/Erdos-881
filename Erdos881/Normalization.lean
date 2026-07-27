import Erdos881.AdditiveSupports

/-!
# Translation to a zero-normalized additive basis

An additive basis in `ℕ` need not contain zero.  If `a` is its least
element, subtracting `a` from every basis element produces a set containing
zero.  Exact `h`-term representations are transported by translating their
targets by `h * a`; infinite deletions are transported by the same bijection.

This file isolates that bookkeeping so the zero-normalized Erdős 881
machinery can be used without adding `0 ∈ A` to the original problem.
-/

open scoped BigOperators

namespace Erdos881

/-- Subtract `a` from a set of naturals, expressed without truncated
subtraction: `x` belongs to the normalized set exactly when `x + a` belongs
to the original set. -/
def normalizeNatSet (a : ℕ) (A : Set ℕ) : Set ℕ :=
  {x | x + a ∈ A}

/-- Translate every member of a set upward by `a`. -/
def translateNatSet (a : ℕ) (A : Set ℕ) : Set ℕ :=
  (fun x => x + a) '' A

@[simp]
theorem mem_normalizeNatSet {a x : ℕ} {A : Set ℕ} :
    x ∈ normalizeNatSet a A ↔ x + a ∈ A :=
  Iff.rfl

@[simp]
theorem mem_translateNatSet {a y : ℕ} {A : Set ℕ} :
    y ∈ translateNatSet a A ↔ ∃ x ∈ A, x + a = y :=
  Iff.rfl

theorem zero_mem_normalizeNatSet {a : ℕ} {A : Set ℕ}
    (haA : a ∈ A) :
    0 ∈ normalizeNatSet a A := by
  simpa using haA

theorem translateNatSet_infinite {a : ℕ} {A : Set ℕ}
    (hA : A.Infinite) :
    (translateNatSet a A).Infinite := by
  rw [translateNatSet, Set.infinite_image_iff]
  · exact hA
  · intro x _ y _ hxy
    exact Nat.add_right_cancel hxy

theorem translateNatSet_subset {a : ℕ} {A C : Set ℕ}
    (hCA : C ⊆ normalizeNatSet a A) :
    translateNatSet a C ⊆ A := by
  rintro _ ⟨x, hxC, rfl⟩
  exact hCA hxC

@[simp]
theorem normalizeNatSet_diff_translateNatSet
    {a : ℕ} {A C : Set ℕ} :
    normalizeNatSet a (A \ translateNatSet a C) =
      normalizeNatSet a A \ C := by
  ext x
  constructor
  · rintro ⟨hxA, hxnot⟩
    refine ⟨hxA, ?_⟩
    intro hxC
    exact hxnot ⟨x, hxC, rfl⟩
  · rintro ⟨hxA, hxC⟩
    refine ⟨hxA, ?_⟩
    rintro ⟨y, hyC, hy⟩
    have : y = x := Nat.add_right_cancel hy
    exact hxC (this ▸ hyC)

/-- Translating a normalized exact basis upward produces an exact basis of
the same tuple length.  A target `n` is normalized to `n - h * a`. -/
theorem exactTupleBasis_of_normalizeNatSet
    {a h : ℕ} {A : Set ℕ}
    (hbasis : IsExactTupleAsymptoticBasis (normalizeNatSet a A) h) :
    IsExactTupleAsymptoticBasis A h := by
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N + h * a, ?_⟩
  intro n hn
  obtain ⟨v, hvA, hvsum⟩ := hN (n - h * a) (by omega)
  let w : Fin h → ℕ := fun i => v i + a
  refine ⟨w, ?_, ?_⟩
  · intro i
    exact hvA i
  · have hsum :
        (∑ i, w i) = (∑ i, v i) + h * a := by
      simp [w, Finset.sum_add_distrib]
    rw [hsum, hvsum]
    omega

/-- If every member of `A` lies above `a`, subtracting `a` transports an
exact basis to the zero-normalized set. -/
theorem exactTupleBasis_normalizeNatSet
    {a h : ℕ} {A : Set ℕ}
    (hlower : ∀ x ∈ A, a ≤ x)
    (hbasis : IsExactTupleAsymptoticBasis A h) :
    IsExactTupleAsymptoticBasis (normalizeNatSet a A) h := by
  obtain ⟨N, hN⟩ := hbasis
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨v, hvA, hvsum⟩ := hN (n + h * a) (by omega)
  let w : Fin h → ℕ := fun i => v i - a
  have hwadd : ∀ i, w i + a = v i := by
    intro i
    dsimp [w]
    exact Nat.sub_add_cancel (hlower _ (hvA i))
  refine ⟨w, ?_, ?_⟩
  · intro i
    change w i + a ∈ A
    rw [hwadd i]
    exact hvA i
  · have hsum :
        (∑ i, w i) + h * a = ∑ i, v i := by
      calc
        (∑ i, w i) + h * a = ∑ i, (w i + a) := by
          simp [Finset.sum_add_distrib]
        _ = ∑ i, v i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hwadd i
    rw [hvsum] at hsum
    omega

theorem exactTupleBasis_normalizeNatSet_iff
    {a h : ℕ} {A : Set ℕ}
    (hlower : ∀ x ∈ A, a ≤ x) :
    IsExactTupleAsymptoticBasis (normalizeNatSet a A) h ↔
      IsExactTupleAsymptoticBasis A h :=
  ⟨exactTupleBasis_of_normalizeNatSet,
    exactTupleBasis_normalizeNatSet hlower⟩

/-- Strong minimality is preserved when a basis is shifted down by its
minimum. -/
theorem stronglyMinimalExactBasis_normalizeNatSet
    {a h : ℕ} {A : Set ℕ}
    (hlower : ∀ x ∈ A, a ≤ x)
    (hminimal : IsStronglyMinimalExactBasis A h) :
    IsStronglyMinimalExactBasis (normalizeNatSet a A) h := by
  refine ⟨exactTupleBasis_normalizeNatSet hlower hminimal.1, ?_⟩
  rw [strongInfiniteDeletion_additiveSupportFamily_iff]
  have hstrong :=
    strongInfiniteDeletion_additiveSupportFamily_iff.mp hminimal.2
  intro C hCsub hCinf N
  set B := translateNatSet a C with hB
  have hBA : B ⊆ A := by
    rw [hB]
    exact translateNatSet_subset hCsub
  have hBinf : B.Infinite := by
    rw [hB]
    exact translateNatSet_infinite hCinf
  obtain ⟨n, hn, hnorep⟩ :=
    hstrong B hBA hBinf (N + h * a)
  refine ⟨n - h * a, by omega, ?_⟩
  rintro ⟨v, hv, hvsum⟩
  let w : Fin h → ℕ := fun i => v i + a
  apply hnorep
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hvi := hv i
    rw [← normalizeNatSet_diff_translateNatSet (a := a)
      (A := A) (C := C)] at hvi
    exact hvi
  · have hsum :
        (∑ i, w i) = (∑ i, v i) + h * a := by
      simp [w, Finset.sum_add_distrib]
    rw [hsum, hvsum]
    omega

/-- Any zero-normalized solution of Erdős 881 at order two transports to
the unrestricted statement. -/
theorem erdos881_of_zero_normalized
    (hzero : ∀ A : Set ℕ, 0 ∈ A →
      IsStronglyMinimalExactBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ A : Set ℕ, IsStronglyMinimalExactBasis A 2 →
      ∃ B, B ⊆ A ∧ B.Infinite ∧
        IsExactTupleAsymptoticBasis (A \ B) 3 := by
  intro A hminimal
  have hAne : A.Nonempty := by
    obtain ⟨N, hN⟩ := hminimal.1
    obtain ⟨v, hvA, -⟩ := hN N le_rfl
    exact ⟨v 0, hvA 0⟩
  let a := sInf A
  have haA : a ∈ A := by
    exact Nat.sInf_mem hAne
  have halower : ∀ x ∈ A, a ≤ x := by
    intro x hx
    exact Nat.sInf_le hx
  have hnorm :=
    stronglyMinimalExactBasis_normalizeNatSet halower hminimal
  obtain ⟨C, hCsub, hCinf, hthree⟩ :=
    hzero (normalizeNatSet a A)
      (zero_mem_normalizeNatSet haA) hnorm
  refine ⟨translateNatSet a C, translateNatSet_subset hCsub,
    translateNatSet_infinite hCinf, ?_⟩
  rw [← normalizeNatSet_diff_translateNatSet (a := a)
    (A := A) (C := C)] at hthree
  exact exactTupleBasis_of_normalizeNatSet hthree

end Erdos881
