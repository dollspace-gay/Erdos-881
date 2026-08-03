import Erdos881.GeneralOrderAttack
import Erdos881.GuardianRigidity

namespace Erdos881

open Classical

theorem window_dense_dichotomy (S : Set ℕ) :
    (∀ N, ∃ z, N ≤ z ∧ z ∉ S ∧ z + 1 ∉ S ∧ z + 2 ∉ S) ∨
    (∃ N, ∀ z, N ≤ z →
      z ∈ S ∨ z + 1 ∈ S ∨ z + 2 ∈ S) := by
  by_cases h : ∀ N, ∃ z, N ≤ z ∧ z ∉ S ∧
      z + 1 ∉ S ∧ z + 2 ∉ S
  · exact Or.inl h
  · right
    rw [not_forall] at h
    obtain ⟨N, hN⟩ := h
    refine ⟨N, fun z hz => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hN ⟨z, hz, hcon.1, hcon.2.1, hcon.2.2⟩

theorem dense_counting_bound (S : Set ℕ) (N : ℕ)
    (hd : ∀ z, N ≤ z →
      z ∈ S ∨ z + 1 ∈ S ∨ z + 2 ∈ S) :
    ∀ L, L ≤ ((Finset.Ico N (N + 3 * L)).filter
      (fun q => q ∈ S)).card := by
  intro L
  have hchoose : ∀ w : Fin L, ∃ p,
      N + 3 * (w : ℕ) ≤ p ∧
      p < N + 3 * (w : ℕ) + 3 ∧ p ∈ S := by
    intro w
    rcases hd (N + 3 * (w : ℕ)) (by omega)
      with h | h | h
    · exact ⟨N + 3 * (w : ℕ), by omega, by omega, h⟩
    · exact ⟨N + 3 * (w : ℕ) + 1, by omega,
        by omega, h⟩
    · exact ⟨N + 3 * (w : ℕ) + 2, by omega,
        by omega, h⟩
  choose f hf1 hf2 hf3 using hchoose
  have hinj : Function.Injective f := by
    intro a b hab
    have ha1 := hf1 a
    have ha2 := hf2 a
    have hb1 := hf1 b
    have hb2 := hf2 b
    rw [hab] at ha1 ha2
    exact Fin.ext (by omega)
  have hmaps : ∀ w : Fin L,
      f w ∈ (Finset.Ico N (N + 3 * L)).filter
        (fun q => q ∈ S) := by
    intro w
    rw [Finset.mem_filter, Finset.mem_Ico]
    have h1 := hf1 w
    have h2 := hf2 w
    have hw := w.isLt
    exact ⟨⟨by omega, by omega⟩, hf3 w⟩
  have h := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Fin L)))
    (t := (Finset.Ico N (N + 3 * L)).filter
      (fun q => q ∈ S)) f
    (fun w _ => hmaps w)
    (fun a _ b _ hab => hinj hab)
  simpa using h

def DestroyedTargets (A Z : Set ℕ) : Set ℕ :=
  {q | (∃ x ∈ A, ∃ y ∈ A, x + y = q) ∧
    ∀ x ∈ A, ∀ y ∈ A, x + y = q → x ∈ Z ∨ y ∈ Z}

theorem destroyedTargets_window_or_density {A Z : Set ℕ}
    {N₀ : ℕ} (hcov : PairCovers A N₀) :
    (∀ N, ∃ z, N ≤ z ∧ ∀ i, i < 3 →
      ∃ x ∈ A, ∃ y ∈ A,
        x ∉ Z ∧ y ∉ Z ∧ x + y = z + i) ∨
    (∃ N, ∀ L, L ≤
      ((Finset.Ico N (N + 3 * L)).filter
        (fun q => q ∈ DestroyedTargets A Z)).card) := by
  rcases window_dense_dichotomy (DestroyedTargets A Z)
    with h | h
  · left
    intro N
    obtain ⟨z, hz, h0, h1, h2⟩ := h (max N N₀)
    have hzN : N ≤ z :=
      le_trans (le_max_left _ _) hz
    have hzN₀ : N₀ ≤ z :=
      le_trans (le_max_right _ _) hz
    refine ⟨z, hzN, ?_⟩
    intro i hi
    have hcovi : ∃ x ∈ A, ∃ y ∈ A, x + y = z + i :=
      hcov (z + i) (by omega)
    have hnw : z + i ∉ DestroyedTargets A Z := by
      have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi3 with rfl | rfl | rfl
      · simpa using h0
      · exact h1
      · exact h2
    by_contra hcon
    push Not at hcon
    refine hnw ⟨hcovi, ?_⟩
    intro x hx y hy hxy
    by_contra hz2
    push Not at hz2
    exact hcon x hx y hy hz2.1 hz2.2 hxy
  · right
    obtain ⟨N, hN⟩ := h
    exact ⟨N, dense_counting_bound _ N hN⟩

theorem HasCofinalDestroyedPairStream.window_or_density
    {A D : Set ℕ} {N₀ : ℕ} (hcov : PairCovers A N₀)
    (h : HasCofinalDestroyedPairStream A D) :
    ∃ Z : Set ℕ, Z ⊆ D ∧ Z ⊆ A ∧ Z.Infinite ∧
      ((∀ N, ∃ z, N ≤ z ∧ ∀ i, i < 3 →
        ∃ x ∈ A, ∃ y ∈ A,
          x ∉ Z ∧ y ∉ Z ∧ x + y = z + i) ∨
      (∃ N, ∀ L, L ≤
        ((Finset.Ico N (N + 3 * L)).filter
          (fun q =>
            q ∈ DestroyedTargets A Z)).card)) := by
  obtain ⟨Z, hZD, hZA, hZinf, _⟩ := h
  exact ⟨Z, hZD, hZA, hZinf,
    destroyedTargets_window_or_density hcov⟩

end Erdos881
