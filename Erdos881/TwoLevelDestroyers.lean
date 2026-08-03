import Erdos881.PinnedMirror

namespace Erdos881

/-- `n` is two-destroyed by the pair `{u, v}`: a two-term
representation exists and every two-term representation meets the
pair. -/
def IsTwoDestroyer (A : Set ℕ) (u v n : ℕ) : Prop :=
  (∃ y ∈ A, ∃ z ∈ A, y + z = n) ∧
    ∀ y ∈ A, ∀ z ∈ A, y + z = n → y = u ∨ y = v ∨ z = u ∨ z = v

/-- The pair destroys genuinely: neither required element covers all
representations alone. -/
def IsGenuineTwoDestroyer (A : Set ℕ) (u v n : ℕ) : Prop :=
  IsTwoDestroyer A u v n ∧
    (∃ y ∈ A, ∃ z ∈ A, y + z = n ∧ y ≠ u ∧ z ≠ u) ∧
    (∃ y ∈ A, ∃ z ∈ A, y + z = n ∧ y ≠ v ∧ z ≠ v)

/-- The representation dodging `u` must pass through `v`, forcing the
corep `n - v` into `A`. -/
theorem IsGenuineTwoDestroyer.corep_right {A : Set ℕ} {u v n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n) :
    n - v ∈ A ∧ v ≤ n := by
  obtain ⟨⟨_, hdes⟩, ⟨y, hy, z, hz, hsum, hyu, hzu⟩, _⟩ := h
  rcases hdes y hy z hz hsum with h' | h' | h' | h'
  · exact absurd h' hyu
  · subst h'
    exact ⟨by simpa [show n - y = z by omega] using hz, by omega⟩
  · exact absurd h' hzu
  · subst h'
    exact ⟨by simpa [show n - z = y by omega] using hy, by omega⟩

/-- The representation dodging `v` must pass through `u`, forcing the
corep `n - u` into `A`. -/
theorem IsGenuineTwoDestroyer.corep_left {A : Set ℕ} {u v n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n) :
    n - u ∈ A ∧ u ≤ n := by
  obtain ⟨⟨hrep, hdes⟩, hgu, ⟨y, hy, z, hz, hsum, hyv, hzv⟩⟩ := h
  rcases hdes y hy z hz hsum with h' | h' | h' | h'
  · subst h'
    exact ⟨by simpa [show n - y = z by omega] using hz, by omega⟩
  · exact absurd h' hyv
  · subst h'
    exact ⟨by simpa [show n - z = y by omega] using hy, by omega⟩
  · exact absurd h' hzv

theorem IsGenuineTwoDestroyer.support_confined {A : Set ℕ} {u v n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n)
    {y : ℕ} (hy : y ∈ A) (hyn : y ≤ n) (hny : n - y ∈ A) :
    y = u ∨ y = v ∨ y = n - u ∨ y = n - v := by
  have hu := h.corep_left
  have hv := h.corep_right
  rcases h.1.2 y hy (n - y) hny (by omega) with h' | h' | h' | h' <;>
    omega

/-- The representation dodging `v` passes through `u`, so the left
required element is itself an element. -/
theorem IsGenuineTwoDestroyer.left_mem {A : Set ℕ} {u v n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n) : u ∈ A := by
  obtain ⟨⟨_, hdes⟩, _, ⟨y, hy, z, hz, hsum, hyv, hzv⟩⟩ := h
  rcases hdes y hy z hz hsum with h' | h' | h' | h'
  · exact h' ▸ hy
  · exact absurd h' hyv
  · exact h' ▸ hz
  · exact absurd h' hzv

/-- The representation dodging `u` passes through `v`, so the right
required element is itself an element. -/
theorem IsGenuineTwoDestroyer.right_mem {A : Set ℕ} {u v n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n) : v ∈ A := by
  obtain ⟨⟨_, hdes⟩, ⟨y, hy, z, hz, hsum, hyu, hzu⟩, _⟩ := h
  rcases hdes y hy z hz hsum with h' | h' | h' | h'
  · exact absurd h' hyu
  · exact h' ▸ hy
  · exact absurd h' hzu
  · exact h' ▸ hz

theorem genuine_twoDestroyer_required_elements_confined {A : Set ℕ}
    {u v u' v' n : ℕ}
    (h : IsGenuineTwoDestroyer A u v n)
    (h' : IsGenuineTwoDestroyer A u' v' n) :
    (u' = u ∨ u' = v ∨ u' = n - u ∨ u' = n - v) ∧
      (v' = u ∨ v' = v ∨ v' = n - u ∨ v' = n - v) :=
  ⟨h.support_confined h'.left_mem h'.corep_left.2 h'.corep_left.1,
    h.support_confined h'.right_mem h'.corep_right.2 h'.corep_right.1⟩

end Erdos881
