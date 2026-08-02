/-
# The private-target census, formalized

The laboratory census held at 100% in every trimmed minimal world
ever built: every element owns a target that only it can serve.
This file proves the census in the official tuple vocabulary at
EVERY order: in an exact order-`k` tuple basis, every ESSENTIAL
element (one whose removal breaks the basis) owns cofinally many
targets whose every `k`-representation uses it.  At order two the
representation is pinned completely: the unique pair `{a, n - a}`.

Trimmed lab worlds are exactly the elementwise-minimal case, so
`private_census_of_elementwise_minimal` is the 100% census: the
lab observation is a theorem, not a phenomenon.

Shape filter: the conclusions force membership (`a` sits inside
EVERY representation) and, at order two, force the full
decomposition — no `x ∈ A + A` vacuity.  Non-vacuous: minimal
asymptotic bases of order two exist classically, and every
strongly minimal instance in this repository inhabits the
hypotheses after trimming.
-/

import Erdos881.AdditiveSupports

namespace Erdos881

/-- **The essential element's private stream, every order.**  If
`A` is an exact order-`k` tuple basis and deleting `a` breaks
that, then cofinally many targets are covered AND have every
`k`-tuple representation pass through `a`. -/
theorem essential_private_target_stream {A : Set ℕ}
    {k a : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hess : ¬ IsExactTupleAsymptoticBasis
      (A \ {a}) k) :
    ∀ N, ∃ n, N ≤ n ∧
      (∃ v : Fin k → ℕ,
        (∀ i, v i ∈ A) ∧ ∑ i, v i = n) ∧
      (∀ v : Fin k → ℕ, (∀ i, v i ∈ A) →
        ∑ i, v i = n → ∃ i, v i = a) := by
  classical
  obtain ⟨N₀, hN₀⟩ := hbasis
  intro N
  unfold IsExactTupleAsymptoticBasis at hess
  push Not at hess
  obtain ⟨n, hn, hno⟩ := hess (max N N₀)
  refine ⟨n, le_trans (le_max_left _ _) hn,
    hN₀ n (le_trans (le_max_right _ _) hn), ?_⟩
  intro v hv hsum
  by_contra hcon
  push Not at hcon
  exact hno v (fun i => ⟨hv i, hcon i⟩) hsum

/-- **The pinned pair at order two.**  An essential element's
private targets have a UNIQUE decomposition: the pair
`{a, n - a}` — privateness buys uniqueness for free at order two,
which is exactly what the laboratory census measured. -/
theorem essential_unique_pair_tuple {A : Set ℕ} {a : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A 2)
    (hess : ¬ IsExactTupleAsymptoticBasis
      (A \ {a}) 2) :
    ∀ N, ∃ n, N ≤ n ∧ a ≤ n ∧ n - a ∈ A ∧
      ∀ v : Fin 2 → ℕ, (∀ i, v i ∈ A) →
        ∑ i, v i = n →
        (v 0 = a ∧ v 1 = n - a) ∨
        (v 1 = a ∧ v 0 = n - a) := by
  intro N
  obtain ⟨n, hn, ⟨w, hw, hwsum⟩, hall⟩ :=
    essential_private_target_stream hbasis hess
      (N + a)
  rw [Fin.sum_univ_two] at hwsum
  have hpin : ∀ v : Fin 2 → ℕ, (∀ i, v i ∈ A) →
      v 0 + v 1 = n → v 0 = a ∨ v 1 = a := by
    intro v hv hvs
    obtain ⟨j, hj⟩ := hall v hv
      (by rw [Fin.sum_univ_two]; exact hvs)
    have hlt := j.isLt
    rcases (by omega : (j : ℕ) = 0 ∨ (j : ℕ) = 1)
      with h | h
    · left
      rw [show (0 : Fin 2) = j from
        Fin.ext (by simp [h])]
      exact hj
    · right
      rw [show (1 : Fin 2) = j from
        Fin.ext (by simp [h])]
      exact hj
  have hw01 := hpin w hw hwsum
  have hcomp : a ≤ n ∧ n - a ∈ A := by
    rcases hw01 with h | h
    · refine ⟨by omega, ?_⟩
      rw [show n - a = w 1 by omega]
      exact hw 1
    · refine ⟨by omega, ?_⟩
      rw [show n - a = w 0 by omega]
      exact hw 0
  refine ⟨n, by omega, hcomp.1, hcomp.2, ?_⟩
  intro v hv hvsum
  rw [Fin.sum_univ_two] at hvsum
  rcases hpin v hv hvsum with h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr ⟨h, by omega⟩

/-- **The 100% census.**  In an elementwise-minimal exact
order-`k` tuple basis — a trimmed world — EVERY element owns
cofinally many all-representations-marked targets.  The
laboratory's universal private-pair census is a theorem. -/
theorem private_census_of_elementwise_minimal
    {A : Set ℕ} {k : ℕ}
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (hmin : ∀ a ∈ A,
      ¬ IsExactTupleAsymptoticBasis (A \ {a}) k) :
    ∀ a ∈ A, ∀ N, ∃ n, N ≤ n ∧
      (∃ v : Fin k → ℕ,
        (∀ i, v i ∈ A) ∧ ∑ i, v i = n) ∧
      (∀ v : Fin k → ℕ, (∀ i, v i ∈ A) →
        ∑ i, v i = n → ∃ i, v i = a) :=
  fun a ha =>
    essential_private_target_stream hbasis (hmin a ha)

end Erdos881
