import Mathlib

/-!
# Rigidity of order-three private guardians

A target `m` is *order-three private* to a guardian `a ∈ A` when `m` has an
exact three-term representation over `A` and every such representation uses
`a`.  Against an order-two covering hypothesis (`PairCovers`), a private
pair `(a, m)` with a *big* guardian (`m < 2 * a`, i.e. the guardian above
the co-representative `M = m - a`) forces an extremely rigid landscape:

* `corep_mem`      : the co-representative `M = m - a` is an element;
* `desert`         : no element other than `a` lives in `(M, m - N₀]`;
* `mirror`         : `A⁺ ∩ (0, M)` is symmetric under `z ↦ M - z`;
* `guardian_le`    : the guardian is pinned to `a ≤ 2*M + 1`;
* `forced_translate` : every covered number in `(2*M, m - N₀]` is `a`
  plus an element, so `A` contains the whole translate window.

The centerpiece is `no_big_guardian_stacking`: two big-guardian private
pairs cannot coexist at separated scales.  The singleton-destroyer branch
of a counterexample to Erdős 881 is therefore self-limiting — it fires at
most once per scale window, never cofinally.

These statements were located by exhaustive finite search
(`scripts/probe_order3_private_structure.py`, `scripts/probe_stacking.py`):
the unique finite realization is `[0, M] ∪ {2*M+1}` guarding `3*M+1`, and
sweeps over ~200k stacked configurations found no two-level structure.
-/

namespace Erdos881

/-- `A` pair-covers every integer from `N₀` on: order-two covering with
zero allowed as a summand. -/
def PairCovers (A : Set ℕ) (N₀ : ℕ) : Prop :=
  ∀ n, N₀ ≤ n → ∃ x ∈ A, ∃ y ∈ A, x + y = n

/-- `m` is order-three private to the guardian `a`: it has an exact
three-term representation over `A`, and every such representation uses
`a`. -/
def IsPrivateTriple (A : Set ℕ) (a m : ℕ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m → x = a ∨ y = a ∨ z = a

/-- A covering set has a positive element. -/
theorem PairCovers.exists_pos_mem {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) : ∃ c ∈ A, 0 < c := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov (N₀ + 1) (by omega)
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · exact ⟨y, hy, by omega⟩
  · exact ⟨x, hx, hx0⟩

/-- The co-representative `M = m - a` of a private pair is an element:
the forced order-two representation of `m` must pass through `a`. -/
theorem IsPrivateTriple.corep_mem {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    (ha : 0 < a) (hm : N₀ ≤ m) :
    ∃ M ∈ A, a + M = m := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
  rcases hpriv.2 x hx y hy 0 h0 (by omega) with h | h | h
  · exact ⟨y, hy, by omega⟩
  · exact ⟨x, hx, by omega⟩
  · omega

/-- Desert: no element except the guardian itself lives strictly between
the co-representative `M = m - a` and `m - N₀`. -/
theorem IsPrivateTriple.desert {A : Set ℕ} {N₀ a m : ℕ}
    (_h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m) (ha : 0 < a)
    {z : ℕ} (hz : z ∈ A) (hlow : m < a + z) (hhigh : z + N₀ ≤ m) :
    z = a := by
  by_contra hne
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hpriv.2 z hz u hu v hv (by omega) with h | h | h
  · exact hne h
  · omega
  · omega

/-- Mirror: below the co-representative `M = m - a`, every positive
element reflects to an element (`z ↦ M - z`, phrased additively). -/
theorem IsPrivateTriple.mirror {A : Set ℕ} {N₀ a m : ℕ}
    (_h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    (hbig : m < 2 * a) (haN : N₀ + a ≤ m)
    {z : ℕ} (hz : z ∈ A) (hz0 : 0 < z) (hzM : z + a < m) :
    ∃ w ∈ A, a + z + w = m := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hpriv.2 z hz u hu v hv (by omega) with h | h | h
  · omega
  · exact ⟨v, hv, by omega⟩
  · exact ⟨u, hu, by omega⟩

/-- Boundary: a big guardian is pinned just above twice the
co-representative, `a ≤ 2*(m - a) + 1`. -/
theorem IsPrivateTriple.guardian_le {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    (hbig : m < 2 * a) (haN : N₀ + a ≤ m) :
    3 * a ≤ 2 * m + 1 := by
  by_contra hgt
  push Not at hgt
  have ha : 0 < a := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (a - 1) (by omega)
  have hu' : u ≤ m - a := by
    by_contra h
    push Not at h
    have := hpriv.desert h0 hcov ha hu (by omega) (by omega)
    omega
  have hv' : v ≤ m - a := by
    by_contra h
    push Not at h
    have := hpriv.desert h0 hcov ha hv (by omega) (by omega)
    omega
  omega

/-- Forced translate: any covered number strictly above `2*(m - a)` and at
least `N₀` below `m` is the guardian plus an element.  Consequently the
whole window `(2*(m-a) - a, (m-a) - N₀)` of integers lies in `A`. -/
theorem IsPrivateTriple.forced_translate {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m) (ha : 0 < a)
    (haM : a ≤ m)
    {n : ℕ} (hn : N₀ ≤ n) (hn2M : 2 * (m - a) < n) (hnm : n + N₀ ≤ m) :
    ∃ t ∈ A, a + t = n := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov n hn
  rcases Nat.lt_or_ge (m - a) u with hu1 | hu1
  · have := hpriv.desert h0 hcov ha hu (by omega) (by omega)
    exact ⟨v, hv, by omega⟩
  · rcases Nat.lt_or_ge (m - a) v with hv1 | hv1
    · have := hpriv.desert h0 hcov ha hv (by omega) (by omega)
      exact ⟨u, hu, by omega⟩
    · omega

/-- Small guardians leave a *totally empty* desert: when `2*a < m` (the
guardian below its co-representative), no element at all lives in
`(m - a, m - N₀)` — the desert exception `z = a` is out of range. -/
theorem IsPrivateTriple.small_desert {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m) (ha : 0 < a)
    (hsmall : 2 * a < m)
    {z : ℕ} (hz : z ∈ A) (hlow : m < a + z) (hhigh : z + N₀ ≤ m) :
    False := by
  have := hpriv.desert h0 hcov ha hz hlow hhigh
  omega

/-- Guardian-free mirror, valid for guardians of every size: a positive
element below the co-representative other than the guardian itself
reflects to an element.  For small guardians this gives a reflection
level with a single interior defect at `a`. -/
theorem IsPrivateTriple.mirror_of_ne {A : Set ℕ} {N₀ a m : ℕ}
    (_h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    {z : ℕ} (hz : z ∈ A) (hzM : z + a < m) (hzN : z + N₀ ≤ m)
    (hza : z ≠ a) :
    ∃ w ∈ A, a + z + w = m := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hpriv.2 z hz u hu v hv (by omega) with h | h | h
  · exact absurd h hza
  · exact ⟨v, hv, by omega⟩
  · exact ⟨u, hu, by omega⟩

/-- **No stacking.**  Two big-guardian private pairs cannot coexist at
separated scales: if `(a₁, m₁)` and `(a₂, m₂)` are both private with big
guardians, the first has any room at all (`N₀ + 3 ≤ a₁`), and the second
lives strictly above the first (`m₁ + a₂ ≤ m₂`, i.e. `m₁ ≤ M₂`), then the
configuration is contradictory.

Either the second guardian sits near its boundary, in which case the
second forced-translate window plants two distinct elements inside the
first desert; or it sits lower, in which case the mirror below `M₂`
manufactures a representation of `m₂` avoiding `a₂` outright. -/
theorem no_big_guardian_stacking {A : Set ℕ} {N₀ a₁ m₁ a₂ m₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A a₁ m₁) (h2 : IsPrivateTriple A a₂ m₂)
    (hbig1 : m₁ < 2 * a₁) (hN1 : N₀ + a₁ ≤ m₁)
    (hbig2 : m₂ < 2 * a₂) (hN2 : N₀ + a₂ ≤ m₂)
    (hsize : N₀ + 3 ≤ a₁)
    (hsep : m₁ + a₂ ≤ m₂) :
    False := by
  have ha₁ : 0 < a₁ := by omega
  have ha₂ : 0 < a₂ := by omega
  obtain ⟨M₂, hM₂A, hM₂⟩ := h2.corep_mem h0 hcov ha₂ (by omega)
  by_cases hcase : a₂ + (m₁ - a₁) < 2 * M₂
  · -- low guardian: build a representation of m₂ avoiding a₂
    by_cases hjA : (a₂ - M₂) ∈ A
    · rcases h2.2 M₂ hM₂A M₂ hM₂A _ hjA (by omega) with h | h | h <;> omega
    · have hn'' : N₀ ≤ 2 * M₂ - a₂ := by omega
      obtain ⟨u, hu, v, hv, huv⟩ := hcov _ hn''
      rcases Nat.eq_zero_or_pos u with hu0 | hu0
      · -- v = 2*M₂ - a₂ is an element; its mirror is a₂ - M₂, contradiction
        obtain ⟨w, hw, hws⟩ :=
          h2.mirror h0 hcov hbig2 hN2 hv (by omega) (by omega)
        have : w = a₂ - M₂ := by omega
        exact hjA (this ▸ hw)
      rcases Nat.eq_zero_or_pos v with hv0 | hv0
      · obtain ⟨w, hw, hws⟩ :=
          h2.mirror h0 hcov hbig2 hN2 hu (by omega) (by omega)
        have : w = a₂ - M₂ := by omega
        exact hjA (this ▸ hw)
      -- both positive: reflect both and add M₂ to hit m₂ without a₂
      obtain ⟨wu, hwu, hwus⟩ :=
        h2.mirror h0 hcov hbig2 hN2 hu hu0 (by omega)
      obtain ⟨wv, hwv, hwvs⟩ :=
        h2.mirror h0 hcov hbig2 hN2 hv hv0 (by omega)
      rcases h2.2 wu hwu wv hwv M₂ hM₂A (by omega) with h | h | h <;> omega
  · -- boundary guardian: the second translate window floods the first desert
    have key : ∀ j, m₁ - a₁ < j → j + N₀ + 1 ≤ m₁ → j ∈ A := by
      intro j hj1 hj2
      obtain ⟨t, ht, hts⟩ :=
        h2.forced_translate h0 hcov ha₂ (by omega)
          (n := j + a₂) (by omega) (by omega) (by omega)
      have : t = j := by omega
      exact this ▸ ht
    have hj1 : (m₁ - a₁ + 1) ∈ A := key _ (by omega) (by omega)
    have hj2 : (m₁ - a₁ + 2) ∈ A := key _ (by omega) (by omega)
    have e1 : m₁ - a₁ + 1 = a₁ :=
      h1.desert h0 hcov ha₁ hj1 (by omega) (by omega)
    have e2 : m₁ - a₁ + 2 = a₁ :=
      h1.desert h0 hcov ha₁ hj2 (by omega) (by omega)
    omega

end Erdos881
