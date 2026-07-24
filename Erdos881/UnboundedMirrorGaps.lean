import Erdos881.GuardianBridge

/-!
# Spare keys for reflection levels with unbounded gaps

`MirrorPeriodicity.lean` handled reflection-level streams with *bounded*
gaps.  This file removes the bound in the geometric regime: if the levels
are elements and each level more than doubles the previous one — so the
gaps `L (k+1) - L k > L k` are **unbounded** — a surviving infinite
deletion still exists.

The deletion is the mirror `L (2k+2) - c` of a fixed anchor `c < L 0` at
every second level.  Growth kills every collision:

* a cross-level mirror `L a - L b` can never be a deleted element, since
  `c + L a = L (2r+2) + L b` forces two level values within `c < L 0` of
  each other, impossible when consecutive levels more than double
  (`geometric_level_separation`);
* near-anchor mirrors `L k - v` with `v ≤ 2c`, `v ≠ c` escape for the
  same reason, the diagonal case being excluded exactly by `v ≠ c`;
* the both-deleted case `n = (L a - c) + (L b - c)` is repaired by
  `(L a - L (b-1)) + (L (b-1) - w) + (L b - w')` where `w + w' = 2c` is
  an *unbalanced* representation of `2c` (hypothesis `hw`) — this is the
  one place the anchor's own additive structure is needed.

The general conjecture — cofinal reflection levels of arbitrary spacing —
remains open (`docs/unbounded-gaps.md`); the obstruction is precisely the
collision bookkeeping that growth trivializes here.
-/

namespace Erdos881

/-- Under doubling growth, two distinct level values can never lie within
`L 0` of each other after shifting by at most `L 0`: formally,
`c + L s = L r + L t` is impossible for `c < L 0` unless the indices make
it degenerate. -/
theorem geometric_level_separation {L : ℕ → ℕ}
    (hmono : StrictMono L) (hgrow : ∀ k, 2 * L k < L (k + 1))
    {i j : ℕ} (hij : i < j) :
    L 0 + L i < L j := by
  have h1 := hgrow i
  have h2 : L (i + 1) ≤ L j := hmono.monotone (by omega)
  have h0 : L 0 ≤ L i := hmono.monotone (Nat.zero_le i)
  omega

/-- **Unbounded-gap spare keys (geometric regime).**  Reflection levels
that are elements and more than double at every step — hence with
unbounded gaps — admit a surviving infinite deletion: remove the mirror
of a fixed anchor at every second level. -/
theorem surviving_deletion_of_geometric_reflectionLevels
    {A : Set ℕ} {N₀ c : ℕ} (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, IsReflectionLevel A (L k))
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c < L 0)
    (hw : ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc⟩ := hw
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  have hcLk : ∀ k, c < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hLpos : ∀ k, 0 < L k := fun k => by have := hcLk k; omega
  have h2cL : ∀ k, 1 ≤ k → 2 * c < L k := by
    intro k hk
    have h1 : 2 * L 0 < L 1 := hgrow 0
    have h2 : L 1 ≤ L k := hmono.monotone hk
    omega
  set f : ℕ → ℕ := fun k => L (2 * k + 2) - c with hfdef
  have hmirror : ∀ k, L k - c ∈ A := fun k =>
    ((hlev k) c hc0 (hcLk k)).mp hc
  have hfA : ∀ k, f k ∈ A := fun k => hmirror _
  have hfinj : Function.Injective f := by
    intro i j hij
    simp only [hfdef] at hij
    have h1 : L (2 * i + 2) = L (2 * j + 2) := by
      have := hcLk (2 * i + 2); have := hcLk (2 * j + 2); omega
    have := hmono.injective h1
    omega
  have hBsub : Set.range f ⊆ A := by rintro v ⟨k, rfl⟩; exact hfA k
  have h0B : (0 : ℕ) ∉ Set.range f := by
    rintro ⟨r, hr⟩
    simp only [hfdef] at hr
    have := hcLk (2 * r + 2)
    omega
  -- cross-level mirrors escape the deleted set
  have hgapB : ∀ a b, b < a → L a - L b ∉ Set.range f := by
    rintro a b hba ⟨r, hr⟩
    simp only [hfdef] at hr
    have hLb : L b < L a := hmono hba
    have e : L (2 * r + 2) + L b = L a + c := by
      have := hcLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy a (2 * r + 2) with h | h | h
    · have := hdiff a (2 * r + 2) h
      have : L b ≤ L a := le_of_lt hLb
      omega
    · rw [h] at e
      have := hcLk b
      omega
    · have h2 : L (2 * r + 2) ≤ L (a - 1) := hmono.monotone (by omega)
      have h3 : L b ≤ L (a - 1) := hmono.monotone (by omega)
      have h4 := hgrow (a - 1)
      have h5 : a - 1 + 1 = a := by omega
      rw [h5] at h4
      omega
  -- near-anchor mirrors escape unless the shift equals the anchor
  have hnearB : ∀ k v, v ≤ 2 * c → v ≠ c → v < L k →
      L k - v ∉ Set.range f := by
    rintro k v hv2 hvc hvk ⟨r, hr⟩
    simp only [hfdef] at hr
    have e : L (2 * r + 2) + v = L k + c := by
      have := hcLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy k (2 * r + 2) with h | h | h
    · have := hdiff k (2 * r + 2) h
      omega
    · rw [h] at e
      omega
    · have := hdiff (2 * r + 2) k h
      omega
  refine ⟨Set.range f, hBsub, Set.infinite_range_of_injective hfinj, ?_⟩
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  by_cases hxB : x ∈ Set.range f
  · obtain ⟨i, hix⟩ := hxB
    simp only [hfdef] at hix
    by_cases hyB : y ∈ Set.range f
    · -- both deleted: unbalanced 2c-representation repairs the pair
      obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hw'c : w' ≠ c := by omega
      have hwle : w ≤ 2 * c := by omega
      have hw'le : w' ≤ 2 * c := by omega
      rcases le_total j i with hji | hij
      · have hp₁A : L (2 * i + 2) - L (2 * j + 1) ∈ A :=
          ((hlev (2 * i + 2)) _ (hLpos (2 * j + 1))
            (hmono (by omega))).mp (hmem (2 * j + 1))
        have hp₂A : L (2 * j + 1) - w ∈ A := by
          rcases Nat.eq_zero_or_pos w with hw0 | hw0
          · simpa [hw0] using hmem (2 * j + 1)
          · exact ((hlev (2 * j + 1)) w hw0
              (by have := h2cL (2 * j + 1) (by omega); omega)).mp hwA
        have hp₃A : L (2 * j + 2) - w' ∈ A := by
          rcases Nat.eq_zero_or_pos w' with hw0 | hw0
          · simpa [hw0] using hmem (2 * j + 2)
          · exact ((hlev (2 * j + 2)) w' hw0
              (by have := h2cL (2 * j + 2) (by omega); omega)).mp hw'A
        refine ⟨_, hp₁A, _, hp₂A, _, hp₃A,
          hgapB (2 * i + 2) (2 * j + 1) (by omega),
          hnearB (2 * j + 1) w hwle hwc
            (by have := h2cL (2 * j + 1) (by omega); omega),
          hnearB (2 * j + 2) w' hw'le hw'c
            (by have := h2cL (2 * j + 2) (by omega); omega), ?_⟩
        have hb1 : L (2 * j + 1) ≤ L (2 * i + 2) :=
          hmono.monotone (by omega)
        have hb2 : w < L (2 * j + 1) := by
          have := h2cL (2 * j + 1) (by omega); omega
        have hb3 : w' < L (2 * j + 2) := by
          have := h2cL (2 * j + 2) (by omega); omega
        have := hcLk (2 * i + 2); have := hcLk (2 * j + 2)
        omega
      · have hp₁A : L (2 * j + 2) - L (2 * i + 1) ∈ A :=
          ((hlev (2 * j + 2)) _ (hLpos (2 * i + 1))
            (hmono (by omega))).mp (hmem (2 * i + 1))
        have hp₂A : L (2 * i + 1) - w ∈ A := by
          rcases Nat.eq_zero_or_pos w with hw0 | hw0
          · simpa [hw0] using hmem (2 * i + 1)
          · exact ((hlev (2 * i + 1)) w hw0
              (by have := h2cL (2 * i + 1) (by omega); omega)).mp hwA
        have hp₃A : L (2 * i + 2) - w' ∈ A := by
          rcases Nat.eq_zero_or_pos w' with hw0 | hw0
          · simpa [hw0] using hmem (2 * i + 2)
          · exact ((hlev (2 * i + 2)) w' hw0
              (by have := h2cL (2 * i + 2) (by omega); omega)).mp hw'A
        refine ⟨_, hp₁A, _, hp₂A, _, hp₃A,
          hgapB (2 * j + 2) (2 * i + 1) (by omega),
          hnearB (2 * i + 1) w hwle hwc
            (by have := h2cL (2 * i + 1) (by omega); omega),
          hnearB (2 * i + 2) w' hw'le hw'c
            (by have := h2cL (2 * i + 2) (by omega); omega), ?_⟩
        have hb1 : L (2 * i + 1) ≤ L (2 * j + 2) :=
          hmono.monotone (by omega)
        have hb2 : w < L (2 * i + 1) := by
          have := h2cL (2 * i + 1) (by omega); omega
        have hb3 : w' < L (2 * i + 2) := by
          have := h2cL (2 * i + 2) (by omega); omega
        have := hcLk (2 * i + 2); have := hcLk (2 * j + 2)
        omega
    · -- only x deleted: reroute through the previous (odd) level
      have hp₁A : L (2 * i + 1) - c ∈ A := hmirror (2 * i + 1)
      have hp₂A : L (2 * i + 2) - L (2 * i + 1) ∈ A :=
        ((hlev (2 * i + 2)) _ (hLpos (2 * i + 1))
          (hmono (by omega))).mp (hmem (2 * i + 1))
      have hp₁B : L (2 * i + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hfdef] at hr
        have e : L (2 * i + 1) = L (2 * r + 2) := by
          have := hcLk (2 * i + 1); have := hcLk (2 * r + 2); omega
        have := hmono.injective e
        omega
      refine ⟨_, hp₁A, _, hp₂A, y, hy, hp₁B,
        hgapB (2 * i + 2) (2 * i + 1) (by omega), hyB, ?_⟩
      have hb1 : L (2 * i + 1) ≤ L (2 * i + 2) := hmono.monotone (by omega)
      have := hcLk (2 * i + 1); have := hcLk (2 * i + 2)
      omega
  · by_cases hyB : y ∈ Set.range f
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hp₁A : L (2 * j + 1) - c ∈ A := hmirror (2 * j + 1)
      have hp₂A : L (2 * j + 2) - L (2 * j + 1) ∈ A :=
        ((hlev (2 * j + 2)) _ (hLpos (2 * j + 1))
          (hmono (by omega))).mp (hmem (2 * j + 1))
      have hp₁B : L (2 * j + 1) - c ∉ Set.range f := by
        rintro ⟨r, hr⟩
        simp only [hfdef] at hr
        have e : L (2 * j + 1) = L (2 * r + 2) := by
          have := hcLk (2 * j + 1); have := hcLk (2 * r + 2); omega
        have := hmono.injective e
        omega
      refine ⟨_, hp₁A, _, hp₂A, x, hx, hp₁B,
        hgapB (2 * j + 2) (2 * j + 1) (by omega), hxB, ?_⟩
      have hb1 : L (2 * j + 1) ≤ L (2 * j + 2) := hmono.monotone (by omega)
      have := hcLk (2 * j + 1); have := hcLk (2 * j + 2)
      omega
    · exact ⟨x, hx, y, hy, 0, h0, hxB, hyB, h0B, by omega⟩

/-- **The mirror endgame, closed for element-levels.**  Cofinal
reflection levels that are elements — with *no spacing assumption
whatsoever* — admit a surviving infinite deletion: greedily extract a
doubling subsequence and hand it to the geometric theorem.  The geometric
hypotheses never mention consecutiveness, so the extraction is free. -/
theorem surviving_deletion_of_cofinal_reflectionLevels
    {A : Set ℕ} {N₀ c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hlev : ∀ K, ∃ M, K < M ∧ IsReflectionLevel A M ∧ M ∈ A)
    (hc : c ∈ A) (hc0 : 0 < c)
    (hw : ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  choose next hnext hnextLev hnextMem using hlev
  let L : ℕ → ℕ := fun k =>
    Nat.rec (next c) (fun _ prev => next (2 * prev)) k
  have hL0 : L 0 = next c := rfl
  have hLs : ∀ k, L (k + 1) = next (2 * L k) := fun _ => rfl
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    rw [hLs]
    exact hnext (2 * L k)
  have hcL : c < L 0 := by rw [hL0]; exact hnext c
  have hLpos : ∀ k, 0 < L k := by
    intro k
    induction k with
    | zero => omega
    | succ k ih => have := hgrow k; omega
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 := hLpos k
    omega
  have hlevL : ∀ k, IsReflectionLevel A (L k) := by
    intro k
    cases k with
    | zero => exact hnextLev c
    | succ k => rw [hLs]; exact hnextLev (2 * L k)
  have hmemL : ∀ k, L k ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMem c
    | succ k => rw [hLs]; exact hnextMem (2 * L k)
  exact surviving_deletion_of_geometric_reflectionLevels L h0 hcov hmono
    hlevL hmemL hgrow hc hc0 hcL hw

/-- Repo-vocabulary form of the closed mirror endgame: an exact order-two
tuple basis containing zero, with cofinal element-reflection-levels of
arbitrary spacing and an anchor whose double has an unbalanced
representation, admits an infinite deletion leaving an exact order-three
tuple basis. -/
theorem exactTupleBasis_orderThree_deletion_of_cofinal_reflectionLevels
    {A : Set ℕ} {c : ℕ}
    (h0 : 0 ∈ A) (h2 : IsExactTupleAsymptoticBasis A 2)
    (hlev : ∀ K, ∃ M, K < M ∧ IsReflectionLevel A M ∧ M ∈ A)
    (hc : c ∈ A) (hc0 : 0 < c)
    (hw : ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c) :
    ∃ B ⊆ A, B.Infinite ∧ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨N₀, hcov⟩ := pairCovers_of_exactTupleBasis h2
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_cofinal_reflectionLevels h0 hcov hlev hc hc0 hw
  exact ⟨B, hBA, hBinf, exactTupleBasis_diff_of_survival hsurv⟩

/-- Repo-vocabulary corollary: an exact order-two tuple basis with
geometric reflection levels admits an infinite deletion leaving an exact
order-three tuple basis — the positive Erdős 881 answer for the
unbounded-gap geometric mirror regime. -/
theorem exactTupleBasis_orderThree_deletion_of_geometric_reflectionLevels
    {A : Set ℕ} {c : ℕ} (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (h2 : IsExactTupleAsymptoticBasis A 2)
    (hmono : StrictMono L)
    (hlev : ∀ k, IsReflectionLevel A (L k))
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c < L 0)
    (hw : ∃ w ∈ A, ∃ w' ∈ A, w + w' = 2 * c ∧ w ≠ c) :
    ∃ B ⊆ A, B.Infinite ∧ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  obtain ⟨N₀, hcov⟩ := pairCovers_of_exactTupleBasis h2
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_geometric_reflectionLevels L h0 hcov hmono hlev
      hmem hgrow hc hc0 hcL hw
  exact ⟨B, hBA, hBinf, exactTupleBasis_diff_of_survival hsurv⟩

end Erdos881
