import Erdos881.UnboundedMirrorGaps
import Erdos881.GuardianBridge

namespace Erdos881

theorem surviving_deletion_of_geometric_defectiveLevels
    {A : Set ℕ} {N₀ a c : ℕ} (L : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, ∀ z ∈ A, z ≠ a → z < L k → L k - z ∈ A)
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (_ha0 : 0 < a) (haL : a < L 0)
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c < L 0) (hca : c ≠ a)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ a ∧ w' ≠ a) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc, hwa, hw'a⟩ := hw
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  have hcLk : ∀ k, c < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have haLk : ∀ k, a < L k := by
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
    hlev k c hc hca (hcLk k)
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
  have hgapB : ∀ i j, j < i → L i - L j ∉ Set.range f := by
    rintro i j hji ⟨r, hr⟩
    simp only [hfdef] at hr
    have hLj : L j < L i := hmono hji
    have e : L (2 * r + 2) + L j = L i + c := by
      have := hcLk (2 * r + 2); omega
    rcases Nat.lt_trichotomy i (2 * r + 2) with h | h | h
    · have := hdiff i (2 * r + 2) h
      have : L j ≤ L i := le_of_lt hLj
      omega
    · rw [h] at e
      have := hcLk j
      omega
    · have h2 : L (2 * r + 2) ≤ L (i - 1) := hmono.monotone (by omega)
      have h3 : L j ≤ L (i - 1) := hmono.monotone (by omega)
      have h4 := hgrow (i - 1)
      have h5 : i - 1 + 1 = i := by omega
      rw [h5] at h4
      omega
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
    · obtain ⟨j, hjy⟩ := hyB
      simp only [hfdef] at hjy
      have hw'c : w' ≠ c := by omega
      have hwle : w ≤ 2 * c := by omega
      have hw'le : w' ≤ 2 * c := by omega
      rcases le_total j i with hji | hij
      · have hp₁A : L (2 * i + 2) - L (2 * j + 1) ∈ A :=
          hlev (2 * i + 2) _ (hmem (2 * j + 1))
            (by have := haLk (2 * j + 1); omega)
            (hmono (by omega))
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hlev (2 * j + 1) w hwA hwa
            (by have := h2cL (2 * j + 1) (by omega); omega)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hlev (2 * j + 2) w' hw'A hw'a
            (by have := h2cL (2 * j + 2) (by omega); omega)
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
          hlev (2 * j + 2) _ (hmem (2 * i + 1))
            (by have := haLk (2 * i + 1); omega)
            (hmono (by omega))
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hlev (2 * i + 1) w hwA hwa
            (by have := h2cL (2 * i + 1) (by omega); omega)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hlev (2 * i + 2) w' hw'A hw'a
            (by have := h2cL (2 * i + 2) (by omega); omega)
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
    · have hp₁A : L (2 * i + 1) - c ∈ A := hmirror (2 * i + 1)
      have hp₂A : L (2 * i + 2) - L (2 * i + 1) ∈ A :=
        hlev (2 * i + 2) _ (hmem (2 * i + 1))
          (by have := haLk (2 * i + 1); omega)
          (hmono (by omega))
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
        hlev (2 * j + 2) _ (hmem (2 * j + 1))
          (by have := haLk (2 * j + 1); omega)
          (hmono (by omega))
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

theorem surviving_deletion_of_cofinal_fixedRequiredElement
    {A : Set ℕ} {N₀ a c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (ha0 : 0 < a) (haN : N₀ ≤ a)
    (hstream : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A a m)
    (hc : c ∈ A) (hc0 : 0 < c) (hca : c ≠ a)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ a ∧ w' ≠ a) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hlev : ∀ K, ∃ M, K < M ∧ M ∈ A ∧
      ∀ z ∈ A, z ≠ a → z < M → M - z ∈ A := by
    intro K
    obtain ⟨m, hm, hpriv⟩ := hstream (K + a + N₀ + 1)
    obtain ⟨M, hMA, hMe⟩ := hpriv.corep_mem h0 hcov ha0 (by omega)
    refine ⟨M, by omega, hMA, ?_⟩
    intro z hz hza hzM
    obtain ⟨v, hvA, hvs⟩ :=
      hpriv.mirror_of_ne h0 hcov hz (by omega) (by omega) hza
    have hve : v = M - z := by omega
    exact hve ▸ hvA
  choose next hnext hnextMem hnextMir using hlev
  let L : ℕ → ℕ := fun k =>
    Nat.rec (next (c + a)) (fun _ prev => next (2 * prev)) k
  have hL0 : L 0 = next (c + a) := rfl
  have hLs : ∀ k, L (k + 1) = next (2 * L k) := fun _ => rfl
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    rw [hLs]
    exact hnext (2 * L k)
  have hcaL : c + a < L 0 := by rw [hL0]; exact hnext (c + a)
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 : 0 < L 0 := by omega
    have h3 : 0 < L k := by
      induction k with
      | zero => omega
      | succ k ih => have := hgrow k; omega
    omega
  have hlevL : ∀ k, ∀ z ∈ A, z ≠ a → z < L k → L k - z ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMir (c + a)
    | succ k => rw [hLs]; exact hnextMir (2 * L k)
  have hmemL : ∀ k, L k ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMem (c + a)
    | succ k => rw [hLs]; exact hnextMem (2 * L k)
  exact surviving_deletion_of_geometric_defectiveLevels L h0 hcov hmono
    hlevL hmemL hgrow ha0 (by omega) hc hc0 (by omega) hca hw

theorem surviving_deletion_of_singleton_orderThree_failure
    {A : Set ℕ} {N₀ a c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (ha0 : 0 < a) (haN : N₀ ≤ a)
    (hfail : ¬ IsExactTupleAsymptoticBasis
      (A \ (({a} : Finset ℕ) : Set ℕ)) 3)
    (hc : c ∈ A) (hc0 : 0 < c) (hca : c ≠ a)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ a ∧ w' ≠ a) :
    ∃ B ⊆ A, B.Infinite ∧ IsExactTupleAsymptoticBasis (A \ B) 3 := by
  have hstream := exists_late_privateTriple_of_singletonDeletion
    h0 hcov hfail
  have hstream' : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A a m := by
    intro N
    obtain ⟨m, hm, hp⟩ := hstream N
    exact ⟨m, hm, hp⟩
  obtain ⟨B, hBA, hBinf, hsurv⟩ :=
    surviving_deletion_of_cofinal_fixedRequiredElement h0 hcov ha0 haN
      hstream' hc hc0 hca hw
  exact ⟨B, hBA, hBinf, exactTupleBasis_diff_of_survival hsurv⟩

end Erdos881
