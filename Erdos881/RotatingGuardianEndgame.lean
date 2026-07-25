import Erdos881.FixedGuardianEndgame
import Erdos881.TeamGraphRamsey

/-!
# The rotating-guardian endgame: the singleton stream dies

`FixedGuardianEndgame` kills a guardian whose private targets recur
cofinally.  Here the extraction is generalized to guardians that
*rotate*: the defect of each corep level may differ, because the
engine only ever reflects the anchor `c`, the unbalanced parts
`w, w'`, and **lower** levels — all of which are known before the next
level is chosen.  Each new level therefore only has to dodge a finite
forbidden set, and if the stream refuses to dodge, some single
guardian recurs cofinally and the fixed kill fires.

* `IsPrivateTriple.corep_lower` — the desert plus two stacked dyadic
  covering windows force the corep above `~m/4`: stream levels grow.
* `surviving_deletion_of_geometric_rotatingDefects` — the extraction
  engine with per-level defects.
* `surviving_deletion_of_cofinal_privateStream` — **any cofinal stream
  of positive singleton guardians forces a surviving deletion**, given
  anchors dodging any prescribed value.  This closes the singleton
  branch of `master_reduction` (big and small guardians alike) modulo
  the anchor-abundance hypothesis.
-/

namespace Erdos881

/-- **Coreps are large.**  The desert of a private pair tolerates only
the guardian, but two disjoint dyadic covering windows below `m - N₀`
would both have to be the guardian: hence `m ≤ 4(m-a) + 4N₀ + 20`. -/
theorem IsPrivateTriple.corep_lower {A : Set ℕ} {N₀ a m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m) (ha : 0 < a)
    (hbig : 4 * (m - a) + 4 * N₀ + 20 ≤ m) :
    False := by
  have hwin : ∀ q, N₀ ≤ q → q + N₀ + 1 ≤ m → m - a < q / 2 →
      ∃ z, z = a ∧ 2 * z ≥ q ∧ z ≤ q := by
    intro q hq hqm hMq
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov q hq
    rcases le_total y z with h | h
    · have := hpriv.desert h0 hcov ha hz (by omega) (by omega)
      exact ⟨z, this, by omega, by omega⟩
    · have := hpriv.desert h0 hcov ha hy (by omega) (by omega)
      exact ⟨y, this, by omega, by omega⟩
  obtain ⟨z₁, hz₁, hz₁l, hz₁r⟩ :=
    hwin (m - N₀ - 1) (by omega) (by omega) (by omega)
  obtain ⟨z₂, hz₂, hz₂l, hz₂r⟩ :=
    hwin ((m - N₀ - 1) / 2 - 1) (by omega) (by omega) (by omega)
  omega

/-- **Spare keys from rotating defective mirrors.**  The geometric
extraction with a different defect `d k` at each level: every
reflection the proof performs dodges its level's defect by
hypothesis. -/
theorem surviving_deletion_of_geometric_rotatingDefects
    {A : Set ℕ} {N₀ c w w' : ℕ} (L d : ℕ → ℕ)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmono : StrictMono L)
    (hlev : ∀ k, ∀ z ∈ A, z ≠ d k → z + N₀ < L k → L k - z ∈ A)
    (hmem : ∀ k, L k ∈ A)
    (hgrow : ∀ k, 2 * L k < L (k + 1))
    (hc : c ∈ A) (hc0 : 0 < c) (hcL : c + N₀ < L 0)
    (hwA : w ∈ A) (hw'A : w' ∈ A) (hww : w + w' = 2 * c) (hwc : w ≠ c)
    (hcd : ∀ k, c ≠ d k) (hwd : ∀ k, w ≠ d k) (hw'd : ∀ k, w' ≠ d k)
    (hLd : ∀ j k, j < k → L j ≠ d k) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  have hdiff : ∀ i j, i < j → L 0 + L i < L j :=
    fun i j h => geometric_level_separation hmono hgrow h
  have hcLk : ∀ k, c + N₀ < L k := by
    intro k
    have := hmono.monotone (Nat.zero_le k)
    omega
  have hLpos : ∀ k, 0 < L k := fun k => by have := hcLk k; omega
  have h2cL : ∀ k, 1 ≤ k → 2 * c + N₀ < L k := by
    intro k hk
    have h1 : 2 * L 0 < L 1 := hgrow 0
    have h2 : L 1 ≤ L k := hmono.monotone hk
    omega
  have hLslack : ∀ i j, i < j → L i + N₀ < L j := by
    intro i j hij
    have h1 : L (i + 1) ≤ L j := hmono.monotone (by omega)
    have h2 := hgrow i
    have h3 : L 0 ≤ L i := hmono.monotone (Nat.zero_le i)
    omega
  set f : ℕ → ℕ := fun k => L (2 * k + 2) - c with hfdef
  have hmirror : ∀ k, L k - c ∈ A := fun k =>
    hlev k c hc (hcd k) (hcLk k)
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
            (hLd (2 * j + 1) (2 * i + 2) (by omega))
            (hLslack (2 * j + 1) (2 * i + 2) (by omega))
        have hp₂A : L (2 * j + 1) - w ∈ A :=
          hlev (2 * j + 1) w hwA (hwd _)
            (by have := h2cL (2 * j + 1) (by omega); omega)
        have hp₃A : L (2 * j + 2) - w' ∈ A :=
          hlev (2 * j + 2) w' hw'A (hw'd _)
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
            (hLd (2 * i + 1) (2 * j + 2) (by omega))
            (hLslack (2 * i + 1) (2 * j + 2) (by omega))
        have hp₂A : L (2 * i + 1) - w ∈ A :=
          hlev (2 * i + 1) w hwA (hwd _)
            (by have := h2cL (2 * i + 1) (by omega); omega)
        have hp₃A : L (2 * i + 2) - w' ∈ A :=
          hlev (2 * i + 2) w' hw'A (hw'd _)
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
          (hLd (2 * i + 1) (2 * i + 2) (by omega))
          (hLslack (2 * i + 1) (2 * i + 2) (by omega))
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
          (hLd (2 * j + 1) (2 * j + 2) (by omega))
          (hLslack (2 * j + 1) (2 * j + 2) (by omega))
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

/-- Fixed-guardian kill, slack form: no size relation between the
guardian and the covering threshold is needed. -/
theorem surviving_deletion_of_cofinal_fixedGuardian'
    {A : Set ℕ} {N₀ a c : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (ha0 : 0 < a)
    (hstream : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A a m)
    (hc : c ∈ A) (hc0 : 0 < c) (hca : c ≠ a)
    (hw : ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ a ∧ w' ≠ a) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  obtain ⟨w, hwA, w', hw'A, hww, hwc, hwa, hw'a⟩ := hw
  have hlev : ∀ K, ∃ M, K < M ∧ M ∈ A ∧
      ∀ z ∈ A, z ≠ a → z + N₀ < M → M - z ∈ A := by
    intro K
    obtain ⟨m, hm, hpriv⟩ := hstream (4 * K + 5 * N₀ + 21)
    have hMlow : ¬ (4 * (m - a) + 4 * N₀ + 20 ≤ m) :=
      fun h => hpriv.corep_lower h0 hcov ha0 h
    obtain ⟨M, hMA, hMe⟩ := hpriv.corep_mem h0 hcov ha0 (by omega)
    refine ⟨m - a, by omega, by
      have : M = m - a := by omega
      exact this ▸ hMA, ?_⟩
    intro z hz hza hzM
    obtain ⟨v, hvA, hvs⟩ :=
      hpriv.mirror_of_ne h0 hcov hz (by omega) (by omega) hza
    have hve : v = m - a - z := by omega
    exact hve ▸ hvA
  choose next hnext hnextMem hnextMir using hlev
  let L : ℕ → ℕ := fun k =>
    Nat.rec (next (c + N₀ + a)) (fun _ prev => next (2 * prev)) k
  have hL0 : L 0 = next (c + N₀ + a) := rfl
  have hLs : ∀ k, L (k + 1) = next (2 * L k) := fun _ => rfl
  have hgrow : ∀ k, 2 * L k < L (k + 1) := by
    intro k
    rw [hLs]
    exact hnext (2 * L k)
  have hcL : c + N₀ + a < L 0 := by rw [hL0]; exact hnext (c + N₀ + a)
  have hmono : StrictMono L := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 := hgrow k
    have h2 : 0 < L k := by
      induction k with
      | zero => omega
      | succ k ih => have := hgrow k; omega
    omega
  have hlevL : ∀ k, ∀ z ∈ A, z ≠ a → z + N₀ < L k → L k - z ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMir (c + N₀ + a)
    | succ k => rw [hLs]; exact hnextMir (2 * L k)
  have hmemL : ∀ k, L k ∈ A := by
    intro k
    cases k with
    | zero => exact hnextMem (c + N₀ + a)
    | succ k => rw [hLs]; exact hnextMem (2 * L k)
  exact surviving_deletion_of_geometric_rotatingDefects L (fun _ => a)
    h0 hcov hmono hlevL hmemL hgrow hc hc0 (by omega) hwA hw'A hww hwc
    (fun _ => hca) (fun _ => hwa) (fun _ => hw'a)
    (fun j k _ => by
      have h1 := hmono.monotone (Nat.zero_le j)
      show L j ≠ a
      omega)

/-- **The singleton stream dies.**  Any cofinal stream of positive
singleton guardians forces a surviving infinite deletion, provided
anchors dodging any prescribed value exist.  Either every finite
forbidden set is eventually dodged — and the rotating extraction runs,
each new level's guardian avoiding the anchor package and all lower
levels — or all late guardians live in one finite set, one of them
recurs cofinally, and the fixed kill fires. -/
theorem surviving_deletion_of_cofinal_privateStream
    {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  by_cases hro : ∀ (F : Finset ℕ) (N : ℕ), ∃ a m, N ≤ m ∧ 0 < a ∧
      a ∉ F ∧ IsPrivateTriple A a m
  · -- rotating case: every finite forbidden set is dodged
    obtain ⟨c, hc, hc0, -, w, hwA, w', hw'A, hww, hwc, -, -⟩ :=
      hanchor 0
    choose pa pm hpm hpa0 hpaF hppriv using hro
    set F₀ : Finset ℕ := {c, w, w'} with hF₀
    set nxt : ℕ × Finset ℕ → ℕ × Finset ℕ := fun s =>
      (pm s.2 (8 * s.1 + 9 * N₀ + 21) - pa s.2 (8 * s.1 + 9 * N₀ + 21),
        insert
          (pm s.2 (8 * s.1 + 9 * N₀ + 21) -
            pa s.2 (8 * s.1 + 9 * N₀ + 21)) s.2) with hnxt
    set prev : ℕ → ℕ × Finset ℕ := fun k =>
      Nat.rec (c + N₀, F₀) (fun _ p => nxt p) k with hprev
    set L : ℕ → ℕ := fun k => (prev (k + 1)).1 with hLdef
    set d : ℕ → ℕ := fun k =>
      pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) with hddef
    have hprevS : ∀ k, prev (k + 1) = nxt (prev k) := fun _ => rfl
    have hLeq : ∀ k, L k =
        pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
          pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by
      intro k
      simp only [hLdef, hprevS k, hnxt]
    have hFeq : ∀ k, (prev (k + 1)).2 = insert (L k) (prev k).2 := by
      intro k
      simp only [hLdef, hprevS k, hnxt]
    have hdeq : ∀ k, d k =
        pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by
      intro k
      simp only [hddef]
    -- per-step facts
    have hstep : ∀ k, d k ∉ (prev k).2 ∧ 0 < d k ∧ L k ∈ A ∧
        (prev k).1 < L k ∧ 2 * (prev k).1 + N₀ < L k ∧
        ∀ z ∈ A, z ≠ d k → z + N₀ < L k → L k - z ∈ A := by
      intro k
      have hpriv := hppriv (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have hm := hpm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have ha0 := hpa0 (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)
      have hlow : ¬ (4 * (pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
          pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)) +
            4 * N₀ + 20 ≤
          pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21)) :=
        fun h => hpriv.corep_lower h0 hcov ha0 h
      obtain ⟨M, hMA, hMe⟩ := hpriv.corep_mem h0 hcov ha0 (by omega)
      constructor
      · rw [hdeq]
        exact hpaF _ _
      refine ⟨by rw [hdeq]; exact ha0, ?_, ?_, ?_, ?_⟩
      · rw [hLeq]
        have hMeq : M = pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
            pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) := by omega
        exact hMeq ▸ hMA
      · rw [hLeq]; omega
      · rw [hLeq]; omega
      · intro z hz hza hzM
        rw [hLeq] at hzM ⊢
        rw [hdeq] at hza
        obtain ⟨v, hvA, hvs⟩ :=
          hpriv.mirror_of_ne h0 hcov hz (by omega) (by omega) hza
        have hve : v = pm (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) -
            pa (prev k).2 (8 * (prev k).1 + 9 * N₀ + 21) - z := by
          omega
        exact hve ▸ hvA
    -- state invariants
    have hF₀sub : ∀ k, F₀ ⊆ (prev k).2 := by
      intro k
      induction k with
      | zero =>
          have hp0 : prev 0 = (c + N₀, F₀) := rfl
          rw [hp0]
      | succ k ih =>
          rw [hFeq k]
          exact ih.trans (Finset.subset_insert _ _)
    have hLmem : ∀ j k, j < k → L j ∈ (prev k).2 := by
      intro j k hjk
      induction k with
      | zero => omega
      | succ k ih =>
          rw [hFeq k]
          rcases Nat.lt_or_ge j k with h | h
          · exact Finset.mem_insert_of_mem (ih h)
          · have hjeq : j = k := by omega
            subst hjeq
            exact Finset.mem_insert_self _ _
    have hprev1 : ∀ k, (prev (k + 1)).1 = L k := fun _ => rfl
    have hgrow : ∀ k, 2 * L k < L (k + 1) := by
      intro k
      have h1 := (hstep (k + 1)).2.2.2.2.1
      rw [hprev1] at h1
      omega
    have hcL : c + N₀ < L 0 := by
      have h1 := (hstep 0).2.2.2.2.1
      have h2 : (prev 0).1 = c + N₀ := rfl
      omega
    have hmono : StrictMono L := by
      apply strictMono_nat_of_lt_succ
      intro k
      have h1 := hgrow k
      have h2 := (hstep k).2.2.2.1
      omega
    have hcF : ∀ k, c ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    have hwF : ∀ k, w ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    have hw'F : ∀ k, w' ∈ (prev k).2 :=
      fun k => hF₀sub k (by simp [hF₀])
    exact surviving_deletion_of_geometric_rotatingDefects L d h0 hcov
      hmono (fun k => (hstep k).2.2.2.2.2) (fun k => (hstep k).2.2.1)
      hgrow hc hc0 hcL hwA hw'A hww hwc
      (fun k h => (hstep k).1 (h ▸ hcF k))
      (fun k h => (hstep k).1 (h ▸ hwF k))
      (fun k h => (hstep k).1 (h ▸ hw'F k))
      (fun j k hjk h => (hstep k).1 (h ▸ hLmem j k hjk))
  · -- recurring case: all late guardians in one finite set
    push Not at hro
    obtain ⟨F, N₁, hF⟩ := hro
    by_cases hrec : ∃ g ∈ F, 0 < g ∧
        ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A g m
    · obtain ⟨g, hgF, hg0, hgstream⟩ := hrec
      obtain ⟨c, hc, hc0, hcg, w, hwA, w', hw'A, hww, hwc, hwg, hw'g⟩ :=
        hanchor g
      exact surviving_deletion_of_cofinal_fixedGuardian' h0 hcov hg0
        hgstream hc hc0 hcg ⟨w, hwA, w', hw'A, hww, hwc, hwg, hw'g⟩
    · push Not at hrec
      have hbnd : ∀ g, ∃ Ng, ∀ m, Ng ≤ m → g ∈ F → 0 < g →
          ¬ IsPrivateTriple A g m := by
        intro g
        by_cases hgF : g ∈ F
        · by_cases hg0 : 0 < g
          · obtain ⟨Ng', hNg'⟩ := hrec g hgF hg0
            exact ⟨Ng', fun m hm _ _ => hNg' m hm⟩
          · exact ⟨0, fun m _ _ h0g => absurd h0g hg0⟩
        · exact ⟨0, fun m _ hgF' _ => absurd hgF' hgF⟩
      choose Ng hNg using hbnd
      obtain ⟨a, m, hm, ha0, hpriv⟩ :=
        hstream (max N₁ (F.sup Ng))
      have haF : a ∈ F := by
        by_contra haF
        exact hF a m (le_trans (le_max_left _ _) hm) ha0 haF hpriv
      have hbound : Ng a ≤ m :=
        le_trans (le_trans (Finset.le_sup haF) (le_max_right _ _)) hm
      exact absurd hpriv (hNg a m hbound haF ha0)

/-- **The master assembly, upgraded.**  Under the two open links
(cofinal pair funnels and team-clique-freeness) and anchor abundance,
a counterexample structure collapses entirely: either a surviving
infinite deletion exists outright — contradicting counterexamplehood —
or the zero element privately guards arbitrarily late targets, the
single degenerate residue left of the entire singleton-stream
branch. -/
theorem stream_killed_or_zero_guardian {A : Set ℕ} {N₀ : ℕ}
    (hA : A.Infinite) (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfunnel : HasCofinalPairFunnels A)
    (hclique : TeamCliqueFree A)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    (∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n) ∨
    (∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) := by
  obtain ⟨L, hLA, hLinf, hstream⟩ := master_reduction hA hfunnel hclique
  by_cases hz : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m
  · exact Or.inl
      (surviving_deletion_of_cofinal_privateStream h0 hcov hz hanchor)
  · push Not at hz
    obtain ⟨N₁, hN₁⟩ := hz
    refine Or.inr fun N => ?_
    obtain ⟨v, hvL, m, hm, hpriv⟩ := hstream (max N N₁)
    rcases Nat.eq_zero_or_pos v with hv0 | hv0
    · exact ⟨m, le_trans (le_max_left _ _) hm, hv0 ▸ hpriv⟩
    · exact absurd hpriv
        (hN₁ v m (le_trans (le_max_right _ _) hm) hv0)

end Erdos881
