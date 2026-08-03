import Erdos881.TeamGraphRamsey
import Erdos881.InfiniteRamsey
import Erdos881.AdditiveSupports
import Erdos881.RotatingGuardianEndgame
import Erdos881.FunnelTrichotomy
import Erdos881.MirrorPeriodicity
import Erdos881.LevelHubs

namespace Erdos881

/-- `K` pairwise-disjoint exact 3-representations of `n` over `A`:
a matrix of parts, rows are representations, no value shared between
distinct rows. -/
def HasDisjointTripleReps (A : Set ℕ) (n K : ℕ) : Prop :=
  ∃ P : Fin K → Fin 3 → ℕ,
    (∀ i k, P i k ∈ A) ∧
    (∀ i, P i 0 + P i 1 + P i 2 = n) ∧
    (∀ i j k l, i ≠ j → P i k ≠ P j l)

/-- Covering sets are unbounded. -/
lemma pairCovers_unbounded {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ X, ∃ a ∈ A, X ≤ a := by
  intro X
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov (N₀ + 2 * X) (by omega)
  rcases Nat.le_total x y with h | h
  · exact ⟨y, hy, by omega⟩
  · exact ⟨x, hx, by omega⟩

theorem surviving_deletion_of_disjointReps {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hdis : ∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointTripleReps A n K) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n := by
  classical
  -- monotone strengthened thresholds
  choose N hN using hdis
  set Nt : ℕ → ℕ := fun K =>
    Nat.rec (N 0 + 1) (fun k prev => max (N (k + 1)) prev + 1) K with hNt
  have hNtS : ∀ k, Nt (k + 1) = max (N (k + 1)) (Nt k) + 1 :=
    fun _ => rfl
  have hNtmono : ∀ k, Nt k < Nt (k + 1) := by
    intro k
    rw [hNtS k]
    have := Nat.le_max_right (N (k + 1)) (Nt k)
    omega
  have hNtge : ∀ k, N k ≤ Nt k := by
    intro k
    cases k with
    | zero => simp [hNt]
    | succ k =>
      rw [hNtS k]
      have := Nat.le_max_left (N (k + 1)) (Nt k)
      omega
  have hNtincr : ∀ j k, j ≤ k → Nt j ≤ Nt k := by
    intro j k hjk
    induction k with
    | zero =>
      have hj0 : j = 0 := by omega
      subst hj0
      omega
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · have h1 := ih (by omega)
        have h2 := hNtmono k
        omega
      · have hjk1 : j = k + 1 := by omega
        subst hjk1
        omega
  -- the slow spread markers
  have hchoice : ∀ X : ℕ, ∃ a, a ∈ A ∧ X ≤ a := by
    intro X
    obtain ⟨a, ha, hX⟩ := pairCovers_unbounded hcov X
    exact ⟨a, ha, hX⟩
  choose f hfA hfge using hchoice
  set b : ℕ → ℕ := fun k =>
    Nat.rec (f (Nt 2)) (fun k prev => f (max (Nt (k + 3)) (prev + 1))) k
    with hbdef
  have hbS : ∀ k, b (k + 1) = f (max (Nt (k + 3)) (b k + 1)) :=
    fun _ => rfl
  have hbA : ∀ k, b k ∈ A := by
    intro k
    cases k with
    | zero => exact hfA (Nt 2)
    | succ k =>
      rw [hbS k]
      exact hfA _
  have hbge : ∀ k, Nt (k + 2) ≤ b k := by
    intro k
    cases k with
    | zero => exact hfge (Nt 2)
    | succ k =>
      show Nt (k + 3) ≤ b (k + 1)
      rw [hbS k]
      have h1 := hfge (max (Nt (k + 3)) (b k + 1))
      have h2 := Nat.le_max_left (Nt (k + 3)) (b k + 1)
      omega
  have hbmono : ∀ k, b k < b (k + 1) := by
    intro k
    rw [hbS k]
    have h1 := hfge (max (Nt (k + 3)) (b k + 1))
    have h2 := Nat.le_max_right (Nt (k + 3)) (b k + 1)
    omega
  have hbstrict : StrictMono b := strictMono_nat_of_lt_succ hbmono
  refine ⟨Set.range b, ?_, ?_, Nt 2, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact hbA k
  · apply Set.infinite_of_injective_forall_mem
      (f := b) hbstrict.injective
    intro k
    exact ⟨k, rfl⟩
  · intro n hn
    -- K := number of markers at or below n
    have hexceed : ∃ j, n < b j := by
      refine ⟨n + 1, ?_⟩
      have h1 : Nt (n + 3) ≤ b (n + 1) := hbge (n + 1)
      have h2 : n + 3 ≤ Nt (n + 3) := by
        have h3 : ∀ m, m ≤ Nt m := by
          intro m
          induction m with
          | zero => omega
          | succ m ih =>
            have := hNtmono m
            omega
        exact h3 (n + 3)
      omega
    set K := Nat.find hexceed with hK
    have hKspec : n < b K := Nat.find_spec hexceed
    have hKmin : ∀ j, j < K → b j ≤ n := by
      intro j hj
      have := Nat.find_min hexceed hj
      omega
    -- n admits K + 1 disjoint representations
    have hnN : N (K + 1) ≤ n := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · rw [hK0]
        show N 1 ≤ n
        have h1 := hNtge 1
        have h2 := hNtincr 1 2 (by omega)
        omega
      · have h1 := hKmin (K - 1) (by omega)
        have h2 := hbge (K - 1)
        have h3 : K - 1 + 2 = K + 1 := by omega
        rw [h3] at h2
        have h4 := hNtge (K + 1)
        omega
    obtain ⟨P, hPA, hPsum, hPdisj⟩ := hN (K + 1) n hnN
    -- some representation avoids the markers, else pigeonhole
    by_contra hall
    push Not at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, P i k = b j := by
      intro i
      have h0 := hPA i 0
      have h1 := hPA i 1
      have h2 := hPA i 2
      have hs := hPsum i
      by_contra hnone
      push Not at hnone
      -- then this representation avoids B entirely
      have hfree : ∀ k, P i k ∉ Set.range b := by
        intro k
        rintro ⟨j, hj⟩
        have hj' : b j = P i k := hj
        have hle : P i k ≤ n := by
          have hs := hPsum i
          match k with
          | 0 => omega
          | 1 => omega
          | 2 => omega
        have hjK : j < K := by
          by_contra hge
          have h3 : b K ≤ b j := hbstrict.monotone (by omega)
          omega
        exact hnone j hjK k hj'.symm
      exact absurd (hPsum i)
        (hall (P i 0) h0 (P i 1) h1 (P i 2) h2
          (hfree 0) (hfree 1) (hfree 2))
    -- extract the marker index per representation; injective by disjointness
    choose g hgK hghit using hhit
    have hginj : Function.Injective g := by
      intro i i' hgii
      by_contra hne
      obtain ⟨k, hk⟩ := hghit i
      obtain ⟨k', hk'⟩ := hghit i'
      have : P i k = P i' k' := by rw [hk, hgii, hk']
      exact hPdisj i i' k k' hne this
    -- Fin (K+1) injects into Fin K: contradiction
    have hcard : K + 1 ≤ K := by
      have hmaps : ∀ i : Fin (K + 1), g i < K := hgK
      let g' : Fin (K + 1) → Fin K := fun i => ⟨g i, hmaps i⟩
      have hg'inj : Function.Injective g' := by
        intro i i' h
        apply hginj
        have := congrArg Fin.val h
        simpa using this
      have := Fintype.card_le_of_injective g' hg'inj
      simpa using this
    omega

/-- A support transversal set for `n`: a finite set of values meeting every exact
3-representation of `n` over `A`. -/
def IsRepSupportTransversal (A : Set ℕ) (n : ℕ) (H : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
    x ∈ H ∨ y ∈ H ∨ z ∈ H

theorem support_transversal_of_no_disjointReps {A : Set ℕ} {n K : ℕ}
    (hno : ¬HasDisjointTripleReps A n K) :
    ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧ IsRepSupportTransversal A n H := by
  classical
  have h0 : HasDisjointTripleReps A n 0 :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  -- boundary crossing: a maximal achievable family size J < K
  have hcross : ∃ J, J < K ∧ HasDisjointTripleReps A n J ∧
      ¬HasDisjointTripleReps A n (J + 1) := by
    by_contra hnc
    push Not at hnc
    have hall : ∀ J, J ≤ K → HasDisjointTripleReps A n J := by
      intro J hJ
      induction J with
      | zero => exact h0
      | succ J ih => exact hnc J (by omega) (ih (by omega))
    exact hno (hall K (le_refl K))
  obtain ⟨J, hJK, ⟨P, hPA, hPsum, hPdisj⟩, hJmax⟩ := hcross
  refine ⟨(Finset.univ : Finset (Fin J × Fin 3)).image
    (fun p => P p.1 p.2), ?_, ?_⟩
  · calc ((Finset.univ : Finset (Fin J × Fin 3)).image
        (fun p => P p.1 p.2)).card
        ≤ (Finset.univ : Finset (Fin J × Fin 3)).card :=
          Finset.card_image_le
      _ = 3 * J := by simp [Finset.card_univ, Nat.mul_comm]
      _ ≤ 3 * (K - 1) := by omega
  · intro x hx y hy z hz hsum
    by_contra hnot
    push Not at hnot
    obtain ⟨hxH, hyH, hzH⟩ := hnot
    have hmem : ∀ i k, P i k ∈ (Finset.univ :
        Finset (Fin J × Fin 3)).image (fun p => P p.1 p.2) := by
      intro i k
      exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩
    set R : Fin 3 → ℕ := ![x, y, z] with hR
    have hRA : ∀ k, R k ∈ A := by
      intro k
      match k with
      | 0 => exact hx
      | 1 => exact hy
      | 2 => exact hz
    have hRH : ∀ k, R k ∉ (Finset.univ :
        Finset (Fin J × Fin 3)).image (fun p => P p.1 p.2) := by
      intro k
      match k with
      | 0 => exact hxH
      | 1 => exact hyH
      | 2 => exact hzH
    have hRsum : R 0 + R 1 + R 2 = n := hsum
    -- extend the maximal family: contradiction
    refine hJmax ⟨fun i k =>
      if h : (i : ℕ) < J then P ⟨i, h⟩ k else R k, ?_, ?_, ?_⟩
    · intro i k
      by_cases h : (i : ℕ) < J
      · simpa [h] using hPA ⟨i, h⟩ k
      · simpa [h] using hRA k
    · intro i
      by_cases h : (i : ℕ) < J
      · simpa [h] using hPsum ⟨i, h⟩
      · simpa [h] using hRsum
    · intro i j k l hij
      by_cases hi : (i : ℕ) < J
      · by_cases hj : (j : ℕ) < J
        · have hne : (⟨(i : ℕ), hi⟩ : Fin J) ≠ ⟨(j : ℕ), hj⟩ := by
            intro h
            apply hij
            have := congrArg Fin.val h
            exact Fin.ext (by simpa using this)
          simpa [hi, hj] using hPdisj ⟨i, hi⟩ ⟨j, hj⟩ k l hne
        · simp only [dif_pos hi, dif_neg hj]
          intro h
          exact hRH l (h ▸ hmem ⟨i, hi⟩ k)
      · by_cases hj : (j : ℕ) < J
        · simp only [dif_neg hi, dif_pos hj]
          intro h
          exact hRH k (h.symm ▸ hmem ⟨j, hj⟩ l)
        · exfalso
          apply hij
          have hiJ : (i : ℕ) = J := by
            have := i.isLt
            omega
          have hjJ : (j : ℕ) = J := by
            have := j.isLt
            omega
          exact Fin.ext (by omega)

theorem cofinal_bounded_support_transversals_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧ IsRepSupportTransversal A n H := by
  classical
  have hnodis : ¬∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointTripleReps A n K := by
    intro hdis
    obtain ⟨B, hBsub, hBinf, N₁, hN₁⟩ :=
      surviving_deletion_of_disjointReps hcov hdis
    refine hfail B hBsub hBinf ⟨N₁, fun n hn => ?_⟩
    obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := hN₁ n hn
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro i
      match i with
      | 0 => exact ⟨hx, hxB⟩
      | 1 => exact ⟨hy, hyB⟩
      | 2 => exact ⟨hz, hzB⟩
    · simpa [Fin.sum_univ_three] using hsum
  push Not at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := support_transversal_of_no_disjointReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

theorem support_transversal_dichotomy {A : Set ℕ} {C : ℕ}
    (hhub : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H)
    (W : ℕ) :
    (∃ h, h ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepSupportTransversal A n H ∧ h ∈ H) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
      ∀ h ∈ H, W < h) := by
  classical
  by_cases hmeet : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepSupportTransversal A n H ∧ ∃ h ∈ H, h ≤ W
  · left
    by_contra hnoper
    push Not at hnoper
    have hex : ∀ h, ∃ Nh, h ≤ W → ∀ n, Nh ≤ n →
        ∀ H : Finset ℕ, H.card ≤ C → IsRepSupportTransversal A n H → h ∉ H := by
      intro h
      by_cases hh : h ≤ W
      · obtain ⟨N, hN⟩ := hnoper h hh
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h' => absurd h' hh⟩
    choose g hg using hex
    obtain ⟨n, hn, H, hcard, hhubH, h₀, hh₀H, hh₀W⟩ :=
      hmeet ((Finset.range (W + 1)).sup g)
    have hgle : g h₀ ≤ (Finset.range (W + 1)).sup g :=
      Finset.le_sup (Finset.mem_range.2 (by omega))
    exact hg h₀ hh₀W n (by omega) H hcard hhubH hh₀H
  · right
    push Not at hmeet
    obtain ⟨N₀, hN₀⟩ := hmeet
    intro N
    obtain ⟨n, hn, H, hcard, hhubH⟩ := hhub (max N N₀)
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hcard, hhubH, ?_⟩
    intro h hh
    have := hN₀ n (le_trans (le_max_right _ _) hn) H hcard hhubH h hh
    omega

/-- Predicate-generalized cofinal dichotomy: any cofinal family of
finite witness sets either has a persistent element in the window or
cofinally avoids the window. -/
theorem cofinal_dichotomy (Q : ℕ → Finset ℕ → Prop)
    (hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H) (W : ℕ) :
    (∃ h, h ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H ∧ h ∈ H) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H ∧ ∀ h ∈ H, W < h) := by
  classical
  by_cases hmeet : ∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H ∧ ∃ h ∈ H, h ≤ W
  · left
    by_contra hnoper
    push Not at hnoper
    have hex : ∀ h, ∃ Nh, h ≤ W → ∀ n, Nh ≤ n →
        ∀ H, Q n H → h ∉ H := by
      intro h
      by_cases hh : h ≤ W
      · obtain ⟨N, hN⟩ := hnoper h hh
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h' => absurd h' hh⟩
    choose g hg using hex
    obtain ⟨n, hn, H, hQH, h₀, hh₀H, hh₀W⟩ :=
      hmeet ((Finset.range (W + 1)).sup g)
    have hgle : g h₀ ≤ (Finset.range (W + 1)).sup g :=
      Finset.le_sup (Finset.mem_range.2 (by omega))
    exact hg h₀ hh₀W n (by omega) H hQH hh₀H
  · right
    push Not at hmeet
    obtain ⟨N₀, hN₀⟩ := hmeet
    intro N
    obtain ⟨n, hn, H, hQH⟩ := hQ (max N N₀)
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hQH, ?_⟩
    intro h hh
    have := hN₀ n (le_trans (le_max_right _ _) hn) H hQH h hh
    omega

/-- Tower extraction, budget induction: from a cofinal family of support transversals
containing a core `S` with excess budget `d`, produce an enlarged core
`S'` splitting the support transversals at the window: everything outside `S'` is
large. -/
theorem support_transversal_window_split_aux {A : Set ℕ} {C : ℕ} (W : ℕ) :
    ∀ d S, S ⊆ Finset.range (W + 1) →
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
      S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S' ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
        S' ⊆ H ∧ ∀ h ∈ H, h ∉ S' → W < h := by
  classical
  intro d
  induction d with
  | zero =>
    intro S hSW hfam
    refine ⟨S, hSW, fun N => ?_⟩
    obtain ⟨n, hn, H, hcard, hhub, hSH, hbud⟩ := hfam N
    refine ⟨n, hn, H, hcard, hhub, hSH, fun h hhH hhS => ?_⟩
    exfalso
    have hHS : H = S := Finset.Subset.antisymm
      (by
        by_contra hns
        obtain ⟨x, hxH, hxS⟩ := Finset.not_subset.1 hns
        have h1 : S.card < H.card := by
          have h2 : S ⊂ H := Finset.ssubset_iff_of_subset hSH |>.2 ⟨x, hxH, hxS⟩
          exact Finset.card_lt_card h2
        omega) hSH
    rw [hHS] at hhH
    exact hhS hhH
  | succ d ih =>
    intro S hSW hfam
    rcases cofinal_dichotomy
      (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
        S ⊆ H ∧ H.card ≤ S.card + (d + 1) ∧ H' = H \ S)
      (fun N => by
        obtain ⟨n, hn, H, hcard, hhub, hSH, hbud⟩ := hfam N
        exact ⟨n, hn, H \ S, H, hcard, hhub, hSH, hbud, rfl⟩) W
      with ⟨h, hhW, hper⟩ | hlarge
    · -- persistent new element h ∉ S: grow the core
      refine ih (insert h S) ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.1 hx with hxh | hxS
        · exact Finset.mem_range.2 (by omega)
        · exact hSW hxS
      · intro N
        obtain ⟨n, hn, H', ⟨H, hcard, hhub, hSH, hbud, hH'⟩, hhH'⟩ :=
          hper N
        subst hH'
        have hhH : h ∈ H := (Finset.mem_sdiff.1 hhH').1
        have hhS : h ∉ S := (Finset.mem_sdiff.1 hhH').2
        refine ⟨n, hn, H, hcard, hhub, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with hxh | hxS
          · rw [hxh]; exact hhH
          · exact hSH hxS
        · have : (insert h S).card = S.card + 1 :=
            Finset.card_insert_of_notMem hhS
          omega
    · -- reduced support transversals cofinally avoid the window: done with core S
      refine ⟨S, hSW, fun N => ?_⟩
      obtain ⟨n, hn, H', ⟨H, hcard, hhub, hSH, hbud, hH'⟩, hlargeH⟩ :=
        hlarge N
      subst hH'
      refine ⟨n, hn, H, hcard, hhub, hSH, fun h hhH hhS => ?_⟩
      exact hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)

theorem support_transversal_window_split {A : Set ℕ} {C : ℕ}
    (hhub : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepSupportTransversal A n H) (W : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  refine support_transversal_window_split_aux W C ∅ (by simp) fun N => ?_
  obtain ⟨n, hn, H, hcard, hhub'⟩ := hhub N
  exact ⟨n, hn, H, hcard, hhub', Finset.empty_subset _, by simpa using hcard⟩

/-- With `0 ∈ A` and covering, late targets always have 3-reps, so
support transversals are nonempty. -/
theorem support_transversal_nonempty_of_covering {A : Set ℕ} {N₀ n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepSupportTransversal A n H) : H.Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact ⟨x, h⟩
  · exact ⟨y, h⟩
  · exact ⟨0, h⟩

/-- A singleton support transversal is exactly a private triple. -/
theorem privateTriple_of_singleton_support_transversal {A : Set ℕ} {N₀ n a : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepSupportTransversal A n {a}) : IsPrivateTriple A a n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  refine ⟨⟨x, hx, y, hy, 0, h0, by omega⟩, ?_⟩
  intro x' hx' y' hy' z' hz' hsum
  rcases hhub x' hx' y' hy' z' hz' hsum with h | h | h
  · exact Or.inl (Finset.mem_singleton.1 h)
  · exact Or.inr (Or.inl (Finset.mem_singleton.1 h))
  · exact Or.inr (Or.inr (Finset.mem_singleton.1 h))

def StreamSurvives (A : Set ℕ) (N₀ : ℕ) : Prop :=
  (∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m) →
    ∃ B ⊆ A, B.Infinite ∧ ∀ n, N₀ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
        x ∉ B ∧ y ∉ B ∧ z ∉ B ∧ x + y + z = n

/-- Anchored worlds implement the oracle. -/
theorem streamSurvives_of_anchor {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanc : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g) :
    StreamSurvives A N₀ :=
  fun hstream =>
    surviving_deletion_of_cofinal_privateStream h0 hcov hstream hanc

theorem singleton_support_transversals_refuted {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ¬(∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepSupportTransversal A n {a}) := by
  intro hsing
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_support_transversal h0 hcov
        (le_trans (le_max_right _ _) hn) hhub⟩
  obtain ⟨B, hBsub, hBinf, hsurv⟩ := hanchor hstream
  refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := hsurv n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · simpa [Fin.sum_univ_three] using hsum

theorem pair_transversal_configuration_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧
        IsRepSupportTransversal A n H ∧ S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  obtain ⟨K, hK⟩ := cofinal_bounded_support_transversals_of_hfail hcov hfail
  refine ⟨K, fun W => ?_⟩
  exact support_transversal_window_split (fun N => hK N) W

theorem support_transversal_card_ge_two_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ N, ∀ n, N ≤ n → ∀ H : Finset ℕ, IsRepSupportTransversal A n H → 2 ≤ H.card := by
  classical
  have hzero := not_zero_residue_of_doubling hcov hdb
  push Not at hzero
  obtain ⟨Nz, hNz⟩ := hzero
  have hpos := singleton_support_transversals_refuted h0 hcov hanchor hfail
  push Not at hpos
  obtain ⟨Np, hNp⟩ := hpos
  refine ⟨max N₀ (max Nz Np), fun n hn H hhub => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnz : Nz ≤ n := le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) hn
  have hnp : Np ≤ n := le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hn
  by_contra hlt
  push Not at hlt
  interval_cases hc : H.card
  · obtain ⟨x, hx⟩ := support_transversal_nonempty_of_covering h0 hcov hn₀ hhub
    have := Finset.card_pos.2 ⟨x, hx⟩
    omega
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      exact hNz n hnz (privateTriple_of_singleton_support_transversal h0 hcov hn₀ hhub)
    · exact hNp n hnp a hapos hhub

/-- An exact-pair support transversal is a pair destroyer. -/
theorem pairDestroyer_of_pair_support_transversal {A : Set ℕ} {N₀ n u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepSupportTransversal A n {u, v}) : IsPairDestroyer A u v n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  refine ⟨⟨x, hx, y, hy, 0, h0, by omega⟩, ?_⟩
  have hmem : ∀ w, w ∈ ({u, v} : Finset ℕ) → w = u ∨ w = v := by
    intro w hw
    rcases Finset.mem_insert.1 hw with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Finset.mem_singleton.1 h')
  intro x' hx' y' hy' z' hz' hsum
  rcases hhub x' hx' y' hy' z' hz' hsum with h | h | h <;>
    rcases hmem _ h with h' | h' <;> tauto

/-- Every support transversal contains a minimal support transversal. -/
theorem exists_minimal_support_transversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H) :
    ∃ H' ⊆ H, IsRepSupportTransversal A n H' ∧
      ∀ h ∈ H', ¬IsRepSupportTransversal A n (H' \ {h}) := by
  classical
  revert hhub
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro hhub
    by_cases hmin : ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})
    · exact ⟨H, Finset.Subset.refl H, hhub, hmin⟩
    · push Not at hmin
      obtain ⟨h, hhH, hsub⟩ := hmin
      have hss : H \ {h} ⊂ H :=
        Finset.sdiff_ssubset (Finset.singleton_subset_iff.2 hhH)
          (Finset.singleton_nonempty h)
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := ih (H \ {h}) hss hsub
      exact ⟨H', Finset.Subset.trans hH'sub Finset.sdiff_subset,
        hH'hub, hH'min⟩

theorem minimal_support_transversal_necessity {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H)
    (hmin : ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) :
    ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
      (x = h ∨ y = h ∨ z = h) ∧
      (∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) := by
  intro h hhH
  have hnot := hmin h hhH
  rw [IsRepSupportTransversal] at hnot
  push Not at hnot
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxH, hyH, hzH⟩ := hnot
  have hcx : x ∈ H → x = h := by
    intro hxH'
    by_contra hne
    exact hxH (Finset.mem_sdiff.2 ⟨hxH', Finset.notMem_singleton.2 hne⟩)
  have hcy : y ∈ H → y = h := by
    intro hyH'
    by_contra hne
    exact hyH (Finset.mem_sdiff.2 ⟨hyH', Finset.notMem_singleton.2 hne⟩)
  have hcz : z ∈ H → z = h := by
    intro hzH'
    by_contra hne
    exact hzH (Finset.mem_sdiff.2 ⟨hzH', Finset.notMem_singleton.2 hne⟩)
  refine ⟨x, hx, y, hy, z, hz, hsum, ?_, ?_⟩
  · rcases hhub x hx y hy z hz hsum with hw | hw | hw
    · exact Or.inl (hcx hw)
    · exact Or.inr (Or.inl (hcy hw))
    · exact Or.inr (Or.inr (hcz hw))
  · refine fun g hgH hgh => ⟨fun hxg => hgh ?_, fun hyg => hgh ?_,
      fun hzg => hgh ?_⟩
    · have := hcx (hxg ▸ hgH)
      omega
    · have := hcy (hyg ▸ hgH)
      omega
    · have := hcz (hzg ▸ hgH)
      omega

theorem recurring_pair_of_bounded_pair_support_transversals {A : Set ℕ} {W : ℕ}
    (hpairs : ∀ N, ∃ n, N ≤ n ∧ ∃ u v, u ≤ W ∧ v ≤ W ∧
      IsRepSupportTransversal A n {u, v}) :
    ∃ u v, u ≤ W ∧ v ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧ IsRepSupportTransversal A n {u, v} := by
  classical
  by_contra hno
  push Not at hno
  have hex : ∀ u v, ∃ Nuv, u ≤ W → v ≤ W → ∀ n, Nuv ≤ n →
      ¬IsRepSupportTransversal A n {u, v} := by
    intro u v
    by_cases hu : u ≤ W
    · by_cases hv : v ≤ W
      · obtain ⟨N, hN⟩ := hno u v hu hv
        exact ⟨N, fun _ _ => hN⟩
      · exact ⟨0, fun _ h => absurd h hv⟩
    · exact ⟨0, fun h => absurd h hu⟩
  choose g hg using hex
  set NS := (Finset.range (W + 1)).sup fun u =>
    (Finset.range (W + 1)).sup (g u) with hNS
  obtain ⟨n, hn, u, v, hu, hv, hhub⟩ := hpairs NS
  have h2 : g u v ≤ (Finset.range (W + 1)).sup (g u) :=
    Finset.le_sup (b := v) (Finset.mem_range.2 (by omega : v < W + 1))
  have h3 : (Finset.range (W + 1)).sup (g u) ≤ NS := by
    rw [hNS]
    exact Finset.le_sup (f := fun x => (Finset.range (W + 1)).sup (g x))
      (b := u) (Finset.mem_range.2 (by omega : u < W + 1))
  exact hg u v hu hv n (le_trans (le_trans h2 h3) hn) hhub

theorem pipeline_entry_of_bounded_pair_support_transversals {A : Set ℕ} {N₀ W : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpairs : ∀ N, ∃ n, N ≤ n ∧ ∃ u v, u ≤ W ∧ v ≤ W ∧
      IsRepSupportTransversal A n {u, v}) :
    ∃ u v, ∀ N, ∃ n, N ≤ n ∧ IsPairDestroyer A u v n := by
  obtain ⟨u, v, _, _, hrec⟩ := recurring_pair_of_bounded_pair_support_transversals hpairs
  refine ⟨u, v, fun N => ?_⟩
  obtain ⟨n, hn, hhub⟩ := hrec (max N N₀)
  exact ⟨n, le_trans (le_max_left _ _) hn,
    pairDestroyer_of_pair_support_transversal h0 hcov (le_trans (le_max_right _ _) hn) hhub⟩

/-- Side-predicate tower: the window split carries any extra property
`R` of the support transversal family through unchanged. -/
theorem support_transversal_window_split_aux' {A : Set ℕ} {C : ℕ}
    (R : ℕ → Finset ℕ → Prop) (W : ℕ) :
    ∀ d S, S ⊆ Finset.range (W + 1) →
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
      R n H ∧ S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S' ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
        R n H ∧ S' ⊆ H ∧ ∀ h ∈ H, h ∉ S' → W < h := by
  classical
  intro d
  induction d with
  | zero =>
    intro S hSW hfam
    refine ⟨S, hSW, fun N => ?_⟩
    obtain ⟨n, hn, H, hcard, hhub, hR, hSH, hbud⟩ := hfam N
    refine ⟨n, hn, H, hcard, hhub, hR, hSH, fun h hhH hhS => ?_⟩
    exfalso
    have hHS : H = S := Finset.Subset.antisymm
      (by
        by_contra hns
        obtain ⟨x, hxH, hxS⟩ := Finset.not_subset.1 hns
        have h1 : S.card < H.card := Finset.card_lt_card
          (Finset.ssubset_iff_of_subset hSH |>.2 ⟨x, hxH, hxS⟩)
        omega) hSH
    rw [hHS] at hhH
    exact hhS hhH
  | succ d ih =>
    intro S hSW hfam
    rcases cofinal_dichotomy
      (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
        R n H ∧ S ⊆ H ∧ H.card ≤ S.card + (d + 1) ∧ H' = H \ S)
      (fun N => by
        obtain ⟨n, hn, H, hcard, hhub, hR, hSH, hbud⟩ := hfam N
        exact ⟨n, hn, H \ S, H, hcard, hhub, hR, hSH, hbud, rfl⟩) W
      with ⟨h, hhW, hper⟩ | hlarge
    · refine ih (insert h S) ?_ ?_
      · intro x hx
        rcases Finset.mem_insert.1 hx with hxh | hxS
        · exact Finset.mem_range.2 (by omega)
        · exact hSW hxS
      · intro N
        obtain ⟨n, hn, H', ⟨H, hcard, hhub, hR, hSH, hbud, hH'⟩, hhH'⟩ :=
          hper N
        subst hH'
        have hhH : h ∈ H := (Finset.mem_sdiff.1 hhH').1
        have hhS : h ∉ S := (Finset.mem_sdiff.1 hhH').2
        refine ⟨n, hn, H, hcard, hhub, hR, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.1 hx with hxh | hxS
          · rw [hxh]; exact hhH
          · exact hSH hxS
        · have : (insert h S).card = S.card + 1 :=
            Finset.card_insert_of_notMem hhS
          omega
    · refine ⟨S, hSW, fun N => ?_⟩
      obtain ⟨n, hn, H', ⟨H, hcard, hhub, hR, hSH, hbud, hH'⟩, hlargeH⟩ :=
        hlarge N
      subst hH'
      refine ⟨n, hn, H, hcard, hhub, hR, hSH, fun h hhH hhS => ?_⟩
      exact hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)

theorem pair_transversal_configuration_minimal_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧
        IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_support_transversals_of_hfail hcov hfail
  refine ⟨K, fun W => ?_⟩
  refine support_transversal_window_split_aux'
    (R := fun n H => ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) W
    (3 * (K - 1)) ∅ (by simp) fun N => ?_
  obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
  exact ⟨n, hn, H', le_trans (Finset.card_le_card hH'sub) hcard,
    hH'hub, hH'min, Finset.empty_subset _,
    by simpa using le_trans (Finset.card_le_card hH'sub) hcard⟩

/-- Stable-core descent: either the current core already splits at
every window, or some window forces the core to grow — and growth is
budget-bounded. -/
theorem stable_core_aux {A : Set ℕ} {C : ℕ}
    (R : ℕ → Finset ℕ → Prop) :
    ∀ d S,
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
      R n H ∧ S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S ⊆ S' ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        IsRepSupportTransversal A n H ∧ R n H ∧ S' ⊆ H ∧
        ∀ h ∈ H, h ∉ S' → W < h := by
  classical
  intro d
  induction d with
  | zero =>
    intro S hfam
    refine ⟨S, Finset.Subset.refl S, fun W N => ?_⟩
    obtain ⟨n, hn, H, hcard, hhub, hR, hSH, hbud⟩ := hfam N
    refine ⟨n, hn, H, hcard, hhub, hR, hSH, fun h hhH hhS => ?_⟩
    exfalso
    have hHS : H = S := Finset.Subset.antisymm
      (by
        by_contra hns
        obtain ⟨x, hxH, hxS⟩ := Finset.not_subset.1 hns
        have h1 : S.card < H.card := Finset.card_lt_card
          (Finset.ssubset_iff_of_subset hSH |>.2 ⟨x, hxH, hxS⟩)
        omega) hSH
    rw [hHS] at hhH
    exact hhS hhH
  | succ d ih =>
    intro S hfam
    by_cases hstable : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card ≤ C ∧ IsRepSupportTransversal A n H ∧ R n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h
    · exact ⟨S, Finset.Subset.refl S, hstable⟩
    · push Not at hstable
      obtain ⟨W₁, N₁, hW₁⟩ := hstable
      rcases cofinal_dichotomy
        (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepSupportTransversal A n H ∧
          R n H ∧ S ⊆ H ∧ H.card ≤ S.card + (d + 1) ∧ H' = H \ S)
        (fun N => by
          obtain ⟨n, hn, H, hcard, hhub, hR, hSH, hbud⟩ := hfam N
          exact ⟨n, hn, H \ S, H, hcard, hhub, hR, hSH, hbud, rfl⟩) W₁
        with ⟨h, hhW, hper⟩ | hlarge
      · -- growth at W₁
        obtain ⟨S', hS'sub, hS'split⟩ := ih (insert h S) (fun N => by
          obtain ⟨n, hn, H', ⟨H, hcard, hhub, hR, hSH, hbud, hH'⟩, hhH'⟩ :=
            hper N
          subst hH'
          have hhH : h ∈ H := (Finset.mem_sdiff.1 hhH').1
          have hhS : h ∉ S := (Finset.mem_sdiff.1 hhH').2
          refine ⟨n, hn, H, hcard, hhub, hR, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with hxh | hxS
            · rw [hxh]; exact hhH
            · exact hSH hxS
          · have : (insert h S).card = S.card + 1 :=
              Finset.card_insert_of_notMem hhS
            omega)
        exact ⟨S', Finset.Subset.trans (Finset.subset_insert h S) hS'sub,
          hS'split⟩
      · -- The second alternative contradicts the failing window.
        exfalso
        obtain ⟨n, hn, H', ⟨H, hcard, hhub, hR, hSH, hbud, hH'⟩, hlargeH⟩ :=
          hlarge N₁
        subst hH'
        obtain ⟨h, hhH, hhS, hhW⟩ := hW₁ n hn H hcard hhub hR hSH
        have := hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)
        omega

theorem stable_core_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_support_transversals_of_hfail hcov hfail
  obtain ⟨S, -, hsplit⟩ := stable_core_aux
    (A := A) (C := 3 * (K - 1))
    (R := fun n H => ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}))
    (3 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
      exact ⟨n, hn, H', le_trans (Finset.card_le_card hH'sub) hcard,
        hH'hub, hH'min, Finset.empty_subset _,
        by simpa using le_trans (Finset.card_le_card hH'sub) hcard⟩)
  exact ⟨K, S, hsplit⟩

theorem two_rep_shadow_of_large_support_transversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hhub : IsRepSupportTransversal A n H) (hlarge : ∀ h ∈ H, 0 < h) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hlarge 0 h) (by omega)

theorem large_pair_transversal_shadow_of_empty_core {A : Set ℕ} {N₀ K : ℕ}
    (h0 : 0 ∈ A)
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      (∅ : Finset ℕ) ⊆ H ∧ ∀ h ∈ H, h ∉ (∅ : Finset ℕ) → W < h) :
    ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ (∀ h ∈ H, W < h) ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H) ∧
      IsRepSupportTransversal A n H := by
  intro W N
  obtain ⟨n, hn, H, hcard, hhub, hmin, -, hrest⟩ := hsplit W N
  have hlargeW : ∀ h ∈ H, W < h := fun h hh =>
    hrest h hh (Finset.notMem_empty h)
  refine ⟨n, hn, H, hcard, hlargeW, ?_, hhub⟩
  exact two_rep_shadow_of_large_support_transversal h0 hhub
    (fun h hh => by have := hlargeW h hh; omega)

/-- Cofinal pigeonhole over a bounded value: some value recurs
cofinally. -/
theorem cofinal_value_pigeonhole {C : ℕ} (P : ℕ → ℕ → Prop)
    (hP : ∀ N, ∃ n, N ≤ n ∧ ∃ c, c ≤ C ∧ P n c) :
    ∃ c, c ≤ C ∧ ∀ N, ∃ n, N ≤ n ∧ P n c := by
  classical
  by_contra hno
  push Not at hno
  have hex : ∀ c, ∃ Nc, c ≤ C → ∀ n, Nc ≤ n → ¬P n c := by
    intro c
    by_cases hc : c ≤ C
    · obtain ⟨N, hN⟩ := hno c hc
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose g hg using hex
  set NS := (Finset.range (C + 1)).sup g with hNS
  obtain ⟨n, hn, c, hc, hPc⟩ := hP NS
  have h2 : g c ≤ NS := by
    rw [hNS]
    exact Finset.le_sup (Finset.mem_range.2 (by omega))
  exact hg c hc n (by omega) hPc

theorem stable_core_card_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K S c, c ≤ 3 * (K - 1) ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, S, hsplit⟩ := stable_core_of_hfail hcov hfail
  -- the set of cards recurring cofinally at window W
  set Good : ℕ → ℕ → Prop := fun W c =>
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card = c ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h with hGood
  have hdown : ∀ W W' c, W ≤ W' → Good W' c → Good W c := by
    intro W W' c hWW' hg N
    obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hg N
    exact ⟨n, hn, H, hcard, hhub, hmin, hSH,
      fun h hh hhS => by have := hrest h hh hhS; omega⟩
  have hperW : ∀ W, ∃ c, c ≤ 3 * (K - 1) ∧ Good W c := by
    intro W
    have hP : ∀ N, ∃ n, N ≤ n ∧ ∃ c, c ≤ 3 * (K - 1) ∧
        (∃ H : Finset ℕ, H.card = c ∧ IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) := by
      intro N
      obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit W N
      exact ⟨n, hn, H.card, hcard, H, rfl, hhub, hmin, hSH, hrest⟩
    obtain ⟨c, hc, hcof⟩ := cofinal_value_pigeonhole
      (P := fun n c => ∃ H : Finset ℕ, H.card = c ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) hP
    exact ⟨c, hc, hcof⟩
  -- pigeonhole the card across windows; downward closure finishes
  by_contra hno
  push Not at hno
  have hex : ∀ c, ∃ Wc, c ≤ 3 * (K - 1) → ¬Good Wc c := by
    intro c
    by_cases hc : c ≤ 3 * (K - 1)
    · obtain ⟨W, hW⟩ := hno K S c hc
      refine ⟨W, fun _ => ?_⟩
      intro hgood
      obtain ⟨N, hN⟩ := hW
      obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hgood N
      obtain ⟨h, hh, hhS, hhW⟩ := hN n hn H hcard hhub hmin hSH
      have := hrest h hh hhS
      omega
    · exact ⟨0, fun h => absurd h hc⟩
  choose gW hgW using hex
  set WS := (Finset.range (3 * (K - 1) + 1)).sup gW with hWS
  obtain ⟨c, hc, hgood⟩ := hperW WS
  have h2 : gW c ≤ WS := by
    rw [hWS]
    exact Finset.le_sup (Finset.mem_range.2 (by omega))
  exact hgW c hc (hdown (gW c) WS c h2 hgood)

/-- Tight core: when the canonical cardinality equals the core size,
the support transversals ARE the core — one fixed finite pair transversal hits every 3-rep of
cofinally many targets. -/
theorem recurring_pair_transversal_of_tight_core {A : Set ℕ} {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hceq : c = S.card) :
    ∀ N, ∃ n, N ≤ n ∧ IsRepSupportTransversal A n S := by
  intro N
  obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit 0 N
  have hHS : S = H := Finset.eq_of_subset_of_card_le hSH (by omega)
  rw [← hHS] at hhub
  exact ⟨n, hn, hhub⟩

theorem support_transversal_counterexample_structure_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K S c, c ≤ 3 * (K - 1) ∧ 2 ≤ c ∧ S.card ≤ c ∧
      (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) ∧
      (c = S.card → ∀ N, ∃ n, N ≤ n ∧ IsRepSupportTransversal A n S) := by
  obtain ⟨K, S, c, hcK, hsplit⟩ := stable_core_card_of_hfail hcov hfail
  obtain ⟨N₂, hN₂⟩ := support_transversal_card_ge_two_of_hfail h0 hcov hdb hanchor hfail
  obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit 0 N₂
  have hc2 : 2 ≤ c := by
    have := hN₂ n hn H hhub
    omega
  have hSc : S.card ≤ c := by
    have := Finset.card_le_card hSH
    omega
  exact ⟨K, S, c, hcK, hc2, hSc, hsplit,
    fun hceq => recurring_pair_transversal_of_tight_core hsplit hceq⟩

/-- The tight-pair leaf, explicit: a tight core of size two hands the
fixed-pair pipeline its recurring destroyer pair. -/
theorem pipeline_entry_of_tight_pair {A : Set ℕ} {N₀ : ℕ} {S : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hteam : ∀ N, ∃ n, N ≤ n ∧ IsRepSupportTransversal A n S)
    (hS2 : S.card = 2) :
    ∃ u v, u ≠ v ∧ ∀ N, ∃ n, N ≤ n ∧ IsPairDestroyer A u v n := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 hS2
  refine ⟨u, v, huv, fun N => ?_⟩
  obtain ⟨n, hn, hhub⟩ := hteam (max N N₀)
  exact ⟨n, le_trans (le_max_left _ _) hn,
    pairDestroyer_of_pair_support_transversal h0 hcov (le_trans (le_max_right _ _) hn)
      hhub⟩

theorem pair_transversal_target_fails_iff {A B : Set ℕ} {n : ℕ} {S : Finset ℕ}
    (hhub : IsRepSupportTransversal A n S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS : ∀ s ∈ S, s ∉ B) (hSn : ∀ s ∈ S, s ≤ n) :
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) ↔
    (∀ s ∈ S, ∀ x ∈ A, ∀ y ∈ A, x + y = n - s →
      x ∈ B ∨ y ∈ B) := by
  constructor
  · intro hdead s hs x hx y hy hxy
    have hsn : s ≤ n := hSn s hs
    rcases hdead s (hSA s hs) x hx y hy (by omega) with h | h | h
    · exact absurd h (hBS s hs)
    · exact Or.inl h
    · exact Or.inr h
  · intro htrans x hx y hy z hz hsum
    rcases hhub x hx y hy z hz hsum with h | h | h
    · rcases htrans x h y hy z hz (by omega) with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · rcases htrans y h x hx z hz (by omega) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases htrans z h x hx y hy (by omega) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')

theorem disjointReps_le_hits {A B : Set ℕ} {n K : ℕ}
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (hdis : HasDisjointTripleReps A n K) :
    ∃ f : Fin K → ℕ, Function.Injective f ∧
      ∀ i, f i ∈ B ∧ f i ≤ n := by
  classical
  obtain ⟨P, hPA, hPsum, hPdisj⟩ := hdis
  have hhit : ∀ i : Fin K, ∃ k : Fin 3, P i k ∈ B := by
    intro i
    rcases hdead (P i 0) (hPA i 0) (P i 1) (hPA i 1) (P i 2) (hPA i 2)
      (hPsum i) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose g hg using hhit
  refine ⟨fun i => P i (g i), ?_, ?_⟩
  · intro i j hij
    by_contra hne
    exact hPdisj i j (g i) (g j) hne hij
  · intro i
    refine ⟨hg i, ?_⟩
    have hle : ∀ k, P i k ≤ n := by
      intro k
      have hs := hPsum i
      match k with
      | 0 => omega
      | 1 => omega
      | 2 => omega
    exact hle (g i)

theorem alignment_of_single_marker_failure {A B : Set ℕ} {n b : ℕ}
    {S : Finset ℕ}
    (hhub : IsRepSupportTransversal A n S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS : ∀ s ∈ S, s ∉ B) (hSn : ∀ s ∈ S, s ≤ n)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (honly : ∀ x ∈ B, x ≤ n → x = b) :
    ∀ s ∈ S, ∀ x ∈ A, ∀ y ∈ A, x + y = n - s → x = b ∨ y = b := by
  intro s hs x hx y hy hxy
  have htrans := (pair_transversal_target_fails_iff hhub hSA hBS hSn).1 hdead
  rcases htrans s hs x hx y hy hxy with h | h
  · exact Or.inl (honly x h (by omega))
  · exact Or.inr (honly y h (by omega))

theorem reversed_translate_of_alignment {A B : Set ℕ} {N₀ n b : ℕ}
    {S : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hhub : IsRepSupportTransversal A n S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS : ∀ s ∈ S, s ∉ B) (hSn : ∀ s ∈ S, s + N₀ ≤ n)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (honly : ∀ x ∈ B, x ≤ n → x = b) :
    ∀ s ∈ S, n - s - b ∈ A := by
  intro s hs
  have halign := alignment_of_single_marker_failure hhub hSA hBS
    (fun s hs => by have := hSn s hs; omega) hdead honly
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov (n - s) (by
    have := hSn s hs
    omega)
  rcases halign s hs x hx y hy hxy with h | h
  · have hyv : y = n - s - b := by omega
    rw [← hyv]
    exact hy
  · have hxv : x = n - s - b := by omega
    rw [← hxv]
    exact hx

theorem block_self_interaction {A B₁ : Set ℕ} {N₀ n₁ n₂ b₁ b₂ : ℕ}
    {S : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hhub₁ : IsRepSupportTransversal A n₁ S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS₁ : ∀ s ∈ S, s ∉ B₁) (hSn₁ : ∀ s ∈ S, s + N₀ ≤ n₁)
    (hdead₁ : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n₁ →
      x ∈ B₁ ∨ y ∈ B₁ ∨ z ∈ B₁)
    (honly₁ : ∀ x ∈ B₁, x ≤ n₁ → x = b₁)
    (hblock₂ : ∀ s ∈ S, n₂ - b₂ - s ∈ A) :
    ∀ s ∈ S, ∀ s' ∈ S, n₂ - b₂ - s' ≤ n₁ - s →
      n₁ - s - (n₂ - b₂ - s') ∈ A →
      (n₂ - b₂ - s' = b₁ ∨ n₁ - s - (n₂ - b₂ - s') = b₁) := by
  intro s hs s' hs' hle hmem
  have halign := alignment_of_single_marker_failure hhub₁ hSA hBS₁
    (fun t ht => by have := hSn₁ t ht; omega) hdead₁ honly₁
  exact halign s hs (n₂ - b₂ - s') (hblock₂ s' hs')
    (n₁ - s - (n₂ - b₂ - s')) hmem (by omega)

theorem doubling_rigidity_of_coverage {A B : Set ℕ} {n b s₀ : ℕ}
    {S : Finset ℕ}
    (hhub : IsRepSupportTransversal A n S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS : ∀ s ∈ S, s ∉ B) (hSn : ∀ s ∈ S, s ≤ n)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (honly : ∀ x ∈ B, x ≤ n → x = b)
    (hs₀ : s₀ ∈ S) (hn : n = 2 * b + s₀) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b → x = b ∧ y = b := by
  intro x hx y hy hxy
  have halign := alignment_of_single_marker_failure hhub hSA hBS hSn
    hdead honly
  have h2b : n - s₀ = 2 * b := by omega
  rcases halign s₀ hs₀ x hx y hy (by omega) with h | h <;> omega

theorem doubling_rigid_iff_reflection_free {A : Set ℕ} {x : ℕ}
    (hx : x ∈ A) :
    (∀ a ∈ A, ∀ b ∈ A, a + b = 2 * x → a = x ∧ b = x) ↔
    (∀ w, 0 < w → w ≤ x → ¬(x - w ∈ A ∧ x + w ∈ A)) := by
  constructor
  · intro hrig w hw hwx ⟨hlo, hhi⟩
    have := hrig (x - w) hlo (x + w) hhi (by omega)
    omega
  · intro hfree a ha b hb hab
    rcases Nat.lt_trichotomy a x with h | h | h
    · exfalso
      exact hfree (x - a) (by omega) (by omega)
        ⟨by
          have hxa : x - (x - a) = a := by omega
          rwa [hxa], by
          have hxb : x + (x - a) = b := by omega
          rwa [hxb]⟩
    · omega
    · exfalso
      exact hfree (a - x) (by omega) (by omega)
        ⟨by
          have hxa : x - (a - x) = 2 * x - a := by omega
          rw [hxa]
          have hxb : 2 * x - a = b := by omega
          rwa [hxb], by
          have hxa : x + (a - x) = a := by omega
          rwa [hxa]⟩

theorem not_reflectionLevel_of_rigid {A : Set ℕ} {N₀ x : ℕ}
    (hcov : PairCovers A N₀)
    (hrig : ∀ a ∈ A, ∀ b ∈ A, a + b = 2 * x → a = x ∧ b = x)
    (hx2 : 2 ≤ x) (hxN : N₀ + 1 ≤ 2 * x - 1) :
    ¬IsReflectionLevel A (2 * x) := by
  intro hlev
  obtain ⟨p, hp, q, hq, hpq⟩ := hcov (2 * x - 1) (by omega)
  -- some fiber element of 2x - 1 lies in (0, 2x) and differs from x
  have hz : ∃ z ∈ A, 0 < z ∧ z < 2 * x ∧ z ≠ x := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp0
    · exact ⟨q, hq, by omega, by omega, by omega⟩
    · rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · exact ⟨p, hp, by omega, by omega, by omega⟩
      · by_cases hpx : p = x
        · exact ⟨q, hq, by omega, by omega, by omega⟩
        · exact ⟨p, hp, by omega, by omega, hpx⟩
  obtain ⟨z, hzA, hz0, hzlt, hzx⟩ := hz
  have hmir : 2 * x - z ∈ A := (hlev z hz0 hzlt).1 hzA
  have := hrig z hzA (2 * x - z) hmir (by omega)
  omega

theorem translate_destruction_of_double_failure {A B : Set ℕ}
    {x c : ℕ}
    (hdead : ∀ p ∈ A, ∀ q ∈ A, ∀ r ∈ A, p + q + r = 2 * x →
      p ∈ B ∨ q ∈ B ∨ r ∈ B)
    (hc : c ∈ A) (hcB : c ∉ B) (hcx : c ≤ 2 * x) :
    ∀ a ∈ A, ∀ b ∈ A, a + b = 2 * x - c → a ∈ B ∨ b ∈ B := by
  intro a ha b hb hab
  rcases hdead a ha b hb c hc (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hcB

theorem no_total_doubles_coverage {A : Set ℕ} {N₀ Ns d : ℕ}
    (hcov : PairCovers A N₀) (hd : 0 < d)
    (hchain : ∀ b ∈ A, Ns ≤ b → b - d ∈ A)
    (hrig : ∀ b ∈ A, Ns ≤ b →
      ∀ p ∈ A, ∀ q ∈ A, p + q = 2 * b → p = b ∧ q = b) :
    False := by
  obtain ⟨b, hbA, hbge⟩ := pairCovers_unbounded hcov (Ns + 2 * d)
  have hb1 : b - d ∈ A := hchain b hbA (by omega)
  have hb2 : b - 2 * d ∈ A := by
    have := hchain (b - d) hb1 (by omega)
    have hbd : b - d - d = b - 2 * d := by omega
    rwa [hbd] at this
  have := hrig (b - d) hb1 (by omega) b hbA (b - 2 * d) hb2 (by omega)
  omega

theorem coverage_exclusion {A : Set ℕ} {b q : ℕ}
    (hb : b ∈ A) (hq : q ∈ A)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = b + q →
      (p = b ∧ r = q) ∨ (p = q ∧ r = b))
    {a : ℕ} (ha : a ∈ A) (hab : a ≠ b) (haq : a ≠ q)
    (hale : a ≤ b + q) :
    b + q - a ∉ A := by
  intro hmem
  rcases huniq a ha (b + q - a) hmem (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hab h1
  · exact haq h1

theorem coverage_sum_not_mem {A : Set ℕ} {b q : ℕ}
    (h0 : 0 ∈ A) (hb : b ∈ A) (hq : q ∈ A) (hb0 : 0 < b) (hq0 : 0 < q)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = b + q →
      (p = b ∧ r = q) ∨ (p = q ∧ r = b)) :
    b + q ∉ A := by
  intro hmem
  rcases huniq 0 h0 (b + q) hmem (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    omega

theorem coverage_sums_injective {A : Set ℕ} {b₁ q₁ b₂ q₂ : ℕ}
    (hb₁ : b₁ ∈ A) (hq₁ : q₁ ∈ A) (hb₂ : b₂ ∈ A) (hq₂ : q₂ ∈ A)
    (huniq₁ : ∀ p ∈ A, ∀ r ∈ A, p + r = b₁ + q₁ →
      (p = b₁ ∧ r = q₁) ∨ (p = q₁ ∧ r = b₁))
    (hne : b₂ ≠ b₁ ∧ b₂ ≠ q₁) :
    b₁ + q₁ ≠ b₂ + q₂ := by
  intro heq
  rcases huniq₁ b₂ hb₂ q₂ hq₂ (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hne.1 h1
  · exact hne.2 h1

theorem no_predecessor_of_partner_coverage {A : Set ℕ} {b q d : ℕ}
    (hd : 0 < d) (hdb : d ≤ b) (hdq : d ≤ q) (hqb : q ≠ b)
    (hq : q ∈ A) (hqd : q - d ∈ A)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = b + q - d →
      (p = b ∧ r = q - d) ∨ (p = q - d ∧ r = b)) :
    b - d ∉ A := by
  intro hmem
  rcases huniq q hq (b - d) hmem (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hqb h1
  · omega

theorem no_three_chain_of_rigid_middle {A : Set ℕ} {x d : ℕ}
    (hd : 0 < d)
    (hx : x ∈ A) (hxu : x + d ∈ A) (hxd : x + 2 * d ∈ A)
    (hrig : ∀ p ∈ A, ∀ r ∈ A, p + r = 2 * (x + d) → p = x + d ∧ r = x + d) :
    False := by
  have := hrig x hx (x + 2 * d) hxd (by ring)
  omega

theorem partner_is_doubles_served {A : Set ℕ} {q q' d : ℕ}
    (hd : 0 < d) (hdq : d ≤ q) (hdq' : d ≤ q') (hq'q : q' ≠ q)
    (hq' : q' ∈ A) (hq'd : q' - d ∈ A)
    (hqd : q - d ∈ A)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = q + q' - d →
      (p = q ∧ r = q' - d) ∨ (p = q' - d ∧ r = q)) :
    False :=
  no_predecessor_of_partner_coverage hd hdq hdq' hq'q hq' hq'd huniq hqd

/-- Order-2 disjoint representations: `K` pair-representations with
no shared part values. -/
def HasDisjointPairReps (A : Set ℕ) (n K : ℕ) : Prop :=
  ∃ P : Fin K → Fin 2 → ℕ,
    (∀ i k, P i k ∈ A) ∧
    (∀ i, P i 0 + P i 1 = n) ∧
    (∀ i j k l, i ≠ j → P i k ≠ P j l)

/-- Order-2 support transversal: a finite set meeting every pair representation. -/
def IsPairSupportTransversal (A : Set ℕ) (n : ℕ) (H : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H

theorem surviving_pair_deletion_of_disjointPairReps {A : Set ℕ}
    {N₀ : ℕ} (hcov : PairCovers A N₀)
    (hdis : ∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K) :
    ∃ B ⊆ A, B.Infinite ∧ ∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n := by
  classical
  choose N hN using hdis
  set Nt : ℕ → ℕ := fun K =>
    Nat.rec (N 0 + 1) (fun k prev => max (N (k + 1)) prev + 1) K with hNt
  have hNtS : ∀ k, Nt (k + 1) = max (N (k + 1)) (Nt k) + 1 :=
    fun _ => rfl
  have hNtmono : ∀ k, Nt k < Nt (k + 1) := by
    intro k
    rw [hNtS k]
    have := Nat.le_max_right (N (k + 1)) (Nt k)
    omega
  have hNtge : ∀ k, N k ≤ Nt k := by
    intro k
    cases k with
    | zero => simp [hNt]
    | succ k =>
      rw [hNtS k]
      have := Nat.le_max_left (N (k + 1)) (Nt k)
      omega
  have hchoice : ∀ X : ℕ, ∃ a, a ∈ A ∧ X ≤ a := by
    intro X
    obtain ⟨a, ha, hX⟩ := pairCovers_unbounded hcov X
    exact ⟨a, ha, hX⟩
  choose f hfA hfge using hchoice
  set b : ℕ → ℕ := fun k =>
    Nat.rec (f (Nt 2)) (fun k prev => f (max (Nt (k + 3)) (prev + 1))) k
    with hbdef
  have hbS : ∀ k, b (k + 1) = f (max (Nt (k + 3)) (b k + 1)) :=
    fun _ => rfl
  have hbA : ∀ k, b k ∈ A := by
    intro k
    cases k with
    | zero => exact hfA (Nt 2)
    | succ k =>
      rw [hbS k]
      exact hfA _
  have hbge : ∀ k, Nt (k + 2) ≤ b k := by
    intro k
    cases k with
    | zero => exact hfge (Nt 2)
    | succ k =>
      show Nt (k + 3) ≤ b (k + 1)
      rw [hbS k]
      have h1 := hfge (max (Nt (k + 3)) (b k + 1))
      have h2 := Nat.le_max_left (Nt (k + 3)) (b k + 1)
      omega
  have hbmono : ∀ k, b k < b (k + 1) := by
    intro k
    rw [hbS k]
    have h1 := hfge (max (Nt (k + 3)) (b k + 1))
    have h2 := Nat.le_max_right (Nt (k + 3)) (b k + 1)
    omega
  have hbstrict : StrictMono b := strictMono_nat_of_lt_succ hbmono
  refine ⟨Set.range b, ?_, ?_, Nt 2, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact hbA k
  · apply Set.infinite_of_injective_forall_mem
      (f := b) hbstrict.injective
    intro k
    exact ⟨k, rfl⟩
  · intro n hn
    have hexceed : ∃ j, n < b j := by
      refine ⟨n + 1, ?_⟩
      have h1 : Nt (n + 3) ≤ b (n + 1) := hbge (n + 1)
      have h2 : n + 3 ≤ Nt (n + 3) := by
        have h3 : ∀ m, m ≤ Nt m := by
          intro m
          induction m with
          | zero => omega
          | succ m ih =>
            have := hNtmono m
            omega
        exact h3 (n + 3)
      omega
    set K := Nat.find hexceed with hK
    have hKspec : n < b K := Nat.find_spec hexceed
    have hKmin : ∀ j, j < K → b j ≤ n := by
      intro j hj
      have := Nat.find_min hexceed hj
      omega
    have hnN : N (K + 1) ≤ n := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · rw [hK0]
        show N 1 ≤ n
        have h1 := hNtge 1
        have h2 : Nt 1 < Nt 2 := hNtmono 1
        omega
      · have h1 := hKmin (K - 1) (by omega)
        have h2 := hbge (K - 1)
        have h3 : K - 1 + 2 = K + 1 := by omega
        rw [h3] at h2
        have h4 := hNtge (K + 1)
        omega
    obtain ⟨P, hPA, hPsum, hPdisj⟩ := hN (K + 1) n hnN
    by_contra hall
    push Not at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, P i k = b j := by
      intro i
      have h0 := hPA i 0
      have h1 := hPA i 1
      by_contra hnone
      push Not at hnone
      have hfree : ∀ k, P i k ∉ Set.range b := by
        intro k
        rintro ⟨j, hj⟩
        have hj' : b j = P i k := hj
        have hle : P i k ≤ n := by
          have hs := hPsum i
          match k with
          | 0 => omega
          | 1 => omega
        have hjK : j < K := by
          by_contra hge
          have h3 : b K ≤ b j := hbstrict.monotone (by omega)
          omega
        exact hnone j hjK k hj'.symm
      exact absurd (hPsum i)
        (hall (P i 0) h0 (P i 1) h1 (hfree 0) (hfree 1))
    choose g hgK hghit using hhit
    have hginj : Function.Injective g := by
      intro i i' hgii
      by_contra hne
      obtain ⟨k, hk⟩ := hghit i
      obtain ⟨k', hk'⟩ := hghit i'
      have : P i k = P i' k' := by rw [hk, hgii, hk']
      exact hPdisj i i' k k' hne this
    have hcard : K + 1 ≤ K := by
      let g' : Fin (K + 1) → Fin K := fun i => ⟨g i, hgK i⟩
      have hg'inj : Function.Injective g' := by
        intro i i' h
        apply hginj
        have := congrArg Fin.val h
        simpa using this
      have := Fintype.card_le_of_injective g' hg'inj
      simpa using this
    omega

/-- Pair-support transversal extraction: no `K` disjoint pair-representations yields
a support transversal of at most `2·(K-1)` values meeting every pair representation. -/
theorem pairSupportTransversal_of_no_disjointPairReps {A : Set ℕ} {n K : ℕ}
    (hno : ¬HasDisjointPairReps A n K) :
    ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairSupportTransversal A n H := by
  classical
  have h0 : HasDisjointPairReps A n 0 :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  have hcross : ∃ J, J < K ∧ HasDisjointPairReps A n J ∧
      ¬HasDisjointPairReps A n (J + 1) := by
    by_contra hnc
    push Not at hnc
    have hall : ∀ J, J ≤ K → HasDisjointPairReps A n J := by
      intro J hJ
      induction J with
      | zero => exact h0
      | succ J ih => exact hnc J (by omega) (ih (by omega))
    exact hno (hall K (le_refl K))
  obtain ⟨J, hJK, ⟨P, hPA, hPsum, hPdisj⟩, hJmax⟩ := hcross
  refine ⟨(Finset.univ : Finset (Fin J × Fin 2)).image
    (fun p => P p.1 p.2), ?_, ?_⟩
  · calc ((Finset.univ : Finset (Fin J × Fin 2)).image
        (fun p => P p.1 p.2)).card
        ≤ (Finset.univ : Finset (Fin J × Fin 2)).card :=
          Finset.card_image_le
      _ = 2 * J := by simp [Finset.card_univ, Nat.mul_comm]
      _ ≤ 2 * (K - 1) := by omega
  · intro x hx y hy hsum
    by_contra hnot
    push Not at hnot
    obtain ⟨hxH, hyH⟩ := hnot
    have hmem : ∀ i k, P i k ∈ (Finset.univ :
        Finset (Fin J × Fin 2)).image (fun p => P p.1 p.2) := by
      intro i k
      exact Finset.mem_image.2 ⟨(i, k), Finset.mem_univ _, rfl⟩
    set R : Fin 2 → ℕ := ![x, y] with hR
    have hRA : ∀ k, R k ∈ A := by
      intro k
      match k with
      | 0 => exact hx
      | 1 => exact hy
    have hRH : ∀ k, R k ∉ (Finset.univ :
        Finset (Fin J × Fin 2)).image (fun p => P p.1 p.2) := by
      intro k
      match k with
      | 0 => exact hxH
      | 1 => exact hyH
    have hRsum : R 0 + R 1 = n := hsum
    refine hJmax ⟨fun i k =>
      if h : (i : ℕ) < J then P ⟨i, h⟩ k else R k, ?_, ?_, ?_⟩
    · intro i k
      by_cases h : (i : ℕ) < J
      · simpa [h] using hPA ⟨i, h⟩ k
      · simpa [h] using hRA k
    · intro i
      by_cases h : (i : ℕ) < J
      · simpa [h] using hPsum ⟨i, h⟩
      · simpa [h] using hRsum
    · intro i j k l hij
      by_cases hi : (i : ℕ) < J
      · by_cases hj : (j : ℕ) < J
        · have hne : (⟨(i : ℕ), hi⟩ : Fin J) ≠ ⟨(j : ℕ), hj⟩ := by
            intro h
            apply hij
            have := congrArg Fin.val h
            exact Fin.ext (by simpa using this)
          simpa [hi, hj] using hPdisj ⟨i, hi⟩ ⟨j, hj⟩ k l hne
        · simp only [dif_pos hi, dif_neg hj]
          intro h
          exact hRH l (h ▸ hmem ⟨i, hi⟩ k)
      · by_cases hj : (j : ℕ) < J
        · simp only [dif_neg hi, dif_pos hj]
          intro h
          exact hRH k (h.symm ▸ hmem ⟨j, hj⟩ l)
        · exfalso
          apply hij
          have hiJ : (i : ℕ) = J := by
            have := i.isLt
            omega
          have hjJ : (j : ℕ) = J := by
            have := j.isLt
            omega
          exact Fin.ext (by omega)

theorem cofinal_bounded_pairSupportTransversals_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairSupportTransversal A n H := by
  classical
  have hnodis : ¬∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K := by
    intro hdis
    obtain ⟨B, hBsub, hBinf, N₁, hN₁⟩ :=
      surviving_pair_deletion_of_disjointPairReps hcov hdis
    exact hmin B hBsub hBinf ⟨N₁, hN₁⟩
  push Not at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := pairSupportTransversal_of_no_disjointPairReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

/-- Predicate-generic stable core: the budget descent works for any
support transversal notion. -/
theorem stable_core_generic {C : ℕ} (SupportTransversal : ℕ → Finset ℕ → Prop) :
    ∀ d S,
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ SupportTransversal n H ∧
      S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S ⊆ S' ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        SupportTransversal n H ∧ S' ⊆ H ∧
        ∀ h ∈ H, h ∉ S' → W < h := by
  classical
  intro d
  induction d with
  | zero =>
    intro S hfam
    refine ⟨S, Finset.Subset.refl S, fun W N => ?_⟩
    obtain ⟨n, hn, H, hcard, hhub, hSH, hbud⟩ := hfam N
    refine ⟨n, hn, H, hcard, hhub, hSH, fun h hhH hhS => ?_⟩
    exfalso
    have hHS : H = S := Finset.Subset.antisymm
      (by
        by_contra hns
        obtain ⟨x, hxH, hxS⟩ := Finset.not_subset.1 hns
        have h1 : S.card < H.card := Finset.card_lt_card
          (Finset.ssubset_iff_of_subset hSH |>.2 ⟨x, hxH, hxS⟩)
        omega) hSH
    rw [hHS] at hhH
    exact hhS hhH
  | succ d ih =>
    intro S hfam
    by_cases hstable : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card ≤ C ∧ SupportTransversal n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h
    · exact ⟨S, Finset.Subset.refl S, hstable⟩
    · push Not at hstable
      obtain ⟨W₁, N₁, hW₁⟩ := hstable
      rcases cofinal_dichotomy
        (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ SupportTransversal n H ∧
          S ⊆ H ∧ H.card ≤ S.card + (d + 1) ∧ H' = H \ S)
        (fun N => by
          obtain ⟨n, hn, H, hcard, hhub, hSH, hbud⟩ := hfam N
          exact ⟨n, hn, H \ S, H, hcard, hhub, hSH, hbud, rfl⟩) W₁
        with ⟨h, hhW, hper⟩ | hlarge
      · obtain ⟨S', hS'sub, hS'split⟩ := ih (insert h S) (fun N => by
          obtain ⟨n, hn, H', ⟨H, hcard, hhub, hSH, hbud, hH'⟩, hhH'⟩ :=
            hper N
          subst hH'
          have hhH : h ∈ H := (Finset.mem_sdiff.1 hhH').1
          have hhS : h ∉ S := (Finset.mem_sdiff.1 hhH').2
          refine ⟨n, hn, H, hcard, hhub, ?_, ?_⟩
          · intro x hx
            rcases Finset.mem_insert.1 hx with hxh | hxS
            · rw [hxh]; exact hhH
            · exact hSH hxS
          · have : (insert h S).card = S.card + 1 :=
              Finset.card_insert_of_notMem hhS
            omega)
        exact ⟨S', Finset.Subset.trans (Finset.subset_insert h S) hS'sub,
          hS'split⟩
      · exfalso
        obtain ⟨n, hn, H', ⟨H, hcard, hhub, hSH, hbud, hH'⟩, hlargeH⟩ :=
          hlarge N₁
        subst hH'
        obtain ⟨h, hhH, hhS, hhW⟩ := hW₁ n hn H hcard hhub hSH
        have := hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)
        omega

theorem stable_pair_core_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairSupportTransversal A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_pairSupportTransversals_of_minimality hcov hmin
  obtain ⟨S, -, hsplit⟩ := stable_core_generic
    (C := 2 * (K - 1)) (fun n H => IsPairSupportTransversal A n H)
    (2 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      exact ⟨n, hn, H, hcard, hhub, Finset.empty_subset _,
        by simpa using hcard⟩)
  exact ⟨K, S, hsplit⟩

theorem stable_pair_core_card_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K S c, c ≤ 2 * (K - 1) ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsPairSupportTransversal A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, S, hsplit⟩ := stable_pair_core_of_minimality hcov hmin
  set Good : ℕ → ℕ → Prop := fun W c =>
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card = c ∧ IsPairSupportTransversal A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h with hGood
  have hdown : ∀ W W' c, W ≤ W' → Good W' c → Good W c := by
    intro W W' c hWW' hg N
    obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hg N
    exact ⟨n, hn, H, hcard, hhub, hSH,
      fun h hh hhS => by have := hrest h hh hhS; omega⟩
  have hperW : ∀ W, ∃ c, c ≤ 2 * (K - 1) ∧ Good W c := by
    intro W
    obtain ⟨c, hc, hcof⟩ := cofinal_value_pigeonhole
      (P := fun n c => ∃ H : Finset ℕ, H.card = c ∧ IsPairSupportTransversal A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) (fun N => by
        obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hsplit W N
        exact ⟨n, hn, H.card, hcard, H, rfl, hhub, hSH, hrest⟩)
    exact ⟨c, hc, hcof⟩
  by_contra hno
  push Not at hno
  have hex : ∀ c, ∃ Wc, c ≤ 2 * (K - 1) → ¬Good Wc c := by
    intro c
    by_cases hc : c ≤ 2 * (K - 1)
    · obtain ⟨W, hW⟩ := hno K S c hc
      refine ⟨W, fun _ hgood => ?_⟩
      obtain ⟨N, hN⟩ := hW
      obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hgood N
      obtain ⟨h, hh, hhS, hhW⟩ := hN n hn H hcard hhub hSH
      have := hrest h hh hhS
      omega
    · exact ⟨0, fun h => absurd h hc⟩
  choose gW hgW using hex
  set WS := (Finset.range (2 * (K - 1) + 1)).sup gW with hWS
  obtain ⟨c, hc, hgood⟩ := hperW WS
  have h2 : gW c ≤ WS := by
    rw [hWS]
    exact Finset.le_sup (Finset.mem_range.2 (by omega))
  exact hgW c hc (hdown (gW c) WS c h2 hgood)

theorem recurring_destroyer_pair_of_tight_core {A : Set ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsPairSupportTransversal A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hceq : c = S.card) (hS2 : S.card = 2) :
    ∃ u v, u ≠ v ∧ ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = n → x = u ∨ x = v ∨ y = u ∨ y = v := by
  obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.1 hS2
  refine ⟨u, v, huv, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hsplit 0 N
  have hHS : S = H := Finset.eq_of_subset_of_card_le hSH (by omega)
  refine ⟨n, hn, fun x hx y hy hxy => ?_⟩
  rcases hhub x hx y hy hxy with h | h
  · rw [← hHS, hSuv] at h
    rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (Finset.mem_singleton.1 h'))
  · rw [← hHS, hSuv] at h
    rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.1 h')))

theorem pairSupportTransversal_iff_twoDestroyed {A : Set ℕ} {n : ℕ} {H : Finset ℕ} :
    IsPairSupportTransversal A n H ↔ TwoDestroyedBySet A (↑H) n := by
  constructor
  · intro h y hy z hz hyz
    rcases h y hy z hz hyz with h' | h'
    · exact Or.inl (Finset.mem_coe.2 h')
    · exact Or.inr (Finset.mem_coe.2 h')
  · intro h x hx y hy hxy
    rcases h x hx y hy hxy with h' | h'
    · exact Or.inl (Finset.mem_coe.1 h')
    · exact Or.inr (Finset.mem_coe.1 h')

theorem legacy_twoDestruction_of_tight_core {A : Set ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsPairSupportTransversal A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hceq : c = S.card) (hS2 : S.card = 2) :
    ∃ u v, u ≠ v ∧ ∀ N, ∃ n, N ≤ n ∧
      TwoDestroyedBySet A {u, v} n := by
  obtain ⟨u, v, huv, hrec⟩ :=
    recurring_destroyer_pair_of_tight_core hsplit hceq hS2
  refine ⟨u, v, huv, fun N => ?_⟩
  obtain ⟨n, hn, hdest⟩ := hrec N
  refine ⟨n, hn, fun y hy z hz hyz => ?_⟩
  rcases hdest y hy z hz hyz with h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem corrected_covering_of_rigidity {A : Set ℕ} {N₀ Ns d : ℕ}
    (hd : 0 < d) (hcov : PairCovers A N₀)
    (hrig : ∀ x ∈ A, Ns ≤ x →
      ∀ p ∈ A, ∀ r ∈ A, p + r = 2 * x → p = x ∧ r = x) :
    ∀ n, N₀ ≤ n → ∃ p ∈ A, ∃ p' ∈ A,
      (d ≤ p → p - d ∈ A → p - d < Ns + d) ∧
      (d ≤ p' → p' - d ∈ A → p' - d < Ns + d) ∧
      ∃ ε, (ε = 0 ∨ ε = d ∨ ε = 2 * d) ∧ p + p' + ε = n := by
  intro n hn
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  -- decompose one element: itself, or its predecessor plus d
  have hdec : ∀ z ∈ A, ∃ p ∈ A, ∃ ε, (ε = 0 ∨ ε = d) ∧ p + ε = z ∧
      (d ≤ p → p - d ∈ A → p - d < Ns + d) := by
    intro z hz
    by_cases hzd : d ≤ z ∧ z - d ∈ A ∧ Ns + d ≤ z - d
    · obtain ⟨hdz, hzdA, hzNs⟩ := hzd
      refine ⟨z - d, hzdA, d, Or.inr rfl, by omega, ?_⟩
      intro hdp hpd
      -- a further predecessor gives a three-chain through z - d
      exfalso
      have hmid : Ns ≤ z - d := by omega
      refine no_three_chain_of_rigid_middle (A := A) (x := z - 2 * d)
        hd ?_ ?_ ?_ ?_
      · have h1 : z - d - d = z - 2 * d := by omega
        rwa [h1] at hpd
      · have h1 : z - 2 * d + d = z - d := by omega
        rwa [h1]
      · have h1 : z - 2 * d + 2 * d = z := by omega
        rwa [h1]
      · have h1 : z - 2 * d + d = z - d := by omega
        rw [h1]
        exact hrig (z - d) hzdA hmid
    · push Not at hzd
      refine ⟨z, hz, 0, Or.inl rfl, by omega, ?_⟩
      intro hdz hzdA
      by_contra hbig
      push Not at hbig
      exact absurd hbig (by
        have := hzd hdz hzdA
        omega)
  obtain ⟨p, hp, ε₁, hε₁, hpε₁, hpfree⟩ := hdec x hx
  obtain ⟨p', hp', ε₂, hε₂, hpε₂, hpfree'⟩ := hdec y hy
  refine ⟨p, hp, p', hp', hpfree, hpfree', ε₁ + ε₂, ?_, by omega⟩
  rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2 <;> omega

theorem surviving_pair_deletion_of_disjointPairReps_pool {A P : Set ℕ}
    (hPA : P ⊆ A)
    (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hdis : ∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K) :
    ∃ B ⊆ P, B.Infinite ∧ ∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n := by
  classical
  choose N hN using hdis
  set Nt : ℕ → ℕ := fun K =>
    Nat.rec (N 0 + 1) (fun k prev => max (N (k + 1)) prev + 1) K with hNt
  have hNtS : ∀ k, Nt (k + 1) = max (N (k + 1)) (Nt k) + 1 :=
    fun _ => rfl
  have hNtmono : ∀ k, Nt k < Nt (k + 1) := by
    intro k
    rw [hNtS k]
    have := Nat.le_max_right (N (k + 1)) (Nt k)
    omega
  have hNtge : ∀ k, N k ≤ Nt k := by
    intro k
    cases k with
    | zero => simp [hNt]
    | succ k =>
      rw [hNtS k]
      have := Nat.le_max_left (N (k + 1)) (Nt k)
      omega
  choose f hfP hfge using hunb
  set b : ℕ → ℕ := fun k =>
    Nat.rec (f (Nt 2)) (fun k prev => f (max (Nt (k + 3)) (prev + 1))) k
    with hbdef
  have hbS : ∀ k, b (k + 1) = f (max (Nt (k + 3)) (b k + 1)) :=
    fun _ => rfl
  have hbP : ∀ k, b k ∈ P := by
    intro k
    cases k with
    | zero => exact hfP (Nt 2)
    | succ k =>
      rw [hbS k]
      exact hfP _
  have hbge : ∀ k, Nt (k + 2) ≤ b k := by
    intro k
    cases k with
    | zero => exact hfge (Nt 2)
    | succ k =>
      show Nt (k + 3) ≤ b (k + 1)
      rw [hbS k]
      have h1 := hfge (max (Nt (k + 3)) (b k + 1))
      have h2 := Nat.le_max_left (Nt (k + 3)) (b k + 1)
      omega
  have hbmono : ∀ k, b k < b (k + 1) := by
    intro k
    rw [hbS k]
    have h1 := hfge (max (Nt (k + 3)) (b k + 1))
    have h2 := Nat.le_max_right (Nt (k + 3)) (b k + 1)
    omega
  have hbstrict : StrictMono b := strictMono_nat_of_lt_succ hbmono
  refine ⟨Set.range b, ?_, ?_, Nt 2, ?_⟩
  · rintro x ⟨k, rfl⟩
    exact hbP k
  · apply Set.infinite_of_injective_forall_mem
      (f := b) hbstrict.injective
    intro k
    exact ⟨k, rfl⟩
  · intro n hn
    have hexceed : ∃ j, n < b j := by
      refine ⟨n + 1, ?_⟩
      have h1 : Nt (n + 3) ≤ b (n + 1) := hbge (n + 1)
      have h2 : n + 3 ≤ Nt (n + 3) := by
        have h3 : ∀ m, m ≤ Nt m := by
          intro m
          induction m with
          | zero => omega
          | succ m ih =>
            have := hNtmono m
            omega
        exact h3 (n + 3)
      omega
    set K := Nat.find hexceed with hK
    have hKspec : n < b K := Nat.find_spec hexceed
    have hKmin : ∀ j, j < K → b j ≤ n := by
      intro j hj
      have := Nat.find_min hexceed hj
      omega
    have hnN : N (K + 1) ≤ n := by
      rcases Nat.eq_zero_or_pos K with hK0 | hKpos
      · rw [hK0]
        show N 1 ≤ n
        have h1 := hNtge 1
        have h2 : Nt 1 < Nt 2 := hNtmono 1
        omega
      · have h1 := hKmin (K - 1) (by omega)
        have h2 := hbge (K - 1)
        have h3 : K - 1 + 2 = K + 1 := by omega
        rw [h3] at h2
        have h4 := hNtge (K + 1)
        omega
    obtain ⟨Pm, hPA', hPsum, hPdisj⟩ := hN (K + 1) n hnN
    by_contra hall
    push Not at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, Pm i k = b j := by
      intro i
      have h0 := hPA' i 0
      have h1 := hPA' i 1
      by_contra hnone
      push Not at hnone
      have hfree : ∀ k, Pm i k ∉ Set.range b := by
        intro k
        rintro ⟨j, hj⟩
        have hj' : b j = Pm i k := hj
        have hle : Pm i k ≤ n := by
          have hs := hPsum i
          match k with
          | 0 => omega
          | 1 => omega
        have hjK : j < K := by
          by_contra hge
          have h3 : b K ≤ b j := hbstrict.monotone (by omega)
          omega
        exact hnone j hjK k hj'.symm
      exact absurd (hPsum i)
        (hall (Pm i 0) h0 (Pm i 1) h1 (hfree 0) (hfree 1))
    choose g hgK hghit using hhit
    have hginj : Function.Injective g := by
      intro i i' hgii
      by_contra hne
      obtain ⟨k, hk⟩ := hghit i
      obtain ⟨k', hk'⟩ := hghit i'
      have : Pm i k = Pm i' k' := by rw [hk, hgii, hk']
      exact hPdisj i i' k k' hne this
    have hcard : K + 1 ≤ K := by
      let g' : Fin (K + 1) → Fin K := fun i => ⟨g i, hgK i⟩
      have hg'inj : Function.Injective g' := by
        intro i i' h
        apply hginj
        have := congrArg Fin.val h
        simpa using this
      have := Fintype.card_le_of_injective g' hg'inj
      simpa using this
    omega

theorem cofinal_bounded_pairSupportTransversals_of_minimality_pool {A P : Set ℕ}
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairSupportTransversal A n H := by
  classical
  have hnodis : ¬∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K := by
    intro hdis
    obtain ⟨B, hBsub, hBinf, N₁, hN₁⟩ :=
      surviving_pair_deletion_of_disjointPairReps_pool hPA hunb hdis
    exact hmin B (fun x hx => hPA (hBsub hx)) hBinf ⟨N₁, hN₁⟩
  push Not at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := pairSupportTransversal_of_no_disjointPairReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

theorem stable_pair_core_of_minimality_pool {A P : Set ℕ}
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairSupportTransversal A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_pairSupportTransversals_of_minimality_pool hPA
    hunb hmin
  obtain ⟨S, -, hsplit⟩ := stable_core_generic
    (C := 2 * (K - 1)) (fun n H => IsPairSupportTransversal A n H)
    (2 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      exact ⟨n, hn, H, hcard, hhub, Finset.empty_subset _,
        by simpa using hcard⟩)
  exact ⟨K, S, hsplit⟩

theorem mixed_pair_destruction_sharpens {A P B : Set ℕ} {t : ℕ}
    (hPA : P ⊆ A) (hB : B ⊆ P)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ p ∈ P, ∀ q ∈ A, q ∉ P → p + q = t → p ∈ B := by
  intro p hp q hq hqP hpq
  rcases hdest p (hPA hp) q hq hpq with h | h
  · exact h
  · exact absurd (hB h) hqP

/-- Pure pool pairs inherit destruction verbatim. -/
theorem pool_pair_destruction {A P B : Set ℕ} {t : ℕ}
    (hPA : P ⊆ A)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ p ∈ P, ∀ p' ∈ P, p + p' = t → p ∈ B ∨ p' ∈ B :=
  fun p hp p' hp' hpp' => hdest p (hPA hp) p' (hPA hp') hpp'

theorem single_marker_mixed_exclusion {A P B : Set ℕ} {b t : ℕ}
    (hPA : P ⊆ A) (hB : B ⊆ P)
    (honly : ∀ x ∈ B, x ≤ t → x = b)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ p ∈ P, p ≠ b → ∀ q ∈ A, q ∉ P → p + q ≠ t := by
  intro p hp hpb q hq hqP hpq
  have hpB : p ∈ B :=
    mixed_pair_destruction_sharpens hPA hB hdest p hp q hq hqP hpq
  exact hpb (honly p hpB (by omega))

theorem no_outside_pairs_of_destroyed {A P B : Set ℕ} {t : ℕ}
    (hB : B ⊆ P)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ q ∈ A, q ∉ P → ∀ q' ∈ A, q' ∉ P → q + q' ≠ t := by
  intro q hq hqP q' hq' hq'P hqq'
  rcases hdest q hq q' hq' hqq' with h | h
  · exact hqP (hB h)
  · exact hq'P (hB h)

theorem level2_corep {A P B : Set ℕ} {N₀ b t : ℕ}
    (hcov : PairCovers A N₀) (htN : N₀ ≤ t)
    (hPA : P ⊆ A) (hB : B ⊆ P)
    (honly : ∀ x ∈ B, x ≤ t → x = b)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    b ≤ t ∧ t - b ∈ A := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov t htN
  rcases hdest x hx y hy hxy with h | h
  · have hxb : x = b := honly x h (by omega)
    subst hxb
    have hyv : y = t - x := by omega
    rw [hyv] at hy
    exact ⟨by omega, hy⟩
  · have hyb : y = b := honly y h (by omega)
    subst hyb
    have hxv : x = t - y := by omega
    rw [hxv] at hx
    exact ⟨by omega, hx⟩

theorem level2_rigidity_free {A P B : Set ℕ} {b : ℕ}
    (hB : B ⊆ P)
    (honly : ∀ x ∈ B, x ≤ 2 * b → x = b)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b → x ∈ B ∨ y ∈ B) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b → x = b ∧ y = b := by
  intro x hx y hy hxy
  rcases hdest x hx y hy hxy with h | h
  · have hxb : x = b := honly x h (by omega)
    omega
  · have hyb : y = b := honly y h (by omega)
    omega

theorem failing_support_transversal_subset_deletion {A B : Set ℕ} {n : ℕ}
    [DecidablePred (· ∈ B)]
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) :
    IsRepSupportTransversal A n ((Finset.range (n + 1)).filter (· ∈ B)) := by
  intro x hx y hy z hz hsum
  rcases hdead x hx y hy z hz hsum with h | h | h
  · exact Or.inl (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩))

theorem cofinal_subset_pigeonhole {Q : ℕ → Finset ℕ → Prop}
    {F : Finset ℕ}
    (hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ H, H ⊆ F ∧ Q n H) :
    ∃ S ⊆ F, ∀ N, ∃ n, N ≤ n ∧ Q n S := by
  classical
  by_contra hno
  push Not at hno
  have hex : ∀ S : Finset ℕ, ∃ NS, S ⊆ F → ∀ n, NS ≤ n → ¬Q n S := by
    intro S
    by_cases hS : S ⊆ F
    · obtain ⟨N, hN⟩ := hno S hS
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose g hg using hex
  set NS := F.powerset.sup g with hNS
  obtain ⟨n, hn, H, hHF, hQH⟩ := hQ NS
  have hgle : g H ≤ NS := by
    rw [hNS]
    exact Finset.le_sup (Finset.mem_powerset.2 hHF)
  exact hg H hHF n (by omega) hQH

theorem per_deletion_window_core {A B : Set ℕ}
    [DecidablePred (· ∈ B)]
    (hfailB : ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
        x ∈ B ∨ y ∈ B ∨ z ∈ B) (W : ℕ) :
    ∃ S ⊆ (Finset.range (W + 1)).filter (· ∈ B),
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
        H ∩ Finset.range (W + 1) =
          S ∩ Finset.range (W + 1) := by
  classical
  have hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ S,
      S ⊆ (Finset.range (W + 1)).filter (· ∈ B) ∧
      (∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
        H ∩ Finset.range (W + 1) = S ∩ Finset.range (W + 1)) := by
    intro N
    obtain ⟨n, hn, hdead⟩ := hfailB N
    have hhub := failing_support_transversal_subset_deletion (A := A) (B := B) hdead
    obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_support_transversal hhub
    refine ⟨n, hn, H ∩ Finset.range (W + 1), ?_, H, hHhub, hHmin, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxH, hxW⟩ := Finset.mem_inter.1 hx
      have := hHsub hxH
      obtain ⟨hxn, hxB⟩ := Finset.mem_filter.1 this
      exact Finset.mem_filter.2 ⟨hxW, hxB⟩
    · exact hHsub
    · rw [Finset.inter_assoc, Finset.inter_self]
  obtain ⟨S, hSF, hrec⟩ := cofinal_subset_pigeonhole
    (Q := fun n S => ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
      H ∩ Finset.range (W + 1) = S ∩ Finset.range (W + 1))
    (F := (Finset.range (W + 1)).filter (· ∈ B)) hQ
  exact ⟨S, hSF, hrec⟩

theorem escape_singleton_of_supergeometric {b : ℕ → ℕ}
    (hsg : ∀ j k, j < k → b j * b j < b k)
    {n : ℕ} {H : Finset ℕ}
    (hHB : ∀ h ∈ H, ∃ j, h = b j)
    (hHn : ∀ h ∈ H, h ≤ n)
    (hesc : ∀ h ∈ H, n < h * h)
    (hne : H.Nonempty) :
    ∃ h₀, H = {h₀} := by
  classical
  obtain ⟨h₀, hh₀⟩ := hne
  refine ⟨h₀, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.2
  refine ⟨hh₀, fun h hh => ?_⟩
  by_contra hne'
  obtain ⟨j, hj⟩ := hHB h hh
  obtain ⟨j₀, hj₀⟩ := hHB h₀ hh₀
  have hjj : j ≠ j₀ := by
    intro h'
    apply hne'
    rw [hj, hj₀, h']
  rcases Nat.lt_or_ge j j₀ with hlt | hge
  · have := hsg j j₀ hlt
    have h1 := hesc h hh
    have h2 := hHn h₀ hh₀
    rw [hj, hj₀] at *
    omega
  · have hlt' : j₀ < j := by omega
    have := hsg j₀ j hlt'
    have h1 := hesc h₀ hh₀
    have h2 := hHn h hh
    rw [hj, hj₀] at *
    omega

theorem per_deletion_dichotomy_final {A : Set ℕ} {b : ℕ → ℕ}
    (hsg : ∀ j k, j < k → b j * b j < b k)
    {n : ℕ}
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      (∃ j, x = b j) ∨ (∃ j, y = b j) ∨ (∃ j, z = b j))
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n) :
    ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      (∀ h ∈ H, (∃ j, h = b j) ∧ h ≤ n) ∧
      ((∃ h ∈ H, h * h ≤ n) ∨ (∃ h₀, H = {h₀})) := by
  classical
  have hdead' : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ {m | ∃ j, m = b j} ∨ y ∈ {m | ∃ j, m = b j} ∨
      z ∈ {m | ∃ j, m = b j} := hdead
  have hhub := failing_support_transversal_subset_deletion
    (B := {m | ∃ j, m = b j}) hdead'
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_support_transversal hhub
  have hHB : ∀ h ∈ H, (∃ j, h = b j) ∧ h ≤ n := by
    intro h hh
    have := hHsub hh
    obtain ⟨hr, hm⟩ := Finset.mem_filter.1 this
    exact ⟨hm, by
      have := Finset.mem_range.1 hr
      omega⟩
  refine ⟨H, hHhub, hHmin, hHB, ?_⟩
  by_cases hesc : ∀ h ∈ H, n < h * h
  · right
    have hne : H.Nonempty := by
      obtain ⟨x, hx, y, hy, z, hz, hsum⟩ := hrep
      rcases hHhub x hx y hy z hz hsum with h | h | h
      · exact ⟨x, h⟩
      · exact ⟨y, h⟩
      · exact ⟨z, h⟩
    exact escape_singleton_of_supergeometric hsg
      (fun h hh => (hHB h hh).1) (fun h hh => (hHB h hh).2) hesc hne
  · left
    push Not at hesc
    obtain ⟨h, hh, hhn⟩ := hesc
    exact ⟨h, hh, hhn⟩

/-- `a` owns `n` when `n ∈ (a, 2a)`, `n - a ∈ A`, and `a` is the unique
element of `A ∩ (n / 2, n)` whose complement in `n` belongs to `A`. -/
def OwnsTarget (A : Set ℕ) (a n : ℕ) : Prop :=
  a < n ∧ n < 2 * a ∧ n - a ∈ A ∧
  ∀ y ∈ A, 2 * y > n → y < n → y ≠ a → n - y ∉ A

/-- The complementary element of an owned target is smaller than its owner. -/
theorem OwnsTarget.chain_step {A : Set ℕ} {a n : ℕ}
    (h : OwnsTarget A a n) : n - a ∈ A ∧ n - a < a := by
  obtain ⟨h1, h2, h3, _⟩ := h
  exact ⟨h3, by omega⟩

/-- A target has at most one owner in `A`. -/
theorem OwnsTarget.unique_marked_element {A : Set ℕ} {a a' n : ℕ}
    (ha : a ∈ A) (ha' : a' ∈ A)
    (h : OwnsTarget A a n) (h' : OwnsTarget A a' n) : a = a' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  by_contra hne
  have := h4 a' ha' (by omega) (by omega) (fun hc => hne hc.symm)
  exact this h3'

def UniversalTargetOwnership (A : Set ℕ) (Ns : ℕ) : Prop :=
  ∀ a ∈ A, Ns ≤ a → ∃ n, OwnsTarget A a n

theorem ownership_chain {A : Set ℕ} {Ns : ℕ}
    (huniv : UniversalTargetOwnership A Ns) :
    ∀ a ∈ A, ∃ k, ∃ c : ℕ → ℕ, c 0 = a ∧
      (∀ i ≤ k, c i ∈ A) ∧
      (∀ i < k, ∃ n, OwnsTarget A (c i) n ∧ c (i + 1) = n - c i) ∧
      c k < Ns := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haA
    by_cases hlt : a < Ns
    · exact ⟨0, fun _ => a, rfl, fun i hi => by
        cases Nat.le_zero.1 hi
        exact haA, fun i hi => absurd hi (by omega), hlt⟩
    · push Not at hlt
      obtain ⟨n, hown⟩ := huniv a haA hlt
      obtain ⟨hsA, hslt⟩ := hown.chain_step
      obtain ⟨k, c, hc0, hcA, hcstep, hcend⟩ := ih (n - a) hslt hsA
      refine ⟨k + 1, fun i => if i = 0 then a else c (i - 1), by simp,
        ?_, ?_, ?_⟩
      · intro i hi
        by_cases hi0 : i = 0
        · simpa [hi0] using haA
        · simp only [if_neg hi0]
          exact hcA (i - 1) (by omega)
      · intro i hi
        by_cases hi0 : i = 0
        · subst hi0
          refine ⟨n, hown, ?_⟩
          simp [hc0]
        · simp only [if_neg hi0, if_neg (by omega : ¬i + 1 = 0)]
          obtain ⟨m, hm, hstep⟩ := hcstep (i - 1) (by omega)
          refine ⟨m, hm, ?_⟩
          have h1 : i + 1 - 1 = i - 1 + 1 := by omega
          rw [h1, hstep]
      · simp only [if_neg (by omega : ¬k + 1 = 0)]
        simpa using hcend

theorem ownership_bans_reflection {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ s' ∈ A, 0 < s' → s' < n - a → n - s' ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro s' hs' h0 hlt hmem
  have hbig : 2 * (n - s') > n := by omega
  have hne : n - s' ≠ a := by omega
  have := h4 (n - s') hmem hbig (by omega) hne
  have hval : n - (n - s') = s' := by omega
  rw [hval] at this
  exact this hs'

theorem ownsTarget_pairSupportTransversal {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n →
      x = a ∨ y = a ∨ 2 * x = n ∨ x = 0 ∨ y = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro x hx y hy hxy
  rcases Nat.eq_zero_or_pos x with hx0 | hx0
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx0)))
  rcases Nat.eq_zero_or_pos y with hy0 | hy0
  · exact Or.inr (Or.inr (Or.inr (Or.inr hy0)))
  rcases Nat.lt_trichotomy (2 * x) n with hlt | heq | hgt
  · by_cases hya : y = a
    · exact Or.inr (Or.inl hya)
    · exfalso
      have := h4 y hy (by omega) (by omega) hya
      have hval : n - y = x := by omega
      rw [hval] at this
      exact this hx
  · exact Or.inr (Or.inr (Or.inl heq))
  · by_cases hxa : x = a
    · exact Or.inl hxa
    · exfalso
      have := h4 x hx (by omega) (by omega) hxa
      have hval : n - x = y := by omega
      rw [hval] at this
      exact this hy

theorem strip_reflection {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ y ∈ A, a < y → y < n → n - y ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro y hy hay hyn
  exact h4 y hy (by omega) (by omega) (by omega)

theorem gap_domination_of_empty_strip {A : Set ℕ} {a n a' : ℕ}
    (hown : OwnsTarget A a n)
    (hstrip : ∀ y ∈ A, a < y → y < n → False)
    (ha' : a' ∈ A) (haa' : a < a') (h0 : 0 ∈ A) :
    n - a ≤ a' - a := by
  by_contra hlt
  push Not at hlt
  have hn' : a' < n := by omega
  exact hstrip a' ha' haa' hn'

theorem strip_card_le {A : Set ℕ} [DecidablePred (· ∈ A)] {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ((Finset.Ioo a n).filter (· ∈ A)).card ≤
      ((Finset.Ioo 0 (n - a)).filter (· ∉ A)).card := by
  apply Finset.card_le_card_of_injOn (fun y => n - y)
  · intro y hy
    obtain ⟨hyI, hyA⟩ := Finset.mem_filter.1 hy
    obtain ⟨hay, hyn⟩ := Finset.mem_Ioo.1 hyI
    show n - y ∈ (Finset.Ioo 0 (n - a)).filter (· ∉ A)
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioo.2
      ⟨by omega, by omega⟩, ?_⟩
    exact strip_reflection hown y hyA hay hyn
  · intro y₁ hy₁ y₂ hy₂ heq
    obtain ⟨hy₁I, _⟩ := Finset.mem_filter.1 hy₁
    obtain ⟨_, hy₁n⟩ := Finset.mem_Ioo.1 hy₁I
    obtain ⟨hy₂I, _⟩ := Finset.mem_filter.1 hy₂
    obtain ⟨_, hy₂n⟩ := Finset.mem_Ioo.1 hy₂I
    have heq' : n - y₁ = n - y₂ := heq
    omega

theorem midwindow_reflection {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ y ∈ A, 2 * y > n → y < a → n - y ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro y hy hbig hya
  exact h4 y hy hbig (by omega) (by omega)

theorem cross_marked_element_exclusion {A : Set ℕ} {a₁ a₂ n₁ n₂ : ℕ}
    (h₁ : OwnsTarget A a₁ n₁) (h₂ : OwnsTarget A a₂ n₂)
    (ha : a₁ < a₂) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) :
    (a₂ < n₁ → n₁ - a₂ ∉ A) ∧
    (2 * a₁ > n₂ → n₂ - a₁ ∉ A) := by
  constructor
  · intro hlt
    exact strip_reflection h₁ a₂ ha₂ ha hlt
  · intro hbig
    exact midwindow_reflection h₂ a₁ ha₁ hbig ha

theorem consecutive_marked_element_dichotomy {A : Set ℕ} {a a' n : ℕ}
    (hown : OwnsTarget A a n) (ha' : a' ∈ A) (haa' : a < a') :
    n - a ≤ a' - a ∨
    (a' - a < n - a ∧ (n - a) - (a' - a) ∉ A) := by
  rcases Nat.lt_or_ge (a' - a) (n - a) with h | h
  · right
    refine ⟨h, ?_⟩
    have hlt : a' < n := by omega
    have hval : n - a' = (n - a) - (a' - a) := by omega
    rw [← hval]
    exact strip_reflection hown a' ha' haa' hlt
  · exact Or.inl h

theorem completion_isolation {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    (∀ y ∈ A, a < y → y < n → (n - a) - (y - a) ∉ A) ∧
    (∀ y ∈ A, 2 * y > n → y < a → (n - a) + (a - y) ∉ A) := by
  have h1 := hown.1
  constructor
  · intro y hy hay hyn
    have hval : (n - a) - (y - a) = n - y := by omega
    rw [hval]
    exact strip_reflection hown y hy hay hyn
  · intro y hy hbig hya
    have hval : (n - a) + (a - y) = n - y := by omega
    rw [hval]
    exact midwindow_reflection hown y hy hbig hya

theorem completion_mutual_avoidance {A : Set ℕ} {a₁ n₁ a₂ n₂ : ℕ}
    (h₁ : OwnsTarget A a₁ n₁) (h₂ : OwnsTarget A a₂ n₂) :
    ∀ y ∈ A, a₁ < y → y < n₁ →
      n₂ - a₂ ≠ (n₁ - a₁) - (y - a₁) := by
  intro y hy hay hyn heq
  have hs₂ : n₂ - a₂ ∈ A := h₂.chain_step.1
  have hban := (completion_isolation h₁).1 y hy hay hyn
  rw [← heq] at hban
  exact hban hs₂

theorem midwindow_demand_injection {A : Set ℕ} {y a₁ n₁ a₂ n₂ : ℕ}
    (hy : y ∈ A) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (h₁ : OwnsTarget A a₁ n₁) (h₂ : OwnsTarget A a₂ n₂)
    (hb₁ : 2 * y > n₁) (hs₁ : y < a₁)
    (hb₂ : 2 * y > n₂) (hs₂ : y < a₂)
    (hne : a₁ ≠ a₂) :
    n₁ - y ∉ A ∧ n₂ - y ∉ A ∧ n₁ - y ≠ n₂ - y := by
  refine ⟨midwindow_reflection h₁ y hy hb₁ hs₁,
    midwindow_reflection h₂ y hy hb₂ hs₂, ?_⟩
  have hnn : n₁ ≠ n₂ := by
    intro h
    subst h
    exact hne (h₁.unique_marked_element ha₁ ha₂ h₂ ▸ rfl)
  have hy₁ : y < n₁ := by
    obtain ⟨g1, _, _, _⟩ := h₁
    omega
  have hy₂ : y < n₂ := by
    obtain ⟨g1, _, _, _⟩ := h₂
    omega
  omega

theorem midwindow_column_bound {A : Set ℕ} [DecidablePred (· ∈ A)]
    {y : ℕ} (hy : y ∈ A) (O : Finset ℕ) (t : ℕ → ℕ)
    (hOA : ∀ a ∈ O, a ∈ A)
    (howns : ∀ a ∈ O, OwnsTarget A a (t a))
    (hmid : ∀ a ∈ O, 2 * y > t a ∧ y < a) :
    O.card ≤ ((Finset.Ioo 0 y).filter (· ∉ A)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun a => t a - y)
  · intro a ha
    obtain ⟨hbig, hya⟩ := hmid a ha
    have hown := howns a ha
    have h1 : a < t a := hown.1
    show t a - y ∈ (Finset.Ioo 0 y).filter (· ∉ A)
    refine Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by omega, by omega⟩, ?_⟩
    exact midwindow_reflection hown y hy hbig hya
  · intro a₁ ha₁ a₂ ha₂ heq
    have heq' : t a₁ - y = t a₂ - y := heq
    by_contra hne
    obtain ⟨hb₁, hy₁⟩ := hmid a₁ ha₁
    obtain ⟨hb₂, hy₂⟩ := hmid a₂ ha₂
    have h₁ := howns a₁ ha₁
    have h₂ := howns a₂ ha₂
    have hgt₁ : y < t a₁ := by
      have := h₁.1
      omega
    have hgt₂ : y < t a₂ := by
      have := h₂.1
      omega
    have htt : t a₁ = t a₂ := by omega
    rw [htt] at h₁
    exact hne (h₁.unique_marked_element (hOA a₁ ha₁) (hOA a₂ ha₂) h₂)

theorem zero_payment_bound {A : Set ℕ} {a t : ℕ}
    (hown : OwnsTarget A a t)
    (hpay : ∀ y ∈ A, 2 * y > t → y < t → y = a) :
    (∀ y ∈ A, y < a → 2 * y ≤ t) ∧ (∀ y ∈ A, a < y → t ≤ y) := by
  have h1 : a < t := hown.1
  have h2 : t < 2 * a := hown.2.1
  constructor
  · intro y hy hya
    by_contra hgt
    push Not at hgt
    have := hpay y hy hgt (by omega)
    omega
  · intro y hy hay
    by_contra hlt
    push Not at hlt
    have := hpay y hy (by omega) hlt
    omega

theorem zero_payment_gap_bound {A : Set ℕ} {a t p q : ℕ}
    (hown : OwnsTarget A a t)
    (hpay : ∀ y ∈ A, 2 * y > t → y < t → y = a)
    (hp : p ∈ A) (hplt : p < a) (hq : q ∈ A) (hqgt : a < q) :
    2 * (q - p) > a := by
  obtain ⟨hpred, hsucc⟩ := zero_payment_bound hown hpay
  have h1 := hpred p hp hplt
  have h2 := hsucc q hq hqgt
  have h3 : a < t := hown.1
  have h4 : t < 2 * a := hown.2.1
  omega

theorem no_five_zero_payers {A : Set ℕ} {X : ℕ}
    {x₁ x₂ x₃ x₄ x₅ t₂ t₄ : ℕ}
    (h₁ : x₁ ∈ A) (h₃ : x₃ ∈ A) (h₅ : x₅ ∈ A)
    (ho₂ : OwnsTarget A x₂ t₂) (ho₄ : OwnsTarget A x₄ t₄)
    (hp₂ : ∀ y ∈ A, 2 * y > t₂ → y < t₂ → y = x₂)
    (hp₄ : ∀ y ∈ A, 2 * y > t₄ → y < t₄ → y = x₄)
    (hord : x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧ x₄ < x₅)
    (hoct : X < x₁ ∧ x₅ ≤ 2 * X) :
    False := by
  obtain ⟨h12, h23, h34, h45⟩ := hord
  obtain ⟨hX1, hX5⟩ := hoct
  have hb₂ := zero_payment_gap_bound ho₂ hp₂ h₁ h12 h₃ h23
  have hb₄ := zero_payment_gap_bound ho₄ hp₄ h₃ h34 h₅ h45
  omega

/-- Exponential beats cubic: `D³ ≤ 2^D` from 10 on. -/
lemma cube_le_two_pow {D : ℕ} (hD : 10 ≤ D) : D ^ 3 ≤ 2 ^ D := by
  induction D with
  | zero => omega
  | succ D ih =>
    rcases Nat.lt_or_ge D 10 with h | h
    · have h9 : D = 9 := by omega
      subst h9
      norm_num
    · have h1 := ih h
      have h2 : (D + 1) ^ 3 ≤ 2 * D ^ 3 := by
        have h3 : 3 * D ^ 2 + 3 * D + 1 ≤ D ^ 3 := by
          nlinarith
        nlinarith
      calc (D + 1) ^ 3 ≤ 2 * D ^ 3 := h2
        _ ≤ 2 * 2 ^ D := by omega
        _ = 2 ^ (D + 1) := by ring

theorem octave_rich_of_covering {A : Set ℕ} [DecidablePred (· ∈ A)]
    {N₀ : ℕ} (hcov : PairCovers A N₀) :
    ∀ k₀, ∃ k, k₀ ≤ k ∧
      5 ≤ ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter (· ∈ A)).card := by
  intro k₀
  by_contra hno
  push Not at hno
  -- octave counts ≤ 4 beyond k₀
  have hoct : ∀ k, k₀ ≤ k →
      ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter (· ∈ A)).card ≤ 4 := by
    intro k hk
    have := hno k hk
    omega
  set cnt : ℕ → ℕ := fun k =>
    ((Finset.range (2 ^ k + 1)).filter (· ∈ A)).card with hcnt
  have hstep : ∀ k, k₀ ≤ k → cnt (k + 1) ≤ cnt k + 4 := by
    intro k hk
    have hsplit : Finset.range (2 ^ (k + 1) + 1) =
        Finset.range (2 ^ k + 1) ∪ Finset.Ioc (2 ^ k) (2 ^ (k + 1)) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]
      have h1 : 2 ^ k < 2 ^ (k + 1) := by
        have h2 : (2:ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have h3 : 0 < 2 ^ k := Nat.two_pow_pos k
        omega
      omega
    have hcard : cnt (k + 1) ≤ cnt k +
        ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter (· ∈ A)).card := by
      rw [hcnt]
      simp only
      rw [hsplit, Finset.filter_union]
      exact Finset.card_union_le _ _
    have := hoct k hk
    omega
  have hlin : ∀ j, cnt (k₀ + j) ≤ cnt k₀ + 4 * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 := hstep (k₀ + j) (by omega)
      have h2 : k₀ + (j + 1) = (k₀ + j) + 1 := by omega
      rw [h2]
      omega
  -- the vise at W := 2^(k₀+j)
  have hvise : ∀ j, 2 ^ (k₀ + j) + 1 - N₀ ≤ (cnt k₀ + 4 * j) ^ 2 := by
    intro j
    have hW : N₀ ≤ 2 ^ (k₀ + j) ∨ 2 ^ (k₀ + j) < N₀ := by omega
    rcases hW with hW | hW
    · have h1 := pairCovers_card_lower (W := 2 ^ (k₀ + j)) hcov hW
      have h2 := hlin j
      have h3 : ((Finset.range (2 ^ (k₀ + j) + 1)).filter
          (· ∈ A)).card ≤ cnt k₀ + 4 * j := h2
      calc 2 ^ (k₀ + j) + 1 - N₀ ≤
          ((Finset.range (2 ^ (k₀ + j) + 1)).filter (· ∈ A)).card ^ 2 := h1
        _ ≤ (cnt k₀ + 4 * j) ^ 2 := Nat.pow_le_pow_left h3 2
    · omega
  -- exponential beats the quadratic: contradiction at large j
  set C := cnt k₀ + N₀ + 5 with hC
  have hbig : ∃ j, 72 ≤ j ∧ C ≤ j ∧ k₀ ≤ j :=
    ⟨72 + C + k₀, by omega, by omega, by omega⟩
  obtain ⟨j, hj72, hjC, hjk⟩ := hbig
  have h1 := hvise j
  have hquad : (cnt k₀ + 4 * j) ^ 2 ≤ 25 * j ^ 2 := by
    have h5j : cnt k₀ + 4 * j ≤ 5 * j := by omega
    calc (cnt k₀ + 4 * j) ^ 2 ≤ (5 * j) ^ 2 := Nat.pow_le_pow_left h5j 2
      _ = 25 * j ^ 2 := by ring
  have hcube : 50 * j ^ 2 ≤ j ^ 3 := by nlinarith
  have hpow := cube_le_two_pow (D := j) (by omega)
  have hexp : 2 ^ j ≤ 2 ^ (k₀ + j) := Nat.pow_le_pow_right (by norm_num)
    (by omega)
  have hQ1 : 1 ≤ j ^ 2 := by nlinarith
  have hjQ : j ≤ j ^ 2 := by nlinarith
  have hN : N₀ ≤ j := by omega
  omega

theorem paying_marked_element_in_rich_octave {A : Set ℕ}
    [DecidablePred (. ∈ A)] {Ns X : ℕ}
    (huniv : UniversalTargetOwnership A Ns) (hXNs : Ns ≤ X)
    (hcard : 5 ≤ ((Finset.Ioc X (2 * X)).filter (. ∈ A)).card) :
    ∃ a t y, a ∈ A ∧ X < a ∧ OwnsTarget A a t ∧
      y ∈ A ∧ 2 * y > t ∧ y < t ∧ y ≠ a := by
  classical
  set F := (Finset.Ioc X (2 * X)).filter (. ∈ A) with hF
  have hne0 : F.Nonempty := Finset.card_pos.1 (by omega)
  set x1 := F.min' hne0 with hx1
  have hm1 : x1 ∈ F := F.min'_mem hne0
  set F1 := F.erase x1 with hFa
  have hc1 : F1.card = F.card - 1 := Finset.card_erase_of_mem hm1
  have hne1 : F1.Nonempty := Finset.card_pos.1 (by omega)
  set x2 := F1.min' hne1 with hx2
  have hm2a : x2 ∈ F1 := F1.min'_mem hne1
  have hm2 : x2 ∈ F := Finset.mem_of_mem_erase hm2a
  have h12 : x1 < x2 := by
    have hle := F.min'_le x2 hm2
    have hne := Finset.ne_of_mem_erase hm2a
    omega
  set F2 := F1.erase x2 with hFb
  have hc2 : F2.card = F1.card - 1 := Finset.card_erase_of_mem hm2a
  have hne2 : F2.Nonempty := Finset.card_pos.1 (by omega)
  set x3 := F2.min' hne2 with hx3
  have hm3b : x3 ∈ F2 := F2.min'_mem hne2
  have hm3a : x3 ∈ F1 := Finset.mem_of_mem_erase hm3b
  have hm3 : x3 ∈ F := Finset.mem_of_mem_erase hm3a
  have h23 : x2 < x3 := by
    have hle := F1.min'_le x3 hm3a
    have hne := Finset.ne_of_mem_erase hm3b
    omega
  set F3 := F2.erase x3 with hFc
  have hc3 : F3.card = F2.card - 1 := Finset.card_erase_of_mem hm3b
  have hne3 : F3.Nonempty := Finset.card_pos.1 (by omega)
  set x4 := F3.min' hne3 with hx4
  have hm4c : x4 ∈ F3 := F3.min'_mem hne3
  have hm4b : x4 ∈ F2 := Finset.mem_of_mem_erase hm4c
  have hm4a : x4 ∈ F1 := Finset.mem_of_mem_erase hm4b
  have hm4 : x4 ∈ F := Finset.mem_of_mem_erase hm4a
  have h34 : x3 < x4 := by
    have hle := F2.min'_le x4 hm4b
    have hne := Finset.ne_of_mem_erase hm4c
    omega
  set F4 := F3.erase x4 with hFd
  have hc4 : F4.card = F3.card - 1 := Finset.card_erase_of_mem hm4c
  have hne4 : F4.Nonempty := Finset.card_pos.1 (by omega)
  set x5 := F4.min' hne4 with hx5
  have hm5d : x5 ∈ F4 := F4.min'_mem hne4
  have hm5c : x5 ∈ F3 := Finset.mem_of_mem_erase hm5d
  have hm5 : x5 ∈ F := Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hm5c))
  have h45 : x4 < x5 := by
    have hle := F3.min'_le x5 hm5c
    have hne := Finset.ne_of_mem_erase hm5d
    omega
  have hFmem : ∀ x, x ∈ F → x ∈ A ∧ X < x ∧ x ≤ 2 * X := by
    intro x hx
    rw [hF] at hx
    obtain ⟨hI, hA⟩ := Finset.mem_filter.1 hx
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hI
    exact ⟨hA, h1, h2⟩
  obtain ⟨hA1, hX1, hU1⟩ := hFmem x1 hm1
  obtain ⟨hA2, hX2, hU2⟩ := hFmem x2 hm2
  obtain ⟨hA3, hX3, hU3⟩ := hFmem x3 hm3
  obtain ⟨hA4, hX4, hU4⟩ := hFmem x4 hm4
  obtain ⟨hA5, hX5, hU5⟩ := hFmem x5 hm5
  obtain ⟨t2, ho2⟩ := huniv x2 hA2 (by omega)
  obtain ⟨t4, ho4⟩ := huniv x4 hA4 (by omega)
  by_contra hno
  push Not at hno
  have hp2 : ∀ y ∈ A, 2 * y > t2 → y < t2 → y = x2 := by
    intro y hy hby hyt
    exact hno x2 t2 y hA2 hX2 ho2 hy hby hyt
  have hp4 : ∀ y ∈ A, 2 * y > t4 → y < t4 → y = x4 := by
    intro y hy hby hyt
    exact hno x4 t4 y hA4 hX4 ho4 hy hby hyt
  exact no_five_zero_payers hA1 hA3 hA5 ho2 ho4 hp2 hp4
    ⟨h12, h23, h34, h45⟩ ⟨hX1, hU5⟩

theorem paying_marked_elements_cofinal {A : Set ℕ} [DecidablePred (· ∈ A)]
    {N₀ Ns : ℕ} (hcov : PairCovers A N₀)
    (huniv : UniversalTargetOwnership A Ns) :
    ∀ M, ∃ a t y, M ≤ a ∧ a ∈ A ∧ OwnsTarget A a t ∧
      y ∈ A ∧ 2 * y > t ∧ y < t ∧ y ≠ a := by
  intro M
  obtain ⟨k, hk, hrich⟩ := octave_rich_of_covering hcov (M + Ns)
  have hpow : M + Ns < 2 ^ k := by
    have h1 : M + Ns < 2 ^ (M + Ns) := Nat.lt_two_pow_self
    have h2 : 2 ^ (M + Ns) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hrich' : 5 ≤ ((Finset.Ioc (2 ^ k) (2 * 2 ^ k)).filter
      (· ∈ A)).card := by
    have hpk : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rwa [hpk] at hrich
  obtain ⟨a, t, y, haA, haX, hown, hyA, hby, hyt, hya⟩ :=
    paying_marked_element_in_rich_octave (X := 2 ^ k) huniv (by omega) hrich'
  exact ⟨a, t, y, by omega, haA, hown, hyA, hby, hyt, hya⟩

theorem payment_demand {A : Set ℕ} {a t y : ℕ}
    (hown : OwnsTarget A a t)
    (hy : y ∈ A) (hby : 2 * y > t) (hyt : y < t) (hya : y ≠ a) :
    t - y ∉ A ∧ 0 < t - y ∧ 2 * (t - y) < t := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  exact ⟨h4 y hy hby (by omega) hya, by omega, by omega⟩

theorem payer_in_five {A : Set ℕ} {Ns X x₁ x₂ x₃ x₄ x₅ : ℕ}
    (huniv : UniversalTargetOwnership A Ns) (hXNs : Ns ≤ X)
    (h₁ : x₁ ∈ A) (h₂ : x₂ ∈ A) (h₃ : x₃ ∈ A) (h₄ : x₄ ∈ A)
    (h₅ : x₅ ∈ A)
    (hord : x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧ x₄ < x₅)
    (hoct : X < x₁ ∧ x₅ ≤ 2 * X) :
    ∃ a t y, (a = x₂ ∨ a = x₄) ∧ OwnsTarget A a t ∧
      y ∈ A ∧ 2 * y > t ∧ y < t ∧ y ≠ a := by
  obtain ⟨t₂, ho₂⟩ := huniv x₂ h₂ (by omega)
  obtain ⟨t₄, ho₄⟩ := huniv x₄ h₄ (by omega)
  by_contra hno
  push Not at hno
  have hp₂ : ∀ y ∈ A, 2 * y > t₂ → y < t₂ → y = x₂ := by
    intro y hy hby hyt
    exact hno x₂ t₂ y (Or.inl rfl) ho₂ hy hby hyt
  have hp₄ : ∀ y ∈ A, 2 * y > t₄ → y < t₄ → y = x₄ := by
    intro y hy hby hyt
    exact hno x₄ t₄ y (Or.inr rfl) ho₄ hy hby hyt
  exact no_five_zero_payers h₁ h₃ h₅ ho₂ ho₄ hp₂ hp₄ hord hoct

theorem ownership_forest {A : Set ℕ} {Ns : ℕ}
    (huniv : UniversalTargetOwnership A Ns) :
    ∃ parent : ℕ → ℕ, ∀ a ∈ A, Ns ≤ a →
      parent a ∈ A ∧ parent a < a ∧
      OwnsTarget A a (a + parent a) := by
  classical
  choose f hf using huniv
  refine ⟨fun a => if h : a ∈ A ∧ Ns ≤ a then f a h.1 h.2 - a else 0,
    fun a haA haNs => ?_⟩
  have hown := hf a haA haNs
  have h1 : a < f a haA haNs := hown.1
  have h2 : f a haA haNs < 2 * a := hown.2.1
  have h3 : f a haA haNs - a ∈ A := hown.2.2.1
  simp only [dif_pos (And.intro haA haNs)]
  refine ⟨h3, by omega, ?_⟩
  have hval : a + (f a haA haNs - a) = f a haA haNs := by omega
  rw [hval]
  exact hown

theorem star_exclusion {A : Set ℕ} {w a b : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hb : b ∈ A) (hbig : 2 * b > a + w) (hlt : b < a + w)
    (hba : b ≠ a) :
    a + w - b ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  exact h4 b hb hbig (by omega) hba

theorem parent_double_exclusion {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hdiff : a - w ∈ A) (hreach : 3 * w < a) :
    2 * w ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  have hw1 : 1 ≤ w := by omega
  have hval : a + w - (a - w) = 2 * w := by omega
  have := h4 (a - w) hdiff (by omega) (by omega) (by omega)
  rwa [hval] at this

theorem child_reach_dichotomy {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w)) (hdiff : a - w ∈ A) :
    a ≤ 3 * w ∨ 2 * w ∉ A := by
  rcases Nat.lt_or_ge (3 * w) a with h | h
  · exact Or.inr (parent_double_exclusion hown hdiff h)
  · exact Or.inl h

theorem edge_exclusion_law {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hne2 : a ≠ 2 * w) (hne3 : a ≠ 3 * w) :
    ¬((a - w) ∈ A ∧ 2 * w ∈ A) := by
  rintro ⟨hd, h2w⟩
  have h1 : a < a + w := hown.1
  rcases Nat.lt_or_ge (3 * w) a with h | h
  · exact parent_double_exclusion hown hd h h2w
  · obtain ⟨g1, g2, g3, g4⟩ := hown
    have := g4 (2 * w) h2w (by omega) (by omega) (by omega)
    have hval : a + w - 2 * w = a - w := by omega
    rw [hval] at this
    exact this hd

theorem edge_tax {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hne2 : a ≠ 2 * w) (hne3 : a ≠ 3 * w) :
    2 * w ∉ A ∨ a - w ∉ A := by
  by_contra h
  push Not at h
  exact edge_exclusion_law hown hne2 hne3 ⟨h.2, h.1⟩

theorem split_children_inject {w a b : ℕ}
    (hab : a ≠ b) : a - w ≠ b - w ∨ a ≤ w ∨ b ≤ w := by
  rcases Nat.lt_or_ge w a with ha | ha
  · rcases Nat.lt_or_ge w b with hb | hb
    · left
      omega
    · right
      right
      omega
  · right
    left
    omega

theorem block_domination {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w)) (hreach : 3 * w < a) :
    2 * w < a - w := by
  have h1 : a < a + w := hown.1
  omega

theorem covering_gap_bound {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ x, ∃ a ∈ A, x < a ∧ a ≤ 2 * x + N₀ + 1 := by
  intro x
  obtain ⟨p, hp, q, hq, hpq⟩ := hcov (2 * x + N₀ + 1) (by omega)
  rcases Nat.lt_or_ge x p with h | h
  · exact ⟨p, hp, h, by omega⟩
  · refine ⟨q, hq, by omega, by omega⟩

theorem shared_block_parent_sieve {A : Set ℕ} {b w w' : ℕ}
    (hown : OwnsTarget A (b + w) (b + w + w))
    (ha' : b + w' ∈ A)
    (hbig : 2 * (b + w') > b + w + w)
    (hlt : b + w' < b + w + w) (hne : w' ≠ w) :
    2 * w - w' ∉ A := by
  have h := star_exclusion (w := w) (a := b + w) hown ha' hbig hlt
    (by omega)
  have hval : b + w + w - (b + w') = 2 * w - w' := by omega
  rwa [hval] at h

theorem cross_block_exclusion {A : Set ℕ} {b w b' w' : ℕ}
    (hown : OwnsTarget A (b + w) (b + w + w))
    (ha' : b' + w' ∈ A)
    (hbig : 2 * (b' + w') > b + w + w)
    (hlt : b' + w' < b + w + w) (hne : b' + w' ≠ b + w) :
    b + 2 * w - b' - w' ∉ A := by
  have h := star_exclusion (w := w) (a := b + w) hown ha' hbig hlt hne
  have hval : b + w + w - (b' + w') = b + 2 * w - b' - w' := by omega
  rwa [hval] at h

theorem boundary_exclusion {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (h3w : 3 * w ∈ A) (hlow : 2 * w < a) (hhigh : a < 5 * w)
    (hne : a ≠ 3 * w) :
    a - 2 * w ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  have h := h4 (3 * w) h3w (by omega) (by omega) (by omega)
  have hval : a + w - 3 * w = a - 2 * w := by omega
  rwa [hval] at h

theorem two_marker_near_rigidity {A B : Set ℕ} {b₁ b₂ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 2 * b₂ →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (honly : ∀ x ∈ B, x ≤ 2 * b₂ → x = b₁ ∨ x = b₂) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b₂ →
      (x = b₂ ∧ y = b₂) ∨ x = b₁ ∨ y = b₁ := by
  intro x hx y hy hxy
  rcases hdead x hx y hy 0 h0 (by omega) with h | h | h
  · rcases honly x h (by omega) with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inl ⟨h', by omega⟩
  · rcases honly y h (by omega) with h' | h'
    · exact Or.inr (Or.inr h')
    · exact Or.inl ⟨by omega, h'⟩
  · exact absurd h h0B

theorem unbounded_avoidance {A : Set ℕ}
    (hunb : ∀ X, ∃ a ∈ A, X ≤ a) (E : Finset ℕ) :
    ∀ X, ∃ a ∈ A, X ≤ a ∧ a ∉ E := by
  intro X
  obtain ⟨a, ha, hX⟩ := hunb (max X (E.sup id + 1))
  refine ⟨a, ha, le_trans (le_max_left _ _) hX, ?_⟩
  intro hmem
  have h1 : a ≤ E.sup id := Finset.le_sup (f := id) hmem
  have h2 : E.sup id + 1 ≤ a := le_trans (le_max_right _ _) hX
  omega

theorem failing_double_fiber_bound {A B : Set ℕ} {b : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 2 * b →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = 2 * b → x ∈ B ∨ y ∈ B := by
  intro x hx y hy hxy
  rcases hdead x hx y hy 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0B

theorem richness_gives_reflection {A : Set ℕ} {b X : ℕ}
    (hrich : ∀ a ∈ A, X ≤ a → a < 2 * b → 2 * b - a ∈ A) :
    ∀ a ∈ A, X ≤ a → a < 2 * b → a ≠ b →
      ∃ p ∈ A, ∃ q ∈ A, p + q = 2 * b ∧ p ≠ b := by
  intro a ha hXa hab hane
  refine ⟨a, ha, 2 * b - a, hrich a ha hXa hab, by omega, hane⟩

theorem fails_iff_support_transversal_subset {A B : Set ℕ} {n : ℕ}
    [DecidablePred (· ∈ B)] :
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) ↔
    ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ ∀ h ∈ H, h ∈ B := by
  constructor
  · intro hdead
    refine ⟨(Finset.range (n + 1)).filter (· ∈ B),
      failing_support_transversal_subset_deletion hdead, ?_⟩
    intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rintro ⟨H, hhub, hHB⟩ x hx y hy z hz hsum
    rcases hhub x hx y hy z hz hsum with h | h | h
    · exact Or.inl (hHB x h)
    · exact Or.inr (Or.inl (hHB y h))
    · exact Or.inr (Or.inr (hHB z h))

theorem avoidance_or_obstruction {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ A) ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a := by
  classical
  by_contra hnotrap
  push Not at hnotrap
  have hpick : ∀ (F : Finset ℕ) (X : ℕ), ∃ a, a ∈ A ∧ X ≤ a ∧
      ((∀ h ∈ F, h ∈ A) →
        ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ a ∈ H ∧
          ∀ h ∈ H, h ∈ F ∨ h = a) := by
    intro F X
    by_cases hFA : ∀ h ∈ F, h ∈ A
    · obtain ⟨a, ha, hXa, hno⟩ := hnotrap F hFA X
      refine ⟨a, ha, hXa, fun _ => ?_⟩
      rintro ⟨n, hnN, H, hhub, haH, hsub⟩
      obtain ⟨h, hhH, hhF, hha⟩ := hno n hnN H hhub haH
      rcases hsub h hhH with h' | h'
      · exact hhF h'
      · exact hha h'
    · obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov X
      exact ⟨a, ha, hXa, fun h => absurd h hFA⟩
  choose pick hpickA hpickge hpickdodge using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 0, {pick ∅ 0})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hst0 : st 0 = (pick ∅ 0, {pick ∅ 0}) := rfl
  have hPA : ∀ j, ∀ h ∈ (st j).2, h ∈ A := by
    intro j
    induction j with
    | zero =>
      intro h hh
      rw [hst0] at hh
      have he : h = pick ∅ 0 := Finset.mem_singleton.1 hh
      rw [he]
      exact hpickA ∅ 0
    | succ j ih =>
      intro h hh
      rw [hstS j] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact hpickA _ _
      · exact ih h h'
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero =>
      rw [hst0]
      exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS j]
      exact Finset.mem_insert_self _ _
  have hchain : ∀ j k, j ≤ k → (st j).2 ⊆ (st k).2 := by
    intro j k hjk
    induction k with
    | zero =>
      have hj0 : j = 0 := by omega
      rw [hj0]
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS k]
        exact Finset.subset_insert _ _
      · have hjk1 : j = k + 1 := by omega
        rw [hjk1]
  have hinv : ∀ j, ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
      H.Nonempty ∧ ∀ h ∈ H, h ∈ (st j).2 := by
    intro j
    induction j with
    | zero =>
      rintro ⟨n, hnN, H, hhub, ⟨x, hx⟩, hsub⟩
      have hx0 : x = pick ∅ 0 := by
        have := hsub x hx
        rw [hst0] at this
        exact Finset.mem_singleton.1 this
      refine hpickdodge ∅ 0 (by simp) ⟨n, hnN, H, hhub, ?_, ?_⟩
      · rw [← hx0]
        exact hx
      · intro h hh
        have := hsub h hh
        rw [hst0] at this
        exact Or.inr (Finset.mem_singleton.1 this)
    | succ j ih =>
      rintro ⟨n, hnN, H, hhub, hne, hsub⟩
      by_cases haH : pick (st j).2 ((st j).1 + 1) ∈ H
      · refine hpickdodge (st j).2 ((st j).1 + 1) (hPA j)
          ⟨n, hnN, H, hhub, haH, ?_⟩
        intro h hh
        have := hsub h hh
        rw [hstS j] at this
        rcases Finset.mem_insert.1 this with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · refine ih ⟨n, hnN, H, hhub, hne, ?_⟩
        intro h hh
        have := hsub h hh
        rw [hstS j] at this
        rcases Finset.mem_insert.1 this with h' | h'
        · exact absurd (h' ▸ hh) haH
        · exact h'
  set B : Set ℕ := {x | ∃ j, x ∈ (st j).2} with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, hj⟩
    exact hPA j x hj
  have hBinf : B.Infinite := by
    have hmono : StrictMono fun j => (st j).1 := by
      apply strictMono_nat_of_lt_succ
      intro j
      have h1 := hpickge (st j).2 ((st j).1 + 1)
      have h2 : (st (j+1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS j]
      show (st j).1 < (st (j+1)).1
      omega
    apply Set.infinite_of_injective_forall_mem
      (f := fun j => (st j).1) hmono.injective
    intro j
    exact ⟨j, hlastmem j⟩
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N0
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push Not at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hdec : DecidablePred (· ∈ B) := fun _ => Classical.propDecidable _
  have hhub := failing_support_transversal_subset_deletion (B := B) hdead
  set H : Finset ℕ := (Finset.range (n + 1)).filter (· ∈ B) with hH
  have hHne : H.Nonempty := support_transversal_nonempty_of_covering h0 hcov hnN hhub
  have hstage : ∀ h ∈ H, ∃ j, h ∈ (st j).2 := by
    intro h hh
    exact (Finset.mem_filter.1 hh).2
  choose stg hstg using hstage
  set J := H.sup (fun h => if hh : h ∈ H then stg h hh else 0) with hJ
  have hHsub : ∀ h ∈ H, h ∈ (st J).2 := by
    intro h hh
    have h1 : stg h hh ≤ J := by
      have := Finset.le_sup (f := fun h' =>
        if hh' : h' ∈ H then stg h' hh' else 0) hh
      simpa [hh] using this
    exact hchain (stg h hh) J h1 (hstg h hh)
  exact hinv J ⟨n, hnN, H, hhub, hHne, hHsub⟩

theorem avoidance_or_obstruction_pool {P A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ P) ∧ ∃ X, ∀ a ∈ P, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a := by
  classical
  by_contra hnotrap
  push Not at hnotrap
  have hpick : ∀ (F : Finset ℕ) (X : ℕ), ∃ a, a ∈ P ∧ X ≤ a ∧
      ((∀ h ∈ F, h ∈ P) →
        ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ a ∈ H ∧
          ∀ h ∈ H, h ∈ F ∨ h = a) := by
    intro F X
    by_cases hFA : ∀ h ∈ F, h ∈ P
    · obtain ⟨a, ha, hXa, hno⟩ := hnotrap F hFA X
      refine ⟨a, ha, hXa, fun _ => ?_⟩
      rintro ⟨n, hnN, H, hhub, haH, hsub⟩
      obtain ⟨h, hhH, hhF, hha⟩ := hno n hnN H hhub haH
      rcases hsub h hhH with h' | h'
      · exact hhF h'
      · exact hha h'
    · obtain ⟨a, ha, hXa⟩ := hunb X
      exact ⟨a, ha, hXa, fun h => absurd h hFA⟩
  choose pick hpickA hpickge hpickdodge using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 0, {pick ∅ 0})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hst0 : st 0 = (pick ∅ 0, {pick ∅ 0}) := rfl
  have hstP : ∀ j, ∀ h ∈ (st j).2, h ∈ P := by
    intro j
    induction j with
    | zero =>
      intro h hh
      rw [hst0] at hh
      have he : h = pick ∅ 0 := Finset.mem_singleton.1 hh
      rw [he]
      exact hpickA ∅ 0
    | succ j ih =>
      intro h hh
      rw [hstS j] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact hpickA _ _
      · exact ih h h'
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero =>
      rw [hst0]
      exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS j]
      exact Finset.mem_insert_self _ _
  have hchain : ∀ j k, j ≤ k → (st j).2 ⊆ (st k).2 := by
    intro j k hjk
    induction k with
    | zero =>
      have hj0 : j = 0 := by omega
      rw [hj0]
    | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS k]
        exact Finset.subset_insert _ _
      · have hjk1 : j = k + 1 := by omega
        rw [hjk1]
  have hinv : ∀ j, ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
      H.Nonempty ∧ ∀ h ∈ H, h ∈ (st j).2 := by
    intro j
    induction j with
    | zero =>
      rintro ⟨n, hnN, H, hhub, ⟨x, hx⟩, hsub⟩
      have hx0 : x = pick ∅ 0 := by
        have := hsub x hx
        rw [hst0] at this
        exact Finset.mem_singleton.1 this
      refine hpickdodge ∅ 0 (by simp) ⟨n, hnN, H, hhub, ?_, ?_⟩
      · rw [← hx0]
        exact hx
      · intro h hh
        have := hsub h hh
        rw [hst0] at this
        exact Or.inr (Finset.mem_singleton.1 this)
    | succ j ih =>
      rintro ⟨n, hnN, H, hhub, hne, hsub⟩
      by_cases haH : pick (st j).2 ((st j).1 + 1) ∈ H
      · refine hpickdodge (st j).2 ((st j).1 + 1) (hstP j)
          ⟨n, hnN, H, hhub, haH, ?_⟩
        intro h hh
        have := hsub h hh
        rw [hstS j] at this
        rcases Finset.mem_insert.1 this with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
      · refine ih ⟨n, hnN, H, hhub, hne, ?_⟩
        intro h hh
        have := hsub h hh
        rw [hstS j] at this
        rcases Finset.mem_insert.1 this with h' | h'
        · exact absurd (h' ▸ hh) haH
        · exact h'
  set B : Set ℕ := {x | ∃ j, x ∈ (st j).2} with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, hj⟩
    exact hPA (hstP j x hj)
  have hBinf : B.Infinite := by
    have hmono : StrictMono fun j => (st j).1 := by
      apply strictMono_nat_of_lt_succ
      intro j
      have h1 := hpickge (st j).2 ((st j).1 + 1)
      have h2 : (st (j+1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS j]
      show (st j).1 < (st (j+1)).1
      omega
    apply Set.infinite_of_injective_forall_mem
      (f := fun j => (st j).1) hmono.injective
    intro j
    exact ⟨j, hlastmem j⟩
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N0
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push Not at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hdec : DecidablePred (· ∈ B) := fun _ => Classical.propDecidable _
  have hhub := failing_support_transversal_subset_deletion (B := B) hdead
  set H : Finset ℕ := (Finset.range (n + 1)).filter (· ∈ B) with hH
  have hHne : H.Nonempty := support_transversal_nonempty_of_covering h0 hcov hnN hhub
  have hstage : ∀ h ∈ H, ∃ j, h ∈ (st j).2 := by
    intro h hh
    exact (Finset.mem_filter.1 hh).2
  choose stg hstg using hstage
  set J := H.sup (fun h => if hh : h ∈ H then stg h hh else 0) with hJ
  have hHsub : ∀ h ∈ H, h ∈ (st J).2 := by
    intro h hh
    have h1 : stg h hh ≤ J := by
      have := Finset.le_sup (f := fun h' =>
        if hh' : h' ∈ H then stg h' hh' else 0) hh
      simpa [hh] using this
    exact hchain (stg h hh) J h1 (hstg h hh)
  exact hinv J ⟨n, hnN, H, hhub, hHne, hHsub⟩

theorem obstruction_level {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ Y, ∃ (F : Finset ℕ) (X : ℕ),
      (∀ h ∈ F, h ∈ A ∧ Y ≤ h) ∧ Y ≤ X ∧
      ∀ a ∈ A, X ≤ a → ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ a ∈ H ∧ ∀ h ∈ H, h ∈ F ∨ h = a := by
  intro Y
  have hPA : {a | a ∈ A ∧ Y ≤ a} ⊆ A := fun a ha => ha.1
  have hunb : ∀ X, ∃ p ∈ {a | a ∈ A ∧ Y ≤ a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X Y)
    exact ⟨a, ⟨ha, le_trans (le_max_right _ _) hXa⟩,
      le_trans (le_max_left _ _) hXa⟩
  obtain ⟨F, hFP, X, htrap⟩ :=
    avoidance_or_obstruction_pool (P := {a | a ∈ A ∧ Y ≤ a}) h0 hcov hPA hunb hfail
  refine ⟨F, max X Y, fun h hh => ⟨(hFP h hh).1, (hFP h hh).2⟩,
    le_max_right _ _, ?_⟩
  intro a ha hXa
  exact htrap a ⟨ha, le_trans (le_max_right _ _) hXa⟩
    (le_trans (le_max_left _ _) hXa)

theorem obstruction_tower {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ) (X : ℕ → ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i ≤ X i) ∧
      (∀ i, X i < Y (i + 1)) ∧
      (∀ i, ∀ h ∈ F i, h < Y (i + 1)) ∧
      (∀ i, ∀ a ∈ A, X i ≤ a → ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ a ∈ H ∧ ∀ h ∈ H, h ∈ F i ∨ h = a) := by
  classical
  choose Ft Xt hFt hXt htrapt using obstruction_level h0 hcov hfail
  set Y : ℕ → ℕ := fun i =>
    Nat.rec (N0 + 1) (fun _ prev =>
      max (Xt prev) ((Ft prev).sup id) + 1) i with hY
  have hYS : ∀ i, Y (i + 1) = max (Xt (Y i)) ((Ft (Y i)).sup id) + 1 :=
    fun _ => rfl
  refine ⟨Y, fun i => Ft (Y i), fun i => Xt (Y i),
    fun i => hFt (Y i), fun i => hXt (Y i), ?_, ?_,
    fun i => htrapt (Y i)⟩
  · intro i
    show Xt (Y i) < Y (i + 1)
    rw [hYS i]
    have := Nat.le_max_left (Xt (Y i)) ((Ft (Y i)).sup id)
    omega
  · intro i h hh
    show h < Y (i + 1)
    rw [hYS i]
    have h1 : h ≤ (Ft (Y i)).sup id := Finset.le_sup (f := id) hh
    have h2 := Nat.le_max_right (Xt (Y i)) ((Ft (Y i)).sup id)
    omega

theorem grand_dichotomy {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ F : Finset ℕ, ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a) ∨
    (∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i < Y (i + 1)) ∧
      ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
        (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
        ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) := by
  classical
  obtain ⟨Y, F, X, hFA, hYX, hXY, hFY, htrap⟩ :=
    obstruction_tower h0 hcov hfail
  by_cases hflood : ∃ i, ∀ M, ∃ a, a ∈ A ∧ M ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F i ∨ h = a
  · left
    obtain ⟨i, hi⟩ := hflood
    exact ⟨F i, hi⟩
  · right
    push Not at hflood
    refine ⟨Y, F, hFA, ?_, ?_⟩
    · intro i
      have h1 := hYX i
      have h2 := hXY i
      omega
    · intro i
      obtain ⟨M, hM⟩ := hflood i
      obtain ⟨a, ha, haM⟩ := pairCovers_unbounded hcov
        (max M (X i))
      have haX : X i ≤ a := le_trans (le_max_right _ _) haM
      obtain ⟨n, hnN, H, hhub, haH, hsub⟩ := htrap i a ha haX
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
      have hH'ne : H'.Nonempty :=
        support_transversal_nonempty_of_covering h0 hcov hnN hH'hub
      have haH' : a ∉ H' := by
        intro haH'
        obtain ⟨h, hh, hhF, hha⟩ := hM a ha
          (le_trans (le_max_left _ _) haM) n hnN H' hH'hub hH'min haH'
        rcases hsub h (hH'sub hh) with h' | h'
        · exact hhF h'
        · exact hha h'
      have hH'F : ∀ h ∈ H', h ∈ F i := by
        intro h hh
        rcases hsub h (hH'sub hh) with h' | h'
        · exact h'
        · exact absurd (h' ▸ hh) haH'
      -- targets march: a necessary element is hit, so n ≥ its size ≥ Y i
      obtain ⟨h₀, hh₀⟩ := hH'ne
      obtain ⟨x, hx, y, hy, z, hz, hsum, hhit, -⟩ :=
        minimal_support_transversal_necessity hH'hub hH'min h₀ hh₀
      have hh₀n : h₀ ≤ n := by
        rcases hhit with h' | h' | h' <;> omega
      have hh₀Y : Y i ≤ h₀ := (hFA i h₀ (hH'F h₀ hh₀)).2
      exact ⟨n, hnN, by omega, H', hH'F, ⟨h₀, hh₀⟩, hH'hub, hH'min⟩

theorem tower_pair_transversals_card {A : Set ℕ} {N0 C : ℕ} {Y : ℕ → ℕ}
    {F : ℕ → Finset ℕ}
    (hY1 : 1 ≤ Y 0)
    (hFA : ∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h)
    (hYmono : ∀ i, Y i < Y (i + 1))
    (hCb : ∀ i, (F i).card ≤ C)
    (hteams : ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
      (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
      ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) :
    ∃ c, 1 ≤ c ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}) := by
  classical
  have hmono : StrictMono Y := strictMono_nat_of_lt_succ hYmono
  have hY1i : ∀ i, 1 ≤ Y i := by
    intro i
    have h0 : Y 0 ≤ Y i := hmono.monotone (Nat.zero_le i)
    omega
  have hYunb : ∀ N, ∃ i, N ≤ Y i := by
    intro N
    refine ⟨N, ?_⟩
    have := hmono.le_apply (x := N)
    omega
  have hP : ∀ N, ∃ n, N ≤ n ∧ ∃ c, c ≤ C ∧
      (∃ H : Finset ℕ, H.card = c ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
        ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) := by
    intro N
    obtain ⟨i, hiN⟩ := hYunb N
    obtain ⟨n, hnN, hnY, H, hHF, hHne, hhub, hmin⟩ := hteams i
    have hcard : H.card ≤ C := by
      calc H.card ≤ (F i).card :=
        Finset.card_le_card (fun h hh => hHF h hh)
        _ ≤ C := hCb i
    refine ⟨n, by omega, H.card, hcard, H, rfl, hHne, hhub, ?_, hmin⟩
    intro h hh
    have h1 := hFA i h (hHF h hh)
    have h2 := hY1i i
    exact ⟨h1.1, by omega⟩
  obtain ⟨c, hc, hcof⟩ := cofinal_value_pigeonhole
    (P := fun n c => ∃ H : Finset ℕ, H.card = c ∧ H.Nonempty ∧
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) hP
  refine ⟨c, ?_, hcof⟩
  obtain ⟨n, -, H, hHc, hHne, -⟩ := hcof 0
  have := Finset.card_pos.2 hHne
  omega

theorem tower_pair_transversals_ge_two {A : Set ℕ} {N0 C : ℕ} {Y : ℕ → ℕ}
    {F : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hanchor : StreamSurvives A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hY1 : 1 ≤ Y 0)
    (hFA : ∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h)
    (hYmono : ∀ i, Y i < Y (i + 1))
    (hCb : ∀ i, (F i).card ≤ C)
    (hteams : ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
      (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
      ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) :
    ∃ c, 2 ≤ c ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}) := by
  obtain ⟨c, hc1, hcof⟩ :=
    tower_pair_transversals_card (N0 := N0) hY1 hFA hYmono hCb hteams
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · exfalso
    have hc1' : c = 1 := by omega
    subst hc1'
    refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨n, hnN, H, hHc, hHne, hhub, hpos, hmin⟩ := hcof N
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hHc
    refine ⟨n, hnN, a, ?_, hhub⟩
    exact (hpos a (Finset.mem_singleton_self a)).2
  · refine ⟨c, hc2, fun N => ?_⟩
    obtain ⟨n, hnN, H, hHc, hHne, hhub, hpos, hmin⟩ := hcof N
    exact ⟨n, hnN, H, hHc, hhub, hpos, hmin⟩

theorem cofinal_supply_canonical {A : Set ℕ} {N0 : ℕ} {F : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hanchor : StreamSurvives A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hflood : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a) :
    ∃ S : Finset ℕ, (∀ h ∈ S, h ∈ F) ∧ S.Nonempty ∧
      ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
        ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H = insert a S := by
  classical
  -- pigeonhole the F-part of the cofinal supply support transversals
  have hQ : ∀ X, ∃ x, X ≤ x ∧ ∃ S, S ⊆ F ∧
      (∃ a, a ∈ A ∧ x = a ∧ a ∉ F ∧
        ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
          H = insert a S) := by
    intro X
    set XF := max X ((F.sup id) + 1) with hXF
    obtain ⟨a, ha, hXa, n, hnN, H, hhub, hmin, haH, hsub⟩ := hflood XF
    have haF : a ∉ F := by
      intro haF
      have h1 : a ≤ F.sup id := Finset.le_sup (f := id) haF
      have h2 : (F.sup id) + 1 ≤ a :=
        le_trans (le_max_right _ _) hXa
      omega
    refine ⟨a, le_trans (le_max_left _ _) hXa, H.erase a, ?_, a, ha,
      rfl, haF, n, hnN, H, hhub, hmin, haH, ?_⟩
    · intro h hh
      obtain ⟨hne, hhH⟩ := Finset.mem_erase.1 hh
      rcases hsub h hhH with h' | h'
      · exact h'
      · exact absurd h' hne
    · exact (Finset.insert_erase haH).symm
  obtain ⟨S, hSF, hrec⟩ := cofinal_subset_pigeonhole
    (Q := fun x S => ∃ a, a ∈ A ∧ x = a ∧ a ∉ F ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
        H = insert a S)
    (F := F) (by
      intro N
      obtain ⟨x, hx, S, hSF, hdata⟩ := hQ N
      exact ⟨x, hx, S, hSF, hdata⟩)
  -- contradiction the empty core by the stream contradiction
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exfalso
    subst hSe
    refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨x, hxN, a, ha, heq, haF, n, hnN, H, hhub, hmin, haH, hHeq⟩ :=
      hrec (max N 1)
    subst heq
    have hHa : H = {x} := by simpa using hHeq
    rw [hHa] at hhub hmin haH
    obtain ⟨x', hx', y', hy', z', hz', hsum, hhit, -⟩ :=
      minimal_support_transversal_necessity hhub hmin x haH
    have han : x ≤ n := by
      rcases hhit with h' | h' | h' <;> omega
    exact ⟨n, by omega, x, by omega, hhub⟩
  · refine ⟨S, fun h hh => hSF hh, hSne, fun X => ?_⟩
    obtain ⟨x, hxN, a, ha, heq, haF, n, hnN, H, hhub, hmin, haH, hHeq⟩ :=
      hrec X
    subst heq
    have haS : x ∉ S := fun haS => haF (hSF haS)
    exact ⟨x, ha, hxN, haS, n, hnN, H, hhub, hmin, hHeq⟩

theorem pair_shadow_of_support_transversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hhub : IsRepSupportTransversal A n H) (h0H : 0 ∉ H) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0H

theorem pair_count_of_support_transversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hhub : IsRepSupportTransversal A n H) (h0H : 0 ∉ H) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * H.card := by
  classical
  have hsub : (Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A) ⊆
      H ∪ H.image (fun h => n - h) := by
    intro x hx
    obtain ⟨hxr, hxA, hnxA⟩ := Finset.mem_filter.1 hx
    have hxn : x ≤ n := by
      have := Finset.mem_range.1 hxr
      omega
    rcases pair_shadow_of_support_transversal h0 hhub h0H x hxA (n - x) hnxA
        (by omega) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨n - x, h, by omega⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le H (H.image (fun h => n - h))
  have h3 : (H.image (fun h => n - h)).card ≤ H.card :=
    Finset.card_image_le
  omega

theorem cofinal_supply_pair_shadow {A : Set ℕ} {N0 : ℕ} {S : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (h0S : 0 ∉ S)
    (hcanon : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        H = insert a S) :
    ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ 0 < a ∧ ∃ n, N0 ≤ n ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y = n →
        x ∈ insert a S ∨ y ∈ insert a S) ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * (S.card + 1) := by
  intro X
  obtain ⟨a, ha, hXa, haS, n, hnN, H, hhub, hmin, hHeq⟩ :=
    hcanon (max X 1)
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) hXa
  subst hHeq
  have h0H : 0 ∉ insert a S := by
    intro h
    rcases Finset.mem_insert.1 h with h' | h'
    · omega
    · exact h0S h'
  have hcard : (insert a S).card ≤ S.card + 1 :=
    Finset.card_insert_le a S
  have hb := pair_count_of_support_transversal h0 hhub h0H
  exact ⟨a, ha, le_trans (le_max_left _ _) hXa, by omega, n, hnN,
    pair_shadow_of_support_transversal h0 hhub h0H, by omega⟩

theorem cofinal_supply_routing_dichotomy {A : Set ℕ} {N0 : ℕ} {S : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0) (h0S : 0 ∉ S)
    (hcanon : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S) :
    (∃ s ∈ S, ∀ X, ∃ n, X ≤ n ∧ N0 ≤ n ∧ (∃ w ∈ A, s + w = n) ∧
      ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        H = insert a S) ∨
    (∀ X, ∃ n, X ≤ n ∧ N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
      (∃ w ∈ A, a + w = n) ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a) ∧
      ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S) := by
  classical
  set Q : ℕ → Finset ℕ → Prop := fun n T =>
    (N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      H = insert a S) ∧
    T = S.filter (fun s => ∃ w ∈ A, s + w = n) with hQdef
  have hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ T, Q n T := by
    intro N
    obtain ⟨a, ha, hNa, haS, n, hnN, H, hhub, hmin, hHeq⟩ :=
      hcanon (max N 1)
    have ha1 : 1 ≤ a := le_trans (le_max_right _ _) hNa
    have haH : a ∈ H := by
      rw [hHeq]
      exact Finset.mem_insert_self a S
    obtain ⟨x, hx, y, hy, z, hz, hsum, hhit, -⟩ :=
      minimal_support_transversal_necessity hhub hmin a haH
    have han : a ≤ n := by
      rcases hhit with h' | h' | h' <;> omega
    have hNn : N ≤ n :=
      le_trans (le_trans (le_max_left N 1) hNa) han
    exact ⟨n, hNn, S.filter (fun s => ∃ w ∈ A, s + w = n),
      ⟨hnN, a, ha, by omega, haS, H, hhub, hmin, hHeq⟩, rfl⟩
  rcases cofinal_dichotomy Q hQ (S.sup id) with
    ⟨s, hsW, hper⟩ | havoid
  · left
    obtain ⟨n₀, hn₀, T₀, hQT₀, hsT₀⟩ := hper 0
    have hinst₀ : (N0 ≤ n₀ ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        ∃ H : Finset ℕ, IsRepSupportTransversal A n₀ H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n₀ (H \ {h})) ∧ H = insert a S) ∧
        T₀ = S.filter (fun s' => ∃ w ∈ A, s' + w = n₀) := hQT₀
    have hsS : s ∈ S := by
      have := hinst₀.2 ▸ hsT₀
      exact (Finset.mem_filter.1 this).1
    refine ⟨s, hsS, fun X => ?_⟩
    obtain ⟨n, hn, T, hQT, hsT⟩ := hper X
    have hinst : (N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S) ∧
        T = S.filter (fun s' => ∃ w ∈ A, s' + w = n) := hQT
    obtain ⟨⟨hnN0, a, ha, ha0, haS, H, hhub, hmin, hHeq⟩, hTeq⟩ := hinst
    have hsw : ∃ w ∈ A, s + w = n := by
      have := hTeq ▸ hsT
      exact (Finset.mem_filter.1 this).2
    obtain ⟨w, hw, hswn⟩ := hsw
    exact ⟨n, hn, hnN0, ⟨w, hw, hswn⟩, a, ha, ha0, haS,
      H, hhub, hmin, hHeq⟩
  · right
    intro X
    obtain ⟨n, hn, T, hQT, hbig⟩ := havoid X
    have hinst : (N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S) ∧
        T = S.filter (fun s' => ∃ w ∈ A, s' + w = n) := hQT
    obtain ⟨⟨hnN0, a, ha, ha0, haS, H, hhub, hmin, hHeq⟩, hTeq⟩ := hinst
    -- the filter is empty: no core element has a corep at n
    have hnoS : ∀ s ∈ S, ¬∃ w ∈ A, s + w = n := by
      intro s hsS hsw
      have hsT : s ∈ T := by
        rw [hTeq]
        exact Finset.mem_filter.2 ⟨hsS, hsw⟩
      have hlt := hbig s hsT
      have hle : s ≤ S.sup id := Finset.le_sup (f := id) hsS
      omega
    have h0H : 0 ∉ H := by
      rw [hHeq]
      intro hmem
      rcases Finset.mem_insert.1 hmem with h' | h'
      · omega
      · exact h0S h'
    have hshadow := pair_shadow_of_support_transversal h0 hhub h0H
    have hall : ∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a := by
      intro x hx y hy hxy
      rcases hshadow x hx y hy hxy with hmem | hmem
      · rw [hHeq] at hmem
        rcases Finset.mem_insert.1 hmem with h' | h'
        · exact Or.inl h'
        · exact absurd ⟨y, hy, hxy⟩ (hnoS x h')
      · rw [hHeq] at hmem
        rcases Finset.mem_insert.1 hmem with h' | h'
        · exact Or.inr h'
        · exact absurd ⟨x, hx, by omega⟩ (hnoS y h')
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hnN0
    have hcorep : ∃ w ∈ A, a + w = n := by
      rcases hall x hx y hy hxy with h' | h'
      · exact ⟨y, hy, by omega⟩
      · exact ⟨x, hx, by omega⟩
    exact ⟨n, hn, hnN0, a, ha, ha0, haS, hcorep, hall,
      H, hhub, hmin, hHeq⟩

theorem obstruction_conclusion_trivial {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ A) ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a := by
  classical
  refine ⟨(Finset.range (N0 + 1)).filter (· ∈ A), ?_, 0, ?_⟩
  · intro h hh
    exact (Finset.mem_filter.1 hh).2
  · intro a ha _
    refine ⟨N0, le_refl _,
      insert a ((Finset.range (N0 + 1)).filter (· ∈ A)), ?_,
      Finset.mem_insert_self _ _, ?_⟩
    · intro x hx y hy z hz hsum
      refine Or.inl (Finset.mem_insert.2 (Or.inr ?_))
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hx⟩
    · intro h hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'

theorem tower_branch_trivial {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0) :
    ∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i < Y (i + 1)) ∧
      ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
        (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepSupportTransversal A n H ∧
        ∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h}) := by
  classical
  refine ⟨fun i => i + 1,
    fun i => (Finset.range (3 * (i + 1) + N0 + 1)).filter
      (fun h => h ∈ A ∧ i + 1 ≤ h), ?_,
    fun i => by show i + 1 < i + 1 + 1; omega, ?_⟩
  · intro i h hh
    exact (Finset.mem_filter.1 hh).2
  · intro i
    have hbig : IsRepSupportTransversal A (3 * (i + 1) + N0)
        ((Finset.range (3 * (i + 1) + N0 + 1)).filter
          (fun h => h ∈ A ∧ i + 1 ≤ h)) := by
      intro x hx y hy z hz hsum
      rcases Nat.lt_or_ge x (i + 1) with hxl | hxg
      · rcases Nat.lt_or_ge y (i + 1) with hyl | hyg
        · exact Or.inr (Or.inr (Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hz, by omega⟩))
        · exact Or.inr (Or.inl (Finset.mem_filter.2
            ⟨Finset.mem_range.2 (by omega), hy, hyg⟩))
      · exact Or.inl (Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hx, hxg⟩)
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hbig
    have hH'ne : H'.Nonempty := support_transversal_nonempty_of_covering h0 hcov
      (by omega) hH'hub
    exact ⟨3 * (i + 1) + N0, by omega,
      by show i + 1 ≤ 3 * (i + 1) + N0; omega, H',
      fun h hh => hH'sub hh, hH'ne, hH'hub, hH'min⟩

theorem forced_pair_shadow_of_hfail {A B : Set ℕ}
    (h0 : 0 ∈ A)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) (h0B : 0 ∉ B) :
    ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ B ∨ y ∈ B := by
  intro N
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N
  refine ⟨n, hnN, ?_⟩
  intro x hx y hy hxy
  by_contra hall
  push Not at hall
  obtain ⟨hxB, hyB⟩ := hall
  refine hnorep ![x, y, 0] ?_ (by simp [Fin.sum_univ_three]; omega)
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩
  | 2 => exact ⟨h0, h0B⟩

/-- Counting form of a pair shadow: the order-2 components at `n`
live in `(B ∩ [0,n]) ∪ (n − (B ∩ [0,n]))`. -/
theorem pair_count_of_shadow {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] {n : ℕ}
    (hshadow : ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ B ∨ y ∈ B) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
      2 * ((Finset.range (n + 1)).filter (· ∈ B)).card := by
  classical
  set Bn := (Finset.range (n + 1)).filter (· ∈ B) with hBn
  have hsub : (Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A) ⊆
      Bn ∪ Bn.image (fun h => n - h) := by
    intro x hx
    obtain ⟨hxr, hxA, hnxA⟩ := Finset.mem_filter.1 hx
    have hxn : x ≤ n := by
      have := Finset.mem_range.1 hxr
      omega
    rcases hshadow x hxA (n - x) hnxA (by omega) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxr, h⟩)
    · refine Finset.mem_union_right _
        (Finset.mem_image.2 ⟨n - x, ?_, by omega⟩)
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le Bn (Bn.image (fun h => n - h))
  have h3 : (Bn.image (fun h => n - h)).card ≤ Bn.card :=
    Finset.card_image_le
  omega

theorem log_sidon_of_hfail {A : Set ℕ} {N0 : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ (∀ j, b j ∈ A) ∧
      (∀ j, 3 ^ j ≤ b j) ∧
      ∀ N, ∃ n, N ≤ n ∧
        (∀ x ∈ A, ∀ y ∈ A, x + y = n →
          x ∈ Set.range b ∨ y ∈ Set.range b) ∧
        ((Finset.range (n + 1)).filter
          (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤
          2 * (Nat.log 3 n + 1) := by
  classical
  have hpick : ∀ X : ℕ, ∃ a, a ∈ A ∧ X ≤ a := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov X
    exact ⟨a, ha, hXa⟩
  choose f hfA hfge using hpick
  set b : ℕ → ℕ := fun j =>
    Nat.rec (f 1) (fun _ prev => f (3 * prev + 1)) j with hb
  have hbS : ∀ j, b (j + 1) = f (3 * b j + 1) := fun _ => rfl
  have hb0 : b 0 = f 1 := rfl
  have hbA : ∀ j, b j ∈ A := by
    intro j
    cases j with
    | zero => exact hfA 1
    | succ j => rw [hbS]; exact hfA _
  have hb1 : 1 ≤ b 0 := by
    rw [hb0]
    exact hfge 1
  have hbgrow : ∀ j, 3 * b j < b (j + 1) := by
    intro j
    have := hfge (3 * b j + 1)
    rw [hbS]
    omega
  have hbpow : ∀ j, 3 ^ j ≤ b j := by
    intro j
    induction j with
    | zero => simpa using hb1
    | succ j ih =>
      have h1 := hbgrow j
      have h3 : 3 ^ (j + 1) = 3 * 3 ^ j := by ring
      omega
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro j
    have h1 := hbgrow j
    have h2 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have h3 := hbpow j
    omega
  have hBA : Set.range b ⊆ A := by
    rintro x ⟨j, rfl⟩
    exact hbA j
  have hBinf : (Set.range b).Infinite :=
    Set.infinite_range_of_injective hbmono.injective
  have h0B : 0 ∉ Set.range b := by
    rintro ⟨j, hj⟩
    have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    have h2 := hbpow j
    omega
  refine ⟨b, hbmono, hbA, hbpow, ?_⟩
  intro N
  obtain ⟨n, hnN, hshadow⟩ :=
    forced_pair_shadow_of_hfail h0 hfail hBA hBinf h0B N
  refine ⟨n, hnN, hshadow, ?_⟩
  have hBn : ((Finset.range (n + 1)).filter (· ∈ Set.range b)).card ≤
      Nat.log 3 n + 1 := by
    have hsub : (Finset.range (n + 1)).filter (· ∈ Set.range b) ⊆
        (Finset.range (Nat.log 3 n + 1)).image b := by
      intro x hx
      obtain ⟨hxr, hxB⟩ := Finset.mem_filter.1 hx
      obtain ⟨j, hj⟩ := hxB
      have hxn : x ≤ n := by
        have := Finset.mem_range.1 hxr
        omega
      have hx1 : 1 ≤ x := by
        have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
        have h2 := hbpow j
        omega
      have hjn : 3 ^ j ≤ n := le_trans (hbpow j) (by omega)
      have hjlog : j ≤ Nat.log 3 n :=
        (Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 hjn
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), hj⟩
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.range (Nat.log 3 n + 1)).image b).card ≤
        Nat.log 3 n + 1 :=
      le_trans Finset.card_image_le (by simp)
    omega
  have hcount := pair_count_of_shadow (B := Set.range b) hshadow
  omega

theorem cofinal_supply_of_singleton_rotator {A : Set ℕ} {N₀ : ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepSupportTransversal A n H ∧
      (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hc : c = S.card + 1) :
    ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S := by
  intro X
  obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit X N₀
  have hsd : (H \ S).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSH]
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hsd
  have hamem : a ∈ H \ S := ha ▸ Finset.mem_singleton_self a
  have haH : a ∈ H := (Finset.mem_sdiff.1 hamem).1
  have haS : a ∉ S := (Finset.mem_sdiff.1 hamem).2
  have hHeq : H = insert a S := by
    have h1 : H \ S ∪ S = H := Finset.sdiff_union_of_subset hSH
    rw [← h1, ha, Finset.singleton_union]
  have hXa : X < a := hrest a haH haS
  obtain ⟨x, hx, y, hy, z, hz, hsum, hhit, -⟩ :=
    minimal_support_transversal_necessity hhub hmin a haH
  have haA : a ∈ A := by
    rcases hhit with h' | h' | h'
    · exact h' ▸ hx
    · exact h' ▸ hy
    · exact h' ▸ hz
  exact ⟨a, haA, by omega, haS, n, hn, H, hhub, hmin, hHeq⟩

theorem stable_core_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, 2 ≤ S.card ∧
      ∀ N, ∃ n, N ≤ n ∧ IsRepSupportTransversal A n S) ∨
    (∃ S' : Finset ℕ, S'.Nonempty ∧
      ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S' ∧
        ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H = insert a S') ∨
    (∃ S : Finset ℕ, ∃ c, S.card + 2 ≤ c ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) := by
  obtain ⟨K, S, c, hcK, hc2, hSc, hsplit, hteam⟩ :=
    support_transversal_counterexample_structure_of_hfail h0 hcov hdb hanchor hfail
  rcases Nat.lt_or_ge c (S.card + 1) with hlt | hge
  · left
    have hceq : c = S.card := by omega
    exact ⟨S, by omega, hteam hceq⟩
  · rcases Nat.lt_or_ge c (S.card + 2) with hlt2 | hge2
    · right
      left
      have hceq : c = S.card + 1 := by omega
      have hflood : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
          ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
            (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ a ∈ H ∧
            ∀ h ∈ H, h ∈ S ∨ h = a := by
        intro X
        obtain ⟨a, haA, hXa, haS, n, hn, H, hhub, hmin, hHeq⟩ :=
          cofinal_supply_of_singleton_rotator (N₀ := N₀) hsplit hceq X
        refine ⟨a, haA, hXa, n, hn, H, hhub, hmin, ?_, ?_⟩
        · rw [hHeq]
          exact Finset.mem_insert_self a S
        · intro h hh
          rw [hHeq] at hh
          rcases Finset.mem_insert.1 hh with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
      obtain ⟨S', hS'S, hS'ne, hcanon⟩ :=
        cofinal_supply_canonical h0 hcov hanchor hfail hflood
      exact ⟨S', hS'ne, hcanon⟩
    · right
      right
      exact ⟨S, c, hge2, hsplit⟩

/-- Pair-support transversal counting: order-2 components live in `H ∪ (n − H)`,
with no zero caveat — the pair support transversal IS the order-2 transversal. -/
theorem pair_count_of_pairSupportTransversal {A : Set ℕ} [DecidablePred (· ∈ A)]
    {n : ℕ} {H : Finset ℕ} (hhub : IsPairSupportTransversal A n H) :
    ((Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ 2 * H.card := by
  classical
  have hsub : (Finset.range (n + 1)).filter
      (fun x => x ∈ A ∧ (n - x) ∈ A) ⊆
      H ∪ H.image (fun h => n - h) := by
    intro x hx
    obtain ⟨hxr, hxA, hnxA⟩ := Finset.mem_filter.1 hx
    have hxn : x ≤ n := by
      have := Finset.mem_range.1 hxr
      omega
    rcases hhub x hxA (n - x) hnxA (by omega) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨n - x, h, by omega⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le H (H.image (fun h => n - h))
  have h3 : (H.image (fun h => n - h)).card ≤ H.card :=
    Finset.card_image_le
  omega

theorem constant_sidon_of_minimality {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ C, ∀ N, ∃ n, N ≤ n ∧
      ((Finset.range (n + 1)).filter
        (fun x => x ∈ A ∧ (n - x) ∈ A)).card ≤ C := by
  classical
  obtain ⟨K, S, c, hcK, hsplit⟩ :=
    stable_pair_core_card_of_minimality hcov hmin
  refine ⟨2 * c, fun N => ?_⟩
  obtain ⟨n, hn, H, hcard, hhub, -, -⟩ := hsplit 0 N
  have := pair_count_of_pairSupportTransversal hhub
  exact ⟨n, hn, by omega⟩

theorem pairSupportTransversal_of_translate {A : Set ℕ} {n w : ℕ} {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H) (hwA : w ∈ A) (hwH : w ∉ H)
    (hwn : w ≤ n) :
    IsPairSupportTransversal A (n - w) H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy w hwA (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hwH

theorem support_transversal_fan_amplification {A : Set ℕ} {N₀ n : ℕ} {H : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (hcov : PairCovers A N₀) (hhub : IsRepSupportTransversal A n H)
    (hHne : H.Nonempty) (hn : N₀ ≤ n) :
    ∃ h ∈ H,
      ((Finset.range (n - N₀ + 1)).filter
        (fun w => w ∈ A ∧ w ∉ H)).card / H.card ≤
      ((Finset.range (n - h + 1)).filter
        (fun x => x ∈ A ∧ (n - h - x) ∈ A)).card := by
  classical
  set W' := (Finset.range (n - N₀ + 1)).filter
    (fun w => w ∈ A ∧ w ∉ H) with hW'
  have hchoice : ∀ w : ℕ, ∃ h, h ∈ H ∧
      (w ∈ W' → h + w ≤ n ∧ (n - w - h) ∈ A) := by
    intro w
    by_cases hw : w ∈ W'
    · obtain ⟨hwr, hwA, hwH⟩ := Finset.mem_filter.1 hw
      have hwle : w ≤ n - N₀ := by
        have := Finset.mem_range.1 hwr
        omega
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov (n - w) (by omega)
      rcases hhub x hx y hy w hwA (by omega) with h' | h' | h'
      · refine ⟨x, h', fun _ => ⟨by omega, ?_⟩⟩
        have hyx : n - w - x = y := by omega
        rw [hyx]
        exact hy
      · refine ⟨y, h', fun _ => ⟨by omega, ?_⟩⟩
        have hxy' : n - w - y = x := by omega
        rw [hxy']
        exact hx
      · exact absurd h' hwH
    · exact ⟨hHne.choose, hHne.choose_spec, fun h => absurd h hw⟩
  choose g hgH hgW using hchoice
  obtain ⟨h₀, hh₀, hfib⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := g) (s := W') (t := H) (fun w _ => hgH w) hHne
      (by
        calc H.card * (W'.card / H.card)
            = W'.card / H.card * H.card := Nat.mul_comm _ _
          _ ≤ W'.card := Nat.div_mul_le_self _ _)
  refine ⟨h₀, hh₀, le_trans hfib (Finset.card_le_card ?_)⟩
  intro w hw
  have hwW' : w ∈ W' := (Finset.mem_filter.1 hw).1
  have hgw : g w = h₀ := (Finset.mem_filter.1 hw).2
  obtain ⟨hle, hmem⟩ := hgW w hwW'
  obtain ⟨hwr, hwA, hwH⟩ := Finset.mem_filter.1 hwW'
  refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hwA, ?_⟩
  have heq : n - h₀ - w = n - w - g w := by
    rw [hgw]
    omega
  rw [heq]
  exact hmem

/-- Covering forces square-root growth: `[N₀, n]` maps injectively
(by its sum) into ordered pairs from `A ∩ [0, n]`, so
`|A ∩ [0,n]|² ≥ n + 1 − N₀`.  Feeds the fan amplification: support transversal targets
have translates with `r₂ ≥ (√n − |H|)/|H|`. -/
theorem covering_sqrt_lower {A : Set ℕ} {N₀ n : ℕ}
    [DecidablePred (· ∈ A)]
    (hcov : PairCovers A N₀) (hn : N₀ ≤ n) :
    n + 1 - N₀ ≤ ((Finset.range (n + 1)).filter (· ∈ A)).card *
      ((Finset.range (n + 1)).filter (· ∈ A)).card := by
  classical
  set F := (Finset.range (n + 1)).filter (· ∈ A) with hF
  have hchoice : ∀ m : ℕ, ∃ q : ℕ × ℕ,
      (m ∈ Finset.Icc N₀ n → q.1 ∈ F ∧ q.2 ∈ F ∧ q.1 + q.2 = m) := by
    intro m
    by_cases hm : m ∈ Finset.Icc N₀ n
    · obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.1 hm
      obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm1
      refine ⟨(x, y), fun _ => ⟨?_, ?_, hxy⟩⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hx⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hy⟩
    · exact ⟨(0, 0), fun h => absurd h hm⟩
  choose q hq using hchoice
  have hmaps : ∀ m ∈ Finset.Icc N₀ n, q m ∈ F ×ˢ F := by
    intro m hm
    obtain ⟨h1, h2, -⟩ := hq m hm
    exact Finset.mem_product.2 ⟨h1, h2⟩
  have hinj : Set.InjOn q (Finset.Icc N₀ n) := by
    intro m₁ hm₁ m₂ hm₂ heq
    obtain ⟨-, -, hs1⟩ := hq m₁ (by simpa using hm₁)
    obtain ⟨-, -, hs2⟩ := hq m₂ (by simpa using hm₂)
    rw [heq] at hs1
    omega
  have hcard := Finset.card_le_card_of_injOn q hmaps hinj
  rw [Nat.card_Icc, Finset.card_product] at hcard
  exact hcard

/-- Pair-freeness: every late target keeps a pair representation
avoiding `P`.  Up-monotone in `P`-complement: the avoidance invariant. -/
def PairFree (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ) : Prop :=
  ∀ m, N₀ ≤ m → ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧ x ∉ P ∧ y ∉ P

/-- Freeness extends below the new element for free: parts of a
small target cannot equal the large newcomer. -/
lemma pairFree_insert {A : Set ℕ} {N₀ : ℕ} {P : Finset ℕ} {b : ℕ}
    (hfree : PairFree A N₀ P)
    (hb : ∀ m, N₀ ≤ m → b ≤ m → ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧
      x ∉ insert b P ∧ y ∉ insert b P) :
    PairFree A N₀ (insert b P) := by
  intro m hm
  rcases Nat.lt_or_ge m b with hmb | hmb
  · obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfree m hm
    refine ⟨x, hx, y, hy, hxy, ?_, ?_⟩
    · intro hmem
      rcases Finset.mem_insert.1 hmem with h' | h'
      · omega
      · exact hxP h'
    · intro hmem
      rcases Finset.mem_insert.1 hmem with h' | h'
      · omega
      · exact hyP h'
  · exact hb m hm hmb

theorem pair_cofinal_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = m →
          x ∈ insert b P ∨ y ∈ insert b P := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : PairFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, hxy, Finset.notMem_empty x,
      Finset.notMem_empty y⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ A ∧ X ≤ b ∧
      (PairFree A N₀ P → ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧
          x ∉ insert b P ∧ y ∉ insert b P) := by
    intro P X
    by_cases hfree : PairFree A N₀ P
    · obtain ⟨b, hbA, hXb, hbgood⟩ := hno P hfree X
      exact ⟨b, hbA, hXb, fun _ => hbgood⟩
    · obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov X
      exact ⟨b, hbA, hXb, fun h => absurd h hfree⟩
  choose pick hpickA hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hfreeS : ∀ j, PairFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show PairFree A N₀ (insert (pick ∅ 1) ∅)
      exact pairFree_insert hfree0 (hpickfree ∅ 1 hfree0)
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact pairFree_insert ih (hpickfree (st j).2 ((st j).1 + 1) ih)
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    cases j with
    | zero => exact hpickA ∅ 1
    | succ j =>
      rw [show (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) from
        by rw [hstS]]
      exact hpickA _ _
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfreeS m m hm
  have hxB : x ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = x := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hxP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  have hyB : y ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = y := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hyP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  have h0B : (0 : ℕ) ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = 0 := hi
    have := hlastge i
    omega
  refine ⟨![x, y, 0], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩
  | 2 => exact ⟨h0, h0B⟩

/-- Every pair support transversal contains a minimal pair support transversal. -/
theorem exists_minimal_pairSupportTransversal {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsPairSupportTransversal A n H) :
    ∃ H' ⊆ H, IsPairSupportTransversal A n H' ∧
      ∀ h ∈ H', ¬IsPairSupportTransversal A n (H' \ {h}) := by
  classical
  revert hhub
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro hhub
    by_cases hmin : ∀ h ∈ H, ¬IsPairSupportTransversal A n (H \ {h})
    · exact ⟨H, Finset.Subset.refl H, hhub, hmin⟩
    · push Not at hmin
      obtain ⟨h, hhH, hsub⟩ := hmin
      have hss : H \ {h} ⊂ H :=
        Finset.sdiff_ssubset (Finset.singleton_subset_iff.2 hhH)
          (Finset.singleton_nonempty h)
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := ih (H \ {h}) hss hsub
      exact ⟨H', Finset.Subset.trans hH'sub Finset.sdiff_subset,
        hH'hub, hH'min⟩

theorem pair_cofinal_supply_canonical {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P S : Finset ℕ, S ⊆ P ∧ PairFree A N₀ P ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsPairSupportTransversal A m (insert b S) ∧
          ∀ h ∈ insert b S,
            ¬IsPairSupportTransversal A m (insert b S \ {h}) := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_cofinal_supply_of_hfail h0 hcov hfail
  have hQ : ∀ N, ∃ x, N ≤ x ∧ ∃ S, S ⊆ P ∧
      (x ∈ A ∧ x ∉ S ∧ ∃ m, N₀ ≤ m ∧ x ≤ m ∧
        IsPairSupportTransversal A m (insert x S) ∧
        ∀ h ∈ insert x S, ¬IsPairSupportTransversal A m (insert x S \ {h})) := by
    intro N
    obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max N X₀)
    obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
      (le_trans (le_max_right _ _) hXb)
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_pairSupportTransversal hhub
    have hbH' : b ∈ H' := by
      by_contra hbH'
      have hH'P : H' ⊆ P := by
        intro h hh
        rcases Finset.mem_insert.1 (hH'sub hh) with h' | h'
        · exact absurd (h' ▸ hh) hbH'
        · exact h'
      obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hPfree m hmN
      rcases hH'hub x hx y hy hxy with h' | h'
      · exact hxP (hH'P h')
      · exact hyP (hH'P h')
    have hSsub : H'.erase b ⊆ P := by
      intro h hh
      obtain ⟨hne, hhH'⟩ := Finset.mem_erase.1 hh
      rcases Finset.mem_insert.1 (hH'sub hhH') with h' | h'
      · exact absurd h' hne
      · exact h'
    have hbS : b ∉ H'.erase b := Finset.notMem_erase b H'
    have hH'eq : H' = insert b (H'.erase b) :=
      (Finset.insert_erase hbH').symm
    refine ⟨b, le_trans (le_max_left _ _) hXb, H'.erase b, hSsub,
      hbA, hbS, m, hmN, hbm, ?_, ?_⟩
    · rw [← hH'eq]
      exact hH'hub
    · rw [← hH'eq]
      exact hH'min
  obtain ⟨S, hSP, hrec⟩ := cofinal_subset_pigeonhole
    (Q := fun x S => x ∈ A ∧ x ∉ S ∧ ∃ m, N₀ ≤ m ∧ x ≤ m ∧
      IsPairSupportTransversal A m (insert x S) ∧
      ∀ h ∈ insert x S, ¬IsPairSupportTransversal A m (insert x S \ {h}))
    (F := P) hQ
  refine ⟨P, S, hSP, hPfree, fun X => ?_⟩
  obtain ⟨b, hXb, hbA, hbS, hdata⟩ := hrec X
  exact ⟨b, hbA, hXb, hbS, hdata⟩

theorem constant_sidon_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_cofinal_supply_of_hfail h0 hcov hfail
  refine ⟨2 * (P.card + 1), fun N => ?_⟩
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max N X₀)
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_right _ _) hXb)
  have hcount := pair_count_of_pairSupportTransversal hhub
  have hcard : (insert b P).card ≤ P.card + 1 := Finset.card_insert_le b P
  exact ⟨m, le_trans (le_trans (le_max_left _ _) hXb) hbm, by omega⟩

theorem pair_cofinal_supply_pool {A P₀ : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hP₀A : P₀ ⊆ A) (h0P₀ : 0 ∉ P₀)
    (hunb : ∀ X, ∃ p ∈ P₀, X ≤ p)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ P₀) ∧ PairFree A N₀ P ∧
      ∃ X, ∀ b ∈ P₀, X ≤ b →
        ∃ m, N₀ ≤ m ∧ b ≤ m ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = m →
            x ∈ insert b P ∨ y ∈ insert b P := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : PairFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, hxy, Finset.notMem_empty x,
      Finset.notMem_empty y⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ P₀ ∧ X ≤ b ∧
      ((∀ h ∈ P, h ∈ P₀) → PairFree A N₀ P →
        ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧
          x ∉ insert b P ∧ y ∉ insert b P) := by
    intro P X
    by_cases hPP : (∀ h ∈ P, h ∈ P₀) ∧ PairFree A N₀ P
    · obtain ⟨b, hbP, hXb, hbgood⟩ := hno P hPP.1 hPP.2 X
      exact ⟨b, hbP, hXb, fun _ _ => hbgood⟩
    · obtain ⟨b, hbP, hXb⟩ := hunb X
      refine ⟨b, hbP, hXb, fun h1 h2 => absurd ⟨h1, h2⟩ hPP⟩
  choose pick hpickP hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hsetP : ∀ j, ∀ h ∈ (st j).2, h ∈ P₀ := by
    intro j
    induction j with
    | zero =>
      intro h hh
      have hh' : h = pick ∅ 1 := Finset.mem_singleton.1 hh
      rw [hh']
      exact hpickP ∅ 1
    | succ j ih =>
      intro h hh
      rw [hstS] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact hpickP _ _
      · exact ih h h'
  have hfreeS : ∀ j, PairFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show PairFree A N₀ (insert (pick ∅ 1) ∅)
      exact pairFree_insert hfree0
        (hpickfree ∅ 1 (fun h hh => absurd hh (Finset.notMem_empty h))
          hfree0)
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact pairFree_insert ih
        (hpickfree (st j).2 ((st j).1 + 1) (hsetP j) ih)
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    exact hP₀A (hsetP j _ (hlastmem j))
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfreeS m m hm
  have hxB : x ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = x := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hxP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  have hyB : y ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = y := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hyP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  have h0B : (0 : ℕ) ∉ B := by
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = 0 := hi
    have := hlastge i
    omega
  refine ⟨![x, y, 0], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩
  | 2 => exact ⟨h0, h0B⟩

/-- The rotating required elements of a canonical pair cofinal supply with core `S`:
elements carrying a minimal pair support transversal `S ∪ {b}` at some personal
target `m ≥ b`. -/
def PairCofinalSupplyRequiredElements (A : Set ℕ) (N₀ : ℕ) (S : Finset ℕ) : Set ℕ :=
  {b | b ∈ A ∧ b ∉ S ∧ 0 < b ∧ ∃ m, N₀ ≤ m ∧ b ≤ m ∧
    IsPairSupportTransversal A m (insert b S) ∧
    ∀ h ∈ insert b S, ¬IsPairSupportTransversal A m (insert b S \ {h})}

theorem pair_cofinal_supply_iteration {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ,
      (∀ X, ∃ b ∈ PairCofinalSupplyRequiredElements A N₀ S, X ≤ b) ∧
      ∃ P' : Finset ℕ,
        (∀ h ∈ P', h ∈ PairCofinalSupplyRequiredElements A N₀ S) ∧
        PairFree A N₀ P' ∧
        ∃ X', ∀ b ∈ PairCofinalSupplyRequiredElements A N₀ S, X' ≤ b →
          ∃ m, N₀ ≤ m ∧ b ≤ m ∧
            ∀ x ∈ A, ∀ y ∈ A, x + y = m →
              x ∈ insert b P' ∨ y ∈ insert b P' := by
  classical
  obtain ⟨P, S, hSP, hPfree, hstream⟩ :=
    pair_cofinal_supply_canonical h0 hcov hfail
  have hunb : ∀ X, ∃ b ∈ PairCofinalSupplyRequiredElements A N₀ S, X ≤ b := by
    intro X
    obtain ⟨b, hbA, hXb, hbS, m, hmN, hbm, hhub, hmin⟩ :=
      hstream (max X 1)
    refine ⟨b, ⟨hbA, hbS, ?_, m, hmN, hbm, hhub, hmin⟩,
      le_trans (le_max_left _ _) hXb⟩
    have := le_trans (le_max_right _ _) hXb
    omega
  have hGA : PairCofinalSupplyRequiredElements A N₀ S ⊆ A := fun b hb => hb.1
  have h0G : 0 ∉ PairCofinalSupplyRequiredElements A N₀ S := by
    intro h
    have := h.2.2.1
    omega
  obtain ⟨P', hP'G, hP'free, X', hcascade⟩ :=
    pair_cofinal_supply_pool h0 hcov hGA h0G hunb hfail
  exact ⟨S, hunb, P', hP'G, hP'free, X', hcascade⟩

theorem singleton_pair_required_element_notMem_free {A : Set ℕ}
    {N₀ b m : ℕ} {Q : Finset ℕ}
    (hfree : PairFree A N₀ Q) (hm : N₀ ≤ m)
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = m → x = b ∨ y = b) :
    b ∉ Q := by
  intro hbQ
  obtain ⟨x, hx, y, hy, hxy, hxQ, hyQ⟩ := hfree m hm
  rcases hall x hx y hy hxy with h | h
  · exact hxQ (h ▸ hbQ)
  · exact hyQ (h ▸ hbQ)

def RepFree (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ) : Prop :=
  ∀ m, N₀ ≤ m → ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
    x ∉ P ∧ y ∉ P ∧ z ∉ P

/-- Freeness extends below the newcomer for free: parts of a small
target cannot equal the large new element. -/
lemma repFree_insert {A : Set ℕ} {N₀ : ℕ} {P : Finset ℕ} {b : ℕ}
    (hfree : RepFree A N₀ P)
    (hb : ∀ m, N₀ ≤ m → b ≤ m →
      ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
        x ∉ insert b P ∧ y ∉ insert b P ∧ z ∉ insert b P) :
    RepFree A N₀ (insert b P) := by
  intro m hm
  rcases Nat.lt_or_ge m b with hmb | hmb
  · obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfree m hm
    refine ⟨x, hx, y, hy, z, hz, hxyz, ?_, ?_, ?_⟩ <;>
      · intro hmem
        rcases Finset.mem_insert.1 hmem with h' | h'
        · omega
        · first
          | exact hxP h'
          | exact hyP h'
          | exact hzP h'
  · exact hb m hm hmb

theorem rep_cofinal_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ A ∧ X ≤ b ∧
      (RepFree A N₀ P → ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
          x ∉ insert b P ∧ y ∉ insert b P ∧ z ∉ insert b P) := by
    intro P X
    by_cases hfree : RepFree A N₀ P
    · obtain ⟨b, hbA, hXb, hbgood⟩ := hno P hfree X
      refine ⟨b, hbA, hXb, fun _ m hm hbm => ?_⟩
      have hnh := hbgood m hm hbm
      rw [IsRepSupportTransversal] at hnh
      push Not at hnh
      obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hnh
      exact ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩
    · obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov X
      exact ⟨b, hbA, hXb, fun h => absurd h hfree⟩
  choose pick hpickA hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hfreeS : ∀ j, RepFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show RepFree A N₀ (insert (pick ∅ 1) ∅)
      exact repFree_insert hfree0 (hpickfree ∅ 1 hfree0)
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact repFree_insert ih (hpickfree (st j).2 ((st j).1 + 1) ih)
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    cases j with
    | zero => exact hpickA ∅ 1
    | succ j =>
      rw [show (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) from
        by rw [hstS]]
      exact hpickA _ _
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfreeS m m hm
  have havoid : ∀ w, w ≤ m → w ∉ (st m).2 → w ∉ B := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = w := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hwP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  refine ⟨![x, y, z], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, havoid x (by omega) hxP⟩
  | 1 => exact ⟨hy, havoid y (by omega) hyP⟩
  | 2 => exact ⟨hz, havoid z (by omega) hzP⟩

/-- The rep cofinal supply with minimal support transversals: the rotator is always necessary
— the free envelope''s surviving representation can only be hit at
`b`, so `b` sits in every minimalization. -/
theorem rep_cofinal_supply_minimal_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, fun X => ?_⟩
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max X X₀)
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_right _ _) hXb)
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
  have hbH' : b ∈ H' := by
    obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hPfree m hmN
    rcases hH'hub x hx y hy z hz hxyz with h' | h' | h'
    · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
      · exact h'' ▸ h'
      · exact absurd h'' hxP
    · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
      · exact h'' ▸ h'
      · exact absurd h'' hyP
    · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
      · exact h'' ▸ h'
      · exact absurd h'' hzP
  refine ⟨b, hbA, le_trans (le_max_left _ _) hXb, m, hmN, hbm,
    H', hH'hub, hH'min, hbH', ?_⟩
  intro h hh
  rcases Finset.mem_insert.1 (hH'sub hh) with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

theorem canonical_cofinal_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧
          H = insert b S := by
  classical
  obtain ⟨P, hPfree, hstream⟩ := rep_cofinal_supply_minimal_of_hfail h0 hcov hfail
  have hflood : ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
    intro X
    obtain ⟨b, hbA, hXb, m, hmN, hbm, H, hhub, hmin, hbH, hsub⟩ :=
      hstream X
    exact ⟨b, hbA, hXb, m, hmN, H, hhub, hmin, hbH, hsub⟩
  obtain ⟨S, hSP, hSne, hcanon⟩ :=
    cofinal_supply_canonical h0 hcov hanchor hfail hflood
  exact ⟨S, hSne, hcanon⟩

theorem rep_cofinal_supply_pool {A P₀ : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hP₀A : P₀ ⊆ A) (h0P₀ : 0 ∉ P₀)
    (hunb : ∀ X, ∃ p ∈ P₀, X ≤ p)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ P₀) ∧ RepFree A N₀ P ∧
      ∃ X, ∀ b ∈ P₀, X ≤ b →
        ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : RepFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, 0, h0, by omega, Finset.notMem_empty x,
      Finset.notMem_empty y, Finset.notMem_empty 0⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ P₀ ∧ X ≤ b ∧
      ((∀ h ∈ P, h ∈ P₀) → RepFree A N₀ P →
        ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m ∧
          x ∉ insert b P ∧ y ∉ insert b P ∧ z ∉ insert b P) := by
    intro P X
    by_cases hPP : (∀ h ∈ P, h ∈ P₀) ∧ RepFree A N₀ P
    · obtain ⟨b, hbP, hXb, hbgood⟩ := hno P hPP.1 hPP.2 X
      refine ⟨b, hbP, hXb, fun _ _ m hm hbm => ?_⟩
      have hnh := hbgood m hm hbm
      rw [IsRepSupportTransversal] at hnh
      push Not at hnh
      obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hnh
      exact ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩
    · obtain ⟨b, hbP, hXb⟩ := hunb X
      exact ⟨b, hbP, hXb, fun h1 h2 => absurd ⟨h1, h2⟩ hPP⟩
  choose pick hpickP hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hsetP : ∀ j, ∀ h ∈ (st j).2, h ∈ P₀ := by
    intro j
    induction j with
    | zero =>
      intro h hh
      have hh' : h = pick ∅ 1 := Finset.mem_singleton.1 hh
      rw [hh']
      exact hpickP ∅ 1
    | succ j ih =>
      intro h hh
      rw [hstS] at hh
      rcases Finset.mem_insert.1 hh with h' | h'
      · rw [h']
        exact hpickP _ _
      · exact ih h h'
  have hfreeS : ∀ j, RepFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show RepFree A N₀ (insert (pick ∅ 1) ∅)
      exact repFree_insert hfree0
        (hpickfree ∅ 1 (fun h hh => absurd hh (Finset.notMem_empty h))
          hfree0)
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact repFree_insert ih
        (hpickfree (st j).2 ((st j).1 + 1) (hsetP j) ih)
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    exact hP₀A (hsetP j _ (hlastmem j))
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfreeS m m hm
  have havoid : ∀ w, w ≤ m → w ∉ (st m).2 → w ∉ B := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = w := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hwP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  refine ⟨![x, y, z], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, havoid x (by omega) hxP⟩
  | 1 => exact ⟨hy, havoid y (by omega) hyP⟩
  | 2 => exact ⟨hz, havoid z (by omega) hzP⟩

theorem canonical_cofinal_supply_pos_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧
          H = insert b S := by
  classical
  have hunb : ∀ X, ∃ p ∈ {a | a ∈ A ∧ 0 < a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X 1)
    exact ⟨a, ⟨ha, by
      have := le_trans (le_max_right _ _) hXa
      omega⟩, le_trans (le_max_left _ _) hXa⟩
  obtain ⟨P, hPpos, hPfree, X₀, hstall⟩ :=
    rep_cofinal_supply_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
      (fun a ha => ha.1) (fun h => by have := h.2; omega) hunb hfail
  have hflood : ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
    intro X
    obtain ⟨p, hp, hXp⟩ := hunb (max X X₀)
    obtain ⟨m, hmN, hbm, hhub⟩ := hstall p hp
      (le_trans (le_max_right _ _) hXp)
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
    have hbH' : p ∈ H' := by
      obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hPfree m hmN
      rcases hH'hub x hx y hy z hz hxyz with h' | h' | h'
      · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
        · exact h'' ▸ h'
        · exact absurd h'' hxP
      · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
        · exact h'' ▸ h'
        · exact absurd h'' hyP
      · rcases Finset.mem_insert.1 (hH'sub h') with h'' | h''
        · exact h'' ▸ h'
        · exact absurd h'' hzP
    refine ⟨p, hp.1, le_trans (le_max_left _ _) hXp, m, hmN,
      H', hH'hub, hH'min, hbH', ?_⟩
    intro h hh
    rcases Finset.mem_insert.1 (hH'sub hh) with h' | h'
    · exact Or.inr h'
    · exact Or.inl h'
  obtain ⟨S, hSP, hSne, hcanon⟩ :=
    cofinal_supply_canonical h0 hcov hanchor hfail hflood
  exact ⟨S, hSne, fun h hh => hPpos h (hSP h hh), hcanon⟩

theorem routing_dichotomy_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ((∃ s ∈ S, ∀ X, ∃ n, X ≤ n ∧ N₀ ≤ n ∧ (∃ w ∈ A, s + w = n) ∧
        ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
          IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          H = insert a S) ∨
      (∀ X, ∃ n, X ≤ n ∧ N₀ ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        (∃ w ∈ A, a + w = n) ∧
        (∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a) ∧
        ∃ H : Finset ℕ, IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧ H = insert a S)) := by
  obtain ⟨S, hSne, hSpos, hcanon⟩ :=
    canonical_cofinal_supply_pos_of_hfail h0 hcov hanchor hfail
  have h0S : 0 ∉ S := by
    intro h
    have := (hSpos 0 h).2
    omega
  exact ⟨S, hSne, hSpos, cofinal_supply_routing_dichotomy h0 hcov h0S hcanon⟩

theorem pair_cofinal_supply_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ t, N₀ ≤ t ∧ b ≤ t ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = t →
          x ∈ insert b P ∨ y ∈ insert b P := by
  classical
  by_contra hno
  push Not at hno
  have hfree0 : PairFree A N₀ ∅ := by
    intro m hm
    obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
    exact ⟨x, hx, y, hy, hxy, Finset.notMem_empty x,
      Finset.notMem_empty y⟩
  have hpick : ∀ (P : Finset ℕ) (X : ℕ), ∃ b, b ∈ A ∧ X ≤ b ∧
      (PairFree A N₀ P → ∀ m, N₀ ≤ m → b ≤ m →
        ∃ x ∈ A, ∃ y ∈ A, x + y = m ∧
          x ∉ insert b P ∧ y ∉ insert b P) := by
    intro P X
    by_cases hfree : PairFree A N₀ P
    · obtain ⟨b, hbA, hXb, hbgood⟩ := hno P hfree X
      exact ⟨b, hbA, hXb, fun _ => hbgood⟩
    · obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov X
      exact ⟨b, hbA, hXb, fun h => absurd h hfree⟩
  choose pick hpickA hpickge hpickfree using hpick
  set st : ℕ → ℕ × Finset ℕ := fun j =>
    Nat.rec (pick ∅ 1, {pick ∅ 1})
      (fun _ prev => (pick prev.2 (prev.1 + 1),
        insert (pick prev.2 (prev.1 + 1)) prev.2)) j with hst
  have hstS : ∀ j, st (j + 1) = (pick (st j).2 ((st j).1 + 1),
      insert (pick (st j).2 ((st j).1 + 1)) (st j).2) := fun _ => rfl
  have hfreeS : ∀ j, PairFree A N₀ (st j).2 := by
    intro j
    induction j with
    | zero =>
      show PairFree A N₀ (insert (pick ∅ 1) ∅)
      exact pairFree_insert hfree0 (hpickfree ∅ 1 hfree0)
    | succ j ih =>
      rw [show (st (j + 1)).2 =
          insert (pick (st j).2 ((st j).1 + 1)) (st j).2 from
        by rw [hstS]]
      exact pairFree_insert ih (hpickfree (st j).2 ((st j).1 + 1) ih)
  have hlastge : ∀ j, j + 1 ≤ (st j).1 := by
    intro j
    induction j with
    | zero => simpa using hpickge ∅ 1
    | succ j ih =>
      have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
        rw [hstS]
      have h2 := hpickge (st j).2 ((st j).1 + 1)
      omega
  have hchain : ∀ i j, i ≤ j → (st i).2 ⊆ (st j).2 := by
    intro i j hij
    induction j with
    | zero =>
      have h0' : i = 0 := by omega
      subst h0'
      exact Finset.Subset.refl _
    | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · refine Finset.Subset.trans (ih (by omega)) ?_
        rw [hstS]
        exact Finset.subset_insert _ _
      · have h1 : i = j + 1 := by omega
        subst h1
        exact Finset.Subset.refl _
  have hlastmem : ∀ j, (st j).1 ∈ (st j).2 := by
    intro j
    cases j with
    | zero => exact Finset.mem_singleton_self _
    | succ j =>
      rw [hstS]
      exact Finset.mem_insert_self _ _
  have hlaststep : ∀ j, (st j).1 < (st (j + 1)).1 := by
    intro j
    have h1 : (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) := by
      rw [hstS]
    have h2 := hpickge (st j).2 ((st j).1 + 1)
    omega
  have hlastmono : StrictMono (fun j => (st j).1) :=
    strictMono_nat_of_lt_succ hlaststep
  set B : Set ℕ := Set.range (fun j => (st j).1) with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    show (st j).1 ∈ A
    cases j with
    | zero => exact hpickA ∅ 1
    | succ j =>
      rw [show (st (j + 1)).1 = pick (st j).2 ((st j).1 + 1) from
        by rw [hstS]]
      exact hpickA _ _
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hlastmono.injective
  refine hmin B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfreeS m m hm
  have havoid : ∀ w, w ≤ m → w ∉ (st m).2 → w ∉ B := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    have hi' : (st i).1 = w := hi
    rcases Nat.lt_or_ge m i with h' | h'
    · have := hlastge i
      omega
    · exact hwP (by
        rw [← hi']
        exact hchain i m h' (hlastmem i))
  exact ⟨x, hx, y, hy, havoid x (by omega) hxP,
    havoid y (by omega) hyP, hxy⟩

theorem double_cofinal_supply_of_counterexample {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P₃)) := by
  obtain ⟨P₂, hP₂free, X₂, h₂⟩ := pair_cofinal_supply_of_minimality hcov hmin
  obtain ⟨P₃, hP₃free, X₃, h₃⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  exact ⟨P₂, P₃, hP₂free, hP₃free, max X₂ X₃, fun b hb hXb =>
    ⟨h₂ b hb (le_trans (le_max_left _ _) hXb),
     h₃ b hb (le_trans (le_max_right _ _) hXb)⟩⟩

theorem two_required_elements_per_pair_target {A : Set ℕ} {N₀ t : ℕ}
    {P : Finset ℕ}
    (hfree : PairFree A N₀ P) (ht : N₀ ≤ t) :
    ∃ x₀ y₀, ∀ b, b ∉ P →
      (∀ x ∈ A, ∀ y ∈ A, x + y = t →
        x ∈ insert b P ∨ y ∈ insert b P) →
      b = x₀ ∨ b = y₀ := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy, hxP, hyP⟩ := hfree t ht
  refine ⟨x₀, y₀, fun b hbP hguard => ?_⟩
  rcases hguard x₀ hx₀ y₀ hy₀ hxy with h | h
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inl h'.symm
    · exact absurd h' hxP
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr h'.symm
    · exact absurd h' hyP

theorem three_required_elements_per_rep_target {A : Set ℕ} {N₀ m : ℕ}
    {P : Finset ℕ}
    (hfree : RepFree A N₀ P) (hm : N₀ ≤ m) :
    ∃ x₀ y₀ z₀, ∀ b, b ∉ P →
      IsRepSupportTransversal A m (insert b P) →
      b = x₀ ∨ b = y₀ ∨ b = z₀ := by
  obtain ⟨x₀, hx₀, y₀, hy₀, z₀, hz₀, hxyz, hxP, hyP, hzP⟩ := hfree m hm
  refine ⟨x₀, y₀, z₀, fun b hbP hguard => ?_⟩
  rcases hguard x₀ hx₀ y₀ hy₀ z₀ hz₀ hxyz with h | h | h
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inl h'.symm
    · exact absurd h' hxP
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr (Or.inl h'.symm)
    · exact absurd h' hyP
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr (Or.inr h'.symm)
    · exact absurd h' hzP

theorem r2_unbounded_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card := by
  classical
  intro C N
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  set c := P.card + 1 with hc
  have hcpos : 0 < c := by omega
  set C₀ := max C N with hC₀
  set D := c * (C₀ + 1) + c + 2 * N₀ + 2 with hD
  have hD1 : 1 ≤ D := by omega
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov
    (max X₀ ((D + 2 * N₀) * (D + 2 * N₀)))
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_left _ _) hXb)
  have hexp : (D + 2 * N₀) * (D + 2 * N₀) =
      D * D + 4 * (D * N₀) + 4 * (N₀ * N₀) := by ring
  have hDN : N₀ ≤ D * N₀ := by
    have h1 : 1 * N₀ ≤ D * N₀ := Nat.mul_le_mul_right N₀ hD1
    omega
  have hmbig : (D + 2 * N₀) * (D + 2 * N₀) ≤ m :=
    le_trans (le_trans (le_max_right _ _) hXb) hbm
  have h2N₀m : 2 * N₀ ≤ m := by omega
  have hsqrt := covering_sqrt_lower (A := A) (N₀ := N₀)
    (n := m - N₀) hcov (by omega)
  set F := (Finset.range (m - N₀ + 1)).filter (· ∈ A) with hF
  have hDF : D * D ≤ F.card * F.card := by omega
  have hDFle : D ≤ F.card := by
    have h1 := Nat.sqrt_le_sqrt hDF
    rw [Nat.sqrt_eq, Nat.sqrt_eq] at h1
    exact h1
  set H := insert b P with hH
  have hHcard : H.card ≤ c := by
    have := Finset.card_insert_le b P
    omega
  have hHpos : 0 < H.card :=
    Finset.card_pos.2 ⟨b, Finset.mem_insert_self b P⟩
  set W' := (Finset.range (m - N₀ + 1)).filter
    (fun w => w ∈ A ∧ w ∉ H) with hW'
  have hsub : F \ H ⊆ W' := by
    intro x hx
    obtain ⟨hxF, hxH⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨hxr, hxA⟩ := Finset.mem_filter.1 hxF
    exact Finset.mem_filter.2 ⟨hxr, hxA, hxH⟩
  have hW'card : D - c ≤ W'.card := by
    have h1 := Finset.le_card_sdiff H F
    have h2 := Finset.card_le_card hsub
    omega
  obtain ⟨h₀, hh₀, hblow⟩ := support_transversal_fan_amplification hcov hhub
    ⟨b, Finset.mem_insert_self b P⟩ hmN
  have hquot : C₀ + 1 ≤ W'.card / H.card := by
    have h1 : C₀ + 1 ≤ W'.card / c := by
      rw [Nat.le_div_iff_mul_le hcpos]
      have h2 : (C₀ + 1) * c = c * (C₀ + 1) := Nat.mul_comm _ _
      omega
    have h2 : W'.card / c ≤ W'.card / H.card :=
      Nat.div_le_div_left hHcard hHpos
    omega
  have hle := le_trans hquot hblow
  refine ⟨m - h₀, ?_, ?_⟩
  · have hcardle : ((Finset.range (m - h₀ + 1)).filter
        (fun x => x ∈ A ∧ (m - h₀ - x) ∈ A)).card ≤ m - h₀ + 1 := by
      have h1 := Finset.card_filter_le (Finset.range (m - h₀ + 1))
        (fun x => x ∈ A ∧ (m - h₀ - x) ∈ A)
      simpa using h1
    omega
  · omega

theorem counterexample_summary {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  ⟨canonical_cofinal_supply_pos_of_hfail h0 hcov hanchor hfail,
   double_cofinal_supply_of_counterexample h0 hcov hmin hfail,
   constant_sidon_of_hfail h0 hcov hfail,
   r2_unbounded_of_hfail h0 hcov hfail⟩

theorem minimalSupportTransversals_from_infiniteDeletion {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) (h0B : 0 ∉ B) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := by
  classical
  have hsing := singleton_support_transversals_refuted h0 hcov hanchor hfail
  push Not at hsing
  obtain ⟨Nₛ, hNₛ⟩ := hsing
  intro N
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push Not at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb (max N (max N₀ Nₛ))
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push Not at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hhub := failing_support_transversal_subset_deletion (B := B) hdead
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_support_transversal hhub
  have hH'B : ∀ h ∈ H', h ∈ B := by
    intro h hh
    exact (Finset.mem_filter.1 (hH'sub hh)).2
  have hH'ne : H'.Nonempty :=
    support_transversal_nonempty_of_covering h0 hcov
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN)
      hH'hub
  have hcard2 : 2 ≤ H'.card := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < H'.card := Finset.card_pos.2 hH'ne
    have hone : H'.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hone
    have haB : a ∈ B := hH'B a (ha ▸ Finset.mem_singleton_self a)
    have hapos : 0 < a := by
      by_contra ha0
      push Not at ha0
      have haz : a = 0 := by omega
      rw [haz] at haB
      exact h0B haB
    exact hNₛ n (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) hnN) a hapos (ha ▸ hH'hub)
  exact ⟨n, le_trans (le_max_left _ _) hnN, H', hH'hub, hH'min,
    hcard2, hH'B⟩

/-- Amplification instances of the rep cofinal supply: a support transversal target `m` required by
`b` over `P`, whose translate by `h₀ ∈ P ∪ {b}` carries at least
`C` pair representations. -/
def AmplificationAt (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ)
    [DecidablePred (· ∈ A)] (C m b h₀ : ℕ) : Prop :=
  b ∈ A ∧ N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P) ∧
  h₀ ∈ insert b P ∧
  C ≤ ((Finset.range (m - h₀ + 1)).filter
    (fun x => x ∈ A ∧ (m - h₀ - x) ∈ A)).card

/-- Amplification instances exist beyond every bound: the quantitative core
of `r2_unbounded_of_hfail`, with the offset data retained. -/
theorem amplification_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧
      ∀ C N, ∃ m b h₀, N ≤ m ∧ AmplificationAt A N₀ P C m b h₀ := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_cofinal_supply_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, fun C N => ?_⟩
  set c := P.card + 1 with hc
  have hcpos : 0 < c := by omega
  set C₀ := max C N with hC₀
  set D := c * (C₀ + 1) + c + 2 * N₀ + 2 with hD
  have hD1 : 1 ≤ D := by omega
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov
    (max X₀ ((D + 2 * N₀) * (D + 2 * N₀)))
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_left _ _) hXb)
  have hexp : (D + 2 * N₀) * (D + 2 * N₀) =
      D * D + 4 * (D * N₀) + 4 * (N₀ * N₀) := by ring
  have hDN : N₀ ≤ D * N₀ := by
    have h1 : 1 * N₀ ≤ D * N₀ := Nat.mul_le_mul_right N₀ hD1
    omega
  have hmbig : (D + 2 * N₀) * (D + 2 * N₀) ≤ m :=
    le_trans (le_trans (le_max_right _ _) hXb) hbm
  have h2N₀m : 2 * N₀ ≤ m := by omega
  have hsqrt := covering_sqrt_lower (A := A) (N₀ := N₀)
    (n := m - N₀) hcov (by omega)
  set F := (Finset.range (m - N₀ + 1)).filter (· ∈ A) with hF
  have hDF : D * D ≤ F.card * F.card := by omega
  have hDFle : D ≤ F.card := by
    have h1 := Nat.sqrt_le_sqrt hDF
    rw [Nat.sqrt_eq, Nat.sqrt_eq] at h1
    exact h1
  set H := insert b P with hH
  have hHcard : H.card ≤ c := by
    have := Finset.card_insert_le b P
    omega
  have hHpos : 0 < H.card :=
    Finset.card_pos.2 ⟨b, Finset.mem_insert_self b P⟩
  set W' := (Finset.range (m - N₀ + 1)).filter
    (fun w => w ∈ A ∧ w ∉ H) with hW'
  have hsub : F \ H ⊆ W' := by
    intro x hx
    obtain ⟨hxF, hxH⟩ := Finset.mem_sdiff.1 hx
    obtain ⟨hxr, hxA⟩ := Finset.mem_filter.1 hxF
    exact Finset.mem_filter.2 ⟨hxr, hxA, hxH⟩
  have hW'card : D - c ≤ W'.card := by
    have h1 := Finset.le_card_sdiff H F
    have h2 := Finset.card_le_card hsub
    omega
  obtain ⟨h₀, hh₀, hblow⟩ := support_transversal_fan_amplification hcov hhub
    ⟨b, Finset.mem_insert_self b P⟩ hmN
  have hquot : C₀ + 1 ≤ W'.card / H.card := by
    have h1 : C₀ + 1 ≤ W'.card / c := by
      rw [Nat.le_div_iff_mul_le hcpos]
      have h2 : (C₀ + 1) * c = c * (C₀ + 1) := Nat.mul_comm _ _
      omega
    have h2 : W'.card / c ≤ W'.card / H.card :=
      Nat.div_le_div_left hHcard hHpos
    omega
  have hle := le_trans hquot hblow
  have hmN' : N ≤ m := by
    have h1 : N ≤ C₀ + 1 := by omega
    have h2 : C₀ + 1 ≤ D := by
      have h3 : 1 * (C₀ + 1) ≤ c * (C₀ + 1) :=
        Nat.mul_le_mul_right (C₀ + 1) hcpos
      omega
    have h3 : D ≤ D * D := Nat.le_mul_of_pos_left D (by omega)
    omega
  exact ⟨m, b, h₀, hmN', hbA, hmN, hbm, hhub, hh₀, by omega⟩

theorem amplification_offset_dichotomy {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧
      ((∃ s₀ ∈ P, ∀ C N, ∃ m b, N ≤ m ∧
        AmplificationAt A N₀ P C m b s₀) ∨
      (∀ C N, ∃ m b, N ≤ m ∧ AmplificationAt A N₀ P C m b b)) := by
  classical
  obtain ⟨P, hPfree, hsupply⟩ := amplification_supply_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, ?_⟩
  by_cases hcorep : ∀ C N, ∃ m b, N ≤ m ∧ AmplificationAt A N₀ P C m b b
  · exact Or.inr hcorep
  · left
    push Not at hcorep
    obtain ⟨C₁, N₁, hblock⟩ := hcorep
    by_contra hnos
    push Not at hnos
    have hex : ∀ s, ∃ Cs Ns, s ∈ P →
        ∀ m b, Ns ≤ m → ¬AmplificationAt A N₀ P Cs m b s := by
      intro s
      by_cases hs : s ∈ P
      · obtain ⟨Cs, Ns, hCs⟩ := hnos s hs
        exact ⟨Cs, Ns, fun _ => hCs⟩
      · exact ⟨0, 0, fun h => absurd h hs⟩
    choose Cf Nf hCf using hex
    set Cmax := max C₁ (P.sup Cf) with hCmax
    set Nmax := max N₁ (P.sup Nf) with hNmax
    obtain ⟨m, b, h₀, hmN, hblow⟩ := hsupply Cmax Nmax
    have hCle : ∀ s ∈ P, Cf s ≤ Cmax := by
      intro s hs
      have := Finset.le_sup (f := Cf) hs
      omega
    have hNle : ∀ s ∈ P, Nf s ≤ Nmax := by
      intro s hs
      have := Finset.le_sup (f := Nf) hs
      omega
    have hmono : ∀ C' , C' ≤ Cmax → AmplificationAt A N₀ P Cmax m b h₀ →
        AmplificationAt A N₀ P C' m b h₀ := by
      intro C' hC' hB
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
      exact ⟨h1, h2, h3, h4, h5, by omega⟩
    rcases Finset.mem_insert.1 hblow.2.2.2.2.1 with hb | hP
    · subst hb
      exact hblock m h₀ (by
        have := le_max_left C₁ (P.sup Cf)
        have := le_max_right N₁ (P.sup Nf)
        omega) (hmono C₁ (le_max_left _ _) hblow)
    · exact hCf h₀ hP m b (by
        have := hNle h₀ hP
        omega) (hmono (Cf h₀) (hCle h₀ hP) hblow)

theorem pair_marked_element_reflection_exclusion_interval {A : Set ℕ} {n a z : ℕ}
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a)
    (hz : z ∈ A) (hzn : z ≤ n) (hza : z ≠ a) (hnza : n - z ≠ a) :
    n - z ∉ A := by
  intro hmem
  rcases hall z hz (n - z) hmem (by omega) with h | h
  · exact hza h
  · exact hnza h

theorem shared_pair_target_is_sum {A : Set ℕ} {N₀ t b b' : ℕ}
    {P : Finset ℕ}
    (hfree : PairFree A N₀ P) (ht : N₀ ≤ t) (hbb' : b ≠ b')
    (hg : ∀ x ∈ A, ∀ y ∈ A, x + y = t →
      x ∈ insert b P ∨ y ∈ insert b P)
    (hg' : ∀ x ∈ A, ∀ y ∈ A, x + y = t →
      x ∈ insert b' P ∨ y ∈ insert b' P) :
    t = b + b' := by
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfree t ht
  have h1 : x = b ∨ y = b := by
    rcases hg x hx y hy hxy with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inl h'
      · exact absurd h' hxP
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr h'
      · exact absurd h' hyP
  have h2 : x = b' ∨ y = b' := by
    rcases hg' x hx y hy hxy with h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inl h'
      · exact absurd h' hxP
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr h'
      · exact absurd h' hyP
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

theorem shared_rep_target_is_sum3 {A : Set ℕ} {N₀ m b₁ b₂ b₃ : ℕ}
    {P : Finset ℕ}
    (hfree : RepFree A N₀ P) (hm : N₀ ≤ m)
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃)
    (hg₁ : IsRepSupportTransversal A m (insert b₁ P))
    (hg₂ : IsRepSupportTransversal A m (insert b₂ P))
    (hg₃ : IsRepSupportTransversal A m (insert b₃ P)) :
    m = b₁ + b₂ + b₃ := by
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfree m hm
  have hpin : ∀ b, IsRepSupportTransversal A m (insert b P) →
      x = b ∨ y = b ∨ z = b := by
    intro b hg
    rcases hg x hx y hy z hz hxyz with h | h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inl h'
      · exact absurd h' hxP
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact absurd h' hyP
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inr h')
      · exact absurd h' hzP
  have hp₁ := hpin b₁ hg₁
  have hp₂ := hpin b₂ hg₂
  have hp₃ := hpin b₃ hg₃
  rcases hp₁ with h1 | h1 | h1 <;> rcases hp₂ with h2 | h2 | h2 <;>
    rcases hp₃ with h3 | h3 | h3 <;> omega

theorem free_prefixes_die_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ¬∀ J, RepFree A N₀ ((Finset.range J).image b) := by
  intro hfree
  classical
  set B : Set ℕ := Set.range b with hB
  have hBA : B ⊆ A := by
    rintro x ⟨j, rfl⟩
    exact hbA j
  have hBinf : B.Infinite :=
    Set.infinite_range_of_injective hmono.injective
  have hidx : ∀ j, j ≤ b j := fun j => hmono.le_apply
  refine hfail B hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ :=
    hfree (m + 1) m hm
  have havoid : ∀ w, w ≤ m →
      w ∉ (Finset.range (m + 1)).image b → w ∉ B := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    rcases Nat.lt_or_ge i (m + 1) with h' | h'
    · exact hwP (Finset.mem_image.2 ⟨i, Finset.mem_range.2 h', hi⟩)
    · have h1 := hidx i
      have h2 : (fun j => b j) i = w := hi
      omega
  refine ⟨![x, y, z], ?_, by simp [Fin.sum_univ_three]; omega⟩
  intro i
  match i with
  | 0 => exact ⟨hx, havoid x (by omega) hxP⟩
  | 1 => exact ⟨hy, havoid y (by omega) hyP⟩
  | 2 => exact ⟨hz, havoid z (by omega) hzP⟩

theorem pair_free_prefixes_die_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ¬∀ J, PairFree A N₀ ((Finset.range J).image b) := by
  intro hfree
  classical
  have hBA : Set.range b ⊆ A := by
    rintro x ⟨j, rfl⟩
    exact hbA j
  have hBinf : (Set.range b).Infinite :=
    Set.infinite_range_of_injective hmono.injective
  have hidx : ∀ j, j ≤ b j := fun j => hmono.le_apply
  refine hmin (Set.range b) hBA hBinf ⟨N₀, fun m hm => ?_⟩
  obtain ⟨x, hx, y, hy, hxy, hxP, hyP⟩ := hfree (m + 1) m hm
  have havoid : ∀ w, w ≤ m →
      w ∉ (Finset.range (m + 1)).image b → w ∉ Set.range b := by
    intro w hwm hwP
    rintro ⟨i, hi⟩
    rcases Nat.lt_or_ge i (m + 1) with h' | h'
    · exact hwP (Finset.mem_image.2 ⟨i, Finset.mem_range.2 h', hi⟩)
    · have h1 := hidx i
      have h2 : b i = w := hi
      omega
  exact ⟨x, hx, y, hy, havoid x (by omega) hxP,
    havoid y (by omega) hyP, hxy⟩

theorem corep_offset_dichotomy {A : Set ℕ} {N₀ : ℕ}
    (hstream : ∀ X, ∃ a w, a ∈ A ∧ w ∈ A ∧ X ≤ a ∧ N₀ ≤ a + w ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = a + w → x = a ∨ y = a) :
    (∃ w₀, w₀ ∈ A ∧ ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ N₀ ≤ a + w₀ ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = a + w₀ → x = a ∨ y = a) ∨
    (∀ W X, ∃ a w, a ∈ A ∧ w ∈ A ∧ X ≤ a ∧ W < w ∧ N₀ ≤ a + w ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = a + w → x = a ∨ y = a) := by
  classical
  by_cases hbnd : ∃ W, ∀ X, ∃ a w, a ∈ A ∧ w ∈ A ∧ X ≤ a ∧ w ≤ W ∧
      N₀ ≤ a + w ∧ ∀ x ∈ A, ∀ y ∈ A, x + y = a + w → x = a ∨ y = a
  · left
    obtain ⟨W, hW⟩ := hbnd
    obtain ⟨w₀, hw₀W, hcof⟩ := cofinal_value_pigeonhole
      (P := fun a w => a ∈ A ∧ w ∈ A ∧ N₀ ≤ a + w ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = a + w → x = a ∨ y = a)
      (fun N => by
        obtain ⟨a, w, ha, hw, hXa, hwW, hNn, hall⟩ := hW N
        exact ⟨a, hXa, w, hwW, ha, hw, hNn, hall⟩)
    have hw₀A : w₀ ∈ A := by
      obtain ⟨a, -, -, hw, -, -⟩ := hcof 0
      exact hw
    refine ⟨w₀, hw₀A, fun X => ?_⟩
    obtain ⟨a, hXa, ha, hw, hNn, hall⟩ := hcof X
    exact ⟨a, ha, hXa, hNn, hall⟩
  · right
    push Not at hbnd
    intro W X
    obtain ⟨X', hX'⟩ := hbnd W
    obtain ⟨a, w, ha, hw, hXa, hNn, hall⟩ := hstream (max X X')
    have hwW : W < w := by
      by_contra hle
      push Not at hle
      obtain ⟨x, hx, y, hy, hxy, hxa, hya⟩ :=
        hX' a w ha hw (le_trans (le_max_right _ _) hXa) hle hNn
      rcases hall x hx y hy hxy with h | h
      · exact hxa h
      · exact hya h
    exact ⟨a, w, ha, hw, le_trans (le_max_left _ _) hXa, hwW, hNn,
      hall⟩

theorem required_element_difference_exclusion_interval {A : Set ℕ} {w₀ a a' : ℕ}
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = a + w₀ → x = a ∨ y = a)
    (ha' : a' ∈ A) (hle : a' ≤ a + w₀) (hne : a' ≠ a)
    (hnw : a' ≠ w₀) :
    a + w₀ - a' ∉ A :=
  pair_marked_element_reflection_exclusion_interval hall ha' hle hne (by omega)

theorem pair_cofinal_supply_two_envelopes {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ E₀ E₁ : Finset ℕ, (∀ h ∈ E₀, h ∈ A ∧ 0 < h) ∧
      (∀ h ∈ E₁, h ∈ A ∧ 0 < h) ∧
      (∀ h ∈ E₁, h ∉ E₀) ∧
      PairFree A N₀ E₀ ∧ PairFree A N₀ E₁ ∧
      ∃ X, ∀ b ∈ A, X ≤ b → b ∉ E₀ →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b E₀ ∨ y ∈ insert b E₀) ∧
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b E₁ ∨ y ∈ insert b E₁) := by
  classical
  have hpos : ∀ X : ℕ, ∃ p ∈ {a | a ∈ A ∧ 0 < a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X 1)
    refine ⟨a, ⟨ha, ?_⟩, le_trans (le_max_left _ _) hXa⟩
    have := le_trans (le_max_right _ _) hXa
    omega
  obtain ⟨E₀, hE₀P, hE₀free, X₀, hf₀⟩ :=
    pair_cofinal_supply_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
      (fun a ha => ha.1) (fun h => by have := h.2; omega) hpos hfail
  have hpos' : ∀ X : ℕ,
      ∃ p ∈ {a | a ∈ A ∧ 0 < a ∧ a ∉ E₀}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov
      (max (max X 1) ((E₀.sup id) + 1))
    have h1 : (E₀.sup id) + 1 ≤ a := le_trans (le_max_right _ _) hXa
    have h2 : 1 ≤ a :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXa
    refine ⟨a, ⟨ha, by omega, fun haE => ?_⟩,
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXa⟩
    have h3 : a ≤ E₀.sup id := Finset.le_sup (f := id) haE
    omega
  obtain ⟨E₁, hE₁P, hE₁free, X₁, hf₁⟩ :=
    pair_cofinal_supply_pool (P₀ := {a | a ∈ A ∧ 0 < a ∧ a ∉ E₀}) h0 hcov
      (fun a ha => ha.1) (fun h => by have := h.2.1; omega) hpos'
      hfail
  refine ⟨E₀, E₁, fun h hh => hE₀P h hh,
    fun h hh => ⟨(hE₁P h hh).1, (hE₁P h hh).2.1⟩,
    fun h hh => (hE₁P h hh).2.2, hE₀free, hE₁free,
    max (max X₀ X₁) 1, fun b hbA hXb hbE₀ => ?_⟩
  have hb1 : 0 < b := by
    have := le_trans (le_max_right _ _) hXb
    omega
  constructor
  · exact hf₀ b ⟨hbA, hb1⟩
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXb)
  · exact hf₁ b ⟨hbA, hb1, hbE₀⟩
      (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXb)

theorem support_transversal_server_dichotomy {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) (h0B : 0 ∉ B) :
    (∃ b ∈ B, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B) ∧ b ∈ H) ∨
    (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B) ∧ ∀ h ∈ H, W < h) := by
  classical
  have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
    hfail hBA hBinf h0B
  set Q : ℕ → Finset ℕ → Prop := fun n H =>
    IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
    2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B with hQdef
  have hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H := by
    intro N
    obtain ⟨n, hn, H, h1, h2, h3, h4⟩ := hteams N
    exact ⟨n, hn, H, h1, h2, h3, h4⟩
  by_cases hserv : ∃ b, ∀ N, ∃ n, N ≤ n ∧ ∃ H, Q n H ∧ b ∈ H
  · left
    obtain ⟨b, hb⟩ := hserv
    have hbB : b ∈ B := by
      obtain ⟨n, -, H, hQH, hbH⟩ := hb 0
      have hinst : IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
      exact hinst.2.2.2 b hbH
    refine ⟨b, hbB, fun N => ?_⟩
    obtain ⟨n, hn, H, hQH, hbH⟩ := hb N
    have hinst : IsRepSupportTransversal A n H ∧
        (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
    exact ⟨n, hn, H, hinst.1, hinst.2.1, hinst.2.2.1,
      hinst.2.2.2, hbH⟩
  · right
    intro W N
    rcases cofinal_dichotomy Q hQ W with ⟨b, hbW, hper⟩ | havoid
    · exact absurd ⟨b, hper⟩ hserv
    · obtain ⟨n, hn, H, hQH, hbig⟩ := havoid N
      have hinst : IsRepSupportTransversal A n H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
      exact ⟨n, hn, H, hinst.1, hinst.2.1, hinst.2.2.1,
        hinst.2.2.2, hbig⟩

/-- Adapter: problem-native ℵ₀-minimality (no infinite deletion
leaves an exact order-2 tuple basis) implies the elementwise
minimality the cofinal supply machinery consumes. -/
theorem minimality_elementwise_of_tuple {A : Set ℕ}
    (hmin : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2) :
    ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n := by
  rintro B hBA hBinf ⟨N₁, hN₁⟩
  refine hmin B hBA hBinf ⟨N₁, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, hxB, hyB, hxy⟩ := hN₁ n hn
  refine ⟨![x, y], ?_, by simpa [Fin.sum_univ_two] using hxy⟩
  intro i
  match i with
  | 0 => exact ⟨hx, hxB⟩
  | 1 => exact ⟨hy, hyB⟩

theorem counterexample_summary' {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepSupportTransversal A m H ∧
          (∀ h ∈ H, ¬IsRepSupportTransversal A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepSupportTransversal A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  counterexample_summary h0 hcov hanchor
    (minimality_elementwise_of_tuple hmin) hfail

theorem rep_pair_clique_or_triple_pair_transversals {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        3 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  set c : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} then true else false
    with hc
  have hciff : ∀ i j, c i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j}
    · simp [hc, h]
    · simp [hc, h]
  obtain ⟨f, hfmono, bcol, hhom⟩ := infinite_ramsey_pairs c
  refine ⟨f, hfmono, ?_⟩
  rcases Bool.eq_false_or_eq_true bcol with hbc | hbc
  · -- clique branch
    left
    subst hbc
    intro i j hij
    have h1 := hhom i j hij
    exact (hciff (f i) (f j)).1 h1
  · -- pair-support transversal-free branch: pair transversals have card ≥ 3
    right
    subst hbc
    have hcomp : StrictMono (fun i => b (f i)) :=
      fun i j hij => hmono (hfmono hij)
    have hBA : Set.range (fun i => b (f i)) ⊆ A := by
      rintro x ⟨i, rfl⟩
      exact hbA (f i)
    have hBinf : (Set.range (fun i => b (f i))).Infinite :=
      Set.infinite_range_of_injective hcomp.injective
    have h0B : 0 ∉ Set.range (fun i => b (f i)) := by
      rintro ⟨i, hi⟩
      have h1 : b (f i) = 0 := hi
      have := hbpos (f i)
      omega
    have hnopair : ∀ i j, i < j →
        ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {b (f i), b (f j)} := by
      intro i j hij hex
      have h1 := (hciff (f i) (f j)).2 hex
      rw [hhom i j hij] at h1
      exact Bool.false_ne_true h1
    have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
      hfail hBA hBinf h0B
    intro N
    obtain ⟨n, hn, H, hhub, hmin, hcard2, hHB⟩ := hteams (max N N₀)
    have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hmin, ?_, hHB⟩
    rcases Nat.lt_or_ge H.card 3 with hlt | hge
    · exfalso
      have hcard : H.card = 2 := by omega
      obtain ⟨u, v, huv, hHuv⟩ := Finset.card_eq_two.1 hcard
      obtain ⟨i, hi⟩ := hHB u (hHuv ▸ Finset.mem_insert_self u {v})
      obtain ⟨j, hj⟩ := hHB v (hHuv ▸ Finset.mem_insert_of_mem
        (Finset.mem_singleton_self v))
      have hi' : b (f i) = u := hi
      have hj' : b (f j) = v := hj
      have hij : i ≠ j := by
        intro h
        rw [h, hj'] at hi'
        exact huv hi'.symm
      rcases Nat.lt_or_ge i j with hlt' | hge'
      · refine hnopair i j hlt' ⟨n, hnN₀, ?_⟩
        have hpair : ({b (f i), b (f j)} : Finset ℕ) = H := by
          rw [hi', hj', hHuv]
        rw [hpair]
        exact hhub
      · have hlt'' : j < i := by omega
        refine hnopair j i hlt'' ⟨n, hnN₀, ?_⟩
        have hpair : ({b (f j), b (f i)} : Finset ℕ) = H := by
          rw [hi', hj', hHuv, Finset.pair_comm]
        rw [hpair]
        exact hhub
    · exact hge

theorem clique_rows_march {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (e : ℕ → ℕ) (hemono : StrictMono e) (hepos : ∀ i, 0 < e i) :
    ¬(∀ X, ∃ i, X ≤ i ∧ ∃ n, N₀ ≤ n ∧ ∀ J, ∃ j, J ≤ j ∧ i < j ∧
      IsRepSupportTransversal A n {e i, e j}) := by
  intro hstable
  refine singleton_support_transversals_refuted h0 hcov hanchor hfail ?_
  intro N
  obtain ⟨i, hNi, n, hnN₀, hrow⟩ := hstable N
  -- a column beyond the target
  obtain ⟨j, hJj, hij, hhub⟩ := hrow (n + 1)
  have hejn : n < e j := by
    have h1 : n + 1 ≤ j := hJj
    have h2 : j ≤ e j := hemono.le_apply
    omega
  -- every representation must hit the row element
  have hsing : IsRepSupportTransversal A n {e i} := by
    intro x hx y hy z hz hsum
    rcases hhub x hx y hy z hz hsum with h | h | h
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inl (Finset.mem_singleton.2 h')
      · have := Finset.mem_singleton.1 h'
        omega
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inl (Finset.mem_singleton.2 h'))
      · have := Finset.mem_singleton.1 h'
        omega
    · rcases Finset.mem_insert.1 h with h' | h'
      · exact Or.inr (Or.inr (Finset.mem_singleton.2 h'))
      · have := Finset.mem_singleton.1 h'
        omega
  -- the row element sits below its target via a hit representation
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hnN₀
  have hein : e i ≤ n := by
    rcases hsing x hx y hy 0 h0 (by omega) with h | h | h
    · have := Finset.mem_singleton.1 h
      omega
    · have := Finset.mem_singleton.1 h
      omega
    · have := Finset.mem_singleton.1 h
      have := hepos i
      omega
  have hNei : N ≤ n := by
    have h1 : i ≤ e i := hemono.le_apply
    omega
  exact ⟨n, hNei, e i, hepos i, hsing⟩

theorem injective_pair_cofinal_supply {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧
      ∃ (g : ℕ → ℕ) (t : ℕ → ℕ), StrictMono g ∧
        (∀ k, g k ∈ A) ∧ (∀ k l, k ≠ l → t k ≠ t l) ∧
        ∀ k, N₀ ≤ t k ∧ g k ≤ t k ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t k →
            x ∈ insert (g k) P ∨ y ∈ insert (g k) P := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_cofinal_supply_of_hfail h0 hcov hfail
  -- ground stream of large elements with chosen targets
  have hpick : ∀ X : ℕ, ∃ a, a ∈ A ∧ X < a := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (X + 1)
    exact ⟨a, ha, by omega⟩
  choose nx hnxA hnxgt using hpick
  set base : ℕ → ℕ := fun k =>
    Nat.rec (nx (max X₀ (P.sup id))) (fun _ prev => nx prev) k
    with hbase
  have hbaseS : ∀ k, base (k + 1) = nx (base k) := fun _ => rfl
  have hbaseA : ∀ k, base k ∈ A := by
    intro k
    cases k with
    | zero => exact hnxA _
    | succ k =>
      rw [hbaseS]
      exact hnxA _
  have hbasemono : StrictMono base := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hbaseS]
    exact hnxgt (base k)
  have hbaseX : ∀ k, X₀ ≤ base k := by
    intro k
    have h1 : base 0 = nx (max X₀ (P.sup id)) := rfl
    have h2 : max X₀ (P.sup id) < base 0 := by
      rw [h1]
      exact hnxgt _
    have h3 : base 0 ≤ base k := hbasemono.monotone (Nat.zero_le k)
    have := le_max_left X₀ (P.sup id)
    omega
  have hbaseP : ∀ k, base k ∉ P := by
    intro k hkP
    have h1 : base k ≤ P.sup id := Finset.le_sup (f := id) hkP
    have h2 : max X₀ (P.sup id) < base 0 := hnxgt _
    have h3 : base 0 ≤ base k := hbasemono.monotone (Nat.zero_le k)
    have := le_max_right X₀ (P.sup id)
    omega
  -- chosen targets
  have htarget : ∀ k, ∃ m, N₀ ≤ m ∧ base k ≤ m ∧
      ∀ x ∈ A, ∀ y ∈ A, x + y = m →
        x ∈ insert (base k) P ∨ y ∈ insert (base k) P :=
    fun k => hflood (base k) (hbaseA k) (hbaseX k)
  choose tg htgN htgge htghub using htarget
  -- Ramsey on target equality
  set c : ℕ → ℕ → Bool := fun k l =>
    if tg k = tg l then true else false with hc
  obtain ⟨f, hfmono, bcol, hhom⟩ := infinite_ramsey_pairs c
  rcases Bool.eq_false_or_eq_true bcol with hbc | hbc
  · -- all-sharing: three required elements on one target, impossible
    exfalso
    subst hbc
    have h01 := hhom 0 1 (by omega)
    have h02 := hhom 0 2 (by omega)
    have heq01 : tg (f 0) = tg (f 1) := by
      by_contra hne
      simp [hc, hne] at h01
    have heq02 : tg (f 0) = tg (f 2) := by
      by_contra hne
      simp [hc, hne] at h02
    obtain ⟨x₀, y₀, hpin⟩ := two_required_elements_per_pair_target hPfree
      (htgN (f 0)) (t := tg (f 0))
    have hg01 : base (f 0) ≠ base (f 1) :=
      fun h => absurd (hbasemono.injective h)
        (by have := hfmono (by omega : (0:ℕ) < 1); omega)
    have hg02 : base (f 0) ≠ base (f 2) :=
      fun h => absurd (hbasemono.injective h)
        (by have := hfmono (by omega : (0:ℕ) < 2); omega)
    have hg12 : base (f 1) ≠ base (f 2) :=
      fun h => absurd (hbasemono.injective h)
        (by have := hfmono (by omega : (1:ℕ) < 2); omega)
    have hp0 := hpin (base (f 0)) (hbaseP (f 0)) (htghub (f 0))
    have hp1 := hpin (base (f 1)) (hbaseP (f 1))
      (heq01 ▸ htghub (f 1))
    have hp2 := hpin (base (f 2)) (hbaseP (f 2))
      (heq02 ▸ htghub (f 2))
    rcases hp0 with h | h <;> rcases hp1 with h' | h' <;>
      rcases hp2 with h'' | h'' <;>
      first
        | exact hg01 (h.trans h'.symm)
        | exact hg02 (h.trans h''.symm)
        | exact hg12 (h'.trans h''.symm)
  · -- no sharing on the subsequence: injective targets
    subst hbc
    refine ⟨P, hPfree, fun k => base (f k), fun k => tg (f k),
      fun k l hkl => hbasemono (hfmono hkl),
      fun k => hbaseA (f k), ?_, fun k =>
        ⟨htgN (f k), htgge (f k), htghub (f k)⟩⟩
    intro k l hkl heq
    rcases Nat.lt_or_ge k l with h' | h'
    · have := hhom k l h'
      simp [hc, heq] at this
    · have hlk : l < k := by omega
      have := hhom l k hlk
      simp [hc, heq.symm] at this

/-- Sorted-index normalization for a three-element set of values of
a strictly monotone sequence. -/
lemma sorted_indices_of_card_three {e : ℕ → ℕ} (hmono : StrictMono e)
    {H : Finset ℕ} (hcard : H.card = 3)
    (hmem : ∀ h ∈ H, ∃ i, e i = h) :
    ∃ i j k, i < j ∧ j < k ∧ ({e i, e j, e k} : Finset ℕ) = H := by
  classical
  obtain ⟨u, v, w, huv, huw, hvw, hHuvw⟩ := Finset.card_eq_three.1 hcard
  obtain ⟨iu, hiu⟩ := hmem u (hHuvw ▸ by simp)
  obtain ⟨iv, hiv⟩ := hmem v (hHuvw ▸ by simp)
  obtain ⟨iw, hiw⟩ := hmem w (hHuvw ▸ by simp)
  have hij : iu ≠ iv := fun h => huv (by rw [← hiu, ← hiv, h])
  have hik : iu ≠ iw := fun h => huw (by rw [← hiu, ← hiw, h])
  have hjk : iv ≠ iw := fun h => hvw (by rw [← hiv, ← hiw, h])
  rcases Nat.lt_trichotomy iu iv with h1 | h1 | h1 <;>
    [skip; exact absurd h1 hij; skip] <;>
  rcases Nat.lt_trichotomy iv iw with h2 | h2 | h2 <;>
    [skip; exact absurd h2 hjk; skip; skip; exact absurd h2 hjk; skip] <;>
  rcases Nat.lt_trichotomy iu iw with h3 | h3 | h3 <;>
    first
      | exact absurd h3 hik
      | (first
          | exact ⟨iu, iv, iw, h1, h2, by
              rw [hiu, hiv, hiw, hHuvw]⟩
          | exact ⟨iu, iw, iv, h3, by omega, by
              rw [hiu, hiv, hiw, hHuvw]
              ext z
              simp
              tauto⟩
          | exact ⟨iw, iu, iv, by omega, h1, by
              rw [hiu, hiv, hiw, hHuvw]
              ext z
              simp
              tauto⟩
          | exact ⟨iv, iu, iw, by omega, by omega, by
              rw [hiu, hiv, hiw, hHuvw]
              ext z
              simp
              tauto⟩
          | exact ⟨iv, iw, iu, h2, by omega, by
              rw [hiu, hiv, hiw, hHuvw]
              ext z
              simp
              tauto⟩
          | exact ⟨iw, iv, iu, by omega, by omega, by
              rw [hiu, hiv, hiw, hHuvw]
              ext z
              simp
              tauto⟩
          | omega)

theorem pair_transversal_card_escalation_two {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j), b (f k)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        4 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  -- arity two
  set c₂ : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} then true else false
    with hc₂
  have hc₂iff : ∀ i j, c₂ i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j}
    · simp [hc₂, h]
    · simp [hc₂, h]
  obtain ⟨f₁, hf₁, b₂col, hhom₂⟩ := infinite_ramsey_pairs c₂
  rcases Bool.eq_false_or_eq_true b₂col with hb₂ | hb₂
  · -- pair clique
    subst hb₂
    exact ⟨f₁, hf₁, Or.inl (fun i j hij =>
      (hc₂iff (f₁ i) (f₁ j)).1 (hhom₂ i j hij))⟩
  · subst hb₂
    -- arity three on the pair-free subsequence
    set e : ℕ → ℕ := fun i => b (f₁ i) with he
    have hemono : StrictMono e := fun i j hij => hmono (hf₁ hij)
    set c₃ : ℕ → ℕ → ℕ → Bool := fun i j k =>
      if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k} then true
      else false with hc₃
    have hc₃iff : ∀ i j k, c₃ i j k = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k} := by
      intro i j k
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k}
      · simp [hc₃, h]
      · simp [hc₃, h]
    obtain ⟨f₂, hf₂, b₃col, hhom₃⟩ := infinite_ramsey_triples c₃
    rcases Bool.eq_false_or_eq_true b₃col with hb₃ | hb₃
    · -- triple clique on the composed subsequence
      subst hb₃
      refine ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr (Or.inl ?_)⟩
      intro i j k hij hjk
      exact (hc₃iff (f₂ i) (f₂ j) (f₂ k)).1 (hhom₃ i j k hij hjk)
    · subst hb₃
      refine ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr (Or.inr ?_)⟩
      set g : ℕ → ℕ := fun i => b ((f₁ ∘ f₂) i) with hgdef
      have hgmono : StrictMono g :=
        fun i j hij => hmono (hf₁ (hf₂ hij))
      have hBA : Set.range g ⊆ A := by
        rintro x ⟨i, rfl⟩
        exact hbA _
      have hBinf : (Set.range g).Infinite :=
        Set.infinite_range_of_injective hgmono.injective
      have h0B : 0 ∉ Set.range g := by
        rintro ⟨i, hi⟩
        have h1 : b ((f₁ ∘ f₂) i) = 0 := hi
        have := hbpos ((f₁ ∘ f₂) i)
        omega
      have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
        hfail hBA hBinf h0B
      intro N
      obtain ⟨n, hn, H, hhub, hminH, hcard2, hHB⟩ := hteams (max N N₀)
      have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
      refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hminH,
        ?_, hHB⟩
      rcases Nat.lt_or_ge H.card 4 with hlt | hge
      · exfalso
        rcases Nat.lt_or_ge H.card 3 with hlt2 | hge2
        · -- card 2: pair colour was false
          have hcard : H.card = 2 := by omega
          obtain ⟨u, v, huv, hHuv⟩ := Finset.card_eq_two.1 hcard
          obtain ⟨i, hi⟩ := hHB u (hHuv ▸ Finset.mem_insert_self _ _)
          obtain ⟨j, hj⟩ := hHB v (hHuv ▸ Finset.mem_insert_of_mem
            (Finset.mem_singleton_self v))
          have hi' : b (f₁ (f₂ i)) = u := hi
          have hj' : b (f₁ (f₂ j)) = v := hj
          have hij : i ≠ j := by
            intro h
            rw [h, hj'] at hi'
            exact huv hi'.symm
          have hkill : ∀ i' j', i' < j' →
              ¬∃ m, N₀ ≤ m ∧
                IsRepSupportTransversal A m {b (f₁ i'), b (f₁ j')} := by
            intro i' j' hij' hex
            have h1 := (hc₂iff (f₁ i') (f₁ j')).2 hex
            rw [hhom₂ i' j' hij'] at h1
            exact Bool.false_ne_true h1
          rcases Nat.lt_or_ge i j with h' | h'
          · refine hkill (f₂ i) (f₂ j) (hf₂ h') ⟨n, hnN₀, ?_⟩
            have hpair : ({b (f₁ (f₂ i)), b (f₁ (f₂ j))} :
                Finset ℕ) = H := by
              rw [hi', hj', hHuv]
            rw [hpair]
            exact hhub
          · have h'' : j < i := by omega
            refine hkill (f₂ j) (f₂ i) (hf₂ h'') ⟨n, hnN₀, ?_⟩
            have hpair : ({b (f₁ (f₂ j)), b (f₁ (f₂ i))} :
                Finset ℕ) = H := by
              rw [hi', hj', hHuv, Finset.pair_comm]
            rw [hpair]
            exact hhub
        · -- card 3: triple colour was false
          have hcard : H.card = 3 := by omega
          have hmem : ∀ h ∈ H, ∃ i, g i = h := hHB
          obtain ⟨i, j, k, hij, hjk, hset⟩ :=
            sorted_indices_of_card_three hgmono hcard hmem
          have hkill : ¬∃ m, N₀ ≤ m ∧
              IsRepSupportTransversal A m {e (f₂ i), e (f₂ j), e (f₂ k)} := by
            intro hex
            have h1 := (hc₃iff (f₂ i) (f₂ j) (f₂ k)).2 hex
            rw [hhom₃ i j k hij hjk] at h1
            exact Bool.false_ne_true h1
          refine hkill ⟨n, hnN₀, ?_⟩
          have hgg : ∀ l, e (f₂ l) = g l := fun _ => rfl
          rw [hgg i, hgg j, hgg k, hset]
          exact hhub
      · exact hge

theorem pair_transversal_target_dominates {A : Set ℕ} {N₀ n u v w : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {u, v})
    (hn : N₀ ≤ n) (hhub : IsRepSupportTransversal A n {u, v, w}) :
    w ≤ n := by
  by_contra hgt
  push Not at hgt
  refine hpf ⟨n, hn, ?_⟩
  intro x hx y hy z hz hsum
  rcases hhub x hx y hy z hz hsum with h | h | h
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inl (Finset.mem_insert.2 (Or.inl h'))
    · rcases Finset.mem_insert.1 h' with h'' | h''
      · exact Or.inl (Finset.mem_insert.2 (Or.inr (by
          simpa using h'')))
      · have := Finset.mem_singleton.1 h''
        omega
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr (Or.inl (Finset.mem_insert.2 (Or.inl h')))
    · rcases Finset.mem_insert.1 h' with h'' | h''
      · exact Or.inr (Or.inl (Finset.mem_insert.2 (Or.inr (by
          simpa using h''))))
      · have := Finset.mem_singleton.1 h''
        omega
  · rcases Finset.mem_insert.1 h with h' | h'
    · exact Or.inr (Or.inr (Finset.mem_insert.2 (Or.inl h')))
    · rcases Finset.mem_insert.1 h' with h'' | h''
      · exact Or.inr (Or.inr (Finset.mem_insert.2 (Or.inr (by
          simpa using h''))))
      · have := Finset.mem_singleton.1 h''
        omega

/-- Escalation step two with the freeness data exported: the
triple-clique branch records pair-freeness (so
`pair_transversal_target_dominates` applies to every clique support transversal), and the
pair transversal branch records freeness at both arities. -/
theorem pair_transversal_card_escalation_two' {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j)}) ∨
      ((∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
          IsRepSupportTransversal A n {b (f i), b (f j)}) ∧
        (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
          IsRepSupportTransversal A n {b (f i), b (f j), b (f k)})) ∨
      ((∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
          IsRepSupportTransversal A n {b (f i), b (f j)}) ∧
        (∀ i j k, i < j → j < k → ¬∃ n, N₀ ≤ n ∧
          IsRepSupportTransversal A n {b (f i), b (f j), b (f k)}) ∧
        ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
          IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
          4 ≤ H.card ∧
          ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  set c₂ : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} then true else false
    with hc₂
  have hc₂iff : ∀ i j, c₂ i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b i, b j}
    · simp [hc₂, h]
    · simp [hc₂, h]
  obtain ⟨f₁, hf₁, b₂col, hhom₂⟩ := infinite_ramsey_pairs c₂
  rcases Bool.eq_false_or_eq_true b₂col with hb₂ | hb₂
  · subst hb₂
    exact ⟨f₁, hf₁, Or.inl (fun i j hij =>
      (hc₂iff (f₁ i) (f₁ j)).1 (hhom₂ i j hij))⟩
  · subst hb₂
    have hpf₁ : ∀ i j, i < j →
        ¬∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {b (f₁ i), b (f₁ j)} := by
      intro i j hij hex
      have h1 := (hc₂iff (f₁ i) (f₁ j)).2 hex
      rw [hhom₂ i j hij] at h1
      exact Bool.false_ne_true h1
    set e : ℕ → ℕ := fun i => b (f₁ i) with he
    set c₃ : ℕ → ℕ → ℕ → Bool := fun i j k =>
      if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k} then true
      else false with hc₃
    have hc₃iff : ∀ i j k, c₃ i j k = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k} := by
      intro i j k
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k}
      · simp [hc₃, h]
      · simp [hc₃, h]
    obtain ⟨f₂, hf₂, b₃col, hhom₃⟩ := infinite_ramsey_triples c₃
    have hpfc : ∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j)} :=
      fun i j hij => hpf₁ (f₂ i) (f₂ j) (hf₂ hij)
    rcases Bool.eq_false_or_eq_true b₃col with hb₃ | hb₃
    · subst hb₃
      refine ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr (Or.inl ⟨hpfc, ?_⟩)⟩
      intro i j k hij hjk
      exact (hc₃iff (f₂ i) (f₂ j) (f₂ k)).1 (hhom₃ i j k hij hjk)
    · subst hb₃
      have htfc : ∀ i j k, i < j → j < k → ¬∃ n, N₀ ≤ n ∧
          IsRepSupportTransversal A n {b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j),
            b ((f₁ ∘ f₂) k)} := by
        intro i j k hij hjk hex
        have h1 := (hc₃iff (f₂ i) (f₂ j) (f₂ k)).2 hex
        rw [hhom₃ i j k hij hjk] at h1
        exact Bool.false_ne_true h1
      obtain ⟨f, hf, hout⟩ := pair_transversal_card_escalation_two h0 hcov
        hanchor hfail b hmono hbA hbpos
      -- reuse the concrete third-branch construction instead:

      clear hout hf f
      refine ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr (Or.inr
        ⟨hpfc, htfc, ?_⟩)⟩
      set g : ℕ → ℕ := fun i => b ((f₁ ∘ f₂) i) with hgdef
      have hgmono : StrictMono g :=
        fun i j hij => hmono (hf₁ (hf₂ hij))
      have hBA : Set.range g ⊆ A := by
        rintro x ⟨i, rfl⟩
        exact hbA _
      have hBinf : (Set.range g).Infinite :=
        Set.infinite_range_of_injective hgmono.injective
      have h0B : 0 ∉ Set.range g := by
        rintro ⟨i, hi⟩
        have h1 : b ((f₁ ∘ f₂) i) = 0 := hi
        have := hbpos ((f₁ ∘ f₂) i)
        omega
      have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
        hfail hBA hBinf h0B
      intro N
      obtain ⟨n, hn, H, hhub, hminH, hcard2, hHB⟩ :=
        hteams (max N N₀)
      have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
      refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hminH,
        ?_, hHB⟩
      rcases Nat.lt_or_ge H.card 4 with hlt | hge
      · exfalso
        rcases Nat.lt_or_ge H.card 3 with hlt2 | hge2
        · have hcard : H.card = 2 := by omega
          obtain ⟨u, v, huv, hHuv⟩ := Finset.card_eq_two.1 hcard
          obtain ⟨i, hi⟩ := hHB u
            (hHuv ▸ Finset.mem_insert_self _ _)
          obtain ⟨j, hj⟩ := hHB v (hHuv ▸ Finset.mem_insert_of_mem
            (Finset.mem_singleton_self v))
          have hi' : g i = u := hi
          have hj' : g j = v := hj
          have hij : i ≠ j := by
            intro h
            rw [h, hj'] at hi'
            exact huv hi'.symm
          rcases Nat.lt_or_ge i j with h' | h'
          · refine hpfc i j h' ⟨n, hnN₀, ?_⟩
            have hpair : ({g i, g j} : Finset ℕ) = H := by
              rw [hi', hj', hHuv]
            rw [show ({b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j)} :
              Finset ℕ) = H from hpair]
            exact hhub
          · have h'' : j < i := by omega
            refine hpfc j i h'' ⟨n, hnN₀, ?_⟩
            have hpair : ({g j, g i} : Finset ℕ) = H := by
              rw [hi', hj', hHuv, Finset.pair_comm]
            rw [show ({b ((f₁ ∘ f₂) j), b ((f₁ ∘ f₂) i)} :
              Finset ℕ) = H from hpair]
            exact hhub
        · have hcard : H.card = 3 := by omega
          obtain ⟨i, j, k, hij, hjk, hset⟩ :=
            sorted_indices_of_card_three hgmono hcard hHB
          refine htfc i j k hij hjk ⟨n, hnN₀, ?_⟩
          rw [show ({b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j),
            b ((f₁ ∘ f₂) k)} : Finset ℕ) = H from hset]
          exact hhub
      · exact hge

theorem clique_targets_dominate {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ → ℕ} {f : ℕ → ℕ}
    (hpf : ∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
      IsRepSupportTransversal A n {b (f i), b (f j)})
    {i j k n : ℕ} (hij : i < j) (hjk : j < k)
    (hn : N₀ ≤ n) (hhub : IsRepSupportTransversal A n {b (f i), b (f j), b (f k)}) :
    b (f k) ≤ n :=
  pair_transversal_target_dominates (hpf i j hij) hn hhub

theorem separated_pair_cofinal_supply {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧
      ∃ (g t : ℕ → ℕ), StrictMono g ∧ (∀ k, g k ∈ A) ∧
        (∀ k, t k < g (k + 1)) ∧
        ∀ k, N₀ ≤ t k ∧ g k ≤ t k ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t k →
            x ∈ insert (g k) P ∨ y ∈ insert (g k) P := by
  classical
  obtain ⟨P, hPfree, g₀, t₀, hg₀mono, hg₀A, hinj, hdata⟩ :=
    injective_pair_cofinal_supply h0 hcov hfail
  set c : ℕ → ℕ → Bool := fun k l =>
    if t₀ k < g₀ l then true else false with hc
  obtain ⟨f, hfmono, bcol, hhom⟩ := infinite_ramsey_pairs c
  rcases Bool.eq_false_or_eq_true bcol with hbc | hbc
  · -- separated
    subst hbc
    refine ⟨P, hPfree, fun k => g₀ (f k), fun k => t₀ (f k),
      fun k l hkl => hg₀mono (hfmono hkl),
      fun k => hg₀A (f k), ?_, fun k => hdata (f k)⟩
    intro k
    have h1 := hhom k (k + 1) (by omega)
    by_cases h : t₀ (f k) < g₀ (f (k + 1))
    · exact h
    · exfalso
      simp [hc, h] at h1
  · -- non-separation is impossible
    exfalso
    subst hbc
    set j := t₀ (f 0) + 1 with hj
    have h1 := hhom 0 j (by omega)
    have h2 : ¬t₀ (f 0) < g₀ (f j) := by
      intro h
      simp [hc, h] at h1
    have h3 : j ≤ f j := hfmono.le_apply
    have h4 : f j ≤ g₀ (f j) := hg₀mono.le_apply
    omega

/-- Sorted-index normalization for a four-element set of values of
a strictly monotone sequence, via the order embedding of `Fin 4`. -/
lemma sorted_indices_of_card_four {e : ℕ → ℕ} (hmono : StrictMono e)
    {H : Finset ℕ} (hcard : H.card = 4)
    (hmem : ∀ h ∈ H, ∃ i, e i = h) :
    ∃ i j k l, i < j ∧ j < k ∧ k < l ∧
      ({e i, e j, e k, e l} : Finset ℕ) = H := by
  classical
  set F := H.orderEmbOfFin hcard with hF
  obtain ⟨i₀, hi₀⟩ := hmem (F 0) (Finset.orderEmbOfFin_mem H hcard 0)
  obtain ⟨i₁, hi₁⟩ := hmem (F 1) (Finset.orderEmbOfFin_mem H hcard 1)
  obtain ⟨i₂, hi₂⟩ := hmem (F 2) (Finset.orderEmbOfFin_mem H hcard 2)
  obtain ⟨i₃, hi₃⟩ := hmem (F 3) (Finset.orderEmbOfFin_mem H hcard 3)
  have hlt01 : F 0 < F 1 := F.strictMono (by decide)
  have hlt12 : F 1 < F 2 := F.strictMono (by decide)
  have hlt23 : F 2 < F 3 := F.strictMono (by decide)
  have h01 : i₀ < i₁ := hmono.lt_iff_lt.1 (by rw [hi₀, hi₁]; exact hlt01)
  have h12 : i₁ < i₂ := hmono.lt_iff_lt.1 (by rw [hi₁, hi₂]; exact hlt12)
  have h23 : i₂ < i₃ := hmono.lt_iff_lt.1 (by rw [hi₂, hi₃]; exact hlt23)
  refine ⟨i₀, i₁, i₂, i₃, h01, h12, h23, ?_⟩
  have hsub : ({e i₀, e i₁, e i₂, e i₃} : Finset ℕ) ⊆ H := by
    intro z hz
    rcases Finset.mem_insert.1 hz with h | h
    · rw [h, hi₀]; exact Finset.orderEmbOfFin_mem H hcard 0
    rcases Finset.mem_insert.1 h with h | h
    · rw [h, hi₁]; exact Finset.orderEmbOfFin_mem H hcard 1
    rcases Finset.mem_insert.1 h with h | h
    · rw [h, hi₂]; exact Finset.orderEmbOfFin_mem H hcard 2
    · rw [Finset.mem_singleton.1 h, hi₃]
      exact Finset.orderEmbOfFin_mem H hcard 3
  have hne : e i₀ ≠ e i₁ ∧ e i₀ ≠ e i₂ ∧ e i₀ ≠ e i₃ ∧
      e i₁ ≠ e i₂ ∧ e i₁ ≠ e i₃ ∧ e i₂ ≠ e i₃ := by
    rw [hi₀, hi₁, hi₂, hi₃]
    have h02 : F 0 < F 2 := lt_trans hlt01 hlt12
    have h03 : F 0 < F 3 := lt_trans h02 hlt23
    have h13 : F 1 < F 3 := lt_trans hlt12 hlt23
    exact ⟨ne_of_lt hlt01, ne_of_lt h02, ne_of_lt h03,
      ne_of_lt hlt12, ne_of_lt h13, ne_of_lt hlt23⟩
  have hcard4 : ({e i₀, e i₁, e i₂, e i₃} : Finset ℕ).card = 4 := by
    obtain ⟨n01, n02, n03, n12, n13, n23⟩ := hne
    rw [Finset.card_insert_of_notMem (by simp [n01, n02, n03]),
      Finset.card_insert_of_notMem (by simp [n12, n13]),
      Finset.card_insert_of_notMem (by simp [n23]),
      Finset.card_singleton]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem pair_transversal_card_escalation_three {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j), b (f k)}) ∨
      (∀ i j k l, i < j → j < k → k < l → ∃ n, N₀ ≤ n ∧
        IsRepSupportTransversal A n {b (f i), b (f j), b (f k), b (f l)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
        5 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  obtain ⟨f₀, hf₀, hout⟩ := pair_transversal_card_escalation_two' h0 hcov
    hanchor hfail b hmono hbA hbpos
  rcases hout with hcl | ⟨hpf, hcl⟩ | ⟨hpf, htf, hteam⟩
  · exact ⟨f₀, hf₀, Or.inl hcl⟩
  · exact ⟨f₀, hf₀, Or.inr (Or.inl hcl)⟩
  · -- doubly free: colour quadruples
    set e : ℕ → ℕ := fun i => b (f₀ i) with he
    have hemono : StrictMono e := fun i j hij => hmono (hf₀ hij)
    set c₄ : ℕ → ℕ → ℕ → ℕ → Bool := fun i j k l =>
      if ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k, e l} then true
      else false with hc₄
    have hc₄iff : ∀ i j k l, c₄ i j k l = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k, e l} := by
      intro i j k l
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n {e i, e j, e k, e l}
      · simp [hc₄, h]
      · simp [hc₄, h]
    obtain ⟨f₄, hf₄, b₄col, hhom₄⟩ := infinite_ramsey_quadruples c₄
    rcases Bool.eq_false_or_eq_true b₄col with hb₄ | hb₄
    · -- quadruple clique
      subst hb₄
      refine ⟨f₀ ∘ f₄, hf₀.comp hf₄, Or.inr (Or.inr (Or.inl ?_))⟩
      intro i j k l hij hjk hkl
      exact (hc₄iff (f₄ i) (f₄ j) (f₄ k) (f₄ l)).1
        (hhom₄ i j k l hij hjk hkl)
    · subst hb₄
      have hqf : ∀ i j k l, i < j → j < k → k < l →
          ¬∃ n, N₀ ≤ n ∧ IsRepSupportTransversal A n
            {e (f₄ i), e (f₄ j), e (f₄ k), e (f₄ l)} := by
        intro i j k l hij hjk hkl hex
        have h1 := (hc₄iff (f₄ i) (f₄ j) (f₄ k) (f₄ l)).2 hex
        rw [hhom₄ i j k l hij hjk hkl] at h1
        exact Bool.false_ne_true h1
      refine ⟨f₀ ∘ f₄, hf₀.comp hf₄, Or.inr (Or.inr (Or.inr ?_))⟩
      set g : ℕ → ℕ := fun i => b ((f₀ ∘ f₄) i) with hgdef
      have hgmono : StrictMono g :=
        fun i j hij => hmono (hf₀ (hf₄ hij))
      have hBA : Set.range g ⊆ A := by
        rintro x ⟨i, rfl⟩
        exact hbA _
      have hBinf : (Set.range g).Infinite :=
        Set.infinite_range_of_injective hgmono.injective
      have h0B : 0 ∉ Set.range g := by
        rintro ⟨i, hi⟩
        have h1 : b ((f₀ ∘ f₄) i) = 0 := hi
        have := hbpos ((f₀ ∘ f₄) i)
        omega
      have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
        hfail hBA hBinf h0B
      intro N
      obtain ⟨n, hn, H, hhub, hminH, hcard2, hHB⟩ :=
        hteams (max N N₀)
      have hnN₀ : N₀ ≤ n := le_trans (le_max_right _ _) hn
      refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hminH,
        ?_, hHB⟩
      rcases Nat.lt_or_ge H.card 5 with hlt | hge
      · exfalso
        rcases Nat.lt_or_ge H.card 3 with hlt2 | hge2
        · have hcard : H.card = 2 := by omega
          obtain ⟨u, v, huv, hHuv⟩ := Finset.card_eq_two.1 hcard
          obtain ⟨i, hi⟩ := hHB u
            (hHuv ▸ Finset.mem_insert_self _ _)
          obtain ⟨j, hj⟩ := hHB v (hHuv ▸ Finset.mem_insert_of_mem
            (Finset.mem_singleton_self v))
          have hi' : g i = u := hi
          have hj' : g j = v := hj
          have hij : i ≠ j := by
            intro h
            rw [h, hj'] at hi'
            exact huv hi'.symm
          rcases Nat.lt_or_ge i j with h' | h'
          · refine hpf (f₄ i) (f₄ j) (hf₄ h') ⟨n, hnN₀, ?_⟩
            have hpair : ({g i, g j} : Finset ℕ) = H := by
              rw [hi', hj', hHuv]
            rw [show ({b (f₀ (f₄ i)), b (f₀ (f₄ j))} :
              Finset ℕ) = H from hpair]
            exact hhub
          · have h'' : j < i := by omega
            refine hpf (f₄ j) (f₄ i) (hf₄ h'') ⟨n, hnN₀, ?_⟩
            have hpair : ({g j, g i} : Finset ℕ) = H := by
              rw [hi', hj', hHuv, Finset.pair_comm]
            rw [show ({b (f₀ (f₄ j)), b (f₀ (f₄ i))} :
              Finset ℕ) = H from hpair]
            exact hhub
        · rcases Nat.lt_or_ge H.card 4 with hlt3 | hge3
          · have hcard : H.card = 3 := by omega
            obtain ⟨i, j, k, hij, hjk, hset⟩ :=
              sorted_indices_of_card_three hgmono hcard hHB
            refine htf (f₄ i) (f₄ j) (f₄ k) (hf₄ hij) (hf₄ hjk)
              ⟨n, hnN₀, ?_⟩
            rw [show ({b (f₀ (f₄ i)), b (f₀ (f₄ j)),
              b (f₀ (f₄ k))} : Finset ℕ) = H from hset]
            exact hhub
          · have hcard : H.card = 4 := by omega
            obtain ⟨i, j, k, l, hij, hjk, hkl, hset⟩ :=
              sorted_indices_of_card_four hgmono hcard hHB
            refine hqf i j k l hij hjk hkl ⟨n, hnN₀, ?_⟩
            rw [show ({e (f₄ i), e (f₄ j), e (f₄ k), e (f₄ l)} :
              Finset ℕ) = H from hset]
            exact hhub
      · exact hge

/-- Domination at arity four: if the triple `{u, v, w}` never support transversals
a late target but `{u, v, w, z}` support transversals `n`, then `z ≤ n`. -/
theorem pair_transversal_target_dominates₄ {A : Set ℕ} {N₀ n u v w z : ℕ}
    (htf : ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {u, v, w})
    (hn : N₀ ≤ n) (hhub : IsRepSupportTransversal A n {u, v, w, z}) :
    z ≤ n := by
  by_contra hgt
  push Not at hgt
  refine htf ⟨n, hn, ?_⟩
  intro x hx y hy z' hz' hsum
  have hmem4 : ∀ q, q ∈ ({u, v, w, z} : Finset ℕ) →
      q = u ∨ q = v ∨ q = w ∨ q = z := by
    intro q hq
    rcases Finset.mem_insert.1 hq with h1 | h1
    · exact Or.inl h1
    rcases Finset.mem_insert.1 h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    rcases Finset.mem_insert.1 h2 with h3 | h3
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_singleton.1 h3)))
  rcases hhub x hx y hy z' hz' hsum with h | h | h
  · rcases hmem4 x h with h1 | h1 | h1 | h1
    · exact Or.inl (by simp [h1])
    · exact Or.inl (by simp [h1])
    · exact Or.inl (by simp [h1])
    · omega
  · rcases hmem4 y h with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inl (by simp [h1]))
    · exact Or.inr (Or.inl (by simp [h1]))
    · exact Or.inr (Or.inl (by simp [h1]))
    · omega
  · rcases hmem4 z' h with h1 | h1 | h1 | h1
    · exact Or.inr (Or.inr (by simp [h1]))
    · exact Or.inr (Or.inr (by simp [h1]))
    · exact Or.inr (Or.inr (by simp [h1]))
    · omega

theorem three_columns_per_clique_target {A : Set ℕ} {N₀ n u v : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {u, v}) (hn : N₀ ≤ n) :
    ∃ x₀ y₀ z₀, ∀ w, IsRepSupportTransversal A n {u, v, w} →
      w = x₀ ∨ w = y₀ ∨ w = z₀ := by
  classical
  have hnohub : ¬IsRepSupportTransversal A n {u, v} := fun h => hpf ⟨n, hn, h⟩
  rw [IsRepSupportTransversal] at hnohub
  push Not at hnohub
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxuv, hyuv, hzuv⟩ := hnohub
  refine ⟨x, y, z, fun w hhub => ?_⟩
  have hmem3 : ∀ q, q ∈ ({u, v, w} : Finset ℕ) →
      q = u ∨ q = v ∨ q = w := by
    intro q hq
    rcases Finset.mem_insert.1 hq with h1 | h1
    · exact Or.inl h1
    rcases Finset.mem_insert.1 h1 with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Finset.mem_singleton.1 h2))
  have hxuv' : x ≠ u ∧ x ≠ v := by
    constructor <;> intro h <;> exact hxuv (by simp [h])
  have hyuv' : y ≠ u ∧ y ≠ v := by
    constructor <;> intro h <;> exact hyuv (by simp [h])
  have hzuv' : z ≠ u ∧ z ≠ v := by
    constructor <;> intro h <;> exact hzuv (by simp [h])
  rcases hhub x hx y hy z hz hsum with h | h | h
  · rcases hmem3 x h with h1 | h1 | h1
    · exact absurd h1 hxuv'.1
    · exact absurd h1 hxuv'.2
    · exact Or.inl h1.symm
  · rcases hmem3 y h with h1 | h1 | h1
    · exact absurd h1 hyuv'.1
    · exact absurd h1 hyuv'.2
    · exact Or.inr (Or.inl h1.symm)
  · rcases hmem3 z h with h1 | h1 | h1
    · exact absurd h1 hzuv'.1
    · exact absurd h1 hzuv'.2
    · exact Or.inr (Or.inr h1.symm)

theorem union_deletion_trichotomy {A B₁ B₂ : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B₁)] [DecidablePred (· ∈ B₂)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : StreamSurvives A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (h1A : B₁ ⊆ A) (h2A : B₂ ⊆ A) (h1inf : B₁.Infinite)
    (h01 : 0 ∉ B₁) (h02 : 0 ∉ B₂) :
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B₁)) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B₂)) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B₁ ∪ B₂) ∧
      (∃ h ∈ H, h ∈ B₁) ∧ ∃ h ∈ H, h ∈ B₂) := by
  classical
  have hUA : B₁ ∪ B₂ ⊆ A := Set.union_subset h1A h2A
  have hUinf : (B₁ ∪ B₂).Infinite := h1inf.mono Set.subset_union_left
  have h0U : 0 ∉ B₁ ∪ B₂ := by
    intro h
    rcases h with h | h
    · exact h01 h
    · exact h02 h
  have hteams := minimalSupportTransversals_from_infiniteDeletion h0 hcov hanchor
    hfail hUA hUinf h0U
  -- Apply the three-way cofinal pigeonhole principle to the transversal-piece profile.
  by_cases hc1 : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B₁
  · exact Or.inl hc1
  by_cases hc2 : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepSupportTransversal A n H ∧ (∀ h ∈ H, ¬IsRepSupportTransversal A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B₂
  · exact Or.inr (Or.inl hc2)
  · refine Or.inr (Or.inr ?_)
    push Not at hc1 hc2
    obtain ⟨N₁, hN₁⟩ := hc1
    obtain ⟨N₂, hN₂⟩ := hc2
    intro N
    obtain ⟨n, hn, H, hhub, hmin, hcard, hHU⟩ :=
      hteams (max N (max N₁ N₂))
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hmin,
      hcard, hHU, ?_, ?_⟩
    · -- some member in B₁: else all in B₂, contradicting hc2
      by_contra hno1
      push Not at hno1
      have hall2 : ∀ h ∈ H, h ∈ B₂ := by
        intro h hh
        rcases hHU h hh with h' | h'
        · exact absurd h' (hno1 h hh)
        · exact h'
      obtain ⟨h, hh, hhB⟩ := hN₂ n (le_trans (le_trans
        (le_max_right _ _) (le_max_right _ _)) hn) H hhub hmin hcard
      exact hhB (hall2 h hh)
    · by_contra hno2
      push Not at hno2
      have hall1 : ∀ h ∈ H, h ∈ B₁ := by
        intro h hh
        rcases hHU h hh with h' | h'
        · exact h'
        · exact absurd h' (hno2 h hh)
      obtain ⟨h, hh, hhB⟩ := hN₁ n (le_trans (le_trans
        (le_max_left _ _) (le_max_right _ _)) hn) H hhub hmin hcard
      exact hhB (hall1 h hh)

theorem three_partners_per_pair_target {A : Set ℕ} {N₀ n u : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepSupportTransversal A m {u}) (hn : N₀ ≤ n) :
    ∃ x₀ y₀ z₀, ∀ w, IsRepSupportTransversal A n {u, w} →
      w = x₀ ∨ w = y₀ ∨ w = z₀ := by
  classical
  have hnohub : ¬IsRepSupportTransversal A n {u} := fun h => hpf ⟨n, hn, h⟩
  rw [IsRepSupportTransversal] at hnohub
  push Not at hnohub
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxu, hyu, hzu⟩ := hnohub
  refine ⟨x, y, z, fun w hhub => ?_⟩
  have hxu' : x ≠ u := fun h => hxu (by simp [h])
  have hyu' : y ≠ u := fun h => hyu (by simp [h])
  have hzu' : z ≠ u := fun h => hzu (by simp [h])
  rcases hhub x hx y hy z hz hsum with h | h | h
  · rcases Finset.mem_insert.1 h with h1 | h1
    · exact absurd h1 hxu'
    · exact Or.inl (Finset.mem_singleton.1 h1).symm
  · rcases Finset.mem_insert.1 h with h1 | h1
    · exact absurd h1 hyu'
    · exact Or.inr (Or.inl (Finset.mem_singleton.1 h1).symm)
  · rcases Finset.mem_insert.1 h with h1 | h1
    · exact absurd h1 hzu'
    · exact Or.inr (Or.inr (Finset.mem_singleton.1 h1).symm)

theorem disjoint_reps_le_support_transversal_card {A : Set ℕ} {n K : ℕ}
    {H : Finset ℕ}
    (hhub : IsRepSupportTransversal A n H) (hdis : HasDisjointTripleReps A n K) :
    K ≤ H.card := by
  classical
  obtain ⟨P, hPA, hPsum, hPdis⟩ := hdis
  have hslot : ∀ i : Fin K, ∃ k : Fin 3, P i k ∈ H := by
    intro i
    rcases hhub (P i 0) (hPA i 0) (P i 1) (hPA i 1) (P i 2)
      (hPA i 2) (hPsum i) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose k hk using hslot
  have hcard := Finset.card_le_card_of_injOn
    (f := fun i : Fin K => P i (k i))
    (s := Finset.univ) (t := H)
    (fun i _ => hk i)
    (by
      intro i hi j hj heq
      by_contra hne
      exact hPdis i j (k i) (k j) hne heq)
  simpa using hcard

/-- `B`-saturation: every order-2 representation of `v` meets `B`.
Failing targets force their entire translate fan into the
saturated set. -/
def Saturated (A B : Set ℕ) (v : ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y = v → x ∈ B ∨ y ∈ B

theorem saturated_mem_add {A B : Set ℕ} {N₀ v : ℕ}
    (hcov : PairCovers A N₀) (hv : N₀ ≤ v)
    (hsat : Saturated A B v) :
    ∃ β ∈ B, ∃ a ∈ A, β + a = v := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov v hv
  rcases hsat x hx y hy hxy with h | h
  · exact ⟨x, h, y, hy, hxy⟩
  · exact ⟨y, h, x, hx, by omega⟩

open Classical in

theorem saturated_count_bound {A B : Set ℕ} {N₀ Y : ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (hcov : PairCovers A N₀) :
    ((Finset.range (Y + 1)).filter
      (fun v => N₀ ≤ v ∧ Saturated A B v)).card ≤
    ((Finset.range (Y + 1)).filter (· ∈ B)).card *
    ((Finset.range (Y + 1)).filter (· ∈ A)).card := by
  classical
  have hchoice : ∀ v : ℕ, ∃ p : ℕ × ℕ,
      (v ∈ (Finset.range (Y + 1)).filter
        (fun v => N₀ ≤ v ∧ Saturated A B v) →
      p.1 ∈ B ∧ p.2 ∈ A ∧ p.1 + p.2 = v) := by
    intro v
    by_cases hv : v ∈ (Finset.range (Y + 1)).filter
      (fun v => N₀ ≤ v ∧ Saturated A B v)
    · obtain ⟨hvr, hvN, hvsat⟩ := Finset.mem_filter.1 hv
      obtain ⟨β, hβ, a, ha, hba⟩ := saturated_mem_add hcov hvN hvsat
      exact ⟨(β, a), fun _ => ⟨hβ, ha, hba⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hv⟩
  choose p hp using hchoice
  have hcard := Finset.card_le_card_of_injOn p
    (t := ((Finset.range (Y + 1)).filter (· ∈ B)) ×ˢ
      ((Finset.range (Y + 1)).filter (· ∈ A)))
    (by
      intro v hv
      obtain ⟨hβ, ha, hba⟩ := hp v hv
      have hvY : v ≤ Y := by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hv).1
        omega
      refine Finset.mem_product.2 ⟨?_, ?_⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hβ⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ha⟩)
    (by
      intro v hv w hw heq
      obtain ⟨-, -, hv2⟩ := hp v (by simpa using hv)
      obtain ⟨-, -, hw2⟩ := hp w (by simpa using hw)
      rw [heq] at hv2
      omega)
  calc ((Finset.range (Y + 1)).filter
      (fun v => N₀ ≤ v ∧ Saturated A B v)).card
      ≤ _ := hcard
    _ = _ := Finset.card_product _ _

theorem failing_fan_saturated {A B : Set ℕ} {m : ℕ}
    (_h0B : 0 ∉ B)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    {z : ℕ} (hz : z ∈ A) (hzB : z ∉ B) (hzm : z ≤ m) :
    Saturated A B (m - z) := by
  intro x hx y hy hxy
  rcases hdead x hx y hy z hz (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hzB

theorem failing_cap_disjoint_deletions {A : Set ℕ} {N₀ m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hm : N₀ ≤ m)
    (B : Fin 4 → Set ℕ)
    (hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ B i → x ∉ B j)
    (hdead : ∀ i, ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x ∈ B i ∨ y ∈ B i ∨ z ∈ B i) :
    False := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov m hm
  -- the parts of one fixed representation
  set part : Fin 3 → ℕ := ![x, y, 0] with hpart
  have hpartA : ∀ s, part s ∈ A := by
    intro s
    fin_cases s
    · exact hx
    · exact hy
    · exact h0
  have hslot : ∀ i : Fin 4, ∃ s : Fin 3, part s ∈ B i := by
    intro i
    rcases hdead i x hx y hy 0 h0 (by omega) with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  choose s hs using hslot
  have hcard : Fintype.card (Fin 3) < Fintype.card (Fin 4) := by
    simp
  obtain ⟨i, j, hij, hsij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt s hcard
  have h1 : part (s i) ∈ B i := hs i
  have h2 : part (s j) ∈ B j := hs j
  rw [hsij] at h1
  exact hdisj j i (fun h => hij h.symm) _ h2 h1

theorem disjoint_deletions_many_failures {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (k : ℕ) (B : Fin k → Set ℕ)
    (hBA : ∀ i, B i ⊆ A) (hBinf : ∀ i, (B i).Infinite)
    (hdisj : ∀ i j, i ≠ j → ∀ x, x ∈ B i → x ∉ B j)
    (N : ℕ) :
    ∃ t : Fin k → ℕ,
      (∀ i, N ≤ t i ∧ N₀ ≤ t i ∧
        ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = t i →
          x ∈ B i ∨ y ∈ B i ∨ z ∈ B i) ∧
      ∀ v, (Finset.univ.filter (fun i : Fin k => t i = v)).card
        ≤ 3 := by
  classical
  have hpick : ∀ i : Fin k, ∃ m, N ≤ m ∧ N₀ ≤ m ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
        x ∈ B i ∨ y ∈ B i ∨ z ∈ B i := by
    intro i
    have hnb := hfail (B i) (hBA i) (hBinf i)
    rw [IsExactTupleAsymptoticBasis] at hnb
    push Not at hnb
    obtain ⟨m, hm, hnorep⟩ := hnb (max N N₀)
    refine ⟨m, le_trans (le_max_left _ _) hm,
      le_trans (le_max_right _ _) hm, ?_⟩
    intro x hx y hy z hz hsum
    by_contra hall
    push Not at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_
      (by simp [Fin.sum_univ_three]; omega)
    intro s
    match s with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  choose t ht1 ht2 ht3 using hpick
  refine ⟨t, fun i => ⟨ht1 i, ht2 i, ht3 i⟩, ?_⟩
  intro v
  by_contra hbig
  push Not at hbig
  obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq
    (show 4 ≤ (Finset.univ.filter
      (fun i : Fin k => t i = v)).card from hbig)
  set g := F.orderEmbOfFin hFcard with hg
  have hgfib : ∀ s : Fin 4, t (g s) = v := by
    intro s
    have h1 : (g s : Fin k) ∈ F := F.orderEmbOfFin_mem hFcard s
    have h2 := hFsub h1
    exact (Finset.mem_filter.1 h2).2
  refine failing_cap_disjoint_deletions h0 hcov (ht2 (g 0))
    (fun s => B (g s)) ?_ ?_
  · intro i j hij x hxi
    refine hdisj (g i) (g j) (fun h => hij (g.injective h)) x hxi
  · intro s
    have h1 := ht3 (g s)
    have h2 : t (g s) = t (g 0) := by
      rw [hgfib s, hgfib 0]
    rw [← h2]
    exact h1

/-- Saturation is monotone in the deletion: sub-deletions of one
mother set share the mother's saturated budget. -/
theorem Saturated.mono {A B B' : Set ℕ} {v : ℕ}
    (hBB' : B ⊆ B') (hsat : Saturated A B v) :
    Saturated A B' v := by
  intro x hx y hy hxy
  rcases hsat x hx y hy hxy with h | h
  · exact Or.inl (hBB' h)
  · exact Or.inr (hBB' h)

theorem immune_survives_sparse {A B : Set ℕ} {v K : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hK : HasDisjointPairReps A v K)
    (hsparse : ((Finset.range (v + 1)).filter (· ∈ B)).card < K) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = v ∧
      x ∉ B ∧ y ∉ B ∧ z ∉ B := by
  classical
  obtain ⟨P, hPA, hPsum, hPdis⟩ := hK
  -- pairs impossible by B inject into the deleted window
  by_contra hall
  push Not at hall
  have hkill : ∀ i : Fin K, ∃ s : Fin 2, P i s ∈ B := by
    intro i
    by_contra hno
    push Not at hno
    have h0' : P i 0 ∉ B := hno 0
    have h1' : P i 1 ∉ B := hno 1
    have hmem := hall (P i 0) (hPA i 0) (P i 1) (hPA i 1) 0 h0
      (by have := hPsum i; omega) h0' h1'
    exact h0B hmem
  choose s hs using hkill
  have hcard := Finset.card_le_card_of_injOn
    (f := fun i : Fin K => P i (s i))
    (s := Finset.univ)
    (t := (Finset.range (v + 1)).filter (· ∈ B))
    (by
      intro i _
      show P i (s i) ∈ (Finset.range (v + 1)).filter (· ∈ B)
      have h1 : P i (s i) ≤ v := by
        have hb : ∀ k : Fin 2, P i k ≤ v := by
          rw [Fin.forall_fin_two]
          constructor <;> (have := hPsum i; omega)
        exact hb (s i)
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega),
        hs i⟩)
    (by
      intro i _ j _ heq
      by_contra hne
      exact hPdis i j (s i) (s j) hne heq)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- Greedy extraction with an avoid-set: from `4K` unblocked pair
components, `K` pairwise-disjoint pairs avoiding the blocked set. -/
theorem disjoint_pairs_extract {A : Set ℕ} {v : ℕ}
    [DecidablePred (· ∈ A)] :
    ∀ (K : ℕ) (U : Finset ℕ),
    4 * K ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x ∉ U ∧ (v - x) ∉ U)).card →
    ∃ P : Fin K → Fin 2 → ℕ,
      (∀ i k, P i k ∈ A) ∧ (∀ i, P i 0 + P i 1 = v) ∧
      (∀ i j k l, i ≠ j → P i k ≠ P j l) ∧
      (∀ i k, P i k ∉ U) := by
  classical
  intro K
  induction K with
  | zero =>
    intro U _
    refine ⟨fun i => absurd i.2 (by omega), ?_, ?_, ?_, ?_⟩ <;>
      · intro i
        exact absurd i.2 (by omega)
  | succ K ih =>
    intro U hcard
    set F := (Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x ∉ U ∧ (v - x) ∉ U) with hFd
    have hFne : F.Nonempty := by
      rw [← Finset.card_pos]
      omega
    obtain ⟨x₀, hx₀⟩ := hFne
    obtain ⟨hx₀r, hx₀A, hx₀A', hx₀U, hx₀U'⟩ := Finset.mem_filter.1 hx₀
    have hx₀v : x₀ ≤ v := by
      have := Finset.mem_range.1 hx₀r
      omega
    set U' := insert x₀ (insert (v - x₀) U) with hU'
    have hstep : 4 * K ≤ ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x ∉ U' ∧
          (v - x) ∉ U')).card := by
      have hsub : F \ ({x₀, v - x₀} ∪
          ({x₀, v - x₀} : Finset ℕ).image (fun b => v - b)) ⊆
          (Finset.range (v + 1)).filter
            (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x ∉ U' ∧
              (v - x) ∉ U') := by
        intro x hx
        obtain ⟨hxF, hxbl⟩ := Finset.mem_sdiff.1 hx
        obtain ⟨hxr, hxA, hxA', hxU, hxU'⟩ := Finset.mem_filter.1 hxF
        have hxv : x ≤ v := by
          have := Finset.mem_range.1 hxr
          omega
        rw [Finset.mem_union] at hxbl
        push Not at hxbl
        obtain ⟨hxb1, hxb2⟩ := hxbl
        have hxx₀ : x ≠ x₀ ∧ x ≠ v - x₀ := by
          constructor <;> intro h <;>
            exact hxb1 (by simp [h])
        have hvxx₀ : v - x ≠ x₀ ∧ v - x ≠ v - x₀ := by
          constructor <;> intro h
          · exact hxb2 (Finset.mem_image.2
              ⟨v - x₀, by simp, by omega⟩)
          · exact hxb2 (Finset.mem_image.2
              ⟨x₀, by simp, by omega⟩)
        refine Finset.mem_filter.2 ⟨hxr, hxA, hxA', ?_, ?_⟩
        · rw [hU']
          intro hmem
          rcases Finset.mem_insert.1 hmem with h | h
          · exact hxx₀.1 h
          rcases Finset.mem_insert.1 h with h | h
          · exact hxx₀.2 h
          · exact hxU h
        · rw [hU']
          intro hmem
          rcases Finset.mem_insert.1 hmem with h | h
          · exact hvxx₀.1 h
          rcases Finset.mem_insert.1 h with h | h
          · exact hvxx₀.2 h
          · exact hxU' h
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.le_card_sdiff ({x₀, v - x₀} ∪
        ({x₀, v - x₀} : Finset ℕ).image (fun b => v - b)) F
      have h3 : (({x₀, v - x₀} : Finset ℕ) ∪
          ({x₀, v - x₀} : Finset ℕ).image (fun b => v - b)).card
          ≤ 4 := by
        have hb1 : ({x₀, v - x₀} : Finset ℕ).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        have hb2 := Finset.card_image_le
          (s := ({x₀, v - x₀} : Finset ℕ)) (f := fun b => v - b)
        have := Finset.card_union_le ({x₀, v - x₀} : Finset ℕ)
          (({x₀, v - x₀} : Finset ℕ).image (fun b => v - b))
        omega
      omega
    obtain ⟨P', hP'A, hP'sum, hP'dis, hP'U⟩ := ih U' hstep
    set newpair : Fin 2 → ℕ := ![x₀, v - x₀] with hnp
    have hnpmem : ∀ k : Fin 2, newpair k = x₀ ∨
        newpair k = v - x₀ := by
      intro k
      fin_cases k
      · exact Or.inl rfl
      · exact Or.inr rfl
    set P : Fin (K + 1) → Fin 2 → ℕ :=
      Fin.cases newpair (fun j => P' j) with hP
    have hPzero : P 0 = newpair := rfl
    have hPsucc : ∀ j : Fin K, P j.succ = P' j := fun j => rfl
    refine ⟨P, ?_, ?_, ?_, ?_⟩
    · intro i k
      refine Fin.cases ?_ ?_ i
      · rw [hPzero]
        fin_cases k
        · exact hx₀A
        · exact hx₀A'
      · intro j
        rw [hPsucc]
        exact hP'A j k
    · intro i
      refine Fin.cases ?_ ?_ i
      · rw [hPzero]
        show x₀ + (v - x₀) = v
        omega
      · intro j
        rw [hPsucc]
        exact hP'sum j
    · have hkey : ∀ i j k l, P i k = P j l → i = j := by
        intro i j k l
        refine Fin.cases ?_ ?_ i <;> [skip; intro i'] <;>
          refine Fin.cases ?_ ?_ j <;> [skip; intro j'; skip;
            intro j']
        · intro _
          rfl
        · rw [hPzero, hPsucc]
          intro heq
          exfalso
          have hin : P' j' l ∈ U' := by
            rcases hnpmem k with h | h
            · rw [hU', ← heq, h]
              exact Finset.mem_insert_self _ _
            · rw [hU', ← heq, h]
              exact Finset.mem_insert_of_mem
                (Finset.mem_insert_self _ _)
          exact hP'U j' l hin
        · rw [hPsucc, hPzero]
          intro heq
          exfalso
          have hin : P' i' k ∈ U' := by
            rcases hnpmem l with h | h
            · rw [hU', heq, h]
              exact Finset.mem_insert_self _ _
            · rw [hU', heq, h]
              exact Finset.mem_insert_of_mem
                (Finset.mem_insert_self _ _)
          exact hP'U i' k hin
        · rw [hPsucc, hPsucc]
          intro heq
          by_contra hne
          exact hP'dis i' j' k l
            (fun h => hne (congrArg Fin.succ h)) heq
      exact fun i j k l hij heq => hij (hkey i j k l heq)
    · intro i k
      refine Fin.cases ?_ ?_ i
      · rw [hPzero]
        rcases hnpmem k with h | h
        · rw [h]
          exact hx₀U
        · rw [h]
          exact hx₀U'
      · intro j
        rw [hPsucc]
        intro hmem
        refine hP'U j k ?_
        rw [hU']
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)

theorem disjoint_pairs_of_r2 {A : Set ℕ} {v K : ℕ}
    [DecidablePred (· ∈ A)]
    (hcount : 4 * K ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :
    HasDisjointPairReps A v K := by
  classical
  have hsub : (Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A) ⊆
      (Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A ∧ x ∉ (∅ : Finset ℕ) ∧
          (v - x) ∉ (∅ : Finset ℕ)) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨h1, h2, h3,
      Finset.notMem_empty _, Finset.notMem_empty _⟩
  obtain ⟨P, h1, h2, h3, -⟩ := disjoint_pairs_extract K ∅
    (le_trans hcount (Finset.card_le_card hsub))
  exact ⟨P, h1, h2, h3⟩

theorem witness_translate_immune {A B : Set ℕ} {N₀ t : ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (ht : N₀ ≤ t)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = t →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) :
    ∃ β, β ∈ B ∧ β ≤ t ∧ ∀ K : ℕ,
      4 * K ≤ ((Finset.range (t - N₀ + 1)).filter
          (fun w => w ∈ A ∧ w ∉ B)).card /
        ((Finset.range (t + 1)).filter (· ∈ B)).card →
      HasDisjointPairReps A (t - β) K := by
  classical
  set H := (Finset.range (t + 1)).filter (· ∈ B) with hH
  have hhub : IsRepSupportTransversal A t H := failing_support_transversal_subset_deletion hdead
  have hHne : H.Nonempty := support_transversal_nonempty_of_covering h0 hcov ht hhub
  obtain ⟨β, hβH, hblow⟩ := support_transversal_fan_amplification hcov hhub hHne ht
  obtain ⟨hβr, hβB⟩ := Finset.mem_filter.1 hβH
  have hβt : β ≤ t := by
    have := Finset.mem_range.1 hβr
    omega
  refine ⟨β, hβB, hβt, fun K hK => ?_⟩
  -- identify the two fan filters: ∉ H equals ∉ B below the window
  have hfans : ((Finset.range (t - N₀ + 1)).filter
      (fun w => w ∈ A ∧ w ∉ B)).card ≤
      ((Finset.range (t - N₀ + 1)).filter
        (fun w => w ∈ A ∧ w ∉ H)).card := by
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwr, hwA, hwB⟩ := Finset.mem_filter.1 hw
    refine Finset.mem_filter.2 ⟨hwr, hwA, ?_⟩
    intro hwH
    exact hwB (Finset.mem_filter.1 hwH).2
  have hquot : ((Finset.range (t - N₀ + 1)).filter
      (fun w => w ∈ A ∧ w ∉ B)).card / H.card ≤
      ((Finset.range (t - N₀ + 1)).filter
        (fun w => w ∈ A ∧ w ∉ H)).card / H.card :=
    Nat.div_le_div_right hfans
  have hr2 : 4 * K ≤ ((Finset.range (t - β + 1)).filter
      (fun x => x ∈ A ∧ (t - β - x) ∈ A)).card := by
    calc 4 * K
        ≤ ((Finset.range (t - N₀ + 1)).filter
            (fun w => w ∈ A ∧ w ∉ B)).card / H.card := hK
      _ ≤ ((Finset.range (t - N₀ + 1)).filter
            (fun w => w ∈ A ∧ w ∉ H)).card / H.card := hquot
      _ ≤ _ := hblow
  exact disjoint_pairs_of_r2 hr2

/-- Total pair-count double-count: summing the order-2 counts over
a window is bounded by the square of the element count. -/
theorem sum_pair_counts_le_sq {A : Set ℕ} {Y : ℕ}
    [DecidablePred (· ∈ A)] :
    ∑ v ∈ Finset.range (Y + 1),
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card ≤
    ((Finset.range (Y + 1)).filter (· ∈ A)).card *
    ((Finset.range (Y + 1)).filter (· ∈ A)).card := by
  classical
  set W := (Finset.range (Y + 1)).filter (· ∈ A) with hW
  set T := (Finset.range (Y + 1)).biUnion (fun v =>
    ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).image (fun x => (v, x)))
    with hT
  have hTcard : T.card = ∑ v ∈ Finset.range (Y + 1),
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card := by
    rw [hT, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.card_image_of_injective]
      intro x x' hxx'
      exact congrArg Prod.snd hxx'
    · intro v _ v' _ hvv'
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp hp'
      obtain ⟨x, -, hxp⟩ := Finset.mem_image.1 hp
      obtain ⟨x', -, hxp'⟩ := Finset.mem_image.1 hp'
      have h1 : v = p.1 := by rw [← hxp]
      have h2 : v' = p.1 := by rw [← hxp']
      exact hvv' (by omega)
  have hinj := Finset.card_le_card_of_injOn
    (f := fun p : ℕ × ℕ => (p.2, p.1 - p.2))
    (s := T) (t := W ×ˢ W)
    (by
      intro p hp
      obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hpv
      obtain ⟨hxr, hxA, hvxA⟩ := Finset.mem_filter.1 hx
      have hvY : v ≤ Y := by
        have := Finset.mem_range.1 hv
        omega
      have hxv : x ≤ v := by
        have := Finset.mem_range.1 hxr
        omega
      have hval : (fun p : ℕ × ℕ => (p.2, p.1 - p.2)) p =
          (x, v - x) := by
        rw [← hxp]
      rw [hval]
      refine Finset.mem_product.2 ⟨?_, ?_⟩
      · exact Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hxA⟩
      · exact Finset.mem_filter.2
          ⟨Finset.mem_range.2 (by omega), hvxA⟩)
    (by
      intro p hp p' hp' heq
      have hpT : p ∈ T := by simpa using hp
      have hpT' : p' ∈ T := by simpa using hp'
      rw [hT] at hpT hpT'
      obtain ⟨v, hv, hpv⟩ := Finset.mem_biUnion.1 hpT
      obtain ⟨x, hx, hxp⟩ := Finset.mem_image.1 hpv
      obtain ⟨v', hv', hpv'⟩ := Finset.mem_biUnion.1 hpT'
      obtain ⟨x', hx', hxp'⟩ := Finset.mem_image.1 hpv'
      have hxv : x ≤ v := by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hx).1
        omega
      have hxv' : x' ≤ v' := by
        have := Finset.mem_range.1 (Finset.mem_filter.1 hx').1
        omega
      have hval : (fun p : ℕ × ℕ => (p.2, p.1 - p.2)) p =
          (x, v - x) := by
        rw [← hxp]
      have hval' : (fun p : ℕ × ℕ => (p.2, p.1 - p.2)) p' =
          (x', v' - x') := by
        rw [← hxp']
      rw [hval, hval'] at heq
      have h1 : x = x' := congrArg Prod.fst heq
      have h2 : v - x = v' - x' := congrArg Prod.snd heq
      have h3 : v = v' := by omega
      rw [← hxp, ← hxp', h1, h3])
  rw [hTcard] at hinj
  calc ∑ v ∈ Finset.range (Y + 1), _ = _ := rfl
    _ ≤ (W ×ˢ W).card := hinj
    _ = W.card * W.card := Finset.card_product _ _

theorem blown_count_bound {A : Set ℕ} {Y K : ℕ}
    [DecidablePred (· ∈ A)] :
    K * ((Finset.range (Y + 1)).filter (fun v =>
      K ≤ ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card)).card ≤
    ((Finset.range (Y + 1)).filter (· ∈ A)).card *
    ((Finset.range (Y + 1)).filter (· ∈ A)).card := by
  classical
  set Blown := (Finset.range (Y + 1)).filter (fun v =>
    K ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) with hBl
  have h1 : K * Blown.card ≤ ∑ v ∈ Blown,
      ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card := by
    have := Finset.card_nsmul_le_sum Blown
      (fun v => ((Finset.range (v + 1)).filter
        (fun x => x ∈ A ∧ (v - x) ∈ A)).card) K
      (fun v hv => (Finset.mem_filter.1 hv).2)
    simpa [Nat.mul_comm] using this
  have h2 : ∑ v ∈ Blown, ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card ≤
      ∑ v ∈ Finset.range (Y + 1),
        ((Finset.range (v + 1)).filter
          (fun x => x ∈ A ∧ (v - x) ∈ A)).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 := sum_pair_counts_le_sq (A := A) (Y := Y)
  omega

end Erdos881
