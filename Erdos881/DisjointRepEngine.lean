/-
# Engine V10: the disjoint-representation engine

A new surviving-deletion engine with a hypothesis interface unlike the
family/identity engines V2–V9: *representation multiplicity growth*.

If for every `K` all sufficiently large `n` admit `K` pairwise-disjoint
3-representations (no shared part values between distinct
representations), then a sufficiently slowly-growing infinite deletion
`B ⊆ A` survives: any target `n` sees at most `K` members of `B` below
it while owning `K + 1` disjoint representations, and hitting all of
them would embed `K + 1` representations injectively into `K` markers —
pigeonhole.

Contrapositive interface for the counterexample: some fixed `K` bounds
the pairwise-disjoint 3-representation count on a cofinal set of
targets — a tangible additive-combinatorics rigidity the lab census
finds nowhere (every covering structure tested has unbounded
disjoint-rep growth; size-≤2 rep covers simply do not exist).
-/

import Erdos881.TeamGraphRamsey
import Erdos881.AdditiveSupports
import Erdos881.RotatingGuardianEndgame
import Erdos881.FunnelTrichotomy

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

/-- **Engine V10.**  Unbounded pairwise-disjoint representation growth
yields a surviving deletion: an infinite `B ⊆ A` with every late
target 3-represented away from `B`. -/
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
    push_neg at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, P i k = b j := by
      intro i
      have h0 := hPA i 0
      have h1 := hPA i 1
      have h2 := hPA i 2
      have hs := hPsum i
      by_contra hnone
      push_neg at hnone
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

/-- A hub set for `n`: a finite set of values meeting every exact
3-representation of `n` over `A`. -/
def IsRepHub (A : Set ℕ) (n : ℕ) (H : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
    x ∈ H ∨ y ∈ H ∨ z ∈ H

/-- **Hub extraction.**  A target without `K` pairwise-disjoint
3-representations has a hub set of at most `3·(K-1)` values: the parts
of a maximal disjoint family meet every representation.  Together with
Engine V10 this reduces a counterexample's order-3 failure to
*cofinal bounded-hub targets* — the constant-size generalization of
the fixed-pair configuration. -/
theorem hub_of_no_disjointReps {A : Set ℕ} {n K : ℕ}
    (hno : ¬HasDisjointTripleReps A n K) :
    ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧ IsRepHub A n H := by
  classical
  have h0 : HasDisjointTripleReps A n 0 :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  -- boundary crossing: a maximal achievable family size J < K
  have hcross : ∃ J, J < K ∧ HasDisjointTripleReps A n J ∧
      ¬HasDisjointTripleReps A n (J + 1) := by
    by_contra hnc
    push_neg at hnc
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
    push_neg at hnot
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

/-- **The hub reduction.**  A counterexample's order-3 failure against
every infinite deletion forces cofinal targets carrying constant-size
representation hubs: some fixed `K` bounds a hub for infinitely many
targets.  This is the fixed-pair configuration generalized to fixed
finite hub size, derived from first principles (Engine V10 +
hub extraction) — the entry point for team-machinery escalation. -/
theorem cofinal_bounded_hubs_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧ IsRepHub A n H := by
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
  push_neg at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := hub_of_no_disjointReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

/-- **Hub dichotomy** (tower extraction, step one).  Given cofinal
bounded-card hub targets and any window `[0, W]`: either some fixed
element `h ≤ W` belongs to hubs cofinally (a persistent guardian), or
hubs avoiding `[0, W]` entirely occur cofinally (level-like hubs).
Iterating consumes the small part of the hubs element by element. -/
theorem hub_dichotomy {A : Set ℕ} {C : ℕ}
    (hhub : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H)
    (W : ℕ) :
    (∃ h, h ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepHub A n H ∧ h ∈ H) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
      ∀ h ∈ H, W < h) := by
  classical
  by_cases hmeet : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepHub A n H ∧ ∃ h ∈ H, h ≤ W
  · left
    by_contra hnoper
    push_neg at hnoper
    have hex : ∀ h, ∃ Nh, h ≤ W → ∀ n, Nh ≤ n →
        ∀ H : Finset ℕ, H.card ≤ C → IsRepHub A n H → h ∉ H := by
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
    push_neg at hmeet
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
    push_neg at hnoper
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
    push_neg at hmeet
    obtain ⟨N₀, hN₀⟩ := hmeet
    intro N
    obtain ⟨n, hn, H, hQH⟩ := hQ (max N N₀)
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hQH, ?_⟩
    intro h hh
    have := hN₀ n (le_trans (le_max_right _ _) hn) H hQH h hh
    omega

/-- Tower extraction, budget induction: from a cofinal family of hubs
containing a core `S` with excess budget `d`, produce an enlarged core
`S'` splitting the hubs at the window: everything outside `S'` is
large. -/
theorem hub_window_split_aux {A : Set ℕ} {C : ℕ} (W : ℕ) :
    ∀ d S, S ⊆ Finset.range (W + 1) →
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
      S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S' ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
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
      (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
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
    · -- reduced hubs cofinally avoid the window: done with core S
      refine ⟨S, hSW, fun N => ?_⟩
      obtain ⟨n, hn, H', ⟨H, hcard, hhub, hSH, hbud, hH'⟩, hlargeH⟩ :=
        hlarge N
      subst hH'
      refine ⟨n, hn, H, hcard, hhub, hSH, fun h hhH hhS => ?_⟩
      exact hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)

/-- **The hub tower.**  Cofinal bounded hubs split at every window: a
fixed core `S ⊆ [0, W]` persists while everything else escapes above
`W`, cofinally.  Combined with `cofinal_bounded_hubs_of_hfail`, a
counterexample's targets concentrate on a fixed small guardian core
plus level-scale rotating guards — the team configuration, now derived
from raw `hfail`. -/
theorem hub_window_split {A : Set ℕ} {C : ℕ}
    (hhub : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
      IsRepHub A n H) (W : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  refine hub_window_split_aux W C ∅ (by simp) fun N => ?_
  obtain ⟨n, hn, H, hcard, hhub'⟩ := hhub N
  exact ⟨n, hn, H, hcard, hhub', Finset.empty_subset _, by simpa using hcard⟩

/-- With `0 ∈ A` and covering, late targets always have 3-reps, so
hubs are nonempty. -/
theorem hub_nonempty_of_covering {A : Set ℕ} {N₀ n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepHub A n H) : H.Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact ⟨x, h⟩
  · exact ⟨y, h⟩
  · exact ⟨0, h⟩

/-- A singleton hub is exactly a private triple. -/
theorem privateTriple_of_singleton_hub {A : Set ℕ} {N₀ n a : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepHub A n {a}) : IsPrivateTriple A a n := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov n hn
  refine ⟨⟨x, hx, y, hy, 0, h0, by omega⟩, ?_⟩
  intro x' hx' y' hy' z' hz' hsum
  rcases hhub x' hx' y' hy' z' hz' hsum with h | h | h
  · exact Or.inl (Finset.mem_singleton.1 h)
  · exact Or.inr (Or.inl (Finset.mem_singleton.1 h))
  · exact Or.inr (Or.inr (Finset.mem_singleton.1 h))

/-- **Positive singleton hubs are refuted**: cofinal positive
singleton-hub targets feed the verified private-stream kill, whose
surviving deletion contradicts `hfail`.  The hub tower's core cannot
collapse to a single positive guardian. -/
theorem singleton_hubs_refuted {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ¬(∀ N, ∃ n, N ≤ n ∧ ∃ a, 0 < a ∧ IsRepHub A n {a}) := by
  intro hsing
  have hstream : ∀ N, ∃ a m, N ≤ m ∧ 0 < a ∧ IsPrivateTriple A a m := by
    intro N
    obtain ⟨n, hn, a, ha, hhub⟩ := hsing (max N N₀)
    exact ⟨a, n, le_trans (le_max_left _ _) hn, ha,
      privateTriple_of_singleton_hub h0 hcov
        (le_trans (le_max_right _ _) hn) hhub⟩
  obtain ⟨B, hBsub, hBinf, hsurv⟩ :=
    surviving_deletion_of_cofinal_privateStream h0 hcov hstream hanchor
  refine hfail B hBsub hBinf ⟨N₀, fun n hn => ?_⟩
  obtain ⟨x, hx, y, hy, z, hz, hxB, hyB, hzB, hsum⟩ := hsurv n hn
  refine ⟨![x, y, z], ?_, ?_⟩
  · intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  · simpa [Fin.sum_univ_three] using hsum

/-- **The team configuration from first principles.**  A
counterexample (covering + order-3 failure against every infinite
deletion) has a fixed hub bound `K` such that at EVERY window `[0, W]`
some fixed core `S ⊆ [0, W]` persists in the hubs of cofinally many
targets while all remaining hub elements exceed `W`.  Nonemptiness and
the singleton refutation then leave: |core ∪ large-part| ≥ 2 with
either a fixed multi-element guardian core (team territory) or
level-scale rotating guards (corep territory). -/
theorem team_configuration_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧
        IsRepHub A n H ∧ S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  obtain ⟨K, hK⟩ := cofinal_bounded_hubs_of_hfail hcov hfail
  refine ⟨K, fun W => ?_⟩
  exact hub_window_split (fun N => hK N) W

/-- **The pair is the true base case.**  Under the counterexample
interfaces (covering, doubling supply, anchor supply, order-3 failure
for every infinite deletion), all sufficiently late representation
hubs have at least two elements: empty hubs die by covering,
zero-singletons by the zero-residue kill, positive singletons by the
private-stream kill. -/
theorem hub_card_ge_two_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ N, ∀ n, N ≤ n → ∀ H : Finset ℕ, IsRepHub A n H → 2 ≤ H.card := by
  classical
  have hzero := not_zero_residue_of_doubling hcov hdb
  push_neg at hzero
  obtain ⟨Nz, hNz⟩ := hzero
  have hpos := singleton_hubs_refuted h0 hcov hanchor hfail
  push_neg at hpos
  obtain ⟨Np, hNp⟩ := hpos
  refine ⟨max N₀ (max Nz Np), fun n hn H hhub => ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hnz : Nz ≤ n := le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) hn
  have hnp : Np ≤ n := le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hn
  by_contra hlt
  push_neg at hlt
  interval_cases hc : H.card
  · obtain ⟨x, hx⟩ := hub_nonempty_of_covering h0 hcov hn₀ hhub
    have := Finset.card_pos.2 ⟨x, hx⟩
    omega
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hc
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · subst ha0
      exact hNz n hnz (privateTriple_of_singleton_hub h0 hcov hn₀ hhub)
    · exact hNp n hnp a hapos hhub

/-- An exact-pair hub is a pair destroyer. -/
theorem pairDestroyer_of_pair_hub {A : Set ℕ} {N₀ n u v : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀) (hn : N₀ ≤ n)
    (hhub : IsRepHub A n {u, v}) : IsPairDestroyer A u v n := by
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

/-- Every hub contains a minimal hub. -/
theorem exists_minimal_hub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsRepHub A n H) :
    ∃ H' ⊆ H, IsRepHub A n H' ∧
      ∀ h ∈ H', ¬IsRepHub A n (H' \ {h}) := by
  classical
  revert hhub
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro hhub
    by_cases hmin : ∀ h ∈ H, ¬IsRepHub A n (H \ {h})
    · exact ⟨H, Finset.Subset.refl H, hhub, hmin⟩
    · push_neg at hmin
      obtain ⟨h, hhH, hsub⟩ := hmin
      have hss : H \ {h} ⊂ H :=
        Finset.sdiff_ssubset (Finset.singleton_subset_iff.2 hhH)
          (Finset.singleton_nonempty h)
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := ih (H \ {h}) hss hsub
      exact ⟨H', Finset.Subset.trans hH'sub Finset.sdiff_subset,
        hH'hub, hH'min⟩

/-- **Necessity witnesses.**  Every element of a minimal hub owns a
representation meeting the hub only at that element: each hub member
is a genuine guardian with a private witness. -/
theorem minimal_hub_necessity {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsRepHub A n H)
    (hmin : ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) :
    ∀ h ∈ H, ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n ∧
      (x = h ∨ y = h ∨ z = h) ∧
      (∀ g ∈ H, g ≠ h → x ≠ g ∧ y ≠ g ∧ z ≠ g) := by
  intro h hhH
  have hnot := hmin h hhH
  rw [IsRepHub] at hnot
  push_neg at hnot
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

/-- **Exact-pair recurrence.**  Cofinal pair hubs inside a fixed
window recur: some single pair carries hubs cofinally (pigeonhole
over the finitely many pairs). -/
theorem recurring_pair_of_bounded_pair_hubs {A : Set ℕ} {W : ℕ}
    (hpairs : ∀ N, ∃ n, N ≤ n ∧ ∃ u v, u ≤ W ∧ v ≤ W ∧
      IsRepHub A n {u, v}) :
    ∃ u v, u ≤ W ∧ v ≤ W ∧ ∀ N, ∃ n, N ≤ n ∧ IsRepHub A n {u, v} := by
  classical
  by_contra hno
  push_neg at hno
  have hex : ∀ u v, ∃ Nuv, u ≤ W → v ≤ W → ∀ n, Nuv ≤ n →
      ¬IsRepHub A n {u, v} := by
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

/-- **Pipeline entry.**  Cofinal windowed pair hubs hand the
fixed-pair pipeline its recurring destroyer pair. -/
theorem pipeline_entry_of_bounded_pair_hubs {A : Set ℕ} {N₀ W : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpairs : ∀ N, ∃ n, N ≤ n ∧ ∃ u v, u ≤ W ∧ v ≤ W ∧
      IsRepHub A n {u, v}) :
    ∃ u v, ∀ N, ∃ n, N ≤ n ∧ IsPairDestroyer A u v n := by
  obtain ⟨u, v, _, _, hrec⟩ := recurring_pair_of_bounded_pair_hubs hpairs
  refine ⟨u, v, fun N => ?_⟩
  obtain ⟨n, hn, hhub⟩ := hrec (max N N₀)
  exact ⟨n, le_trans (le_max_left _ _) hn,
    pairDestroyer_of_pair_hub h0 hcov (le_trans (le_max_right _ _) hn) hhub⟩

/-- Side-predicate tower: the window split carries any extra property
`R` of the hub family through unchanged. -/
theorem hub_window_split_aux' {A : Set ℕ} {C : ℕ}
    (R : ℕ → Finset ℕ → Prop) (W : ℕ) :
    ∀ d S, S ⊆ Finset.range (W + 1) →
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
      R n H ∧ S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S' ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
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
      (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
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

/-- **The minimal team configuration.**  From covering + hfail: a
fixed hub bound and, at every window, a persistent core `S` inside
MINIMAL hubs whose remaining elements all exceed the window — and
every element of such a hub owns a private witness
(`minimal_hub_necessity`).  The strongest launching interface for the
guardian-team escalation. -/
theorem team_configuration_minimal_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∀ W, ∃ S : Finset ℕ, S ⊆ Finset.range (W + 1) ∧
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ 3 * (K - 1) ∧
        IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_hubs_of_hfail hcov hfail
  refine ⟨K, fun W => ?_⟩
  refine hub_window_split_aux'
    (R := fun n H => ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) W
    (3 * (K - 1)) ∅ (by simp) fun N => ?_
  obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
  exact ⟨n, hn, H', le_trans (Finset.card_le_card hH'sub) hcard,
    hH'hub, hH'min, Finset.empty_subset _,
    by simpa using le_trans (Finset.card_le_card hH'sub) hcard⟩

/-- Stable-core descent: either the current core already splits at
every window, or some window forces the core to grow — and growth is
budget-bounded. -/
theorem stable_core_aux {A : Set ℕ} {C : ℕ}
    (R : ℕ → Finset ℕ → Prop) :
    ∀ d S,
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
      R n H ∧ S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S ⊆ S' ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        IsRepHub A n H ∧ R n H ∧ S' ⊆ H ∧
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
        H.card ≤ C ∧ IsRepHub A n H ∧ R n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h
    · exact ⟨S, Finset.Subset.refl S, hstable⟩
    · push_neg at hstable
      obtain ⟨W₁, N₁, hW₁⟩ := hstable
      rcases cofinal_dichotomy
        (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ IsRepHub A n H ∧
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
      · -- but the right branch contradicts the failing window
        exfalso
        obtain ⟨n, hn, H', ⟨H, hcard, hhub, hR, hSH, hbud, hH'⟩, hlargeH⟩ :=
          hlarge N₁
        subst hH'
        obtain ⟨h, hhH, hhS, hhW⟩ := hW₁ n hn H hcard hhub hR hSH
        have := hlargeH h (Finset.mem_sdiff.2 ⟨hhH, hhS⟩)
        omega

/-- **THE STABLE CORE.**  A counterexample has one fixed guardian set
`S*` such that at EVERY window, cofinally many targets carry minimal
hubs consisting of `S*` plus elements above the window.  The enemy's
entire order-3 failure concentrates, at all scales simultaneously, on
a single finite team of guardians and their level-scale escorts. -/
theorem stable_core_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_hubs_of_hfail hcov hfail
  obtain ⟨S, -, hsplit⟩ := stable_core_aux
    (A := A) (C := 3 * (K - 1))
    (R := fun n H => ∀ h ∈ H, ¬IsRepHub A n (H \ {h}))
    (3 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
      exact ⟨n, hn, H', le_trans (Finset.card_le_card hH'sub) hcard,
        hH'hub, hH'min, Finset.empty_subset _,
        by simpa using le_trans (Finset.card_le_card hH'sub) hcard⟩)
  exact ⟨K, S, hsplit⟩

/-- **The order-2 shadow.**  A hub avoiding `0` confines the target's
2-representations as well: `(x, y, 0)` is a 3-representation, and with
`0 ∉ H` the hit must land on `x` or `y`.  All-large hubs therefore
force order-2 destroyer structure at level scale — the pair-funnel
stream, with the verified counting vise waiting. -/
theorem two_rep_shadow_of_large_hub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hhub : IsRepHub A n H) (hlarge : ∀ h ∈ H, 0 < h) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (hlarge 0 h) (by omega)

/-- The stable core's empty case, packaged: if the stable core is
empty then at every window cofinally many targets have BOTH their
3-reps and their 2-reps confined to a bounded set of elements above
the window — rotating level-scale destroyer teams. -/
theorem large_team_shadow_of_empty_core {A : Set ℕ} {N₀ K : ℕ}
    (h0 : 0 ∈ A)
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      (∅ : Finset ℕ) ⊆ H ∧ ∀ h ∈ H, h ∉ (∅ : Finset ℕ) → W < h) :
    ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card ≤ 3 * (K - 1) ∧ (∀ h ∈ H, W < h) ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H) ∧
      IsRepHub A n H := by
  intro W N
  obtain ⟨n, hn, H, hcard, hhub, hmin, -, hrest⟩ := hsplit W N
  have hlargeW : ∀ h ∈ H, W < h := fun h hh =>
    hrest h hh (Finset.notMem_empty h)
  refine ⟨n, hn, H, hcard, hlargeW, ?_, hhub⟩
  exact two_rep_shadow_of_large_hub h0 hhub
    (fun h hh => by have := hlargeW h hh; omega)

/-- Cofinal pigeonhole over a bounded value: some value recurs
cofinally. -/
theorem cofinal_value_pigeonhole {C : ℕ} (P : ℕ → ℕ → Prop)
    (hP : ∀ N, ∃ n, N ≤ n ∧ ∃ c, c ≤ C ∧ P n c) :
    ∃ c, c ≤ C ∧ ∀ N, ∃ n, N ≤ n ∧ P n c := by
  classical
  by_contra hno
  push_neg at hno
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

/-- **The canonical hub shape.**  On top of the stable core: a single
hub cardinality `c*` recurs at every window (cardinality classes are
downward-closed in the window, so the cofinally-recurring class works
everywhere).  A counterexample's failure thus concentrates on minimal
hubs of one fixed size, one fixed core, and level-scale escorts. -/
theorem stable_core_card_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K S c, c ≤ 3 * (K - 1) ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, S, hsplit⟩ := stable_core_of_hfail hcov hfail
  -- the set of cards recurring cofinally at window W
  set Good : ℕ → ℕ → Prop := fun W c =>
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card = c ∧ IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h with hGood
  have hdown : ∀ W W' c, W ≤ W' → Good W' c → Good W c := by
    intro W W' c hWW' hg N
    obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hg N
    exact ⟨n, hn, H, hcard, hhub, hmin, hSH,
      fun h hh hhS => by have := hrest h hh hhS; omega⟩
  have hperW : ∀ W, ∃ c, c ≤ 3 * (K - 1) ∧ Good W c := by
    intro W
    have hP : ∀ N, ∃ n, N ≤ n ∧ ∃ c, c ≤ 3 * (K - 1) ∧
        (∃ H : Finset ℕ, H.card = c ∧ IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) := by
      intro N
      obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit W N
      exact ⟨n, hn, H.card, hcard, H, rfl, hhub, hmin, hSH, hrest⟩
    obtain ⟨c, hc, hcof⟩ := cofinal_value_pigeonhole
      (P := fun n c => ∃ H : Finset ℕ, H.card = c ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) hP
    exact ⟨c, hc, hcof⟩
  -- pigeonhole the card across windows; downward closure finishes
  by_contra hno
  push_neg at hno
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
the hubs ARE the core — one fixed finite team hits every 3-rep of
cofinally many targets. -/
theorem recurring_team_of_tight_core {A : Set ℕ} {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hceq : c = S.card) :
    ∀ N, ∃ n, N ≤ n ∧ IsRepHub A n S := by
  intro N
  obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit 0 N
  have hHS : S = H := Finset.eq_of_subset_of_card_le hSH (by omega)
  rw [← hHS] at hhub
  exact ⟨n, hn, hhub⟩

/-- **The hub endgame.**  Full assembly of tonight's first-principles
chain: under the counterexample interfaces there exist a fixed
guardian core `S`, a fixed hub cardinality `c ≥ 2` with
`S.card ≤ c`, such that at every window cofinally many targets carry
minimal hubs of size exactly `c` containing `S` with everything else
above the window — and if the core is tight (`c = S.card`), one fixed
finite team `S` hubs cofinally many targets outright.  The enemy's
shape is canonical; the branches are: tight team (fixed-pair pipeline
for `c = 2`, team machinery for `c ≥ 3`) or genuine level-scale
escorts (counting-vise territory, with the order-2 shadow when
`S = ∅`). -/
theorem hub_endgame_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ K S c, c ≤ 3 * (K - 1) ∧ 2 ≤ c ∧ S.card ≤ c ∧
      (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) ∧
      (c = S.card → ∀ N, ∃ n, N ≤ n ∧ IsRepHub A n S) := by
  obtain ⟨K, S, c, hcK, hsplit⟩ := stable_core_card_of_hfail hcov hfail
  obtain ⟨N₂, hN₂⟩ := hub_card_ge_two_of_hfail h0 hcov hdb hanchor hfail
  obtain ⟨n, hn, H, hcard, hhub, hmin, hSH, hrest⟩ := hsplit 0 N₂
  have hc2 : 2 ≤ c := by
    have := hN₂ n hn H hhub
    omega
  have hSc : S.card ≤ c := by
    have := Finset.card_le_card hSH
    omega
  exact ⟨K, S, c, hcK, hc2, hSc, hsplit,
    fun hceq => recurring_team_of_tight_core hsplit hceq⟩

/-- The tight-pair leaf, explicit: a tight core of size two hands the
fixed-pair pipeline its recurring destroyer pair. -/
theorem pipeline_entry_of_tight_pair {A : Set ℕ} {N₀ : ℕ} {S : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hteam : ∀ N, ∃ n, N ≤ n ∧ IsRepHub A n S)
    (hS2 : S.card = 2) :
    ∃ u v, u ≠ v ∧ ∀ N, ∃ n, N ≤ n ∧ IsPairDestroyer A u v n := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.1 hS2
  refine ⟨u, v, huv, fun N => ?_⟩
  obtain ⟨n, hn, hhub⟩ := hteam (max N N₀)
  exact ⟨n, le_trans (le_max_left _ _) hn,
    pairDestroyer_of_pair_hub h0 hcov (le_trans (le_max_right _ _) hn)
      hhub⟩

/-- **The team-translate equivalence.**  For a team-hubbed target
whose team survives the deletion, order-3 failure under `B` is
EXACTLY simultaneous order-2 destruction of every team translate:
`n` dies iff for each `s ∈ S`, every 2-representation of `n - s`
meets `B`.  The tight-team branch is therefore the simultaneous
translate-destruction problem — the guardian-bridge territory, with
the counting vise applying per translate. -/
theorem team_target_fails_iff {A B : Set ℕ} {n : ℕ} {S : Finset ℕ}
    (hhub : IsRepHub A n S) (hSA : ∀ s ∈ S, s ∈ A)
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

/-- **Disjoint representations inject into the deletion.**  If a
target fails under `B` (every representation meets `B`), any family of
`K` pairwise-disjoint representations selects `K` distinct elements of
`B` below the target.  The per-target quantitative heart of Engine
V10, standalone: failing targets can never out-multiply the deletion
below them. -/
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

end Erdos881
