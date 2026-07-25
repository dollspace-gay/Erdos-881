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

/-- **The alignment demand.**  If a team-hubbed target fails under a
deletion whose only member below the target is the single marker `b`,
then `b` privately owns EVERY team translate: each `n - s` has all
its 2-representations through `b`.  This is the supply the enemy must
stock, for every choice of marker, at every scale — and the lab
census finds it only in digit-rigid (carry-repairable) structures. -/
theorem alignment_of_single_marker_failure {A B : Set ℕ} {n b : ℕ}
    {S : Finset ℕ}
    (hhub : IsRepHub A n S) (hSA : ∀ s ∈ S, s ∈ A)
    (hBS : ∀ s ∈ S, s ∉ B) (hSn : ∀ s ∈ S, s ≤ n)
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B)
    (honly : ∀ x ∈ B, x ≤ n → x = b) :
    ∀ s ∈ S, ∀ x ∈ A, ∀ y ∈ A, x + y = n - s → x = b ∨ y = b := by
  intro s hs x hx y hy hxy
  have htrans := (team_target_fails_iff hhub hSA hBS hSn).1 hdead
  rcases htrans s hs x hx y hy hxy with h | h
  · exact Or.inl (honly x h (by omega))
  · exact Or.inr (honly y h (by omega))

/-- **Forced supply: reversed team translates.**  Covering makes the
aligned marker's representations exist, not just exclusive: a failing
team target in a single-marker window forces `n - s - b ∈ A` for
every team member — the set `A` must contain the reversed team
translate `(n - b) - S` outright.  The enemy's own failure mandate
stocks `A` with team-patterned blocks at every scale, for every
marker choice: the self-interaction constraints these blocks create
against the privateness demand are the closing front. -/
theorem reversed_translate_of_alignment {A B : Set ℕ} {N₀ n b : ℕ}
    {S : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hhub : IsRepHub A n S) (hSA : ∀ s ∈ S, s ∈ A)
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

/-- **Block self-interaction.**  Two single-marker failures force two
reversed team blocks into `A`; the first target's privateness then
constrains every cross-difference: whenever a second-block element
completes a 2-representation of a first-target translate, it must
pass through the first marker.  These are the accumulating dodge
constraints — `|S|²` per marker pair, at every scale, against the
enemy's own forced supply.  The precise closing front of the
tight-team branch. -/
theorem block_self_interaction {A B₁ : Set ℕ} {N₀ n₁ n₂ b₁ b₂ : ℕ}
    {S : Finset ℕ}
    (hcov : PairCovers A N₀)
    (hhub₁ : IsRepHub A n₁ S) (hSA : ∀ s ∈ S, s ∈ A)
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

/-- **Doubles service is doubling rigidity.**  When the failing
target sits at `n = 2b + s₀` (the marker served through its own
double, the only mechanism the window census finds), the alignment
demand says exactly that `b`''s double has the unique representation
`(b, b)` — the Cantor minimality mechanism, forced.  The convergence,
in one statement: the enemy''s service supply IS doubling rigidity,
and doubling rigidity is the carry-repairable structure. -/
theorem doubling_rigidity_of_service {A B : Set ℕ} {n b s₀ : ℕ}
    {S : Finset ℕ}
    (hhub : IsRepHub A n S) (hSA : ∀ s ∈ S, s ∈ A)
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

/-- **Rigidity is reflection-freeness.**  An element''s double has the
unique representation `(x, x)` exactly when `A` contains no symmetric
pair around `x`: the reflection of `A` through `x` meets `A` only at
`x` itself.  The convergence''s rigidity interface, in the campaign''s
mirror vocabulary. -/
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

/-- **Rigid markers kill reflection levels at their doubles.**  A
doubling-rigid element admits no reflection level at `2x`: covering
supplies a fiber element besides `x`, and level symmetry would
complete it to a forbidden symmetric pair.  Tonight''s rigidity
interface meets the verified mirror bridge: the enemy needs rigid
markers everywhere, and every rigid marker erases a mirror level —
while the bridge kills any enemy whose surviving mirror levels keep
bounded gaps. -/
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

/-- **The propagation base.**  If a double `2x` fails at order 3
under `B`, then for EVERY surviving element `c`, the translate
`2x - c` is 2-destroyed by `B`: the failure cascades one level down
through each of our choices.  Engine V11''s descent iterates this
against the covering supply of surviving `c`''s — each level of the
cascade demands the full alignment supply anew. -/
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

/-- **The doubles-mode chain kill.**  If every late element is
doubles-served — rigid with its `d`-predecessor present (the
`(b, b-d)` alignment) — the chain `b, b-d, b-2d` forms a symmetric
pair around its interior point, violating that point''s own rigidity.
One of the enemy''s two service modes is impossible outright: service
must route through partners `q ≠ b`, whose forced `d`-pairs are
exactly the matching leaf''s demand.  The two remaining leaves share
one supply. -/
theorem no_total_doubles_service {A : Set ℕ} {N₀ Ns d : ℕ}
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

/-- **Service exclusion.**  A unique service fiber bars every third
element: if `b + q` has exactly the representation `(b, q)`, then for
any `a ∈ A` other than `b` and `q`, the complement `b + q - a` is not
in `A`.  Each served marker punches `|A ∩ window|`-many holes into
`A` at the service scale — the partner-mode''s accumulating cost
against covering density. -/
theorem service_exclusion {A : Set ℕ} {b q : ℕ}
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

/-- **Service sums avoid `A`.**  With `0 ∈ A`, a unique service fiber
forces its sum out of `A`: else `(0, s)` would be a second
representation.  Every served marker contributes a valley point. -/
theorem service_sum_not_mem {A : Set ℕ} {b q : ℕ}
    (h0 : 0 ∈ A) (hb : b ∈ A) (hq : q ∈ A) (hb0 : 0 < b) (hq0 : 0 < q)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = b + q →
      (p = b ∧ r = q) ∨ (p = q ∧ r = b)) :
    b + q ∉ A := by
  intro hmem
  rcases huniq 0 h0 (b + q) hmem (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    omega

/-- **Service sums are injective across markers.**  Distinct served
markers have distinct service sums: a shared sum would give the
shared fiber two representations.  Hence unique-fiber values are at
least as plentiful as served markers at every scale — the enemy needs
the unique-fiber set `U` to track `A`''s own density, cofinally. -/
theorem service_sums_injective {A : Set ℕ} {b₁ q₁ b₂ q₂ : ℕ}
    (hb₁ : b₁ ∈ A) (hq₁ : q₁ ∈ A) (hb₂ : b₂ ∈ A) (hq₂ : q₂ ∈ A)
    (huniq₁ : ∀ p ∈ A, ∀ r ∈ A, p + r = b₁ + q₁ →
      (p = b₁ ∧ r = q₁) ∨ (p = q₁ ∧ r = b₁))
    (hne : b₂ ≠ b₁ ∧ b₂ ≠ q₁) :
    b₁ + q₁ ≠ b₂ + q₂ := by
  intro heq
  rcases huniq₁ b₂ hb₂ q₂ hq₂ (by omega) with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hne.1 h1
  · exact hne.2 h1

/-- **Partner service bars the predecessor.**  If the twin service
sum `b + q - d` has the unique fiber `(b, q - d)` with `q ≠ b`, then
`b - d ∉ A`: a predecessor would complete `(q, b - d)` into a second
representation.  With the chain kill this splits every late window:
partner-served markers are predecessor-free, doubles-served markers
have predecessors, and no `d`-chain reaches length three.  The
enemy''s late structure is forced into the exact P/D digit-split the
Cantor world realizes with digit₁ ∈ {0, 1}. -/
theorem no_predecessor_of_partner_service {A : Set ℕ} {b q d : ℕ}
    (hd : 0 < d) (hdb : d ≤ b) (hdq : d ≤ q) (hqb : q ≠ b)
    (hq : q ∈ A) (hqd : q - d ∈ A)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = b + q - d →
      (p = b ∧ r = q - d) ∨ (p = q - d ∧ r = b)) :
    b - d ∉ A := by
  intro hmem
  rcases huniq q hq (b - d) hmem (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hqb h1
  · omega

/-- **No chains of length three.**  Two consecutive `d`-steps inside
`A` put a symmetric pair around the middle element; if the middle is
doubling-rigid the chain collapses.  Standalone form of the chain
kill for the structure split. -/
theorem no_three_chain_of_rigid_middle {A : Set ℕ} {x d : ℕ}
    (hd : 0 < d)
    (hx : x ∈ A) (hxu : x + d ∈ A) (hxd : x + 2 * d ∈ A)
    (hrig : ∀ p ∈ A, ∀ r ∈ A, p + r = 2 * (x + d) → p = x + d ∧ r = x + d) :
    False := by
  have := hrig x hx (x + 2 * d) hxd (by ring)
  omega

/-- **Partners are doubles-served.**  A partner-served marker''s twin
requires `q - d ∈ A`; if the partner `q` were itself partner-served,
its own twin uniqueness would bar exactly that predecessor.  So in
the forced P/D split, every service edge points from P into D: the
enemy''s wiring diagram is bipartite with doubles-rigid pair-tops
serving everyone. -/
theorem partner_is_doubles_served {A : Set ℕ} {q q' d : ℕ}
    (hd : 0 < d) (hdq : d ≤ q) (hdq' : d ≤ q') (hq'q : q' ≠ q)
    (hq' : q' ∈ A) (hq'd : q' - d ∈ A)
    (hqd : q - d ∈ A)
    (huniq : ∀ p ∈ A, ∀ r ∈ A, p + r = q + q' - d →
      (p = q ∧ r = q' - d) ∨ (p = q' - d ∧ r = q)) :
    False :=
  no_predecessor_of_partner_service hd hdq hdq' hq'q hq' hq'd huniq hqd

/-- Order-2 disjoint representations: `K` pair-representations with
no shared part values. -/
def HasDisjointPairReps (A : Set ℕ) (n K : ℕ) : Prop :=
  ∃ P : Fin K → Fin 2 → ℕ,
    (∀ i k, P i k ∈ A) ∧
    (∀ i, P i 0 + P i 1 = n) ∧
    (∀ i j k l, i ≠ j → P i k ≠ P j l)

/-- Order-2 hub: a finite set meeting every pair representation. -/
def IsPairHub (A : Set ℕ) (n : ℕ) (H : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H

/-- **Engine V10 at order 2.**  Unbounded disjoint pair-representation
growth defeats order-2 minimality: a slow spread deletion keeps `A`
an order-2 basis. -/
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
    push_neg at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, P i k = b j := by
      intro i
      have h0 := hPA i 0
      have h1 := hPA i 1
      by_contra hnone
      push_neg at hnone
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

/-- Pair-hub extraction: no `K` disjoint pair-representations yields
a hub of at most `2·(K-1)` values meeting every pair representation. -/
theorem pairHub_of_no_disjointPairReps {A : Set ℕ} {n K : ℕ}
    (hno : ¬HasDisjointPairReps A n K) :
    ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairHub A n H := by
  classical
  have h0 : HasDisjointPairReps A n 0 :=
    ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  have hcross : ∃ J, J < K ∧ HasDisjointPairReps A n J ∧
      ¬HasDisjointPairReps A n (J + 1) := by
    by_contra hnc
    push_neg at hnc
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
    push_neg at hnot
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

/-- **The dual pillar: minimality forces canonical order-2 hubs.**
`A`''s ℵ₀-minimality (every infinite deletion destroys order 2 — the
hypothesis of Erdős 881) plays the role `hfail` played at order 3:
some fixed `K` bounds a pair-hub for cofinally many targets.  The
2-destruction mandate is now canonical, entered from the raw
minimality hypothesis; the whole tower/core/split machinery applies
verbatim one level down, and its interaction with the order-3 tree
is the digit recursion. -/
theorem cofinal_bounded_pairHubs_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairHub A n H := by
  classical
  have hnodis : ¬∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K := by
    intro hdis
    obtain ⟨B, hBsub, hBinf, N₁, hN₁⟩ :=
      surviving_pair_deletion_of_disjointPairReps hcov hdis
    exact hmin B hBsub hBinf ⟨N₁, hN₁⟩
  push_neg at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := pairHub_of_no_disjointPairReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

/-- Predicate-generic stable core: the budget descent works for any
hub notion. -/
theorem stable_core_generic {C : ℕ} (Hub : ℕ → Finset ℕ → Prop) :
    ∀ d S,
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧ Hub n H ∧
      S ⊆ H ∧ H.card ≤ S.card + d) →
    ∃ S' : Finset ℕ, S ⊆ S' ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card ≤ C ∧
        Hub n H ∧ S' ⊆ H ∧
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
        H.card ≤ C ∧ Hub n H ∧ S ⊆ H ∧
        ∀ h ∈ H, h ∉ S → W < h
    · exact ⟨S, Finset.Subset.refl S, hstable⟩
    · push_neg at hstable
      obtain ⟨W₁, N₁, hW₁⟩ := hstable
      rcases cofinal_dichotomy
        (fun n H' => ∃ H : Finset ℕ, H.card ≤ C ∧ Hub n H ∧
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

/-- **The canonical 2-destroyer core.**  From minimality alone: one
fixed finite set `S₂` such that at every window, cofinally many
targets have ALL their pair representations through `S₂` plus
elements above the window.  The 2-destruction mandate the legacy
campaign assumed (recurring destroyer pairs, guardian teams) is now
DERIVED, canonical, and stable across all scales — the order-2 rail
of the digit recursion. -/
theorem stable_pair_core_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairHub A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_pairHubs_of_minimality hcov hmin
  obtain ⟨S, -, hsplit⟩ := stable_core_generic
    (C := 2 * (K - 1)) (fun n H => IsPairHub A n H)
    (2 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      exact ⟨n, hn, H, hcard, hhub, Finset.empty_subset _,
        by simpa using hcard⟩)
  exact ⟨K, S, hsplit⟩

/-- **Canonical order-2 shape**: core and cardinality stabilize
across all windows, exactly as at order 3. -/
theorem stable_pair_core_card_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K S c, c ≤ 2 * (K - 1) ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsPairHub A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, S, hsplit⟩ := stable_pair_core_of_minimality hcov hmin
  set Good : ℕ → ℕ → Prop := fun W c =>
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ, H.card = c ∧ IsPairHub A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h with hGood
  have hdown : ∀ W W' c, W ≤ W' → Good W' c → Good W c := by
    intro W W' c hWW' hg N
    obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hg N
    exact ⟨n, hn, H, hcard, hhub, hSH,
      fun h hh hhS => by have := hrest h hh hhS; omega⟩
  have hperW : ∀ W, ∃ c, c ≤ 2 * (K - 1) ∧ Good W c := by
    intro W
    obtain ⟨c, hc, hcof⟩ := cofinal_value_pigeonhole
      (P := fun n c => ∃ H : Finset ℕ, H.card = c ∧ IsPairHub A n H ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) (fun N => by
        obtain ⟨n, hn, H, hcard, hhub, hSH, hrest⟩ := hsplit W N
        exact ⟨n, hn, H.card, hcard, H, rfl, hhub, hSH, hrest⟩)
    exact ⟨c, hc, hcof⟩
  by_contra hno
  push_neg at hno
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

/-- **The recurring destroyer pair, derived.**  If the canonical
order-2 core is tight with two elements, minimality alone yields the
fixed pair `{u, v}` through which ALL pair representations of
cofinally many targets pass — the 2-destruction configuration the
entire legacy campaign took as its starting hypothesis. -/
theorem recurring_destroyer_pair_of_tight_core {A : Set ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsPairHub A n H ∧
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

/-- **The rails'' interaction bridge.**  The canonical order-2 hub is
definitionally the legacy campaign''s `TwoDestroyedBySet`: the new
first-principles tree and the old funnel/pinning machinery speak the
same language. -/
theorem pairHub_iff_twoDestroyed {A : Set ℕ} {n : ℕ} {H : Finset ℕ} :
    IsPairHub A n H ↔ TwoDestroyedBySet A (↑H) n := by
  constructor
  · intro h y hy z hz hyz
    rcases h y hy z hz hyz with h' | h'
    · exact Or.inl (Finset.mem_coe.2 h')
    · exact Or.inr (Finset.mem_coe.2 h')
  · intro h x hx y hy hxy
    rcases h x hx y hy hxy with h' | h'
    · exact Or.inl (Finset.mem_coe.1 h')
    · exact Or.inr (Finset.mem_coe.1 h')

/-- **Legacy entry from raw minimality.**  In the tight two-element
case the canonical order-2 core hands the legacy machinery its exact
fuel: cofinally many targets two-destroyed by one fixed pair.  The
pinning, fork, and funnel arsenal — built downstream of this shape as
an assumption — now runs on a theorem. -/
theorem legacy_twoDestruction_of_tight_core {A : Set ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsPairHub A n H ∧
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

/-- **Corrected covering: the recursion''s inheritance.**  In the
rigid regime, every late element is a predecessor-free element plus a
correction in `{0, d}` (chains stop at length two), so the
predecessor-free part `P` covers every late target up to a correction
in `{0, d, 2d}`.  This is the covering-like property `P` inherits —
the missing design piece of the digit recursion: the next level''s
analysis runs on `P` with corrected covering exactly as this level
ran on `A` with covering. -/
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
    · push_neg at hzd
      refine ⟨z, hz, 0, Or.inl rfl, by omega, ?_⟩
      intro hdz hzdA
      by_contra hbig
      push_neg at hbig
      exact absurd hbig (by
        have := hzd hdz hzdA
        omega)
  obtain ⟨p, hp, ε₁, hε₁, hpε₁, hpfree⟩ := hdec x hx
  obtain ⟨p', hp', ε₂, hε₂, hpε₂, hpfree'⟩ := hdec y hy
  refine ⟨p, hp, p', hp', hpfree, hpfree', ε₁ + ε₂, ?_, by omega⟩
  rcases hε₁ with h1 | h1 <;> rcases hε₂ with h2 | h2 <;> omega

/-- **Pool-restricted order-2 engine.**  The deletion engine only
needs an unbounded marker pool: restricting `B` to any unbounded
`P ⊆ A` re-runs the argument verbatim.  Applied to the
predecessor-free part, the machinery descends a level. -/
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
    push_neg at hall
    have hhit : ∀ i : Fin (K + 1), ∃ j, j < K ∧ ∃ k, Pm i k = b j := by
      intro i
      have h0 := hPA' i 0
      have h1 := hPA' i 1
      by_contra hnone
      push_neg at hnone
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

/-- **The second modulus exists.**  Restricting deletions to any
unbounded pool `P ⊆ A` (in particular the predecessor-free part),
minimality still forces canonical pair-hubs — and the stable core of
the restricted analysis carries the next level''s canonical
difference.  The digit recursion''s moduli emerge by pool
restriction, level by level. -/
theorem cofinal_bounded_pairHubs_of_minimality_pool {A P : Set ℕ}
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∀ N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairHub A n H := by
  classical
  have hnodis : ¬∀ K, ∃ N, ∀ n, N ≤ n → HasDisjointPairReps A n K := by
    intro hdis
    obtain ⟨B, hBsub, hBinf, N₁, hN₁⟩ :=
      surviving_pair_deletion_of_disjointPairReps_pool hPA hunb hdis
    exact hmin B (fun x hx => hPA (hBsub hx)) hBinf ⟨N₁, hN₁⟩
  push_neg at hnodis
  obtain ⟨K, hK⟩ := hnodis
  refine ⟨K, fun N => ?_⟩
  obtain ⟨n, hn, hno⟩ := hK N
  obtain ⟨H, hHcard, hHhub⟩ := pairHub_of_no_disjointPairReps hno
  exact ⟨n, hn, H, hHcard, hHhub⟩

/-- **The level-descent API, complete.**  Pool-restricted minimality
yields a stable canonical core: applied with `P` = the
predecessor-free part of the previous level, this is the next
level''s fixed guardian team, whose tight-pair difference is the next
modulus.  Iterating descends the digit tower rung by rung. -/
theorem stable_pair_core_of_minimality_pool {A P : Set ℕ}
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ K, ∃ S : Finset ℕ, ∀ W N, ∃ n, N ≤ n ∧
      ∃ H : Finset ℕ, H.card ≤ 2 * (K - 1) ∧ IsPairHub A n H ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h := by
  classical
  obtain ⟨K, hK⟩ := cofinal_bounded_pairHubs_of_minimality_pool hPA
    hunb hmin
  obtain ⟨S, -, hsplit⟩ := stable_core_generic
    (C := 2 * (K - 1)) (fun n H => IsPairHub A n H)
    (2 * (K - 1)) ∅ (fun N => by
      obtain ⟨n, hn, H, hcard, hhub⟩ := hK N
      exact ⟨n, hn, H, hcard, hhub, Finset.empty_subset _,
        by simpa using hcard⟩)
  exact ⟨K, S, hsplit⟩

/-- **Destruction sharpens on descent.**  With deletions drawn from
the pool `P`, a two-destroyed target''s mixed pairs (one part outside
`P`) must be hit on the pool side: the out-of-pool part is immune.
Level-two forks are single-channel — the descent gains strength as
it goes down. -/
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

/-- **Single-marker mixed exclusion.**  In a single-marker pool
window, a two-destroyed target admits NO mixed pair away from the
marker: `t` avoids `(P ∖ {b}) + (A ∖ P)` entirely.  At level two the
alignment demand is not a dichotomy but a direct structural ban —
the target''s mixed fiber collapses onto the marker alone. -/
theorem single_marker_mixed_exclusion {A P B : Set ℕ} {b t : ℕ}
    (hPA : P ⊆ A) (hB : B ⊆ P)
    (honly : ∀ x ∈ B, x ≤ t → x = b)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ p ∈ P, p ≠ b → ∀ q ∈ A, q ∉ P → p + q ≠ t := by
  intro p hp hpb q hq hqP hpq
  have hpB : p ∈ B :=
    mixed_pair_destruction_sharpens hPA hB hdest p hp q hq hqP hpq
  exact hpb (honly p hpB (by omega))

/-- **Outside pairs are banned.**  A two-destroyed target under a
pool deletion admits no representation with both parts outside the
pool: nothing there can be hit.  Destroyed targets avoid
`(A ∖ P) + (A ∖ P)` outright. -/
theorem no_outside_pairs_of_destroyed {A P B : Set ℕ} {t : ℕ}
    (hB : B ⊆ P)
    (hdest : ∀ x ∈ A, ∀ y ∈ A, x + y = t → x ∈ B ∨ y ∈ B) :
    ∀ q ∈ A, q ∉ P → ∀ q' ∈ A, q' ∉ P → q + q' ≠ t := by
  intro q hq hqP q' hq' hq'P hqq'
  rcases hdest q hq q' hq' hqq' with h | h
  · exact hqP (hB h)
  · exact hq'P (hB h)

/-- **The level-2 corep.**  In a single-marker pool window, every
representation shape of a destroyed target routes through the marker
— outside pairs are banned, mixed pairs collapse onto it, pure pairs
hit it — so covering forces `t - b ∈ A`.  The reversed-block supply
regenerates one level down, from bans instead of dichotomies. -/
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

/-- **Level-2 rigidity is free.**  A destroyed double in a
single-marker pool window is automatically doubling-rigid: every
representation must route through the marker, and the complement of
the marker in its own double is itself.  What required the full
alignment machinery at level 1 is definitional at level 2 — the
P/D split machinery (predecessor bans, chain kills) then applies
immediately at the emergent modulus. -/
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

/-- **Failing hubs live inside the deletion.**  A target failing
under `B` has every representation routed through `B`, so the part
of `B` below it is itself a rep-hub: the enemy''s guardians for
`B`-failures are OUR markers.  The tower pigeonholes can therefore
run over subsets of the finite set `B ∩ [0, W]` — a finite alphabet
per window regardless of hub cardinality growth: the constant-vs-log
gap dissolves at the window-split step. -/
theorem failing_hub_subset_deletion {A B : Set ℕ} {n : ℕ}
    [DecidablePred (· ∈ B)]
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) :
    IsRepHub A n ((Finset.range (n + 1)).filter (· ∈ B)) := by
  intro x hx y hy z hz hsum
  rcases hdead x hx y hy z hz hsum with h | h | h
  · exact Or.inl (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩)
  · exact Or.inr (Or.inl (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩))
  · exact Or.inr (Or.inr (Finset.mem_filter.2
      ⟨Finset.mem_range.2 (by omega), h⟩))

/-- **Finite-alphabet window pigeonhole.**  For a cofinal family of
finite witness sets all contained in one fixed finite set, some exact
subset recurs cofinally — direct pigeonhole over the powerset, no
cardinality budget needed.  This is the tower step for
deletion-contained hubs. -/
theorem cofinal_subset_pigeonhole {Q : ℕ → Finset ℕ → Prop}
    {F : Finset ℕ}
    (hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ H, H ⊆ F ∧ Q n H) :
    ∃ S ⊆ F, ∀ N, ∃ n, N ≤ n ∧ Q n S := by
  classical
  by_contra hno
  push_neg at hno
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

/-- **The per-deletion window core.**  For any deletion with cofinal
failing targets: at every window, one exact marker subset
`S ⊆ B ∩ [0, W]` recurs as the small part of minimal failing hubs.
The enemy''s per-deletion guardian structure is canonical over OUR
marker alphabet — the window analysis the constant-vs-log gap
blocked, now unconditional. -/
theorem per_deletion_window_core {A B : Set ℕ}
    [DecidablePred (· ∈ B)]
    (hfailB : ∀ N, ∃ n, N ≤ n ∧
      ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
        x ∈ B ∨ y ∈ B ∨ z ∈ B) (W : ℕ) :
    ∃ S ⊆ (Finset.range (W + 1)).filter (· ∈ B),
      ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
        H ∩ Finset.range (W + 1) =
          S ∩ Finset.range (W + 1) := by
  classical
  have hQ : ∀ N, ∃ n, N ≤ n ∧ ∃ S,
      S ⊆ (Finset.range (W + 1)).filter (· ∈ B) ∧
      (∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
        H ∩ Finset.range (W + 1) = S ∩ Finset.range (W + 1)) := by
    intro N
    obtain ⟨n, hn, hdead⟩ := hfailB N
    have hhub := failing_hub_subset_deletion (A := A) (B := B) hdead
    obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_hub hhub
    refine ⟨n, hn, H ∩ Finset.range (W + 1), ?_, H, hHhub, hHmin, ?_, ?_⟩
    · intro x hx
      obtain ⟨hxH, hxW⟩ := Finset.mem_inter.1 hx
      have := hHsub hxH
      obtain ⟨hxn, hxB⟩ := Finset.mem_filter.1 this
      exact Finset.mem_filter.2 ⟨hxW, hxB⟩
    · exact hHsub
    · rw [Finset.inter_assoc, Finset.inter_self]
  obtain ⟨S, hSF, hrec⟩ := cofinal_subset_pigeonhole
    (Q := fun n S => ∃ H : Finset ℕ, IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      H ⊆ (Finset.range (n + 1)).filter (· ∈ B) ∧
      H ∩ Finset.range (W + 1) = S ∩ Finset.range (W + 1))
    (F := (Finset.range (W + 1)).filter (· ∈ B)) hQ
  exact ⟨S, hSF, hrec⟩

/-- **Super-geometric escape collapse.**  If the deletion''s markers
grow super-geometrically (each beyond the square of the last), a
failing hub that has escaped past `√n` can contain at most one
marker: two escapees would straddle the square gap.  Escaped hubs
are singletons — and singleton hubs are private triples, which the
verified stream kill refutes.  The escape branch of the per-deletion
dichotomy dies at matched scale. -/
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

/-- **The per-deletion capstone.**  Against a super-geometric
deletion, every failing target''s minimal hub either reaches into the
prefix (a marker at or below `√n` — the guardian branch) or is a
single marker (the escape branch, fed to the stream kill).  The
composed endpoint of the night: the enemy''s defenses against each
deletion are our prefix markers or a lone escapee, nothing else. -/
theorem per_deletion_dichotomy_final {A : Set ℕ} {b : ℕ → ℕ}
    (hsg : ∀ j k, j < k → b j * b j < b k)
    {n : ℕ}
    (hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      (∃ j, x = b j) ∨ (∃ j, y = b j) ∨ (∃ j, z = b j))
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = n) :
    ∃ H : Finset ℕ, IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      (∀ h ∈ H, (∃ j, h = b j) ∧ h ≤ n) ∧
      ((∃ h ∈ H, h * h ≤ n) ∨ (∃ h₀, H = {h₀})) := by
  classical
  have hdead' : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ {m | ∃ j, m = b j} ∨ y ∈ {m | ∃ j, m = b j} ∨
      z ∈ {m | ∃ j, m = b j} := hdead
  have hhub := failing_hub_subset_deletion
    (B := {m | ∃ j, m = b j}) hdead'
  obtain ⟨H, hHsub, hHhub, hHmin⟩ := exists_minimal_hub hhub
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
    push_neg at hesc
    obtain ⟨h, hh, hhn⟩ := hesc
    exact ⟨h, hh, hhn⟩

/-- `a` owns `n`: the target sits in `(a, 2a)`, is completed by an
element, and `a` is its unique big-fiber element.  The atomic unit of
the per-element guarding supply — the classification statement''s
formal vocabulary. -/
def OwnsTarget (A : Set ℕ) (a n : ℕ) : Prop :=
  a < n ∧ n < 2 * a ∧ n - a ∈ A ∧
  ∀ y ∈ A, 2 * y > n → y < n → y ≠ a → n - y ∉ A

/-- Ownership steps down: the completion is a smaller element — the
start of the ownership chain whose infinite coherence is the digit
expansion. -/
theorem OwnsTarget.chain_step {A : Set ℕ} {a n : ℕ}
    (h : OwnsTarget A a n) : n - a ∈ A ∧ n - a < a := by
  obtain ⟨h1, h2, h3, _⟩ := h
  exact ⟨h3, by omega⟩

/-- Owned targets are not shared: the unique big fiber pins the
owner. -/
theorem OwnsTarget.unique_owner {A : Set ℕ} {a a' n : ℕ}
    (ha : a ∈ A) (ha' : a' ∈ A)
    (h : OwnsTarget A a n) (h' : OwnsTarget A a' n) : a = a' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  by_contra hne
  have := h4 a' ha' (by omega) (by omega) (fun hc => hne hc.symm)
  exact this h3'

/-- **The classification statement** (the single remaining wall), in
formal vocabulary: universal ownership.  Cofinal per-element supply:
every sufficiently large element owns a target.  Conjecture (the
final step of the campaign): universal ownership + covering forces
digit structure, whose carry repair contradicts `hfail`.  Everything
below this statement is machine-verified; the lab locates the
threshold exactly at universality. -/
def UniversalOwnership (A : Set ℕ) (Ns : ℕ) : Prop :=
  ∀ a ∈ A, Ns ≤ a → ∃ n, OwnsTarget A a n

/-- **The ownership chain.**  Under universal ownership every element
descends to the base through ownership steps: the sequence of
completions `a > s(a) > s²(a) > …` — the digit-expansion object of
the classification, existing unconditionally once ownership is
universal.  Its coherence across elements is the digit-forcing
conjecture; its existence is now a theorem. -/
theorem ownership_chain {A : Set ℕ} {Ns : ℕ}
    (huniv : UniversalOwnership A Ns) :
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
    · push_neg at hlt
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

/-- **Ownership bans the reflection.**  An owned target excludes the
entire reflected copy of `A` below its completion: for every element
`s'` strictly inside `(0, n - a)`, the value `n - s'` is not in `A`
— else it would be a second big fiber.  Each owner punches a
structured, `A`-shaped hole system just below its target; owners at
scale `k` thereby constrain `A` at scale `k - 1` near completions.
The two-scale coupling of the coherence conjecture, as one
identity. -/
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

/-- **Ownership is the singleton 2-hub** (up to the midpoint): every
pair representation of an owned target passes through its owner or
sits exactly at the half.  The classification wall and the order-2
rail''s tight singleton case are the same object — the ring of the
night''s theory closes. -/
theorem ownsTarget_pairHub {A : Set ℕ} {a n : ℕ}
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

/-- **Strip reflection.**  Elements strictly between an owner and its
target reflect into co-`A`: each strip inhabitant sends one demand
into the small scale.  The squeeze''s dichotomy: empty strips force
gap-domination (`s(a) ≤ gap(a)`, the recursive gap-hierarchy of
digit towers); inhabited strips cascade small co-`A` demands at
knife-edge density. -/
theorem strip_reflection {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ y ∈ A, a < y → y < n → n - y ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro y hy hay hyn
  exact h4 y hy (by omega) (by omega) (by omega)

/-- **Gap domination.**  If the strip is empty, the target hides in
the gap: the completion is bounded by the distance to the next
element — the digit-tower gap hierarchy, per owner. -/
theorem gap_domination_of_empty_strip {A : Set ℕ} {a n a' : ℕ}
    (hown : OwnsTarget A a n)
    (hstrip : ∀ y ∈ A, a < y → y < n → False)
    (ha' : a' ∈ A) (haa' : a < a') (h0 : 0 ∈ A) :
    n - a ≤ a' - a := by
  by_contra hlt
  push_neg at hlt
  have hn' : a' < n := by omega
  exact hstrip a' ha' haa' hn'

/-- **The strip counting inequality.**  The reflection injects each
owner''s strip population into the co-`A` room below its completion:
`|A ∩ (a, n)| ≤ |co-A ∩ (0, n - a)|`.  The per-owner quantitative
squeeze; octave sums of these are the multi-owner counting frontier. -/
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

/-- **Mid-window reflection.**  The moat''s other half: big-fiber
elements BELOW the owner also reflect into co-`A`.  Equivalently the
completion''s translate by every near-difference at the owner avoids
`A`: `s + (a - y) ∉ A` — the constraint that links completions to
local difference structure, the gap-branch''s coherence mechanism. -/
theorem midwindow_reflection {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ y ∈ A, 2 * y > n → y < a → n - y ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro y hy hbig hya
  exact h4 y hy hbig (by omega) (by omega)

/-- **Cross-owner exclusion** — the first multi-owner constraint.
Overlapping owners bar each other''s target-differences from `A`:
the later owner sits in the earlier strip, the earlier owner in the
later mid-window.  Pairs of owners cannot coexist without punching
paired holes at the small scale — the pairwise skeleton of the
octave-sum inequality. -/
theorem cross_owner_exclusion {A : Set ℕ} {a₁ a₂ n₁ n₂ : ℕ}
    (h₁ : OwnsTarget A a₁ n₁) (h₂ : OwnsTarget A a₂ n₂)
    (ha : a₁ < a₂) (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) :
    (a₂ < n₁ → n₁ - a₂ ∉ A) ∧
    (2 * a₁ > n₂ → n₂ - a₁ ∉ A) := by
  constructor
  · intro hlt
    exact strip_reflection h₁ a₂ ha₂ ha hlt
  · intro hbig
    exact midwindow_reflection h₂ a₁ ha₁ hbig ha

/-- **The consecutive-owner dichotomy.**  For any owner and any later
element: the completion fits inside the distance to it, or the
completion has no predecessor at that distance — it differs from the
distance by a co-`A` value.  Unconditional, per consecutive pair: the
completions are gap-dominated or gap-predecessor-free.  The P/D split
re-emerges with the LOCAL GAPS as moduli: the digit recursion''s
moduli are the gap structure itself. -/
theorem consecutive_owner_dichotomy {A : Set ℕ} {a a' n : ℕ}
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

/-- **Completion isolation.**  In completion coordinates the moat is
two-sided: `s ± δ ∉ A` for every near-difference `δ` of the owner —
downward by strip elements, upward by mid-window elements.  Each
completion sits alone in `A`, insulated by its owner''s local
difference structure: the working form of the squeeze. -/
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

/-- **Completion mutual avoidance** — the difference-splitting seed.
One owner''s completion can never land in another owner''s isolation
zone: completion values avoid all strip-reflected positions of every
other owner.  Completion-differences and owner-differences separate
into disjoint additive layers — the coherence mechanism: iterated
over octaves, the layer hierarchy is the digit system. -/
theorem completion_mutual_avoidance {A : Set ℕ} {a₁ n₁ a₂ n₂ : ℕ}
    (h₁ : OwnsTarget A a₁ n₁) (h₂ : OwnsTarget A a₂ n₂) :
    ∀ y ∈ A, a₁ < y → y < n₁ →
      n₂ - a₂ ≠ (n₁ - a₁) - (y - a₁) := by
  intro y hy hay hyn heq
  have hs₂ : n₂ - a₂ ∈ A := h₂.chain_step.1
  have hban := (completion_isolation h₁).1 y hy hay hyn
  rw [← heq] at hban
  exact hban hs₂

/-- **Mid-window demand injection** — the incidence seed.  For a
fixed mid-element `y`, distinct owners holding `y` in their
mid-windows pay DISTINCT co-`A` demands (targets are injective, so
the demands `n - y` separate).  Unconditional — gap domination does
not exempt an owner from mid-window payments.  The per-`y` column of
the octave incidence count. -/
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
    exact hne (h₁.unique_owner ha₁ ha₂ h₂ ▸ rfl)
  have hy₁ : y < n₁ := by
    obtain ⟨g1, _, _, _⟩ := h₁
    omega
  have hy₂ : y < n₂ := by
    obtain ⟨g1, _, _, _⟩ := h₂
    omega
  omega

/-- **The column bound.**  The number of owners holding a fixed
mid-element `y` is at most the co-`A` room below `y`-scale: distinct
owners'' demands inject into `co-A ∩ (0, y)`.  The octave incidence
matrix has verified column bounds — the density constraint the
octave aggregation sums. -/
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
    exact hne (h₁.unique_owner (hOA a₁ ha₁) (hOA a₂ ha₂) h₂)

/-- **The zero-payment squeeze.**  An owner paying nothing (big
window empty besides itself) forces its neighbors far away: every
predecessor is at most half the target, every successor at least the
target.  Zero-payment owners sit in giant-gap valleys. -/
theorem zero_payment_squeeze {A : Set ℕ} {a t : ℕ}
    (hown : OwnsTarget A a t)
    (hpay : ∀ y ∈ A, 2 * y > t → y < t → y = a) :
    (∀ y ∈ A, y < a → 2 * y ≤ t) ∧ (∀ y ∈ A, a < y → t ≤ y) := by
  have h1 : a < t := hown.1
  have h2 : t < 2 * a := hown.2.1
  constructor
  · intro y hy hya
    by_contra hgt
    push_neg at hgt
    have := hpay y hy hgt (by omega)
    omega
  · intro y hy hay
    by_contra hlt
    push_neg at hlt
    have := hpay y hy (by omega) hlt
    omega

/-- **Giant gaps around zero-payment owners.**  Any predecessor and
successor of a zero-payment owner straddle more than half the owner:
`a⁺ - a⁻ > a / 2`.  Summed over an octave this caps zero-payment
owner counts at a constant — covering density then forces payments
cofinally: the optimization lower bound''s heart. -/
theorem zero_payment_gap_bound {A : Set ℕ} {a t p q : ℕ}
    (hown : OwnsTarget A a t)
    (hpay : ∀ y ∈ A, 2 * y > t → y < t → y = a)
    (hp : p ∈ A) (hplt : p < a) (hq : q ∈ A) (hqgt : a < q) :
    2 * (q - p) > a := by
  obtain ⟨hpred, hsucc⟩ := zero_payment_squeeze hown hpay
  have h1 := hpred p hp hplt
  have h2 := hsucc q hq hqgt
  have h3 : a < t := hown.1
  have h4 : t < 2 * a := hown.2.1
  omega

/-- **No five zero-payers in an octave.**  Two disjoint straddling
triples each span more than half the octave floor — together they
overfill the octave.  Zero-payment owners number at most four per
octave; covering density (√-supply per octave) therefore forces
PAYING owners cofinally: the optimization lower bound, modulo the
final density count. -/
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

/-- **Rich octaves are cofinal.**  Covering''s √-supply cannot live in
octaves of four: if every late octave held at most four elements, the
count up to `2^D` would grow linearly in `D` while the covering vise
demands `2^D` below its square.  Exponential beats quadratic: some
octave beyond every bound holds at least five elements. -/
theorem octave_rich_of_covering {A : Set ℕ} [DecidablePred (· ∈ A)]
    {N₀ : ℕ} (hcov : PairCovers A N₀) :
    ∀ k₀, ∃ k, k₀ ≤ k ∧
      5 ≤ ((Finset.Ioc (2 ^ k) (2 ^ (k + 1))).filter (· ∈ A)).card := by
  intro k₀
  by_contra hno
  push_neg at hno
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

/-- **Paying owners in rich octaves.**  In any octave holding five
elements above the universality threshold, some owner PAYS.  Zero
payment across the octave would overfill it via the giant-gap
bound. -/
theorem paying_owner_in_rich_octave {A : Set ℕ}
    [DecidablePred (. ∈ A)] {Ns X : ℕ}
    (huniv : UniversalOwnership A Ns) (hXNs : Ns ≤ X)
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
  push_neg at hno
  have hp2 : ∀ y ∈ A, 2 * y > t2 → y < t2 → y = x2 := by
    intro y hy hby hyt
    exact hno x2 t2 y hA2 hX2 ho2 hy hby hyt
  have hp4 : ∀ y ∈ A, 2 * y > t4 → y < t4 → y = x4 := by
    intro y hy hby hyt
    exact hno x4 t4 y hA4 hX4 ho4 hy hby hyt
  exact no_five_zero_payers hA1 hA3 hA5 ho2 ho4 hp2 hp4
    ⟨h12, h23, h34, h45⟩ ⟨hX1, hU5⟩

/-- **THE OPTIMIZATION LOWER BOUND.**  Covering plus universal
ownership force PAYING owners beyond every bound: rich octaves are
cofinal, and rich octaves cannot be all-zero-payment.  The enemy
cannot live payment-free — the co-`A` demand cascade is unavoidable,
completing the payment side of the squeeze.  What remains of the
classification is only the payment-capacity recursion. -/
theorem paying_owners_cofinal {A : Set ℕ} [DecidablePred (· ∈ A)]
    {N₀ Ns : ℕ} (hcov : PairCovers A N₀)
    (huniv : UniversalOwnership A Ns) :
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
    paying_owner_in_rich_octave (X := 2 ^ k) huniv (by omega) hrich'
  exact ⟨a, t, y, by omega, haA, hown, hyA, hby, hyt, hya⟩

/-- **The payment demand.**  A paying witness contributes a fresh
co-`A` point strictly inside the lower half of the target: the
ledger entry each cofinal payer writes.  With the block-pigeonhole
(every five consecutive owners contain a payer) the ledger gains
`⌊octave-count / 5⌋` entries per octave — the telescope''s input. -/
theorem payment_demand {A : Set ℕ} {a t y : ℕ}
    (hown : OwnsTarget A a t)
    (hy : y ∈ A) (hby : 2 * y > t) (hyt : y < t) (hya : y ≠ a) :
    t - y ∉ A ∧ 0 < t - y ∧ 2 * (t - y) < t := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  exact ⟨h4 y hy hby (by omega) hya, by omega, by omega⟩

/-- **A payer among every five.**  Any five ordered octave elements
contain a paying owner at the second or fourth position: the block
pigeonhole that upgrades one payer per octave to a constant fraction
of the octave population — the ledger telescope''s rate. -/
theorem payer_in_five {A : Set ℕ} {Ns X x₁ x₂ x₃ x₄ x₅ : ℕ}
    (huniv : UniversalOwnership A Ns) (hXNs : Ns ≤ X)
    (h₁ : x₁ ∈ A) (h₂ : x₂ ∈ A) (h₃ : x₃ ∈ A) (h₄ : x₄ ∈ A)
    (h₅ : x₅ ∈ A)
    (hord : x₁ < x₂ ∧ x₂ < x₃ ∧ x₃ < x₄ ∧ x₄ < x₅)
    (hoct : X < x₁ ∧ x₅ ≤ 2 * X) :
    ∃ a t y, (a = x₂ ∨ a = x₄) ∧ OwnsTarget A a t ∧
      y ∈ A ∧ 2 * y > t ∧ y < t ∧ y ≠ a := by
  obtain ⟨t₂, ho₂⟩ := huniv x₂ h₂ (by omega)
  obtain ⟨t₄, ho₄⟩ := huniv x₄ h₄ (by omega)
  by_contra hno
  push_neg at hno
  have hp₂ : ∀ y ∈ A, 2 * y > t₂ → y < t₂ → y = x₂ := by
    intro y hy hby hyt
    exact hno x₂ t₂ y (Or.inl rfl) ho₂ hy hby hyt
  have hp₄ : ∀ y ∈ A, 2 * y > t₄ → y < t₄ → y = x₄ := by
    intro y hy hby hyt
    exact hno x₄ t₄ y (Or.inr rfl) ho₄ hy hby hyt
  exact no_five_zero_payers h₁ h₃ h₅ ho₂ ho₄ hp₂ hp₄ hord hoct

/-- **The ownership forest.**  Universal ownership yields a parent
function: every late element has a canonical completion — smaller,
in `A`, with their sum uniquely fibered.  The chain forest flows to
the base; its cross-tree coherence (carry-compatibility of shared
tails) is the classification''s final object, modeled on the verified
Cantor calculus where the forest is exactly base-3 expansion. -/
theorem ownership_forest {A : Set ℕ} {Ns : ℕ}
    (huniv : UniversalOwnership A Ns) :
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

/-- **The star exclusion law.**  Children of a common parent (the
star of `w`) exclude each other''s shifted differences: for siblings
`a, b` with the scale to test, `a + w - b ∉ A`.  Star differences
shifted by the parent exit `A` — the forest''s first coherence law,
the vocabulary of the final induction (in the Cantor model, stars
are digit-shifted block families and the exclusions land on carry
positions). -/
theorem star_exclusion {A : Set ℕ} {w a b : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hb : b ∈ A) (hbig : 2 * b > a + w) (hlt : b < a + w)
    (hba : b ≠ a) :
    a + w - b ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  exact h4 b hb hbig (by omega) hba

/-- **The parent-double exclusion.**  If a child reaches beyond three
times its parent and their difference stays in `A`, the parent''s
double must leave `A`: the difference tests the target''s moat and
reflects to `2w`.  Parents in reachy use are double-free — exactly
the Cantor dodge (doubles carry digit 2) — and the enemy''s doubling
supply can never live on such parents: the forest and the doubling
interface split `A`. -/
theorem parent_double_exclusion {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hdiff : a - w ∈ A) (hreach : 3 * w < a) :
    2 * w ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  have hw1 : 1 ≤ w := by omega
  have hval : a + w - (a - w) = 2 * w := by omega
  have := h4 (a - w) hdiff (by omega) (by omega) (by omega)
  rwa [hval] at this

/-- **The reach dichotomy.**  Every forest edge with difference in
`A` either stays within the boundary band `(w, 3w]` or excludes the
parent''s double.  The threshold 3 is the moat''s own constant
(`2y > t` at `y = a - w` gives `a > 3w`) — and base-3 blocks sit
exactly on it: `3^k = 2(3^{k-1} + ⋯ + 1) + 1`.  The base of the
digit tower is the order of the problem: order-3 representation
forces ternary strata. -/
theorem child_reach_dichotomy {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w)) (hdiff : a - w ∈ A) :
    a ≤ 3 * w ∨ 2 * w ∉ A := by
  rcases Nat.lt_or_ge (3 * w) a with h | h
  · exact Or.inr (parent_double_exclusion hown hdiff h)
  · exact Or.inl h

/-- **The edge exclusion law**, unified.  Along any forest edge away
from the exact points `a = 2w, 3w`: the difference and the parent''s
double cannot both lie in `A`.  Reachy edges exclude the double
(`parent_double_exclusion`); boundary edges test the double in the
moat and exclude the difference.  One law, both regimes — in the
ternary model both sides exit by digit-2, on the nose. -/
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

/-- **The edge tax.**  Every forest edge away from the exact points
pays a co-`A` point: the parent''s double (split edges — shared
across the star, paid once) or the edge''s own difference (non-split
edges — distinct per child).  No edge is free. -/
theorem edge_tax {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (hne2 : a ≠ 2 * w) (hne3 : a ≠ 3 * w) :
    2 * w ∉ A ∨ a - w ∉ A := by
  by_contra h
  push_neg at h
  exact edge_exclusion_law hown hne2 hne3 ⟨h.2, h.1⟩

/-- **Split differences inject.**  Distinct split children of one
parent have distinct differences, all in `A`: the star''s split part
embeds into `A` below the children — each difference is itself an
element with its own chain.  The expansion recursion lives here:
`a = (a - w) + w` with `a - w ∈ A` dominant, and the tower unfolds
along split chains. -/
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

/-- **Block domination.**  A reachy forest edge''s block (the
difference) exceeds twice the parent — twice everything below it in
the chain.  Chains of reachy edges therefore produce DOMINATED
expansions: each block more than double the remaining sum, the
classical characterization of canonical (greedy, unique) digit
expansions.  The chain differences are the digits; reach is
canonicity. -/
theorem block_domination {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w)) (hreach : 3 * w < a) :
    2 * w < a - w := by
  have h1 : a < a + w := hown.1
  omega

/-- **Covering permits no doubling gaps.**  Every window `(x, 2x+N₀]`
contains an element: the pair for `2x + N₀ + 1` needs a big part.
The coverage side of the alphabet pincer — scale ratios are bounded,
while reach bounds them below: the tower''s ratio is squeezed to the
ternary value from both sides. -/
theorem covering_gap_bound {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀) :
    ∀ x, ∃ a ∈ A, x < a ∧ a ≤ 2 * x + N₀ + 1 := by
  intro x
  obtain ⟨p, hp, q, hq, hpq⟩ := hcov (2 * x + N₀ + 1) (by omega)
  rcases Nat.lt_or_ge x p with h | h
  · exact ⟨p, hp, h, by omega⟩
  · refine ⟨q, hq, by omega, by omega⟩

/-- **The shared-block parent sieve.**  When one block `b` serves two
owners through different parents, the parents sieve each other:
`2w - w' ∉ A`.  Each block''s parent set is Sidon-like under the
doubled-difference sieve — the first concrete law of alphabet
coherence: blocks can be shared only by sieve-compatible parents,
and in the ternary model the sieve values are exactly carry
positions. -/
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

/-- **The master block sieve.**  In block coordinates, every owner
excludes every same-window element: `b + 2w - b' - w' ∉ A`.  All
coherence laws are specializations (equal blocks: the parent sieve;
equal parents: the star law).  Offsets between in-use blocks are
sieved by every parent pair below them — the offset lattice is
forced into the sieve''s sparse complement: coherence. -/
theorem cross_block_exclusion {A : Set ℕ} {b w b' w' : ℕ}
    (hown : OwnsTarget A (b + w) (b + w + w))
    (ha' : b' + w' ∈ A)
    (hbig : 2 * (b' + w') > b + w + w)
    (hlt : b' + w' < b + w + w) (hne : b' + w' ≠ b + w) :
    b + 2 * w - b' - w' ∉ A := by
  have h := star_exclusion (w := w) (a := b + w) hown ha' hbig hlt hne
  have hval : b + w + w - (b' + w') = b + 2 * w - b' - w' := by omega
  rwa [hval] at h

/-- **The boundary exclusion.**  Boundary-band edges are sieved by
the parent''s triple: if `3w ∈ A`, the band value `a - 2w` exits.
The band `(w, 3w]` — where reach fails — carries its own exclusion
family through the tri-multiples: no hiding place is law-free. -/
theorem boundary_exclusion {A : Set ℕ} {w a : ℕ}
    (hown : OwnsTarget A a (a + w))
    (h3w : 3 * w ∈ A) (hlow : 2 * w < a) (hhigh : a < 5 * w)
    (hne : a ≠ 3 * w) :
    a - 2 * w ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  have h := h4 (3 * w) h3w (by omega) (by omega) (by omega)
  have hval : a + w - 3 * w = a - 2 * w := by omega
  rwa [hval] at h

/-- **Two-marker near-rigidity.**  A failing double under a
two-marker window is rigid up to fibers through the lower marker:
every representation is the diagonal or passes through `b₁`.  The
exceptions route through OUR markers — and marker positions are
ours to choose, so the dodge-selection machinery upgrades
near-rigidity to rigidity along dodging deletions.  The multi-marker
rigidity derivation''s base case. -/
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

/-- **The dodge primitive.**  An unbounded set escapes any finite
exclusion set from any starting point: pick beyond the exclusions''
maximum.  Feeds the geometric marker builders: deletions can always
be chosen dodging the canonical owners'' exception positions
(`2b - A`-sets), upgrading near-rigidity to rigidity along the
chosen deletion — the rails-to-rigidity chain''s selection step. -/
theorem unbounded_dodge {A : Set ℕ}
    (hunb : ∀ X, ∃ a ∈ A, X ≤ a) (E : Finset ℕ) :
    ∀ X, ∃ a ∈ A, X ≤ a ∧ a ∉ E := by
  intro X
  obtain ⟨a, ha, hX⟩ := hunb (max X (E.sup id + 1))
  refine ⟨a, ha, le_trans (le_max_left _ _) hX, ?_⟩
  intro hmem
  have h1 : a ≤ E.sup id := Finset.le_sup (f := id) hmem
  have h2 : E.sup id + 1 ≤ a := le_trans (le_max_right _ _) hX
  omega

/-- **The failing-double fiber bound.**  Every proper fiber of a
failing double routes through the deletion: the small sides of its
representations inject into `B`-hits below it.  Doubles failing
under a `K`-marker deletion have at most `2K` fiber elements —
quantitative near-rigidity: sparse deletions leave failing doubles
nearly rigid, and the dodge selection removes the remainder. -/
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

/-- **Richness is reflection.**  If every window element completes to
a fixed double (the dodge-failure at one center), the center carries
symmetric pairs — it is doubling-NON-rigid, and the window is
one-sidedly mirror-symmetric about it.  The richness horn of the
final dichotomy produces mirror structure: near-periodic windows,
the verified mirror bridge''s territory.  Both horns now end at
verified kill machinery — dodge → rigidity → digits → carry kill;
richness → mirrors → reflection-level kill. -/
theorem richness_gives_reflection {A : Set ℕ} {b X : ℕ}
    (hrich : ∀ a ∈ A, X ≤ a → a < 2 * b → 2 * b - a ∈ A) :
    ∀ a ∈ A, X ≤ a → a < 2 * b → a ≠ b →
      ∃ p ∈ A, ∃ q ∈ A, p + q = 2 * b ∧ p ≠ b := by
  intro a ha hXa hab hane
  refine ⟨a, ha, 2 * b - a, hrich a ha hXa hab, by omega, hane⟩

/-- **The exact failure characterization.**  A target fails under a
deletion IF AND ONLY IF one of its hubs lies inside the deletion:
hubs inside `B` kill every representation; conversely the part of
`B` below a failing target IS such a hub.  `hfail` is precisely the
statement that every infinite deletion contains hubs cofinally — the
problem becomes hypergraph unavoidability, exactly. -/
theorem fails_iff_hub_subset {A B : Set ℕ} {n : ℕ}
    [DecidablePred (· ∈ B)] :
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B) ↔
    ∃ H : Finset ℕ, IsRepHub A n H ∧ ∀ h ∈ H, h ∈ B := by
  constructor
  · intro hdead
    refine ⟨(Finset.range (n + 1)).filter (· ∈ B),
      failing_hub_subset_deletion hdead, ?_⟩
    intro h hh
    exact (Finset.mem_filter.1 hh).2
  · rintro ⟨H, hhub, hHB⟩ x hx y hy z hz hsum
    rcases hhub x hx y hy z hz hsum with h | h | h
    · exact Or.inl (hHB x h)
    · exact Or.inr (Or.inl (hHB y h))
    · exact Or.inr (Or.inr (hHB z h))

/-- **DODGE OR TRAP.**  CAUTION (2026-07-25 audit): this conclusion
is TRIVIALLY SATISFIABLE without `hfail` — see
`trap_conclusion_trivial` (junk envelope `A ∩ [0, N0]`).  Kept for
the historical record; the SOUND replacements are the flood
theorems (`rep_flood_of_hfail` etc.), whose stalled envelope
carries the freeness certificate this statement lacks. -/
theorem dodge_or_trap {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ A) ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a := by
  classical
  by_contra hnotrap
  push_neg at hnotrap
  have hpick : ∀ (F : Finset ℕ) (X : ℕ), ∃ a, a ∈ A ∧ X ≤ a ∧
      ((∀ h ∈ F, h ∈ A) →
        ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧ a ∈ H ∧
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
  have hinv : ∀ j, ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
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
  push_neg at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N0
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push_neg at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hdec : DecidablePred (· ∈ B) := fun _ => Classical.propDecidable _
  have hhub := failing_hub_subset_deletion (B := B) hdead
  set H : Finset ℕ := (Finset.range (n + 1)).filter (· ∈ B) with hH
  have hHne : H.Nonempty := hub_nonempty_of_covering h0 hcov hnN hhub
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

theorem dodge_or_trap_pool {P A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hPA : P ⊆ A) (hunb : ∀ X, ∃ p ∈ P, X ≤ p)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ P) ∧ ∃ X, ∀ a ∈ P, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a := by
  classical
  by_contra hnotrap
  push_neg at hnotrap
  have hpick : ∀ (F : Finset ℕ) (X : ℕ), ∃ a, a ∈ P ∧ X ≤ a ∧
      ((∀ h ∈ F, h ∈ P) →
        ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧ a ∈ H ∧
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
  have hinv : ∀ j, ¬∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
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
  push_neg at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N0
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push_neg at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hdec : DecidablePred (· ∈ B) := fun _ => Classical.propDecidable _
  have hhub := failing_hub_subset_deletion (B := B) hdead
  set H : Finset ℕ := (Finset.range (n + 1)).filter (· ∈ B) with hH
  have hHne : H.Nonempty := hub_nonempty_of_covering h0 hcov hnN hhub
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


/-- Level extractor.  CAUTION (2026-07-25 audit): junk-satisfiable
without `hfail` via the interval escape (`tower_branch_trivial`);
see the flood theorems for the sound form. -/
theorem trap_level {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ Y, ∃ (F : Finset ℕ) (X : ℕ),
      (∀ h ∈ F, h ∈ A ∧ Y ≤ h) ∧ Y ≤ X ∧
      ∀ a ∈ A, X ≤ a → ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ a ∈ H ∧ ∀ h ∈ H, h ∈ F ∨ h = a := by
  intro Y
  have hPA : {a | a ∈ A ∧ Y ≤ a} ⊆ A := fun a ha => ha.1
  have hunb : ∀ X, ∃ p ∈ {a | a ∈ A ∧ Y ≤ a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X Y)
    exact ⟨a, ⟨ha, le_trans (le_max_right _ _) hXa⟩,
      le_trans (le_max_left _ _) hXa⟩
  obtain ⟨F, hFP, X, htrap⟩ :=
    dodge_or_trap_pool (P := {a | a ∈ A ∧ Y ≤ a}) h0 hcov hPA hunb hfail
  refine ⟨F, max X Y, fun h hh => ⟨(hFP h hh).1, (hFP h hh).2⟩,
    le_max_right _ _, ?_⟩
  intro a ha hXa
  exact htrap a ⟨ha, le_trans (le_max_right _ _) hXa⟩
    (le_trans (le_max_left _ _) hXa)

/-- **THE TRAP TOWER.**  CAUTION (2026-07-25 audit): the tower
statement is junk-satisfiable without `hfail` (`tower_branch_trivial`
— every representation of `n ≥ 3Y` carries a part `≥ Y`).  Kept for
the record; content requires hub-cardinality bounds or the freeness
certificate of the flood theorems. -/
theorem trap_tower {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ) (X : ℕ → ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i ≤ X i) ∧
      (∀ i, X i < Y (i + 1)) ∧
      (∀ i, ∀ h ∈ F i, h < Y (i + 1)) ∧
      (∀ i, ∀ a ∈ A, X i ≤ a → ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ a ∈ H ∧ ∀ h ∈ H, h ∈ F i ∨ h = a) := by
  classical
  choose Ft Xt hFt hXt htrapt using trap_level h0 hcov hfail
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

/-- **THE GRAND DICHOTOMY.**  From the trap tower, every
counterexample lives in one of two worlds: THE FLOOD — some finite
envelope `F` with cofinally many elements necessary in their own
minimal repful hubs inside `F ∪ {a}` (universal-ownership supply,
derived) — or THE TOWER TEAMS — at every level a repful minimal
nonempty hub inside that level''s finite trap, with targets marching
to infinity (fixed-finite-team supply at all scales, derived).  The
two long-assumed configurations of the campaign are now exhaustive
and unconditional.  CAUTION (2026-07-25 audit): the TOWER branch of
this disjunction is junk-satisfiable (`tower_branch_trivial`), so
this dichotomy proves nothing when the flood branch fails; the
sound successor is `stable_core_trichotomy` and, stronger, the
unconditional `canonical_flood_pos_of_hfail`. -/
theorem grand_dichotomy {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ F : Finset ℕ, ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a) ∨
    (∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i < Y (i + 1)) ∧
      ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
        (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepHub A n H ∧
        ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) := by
  classical
  obtain ⟨Y, F, X, hFA, hYX, hXY, hFY, htrap⟩ :=
    trap_tower h0 hcov hfail
  by_cases hflood : ∃ i, ∀ M, ∃ a, a ∈ A ∧ M ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F i ∨ h = a
  · left
    obtain ⟨i, hi⟩ := hflood
    exact ⟨F i, hi⟩
  · right
    push_neg at hflood
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
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
      have hH'ne : H'.Nonempty :=
        hub_nonempty_of_covering h0 hcov hnN hH'hub
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
        minimal_hub_necessity hH'hub hH'min h₀ hh₀
      have hh₀n : h₀ ≤ n := by
        rcases hhit with h' | h' | h' <;> omega
      have hh₀Y : Y i ≤ h₀ := (hFA i h₀ (hH'F h₀ hh₀)).2
      exact ⟨n, hnN, by omega, H', hH'F, ⟨h₀, hh₀⟩, hH'hub, hH'min⟩

/-- **Team-branch collapse.**  Pigeonholing hub cardinalities across
tower levels: the tower teams contain cofinal minimal hubs of one
fixed size `c ≥ 1`, all elements positive.  Positive singletons
(`c = 1`) feed the verified stream kill; the surviving branch starts
at `c = 2` — cofinal destroyer teams of one fixed size, the
pipeline''s entry, derived. -/
theorem tower_teams_card {A : Set ℕ} {N0 C : ℕ} {Y : ℕ → ℕ}
    {F : ℕ → Finset ℕ}
    (hY1 : 1 ≤ Y 0)
    (hFA : ∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h)
    (hYmono : ∀ i, Y i < Y (i + 1))
    (hCb : ∀ i, (F i).card ≤ C)
    (hteams : ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
      (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepHub A n H ∧
      ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) :
    ∃ c, 1 ≤ c ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ H.Nonempty ∧ IsRepHub A n H ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepHub A n (H \ {h}) := by
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
      (∃ H : Finset ℕ, H.card = c ∧ H.Nonempty ∧ IsRepHub A n H ∧
        (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
        ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) := by
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
      IsRepHub A n H ∧ (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) hP
  refine ⟨c, ?_, hcof⟩
  obtain ⟨n, -, H, hHc, hHne, -⟩ := hcof 0
  have := Finset.card_pos.2 hHne
  omega

/-- **Tower teams start at two.**  The fixed team size cannot be one:
cofinal positive singleton hubs are private triples and die by the
verified stream kill.  Under the interfaces, the tower-team world
has teams of size at least two — the destroyer-team supply at the
pipeline''s doorstep. -/
theorem tower_teams_ge_two {A : Set ℕ} {N0 C : ℕ} {Y : ℕ → ℕ}
    {F : ℕ → Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hY1 : 1 ≤ Y 0)
    (hFA : ∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h)
    (hYmono : ∀ i, Y i < Y (i + 1))
    (hCb : ∀ i, (F i).card ≤ C)
    (hteams : ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
      (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepHub A n H ∧
      ∀ h ∈ H, ¬IsRepHub A n (H \ {h})) :
    ∃ c, 2 ≤ c ∧ ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepHub A n H ∧
      (∀ h ∈ H, h ∈ A ∧ 0 < h) ∧
      ∀ h ∈ H, ¬IsRepHub A n (H \ {h}) := by
  obtain ⟨c, hc1, hcof⟩ :=
    tower_teams_card (N0 := N0) hY1 hFA hYmono hCb hteams
  rcases Nat.lt_or_ge c 2 with hc2 | hc2
  · exfalso
    have hc1' : c = 1 := by omega
    subst hc1'
    refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨n, hnN, H, hHc, hHne, hhub, hpos, hmin⟩ := hcof N
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hHc
    refine ⟨n, hnN, a, ?_, hhub⟩
    exact (hpos a (Finset.mem_singleton_self a)).2
  · refine ⟨c, hc2, fun N => ?_⟩
    obtain ⟨n, hnN, H, hHc, hHne, hhub, hpos, hmin⟩ := hcof N
    exact ⟨n, hnN, H, hHc, hhub, hpos, hmin⟩

/-- **The flood''s canonical form.**  Subset-pigeonholing the flood
inside its fixed finite envelope: one exact core `S* ⊆ F` recurs, so
cofinally many elements carry minimal hubs EXACTLY `S* ∪ {a}` — the
half-fixed configuration in canonical form.  With the stream kill,
the empty core dies: under the interfaces the flood has a nonempty
fixed core plus one rotating necessary guardian.  Constant-sized
everywhere; no log anywhere. -/
theorem flood_canonical {A : Set ℕ} {N0 : ℕ} {F : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (hflood : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
        ∀ h ∈ H, h ∈ F ∨ h = a) :
    ∃ S : Finset ℕ, (∀ h ∈ S, h ∈ F) ∧ S.Nonempty ∧
      ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
        ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          H = insert a S := by
  classical
  -- pigeonhole the F-part of the flood hubs
  have hQ : ∀ X, ∃ x, X ≤ x ∧ ∃ S, S ⊆ F ∧
      (∃ a, a ∈ A ∧ x = a ∧ a ∉ F ∧
        ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
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
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
        H = insert a S)
    (F := F) (by
      intro N
      obtain ⟨x, hx, S, hSF, hdata⟩ := hQ N
      exact ⟨x, hx, S, hSF, hdata⟩)
  -- kill the empty core by the stream kill
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · exfalso
    subst hSe
    refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
    intro N
    obtain ⟨x, hxN, a, ha, heq, haF, n, hnN, H, hhub, hmin, haH, hHeq⟩ :=
      hrec (max N 1)
    subst heq
    have hHa : H = {x} := by simpa using hHeq
    rw [hHa] at hhub hmin haH
    obtain ⟨x', hx', y', hy', z', hz', hsum, hhit, -⟩ :=
      minimal_hub_necessity hhub hmin x haH
    have han : x ≤ n := by
      rcases hhit with h' | h' | h' <;> omega
    exact ⟨n, by omega, x, by omega, hhub⟩
  · refine ⟨S, fun h hh => hSF hh, hSne, fun X => ?_⟩
    obtain ⟨x, hxN, a, ha, heq, haF, n, hnN, H, hhub, hmin, haH, hHeq⟩ :=
      hrec X
    subst heq
    have haS : x ∉ S := fun haS => haF (hSF haS)
    exact ⟨x, ha, hxN, haS, n, hnN, H, hhub, hmin, hHeq⟩

/-- **The pair shadow.**  With `0 ∈ A` and `0 ∉ H`, a rep hub for `n`
is in particular a transversal of the order-2 representations: the
representation `(x, n − x, 0)` must be hit, and `0` is not in the
hub, so every pair representation routes through the hub. -/
theorem pair_shadow_of_hub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (h0 : 0 ∈ A) (hhub : IsRepHub A n H) (h0H : 0 ∉ H) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n → x ∈ H ∨ y ∈ H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy 0 h0 (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h h0H

/-- **The pair-count collapse.**  A 0-free hub bounds the order-2
representation count of its target: pair-rep components live in
`H ∪ (n − H)`, so there are at most `2·|H|` of them.  Constant-size
hubs force essentially-Sidon targets. -/
theorem pair_count_of_hub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hhub : IsRepHub A n H) (h0H : 0 ∉ H) :
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
    rcases pair_shadow_of_hub h0 hhub h0H x hxA (n - x) hnxA
        (by omega) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _
        (Finset.mem_image.2 ⟨n - x, h, by omega⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le H (H.image (fun h => n - h))
  have h3 : (H.image (fun h => n - h)).card ≤ H.card :=
    Finset.card_image_le
  omega

/-- **The flood''s order-2 shadow.**  In the canonical flood with a
0-free core, cofinally many targets have ALL pair representations
routed through the fixed core plus the rotating guardian, hence
order-2 representation count at most `2·(|S| + 1)`.  The flood is
an essentially-Sidon stream with fixed routing. -/
theorem flood_pair_shadow {A : Set ℕ} {N0 : ℕ} {S : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (h0S : 0 ∉ S)
    (hcanon : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
  have hb := pair_count_of_hub h0 hhub h0H
  exact ⟨a, ha, le_trans (le_max_left _ _) hXa, by omega, n, hnN,
    pair_shadow_of_hub h0 hhub h0H, by omega⟩

/-- **The flood routing dichotomy.**  Canonical flood targets route
all pair representations through `S ∪ {a}`.  Cofinally, one of two
regimes recurs: a FIXED CORE COREP — one recurring `s ∈ S` with
`n − s ∈ A` at cofinally many canonical targets — or the VANISHING
GUARDIAN PAIR-HUB — cofinally many canonical targets whose EVERY
pair representation uses the rotating guardian itself, which is then
a singleton hub for its target''s entire order-2 life. -/
theorem flood_routing_dichotomy {A : Set ℕ} {N0 : ℕ} {S : Finset ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0) (h0S : 0 ∉ S)
    (hcanon : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S) :
    (∃ s ∈ S, ∀ X, ∃ n, X ≤ n ∧ N0 ≤ n ∧ (∃ w ∈ A, s + w = n) ∧
      ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        H = insert a S) ∨
    (∀ X, ∃ n, X ≤ n ∧ N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
      (∃ w ∈ A, a + w = n) ∧
      (∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a) ∧
      ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S) := by
  classical
  set Q : ℕ → Finset ℕ → Prop := fun n T =>
    (N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
      minimal_hub_necessity hhub hmin a haH
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
        ∃ H : Finset ℕ, IsRepHub A n₀ H ∧
          (∀ h ∈ H, ¬IsRepHub A n₀ (H \ {h})) ∧ H = insert a S) ∧
        T₀ = S.filter (fun s' => ∃ w ∈ A, s' + w = n₀) := hQT₀
    have hsS : s ∈ S := by
      have := hinst₀.2 ▸ hsT₀
      exact (Finset.mem_filter.1 this).1
    refine ⟨s, hsS, fun X => ?_⟩
    obtain ⟨n, hn, T, hQT, hsT⟩ := hper X
    have hinst : (N0 ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S) ∧
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
        ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S) ∧
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
    have hshadow := pair_shadow_of_hub h0 hhub h0H
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

/-- **VACUITY CERTIFICATE for the plain trap.**  The conclusion of
`dodge_or_trap` is satisfiable WITHOUT `hfail`: the junk envelope
`F := A ∩ [0, N0]` hubs the target `N0` outright (every part of
every representation of `N0` lies under it), and then every element
`a` completes `F ∪ {a}` trivially.  The bare trap therefore carries
no information about a counterexample; content requires the
minimality-and-membership guarded flood form, or explicit hub
cardinality bounds.  Recorded so no future work leans on it. -/
theorem trap_conclusion_trivial {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) :
    ∃ F : Finset ℕ, (∀ h ∈ F, h ∈ A) ∧ ∃ X, ∀ a ∈ A, X ≤ a →
      ∃ n, N0 ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧ a ∈ H ∧
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

/-- **VACUITY CERTIFICATE for the un-carded tower branch.**  The
tower-teams disjunct of `grand_dichotomy` — floors, marching
targets, minimal nonempty hubs and all — is satisfiable WITHOUT
`hfail`: at floor `Y`, any target `n ≥ 3·Y + N0` has every
representation carrying a part in `[Y, n]` (three parts below `Y`
cannot reach the sum), so `A ∩ [Y, n]` is a hub and minimalizes
inside itself.  Without a hub-cardinality bound the tower branch
says nothing about the enemy: the constant-vs-log wall IS the
missing cardinality bound. -/
theorem tower_branch_trivial {A : Set ℕ} {N0 : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N0) :
    ∃ (Y : ℕ → ℕ) (F : ℕ → Finset ℕ),
      (∀ i, ∀ h ∈ F i, h ∈ A ∧ Y i ≤ h) ∧
      (∀ i, Y i < Y (i + 1)) ∧
      ∀ i, ∃ n, N0 ≤ n ∧ Y i ≤ n ∧ ∃ H : Finset ℕ,
        (∀ h ∈ H, h ∈ F i) ∧ H.Nonempty ∧ IsRepHub A n H ∧
        ∀ h ∈ H, ¬IsRepHub A n (H \ {h}) := by
  classical
  refine ⟨fun i => i + 1,
    fun i => (Finset.range (3 * (i + 1) + N0 + 1)).filter
      (fun h => h ∈ A ∧ i + 1 ≤ h), ?_,
    fun i => by show i + 1 < i + 1 + 1; omega, ?_⟩
  · intro i h hh
    exact (Finset.mem_filter.1 hh).2
  · intro i
    have hbig : IsRepHub A (3 * (i + 1) + N0)
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
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hbig
    have hH'ne : H'.Nonempty := hub_nonempty_of_covering h0 hcov
      (by omega) hH'hub
    exact ⟨3 * (i + 1) + N0, by omega,
      by show i + 1 ≤ 3 * (i + 1) + N0; omega, H',
      fun h hh => hH'sub hh, hH'ne, hH'hub, hH'min⟩

/-- **THE FORCED PAIR SHADOW.**  The sound content of the trap: what
a counterexample REALLY yields against any chosen 0-free infinite
deletion `B` is cofinally many targets whose EVERY order-2
representation routes through `B` — the representation
`(x, n − x, 0)` must die, and `0 ∉ B`. -/
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
  push_neg at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb N
  refine ⟨n, hnN, ?_⟩
  intro x hx y hy hxy
  by_contra hall
  push_neg at hall
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

/-- **THE LOG WALL, from the sound side.**  A counterexample admits
a geometric deletion `b 0 < b 1 < ⋯` inside `A` with `3^j ≤ b j`,
against which cofinally many targets have their ENTIRE order-2 life
routed through the deletion; at those targets the order-2
representation count is at most `2·(log₃ n + 1)`.  The enemy is
forced to be log-Sidon cofinally — no interfaces beyond covering,
and no vacuity: this is the true quantitative content the trap was
after. -/
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
        (Nat.pow_le_iff_le_log (by norm_num) (by omega)).1 hjn
      exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), hj⟩
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.range (Nat.log 3 n + 1)).image b).card ≤
        Nat.log 3 n + 1 :=
      le_trans Finset.card_image_le (by simp)
    omega
  have hcount := pair_count_of_shadow (B := Set.range b) hshadow
  omega

/-- **THE SOUND FLOOD.**  When the stable-core canonical shape has
exactly one rotating slot (`c = |S| + 1`), the flood hypothesis of
`flood_canonical` holds verbatim with envelope `S` — derived from
the V10 bounded-hub stream, immune to the trap vacuities: hubs here
have EXACT card `c`, minimality, and an arbitrarily high rotator. -/
theorem flood_of_singleton_rotator {A : Set ℕ} {N₀ : ℕ}
    {S : Finset ℕ} {c : ℕ}
    (hsplit : ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      H.card = c ∧ IsRepHub A n H ∧
      (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h)
    (hc : c = S.card + 1) :
    ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S ∧
      ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S := by
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
    minimal_hub_necessity hhub hmin a haH
  have haA : a ∈ A := by
    rcases hhit with h' | h' | h'
    · exact h' ▸ hx
    · exact h' ▸ hy
    · exact h' ▸ hz
  exact ⟨a, haA, by omega, haS, n, hn, H, hhub, hmin, hHeq⟩

/-- **THE SOUND TRICHOTOMY.**  The V10 stable-core shape splits a
counterexample three ways by its rotating-slot count `c − |S|`:

* TIGHT TEAM — `c = |S|`: one fixed finite team of size `≥ 2` hubs
  cofinally many targets;
* THE FLOOD — `c = |S| + 1`: one rotating guardian over the stable
  core, which collapses (`flood_canonical`) to the canonical exact
  form: a NONEMPTY fixed core `S*` with cofinal minimal hubs
  EXACTLY `S* ∪ {a}`, plus the stream kill on the empty core;
* MULTI-ROTATION — `c ≥ |S| + 2`: cofinal minimal hubs of exact
  card `c` carrying at least two arbitrarily high members over the
  fixed core.

This replaces the vacuous trap dichotomy: every branch is
card-exact and minimality-guarded, inherited from the V10
bounded-hub stream.  No junk instantiation reaches any of them. -/
theorem stable_core_trichotomy {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, 2 ≤ S.card ∧
      ∀ N, ∃ n, N ≤ n ∧ IsRepHub A n S) ∨
    (∃ S' : Finset ℕ, S'.Nonempty ∧
      ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧ a ∉ S' ∧
        ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          H = insert a S') ∨
    (∃ S : Finset ℕ, ∃ c, S.card + 2 ≤ c ∧
      ∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        H.card = c ∧ IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        S ⊆ H ∧ ∀ h ∈ H, h ∉ S → W < h) := by
  obtain ⟨K, S, c, hcK, hc2, hSc, hsplit, hteam⟩ :=
    hub_endgame_of_hfail h0 hcov hdb hanchor hfail
  rcases Nat.lt_or_ge c (S.card + 1) with hlt | hge
  · left
    have hceq : c = S.card := by omega
    exact ⟨S, by omega, hteam hceq⟩
  · rcases Nat.lt_or_ge c (S.card + 2) with hlt2 | hge2
    · right
      left
      have hceq : c = S.card + 1 := by omega
      have hflood : ∀ X, ∃ a, a ∈ A ∧ X ≤ a ∧
          ∃ n, N₀ ≤ n ∧ ∃ H : Finset ℕ, IsRepHub A n H ∧
            (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ a ∈ H ∧
            ∀ h ∈ H, h ∈ S ∨ h = a := by
        intro X
        obtain ⟨a, haA, hXa, haS, n, hn, H, hhub, hmin, hHeq⟩ :=
          flood_of_singleton_rotator (N₀ := N₀) hsplit hceq X
        refine ⟨a, haA, hXa, n, hn, H, hhub, hmin, ?_, ?_⟩
        · rw [hHeq]
          exact Finset.mem_insert_self a S
        · intro h hh
          rw [hHeq] at hh
          rcases Finset.mem_insert.1 hh with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
      obtain ⟨S', hS'S, hS'ne, hcanon⟩ :=
        flood_canonical h0 hcov hanchor hfail hflood
      exact ⟨S', hS'ne, hcanon⟩
    · right
      right
      exact ⟨S, c, hge2, hsplit⟩

/-- Pair-hub counting: order-2 components live in `H ∪ (n − H)`,
with no zero caveat — the pair hub IS the order-2 transversal. -/
theorem pair_count_of_pairHub {A : Set ℕ} [DecidablePred (· ∈ A)]
    {n : ℕ} {H : Finset ℕ} (hhub : IsPairHub A n H) :
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

/-- **CONSTANT SIDON FROM MINIMALITY ALONE.**  Every ℵ₀-minimal
order-2 covering set carries a cofinal stream of targets whose
order-2 representation count is bounded by ONE constant — twice the
canonical pair-hub card.  The minimality half of Erdős 881 already
forces any minimal basis to be essentially Sidon along a stream,
with no counterexample hypothesis anywhere. -/
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
  have := pair_count_of_pairHub hhub
  exact ⟨n, hn, by omega⟩

/-- **The translate bridge.**  An order-3 rep hub at `n` is an
order-2 PAIR hub at every basis translate `n − w`, `w ∈ A ∖ H`,
`w ≤ n`: constant-size order-3 protection makes entire translate
fans essentially Sidon (`pair_count_of_pairHub` applies at each). -/
theorem pairHub_of_translate {A : Set ℕ} {n w : ℕ} {H : Finset ℕ}
    (hhub : IsRepHub A n H) (hwA : w ∈ A) (hwH : w ∉ H)
    (hwn : w ≤ n) :
    IsPairHub A (n - w) H := by
  intro x hx y hy hxy
  rcases hhub x hx y hy w hwA (by omega) with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hwH

/-- **THE FAN BLOWUP.**  A hub target has a translate BY A HUB
ELEMENT with enormous order-2 multiplicity: every basis element
`w ≤ n − N₀` outside `H` routes the pair life of `n − w` through
`H`, and pigeonholing those routes over the `|H|` members hands one
member `h` at least `|A∖H ∩ [0, n−N₀]| / |H|` distinct pair
representations of `n − h`.  Sidon on the fan, blowup on the hub
translate — both forced by one hub. -/
theorem hub_fan_blowup {A : Set ℕ} {N₀ n : ℕ} {H : Finset ℕ}
    [DecidablePred (· ∈ A)]
    (hcov : PairCovers A N₀) (hhub : IsRepHub A n H)
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
`|A ∩ [0,n]|² ≥ n + 1 − N₀`.  Feeds the fan blowup: hub targets
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
avoiding `P`.  Up-monotone in `P`-complement: the dodge invariant. -/
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

/-- **THE PAIR FLOOD, UNCONDITIONAL.**  The sound trap, found: a
counterexample yields ONE finite pair-free envelope `P` and a
threshold beyond which EVERY basis element `b` personally
pair-guards a target `m ≥ b`: every order-2 representation of `m`
routes through `P ∪ {b}`.

Why this cannot be junk: `P ∪ {b}` has constant cardinality, and a
target all of whose pair representations pass through a
constant-size set is `r₂`-bounded — for `A = ℕ` (or any rep-rich
set) no such target exists at all.  Why it is forced: pair-hub-ness
is up-monotone, so the transversal-free finite sets form a tree the
counterexample must make well-founded — if the pair dodge never
stalled, its infinite deletion `B` would leave every late target a
pair representation avoiding all of `B` (parts below the target
only meet picks below the target, which sit inside the stalled
prefix), and `(x, y, 0)` would 3-represent every late target in
`A ∖ B`, refuting `hfail`.  No stable-core detour, no interfaces
beyond covering and `0 ∈ A`: THE FLOOD IS UNCONDITIONAL AT ORDER 2. -/
theorem pair_flood_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = m →
          x ∈ insert b P ∨ y ∈ insert b P := by
  classical
  by_contra hno
  push_neg at hno
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

/-- Every pair hub contains a minimal pair hub. -/
theorem exists_minimal_pairHub {A : Set ℕ} {n : ℕ} {H : Finset ℕ}
    (hhub : IsPairHub A n H) :
    ∃ H' ⊆ H, IsPairHub A n H' ∧
      ∀ h ∈ H', ¬IsPairHub A n (H' \ {h}) := by
  classical
  revert hhub
  induction H using Finset.strongInduction with
  | _ H ih =>
    intro hhub
    by_cases hmin : ∀ h ∈ H, ¬IsPairHub A n (H \ {h})
    · exact ⟨H, Finset.Subset.refl H, hhub, hmin⟩
    · push_neg at hmin
      obtain ⟨h, hhH, hsub⟩ := hmin
      have hss : H \ {h} ⊂ H :=
        Finset.sdiff_ssubset (Finset.singleton_subset_iff.2 hhH)
          (Finset.singleton_nonempty h)
      obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := ih (H \ {h}) hss hsub
      exact ⟨H', Finset.Subset.trans hH'sub Finset.sdiff_subset,
        hH'hub, hH'min⟩

/-- **THE PAIR FLOOD, CANONICAL.**  Pigeonholing the unconditional
pair flood inside its free envelope: one exact core `S* ⊆ P` recurs
— cofinally many basis elements `b` carry MINIMAL pair hubs EXACTLY
`S* ∪ {b}` at targets `m ≥ b`.  The rotator `b` is always necessary
(a hub inside the free `P` alone would contradict freeness), so the
counterexample''s order-2 protection is one fixed finite core plus
one rotating personal guardian, exactly, cofinally, r₂-bounded. -/
theorem pair_flood_canonical {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P S : Finset ℕ, S ⊆ P ∧ PairFree A N₀ P ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsPairHub A m (insert b S) ∧
          ∀ h ∈ insert b S,
            ¬IsPairHub A m (insert b S \ {h}) := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_flood_of_hfail h0 hcov hfail
  have hQ : ∀ N, ∃ x, N ≤ x ∧ ∃ S, S ⊆ P ∧
      (x ∈ A ∧ x ∉ S ∧ ∃ m, N₀ ≤ m ∧ x ≤ m ∧
        IsPairHub A m (insert x S) ∧
        ∀ h ∈ insert x S, ¬IsPairHub A m (insert x S \ {h})) := by
    intro N
    obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max N X₀)
    obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
      (le_trans (le_max_right _ _) hXb)
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_pairHub hhub
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
      IsPairHub A m (insert x S) ∧
      ∀ h ∈ insert x S, ¬IsPairHub A m (insert x S \ {h}))
    (F := P) hQ
  refine ⟨P, S, hSP, hPfree, fun X => ?_⟩
  obtain ⟨b, hXb, hbA, hbS, hdata⟩ := hrec X
  exact ⟨b, hbA, hXb, hbS, hdata⟩

/-- **CONSTANT SIDON FROM `hfail` ALONE.**  The pair flood''s targets
have all pair components inside `(P ∪ {b}) ∪ (m − (P ∪ {b}))`:
cofinally many targets with `r₂(m) ≤ 2·(|P| + 1)` — one constant.
Together with `constant_sidon_of_minimality`, BOTH rails of the
counterexample force constant-Sidon streams, unconditionally. -/
theorem constant_sidon_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_flood_of_hfail h0 hcov hfail
  refine ⟨2 * (P.card + 1), fun N => ?_⟩
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max N X₀)
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_right _ _) hXb)
  have hcount := pair_count_of_pairHub hhub
  have hcard : (insert b P).card ≤ P.card + 1 := Finset.card_insert_le b P
  exact ⟨m, le_trans (le_trans (le_max_left _ _) hXb) hbm, by omega⟩

/-- **THE PAIR FLOOD, POOL-RELATIVE.**  The pair dodge restricted to
picks from any unbounded pool `P₀ ⊆ A ∖ {0}`: the stalled envelope
`P` consists of POOL elements, and every large POOL element `b`
pair-guards a target `m ≥ b` over `P ∪ {b}`.  The sound descent
tool: rerunning the flood inside its own guardian supply yields
envelopes made of guardians — junk cannot enter a proper pool. -/
theorem pair_flood_pool {A P₀ : Set ℕ} {N₀ : ℕ}
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
  push_neg at hno
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

/-- The rotating guardians of a canonical pair flood with core `S`:
elements carrying a minimal pair hub `S ∪ {b}` at some personal
target `m ≥ b`. -/
def PairFloodGuardians (A : Set ℕ) (N₀ : ℕ) (S : Finset ℕ) : Set ℕ :=
  {b | b ∈ A ∧ b ∉ S ∧ 0 < b ∧ ∃ m, N₀ ≤ m ∧ b ≤ m ∧
    IsPairHub A m (insert b S) ∧
    ∀ h ∈ insert b S, ¬IsPairHub A m (insert b S \ {h})}

/-- **THE GUARDIAN CASCADE, ORDER 2.**  Rerunning the pair flood
inside its own guardian supply: the canonical core `S*` has an
unbounded guardian set `G`, and the pool flood on `G` yields a
SECOND envelope `P′` MADE OF GUARDIANS — every large guardian `b`
pair-guards a second target `m′ ≥ b` whose entire order-2 life
routes through fellow guardians `P′` plus `b` itself.  Every
element of `P′` carries the double structure: its own `S* ∪ {g}`
hub AND membership in the level-two envelope.  Sound self-similar
descent with no vacuity at any level. -/
theorem pair_flood_cascade {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ,
      (∀ X, ∃ b ∈ PairFloodGuardians A N₀ S, X ≤ b) ∧
      ∃ P' : Finset ℕ,
        (∀ h ∈ P', h ∈ PairFloodGuardians A N₀ S) ∧
        PairFree A N₀ P' ∧
        ∃ X', ∀ b ∈ PairFloodGuardians A N₀ S, X' ≤ b →
          ∃ m, N₀ ≤ m ∧ b ≤ m ∧
            ∀ x ∈ A, ∀ y ∈ A, x + y = m →
              x ∈ insert b P' ∨ y ∈ insert b P' := by
  classical
  obtain ⟨P, S, hSP, hPfree, hstream⟩ :=
    pair_flood_canonical h0 hcov hfail
  have hunb : ∀ X, ∃ b ∈ PairFloodGuardians A N₀ S, X ≤ b := by
    intro X
    obtain ⟨b, hbA, hXb, hbS, m, hmN, hbm, hhub, hmin⟩ :=
      hstream (max X 1)
    refine ⟨b, ⟨hbA, hbS, ?_, m, hmN, hbm, hhub, hmin⟩,
      le_trans (le_max_left _ _) hXb⟩
    have := le_trans (le_max_right _ _) hXb
    omega
  have hGA : PairFloodGuardians A N₀ S ⊆ A := fun b hb => hb.1
  have h0G : 0 ∉ PairFloodGuardians A N₀ S := by
    intro h
    have := h.2.2.1
    omega
  obtain ⟨P', hP'G, hP'free, X', hcascade⟩ :=
    pair_flood_pool h0 hcov hGA h0G hunb hfail
  exact ⟨S, hunb, P', hP'G, hP'free, X', hcascade⟩

/-- **Singleton guardians live outside every free set.**  If all
pair representations of some late target use `b`, then every
pair-free set excludes `b`.  Consequence: in an empty-core flood
the cascade envelopes are forced empty — the singleton world is
totally self-isolating (and is exactly the near-Sidon regime that
unique-representation targets realize for free). -/
theorem singleton_pair_guardian_notMem_free {A : Set ℕ}
    {N₀ b m : ℕ} {Q : Finset ℕ}
    (hfree : PairFree A N₀ Q) (hm : N₀ ≤ m)
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = m → x = b ∨ y = b) :
    b ∉ Q := by
  intro hbQ
  obtain ⟨x, hx, y, hy, hxy, hxQ, hyQ⟩ := hfree m hm
  rcases hall x hx y hy hxy with h | h
  · exact hxQ (h ▸ hbQ)
  · exact hyQ (h ▸ hbQ)

/-- Triple-freeness: every late target keeps a 3-representation
avoiding `P`.  The order-3 dodge invariant; junk envelopes are
precisely the non-free sets (any set containing `0` fails freeness
against 0-padded representations it blocks). -/
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

/-- **THE REP FLOOD, UNCONDITIONAL.**  The theorem the campaign''s
assumed configurations were reaching for, with no interface beyond
covering and `0 ∈ A`: a counterexample yields ONE finite rep-free
envelope `P` and a threshold beyond which EVERY basis element `b`
personally guards a target `m ≥ b` at ORDER 3 — every
3-representation of `m` routes through `P ∪ {b}`.  Constant
cardinality; the freeness of `P` is the recorded non-vacuity (junk
envelopes are never free).  Proof: the rep dodge; if it never
stalls, all parts of a late target''s surviving representation lie
below the target and hence inside the stalled prefix''s shadow, so
the built deletion leaves every late target represented, refuting
`hfail` directly. -/
theorem rep_flood_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) := by
  classical
  by_contra hno
  push_neg at hno
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
      rw [IsRepHub] at hnh
      push_neg at hnh
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

/-- The rep flood with minimal hubs: the rotator is always necessary
— the free envelope''s surviving representation can only be hit at
`b`, so `b` sits in every minimalization. -/
theorem rep_flood_minimal_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧ ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ b ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
        (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, fun X => ?_⟩
  obtain ⟨b, hbA, hXb⟩ := pairCovers_unbounded hcov (max X X₀)
  obtain ⟨m, hmN, hbm, hhub⟩ := hflood b hbA
    (le_trans (le_max_right _ _) hXb)
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
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

/-- **THE CANONICAL FLOOD, UNCONDITIONAL.**  The full canonical
configuration, derived end to end: a counterexample has ONE
NONEMPTY fixed core `S*` and cofinally many rotating guardians `b`
whose minimal order-3 hubs are EXACTLY `S* ∪ {b}`.  The envelope
comes from the rep dodge, exactness from the subset pigeonhole,
necessity of `b` from the envelope''s freeness, and the nonempty
core from the private-stream kill.  Interfaces: covering, `0 ∈ A`,
and the anchor supply — nothing else. -/
theorem canonical_flood_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
          (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧
          H = insert b S := by
  classical
  obtain ⟨P, hPfree, hstream⟩ := rep_flood_minimal_of_hfail h0 hcov hfail
  have hflood : ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
        (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
    intro X
    obtain ⟨b, hbA, hXb, m, hmN, hbm, H, hhub, hmin, hbH, hsub⟩ :=
      hstream X
    exact ⟨b, hbA, hXb, m, hmN, H, hhub, hmin, hbH, hsub⟩
  obtain ⟨S, hSP, hSne, hcanon⟩ :=
    flood_canonical h0 hcov hanchor hfail hflood
  exact ⟨S, hSne, hcanon⟩

/-- **THE REP FLOOD, POOL-RELATIVE.**  The rep dodge with picks from
any unbounded pool `P₀ ⊆ A ∖ {0}`: the stalled envelope is MADE OF
POOL ELEMENTS and every large pool element guards a personal
order-3 target over it.  With `P₀ := A ∖ {0}` this puts the
envelope — hence the canonical core — inside the positive part of
`A`, unblocking the routing dichotomy''s zero caveat for free. -/
theorem rep_flood_pool {A P₀ : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hP₀A : P₀ ⊆ A) (h0P₀ : 0 ∉ P₀)
    (hunb : ∀ X, ∃ p ∈ P₀, X ≤ p)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, (∀ h ∈ P, h ∈ P₀) ∧ RepFree A N₀ P ∧
      ∃ X, ∀ b ∈ P₀, X ≤ b →
        ∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) := by
  classical
  by_contra hno
  push_neg at hno
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
      rw [IsRepHub] at hnh
      push_neg at hnh
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

/-- **THE CANONICAL FLOOD WITH POSITIVE CORE.**  Running the rep
dodge in the positive pool puts the envelope — hence the exact
core — inside the positive part of `A`: the zero-in-core sliver is
closed structurally, before any case analysis. -/
theorem canonical_flood_pos_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
          (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧
          H = insert b S := by
  classical
  have hunb : ∀ X, ∃ p ∈ {a | a ∈ A ∧ 0 < a}, X ≤ p := by
    intro X
    obtain ⟨a, ha, hXa⟩ := pairCovers_unbounded hcov (max X 1)
    exact ⟨a, ⟨ha, by
      have := le_trans (le_max_right _ _) hXa
      omega⟩, le_trans (le_max_left _ _) hXa⟩
  obtain ⟨P, hPpos, hPfree, X₀, hstall⟩ :=
    rep_flood_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
      (fun a ha => ha.1) (fun h => by have := h.2; omega) hunb hfail
  have hflood : ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧
      ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
        (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ b ∈ H ∧
        ∀ h ∈ H, h ∈ P ∨ h = b := by
    intro X
    obtain ⟨p, hp, hXp⟩ := hunb (max X X₀)
    obtain ⟨m, hmN, hbm, hhub⟩ := hstall p hp
      (le_trans (le_max_right _ _) hXp)
    obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
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
    flood_canonical h0 hcov hanchor hfail hflood
  exact ⟨S, hSne, fun h hh => hPpos h (hSP h hh), hcanon⟩

/-- **THE ROUTING DICHOTOMY, UNCONDITIONAL.**  Every counterexample
(covering, `0 ∈ A`, anchors) carries a nonempty positive fixed core
`S*` with exact rotating hubs, and cofinally lives in one of two
order-2 regimes: a FIXED CORE ELEMENT owns coreps at cofinally many
canonical targets, or the ROTATING GUARDIAN owns its target''s
entire order-2 life.  The campaign''s endgame, derived end to end
from first principles. -/
theorem routing_dichotomy_of_hfail {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ((∃ s ∈ S, ∀ X, ∃ n, X ≤ n ∧ N₀ ≤ n ∧ (∃ w ∈ A, s + w = n) ∧
        ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧ ∃ H : Finset ℕ,
          IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          H = insert a S) ∨
      (∀ X, ∃ n, X ≤ n ∧ N₀ ≤ n ∧ ∃ a, a ∈ A ∧ 0 < a ∧ a ∉ S ∧
        (∃ w ∈ A, a + w = n) ∧
        (∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a) ∧
        ∃ H : Finset ℕ, IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧ H = insert a S)) := by
  obtain ⟨S, hSne, hSpos, hcanon⟩ :=
    canonical_flood_pos_of_hfail h0 hcov hanchor hfail
  have h0S : 0 ∉ S := by
    intro h
    have := (hSpos 0 h).2
    omega
  exact ⟨S, hSne, hSpos, flood_routing_dichotomy h0 hcov h0S hcanon⟩

/-- **THE PAIR FLOOD FROM MINIMALITY ALONE.**  A structure theorem
for EVERY ℵ₀-minimal order-2 covering set — no counterexample
hypothesis anywhere: there is one finite pair-free envelope `P`
such that every large basis element `b` pair-guards a personal
target `t ≥ b` (all order-2 representations of `t` route through
`P ∪ {b}`).  A never-stalling pair dodge would build an infinite
deletion leaving every late target a surviving pair — an order-2
basis after deletion, contradicting minimality.  Sanity model: in
the Cantor world every element `c` pair-guards its double `2c`
with empty envelope. -/
theorem pair_flood_of_minimality {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n) :
    ∃ P : Finset ℕ, PairFree A N₀ P ∧ ∃ X, ∀ b ∈ A, X ≤ b →
      ∃ t, N₀ ≤ t ∧ b ≤ t ∧
        ∀ x ∈ A, ∀ y ∈ A, x + y = t →
          x ∈ insert b P ∨ y ∈ insert b P := by
  classical
  by_contra hno
  push_neg at hno
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

/-- **THE DOUBLE FLOOD.**  In a counterexample the two rails align
on the SAME guardian: beyond one threshold, every basis element `b`
simultaneously pair-guards a target `t_b ≥ b` over `P₂ ∪ {b}`
(from minimality) and rep-guards a target `m_b ≥ b` over `P₃ ∪ {b}`
(from order-3 failure).  Every large element of the enemy carries
both duties at once — the full portrait of the enemy''s workforce. -/
theorem double_flood_of_counterexample {A : Set ℕ} {N₀ : ℕ}
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
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P₃)) := by
  obtain ⟨P₂, hP₂free, X₂, h₂⟩ := pair_flood_of_minimality hcov hmin
  obtain ⟨P₃, hP₃free, X₃, h₃⟩ := rep_flood_of_hfail h0 hcov hfail
  exact ⟨P₂, P₃, hP₂free, hP₃free, max X₂ X₃, fun b hb hXb =>
    ⟨h₂ b hb (le_trans (le_max_left _ _) hXb),
     h₃ b hb (le_trans (le_max_right _ _) hXb)⟩⟩

/-- **At most two guardians per pair-target.**  One envelope-avoiding
pair representation of `t` pins every possible pair-guardian of `t`
to its two parts: the guardian→target map of the pair flood is at
most 2-to-1.  With every large basis element on duty, the enemy
needs (at least) one fresh Sidon target for every two elements —
the workforce cannot share. -/
theorem two_guardians_per_pair_target {A : Set ℕ} {N₀ t : ℕ}
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

/-- **At most three guardians per rep-target.**  The order-3
analogue: one envelope-avoiding triple pins every rep-guardian of
`m` to its three parts. -/
theorem three_guardians_per_rep_target {A : Set ℕ} {N₀ m : ℕ}
    {P : Finset ℕ}
    (hfree : RepFree A N₀ P) (hm : N₀ ≤ m) :
    ∃ x₀ y₀ z₀, ∀ b, b ∉ P →
      IsRepHub A m (insert b P) →
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

/-- **THE SIDON DOOR IS CLOSED: `r₂` is unbounded in any
counterexample.**  Erdős–Turán holds for Erdős-881 counterexamples,
unconditionally: the rep flood hands every large element a hub
target `m`, the fan blowup forces some hub translate `m − h` to
carry at least `(√m − c)/c` pair representations, and square-root
growth of a covering set makes that quantity exceed any bound.  A
counterexample can NEVER be globally Sidon-like — while its flood
targets are simultaneously forced to be essentially Sidon: the
enemy's pair-multiplicity must oscillate between `≤ 2(|P|+1)` and
`∞` forever. -/
theorem r2_unbounded_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card := by
  classical
  intro C N
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
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
  obtain ⟨h₀, hh₀, hblow⟩ := hub_fan_blowup hcov hhub
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

/-- **THE COUNTEREXAMPLE PORTRAIT.**  Everything the session proved
about a counterexample to Erdős 881 (k = 2), in one statement, from
covering + `0 ∈ A` + anchors + minimality + order-3 failure:

1. CENTRAL ADMINISTRATION: one NONEMPTY POSITIVE fixed core `S*`;
   cofinally many rotating guardians `b` with minimal order-3 hubs
   EXACTLY `S* ∪ {b}`.
2. FULL EMPLOYMENT: beyond one threshold, EVERY basis element
   simultaneously pair-guards a personal target `t ≥ b` over a
   fixed pair-free envelope and rep-guards a personal target
   `m ≥ b` over a fixed rep-free envelope.
3. SIDON STREETS: cofinally many targets carry order-2
   representation count bounded by one constant.
4. BLOWN AVENUES: the order-2 representation count is UNBOUNDED —
   the enemy can never be globally Sidon.

A minimal order-2 basis failing order-3 survival under every
infinite deletion must be all four at once, forever. -/
theorem counterexample_portrait {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hmin : ∀ B ⊆ A, B.Infinite → ¬∃ N₁, ∀ n, N₁ ≤ n →
      ∃ x ∈ A, ∃ y ∈ A, x ∉ B ∧ y ∉ B ∧ x + y = n)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
          (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  ⟨canonical_flood_pos_of_hfail h0 hcov hanchor hfail,
   double_flood_of_counterexample h0 hcov hmin hfail,
   constant_sidon_of_hfail h0 hcov hfail,
   r2_unbounded_of_hfail h0 hcov hfail⟩

/-- **TEAM SUPPLY FROM EVERY DELETION.**  Against any 0-free
infinite deletion, beyond a single global threshold every failing
target carries a minimal hub MADE OF DELETED ELEMENTS with at least
TWO members: the private-stream kill bounds singleton hubs
globally, so the enemy must field genuine teams from inside every
deletion, forever.  The legacy campaign's team hypothesis, derived. -/
theorem guardian_team_hubs_of_deletion {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) (h0B : 0 ∉ B) :
    ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := by
  classical
  have hsing := singleton_hubs_refuted h0 hcov hanchor hfail
  push_neg at hsing
  obtain ⟨Nₛ, hNₛ⟩ := hsing
  intro N
  have hnb := hfail B hBA hBinf
  rw [IsExactTupleAsymptoticBasis] at hnb
  push_neg at hnb
  obtain ⟨n, hnN, hnorep⟩ := hnb (max N (max N₀ Nₛ))
  have hdead : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = n →
      x ∈ B ∨ y ∈ B ∨ z ∈ B := by
    intro x hx y hy z hz hsum
    by_contra hall
    push_neg at hall
    obtain ⟨hxB, hyB, hzB⟩ := hall
    refine hnorep ![x, y, z] ?_ (by simpa [Fin.sum_univ_three] using hsum)
    intro i
    match i with
    | 0 => exact ⟨hx, hxB⟩
    | 1 => exact ⟨hy, hyB⟩
    | 2 => exact ⟨hz, hzB⟩
  have hhub := failing_hub_subset_deletion (B := B) hdead
  obtain ⟨H', hH'sub, hH'hub, hH'min⟩ := exists_minimal_hub hhub
  have hH'B : ∀ h ∈ H', h ∈ B := by
    intro h hh
    exact (Finset.mem_filter.1 (hH'sub hh)).2
  have hH'ne : H'.Nonempty :=
    hub_nonempty_of_covering h0 hcov
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hnN)
      hH'hub
  have hcard2 : 2 ≤ H'.card := by
    by_contra hlt
    push_neg at hlt
    have hpos : 0 < H'.card := Finset.card_pos.2 hH'ne
    have hone : H'.card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hone
    have haB : a ∈ B := hH'B a (ha ▸ Finset.mem_singleton_self a)
    have hapos : 0 < a := by
      by_contra ha0
      push_neg at ha0
      have haz : a = 0 := by omega
      rw [haz] at haB
      exact h0B haB
    exact hNₛ n (le_trans (le_trans (le_max_right _ _)
      (le_max_right _ _)) hnN) a hapos (ha ▸ hH'hub)
  exact ⟨n, le_trans (le_max_left _ _) hnN, H', hH'hub, hH'min,
    hcard2, hH'B⟩

/-- Blowup instances of the rep flood: a hub target `m` guarded by
`b` over `P`, whose translate by `h₀ ∈ P ∪ {b}` carries at least
`C` pair representations. -/
def BlowupAt (A : Set ℕ) (N₀ : ℕ) (P : Finset ℕ)
    [DecidablePred (· ∈ A)] (C m b h₀ : ℕ) : Prop :=
  b ∈ A ∧ N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P) ∧
  h₀ ∈ insert b P ∧
  C ≤ ((Finset.range (m - h₀ + 1)).filter
    (fun x => x ∈ A ∧ (m - h₀ - x) ∈ A)).card

/-- Blowup instances exist beyond every bound: the quantitative core
of `r2_unbounded_of_hfail`, with the offset data retained. -/
theorem blowup_supply_of_hfail {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧
      ∀ C N, ∃ m b h₀, N ≤ m ∧ BlowupAt A N₀ P C m b h₀ := by
  classical
  obtain ⟨P, hPfree, X₀, hflood⟩ := rep_flood_of_hfail h0 hcov hfail
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
  obtain ⟨h₀, hh₀, hblow⟩ := hub_fan_blowup hcov hhub
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

/-- **THE BLOWUP OFFSET DICHOTOMY.**  Where do the blown translates
sit?  Pigeonholing the offsets over the finite envelope: either ONE
FIXED envelope element `s₀` carries blowups beyond every bound —
Sidon flood-target and blown translate at fixed distance `s₀`,
cofinally — or the blowups ride the ROTATING COREP `m − b` itself. -/
theorem blowup_offset_dichotomy {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∃ P : Finset ℕ, RepFree A N₀ P ∧
      ((∃ s₀ ∈ P, ∀ C N, ∃ m b, N ≤ m ∧
        BlowupAt A N₀ P C m b s₀) ∨
      (∀ C N, ∃ m b, N ≤ m ∧ BlowupAt A N₀ P C m b b)) := by
  classical
  obtain ⟨P, hPfree, hsupply⟩ := blowup_supply_of_hfail h0 hcov hfail
  refine ⟨P, hPfree, ?_⟩
  by_cases hcorep : ∀ C N, ∃ m b, N ≤ m ∧ BlowupAt A N₀ P C m b b
  · exact Or.inr hcorep
  · left
    push_neg at hcorep
    obtain ⟨C₁, N₁, hblock⟩ := hcorep
    by_contra hnos
    push_neg at hnos
    have hex : ∀ s, ∃ Cs Ns, s ∈ P →
        ∀ m b, Ns ≤ m → ¬BlowupAt A N₀ P Cs m b s := by
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
    have hmono : ∀ C' , C' ≤ Cmax → BlowupAt A N₀ P Cmax m b h₀ →
        BlowupAt A N₀ P C' m b h₀ := by
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

/-- **The pair-owner reflection desert.**  When one element owns a
target's entire order-2 life, the target's reflection of `A` misses
`A` everywhere except at the owner and its corep: for any element
`z` other than the owner whose complement part is not the owner
either, `n − z` is a non-element.  Feeding two rotating guardians
into each other's deserts forbids entire shifted difference sets. -/
theorem pair_owner_reflection_desert {A : Set ℕ} {n a z : ℕ}
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a)
    (hz : z ∈ A) (hzn : z ≤ n) (hza : z ≠ a) (hnza : n - z ≠ a) :
    n - z ∉ A := by
  intro hmem
  rcases hall z hz (n - z) hmem (by omega) with h | h
  · exact hza h
  · exact hnza h

/-- **Shared pair-targets are guardian sums.**  If two distinct
guardians pair-guard the same target over one free envelope, the
envelope-avoiding pair IS the guardian pair: `t = b + b'`, and the
target's only envelope-free order-2 life is the two guardians
summing to it.  Sharing is total exposure. -/
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

/-- **Shared rep-targets of three guardians are triple sums.**  If
three pairwise-distinct guardians rep-guard the same target over
one free envelope, the envelope-avoiding triple IS the guardian
triple: `m = b₁ + b₂ + b₃`. -/
theorem shared_rep_target_is_sum3 {A : Set ℕ} {N₀ m b₁ b₂ b₃ : ℕ}
    {P : Finset ℕ}
    (hfree : RepFree A N₀ P) (hm : N₀ ≤ m)
    (h12 : b₁ ≠ b₂) (h13 : b₁ ≠ b₃) (h23 : b₂ ≠ b₃)
    (hg₁ : IsRepHub A m (insert b₁ P))
    (hg₂ : IsRepHub A m (insert b₂ P))
    (hg₃ : IsRepHub A m (insert b₃ P)) :
    m = b₁ + b₂ + b₃ := by
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hxP, hyP, hzP⟩ := hfree m hm
  have hpin : ∀ b, IsRepHub A m (insert b P) →
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

/-- **WELL-FOUNDEDNESS OF FREENESS.**  Against a counterexample, NO
infinite increasing positive sequence in `A` keeps all its finite
prefixes rep-free: freeness must die at some finite stage along
every branch.  This is the tree the ordinal-rank program climbs:
the rep-free finite subsets of `A`, ordered by end-extension, form
a well-founded tree whose every leaf hands a guardian its personal
hub (the stall).  The dodge theorems are the traversal; this is the
tree itself. -/
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

/-- **Well-foundedness at order 2, from minimality alone.**  In any
ℵ₀-minimal order-2 covering set, no infinite increasing positive
sequence keeps all its finite prefixes pair-free: the pair-free
tree is well-founded for EVERY minimal basis, counterexample or
not.  Minimality IS a well-foundedness statement. -/
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

/-- **The corep offset dichotomy.**  In a guardian-owned pair
stream (each target `a + w` has all its order-2 life through `a`),
either the corep offset pigeonholes to ONE fixed `w₀` — cofinally
many guardians own the target `a + w₀` at fixed distance — or the
coreps run away beyond every bound. -/
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
    push_neg at hbnd
    intro W X
    obtain ⟨X', hX'⟩ := hbnd W
    obtain ⟨a, w, ha, hw, hXa, hNn, hall⟩ := hstream (max X X')
    have hwW : W < w := by
      by_contra hle
      push_neg at hle
      obtain ⟨x, hx, y, hy, hxy, hxa, hya⟩ :=
        hX' a w ha hw (le_trans (le_max_right _ _) hXa) hle hNn
      rcases hall x hx y hy hxy with h | h
      · exact hxa h
      · exact hya h
    exact ⟨a, w, ha, hw, le_trans (le_max_left _ _) hXa, hwW, hNn,
      hall⟩

/-- **The guardian difference desert.**  In the fixed-offset regime,
any second element inside the window — in particular any OTHER
guardian — reflects to a non-element: `a + w₀ − a' ∉ A` whenever
`a' ≠ a, w₀`.  The shifted difference set of the guardian family
avoids `A` wholesale. -/
theorem guardian_difference_desert {A : Set ℕ} {w₀ a a' : ℕ}
    (hall : ∀ x ∈ A, ∀ y ∈ A, x + y = a + w₀ → x = a ∨ y = a)
    (ha' : a' ∈ A) (hle : a' ≤ a + w₀) (hne : a' ≠ a)
    (hnw : a' ≠ w₀) :
    a + w₀ - a' ∉ A :=
  pair_owner_reflection_desert hall ha' hle hne (by omega)

/-- **Disjoint envelopes: the double duty.**  Removing the first
stalled envelope from the pool and re-running the dodge yields a
SECOND envelope disjoint from the first — and every sufficiently
large element outside the first envelope guards two targets over
the two disjoint envelopes simultaneously.  The finite level-2
instance of the simultaneous-duty load; iterates to any level. -/
theorem pair_flood_two_envelopes {A : Set ℕ} {N₀ : ℕ}
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
    pair_flood_pool (P₀ := {a | a ∈ A ∧ 0 < a}) h0 hcov
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
    pair_flood_pool (P₀ := {a | a ∈ A ∧ 0 < a ∧ a ∉ E₀}) h0 hcov
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

/-- **The hub-server dichotomy.**  Under any 0-free infinite
deletion, the team supply splits: either ONE fixed deleted element
serves minimal team hubs at cofinally many failing targets (a
hub-server — a fixed element necessary at infinitely many fresh
targets), or the teams escape every window (hubs made of deleted
elements all beyond any bound, cofinally).  The concrete dichotomy
the rank program's deletion-feedback route runs on. -/
theorem hub_server_dichotomy {A B : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B' ⊆ A, B'.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B') 3)
    (hBA : B ⊆ A) (hBinf : B.Infinite) (h0B : 0 ∉ B) :
    (∃ b ∈ B, ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B) ∧ b ∈ H) ∨
    (∀ W N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B) ∧ ∀ h ∈ H, W < h) := by
  classical
  have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
    hfail hBA hBinf h0B
  set Q : ℕ → Finset ℕ → Prop := fun n H =>
    IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
      have hinst : IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
      exact hinst.2.2.2 b hbH
    refine ⟨b, hbB, fun N => ?_⟩
    obtain ⟨n, hn, H, hQH, hbH⟩ := hb N
    have hinst : IsRepHub A n H ∧
        (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
    exact ⟨n, hn, H, hinst.1, hinst.2.1, hinst.2.2.1,
      hinst.2.2.2, hbH⟩
  · right
    intro W N
    rcases cofinal_dichotomy Q hQ W with ⟨b, hbW, hper⟩ | havoid
    · exact absurd ⟨b, hper⟩ hserv
    · obtain ⟨n, hn, H, hQH, hbig⟩ := havoid N
      have hinst : IsRepHub A n H ∧
          (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B := hQH
      exact ⟨n, hn, H, hinst.1, hinst.2.1, hinst.2.2.1,
        hinst.2.2.2, hbig⟩

/-- Adapter: problem-native ℵ₀-minimality (no infinite deletion
leaves an exact order-2 tuple basis) implies the elementwise
minimality the flood machinery consumes. -/
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

/-- **THE COUNTEREXAMPLE PORTRAIT, PROBLEM-NATIVE FORM.**  The full
structure theorem with both hypotheses stated exactly as in Erdős
881 (k = 2): `A` is ℵ₀-minimal as an exact order-2 tuple basis, and
no infinite deletion leaves an exact order-3 tuple basis. -/
theorem counterexample_portrait' {A : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ A)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hmin : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 2)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3) :
    (∃ S : Finset ℕ, S.Nonempty ∧ (∀ h ∈ S, h ∈ A ∧ 0 < h) ∧
      ∀ X, ∃ b, b ∈ A ∧ X ≤ b ∧ b ∉ S ∧
        ∃ m, N₀ ≤ m ∧ ∃ H : Finset ℕ, IsRepHub A m H ∧
          (∀ h ∈ H, ¬IsRepHub A m (H \ {h})) ∧ H = insert b S) ∧
    (∃ P₂ P₃ : Finset ℕ, PairFree A N₀ P₂ ∧ RepFree A N₀ P₃ ∧
      ∃ X, ∀ b ∈ A, X ≤ b →
        (∃ t, N₀ ≤ t ∧ b ≤ t ∧
          ∀ x ∈ A, ∀ y ∈ A, x + y = t →
            x ∈ insert b P₂ ∨ y ∈ insert b P₂) ∧
        (∃ m, N₀ ≤ m ∧ b ≤ m ∧ IsRepHub A m (insert b P₃))) ∧
    (∃ C, ∀ N, ∃ m, N ≤ m ∧
      ((Finset.range (m + 1)).filter
        (fun x => x ∈ A ∧ (m - x) ∈ A)).card ≤ C) ∧
    (∀ C N, ∃ v, N ≤ v ∧ C ≤ ((Finset.range (v + 1)).filter
      (fun x => x ∈ A ∧ (v - x) ∈ A)).card) :=
  counterexample_portrait h0 hcov hanchor
    (minimality_elementwise_of_tuple hmin) hfail

/-- **REP-PAIR CLIQUE OR TRIPLE TEAMS.**  The first Ramsey harvest
on the hub hypergraph: along any increasing positive ground stream
in `A`, either an infinite subsequence forms a REP-PAIR CLIQUE —
every pair of its members jointly hubs some late target — or an
infinite subsequence is pair-hub-free, and then every minimal team
hub inside it (supplied cofinally by
`guardian_team_hubs_of_deletion`) has at least THREE members.
Team-card escalation, step one. -/
theorem rep_pair_clique_or_triple_teams {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        3 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  set c : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} then true else false
    with hc
  have hciff : ∀ i j, c i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j}
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
  · -- pair-hub-free branch: teams have card ≥ 3
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
        ¬∃ m, N₀ ≤ m ∧ IsRepHub A m {b (f i), b (f j)} := by
      intro i j hij hex
      have h1 := (hciff (f i) (f j)).2 hex
      rw [hhom i j hij] at h1
      exact Bool.false_ne_true h1
    have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
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

/-- **Clique rows must march.**  In a rep-pair clique, no cofinal
family of rows can keep a single stable target served by unboundedly
many columns: a stable row target `n` eventually sees columns
`e j > n`, which cannot be parts of any representation, so every
representation is forced onto the row element alone — a positive
singleton hub.  Cofinally many such rows contradict the
private-stream kill.  The clique''s target array escapes upward on
almost every row. -/
theorem clique_rows_march {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (e : ℕ → ℕ) (hemono : StrictMono e) (hepos : ∀ i, 0 < e i) :
    ¬(∀ X, ∃ i, X ≤ i ∧ ∃ n, N₀ ≤ n ∧ ∀ J, ∃ j, J ≤ j ∧ i < j ∧
      IsRepHub A n {e i, e j}) := by
  intro hstable
  refine singleton_hubs_refuted h0 hcov hanchor hfail ?_
  intro N
  obtain ⟨i, hNi, n, hnN₀, hrow⟩ := hstable N
  -- a column beyond the target
  obtain ⟨j, hJj, hij, hhub⟩ := hrow (n + 1)
  have hejn : n < e j := by
    have h1 : n + 1 ≤ j := hJj
    have h2 : j ≤ e j := hemono.le_apply
    omega
  -- every representation must hit the row element
  have hsing : IsRepHub A n {e i} := by
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

/-- **The injective flood.**  Ramsey against the sharer law: from
the pair flood one extracts an infinite strictly-monotone guardian
sequence whose personal targets are PAIRWISE DISTINCT — the
guardian→target map, made injective.  (All-sharing is impossible:
three guardians of one target would exceed the two-sharer cap.) -/
theorem injective_pair_flood {A : Set ℕ} {N₀ : ℕ}
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
  obtain ⟨P, hPfree, X₀, hflood⟩ := pair_flood_of_hfail h0 hcov hfail
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
  · -- all-sharing: three guardians on one target, impossible
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
    obtain ⟨x₀, y₀, hpin⟩ := two_guardians_per_pair_target hPfree
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

/-- **TEAM-CARD ESCALATION, STEP TWO.**  Along any ground stream,
Ramsey at arities two and three refines to a subsequence that is a
rep-pair clique, a rep-triple clique, or hub-free at both arities —
and in the last case every minimal team hub inside it has at least
FOUR members.  The enemy admits no finite team-size bound that the
Ramsey ladder cannot outclimb arity by arity. -/
theorem team_card_escalation_two {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j), b (f k)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        4 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  -- arity two
  set c₂ : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} then true else false
    with hc₂
  have hc₂iff : ∀ i j, c₂ i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j}
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
      if ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k} then true
      else false with hc₃
    have hc₃iff : ∀ i j k, c₃ i j k = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k} := by
      intro i j k
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k}
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
      have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
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
                IsRepHub A m {b (f₁ i'), b (f₁ j')} := by
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
              IsRepHub A m {e (f₂ i), e (f₂ j), e (f₂ k)} := by
            intro hex
            have h1 := (hc₃iff (f₂ i) (f₂ j) (f₂ k)).2 hex
            rw [hhom₃ i j k hij hjk] at h1
            exact Bool.false_ne_true h1
          refine hkill ⟨n, hnN₀, ?_⟩
          have hgg : ∀ l, e (f₂ l) = g l := fun _ => rfl
          rw [hgg i, hgg j, hgg k, hset]
          exact hhub
      · exact hge

/-- **Team targets dominate their members, pair-free version.**  If
the pair `{u, v}` never hubs a late target but the triple
`{u, v, w}` hubs `n`, then `w ≤ n`: a member beyond the target
would be unhittable, collapsing the triple hub onto the banned
pair.  In pair-free worlds, triple-clique targets march at least as
fast as their largest member. -/
theorem team_target_dominates {A : Set ℕ} {N₀ n u v w : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepHub A m {u, v})
    (hn : N₀ ≤ n) (hhub : IsRepHub A n {u, v, w}) :
    w ≤ n := by
  by_contra hgt
  push_neg at hgt
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
`team_target_dominates` applies to every clique hub), and the
team branch records freeness at both arities. -/
theorem team_card_escalation_two' {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j)}) ∨
      ((∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
          IsRepHub A n {b (f i), b (f j)}) ∧
        (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
          IsRepHub A n {b (f i), b (f j), b (f k)})) ∨
      ((∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
          IsRepHub A n {b (f i), b (f j)}) ∧
        (∀ i j k, i < j → j < k → ¬∃ n, N₀ ≤ n ∧
          IsRepHub A n {b (f i), b (f j), b (f k)}) ∧
        ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
          IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
          4 ≤ H.card ∧
          ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  set c₂ : ℕ → ℕ → Bool := fun i j =>
    if ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} then true else false
    with hc₂
  have hc₂iff : ∀ i j, c₂ i j = true ↔
      ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j} := by
    intro i j
    by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {b i, b j}
    · simp [hc₂, h]
    · simp [hc₂, h]
  obtain ⟨f₁, hf₁, b₂col, hhom₂⟩ := infinite_ramsey_pairs c₂
  rcases Bool.eq_false_or_eq_true b₂col with hb₂ | hb₂
  · subst hb₂
    exact ⟨f₁, hf₁, Or.inl (fun i j hij =>
      (hc₂iff (f₁ i) (f₁ j)).1 (hhom₂ i j hij))⟩
  · subst hb₂
    have hpf₁ : ∀ i j, i < j →
        ¬∃ n, N₀ ≤ n ∧ IsRepHub A n {b (f₁ i), b (f₁ j)} := by
      intro i j hij hex
      have h1 := (hc₂iff (f₁ i) (f₁ j)).2 hex
      rw [hhom₂ i j hij] at h1
      exact Bool.false_ne_true h1
    set e : ℕ → ℕ := fun i => b (f₁ i) with he
    set c₃ : ℕ → ℕ → ℕ → Bool := fun i j k =>
      if ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k} then true
      else false with hc₃
    have hc₃iff : ∀ i j k, c₃ i j k = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k} := by
      intro i j k
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k}
      · simp [hc₃, h]
      · simp [hc₃, h]
    obtain ⟨f₂, hf₂, b₃col, hhom₃⟩ := infinite_ramsey_triples c₃
    have hpfc : ∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
        IsRepHub A n {b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j)} :=
      fun i j hij => hpf₁ (f₂ i) (f₂ j) (hf₂ hij)
    rcases Bool.eq_false_or_eq_true b₃col with hb₃ | hb₃
    · subst hb₃
      refine ⟨f₁ ∘ f₂, hf₁.comp hf₂, Or.inr (Or.inl ⟨hpfc, ?_⟩)⟩
      intro i j k hij hjk
      exact (hc₃iff (f₂ i) (f₂ j) (f₂ k)).1 (hhom₃ i j k hij hjk)
    · subst hb₃
      have htfc : ∀ i j k, i < j → j < k → ¬∃ n, N₀ ≤ n ∧
          IsRepHub A n {b ((f₁ ∘ f₂) i), b ((f₁ ∘ f₂) j),
            b ((f₁ ∘ f₂) k)} := by
        intro i j k hij hjk hex
        have h1 := (hc₃iff (f₂ i) (f₂ j) (f₂ k)).2 hex
        rw [hhom₃ i j k hij hjk] at h1
        exact Bool.false_ne_true h1
      obtain ⟨f, hf, hout⟩ := team_card_escalation_two h0 hcov
        hanchor hfail b hmono hbA hbpos
      -- reuse the concrete third-branch construction instead:
      -- rebuild teams for THIS subsequence directly
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
      have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
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

/-- **Clique targets march with their columns.**  In the
triple-clique branch of the escalation, every hub target of the
clique triple `{b(f i), b(f j), b(f k)}` is at least `b(f k)`:
combining the exported pair-freeness with the domination law.  The
2-dimensional target array of any surviving triple clique escapes
along every column at linear speed. -/
theorem clique_targets_dominate {A : Set ℕ} {N₀ : ℕ}
    {b : ℕ → ℕ} {f : ℕ → ℕ}
    (hpf : ∀ i j, i < j → ¬∃ n, N₀ ≤ n ∧
      IsRepHub A n {b (f i), b (f j)})
    {i j k n : ℕ} (hij : i < j) (hjk : j < k)
    (hn : N₀ ≤ n) (hhub : IsRepHub A n {b (f i), b (f j), b (f k)}) :
    b (f k) ≤ n :=
  team_target_dominates (hpf i j hij) hn hhub

/-- **THE SEPARATED LADDER.**  The injective flood refines to full
alternation: guardians and their personal targets interleave in
strict order, `g 0 ≤ t 0 < g 1 ≤ t 1 < g 2 ≤ ⋯`.  (The
non-separated Ramsey colour is impossible outright: a single row
would need unboundedly many guardians below one target.)  The
flood in ladder form — the geometry the endgame deletions run on. -/
theorem separated_pair_flood {A : Set ℕ} {N₀ : ℕ}
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
    injective_pair_flood h0 hcov hfail
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

/-- **TEAM-CARD ESCALATION, STEP THREE.**  The ladder climbs to
arity four: any ground stream refines to a clique at some arity in
{2, 3, 4} (with freeness below it recorded), or a triply hub-free
subsequence whose minimal team hubs all have at least FIVE members. -/
theorem team_card_escalation_three {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (b : ℕ → ℕ) (hmono : StrictMono b)
    (hbA : ∀ j, b j ∈ A) (hbpos : ∀ j, 0 < b j) :
    ∃ f : ℕ → ℕ, StrictMono f ∧
      ((∀ i j, i < j → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j)}) ∨
      (∀ i j k, i < j → j < k → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j), b (f k)}) ∨
      (∀ i j k l, i < j → j < k → k < l → ∃ n, N₀ ≤ n ∧
        IsRepHub A n {b (f i), b (f j), b (f k), b (f l)}) ∨
      (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
        IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
        5 ≤ H.card ∧
        ∀ h ∈ H, h ∈ Set.range (fun i => b (f i)))) := by
  classical
  obtain ⟨f₀, hf₀, hout⟩ := team_card_escalation_two' h0 hcov
    hanchor hfail b hmono hbA hbpos
  rcases hout with hcl | ⟨hpf, hcl⟩ | ⟨hpf, htf, hteam⟩
  · exact ⟨f₀, hf₀, Or.inl hcl⟩
  · exact ⟨f₀, hf₀, Or.inr (Or.inl hcl)⟩
  · -- doubly free: colour quadruples
    set e : ℕ → ℕ := fun i => b (f₀ i) with he
    have hemono : StrictMono e := fun i j hij => hmono (hf₀ hij)
    set c₄ : ℕ → ℕ → ℕ → ℕ → Bool := fun i j k l =>
      if ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k, e l} then true
      else false with hc₄
    have hc₄iff : ∀ i j k l, c₄ i j k l = true ↔
        ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k, e l} := by
      intro i j k l
      by_cases h : ∃ n, N₀ ≤ n ∧ IsRepHub A n {e i, e j, e k, e l}
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
          ¬∃ n, N₀ ≤ n ∧ IsRepHub A n
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
      have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
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

/-- Domination at arity four: if the triple `{u, v, w}` never hubs
a late target but `{u, v, w, z}` hubs `n`, then `z ≤ n`. -/
theorem team_target_dominates₄ {A : Set ℕ} {N₀ n u v w z : ℕ}
    (htf : ¬∃ m, N₀ ≤ m ∧ IsRepHub A m {u, v, w})
    (hn : N₀ ≤ n) (hhub : IsRepHub A n {u, v, w, z}) :
    z ≤ n := by
  by_contra hgt
  push_neg at hgt
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

/-- **Three columns per clique target.**  If the pair `{u, v}` never
hubs a late target, then any target `n` admits at most three
third-members `w` completing `{u, v, w}` to a hub of `n`: a
representation of `n` avoiding `u` and `v` exists, and every such
`w` must be one of its three parts.  In a pair-free triple clique
the column map is at most 3-to-1 onto its targets. -/
theorem three_columns_per_clique_target {A : Set ℕ} {N₀ n u v : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepHub A m {u, v}) (hn : N₀ ≤ n) :
    ∃ x₀ y₀ z₀, ∀ w, IsRepHub A n {u, v, w} →
      w = x₀ ∨ w = y₀ ∨ w = z₀ := by
  classical
  have hnohub : ¬IsRepHub A n {u, v} := fun h => hpf ⟨n, hn, h⟩
  rw [IsRepHub] at hnohub
  push_neg at hnohub
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

/-- **THE UNION-DELETION TRICHOTOMY.**  Splitting a deletion in two
forces the enemy's hand cofinally: minimal team hubs against the
union either concentrate inside the first piece, concentrate inside
the second, or genuinely straddle both — and a straddling minimal
hub makes members of BOTH pieces necessary at one shared target.
The first verified device that pins two chosen structures to a
single target. -/
theorem union_deletion_trichotomy {A B₁ B₂ : Set ℕ} {N₀ : ℕ}
    [DecidablePred (· ∈ B₁)] [DecidablePred (· ∈ B₂)]
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hanchor : ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬IsExactTupleAsymptoticBasis (A \ B) 3)
    (h1A : B₁ ⊆ A) (h2A : B₂ ⊆ A) (h1inf : B₁.Infinite)
    (h01 : 0 ∉ B₁) (h02 : 0 ∉ B₂) :
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B₁)) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ (∀ h ∈ H, h ∈ B₂)) ∨
    (∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
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
  have hteams := guardian_team_hubs_of_deletion h0 hcov hanchor
    hfail hUA hUinf h0U
  -- three-way cofinal pigeonhole on the hub's piece profile
  by_cases hc1 : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B₁
  · exact Or.inl hc1
  by_cases hc2 : ∀ N, ∃ n, N ≤ n ∧ ∃ H : Finset ℕ,
      IsRepHub A n H ∧ (∀ h ∈ H, ¬IsRepHub A n (H \ {h})) ∧
      2 ≤ H.card ∧ ∀ h ∈ H, h ∈ B₂
  · exact Or.inr (Or.inl hc2)
  · refine Or.inr (Or.inr ?_)
    push_neg at hc1 hc2
    obtain ⟨N₁, hN₁⟩ := hc1
    obtain ⟨N₂, hN₂⟩ := hc2
    intro N
    obtain ⟨n, hn, H, hhub, hmin, hcard, hHU⟩ :=
      hteams (max N (max N₁ N₂))
    refine ⟨n, le_trans (le_max_left _ _) hn, H, hhub, hmin,
      hcard, hHU, ?_, ?_⟩
    · -- some member in B₁: else all in B₂, contradicting hc2
      by_contra hno1
      push_neg at hno1
      have hall2 : ∀ h ∈ H, h ∈ B₂ := by
        intro h hh
        rcases hHU h hh with h' | h'
        · exact absurd h' (hno1 h hh)
        · exact h'
      obtain ⟨h, hh, hhB⟩ := hN₂ n (le_trans (le_trans
        (le_max_right _ _) (le_max_right _ _)) hn) H hhub hmin hcard
      exact hhB (hall2 h hh)
    · by_contra hno2
      push_neg at hno2
      have hall1 : ∀ h ∈ H, h ∈ B₁ := by
        intro h hh
        rcases hHU h hh with h' | h'
        · exact h'
        · exact absurd h' (hno2 h hh)
      obtain ⟨h, hh, hhB⟩ := hN₁ n (le_trans (le_trans
        (le_max_left _ _) (le_max_right _ _)) hn) H hhub hmin hcard
      exact hhB (hall1 h hh)

/-- **Three columns per pair-clique target, singleton version.**
If `{u}` never hubs a late target (u is not a private guardian),
then any target admits at most three partners `w` making `{u, w}` a
hub: the `u`-avoiding representation pins them.  In a pair-clique
world over private-free elements, every row's column map is at most
3-to-1. -/
theorem three_partners_per_pair_target {A : Set ℕ} {N₀ n u : ℕ}
    (hpf : ¬∃ m, N₀ ≤ m ∧ IsRepHub A m {u}) (hn : N₀ ≤ n) :
    ∃ x₀ y₀ z₀, ∀ w, IsRepHub A n {u, w} →
      w = x₀ ∨ w = y₀ ∨ w = z₀ := by
  classical
  have hnohub : ¬IsRepHub A n {u} := fun h => hpf ⟨n, hn, h⟩
  rw [IsRepHub] at hnohub
  push_neg at hnohub
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

/-- **Disjoint representations inject into any hub.**  Each member
of a pairwise-disjoint family of representations must hit the hub,
and full disjointness makes those hits pairwise distinct: so the
number of disjoint representations never exceeds the hub's
cardinality.  Converse-quantitative partner of
`hub_of_no_disjointReps`: hubs of card `c` forbid `c + 1` disjoint
representations, so bounded hubs and bounded disjointness are one
phenomenon.  In particular every perfect-world target — hubbed by
a `(d+1)`-set — carries at most `d + 1` pairwise-disjoint
representations. -/
theorem disjoint_reps_le_hub_card {A : Set ℕ} {n K : ℕ}
    {H : Finset ℕ}
    (hhub : IsRepHub A n H) (hdis : HasDisjointTripleReps A n K) :
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

/-- **Saturated points live in `B + A`.**  A covered saturated
point has a pair meeting `B`, so it decomposes as a `B`-element
plus an `A`-element: the saturated set is additively thin whenever
`B` is. -/
theorem saturated_mem_add {A B : Set ℕ} {N₀ v : ℕ}
    (hcov : PairCovers A N₀) (hv : N₀ ≤ v)
    (hsat : Saturated A B v) :
    ∃ β ∈ B, ∃ a ∈ A, β + a = v := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hcov v hv
  rcases hsat x hx y hy hxy with h | h
  · exact ⟨x, h, y, hy, hxy⟩
  · exact ⟨y, h, x, hx, by omega⟩

open Classical in
/-- **The saturation count bound.**  In any window, saturated
points inject into `B`-window × `A`-window pairs: there are at
most `|B ∩ [0,Y]| · |A ∩ [0,Y]|` of them.  Sparse deletions have
additively sparse saturated sets. -/
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

/-- **Failing targets saturate their fans.**  If every
3-representation of `m` meets `B` (with `0 ∉ B`), then every
translate `m − z` by an undeleted element is `B`-saturated: the
enemy must fit `≈ |A ∩ [0, m]|` fan points inside the additively
thin saturated set at every failing target of every deletion. -/
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

end Erdos881
