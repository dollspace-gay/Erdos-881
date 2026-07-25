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
import Erdos881.MirrorPeriodicity

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
  ∀ y ∈ A, 2 * y > n → y ≤ n → y ≠ a → n - y ∉ A

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

/-- Owned targets are co-`A` points: membership would make the target
its own big fiber with the zero partner.  With `unique_owner`, owners
inject into the complement — the formal dual of the U-density
interface. -/
theorem OwnsTarget.not_mem {A : Set ℕ} {a n : ℕ}
    (h0 : 0 ∈ A) (h : OwnsTarget A a n) : n ∉ A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro hn
  have := h4 n hn (by omega) (le_refl n) (by omega)
  have hval : n - n = 0 := by omega
  rw [hval] at this
  exact this h0

/-- **Ownership is the singleton 2-hub** (up to the midpoint): every
pair representation of an owned target passes through its owner or
sits exactly at the half.  The classification wall and the order-2
rail''s tight singleton case are the same object — the ring of the
night''s theory closes. -/
theorem ownsTarget_pairHub {A : Set ℕ} {a n : ℕ}
    (hown : OwnsTarget A a n) :
    ∀ x ∈ A, ∀ y ∈ A, x + y = n → x = a ∨ y = a ∨ 2 * x = n := by
  obtain ⟨h1, h2, h3, h4⟩ := hown
  intro x hx y hy hxy
  rcases Nat.lt_trichotomy (2 * x) n with hlt | heq | hgt
  · -- y is the big side
    by_cases hya : y = a
    · exact Or.inr (Or.inl hya)
    · exfalso
      have := h4 y hy (by omega) (by omega) hya
      have hval : n - y = x := by omega
      rw [hval] at this
      exact this hx
  · exact Or.inr (Or.inr heq)
  · -- x is the big side
    by_cases hxa : x = a
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

end Erdos881
