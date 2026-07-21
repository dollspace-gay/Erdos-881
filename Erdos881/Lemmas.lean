import Mathlib

/-!
# Checks for lemmas arising in the investigation of Erdős Problem 881

This file formalizes the combinatorial and logical cores of the main lemmas in
the shared investigation.  It deliberately separates those cores from the
number-theoretic definitions, so that Lean checks the actual implications
without hiding assumptions in notation.
-/

open scoped BigOperators

namespace Erdos881

/-! ## Representation predicates -/

/-- `Rep A h n xs` says that `xs` is an ordered, exact `h`-term
representation of `n` by members of `A`. -/
def Rep (A : Set ℕ) (h n : ℕ) (xs : List ℕ) : Prop :=
  xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n

/-- Exact asymptotic basis of order `h`. -/
def IsAsymptoticBasis (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, ∃ xs, Rep A h n xs

/-- The private witnesses for `a`: represented by `A`, but not after removing
`a`. -/
def IsPrivateWitness (A : Set ℕ) (h a n : ℕ) : Prop :=
  (∃ xs, Rep A h n xs) ∧ ¬ ∃ xs, Rep (A \ {a}) h n xs

/-- Ordinary minimality among asymptotic bases. -/
def IsOrdinarilyMinimal (A : Set ℕ) (h : ℕ) : Prop :=
  IsAsymptoticBasis A h ∧ ∀ a ∈ A, ¬ IsAsymptoticBasis (A \ {a}) h

/-- Lemma 2: ordinary minimality is equivalent to unbounded private witnesses. -/
theorem ordinarilyMinimal_iff_privateWitnesses
    {A : Set ℕ} {h : ℕ} :
    IsOrdinarilyMinimal A h ↔
      IsAsymptoticBasis A h ∧
        ∀ a ∈ A, ∀ M, ∃ n ≥ M, IsPrivateWitness A h a n := by
  constructor
  · rintro ⟨hA, hmin⟩
    refine ⟨hA, ?_⟩
    obtain ⟨N, hN⟩ := hA
    intro a ha M
    have hnot := hmin a ha
    simp only [IsAsymptoticBasis, not_exists, not_forall] at hnot
    obtain ⟨n, hnN, hnrep⟩ := hnot (max N M)
    refine ⟨n, le_trans (le_max_right _ _) hnN, ?_⟩
    refine ⟨hN n (le_trans (le_max_left _ _) hnN), ?_⟩
    simpa using hnrep
  · rintro ⟨hA, hprivate⟩
    refine ⟨hA, ?_⟩
    intro a ha hdel
    obtain ⟨N, hN⟩ := hdel
    obtain ⟨n, hn, _, hnoprivate⟩ := hprivate a ha N
    exact hnoprivate (hN n hn)

/-! ## Translation of a transversal from order `k+1` to order `k` -/

/-- A support-free formulation of "every representation meets `S`". -/
def EveryRepMeets (A S : Set ℕ) (h n : ℕ) : Prop :=
  ∀ xs, Rep A h n xs → ∃ x ∈ xs, x ∈ S

/-- Lemma 4, repaired for naturals by making the necessary hypothesis `a ≤ n`
explicit. -/
theorem everyRepMeets_pred
    {A S : Set ℕ} {k n a : ℕ}
    (hall : EveryRepMeets A S (k + 1) n)
    (haA : a ∈ A) (haS : a ∉ S) (han : a ≤ n) :
    EveryRepMeets A S k (n - a) := by
  intro xs hxs
  have hrep : Rep A (k + 1) n (a :: xs) := by
    rcases hxs with ⟨hlen, hmem, hsum⟩
    refine ⟨by simp [hlen], ?_, ?_⟩
    · simp only [List.mem_cons]
      rintro x (rfl | hx)
      · exact haA
      · exact hmem x hx
    · simp [hsum, Nat.add_sub_of_le han]
  obtain ⟨x, hx, hxS⟩ := hall (a :: xs) hrep
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact (haS hxS).elim
  · exact ⟨x, hx, hxS⟩

/-! ## Bounded matching implies a small transversal -/

variable {α : Type*} [DecidableEq α]

/-- A finite family of pairwise disjoint finite edges. -/
def IsMatching (M : Finset (Finset α)) : Prop :=
  (M : Set (Finset α)).PairwiseDisjoint id

/-- `T` meets every edge in `H`. -/
def IsTransversal (H : Finset (Finset α)) (T : Finset α) : Prop :=
  ∀ E ∈ H, (E ∩ T).Nonempty

/-- The union of a maximal matching is a transversal.  This is the constructive
core of the bounded-matching lemma.  Deriving `hmax` merely from maximality
requires the hypergraph's edges to be nonempty. -/
theorem maximalMatching_union_transversal
    {H M : Finset (Finset α)}
    (hmax : ∀ E ∈ H, ∃ D ∈ M, ¬ Disjoint E D) :
    IsTransversal H (M.biUnion id) := by
  intro E hEH
  obtain ⟨D, hDM, hnotdisj⟩ := hmax E hEH
  rw [Finset.not_disjoint_iff] at hnotdisj
  obtain ⟨x, hxE, hxD⟩ := hnotdisj
  refine ⟨x, Finset.mem_inter.mpr ⟨hxE, ?_⟩⟩
  exact Finset.mem_biUnion.mpr ⟨D, hDM, hxD⟩

/-- Cardinality estimate used in the bounded-matching lemma. -/
theorem biUnion_card_le_of_edge_card_le
    {H M : Finset (Finset α)} {r : ℕ}
    (hsub : M ⊆ H)
    (hcard : ∀ E ∈ H, E.card ≤ r) :
    (M.biUnion id).card ≤ r * M.card := by
  calc
    (M.biUnion id).card ≤ ∑ E ∈ M, E.card := Finset.card_biUnion_le
    _ ≤ ∑ _E ∈ M, r := by
      gcongr with E hEM
      exact hcard E (hsub hEM)
    _ = r * M.card := by simp [Nat.mul_comm]

/-- The largest cardinality of a matching in a finite hypergraph. -/
noncomputable def matchingNumber (H : Finset (Finset α)) : ℕ := by
  classical
  exact (H.powerset.filter IsMatching).sup Finset.card

/- Every explicit matching is bounded by the matching number. -/
omit [DecidableEq α] in
theorem card_le_matchingNumber
    {H M : Finset (Finset α)}
    (hsub : M ⊆ H) (hmatching : IsMatching M) :
    M.card ≤ matchingNumber H := by
  classical
  unfold matchingNumber
  apply Finset.le_sup (f := Finset.card)
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr hsub, hmatching⟩

/-- A finite hypergraph with nonempty edges has a maximum matching whose union
meets every edge. -/
theorem exists_maximumMatching
    {H : Finset (Finset α)}
    (hedges : ∀ E ∈ H, E.Nonempty) :
    ∃ M : Finset (Finset α),
      M ⊆ H ∧
      IsMatching M ∧
      M.card = matchingNumber H ∧
      ∀ E ∈ H, ∃ D ∈ M, ¬ Disjoint E D := by
  classical
  let C := H.powerset.filter IsMatching
  have hCnonempty : C.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [C, IsMatching]
  obtain ⟨M, hMC, hmaxcard⟩ :=
    Finset.exists_mem_eq_sup C hCnonempty Finset.card
  have hMsub : M ⊆ H :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hMC).1
  have hMmatch : IsMatching M := (Finset.mem_filter.mp hMC).2
  have hMcard : M.card = matchingNumber H := by
    exact hmaxcard.symm
  refine ⟨M, hMsub, hMmatch, hMcard, ?_⟩
  intro E hEH
  by_contra hnone
  push Not at hnone
  have hEnotM : E ∉ M := by
    intro hEM
    obtain ⟨x, hxE⟩ := hedges E hEH
    exact (Finset.not_disjoint_iff.mpr ⟨x, hxE, hxE⟩) (hnone E hEM)
  have hInsertMatch : IsMatching (insert E M) := by
    rw [IsMatching, Finset.coe_insert, Set.pairwiseDisjoint_insert]
    exact ⟨hMmatch, fun D hDM hED => hnone D hDM⟩
  have hInsertC : insert E M ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, hInsertMatch⟩
    exact Finset.insert_subset hEH hMsub
  have hle := Finset.le_sup (f := Finset.card) hInsertC
  rw [hmaxcard] at hle
  simp [hEnotM] at hle

/-- Full bounded-matching lemma for finite hypergraphs. -/
theorem exists_small_transversal_of_matchingNumber_le
    {H : Finset (Finset α)} {r m : ℕ}
    (hedges : ∀ E ∈ H, E.Nonempty)
    (hsize : ∀ E ∈ H, E.card ≤ r)
    (hmatching : matchingNumber H ≤ m) :
    ∃ T : Finset α, IsTransversal H T ∧ T.card ≤ r * m := by
  obtain ⟨M, hMH, hMmatch, hMcard, hmax⟩ :=
    exists_maximumMatching hedges
  refine ⟨M.biUnion id, maximalMatching_union_transversal hmax, ?_⟩
  calc
    (M.biUnion id).card ≤ r * M.card :=
      biUnion_card_le_of_edge_card_le hMH hsize
    _ ≤ r * m := Nat.mul_le_mul_left r (hMcard ▸ hmatching)

/-- A transversal of a finite hypergraph is at least as large as every
matching.  In particular it bounds the matching number. -/
theorem matchingNumber_le_card_of_transversal
    {H : Finset (Finset α)} {T : Finset α}
    (hedges : ∀ E ∈ H, E.Nonempty)
    (htrans : IsTransversal H T) :
    matchingNumber H ≤ T.card := by
  classical
  obtain ⟨M, hMH, hMmatch, hMcard, _hmax⟩ :=
    exists_maximumMatching hedges
  let pick : ∀ E : {E // E ∈ M}, {x // x ∈ T} := fun E =>
    let w := htrans E.1 (hMH E.2)
    ⟨w.choose, (Finset.mem_inter.mp w.choose_spec).2⟩
  have hpick_mem :
      ∀ E : {E // E ∈ M}, (pick E).1 ∈ E.1 := by
    intro E
    change
      (htrans E.1 (hMH E.2)).choose ∈ E.1
    exact (Finset.mem_inter.mp
      (htrans E.1 (hMH E.2)).choose_spec).1
  have hpick_injective : Function.Injective pick := by
    intro E E' hpick
    apply Subtype.ext
    by_contra hEE'
    have hdisj : Disjoint E.1 E'.1 :=
      hMmatch E.2 E'.2 hEE'
    have hx :
        (pick E).1 = (pick E').1 :=
      congrArg Subtype.val hpick
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick E).1, hpick_mem E, hx ▸ hpick_mem E'⟩) hdisj
  have hcard : M.card ≤ T.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  rw [← hMcard]
  exact hcard

/- A family of pairwise-disjoint transversals cannot be larger than any one
edge: choosing a point where each transversal meets that edge gives an
injection into the edge. -/
theorem card_le_edge_card_of_pairwiseDisjoint_transversals
    {H 𝒯 : Finset (Finset α)} {E : Finset α}
    (hE : E ∈ H)
    (hpair : IsMatching 𝒯)
    (htrans : ∀ T ∈ 𝒯, IsTransversal H T) :
    𝒯.card ≤ E.card := by
  classical
  let pick : ∀ T : {T // T ∈ 𝒯}, {x // x ∈ E} := fun T =>
    let w := htrans T.1 T.2 E hE
    ⟨w.choose, (Finset.mem_inter.mp w.choose_spec).1⟩
  have hpick_mem :
      ∀ T : {T // T ∈ 𝒯}, (pick T).1 ∈ T.1 := by
    intro T
    change (htrans T.1 T.2 E hE).choose ∈ T.1
    exact (Finset.mem_inter.mp
      (htrans T.1 T.2 E hE).choose_spec).2
  have hpick_injective : Function.Injective pick := by
    intro T T' hpick
    apply Subtype.ext
    by_contra hTT'
    have hdisj : Disjoint T.1 T'.1 := hpair T.2 T'.2 hTT'
    have hx : (pick T).1 = (pick T').1 :=
      congrArg Subtype.val hpick
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick T).1, hpick_mem T, hx ▸ hpick_mem T'⟩) hdisj
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective pick hpick_injective

/-! ## Greedy anti-concentration estimate -/

/-- If `M` is maximal and every vertex belongs to at most `Δ` edges, then the
entire hypergraph has at most `r * Δ * |M|` edges. -/
theorem card_edges_le_of_maximalMatching
    {H M : Finset (Finset α)} {r Δ : ℕ}
    (hsub : M ⊆ H)
    (hmax : ∀ E ∈ H, ∃ D ∈ M, ¬ Disjoint E D)
    (hcard : ∀ E ∈ H, E.card ≤ r)
    (hdeg : ∀ x, (H.filter fun E => x ∈ E).card ≤ Δ) :
    H.card ≤ r * Δ * M.card := by
  let f : Finset α → Finset (Finset α) :=
    fun D => H.filter fun E => ¬ Disjoint E D
  have hcover : H ⊆ M.biUnion f := by
    intro E hEH
    obtain ⟨D, hDM, hED⟩ := hmax E hEH
    exact Finset.mem_biUnion.mpr ⟨D, hDM, Finset.mem_filter.mpr ⟨hEH, hED⟩⟩
  calc
    H.card ≤ (M.biUnion f).card := Finset.card_le_card hcover
    _ ≤ ∑ D ∈ M, (f D).card := Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ M, r * Δ := by
      gcongr with D hDM
      calc
        (f D).card ≤
            (D.biUnion fun x => H.filter fun E => x ∈ E).card := by
          apply Finset.card_le_card
          intro E hEf
          simp only [f, Finset.mem_filter] at hEf
          obtain ⟨hEH, hED⟩ := hEf
          obtain ⟨x, hxE, hxD⟩ := Finset.not_disjoint_iff.mp hED
          exact Finset.mem_biUnion.mpr
            ⟨x, hxD, Finset.mem_filter.mpr ⟨hEH, hxE⟩⟩
        _ ≤ ∑ x ∈ D, (H.filter fun E => x ∈ E).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _x ∈ D, Δ := by
          gcongr with x hx
          exact hdeg x
        _ = D.card * Δ := by simp
        _ ≤ r * Δ := Nat.mul_le_mul_right Δ (hcard D (hsub hDM))
    _ = r * Δ * M.card := by simp [Nat.mul_comm, Nat.mul_left_comm]

/-! ## The finite-core sparse-deletion argument -/

/-- The finite counting step in Theorems 6 and 7.  If the outside-`F`
supports are pairwise disjoint, and every destroyed support can be assigned a
deleted outside vertex, fewer deleted vertices than supports cannot destroy all
supports. -/
theorem exists_surviving_support
    {M : Finset (Finset α)} {F D : Finset α} {B : Set α}
    (hdisj : ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' → Disjoint (E \ F) (E' \ F))
    (hhit : ∀ E ∈ M, ¬ Disjoint (E : Set α) B → ∃ x ∈ D, x ∈ E \ F)
    (hcard : D.card < M.card) :
    ∃ E ∈ M, Disjoint (E : Set α) B := by
  classical
  by_contra hall
  push Not at hall
  let pick : ∀ E : {E // E ∈ M}, {x // x ∈ D} := fun E =>
    let w := hhit E.1 E.2 (hall E.1 E.2)
    ⟨w.choose, w.choose_spec.1⟩
  have hpick_mem : ∀ E : {E // E ∈ M}, (pick E).1 ∈ E.1 \ F := by
    intro E
    change (hhit E.1 E.2 (hall E.1 E.2)).choose ∈ E.1 \ F
    exact (hhit E.1 E.2 (hall E.1 E.2)).choose_spec.2
  have hinj : Function.Injective pick := by
    intro E E' heq
    apply Subtype.ext
    by_contra hne
    have hxE := hpick_mem E
    have hxE' := hpick_mem E'
    have hx : (pick E).1 = (pick E').1 := congrArg Subtype.val heq
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick E).1, hxE, hx ▸ hxE'⟩) (hdisj E.1 E.2 E'.1 E'.2 hne)
  have hle := Fintype.card_le_of_injective pick hinj
  have hle' : M.card ≤ D.card := by simpa only [Fintype.card_coe] using hle
  omega

/-! The full diagonal step behind Theorems 6 and 7. -/

/-- An abstract family of representation supports, indexed by the represented
natural number. -/
abbrev SupportFamily := ℕ → Finset (Finset ℕ)

/-- Nonnegativity ensures that a support of a representation of `n` contains
only vertices at most `n`. -/
def SupportsBounded (R : SupportFamily) : Prop :=
  ∀ n E, E ∈ R n → ∀ x ∈ E, x ≤ n

/-- The finite-core matching-growth hypothesis. -/
def MatchingTendsToInfinityOutside (R : SupportFamily) (F : Finset ℕ) : Prop :=
  ∀ j, ∃ T, ∀ n ≥ T, ∃ M : Finset (Finset ℕ),
    M ⊆ R n ∧ j < M.card ∧
      (∀ E ∈ M, (E \ F).Nonempty) ∧
      ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' → Disjoint (E \ F) (E' \ F)

/- Explicit matching growth along a prescribed target set. -/
def MatchingTendsToInfinityOutsideAlong
    (R : SupportFamily) (F : Finset ℕ) (S : Set ℕ) : Prop :=
  ∀ j, ∃ T, ∀ n ≥ T, n ∈ S → ∃ M : Finset (Finset ℕ),
    M ⊆ R n ∧ j < M.card ∧
      (∀ E ∈ M, (E \ F).Nonempty) ∧
      ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' → Disjoint (E \ F) (E' \ F)

/-- Adaptive finite-core matching growth.  The requested matching level may
be protected by a new finite core after seeing an arbitrary finite deletion
prefix, but that core must avoid the prefix. -/
def AdaptiveCoreMatchingTendsToInfinityOutsideAlong
    (R : SupportFamily) (S : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, ∀ j,
    ∃ F : Finset ℕ, Disjoint F D ∧
      ∃ T, ∀ n ≥ T, n ∈ S → ∃ M : Finset (Finset ℕ),
        M ⊆ R n ∧ j < M.card ∧
          (∀ E ∈ M, (E \ F).Nonempty) ∧
          ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
            Disjoint (E \ F) (E' \ F)

/-- A fixed-prefix, fixed-level obstruction to adaptive matching growth. -/
def IsAdaptiveCoreMatchingObstructionAt
    (R : SupportFamily) (S : Set ℕ) (D : Finset ℕ) (j : ℕ) : Prop :=
  ∀ F : Finset ℕ, Disjoint F D → ∀ T,
    ∃ n, T ≤ n ∧ n ∈ S ∧
      ¬ ∃ M : Finset (Finset ℕ),
        M ⊆ R n ∧ j < M.card ∧
          (∀ E ∈ M, (E \ F).Nonempty) ∧
          ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
            Disjoint (E \ F) (E' \ F)

/- Failure of adaptive growth has a useful uniformity: one finite prefix `D`
and one matching level `j` defeat every core disjoint from `D`.  The bad
target may still depend on the core and the requested lower bound. -/
theorem not_adaptiveCoreMatchingTendsToInfinityOutsideAlong_iff
    {R : SupportFamily} {S : Set ℕ} :
    ¬ AdaptiveCoreMatchingTendsToInfinityOutsideAlong R S ↔
      ∃ D : Finset ℕ, ∃ j,
        IsAdaptiveCoreMatchingObstructionAt R S D j := by
  classical
  unfold AdaptiveCoreMatchingTendsToInfinityOutsideAlong
  unfold IsAdaptiveCoreMatchingObstructionAt
  push Not
  rfl

/-- One stage of the adaptive sparse-deletion recursion. -/
structure AdaptiveSparseDeletionStep
    (R : SupportFamily) (C S : Set ℕ)
    (D : Finset ℕ) (j last : ℕ) where
  core : Finset ℕ
  threshold : ℕ
  point : ℕ
  core_disjoint : Disjoint core D
  matching : ∀ n ≥ threshold, n ∈ S → ∃ M : Finset (Finset ℕ),
    M ⊆ R n ∧ j < M.card ∧
      (∀ E ∈ M, (E \ core).Nonempty) ∧
      ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
        Disjoint (E \ core) (E' \ core)
  point_mem : point ∈ C
  point_outside_core : point ∉ core
  point_lower : max threshold (last + 1) ≤ point

theorem adaptiveSparseDeletionStep_nonempty
    {R : SupportFamily} {C S : Set ℕ}
    (hadaptive : AdaptiveCoreMatchingTendsToInfinityOutsideAlong R S)
    (hC : ∀ F : Finset ℕ, ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b)
    (D : Finset ℕ) (j last : ℕ) :
    Nonempty (AdaptiveSparseDeletionStep R C S D j last) := by
  obtain ⟨F, hFD, T, hmatches⟩ := hadaptive D j
  obtain ⟨b, hbC, hbF, hbLower⟩ := hC F (max T (last + 1))
  exact ⟨⟨F, T, b, hFD, hmatches, hbC, hbF, hbLower⟩⟩

/-- Finite-menu adaptive growth.  At one deletion stage each member of a
finite target family may use its own protected core and threshold.  All cores
avoid the current deletion prefix. -/
def FiniteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong
    {ι : Type*} [Fintype ι]
    (R : SupportFamily) (S : ι → Set ℕ) : Prop :=
  ∀ D : Finset ℕ, ∀ j,
    ∃ core : ι → Finset ℕ,
      (∀ i, Disjoint (core i) D) ∧
      ∃ threshold : ι → ℕ,
        ∀ i, ∀ n ≥ threshold i, n ∈ S i →
          ∃ M : Finset (Finset ℕ),
            M ⊆ R n ∧ j < M.card ∧
              (∀ E ∈ M, (E \ core i).Nonempty) ∧
              ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
                Disjoint (E \ core i) (E' \ core i)

/-- One stage of the finite-menu adaptive sparse-deletion recursion. -/
structure FiniteMenuAdaptiveSparseDeletionStep
    {ι : Type*} [Fintype ι]
    (R : SupportFamily) (C : Set ℕ) (S : ι → Set ℕ)
    (D : Finset ℕ) (j last : ℕ) where
  core : ι → Finset ℕ
  threshold : ι → ℕ
  point : ℕ
  core_disjoint : ∀ i, Disjoint (core i) D
  matching : ∀ i, ∀ n ≥ threshold i, n ∈ S i →
    ∃ M : Finset (Finset ℕ),
      M ⊆ R n ∧ j < M.card ∧
        (∀ E ∈ M, (E \ core i).Nonempty) ∧
        ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
          Disjoint (E \ core i) (E' \ core i)
  point_mem : point ∈ C
  point_outside_core : ∀ i, point ∉ core i
  point_lower :
    max ((Finset.univ : Finset ι).sup threshold) (last + 1) ≤ point

theorem finiteMenuAdaptiveSparseDeletionStep_nonempty
    {ι : Type*} [Fintype ι]
    {R : SupportFamily} {C : Set ℕ} {S : ι → Set ℕ}
    (hadaptive :
      FiniteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong R S)
    (hC : ∀ F : Finset ℕ, ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b)
    (D : Finset ℕ) (j last : ℕ) :
    Nonempty (FiniteMenuAdaptiveSparseDeletionStep R C S D j last) := by
  classical
  obtain ⟨core, hcoreD, threshold, hmatching⟩ := hadaptive D j
  let U : Finset ℕ := (Finset.univ : Finset ι).biUnion core
  obtain ⟨b, hbC, hbU, hbLower⟩ :=
    hC U (max ((Finset.univ : Finset ι).sup threshold) (last + 1))
  have hbcore : ∀ i, b ∉ core i := by
    intro i hbi
    apply hbU
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hbi⟩
  exact ⟨⟨core, threshold, b, hcoreD, hmatching,
    hbC, hbcore, hbLower⟩⟩

/-- Two-repair extension property.  After any finite deletion prefix inside
`C`, every sufficiently late target in `S` has two pairwise-disjoint supports,
both already avoiding that prefix. -/
def HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
    (R : SupportFamily) (C S : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, (D : Set ℕ) ⊆ C →
    ∃ threshold, ∀ n ≥ threshold, n ∈ S →
      ∃ E ∈ R n, Disjoint E D ∧
        ∃ E' ∈ R n, Disjoint E' D ∧ Disjoint E E'

/-- Reservoir-relative two-repair property.  The two supports may share
vertices outside the deletion reservoir `C`; only their portions inside `C`
must be disjoint.  This is the exact condition used by the sparse-deletion
recursion, since every newly deleted point is chosen from `C`. -/
def HasTwoRepairsDisjointOnDeletionReservoirAlong
    (R : SupportFamily) (C S : Set ℕ) : Prop :=
  ∀ D : Finset ℕ, (D : Set ℕ) ⊆ C →
    ∃ threshold, ∀ n ≥ threshold, n ∈ S →
      ∃ E ∈ R n, Disjoint E D ∧
        ∃ E' ∈ R n, Disjoint E' D ∧
          Disjoint ((E : Set ℕ) ∩ C) ((E' : Set ℕ) ∩ C)

theorem HasTwoDisjointRepairsAvoidingFinitePrefixesAlong.onDeletionReservoir
    {R : SupportFamily} {C S : Set ℕ}
    (h : HasTwoDisjointRepairsAvoidingFinitePrefixesAlong R C S) :
    HasTwoRepairsDisjointOnDeletionReservoirAlong R C S := by
  intro D hDC
  obtain ⟨threshold, hrepair⟩ := h D hDC
  refine ⟨threshold, ?_⟩
  intro n hn hnS
  obtain ⟨E, hER, hED, E', hE'R, hE'D, hEE'⟩ := hrepair n hn hnS
  refine ⟨E, hER, hED, E', hE'R, hE'D, ?_⟩
  exact Set.disjoint_of_subset_left Set.inter_subset_left
    (Set.disjoint_of_subset_right Set.inter_subset_left (by simpa using hEE'))

/-- A reservoir-relative repair property along a target set containing a
tail is already the global property. -/
theorem HasTwoRepairsDisjointOnDeletionReservoirAlong.of_eventually_mem
    {R : SupportFamily} {C S : Set ℕ}
    (h : HasTwoRepairsDisjointOnDeletionReservoirAlong R C S)
    (hS : ∃ M, ∀ n, M ≤ n → n ∈ S) :
    HasTwoRepairsDisjointOnDeletionReservoirAlong R C Set.univ := by
  obtain ⟨M, hM⟩ := hS
  intro D hDC
  obtain ⟨threshold, hrepair⟩ := h D hDC
  refine ⟨max threshold M, ?_⟩
  intro n hn _hnuniv
  exact hrepair n (le_trans (le_max_left threshold M) hn)
    (hM n (le_trans (le_max_right threshold M) hn))

/-- Restricting the target set preserves the repair property. -/
theorem HasTwoRepairsDisjointOnDeletionReservoirAlong.mono_targets
    {R : SupportFamily} {C S T : Set ℕ}
    (h : HasTwoRepairsDisjointOnDeletionReservoirAlong R C S)
    (hTS : T ⊆ S) :
    HasTwoRepairsDisjointOnDeletionReservoirAlong R C T := by
  intro D hDC
  obtain ⟨threshold, hrepair⟩ := h D hDC
  exact ⟨threshold, fun n hn hnT => hrepair n hn (hTS hnT)⟩

theorem not_hasTwoDisjointRepairsAvoidingFinitePrefixesAlong_iff
    {R : SupportFamily} {C S : Set ℕ} :
    ¬ HasTwoDisjointRepairsAvoidingFinitePrefixesAlong R C S ↔
      ∃ D : Finset ℕ, (D : Set ℕ) ⊆ C ∧
        ∀ threshold, ∃ n, threshold ≤ n ∧ n ∈ S ∧
          ¬ ∃ E ∈ R n, Disjoint E D ∧
            ∃ E' ∈ R n, Disjoint E' D ∧ Disjoint E E' := by
  classical
  unfold HasTwoDisjointRepairsAvoidingFinitePrefixesAlong
  push Not
  rfl

theorem not_hasTwoRepairsDisjointOnDeletionReservoirAlong_iff
    {R : SupportFamily} {C S : Set ℕ} :
    ¬ HasTwoRepairsDisjointOnDeletionReservoirAlong R C S ↔
      ∃ D : Finset ℕ, (D : Set ℕ) ⊆ C ∧
        ∀ threshold, ∃ n, threshold ≤ n ∧ n ∈ S ∧
          ¬ ∃ E ∈ R n, Disjoint E D ∧
            ∃ E' ∈ R n, Disjoint E' D ∧
              Disjoint ((E : Set ℕ) ∩ C) ((E' : Set ℕ) ∩ C) := by
  classical
  unfold HasTwoRepairsDisjointOnDeletionReservoirAlong
  push Not
  rfl

/-- One stage in the two-repair sparse-deletion recursion. -/
structure TwoRepairSparseDeletionStep
    (R : SupportFamily) (C S : Set ℕ)
    (D : Finset ℕ) (last : ℕ) where
  threshold : ℕ
  point : ℕ
  repairs : ∀ n ≥ threshold, n ∈ S →
    ∃ E ∈ R n, Disjoint E D ∧
      ∃ E' ∈ R n, Disjoint E' D ∧
        Disjoint ((E : Set ℕ) ∩ C) ((E' : Set ℕ) ∩ C)
  point_mem : point ∈ C
  point_lower : max threshold (last + 1) ≤ point

theorem twoRepairSparseDeletionStep_nonempty
    {R : SupportFamily} {C S : Set ℕ}
    (hrepairs : HasTwoRepairsDisjointOnDeletionReservoirAlong R C S)
    (hC : ∀ T, ∃ b ∈ C, T ≤ b)
    (D : Finset ℕ) (hDC : (D : Set ℕ) ⊆ C) (last : ℕ) :
    Nonempty (TwoRepairSparseDeletionStep R C S D last) := by
  obtain ⟨threshold, hrepair⟩ := hrepairs D hDC
  obtain ⟨b, hbC, hbLower⟩ := hC (max threshold (last + 1))
  exact ⟨⟨threshold, b, hrepair, hbC, hbLower⟩⟩

/-- Abstract form of "the undeleted set is eventually a basis". -/
def HasEventuallySurvivingSupport (R : SupportFamily) (B : Set ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, ∃ E ∈ R n, Disjoint (E : Set ℕ) B

/- Eventual survival restricted to a prescribed target set. -/
def HasEventuallySurvivingSupportAlong
    (R : SupportFamily) (B S : Set ℕ) : Prop :=
  ∃ N, ∀ n ≥ N, n ∈ S →
    ∃ E ∈ R n, Disjoint (E : Set ℕ) B

/- A countable family covers the tail uniformly against arbitrary individual
thresholds if, after assigning a threshold to every member of the family,
the portions above those thresholds still cover a tail.  This is exactly the
uniformity needed to turn countably many relative eventual statements into
one global eventual statement. -/
def UniformThresholdCover (S : ℕ → Set ℕ) : Prop :=
  ∀ t : ℕ → ℕ, ∃ N, ∀ n, N ≤ n →
    ∃ i, t i ≤ n ∧ n ∈ S i

/- A finite subfamily has cofinite union. -/
def HasFiniteCofiniteSubcover (S : ℕ → Set ℕ) : Prop :=
  ∃ I : Finset ℕ, ∃ N, ∀ n, N ≤ n →
    ∃ i ∈ I, n ∈ S i

/- On the naturals, resistance to arbitrary coordinatewise thresholds is not
an extra countable compactness principle: it is equivalent to a finite
cofinite subcover.  In the reverse direction, if no finite subfamily covers a
tail, recursively choose `b m` outside the first `m + 1` sets and put the
threshold of set `i` above `b i`. -/
theorem uniformThresholdCover_iff_finiteCofiniteSubcover
    {S : ℕ → Set ℕ} :
    UniformThresholdCover S ↔ HasFiniteCofiniteSubcover S := by
  classical
  constructor
  · intro huniform
    by_contra hfinite
    have hescape : ∀ I : Finset ℕ, ∀ N, ∃ n, N ≤ n ∧
        ∀ i ∈ I, n ∉ S i := by
      intro I N
      by_contra hno
      have hcover : ∀ n, N ≤ n → ∃ i ∈ I, n ∈ S i := by
        intro n hn
        by_contra hnone
        apply hno
        refine ⟨n, hn, ?_⟩
        intro i hiI hiS
        exact hnone ⟨i, hiI, hiS⟩
      exact hfinite ⟨I, N, hcover⟩
    have hstep : ∀ m last, ∃ n, last + 1 ≤ n ∧
        ∀ i ∈ Finset.range (m + 1), n ∉ S i := by
      intro m last
      exact hescape (Finset.range (m + 1)) (last + 1)
    choose next hnext havoid using hstep
    let b : ℕ → ℕ := fun m =>
      Nat.rec (next 0 0) (fun j last => next (j + 1) last) m
    have hbnext : ∀ m, b m + 1 ≤ b (m + 1) := by
      intro m
      exact hnext (m + 1) (b m)
    have hbmono : StrictMono b := by
      apply strictMono_nat_of_lt_succ
      intro m
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (hbnext m)
    have hbavoid : ∀ m i, i ≤ m → b m ∉ S i := by
      intro m i him
      cases m with
      | zero =>
          exact havoid 0 0 i
            (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
      | succ j =>
          exact havoid (j + 1) (b j) i
            (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    let t : ℕ → ℕ := fun i => b i + 1
    obtain ⟨N, hN⟩ := huniform t
    obtain ⟨i, hti, hiS⟩ := hN (b N) (hbmono.id_le N)
    by_cases hiN : i ≤ N
    · exact hbavoid N i hiN hiS
    · have hNilt : b N < b i := hbmono (Nat.lt_of_not_ge hiN)
      exact (not_le_of_gt (lt_trans hNilt (Nat.lt_succ_self (b i))))
        (show b i + 1 ≤ b N from hti)
  · rintro ⟨I, N, hcover⟩ t
    refine ⟨max N (I.sup t), ?_⟩
    intro n hn
    obtain ⟨i, hiI, hiS⟩ :=
      hcover n (le_trans (le_max_left _ _) hn)
    exact ⟨i,
      le_trans (Finset.le_sup hiI)
        (le_trans (le_max_right _ _) hn), hiS⟩

/- Uniform threshold coverage is precisely what globalizes countably many
relative eventual-survival statements whose thresholds may vary. -/
theorem hasEventuallySurvivingSupport_of_countableAlong_of_uniformThresholdCover
    {R : SupportFamily} {B : Set ℕ} {S : ℕ → Set ℕ}
    (hsurvive : ∀ i, HasEventuallySurvivingSupportAlong R B (S i))
    (hcover : UniformThresholdCover S) :
    HasEventuallySurvivingSupport R B := by
  choose threshold hthreshold using hsurvive
  obtain ⟨N, hN⟩ := hcover threshold
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨i, hti, hnS⟩ := hN n hn
  exact hthreshold i n hti hnS

/- Relative matching growth is stable when the protected finite core is
enlarged.  Starting with `j + |G|` outside-`F` disjoint supports, at most
`|G|` can become empty after deleting `G`, since those lost supports consume
distinct vertices of `G`. -/
theorem matchingTendsToInfinityOutsideAlong_mono_core
    {R : SupportFamily} {F G : Finset ℕ} {S : Set ℕ}
    (hFG : F ⊆ G)
    (hmatches : MatchingTendsToInfinityOutsideAlong R F S) :
    MatchingTendsToInfinityOutsideAlong R G S := by
  classical
  intro j
  obtain ⟨T, hT⟩ := hmatches (j + G.card)
  refine ⟨T, ?_⟩
  intro n hn hnS
  obtain ⟨M, hMR, hlarge, hnonempty, hdisjoint⟩ := hT n hn hnS
  let good : Finset (Finset ℕ) := M.filter fun E => (E \ G).Nonempty
  let bad : Finset (Finset ℕ) := M.filter fun E => ¬ (E \ G).Nonempty
  have hbadPick : ∀ E : {E // E ∈ bad},
      ∃ x : {x // x ∈ G}, x.1 ∈ E.1 \ F := by
    intro E
    have hEM : E.1 ∈ M := (Finset.mem_filter.mp E.2).1
    obtain ⟨x, hxEF⟩ := hnonempty E.1 hEM
    have hxG : x ∈ G := by
      by_contra hxG
      have hxEG : x ∈ E.1 \ G :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxEF).1, hxG⟩
      exact (Finset.mem_filter.mp E.2).2 ⟨x, hxEG⟩
    exact ⟨⟨x, hxG⟩, hxEF⟩
  choose pick hpick using hbadPick
  have hpick_injective : Function.Injective pick := by
    intro E E' hpickEq
    apply Subtype.ext
    by_contra hEE'
    have hEM : E.1 ∈ M := (Finset.mem_filter.mp E.2).1
    have hE'M : E'.1 ∈ M := (Finset.mem_filter.mp E'.2).1
    have hx : (pick E).1 = (pick E').1 :=
      congrArg Subtype.val hpickEq
    exact (Finset.not_disjoint_iff.mpr
      ⟨(pick E).1, hpick E, hx ▸ hpick E'⟩)
      (hdisjoint E.1 hEM E'.1 hE'M hEE')
  have hbadCard : bad.card ≤ G.card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_le_of_injective pick hpick_injective
  have hsplit : good.card + bad.card = M.card := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := M) (fun E => (E \ G).Nonempty))
  have hgoodLarge : j < good.card := by omega
  refine ⟨good, ?_, hgoodLarge, ?_, ?_⟩
  · intro E hEgood
    exact hMR (Finset.mem_filter.mp hEgood).1
  · intro E hEgood
    exact (Finset.mem_filter.mp hEgood).2
  · intro E hEgood E' hE'good hEE'
    have hEFsubset : E \ G ⊆ E \ F := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hx).1,
          fun hxF => (Finset.mem_sdiff.mp hx).2 (hFG hxF)⟩
    have hE'Fsubset : E' \ G ⊆ E' \ F := by
      intro x hx
      exact Finset.mem_sdiff.mpr
        ⟨(Finset.mem_sdiff.mp hx).1,
          fun hxF => (Finset.mem_sdiff.mp hx).2 (hFG hxF)⟩
    exact Disjoint.mono hEFsubset hE'Fsubset <|
      hdisjoint E (Finset.mem_filter.mp hEgood).1
        E' (Finset.mem_filter.mp hE'good).1 hEE'

/-- Theorems 6 and 7: matching growth outside a protected finite core permits
an infinite sparse deletion. -/
theorem sparseDeletion_of_matchingTendsToInfinityOutsideAlong
    {C S : Set ℕ} {R : SupportFamily} {F : Finset ℕ}
    (hbounded : SupportsBounded R)
    (hmatches : MatchingTendsToInfinityOutsideAlong R F S)
    (hC : ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      HasEventuallySurvivingSupportAlong R B S := by
  classical
  choose T hT using hmatches
  have hstep : ∀ i last, ∃ x ∈ C, x ∉ F ∧
      max (T (i + 1)) (last + 1) ≤ x :=
    fun i last => hC (max (T (i + 1)) (last + 1))
  choose next hnextC hnextF hnext using hstep
  let b : ℕ → ℕ :=
    fun i => Nat.rec (next 0 0) (fun j last => next (j + 1) last) i
  have hbC : ∀ i, b i ∈ C := by
    intro i
    cases i with
    | zero => exact hnextC 0 0
    | succ j => exact hnextC (j + 1) (b j)
  have hbF : ∀ i, b i ∉ F := by
    intro i
    cases i with
    | zero => exact hnextF 0 0
    | succ j => exact hnextF (j + 1) (b j)
  have hbT : ∀ i, T (i + 1) ≤ b i := by
    intro i
    cases i with
    | zero =>
        exact le_trans (le_max_left _ _) (hnext 0 0)
    | succ j =>
        exact le_trans (le_max_left _ _) (hnext (j + 1) (b j))
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact lt_of_lt_of_le (Nat.lt_succ_self _) <|
      le_trans (le_max_right _ _) (hnext (i + 1) (b i))
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbC i
  · rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ hiF
    exact hbF i hiF
  · refine ⟨b 0, ?_⟩
    intro n hn hnS
    have hex : ∃ i, n < b i := by
      refine ⟨n + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (hbmono.id_le (n + 1))
    let dec : DecidablePred (fun i : ℕ => n < b i) :=
      fun i => Nat.decLt n (b i)
    let r : ℕ := @Nat.find (fun i => n < b i) dec hex
    have hnr : n < b r := @Nat.find_spec (fun i => n < b i) dec hex
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr
      rw [hr] at hnr
      exact (not_lt_of_ge hn) hnr
    have hbprev : b (r - 1) ≤ n := by
      letI : Decidable (b (r - 1) ≤ n) := Nat.decLe (b (r - 1)) n
      by_contra hprev
      have hp : n < b (r - 1) := Nat.lt_of_not_ge hprev
      have hmin : r ≤ r - 1 :=
        @Nat.find_min' (fun i => n < b i) dec hex (r - 1) hp
      omega
    have hTr : T r ≤ n := by
      have hr : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
      exact le_trans (hr ▸ hbT (r - 1)) hbprev
    obtain ⟨M, hMR, hrM, _hMnonempty, hMdisj⟩ :=
      hT r n hTr hnS
    let D : Finset ℕ := (Finset.range r).image b
    have hDcard : D.card = r := by
      exact (Finset.card_image_iff.mpr hbmono.injective.injOn).trans
        (Finset.card_range r)
    have hhit :
        ∀ E ∈ M, ¬ Disjoint (E : Set ℕ) B → ∃ x ∈ D, x ∈ E \ F := by
      intro E hEM hEB
      obtain ⟨x, hxE, hxB⟩ := Set.not_disjoint_iff.mp hEB
      obtain ⟨i, rfl⟩ := hxB
      have hbi : b i ≤ n := hbounded n E (hMR hEM) (b i) hxE
      have hir : i < r := by
        by_contra hir
        have hri : r ≤ i := Nat.le_of_not_gt hir
        exact (not_lt_of_ge (le_trans (hbmono.monotone hri) hbi)) hnr
      exact ⟨b i,
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hir, rfl⟩,
        Finset.mem_sdiff.mpr ⟨hxE, hbF i⟩⟩
    obtain ⟨E, hEM, hEB⟩ := exists_surviving_support
      hMdisj hhit (by simpa [hDcard] using hrM)
    exact ⟨E, hMR hEM, hEB⟩

/-- Sparse deletion with cores chosen adaptively against the finite deletion
prefix.  At stage `i`, first choose a core avoiding the preceding points;
then put the new point outside that core and beyond its level-`i+1` matching
threshold.  The core used for an interval consequently avoids every deletion
point that can lie below a target in that interval. -/
theorem sparseDeletion_of_adaptiveCoreMatchingTendsToInfinityOutsideAlong
    {C S : Set ℕ} {R : SupportFamily}
    (hbounded : SupportsBounded R)
    (hadaptive : AdaptiveCoreMatchingTendsToInfinityOutsideAlong R S)
    (hC : ∀ F : Finset ℕ, ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧
      HasEventuallySurvivingSupportAlong R B S := by
  classical
  let State := Finset ℕ × ℕ
  let initial : State := (∅, 0)
  let chooseStep : (i : ℕ) → (s : State) →
      AdaptiveSparseDeletionStep R C S s.1 (i + 1) s.2 :=
    fun i s => Classical.choice
      (adaptiveSparseDeletionStep_nonempty hadaptive hC s.1 (i + 1) s.2)
  let advance : ℕ → State → State := fun i s =>
    (insert (chooseStep i s).point s.1, (chooseStep i s).point)
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun j s => advance j s) i
  let witness (i : ℕ) := chooseStep i (state i)
  let used (i : ℕ) : Finset ℕ := (state i).1
  let b (i : ℕ) : ℕ := (witness i).point
  let core (i : ℕ) : Finset ℕ := (witness i).core
  let threshold (i : ℕ) : ℕ := (witness i).threshold
  have hstate_succ : ∀ i, state (i + 1) = advance i (state i) := by
    intro i
    simp [state]
  have hused_succ : ∀ i, used (i + 1) = insert (b i) (used i) := by
    intro i
    change (state (i + 1)).1 =
      insert (chooseStep i (state i)).point (state i).1
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).2 = b i := by
    intro i
    change (state (i + 1)).2 = (chooseStep i (state i)).point
    rw [hstate_succ]
  have hused_step : ∀ i, used i ⊆ used (i + 1) := by
    intro i
    rw [hused_succ]
    exact Finset.subset_insert _ _
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hb_into_next : ∀ i, b i ∈ used (i + 1) := by
    intro i
    rw [hused_succ]
    exact Finset.mem_insert_self _ _
  have hcore_disjoint_next : ∀ i, Disjoint (core i) (used (i + 1)) := by
    intro i
    rw [hused_succ, Finset.disjoint_left]
    intro x hxCore hxUsed
    obtain rfl | hxOld := Finset.mem_insert.mp hxUsed
    · exact (witness i).point_outside_core hxCore
    · exact Finset.disjoint_left.mp (witness i).core_disjoint hxCore hxOld
  have hbC : ∀ i, b i ∈ C := fun i => (witness i).point_mem
  have hthreshold_b : ∀ i, threshold i ≤ b i := by
    intro i
    exact le_trans (le_max_left _ _) (witness i).point_lower
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower : (state (i + 1)).2 + 1 ≤ b (i + 1) :=
      le_trans (le_max_right _ _) (witness (i + 1)).point_lower
    rw [hlast_succ] at hlower
    exact Nat.lt_of_succ_le hlower
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbC i
  · refine ⟨b 0, ?_⟩
    intro n hn hnS
    have hex : ∃ i, n < b i := by
      refine ⟨n + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (hbmono.id_le (n + 1))
    let dec : DecidablePred (fun i : ℕ => n < b i) :=
      fun i => Nat.decLt n (b i)
    let r : ℕ := @Nat.find (fun i => n < b i) dec hex
    have hnr : n < b r := @Nat.find_spec (fun i => n < b i) dec hex
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr
      rw [hr] at hnr
      exact (not_lt_of_ge hn) hnr
    have hbprev : b (r - 1) ≤ n := by
      letI : Decidable (b (r - 1) ≤ n) := Nat.decLe (b (r - 1)) n
      by_contra hprev
      have hp : n < b (r - 1) := Nat.lt_of_not_ge hprev
      have hmin : r ≤ r - 1 :=
        @Nat.find_min' (fun i => n < b i) dec hex (r - 1) hp
      omega
    have hrEq : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
    have hTr : threshold (r - 1) ≤ n :=
      le_trans (hthreshold_b (r - 1)) hbprev
    obtain ⟨M, hMR, hrM, _hMnonempty, hMdisj⟩ :=
      (witness (r - 1)).matching n hTr hnS
    rw [hrEq] at hrM
    let D : Finset ℕ := (Finset.range r).image b
    have hDcard : D.card = r := by
      exact (Finset.card_image_iff.mpr hbmono.injective.injOn).trans
        (Finset.card_range r)
    have hprefixUsed : ∀ i < r, b i ∈ used r := by
      intro i hir
      exact hused_mono (Nat.succ_le_of_lt hir) (hb_into_next i)
    have hprefixCore : ∀ i < r, b i ∉ core (r - 1) := by
      intro i hir hbiCore
      have hdisj : Disjoint (core (r - 1)) (used r) := by
        rw [← hrEq]
        exact hcore_disjoint_next (r - 1)
      exact Finset.disjoint_left.mp hdisj hbiCore (hprefixUsed i hir)
    have hhit :
        ∀ E ∈ M, ¬ Disjoint (E : Set ℕ) B →
          ∃ x ∈ D, x ∈ E \ core (r - 1) := by
      intro E hEM hEB
      obtain ⟨x, hxE, hxB⟩ := Set.not_disjoint_iff.mp hEB
      obtain ⟨i, rfl⟩ := hxB
      have hbi : b i ≤ n := hbounded n E (hMR hEM) (b i) hxE
      have hir : i < r := by
        by_contra hir
        have hri : r ≤ i := Nat.le_of_not_gt hir
        exact (not_lt_of_ge (le_trans (hbmono.monotone hri) hbi)) hnr
      exact ⟨b i,
        Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hir, rfl⟩,
        Finset.mem_sdiff.mpr ⟨hxE, hprefixCore i hir⟩⟩
    obtain ⟨E, hEM, hEB⟩ := exists_surviving_support
      hMdisj hhit (by simpa [hDcard] using hrM)
    exact ⟨E, hMR hEM, hEB⟩

/-- Finite-menu version of adaptive sparse deletion.  Each target class may
use a different core at a stage; the next deletion point is selected outside
the union of all of them. -/
theorem sparseDeletion_of_finiteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong
    {ι : Type*} [Fintype ι]
    {C : Set ℕ} {S : ι → Set ℕ} {R : SupportFamily}
    (hbounded : SupportsBounded R)
    (hadaptive :
      FiniteMenuAdaptiveCoreMatchingTendsToInfinityOutsideAlong R S)
    (hC : ∀ F : Finset ℕ, ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧
      HasEventuallySurvivingSupportAlong R B {n | ∃ i, n ∈ S i} := by
  classical
  let State := Finset ℕ × ℕ
  let initial : State := (∅, 0)
  let chooseStep : (m : ℕ) → (s : State) →
      FiniteMenuAdaptiveSparseDeletionStep R C S s.1 (m + 1) s.2 :=
    fun m s => Classical.choice
      (finiteMenuAdaptiveSparseDeletionStep_nonempty
        hadaptive hC s.1 (m + 1) s.2)
  let advance : ℕ → State → State := fun m s =>
    (insert (chooseStep m s).point s.1, (chooseStep m s).point)
  let state : ℕ → State := fun m =>
    Nat.rec initial (fun i s => advance i s) m
  let witness (m : ℕ) := chooseStep m (state m)
  let used (m : ℕ) : Finset ℕ := (state m).1
  let b (m : ℕ) : ℕ := (witness m).point
  let core (m : ℕ) (i : ι) : Finset ℕ := (witness m).core i
  let threshold (m : ℕ) (i : ι) : ℕ := (witness m).threshold i
  have hstate_succ : ∀ m, state (m + 1) = advance m (state m) := by
    intro m
    simp [state]
  have hused_succ : ∀ m, used (m + 1) = insert (b m) (used m) := by
    intro m
    change (state (m + 1)).1 =
      insert (chooseStep m (state m)).point (state m).1
    rw [hstate_succ]
  have hlast_succ : ∀ m, (state (m + 1)).2 = b m := by
    intro m
    change (state (m + 1)).2 = (chooseStep m (state m)).point
    rw [hstate_succ]
  have hused_step : ∀ m, used m ⊆ used (m + 1) := by
    intro m
    rw [hused_succ]
    exact Finset.subset_insert _ _
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hb_into_next : ∀ m, b m ∈ used (m + 1) := by
    intro m
    rw [hused_succ]
    exact Finset.mem_insert_self _ _
  have hcore_disjoint_next :
      ∀ m i, Disjoint (core m i) (used (m + 1)) := by
    intro m i
    rw [hused_succ, Finset.disjoint_left]
    intro x hxCore hxUsed
    obtain rfl | hxOld := Finset.mem_insert.mp hxUsed
    · exact (witness m).point_outside_core i hxCore
    · exact Finset.disjoint_left.mp
        ((witness m).core_disjoint i) hxCore hxOld
  have hbC : ∀ m, b m ∈ C := fun m => (witness m).point_mem
  have hthreshold_b : ∀ m i, threshold m i ≤ b m := by
    intro m i
    exact le_trans
      (Finset.le_sup (f := (witness m).threshold) (Finset.mem_univ i))
      (le_trans (le_max_left _ _) (witness m).point_lower)
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro m
    have hlower : (state (m + 1)).2 + 1 ≤ b (m + 1) :=
      le_trans (le_max_right _ _) (witness (m + 1)).point_lower
    rw [hlast_succ] at hlower
    exact Nat.lt_of_succ_le hlower
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact hbC m
  · refine ⟨b 0, ?_⟩
    intro n hn hnS
    obtain ⟨i, hni⟩ := hnS
    have hex : ∃ m, n < b m := by
      refine ⟨n + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (hbmono.id_le (n + 1))
    let dec : DecidablePred (fun m : ℕ => n < b m) :=
      fun m => Nat.decLt n (b m)
    let r : ℕ := @Nat.find (fun m => n < b m) dec hex
    have hnr : n < b r := @Nat.find_spec (fun m => n < b m) dec hex
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr
      rw [hr] at hnr
      exact (not_lt_of_ge hn) hnr
    have hbprev : b (r - 1) ≤ n := by
      letI : Decidable (b (r - 1) ≤ n) := Nat.decLe (b (r - 1)) n
      by_contra hprev
      have hp : n < b (r - 1) := Nat.lt_of_not_ge hprev
      have hmin : r ≤ r - 1 :=
        @Nat.find_min' (fun m => n < b m) dec hex (r - 1) hp
      omega
    have hrEq : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
    have hTr : threshold (r - 1) i ≤ n :=
      le_trans (hthreshold_b (r - 1) i) hbprev
    obtain ⟨M, hMR, hrM, _hMnonempty, hMdisj⟩ :=
      (witness (r - 1)).matching i n hTr hni
    rw [hrEq] at hrM
    let D : Finset ℕ := (Finset.range r).image b
    have hDcard : D.card = r := by
      exact (Finset.card_image_iff.mpr hbmono.injective.injOn).trans
        (Finset.card_range r)
    have hprefixUsed : ∀ m < r, b m ∈ used r := by
      intro m hmr
      exact hused_mono (Nat.succ_le_of_lt hmr) (hb_into_next m)
    have hprefixCore : ∀ m < r, b m ∉ core (r - 1) i := by
      intro m hmr hbmCore
      have hdisj : Disjoint (core (r - 1) i) (used r) := by
        rw [← hrEq]
        exact hcore_disjoint_next (r - 1) i
      exact Finset.disjoint_left.mp hdisj hbmCore (hprefixUsed m hmr)
    have hhit :
        ∀ E ∈ M, ¬ Disjoint (E : Set ℕ) B →
          ∃ x ∈ D, x ∈ E \ core (r - 1) i := by
      intro E hEM hEB
      obtain ⟨x, hxE, hxB⟩ := Set.not_disjoint_iff.mp hEB
      obtain ⟨m, rfl⟩ := hxB
      have hbm : b m ≤ n := hbounded n E (hMR hEM) (b m) hxE
      have hmr : m < r := by
        by_contra hmr
        have hrm : r ≤ m := Nat.le_of_not_gt hmr
        exact (not_lt_of_ge (le_trans (hbmono.monotone hrm) hbm)) hnr
      exact ⟨b m,
        Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmr, rfl⟩,
        Finset.mem_sdiff.mpr ⟨hxE, hprefixCore m hmr⟩⟩
    obtain ⟨E, hEM, hEB⟩ := exists_surviving_support
      hMdisj hhit (by simpa [hDcard] using hrM)
    exact ⟨E, hMR hEM, hEB⟩

/-- Two disjoint repairs avoiding every finite prefix suffice for sparse
deletion.  At a stage, choose the next deletion point beyond the repair
threshold.  For a target before the following deletion point, all later
points are too large, all earlier points are already avoided, and the newest
point can meet at most one of the two disjoint repairs. -/
theorem sparseDeletion_of_twoRepairsDisjointOnDeletionReservoirAlong
    {C S : Set ℕ} {R : SupportFamily}
    (hbounded : SupportsBounded R)
    (hrepairs : HasTwoRepairsDisjointOnDeletionReservoirAlong R C S)
    (hC : ∀ T, ∃ b ∈ C, T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧
      HasEventuallySurvivingSupportAlong R B S := by
  classical
  let State := {p : Finset ℕ × ℕ // (p.1 : Set ℕ) ⊆ C}
  let initial : State := ⟨(∅, 0), by simp⟩
  let chooseStep : (s : State) →
      TwoRepairSparseDeletionStep R C S s.1.1 s.1.2 := fun s =>
    Classical.choice
      (twoRepairSparseDeletionStep_nonempty
        hrepairs hC s.1.1 s.2 s.1.2)
  let advance : State → State := fun s =>
    ⟨(insert (chooseStep s).point s.1.1, (chooseStep s).point), by
      intro x hx
      obtain rfl | hxOld := Finset.mem_insert.mp hx
      · exact (chooseStep s).point_mem
      · exact s.2 hxOld⟩
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let witness (i : ℕ) := chooseStep (state i)
  let used (i : ℕ) : Finset ℕ := (state i).1.1
  let b (i : ℕ) : ℕ := (witness i).point
  let threshold (i : ℕ) : ℕ := (witness i).threshold
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hused_succ : ∀ i, used (i + 1) = insert (b i) (used i) := by
    intro i
    change (state (i + 1)).1.1 =
      insert (chooseStep (state i)).point (state i).1.1
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).1.2 = b i := by
    intro i
    change (state (i + 1)).1.2 = (chooseStep (state i)).point
    rw [hstate_succ]
  have hused_step : ∀ i, used i ⊆ used (i + 1) := by
    intro i
    rw [hused_succ]
    exact Finset.subset_insert _ _
  have hused_mono : Monotone used :=
    monotone_nat_of_le_succ hused_step
  have hb_into_next : ∀ i, b i ∈ used (i + 1) := by
    intro i
    rw [hused_succ]
    exact Finset.mem_insert_self _ _
  have hbC : ∀ i, b i ∈ C := fun i => (witness i).point_mem
  have hthreshold_b : ∀ i, threshold i ≤ b i := by
    intro i
    exact le_trans (le_max_left _ _) (witness i).point_lower
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro i
    have hlower : (state (i + 1)).1.2 + 1 ≤ b (i + 1) :=
      le_trans (le_max_right _ _) (witness (i + 1)).point_lower
    rw [hlast_succ] at hlower
    exact Nat.lt_of_succ_le hlower
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbC i
  · refine ⟨b 0, ?_⟩
    intro n hn hnS
    have hex : ∃ i, n < b i := by
      refine ⟨n + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (hbmono.id_le (n + 1))
    let dec : DecidablePred (fun i : ℕ => n < b i) :=
      fun i => Nat.decLt n (b i)
    let r : ℕ := @Nat.find (fun i => n < b i) dec hex
    have hnr : n < b r := @Nat.find_spec (fun i => n < b i) dec hex
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr
      rw [hr] at hnr
      exact (not_lt_of_ge hn) hnr
    have hbprev : b (r - 1) ≤ n := by
      letI : Decidable (b (r - 1) ≤ n) := Nat.decLe (b (r - 1)) n
      by_contra hprev
      have hp : n < b (r - 1) := Nat.lt_of_not_ge hprev
      have hmin : r ≤ r - 1 :=
        @Nat.find_min' (fun i => n < b i) dec hex (r - 1) hp
      omega
    have hTr : threshold (r - 1) ≤ n :=
      le_trans (hthreshold_b (r - 1)) hbprev
    obtain ⟨E, hER, hEold, E', hE'R, hE'old, hEE'⟩ :=
      (witness (r - 1)).repairs n hTr hnS
    have hfinish : ∀ G : Finset ℕ,
        G ∈ R n → Disjoint G (used (r - 1)) →
        b (r - 1) ∉ G →
        ∃ H ∈ R n, Disjoint (H : Set ℕ) B := by
      intro G hGR hGold hbG
      refine ⟨G, hGR, ?_⟩
      rw [Set.disjoint_left]
      intro x hxG hxB
      obtain ⟨i, rfl⟩ := hxB
      have hbi : b i ≤ n := hbounded n G hGR (b i) hxG
      have hir : i < r := by
        by_contra hir
        have hri : r ≤ i := Nat.le_of_not_gt hir
        exact (not_lt_of_ge (le_trans (hbmono.monotone hri) hbi)) hnr
      by_cases hi : i = r - 1
      · subst i
        exact hbG hxG
      · have hiold : i < r - 1 := by omega
        have hbiUsed : b i ∈ used (r - 1) :=
          hused_mono (Nat.succ_le_of_lt hiold) (hb_into_next i)
        exact Finset.disjoint_left.mp hGold hxG hbiUsed
    by_cases hbE : b (r - 1) ∈ E
    · have hbE' : b (r - 1) ∉ E' := by
        intro hbE'
        exact Set.disjoint_left.mp hEE'
          ⟨Finset.mem_coe.mpr hbE, hbC (r - 1)⟩
          ⟨Finset.mem_coe.mpr hbE', hbC (r - 1)⟩
      exact hfinish E' hE'R hE'old hbE'
    · exact hfinish E hER hEold hbE

/-- Full disjointness is a convenient stronger hypothesis for the
reservoir-relative sparse-deletion theorem. -/
theorem sparseDeletion_of_twoDisjointRepairsAvoidingFinitePrefixesAlong
    {C S : Set ℕ} {R : SupportFamily}
    (hbounded : SupportsBounded R)
    (hrepairs : HasTwoDisjointRepairsAvoidingFinitePrefixesAlong R C S)
    (hC : ∀ T, ∃ b ∈ C, T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧
      HasEventuallySurvivingSupportAlong R B S :=
  sparseDeletion_of_twoRepairsDisjointOnDeletionReservoirAlong
    hbounded hrepairs.onDeletionReservoir hC

/- Countable fusion with one common protected core.  At stage `m` the new
deleted vertex is placed beyond the matching thresholds for the first
`m + 1` target sets, each at matching size `m + 1`.  Thus every fixed target
set eventually sees exactly the same sparse-deletion argument as in the
single-set theorem. -/
theorem sparseDeletion_of_countable_matchingTendsToInfinityOutsideAlong
    {C : Set ℕ} {S : ℕ → Set ℕ} {R : SupportFamily} {F : Finset ℕ}
    (hbounded : SupportsBounded R)
    (hmatches : ∀ i,
      MatchingTendsToInfinityOutsideAlong R F (S i))
    (hC : ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      ∀ i, HasEventuallySurvivingSupportAlong R B (S i) := by
  classical
  have hthreshold : ∀ i j, ∃ T, ∀ n ≥ T, n ∈ S i →
      ∃ M : Finset (Finset ℕ),
        M ⊆ R n ∧ j < M.card ∧
          (∀ E ∈ M, (E \ F).Nonempty) ∧
          ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
            Disjoint (E \ F) (E' \ F) :=
    fun i j => hmatches i j
  choose T hT using hthreshold
  let stageThreshold (m : ℕ) : ℕ :=
    (Finset.range (m + 1)).sup fun i => T i (m + 1)
  have hstep : ∀ m last, ∃ x ∈ C, x ∉ F ∧
      max (stageThreshold m) (last + 1) ≤ x :=
    fun m last => hC (max (stageThreshold m) (last + 1))
  choose next hnextC hnextF hnext using hstep
  let b : ℕ → ℕ :=
    fun i => Nat.rec (next 0 0) (fun j last => next (j + 1) last) i
  have hbC : ∀ i, b i ∈ C := by
    intro i
    cases i with
    | zero => exact hnextC 0 0
    | succ j => exact hnextC (j + 1) (b j)
  have hbF : ∀ i, b i ∉ F := by
    intro i
    cases i with
    | zero => exact hnextF 0 0
    | succ j => exact hnextF (j + 1) (b j)
  have hbStage : ∀ m, stageThreshold m ≤ b m := by
    intro m
    cases m with
    | zero => exact le_trans (le_max_left _ _) (hnext 0 0)
    | succ j => exact le_trans (le_max_left _ _) (hnext (j + 1) (b j))
  have hbT : ∀ m i, i ≤ m → T i (m + 1) ≤ b m := by
    intro m i him
    exact le_trans
      (Finset.le_sup
        (f := fun i => T i (m + 1))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le him)))
      (hbStage m)
  have hbmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact lt_of_lt_of_le (Nat.lt_succ_self _) <|
      le_trans (le_max_right _ _) (hnext (i + 1) (b i))
  let B : Set ℕ := Set.range b
  refine ⟨B, ?_, Set.infinite_range_of_injective hbmono.injective, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact hbC i
  · rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ hiF
    exact hbF i hiF
  · intro i
    refine ⟨b i, ?_⟩
    intro n hn hnS
    have hex : ∃ r, n < b r := by
      refine ⟨n + 1, ?_⟩
      exact lt_of_lt_of_le (Nat.lt_succ_self n) (hbmono.id_le (n + 1))
    let dec : DecidablePred (fun r : ℕ => n < b r) :=
      fun r => Nat.decLt n (b r)
    let r : ℕ := @Nat.find (fun r => n < b r) dec hex
    have hnr : n < b r := @Nat.find_spec (fun r => n < b r) dec hex
    have hir : i < r := by
      by_contra hir
      have hri : r ≤ i := Nat.le_of_not_gt hir
      exact (not_lt_of_ge (le_trans (hbmono.monotone hri) hn)) hnr
    have hrpos : 0 < r := lt_of_le_of_lt (Nat.zero_le i) hir
    have hbprev : b (r - 1) ≤ n := by
      letI : Decidable (b (r - 1) ≤ n) := Nat.decLe (b (r - 1)) n
      by_contra hprev
      have hp : n < b (r - 1) := Nat.lt_of_not_ge hprev
      have hmin : r ≤ r - 1 :=
        @Nat.find_min' (fun r => n < b r) dec hex (r - 1) hp
      omega
    have hirprev : i ≤ r - 1 := by omega
    have hTr : T i r ≤ n := by
      have hr : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
      exact le_trans (hr ▸ hbT (r - 1) i hirprev) hbprev
    obtain ⟨M, hMR, hrM, _hMnonempty, hMdisj⟩ :=
      hT i r n hTr hnS
    let D : Finset ℕ := (Finset.range r).image b
    have hDcard : D.card = r := by
      exact (Finset.card_image_iff.mpr hbmono.injective.injOn).trans
        (Finset.card_range r)
    have hhit :
        ∀ E ∈ M, ¬ Disjoint (E : Set ℕ) B → ∃ x ∈ D, x ∈ E \ F := by
      intro E hEM hEB
      obtain ⟨x, hxE, hxB⟩ := Set.not_disjoint_iff.mp hEB
      obtain ⟨j, rfl⟩ := hxB
      have hbj : b j ≤ n := hbounded n E (hMR hEM) (b j) hxE
      have hjr : j < r := by
        by_contra hjr
        have hrj : r ≤ j := Nat.le_of_not_gt hjr
        exact (not_lt_of_ge (le_trans (hbmono.monotone hrj) hbj)) hnr
      exact ⟨b j,
        Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjr, rfl⟩,
        Finset.mem_sdiff.mpr ⟨hxE, hbF j⟩⟩
    obtain ⟨E, hEM, hEB⟩ := exists_surviving_support
      hMdisj hhit (by simpa [hDcard] using hrM)
    exact ⟨E, hMR hEM, hEB⟩

/- The unrestricted sparse-deletion theorem is the special case `S = univ`. -/
theorem sparseDeletion_of_matchingTendsToInfinityOutside
    {C : Set ℕ} {R : SupportFamily} {F : Finset ℕ}
    (hbounded : SupportsBounded R)
    (hmatches : MatchingTendsToInfinityOutside R F)
    (hC : ∀ T, ∃ b ∈ C, b ∉ F ∧ T ≤ b) :
    ∃ B ⊆ C, B.Infinite ∧ Disjoint B (F : Set ℕ) ∧
      HasEventuallySurvivingSupport R B := by
  have hmAlong :
      MatchingTendsToInfinityOutsideAlong R F Set.univ := by
    intro j
    obtain ⟨T, hT⟩ := hmatches j
    exact ⟨T, fun n hn _hnuniv => hT n hn⟩
  obtain ⟨B, hBC, hB, hBF, N, hN⟩ :=
    sparseDeletion_of_matchingTendsToInfinityOutsideAlong
      hbounded hmAlong hC
  exact ⟨B, hBC, hB, hBF, N,
    fun n hn => hN n hn (Set.mem_univ n)⟩

/-! ## Private-witness counterexample criterion -/

/-- Proposition 10, isolated as a quantifier lemma. -/
theorem privateWitnesses_defeat_every_infinite_deletion
    {A A₀ : Set ℕ} {k : ℕ} {w : ℕ → ℕ → ℕ}
    (hcofinite : (A \ A₀).Finite)
    (hprivate : ∀ a ∈ A₀, ∀ h ∈ ({k, k + 1} : Set ℕ),
      IsPrivateWitness A h a (w h a))
    (hproper : ∀ h ∈ ({k, k + 1} : Set ℕ), ∀ M,
      Set.Finite {a | a ∈ A₀ ∧ w h a ≤ M}) :
    ∀ B ⊆ A, B.Infinite →
      ∀ h ∈ ({k, k + 1} : Set ℕ), ¬ IsAsymptoticBasis (A \ B) h := by
  intro B hBA hB h hh hbasis
  have hBA₀ : (B ∩ A₀).Infinite := by
    apply (hB.diff hcofinite).mono
    intro x hx
    refine ⟨hx.1, ?_⟩
    by_contra hxA₀
    exact hx.2 ⟨hBA hx.1, hxA₀⟩
  obtain ⟨N, hN⟩ := hbasis
  have hfinite := hproper h hh N
  have hnsub :
      ¬ B ∩ A₀ ⊆ {a | a ∈ A₀ ∧ w h a ≤ N} := by
    intro hsub
    exact hBA₀ (hfinite.subset hsub)
  obtain ⟨a, ⟨haB, haA₀⟩, habad⟩ := Set.not_subset.mp hnsub
  have hNa : N < w h a := by
    exact Nat.lt_of_not_ge fun hle => habad ⟨haA₀, hle⟩
  rcases hprivate a haA₀ h hh with ⟨_, hno⟩
  apply hno
  obtain ⟨xs, hxs⟩ := hN (w h a) hNa.le
  refine ⟨xs, hxs.1, ?_, hxs.2.2⟩
  intro x hx
  refine ⟨(hxs.2.1 x hx).1, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hxa
  subst x
  exact (hxs.2.1 a hx).2 haB

end Erdos881
