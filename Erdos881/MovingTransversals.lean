import Erdos881.FiniteBlocks
import Erdos881.ChoiceUnion

/-!
# Bounded moving transversals

This file states the moving-core obstruction and its descent from order
`k + 1` to order `k` at the level of finite support hypergraphs.  It also
records, in exact quantifier form, the additional statement still needed to
obtain a removable block selector.
-/

namespace Erdos881

/-! ## Failure of finite-core matching -/

/-- Every support is nonempty. -/
def SupportsNonempty (R : SupportFamily) : Prop :=
  ∀ n E, E ∈ R n → E.Nonempty

/-- Every support has cardinality at most `r`. -/
def SupportsCardAtMost (R : SupportFamily) (r : ℕ) : Prop :=
  ∀ n E, E ∈ R n → E.card ≤ r

/-- The distinct nonempty outside-core supports at `n`. -/
def outsideSupportHypergraph
    (R : SupportFamily) (F : Finset ℕ) (n : ℕ) :
    Finset (Finset ℕ) :=
  ((R n).image fun E => E \ F).erase ∅

/-- Pointwise form of the maximum-matching conversion.  A large matching in
the outside-support hypergraph is equivalent to a family of original supports
whose nonempty outside parts are pairwise disjoint. -/
theorem lt_matchingNumber_outsideSupportHypergraph_iff
    {R : SupportFamily} {F : Finset ℕ} {n j : ℕ} :
    j < matchingNumber (outsideSupportHypergraph R F n) ↔
      ∃ M : Finset (Finset ℕ),
        M ⊆ R n ∧ j < M.card ∧
          (∀ E ∈ M, (E \ F).Nonempty) ∧
          ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
            Disjoint (E \ F) (E' \ F) := by
  classical
  let H := outsideSupportHypergraph R F n
  have hHnonempty : ∀ D ∈ H, D.Nonempty := by
    intro D hDH
    exact Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hDH).1
  constructor
  · intro hlarge
    obtain ⟨D, hDH, hDmatching, hDcard, _hDmax⟩ :=
      exists_maximumMatching hHnonempty
    have hex :
        ∀ d : {d // d ∈ D},
          ∃ E : Finset ℕ, E ∈ R n ∧ E \ F = d.1 := by
      intro d
      have hdH : d.1 ∈ H := hDH d.2
      obtain ⟨E, hER, hEF⟩ :=
        Finset.mem_image.mp (Finset.mem_erase.mp hdH).2
      exact ⟨E, hER, hEF⟩
    choose lift hliftR hlift using hex
    have hlift_injective : Function.Injective lift := by
      intro d d' hdd'
      apply Subtype.ext
      rw [← hlift d, ← hlift d', hdd']
    let M : Finset (Finset ℕ) := D.attach.image lift
    have hMcard : M.card = D.card := by
      change (D.attach.image lift).card = D.card
      rw [Finset.card_image_iff.mpr hlift_injective.injOn,
        Finset.card_attach]
    have hMR : M ⊆ R n := by
      intro E hEM
      obtain ⟨d, _hdD, rfl⟩ := Finset.mem_image.mp hEM
      exact hliftR d
    have hMnonempty : ∀ E ∈ M, (E \ F).Nonempty := by
      intro E hEM
      obtain ⟨d, _hdD, rfl⟩ := Finset.mem_image.mp hEM
      rw [hlift d]
      exact hHnonempty d.1 (hDH d.2)
    have hMdisjoint :
        ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
          Disjoint (E \ F) (E' \ F) := by
      intro E hEM E' hE'M hEE'
      obtain ⟨d, _hdD, rfl⟩ := Finset.mem_image.mp hEM
      obtain ⟨d', _hd'D, rfl⟩ := Finset.mem_image.mp hE'M
      have hdd' : d ≠ d' := by
        intro hdd'
        apply hEE'
        exact congrArg lift hdd'
      rw [hlift d, hlift d']
      exact hDmatching d.2 d'.2
        (fun hval => hdd' (Subtype.ext hval))
    refine ⟨M, hMR, ?_, hMnonempty, hMdisjoint⟩
    rw [hMcard, hDcard]
    exact hlarge
  · rintro ⟨M, hMR, hlarge, hnonempty, hdisjoint⟩
    let outside : Finset ℕ → Finset ℕ := fun E => E \ F
    have houtside_inj : Set.InjOn outside (M : Set (Finset ℕ)) := by
      intro E hEM E' hE'M heq
      by_contra hEE'
      obtain ⟨x, hx⟩ := hnonempty E hEM
      have hx' : x ∈ outside E' := by
        rw [← heq]
        exact hx
      exact Finset.disjoint_left.mp
        (hdisjoint E hEM E' hE'M hEE') hx hx'
    let D : Finset (Finset ℕ) := M.image outside
    have hDcard : D.card = M.card :=
      Finset.card_image_iff.mpr houtside_inj
    have hDsub : D ⊆ outsideSupportHypergraph R F n := by
      intro d hdD
      obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hdD
      apply Finset.mem_erase.mpr
      exact ⟨Finset.nonempty_iff_ne_empty.mp (hnonempty E hEM),
        Finset.mem_image.mpr ⟨E, hMR hEM, rfl⟩⟩
    have hDmatching : IsMatching D := by
      intro d hdD d' hdD' hdd'
      obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hdD
      obtain ⟨E', hE'M, rfl⟩ := Finset.mem_image.mp hdD'
      apply hdisjoint E hEM E' hE'M
      intro hEE'
      subst E'
      exact hdd' rfl
    exact lt_of_lt_of_le (hDcard ▸ hlarge)
      (card_le_matchingNumber hDsub hDmatching)

/-- Matching growth outside a fixed finite core, expressed using the actual
finite matching number. -/
def OutsideMatchingTendsToInfinity
    (R : SupportFamily) (F : Finset ℕ) : Prop :=
  ∀ j, ∃ N, ∀ n, N ≤ n →
    j < matchingNumber (outsideSupportHypergraph R F n)

/- Matching growth relative to a prescribed set of targets.  The membership
premise is inside the eventual quantifier, so negating this property produces
arbitrarily large bad targets which still belong to `S`. -/
def OutsideMatchingTendsToInfinityAlong
    (R : SupportFamily) (F : Finset ℕ) (S : Set ℕ) : Prop :=
  ∀ j, ∃ N, ∀ n, N ≤ n → n ∈ S →
    j < matchingNumber (outsideSupportHypergraph R F n)

/-- The maximum-matching formulation supplies the explicit families of
supports required by the sparse-deletion theorem. -/
theorem matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong
    {R : SupportFamily} {F : Finset ℕ} {S : Set ℕ}
    (hgrowth : OutsideMatchingTendsToInfinityAlong R F S) :
    MatchingTendsToInfinityOutsideAlong R F S := by
  classical
  intro j
  obtain ⟨N, hN⟩ := hgrowth j
  refine ⟨N, ?_⟩
  intro n hn hnS
  let H := outsideSupportHypergraph R F n
  have hHnonempty : ∀ D ∈ H, D.Nonempty := by
    intro D hDH
    exact Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hDH).1
  obtain ⟨D, hDH, hDmatching, hDcard, _hDmax⟩ :=
    exists_maximumMatching hHnonempty
  have hex :
      ∀ d : {d // d ∈ D},
        ∃ E : Finset ℕ, E ∈ R n ∧ E \ F = d.1 := by
    intro d
    have hdH : d.1 ∈ H := hDH d.2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hdH).2
    exact ⟨E, hER, hEF⟩
  choose lift hliftR hlift using hex
  have hlift_injective : Function.Injective lift := by
    intro d d' hdd'
    apply Subtype.ext
    rw [← hlift d, ← hlift d', hdd']
  let M : Finset (Finset ℕ) := D.attach.image lift
  have hMcard : M.card = D.card := by
    change (D.attach.image lift).card = D.card
    rw [Finset.card_image_iff.mpr hlift_injective.injOn,
      Finset.card_attach]
  have hMR : M ⊆ R n := by
    intro E hEM
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp hEM
    exact hliftR d
  have hMnonempty : ∀ E ∈ M, (E \ F).Nonempty := by
    intro E hEM
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp hEM
    rw [hlift d]
    exact hHnonempty d.1 (hDH d.2)
  have hMdisjoint :
      ∀ E ∈ M, ∀ E' ∈ M, E ≠ E' →
        Disjoint (E \ F) (E' \ F) := by
    intro E hEM E' hE'M hEE'
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp hEM
    obtain ⟨d', hd'D, rfl⟩ := Finset.mem_image.mp hE'M
    have hdd' : d ≠ d' := by
      intro hdd'
      apply hEE'
      exact congrArg lift hdd'
    rw [hlift d, hlift d']
    exact hDmatching d.2 d'.2
      (fun hval => hdd' (Subtype.ext hval))
  refine ⟨M, hMR, ?_, hMnonempty, hMdisjoint⟩
  rw [hMcard, hDcard]
  exact hN n hn hnS

/- Conversely, an explicit outside-core matching gives a matching of the
outside support hypergraph by mapping every support to its nonempty outside
part.  Pairwise disjoint nonempty outside parts are automatically distinct,
so cardinality is preserved. -/
theorem outsideMatchingTendsToInfinityAlong_of_matchingTendsToInfinityOutsideAlong
    {R : SupportFamily} {F : Finset ℕ} {S : Set ℕ}
    (hmatches : MatchingTendsToInfinityOutsideAlong R F S) :
    OutsideMatchingTendsToInfinityAlong R F S := by
  classical
  intro j
  obtain ⟨N, hN⟩ := hmatches j
  refine ⟨N, ?_⟩
  intro n hn hnS
  obtain ⟨M, hMR, hlarge, hnonempty, hdisjoint⟩ :=
    hN n hn hnS
  let outside : Finset ℕ → Finset ℕ := fun E => E \ F
  have houtside_inj : Set.InjOn outside (M : Set (Finset ℕ)) := by
    intro E hEM E' hE'M heq
    by_contra hEE'
    obtain ⟨x, hx⟩ := hnonempty E hEM
    have hx' : x ∈ outside E' := by
      rw [← heq]
      exact hx
    exact Finset.disjoint_left.mp
      (hdisjoint E hEM E' hE'M hEE') hx hx'
  let D : Finset (Finset ℕ) := M.image outside
  have hDcard : D.card = M.card :=
    Finset.card_image_iff.mpr houtside_inj
  have hDsub : D ⊆ outsideSupportHypergraph R F n := by
    intro d hdD
    obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hdD
    apply Finset.mem_erase.mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp (hnonempty E hEM),
      Finset.mem_image.mpr ⟨E, hMR hEM, rfl⟩⟩
  have hDmatching : IsMatching D := by
    intro d hdD d' hdD' hdd'
    obtain ⟨E, hEM, rfl⟩ := Finset.mem_image.mp hdD
    obtain ⟨E', hE'M, rfl⟩ := Finset.mem_image.mp hdD'
    apply hdisjoint E hEM E' hE'M
    intro hEE'
    subst E'
    exact hdd' rfl
  exact lt_of_lt_of_le (hDcard ▸ hlarge)
    (card_le_matchingNumber hDsub hDmatching)

theorem outsideMatchingTendsToInfinityAlong_iff_matchingTendsToInfinityOutsideAlong
    {R : SupportFamily} {F : Finset ℕ} {S : Set ℕ} :
    OutsideMatchingTendsToInfinityAlong R F S ↔
      MatchingTendsToInfinityOutsideAlong R F S :=
  ⟨matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong,
    outsideMatchingTendsToInfinityAlong_of_matchingTendsToInfinityOutsideAlong⟩

/- Maximum-matching growth, like its explicit formulation, survives
enlarging the protected finite core. -/
theorem outsideMatchingTendsToInfinityAlong_mono_core
    {R : SupportFamily} {F G : Finset ℕ} {S : Set ℕ}
    (hFG : F ⊆ G)
    (hgrowth : OutsideMatchingTendsToInfinityAlong R F S) :
    OutsideMatchingTendsToInfinityAlong R G S :=
  outsideMatchingTendsToInfinityAlong_of_matchingTendsToInfinityOutsideAlong <|
    matchingTendsToInfinityOutsideAlong_mono_core hFG <|
      matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong hgrowth

/- The unrestricted maximum-matching conversion is the special case of the
relative theorem with no target restriction. -/
theorem matchingTendsToInfinityOutside_of_outsideMatching
    {R : SupportFamily} {F : Finset ℕ}
    (hgrowth : OutsideMatchingTendsToInfinity R F) :
    MatchingTendsToInfinityOutside R F := by
  have hgrowthAlong :
      OutsideMatchingTendsToInfinityAlong R F Set.univ := by
    intro j
    obtain ⟨N, hN⟩ := hgrowth j
    exact ⟨N, fun n hn _hnuniv => hN n hn⟩
  have hmatches :=
    matchingTendsToInfinityOutsideAlong_of_outsideMatchingAlong
      hgrowthAlong
  intro j
  obtain ⟨N, hN⟩ := hmatches j
  exact ⟨N, fun n hn => hN n hn (Set.mem_univ n)⟩

/-- Failure of finite-core matching growth outside every finite core contained
in the ambient vertex set. -/
def FailsFiniteCoreMatching
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ¬ OutsideMatchingTendsToInfinity R F

/- Failure of matching growth along a target set, outside every finite core. -/
def FailsFiniteCoreMatchingAlong
    (R : SupportFamily) (A S : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ¬ OutsideMatchingTendsToInfinityAlong R F S

/-- The full output of the bounded-matching argument: the moving part `T`
itself meets every nonempty support after the protected core `F` is removed.
This retains more information than merely saying that `F ∪ T` destroys the
target. -/
def HasBoundedMovingOutsideTransversals
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      IsTransversal (outsideSupportHypergraph R F n) T

/- The relative moving-transversal alternative retains membership of every
bad target in `S`; this is the recurrence information lost by the unrestricted
cofinal formulation. -/
def HasBoundedMovingOutsideTransversalsAlong
    (R : SupportFamily) (A S : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧ n ∈ S ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      IsTransversal (outsideSupportHypergraph R F n) T

/-- Outside every finite core, arbitrarily large support hypergraphs have a
transversal consisting of the core plus a uniformly bounded moving part. -/
def HasBoundedMovingTransversals
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      DestroysAt R ((F ∪ T : Finset ℕ) : Set ℕ) n

/-- Every sufficiently late support escapes any prescribed finite core. -/
def SupportsEventuallyEscapeFiniteCores (R : SupportFamily) : Prop :=
  ∀ F : Finset ℕ, ∃ N, ∀ n, N ≤ n →
    ∀ E ∈ R n, (E \ F).Nonempty

/-- Bounded transversals can be chosen arbitrarily far out in the vertex set,
and the moving part alone destroys the selected target. -/
def HasBoundedEscapingTransversals
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      DestroysAt R (T : Set ℕ) n

/-- One nonempty escaping transversal, packaged for recursive constructions. -/
structure EscapingTransversalWitness
    (R : SupportFamily) (A : Set ℕ)
    (F : Finset ℕ) (N : ℕ) where
  n : ℕ
  T : Finset ℕ
  lower : N ≤ n
  subset : ∀ x ∈ T, x ∈ A
  disjoint : Disjoint T F
  nonempty : T.Nonempty
  destroys : DestroysAt R (T : Set ℕ) n

/-- An infinite sequence of pairwise-disjoint nonempty escaping transversals
at strictly increasing targets. -/
structure EscapingTransversalSequence
    (R : SupportFamily) (A : Set ℕ) where
  n : ℕ → ℕ
  T : ℕ → Finset ℕ
  n_strictMono : StrictMono n
  subset : ∀ i x, x ∈ T i → x ∈ A
  disjoint : Pairwise fun i j => Disjoint (T i) (T j)
  nonempty : ∀ i, (T i).Nonempty
  destroys : ∀ i, DestroysAt R (T i : Set ℕ) (n i)

/-- A pointwise bounded-matching conversion which retains that the resulting
outside transversal lies in the ambient vertex set and avoids the core. -/
theorem exists_small_outsideTransversal_of_matchingNumber_le
    {A : Set ℕ} {R : SupportFamily} {F : Finset ℕ} {n r m : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hmatch : matchingNumber (outsideSupportHypergraph R F n) ≤ m) :
    ∃ T : Finset ℕ,
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T F ∧ T.card ≤ r * m ∧
        IsTransversal (outsideSupportHypergraph R F n) T := by
  classical
  let H := outsideSupportHypergraph R F n
  have hHnonempty : ∀ D ∈ H, D.Nonempty := by
    intro D hDH
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hDH).1
  have hHcard : ∀ D ∈ H, D.card ≤ r := by
    intro D hDH
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (hcard n E hER)
  obtain ⟨T₀, hT₀trans, hT₀card⟩ :=
    exists_small_transversal_of_matchingNumber_le
      hHnonempty hHcard hmatch
  let U : Finset ℕ := H.biUnion id
  let T : Finset ℕ := T₀ ∩ U
  have hTtrans : IsTransversal H T := by
    intro D hDH
    obtain ⟨x, hx⟩ := hT₀trans D hDH
    obtain ⟨hxD, hxT₀⟩ := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_inter.mpr ⟨hxD,
      Finset.mem_inter.mpr ⟨hxT₀, ?_⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨D, hDH, hxD⟩
  have hTA : ∀ x ∈ T, x ∈ A := by
    intro x hxT
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    have hxE : x ∈ E := by
      rw [← hEF] at hxD
      exact (Finset.mem_sdiff.mp hxD).1
    exact hRA n E hER x hxE
  have hTF : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, _hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF] at hxD
    exact (Finset.mem_sdiff.mp hxD).2 hxF
  exact ⟨T, hTA, hTF,
    le_trans (Finset.card_le_card Finset.inter_subset_left) hT₀card,
    hTtrans⟩

/-- If a target has no two disjoint supports both avoiding a finite prefix
`D`, then `D` can be extended by at most one support to a transversal.  Pick
one `D`-avoiding support when it exists; every other such support must meet
it. -/
theorem exists_bounded_extensionTransversal_of_no_twoDisjointRepairs
    {A : Set ℕ} {R : SupportFamily} {D : Finset ℕ} {n r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hno : ¬ ∃ E ∈ R n, Disjoint E D ∧
      ∃ E' ∈ R n, Disjoint E' D ∧ Disjoint E E') :
    ∃ T : Finset ℕ,
      (∀ x ∈ T, x ∈ A) ∧ Disjoint T D ∧ T.card ≤ r ∧
        DestroysAt R (((D ∪ T : Finset ℕ) : Set ℕ)) n := by
  classical
  by_cases hex : ∃ E ∈ R n, Disjoint E D
  · obtain ⟨E₀, hE₀R, hE₀D⟩ := hex
    refine ⟨E₀, hRA n E₀ hE₀R, hE₀D,
      hcard n E₀ hE₀R, ?_⟩
    intro E hER
    by_cases hED : Disjoint E D
    · have hnotEE₀ : ¬ Disjoint E E₀ := by
        intro hEE₀
        apply hno
        exact ⟨E, hER, hED, E₀, hE₀R, hE₀D, hEE₀⟩
      obtain ⟨x, hxE, hxE₀⟩ := Finset.not_disjoint_iff.mp hnotEE₀
      exact Set.not_disjoint_iff.mpr
        ⟨x, Finset.mem_coe.mpr hxE,
          Finset.mem_coe.mpr (Finset.mem_union_right D hxE₀)⟩
    · obtain ⟨x, hxE, hxD⟩ := Finset.not_disjoint_iff.mp hED
      exact Set.not_disjoint_iff.mpr
        ⟨x, Finset.mem_coe.mpr hxE,
          Finset.mem_coe.mpr (Finset.mem_union_left E₀ hxD)⟩
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    intro E hER
    have hnotED : ¬ Disjoint E D := by
      intro hED
      exact hex ⟨E, hER, hED⟩
    obtain ⟨x, hxE, hxD⟩ := Finset.not_disjoint_iff.mp hnotED
    exact Set.not_disjoint_iff.mpr
      ⟨x, Finset.mem_coe.mpr hxE, by simpa using hxD⟩

/-- Protected form of the one-support extension argument.  Starting from a
fixed prefix `D` at a target with no two disjoint `D`-avoiding supports, an
arbitrary additional finite set `F` gives an exact alternative: either
`D ∪ F` already destroys the target, or one support surviving `D ∪ F`
can itself be used as a bounded extension `T`.  In the latter case `T` is
disjoint from all previously protected vertices, while `D ∪ T` destroys
the target. -/
theorem destroysAt_union_or_exists_protectedBoundedExtension_of_no_twoDisjointRepairs
    {A : Set ℕ} {R : SupportFamily} {D F : Finset ℕ} {n r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hno : ¬ ∃ E ∈ R n, Disjoint E D ∧
      ∃ E' ∈ R n, Disjoint E' D ∧ Disjoint E E') :
    DestroysAt R ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
      ∃ T : Finset ℕ,
        T ∈ R n ∧ (∀ x ∈ T, x ∈ A) ∧
          Disjoint T (D ∪ F) ∧ T.card ≤ r ∧
          DestroysAt R (((D ∪ T : Finset ℕ) : Set ℕ)) n := by
  classical
  by_cases hdestroy :
      DestroysAt R ((((D ∪ F : Finset ℕ) : Set ℕ))) n
  · exact Or.inl hdestroy
  · obtain ⟨T, hTR, hTDFset⟩ := not_destroysAt_iff.mp hdestroy
    have hTDF : Disjoint T (D ∪ F) := by
      rw [Finset.disjoint_left]
      intro x hxT hxDF
      exact Set.disjoint_left.mp hTDFset
        (Finset.mem_coe.mpr hxT) (Finset.mem_coe.mpr hxDF)
    have hTD : Disjoint T D :=
      hTDF.mono_right Finset.subset_union_left
    refine Or.inr ⟨T, hTR, hRA n T hTR, hTDF, hcard n T hTR, ?_⟩
    intro E hER
    by_cases hED : Disjoint E D
    · have hnotET : ¬ Disjoint E T := by
        intro hET
        apply hno
        exact ⟨E, hER, hED, T, hTR, hTD, hET⟩
      obtain ⟨x, hxE, hxT⟩ := Finset.not_disjoint_iff.mp hnotET
      exact Set.not_disjoint_iff.mpr
        ⟨x, Finset.mem_coe.mpr hxE,
          Finset.mem_coe.mpr (Finset.mem_union_right D hxT)⟩
    · obtain ⟨x, hxE, hxD⟩ := Finset.not_disjoint_iff.mp hED
      exact Set.not_disjoint_iff.mpr
        ⟨x, Finset.mem_coe.mpr hxE,
          Finset.mem_coe.mpr (Finset.mem_union_left T hxD)⟩

/-- Reservoir-relative protected extension.  If two supports cannot have
disjoint portions in `C`, a support surviving `D ∪ F` contributes only its
`C`-part as the new moving set.  Shared vertices outside `C` are retained and
do not enter the destroyer extension. -/
theorem destroysAt_union_or_exists_protectedBoundedReservoirExtension_of_no_twoRepairs
    {A C : Set ℕ} {R : SupportFamily} {D F : Finset ℕ} {n r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hno : ¬ ∃ E ∈ R n, Disjoint E D ∧
      ∃ E' ∈ R n, Disjoint E' D ∧
        Disjoint ((E : Set ℕ) ∩ C) ((E' : Set ℕ) ∩ C)) :
    DestroysAt R ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
      ∃ T : Finset ℕ,
        (∀ x ∈ T, x ∈ A ∧ x ∈ C) ∧
          Disjoint T (D ∪ F) ∧ T.Nonempty ∧ T.card ≤ r ∧
          DestroysAt R (((D ∪ T : Finset ℕ) : Set ℕ)) n := by
  classical
  by_cases hdestroy :
      DestroysAt R ((((D ∪ F : Finset ℕ) : Set ℕ))) n
  · exact Or.inl hdestroy
  · obtain ⟨E, hER, hEDFset⟩ := not_destroysAt_iff.mp hdestroy
    have hEDF : Disjoint E (D ∪ F) := by
      rw [Finset.disjoint_left]
      intro x hxE hxDF
      exact Set.disjoint_left.mp hEDFset
        (Finset.mem_coe.mpr hxE) (Finset.mem_coe.mpr hxDF)
    have hED : Disjoint E D :=
      hEDF.mono_right Finset.subset_union_left
    let T : Finset ℕ := E.filter fun x => x ∈ C
    have hTA : ∀ x ∈ T, x ∈ A ∧ x ∈ C := by
      intro x hxT
      have hx := Finset.mem_filter.mp hxT
      exact ⟨hRA n E hER x hx.1, hx.2⟩
    have hTDF : Disjoint T (D ∪ F) := by
      rw [Finset.disjoint_left]
      intro x hxT hxDF
      exact Finset.disjoint_left.mp hEDF
        (Finset.mem_filter.mp hxT).1 hxDF
    have hTnonempty : T.Nonempty := by
      by_contra hnot
      have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
      have hECempty : (E : Set ℕ) ∩ C = ∅ := by
        ext x
        constructor
        · intro hx
          have hxT : x ∈ T := Finset.mem_filter.mpr
            ⟨Finset.mem_coe.mp hx.1, hx.2⟩
          rw [hTempty] at hxT
          simp at hxT
        · simp
      apply hno
      refine ⟨E, hER, hED, E, hER, hED, ?_⟩
      simp [hECempty]
    refine Or.inr ⟨T, hTA, hTDF, hTnonempty,
      (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (hcard n E hER), ?_⟩
    intro G hGR
    by_cases hGD : Disjoint G D
    · have hnotEG :
          ¬ Disjoint ((E : Set ℕ) ∩ C) ((G : Set ℕ) ∩ C) := by
        intro hEG
        apply hno
        exact ⟨E, hER, hED, G, hGR, hGD, hEG⟩
      obtain ⟨x, hxEC, hxGC⟩ := Set.not_disjoint_iff.mp hnotEG
      exact Set.not_disjoint_iff.mpr
        ⟨x, hxGC.1, Finset.mem_coe.mpr
          (Finset.mem_union_right D
            (Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hxEC.1, hxEC.2⟩))⟩
    · obtain ⟨x, hxG, hxD⟩ := Finset.not_disjoint_iff.mp hGD
      exact Set.not_disjoint_iff.mpr
        ⟨x, Finset.mem_coe.mpr hxG,
          Finset.mem_coe.mpr (Finset.mem_union_left T hxD)⟩

/-- A finite matching produced by repeatedly applying the protected
one-support extension alternative.  Every moving support avoids the common
prefix `D`, has the prescribed cardinal bound, and together with `D`
destroys its own late target. -/
def IsProtectedBoundedExtensionFamily
    (R : SupportFamily) (A S : Set ℕ) (D : Finset ℕ) (r N : ℕ)
    (𝒯 : Finset (Finset ℕ)) : Prop :=
  IsMatching 𝒯 ∧
    (∀ T ∈ 𝒯, T.Nonempty) ∧
    (∀ T ∈ 𝒯, ∀ x ∈ T, x ∈ A) ∧
    (∀ T ∈ 𝒯, Disjoint T D) ∧
    (∀ T ∈ 𝒯, T.card ≤ r) ∧
    ∀ T ∈ 𝒯, ∃ n,
      N ≤ n ∧ n ∈ S ∧ T ∈ R n ∧
        DestroysAt R (((D ∪ T : Finset ℕ) : Set ℕ)) n

/-- Finite recursive normal form for the protected extension dichotomy.
After any requested number `m` of stages, either one has built `m`
pairwise-disjoint moving supports, or the process stopped earlier because
the common prefix together with the union of the supports already built
destroys a late target. -/
theorem exists_protectedBoundedExtensionFamily_or_accumulatedDestroyer
    {A S : Set ℕ} {R : SupportFamily} {D : Finset ℕ} {r : ℕ}
    (hnonempty : SupportsNonempty R)
    (hrecur : ∀ F : Finset ℕ, ∀ N, ∃ n,
      N ≤ n ∧ n ∈ S ∧
        (DestroysAt R ((((D ∪ F : Finset ℕ) : Set ℕ))) n ∨
          ∃ T : Finset ℕ,
            T ∈ R n ∧ (∀ x ∈ T, x ∈ A) ∧
              Disjoint T (D ∪ F) ∧ T.card ≤ r ∧
              DestroysAt R (((D ∪ T : Finset ℕ) : Set ℕ)) n)) :
    ∀ m N, ∃ 𝒯 : Finset (Finset ℕ),
      IsProtectedBoundedExtensionFamily R A S D r N 𝒯 ∧
        (𝒯.card = m ∨
          (𝒯.card < m ∧ ∃ n,
            N ≤ n ∧ n ∈ S ∧
              DestroysAt R
                (((D ∪ 𝒯.biUnion id : Finset ℕ) : Set ℕ)) n)) := by
  classical
  intro m
  induction m with
  | zero =>
      intro N
      refine ⟨∅, ?_, Or.inl (by simp)⟩
      simp [IsProtectedBoundedExtensionFamily, IsMatching]
  | succ m ih =>
      intro N
      obtain ⟨𝒯, hfamily, hfull | hstopped⟩ := ih N
      · let F : Finset ℕ := 𝒯.biUnion id
        obtain ⟨n, hn, hnS, hdestroy | hnew⟩ := hrecur F N
        · refine ⟨𝒯, hfamily, Or.inr ⟨?_, n, hn, hnS, ?_⟩⟩
          · omega
          · simpa [F] using hdestroy
        · obtain ⟨T, hTR, hTA, hTDF, hTcard, hTdestroy⟩ := hnew
          have hTnonempty : T.Nonempty := hnonempty n T hTR
          have hTF : Disjoint T F :=
            hTDF.mono_right Finset.subset_union_right
          have hTD : Disjoint T D :=
            hTDF.mono_right Finset.subset_union_left
          have hTnot : T ∉ 𝒯 := by
            intro hT𝒯
            obtain ⟨x, hxT⟩ := hTnonempty
            exact Finset.disjoint_left.mp hTF hxT
              (Finset.mem_biUnion.mpr ⟨T, hT𝒯, hxT⟩)
          have hmatching : IsMatching (insert T 𝒯) := by
            rw [IsMatching, Finset.coe_insert, Set.pairwiseDisjoint_insert]
            refine ⟨hfamily.1, ?_⟩
            intro E hE𝒯 hTE
            rw [Finset.disjoint_left]
            intro x hxT hxE
            exact Finset.disjoint_left.mp hTF hxT
              (Finset.mem_biUnion.mpr ⟨E, hE𝒯, hxE⟩)
          have hnewfamily :
              IsProtectedBoundedExtensionFamily
                R A S D r N (insert T 𝒯) := by
            refine ⟨hmatching, ?_, ?_, ?_, ?_, ?_⟩
            · intro E hE
              rcases Finset.mem_insert.mp hE with rfl | hE𝒯
              · exact hTnonempty
              · exact hfamily.2.1 E hE𝒯
            · intro E hE x hxE
              rcases Finset.mem_insert.mp hE with rfl | hE𝒯
              · exact hTA x hxE
              · exact hfamily.2.2.1 E hE𝒯 x hxE
            · intro E hE
              rcases Finset.mem_insert.mp hE with rfl | hE𝒯
              · exact hTD
              · exact hfamily.2.2.2.1 E hE𝒯
            · intro E hE
              rcases Finset.mem_insert.mp hE with rfl | hE𝒯
              · exact hTcard
              · exact hfamily.2.2.2.2.1 E hE𝒯
            · intro E hE
              rcases Finset.mem_insert.mp hE with rfl | hE𝒯
              · exact ⟨n, hn, hnS, hTR, hTdestroy⟩
              · exact hfamily.2.2.2.2.2 E hE𝒯
          refine ⟨insert T 𝒯, hnewfamily, Or.inl ?_⟩
          simp [hTnot, hfull]
      · refine ⟨𝒯, hfamily, Or.inr ⟨?_, hstopped.2⟩⟩
        omega

/-- Proposition 3 in its strongest form: failure of finite-core matching
yields a bounded transversal of the outside-support hypergraph. -/
theorem boundedMovingOutsideTransversals_of_failsFiniteCoreMatching
    {A : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hfail : FailsFiniteCoreMatching R A) :
    HasBoundedMovingOutsideTransversals R A := by
  intro F hFA
  have hnot := hfail F hFA
  unfold OutsideMatchingTendsToInfinity at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  refine ⟨r * j, ?_⟩
  intro N
  obtain ⟨n, hn, hnmatch⟩ := hj N
  let H := outsideSupportHypergraph R F n
  have hHnonempty : ∀ D ∈ H, D.Nonempty := by
    intro D hDH
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hDH).1
  have hHcard : ∀ D ∈ H, D.card ≤ r := by
    intro D hDH
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (hcard n E hER)
  obtain ⟨T₀, hT₀trans, hT₀card⟩ :=
    exists_small_transversal_of_matchingNumber_le
      hHnonempty hHcard hnmatch
  let U : Finset ℕ := H.biUnion id
  let T : Finset ℕ := T₀ ∩ U
  have hTtrans : IsTransversal H T := by
    intro D hDH
    obtain ⟨x, hx⟩ := hT₀trans D hDH
    obtain ⟨hxD, hxT₀⟩ := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_inter.mpr ⟨hxD,
      Finset.mem_inter.mpr ⟨hxT₀, ?_⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨D, hDH, hxD⟩
  have hTA : ∀ x ∈ T, x ∈ A := by
    intro x hxT
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    have hxE : x ∈ E := by
      rw [← hEF] at hxD
      exact (Finset.mem_sdiff.mp hxD).1
    exact hRA n E hER x hxE
  have hTF : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF] at hxD
    exact (Finset.mem_sdiff.mp hxD).2 hxF
  exact ⟨n, T, hn, hTA, hTF,
    le_trans (Finset.card_le_card Finset.inter_subset_left) hT₀card,
    hTtrans⟩

/- Relative Proposition 3: failure along `S` yields bounded moving
transversals at arbitrarily large targets which remain in `S`. -/
theorem boundedMovingOutsideTransversalsAlong_of_failsFiniteCoreMatchingAlong
    {A S : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r)
    (hfail : FailsFiniteCoreMatchingAlong R A S) :
    HasBoundedMovingOutsideTransversalsAlong R A S := by
  intro F hFA
  have hnot := hfail F hFA
  unfold OutsideMatchingTendsToInfinityAlong at hnot
  push Not at hnot
  obtain ⟨j, hj⟩ := hnot
  refine ⟨r * j, ?_⟩
  intro N
  obtain ⟨n, hn, hnS, hnmatch⟩ := hj N
  let H := outsideSupportHypergraph R F n
  have hHnonempty : ∀ D ∈ H, D.Nonempty := by
    intro D hDH
    exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hDH).1
  have hHcard : ∀ D ∈ H, D.card ≤ r := by
    intro D hDH
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF]
    exact le_trans (Finset.card_le_card Finset.sdiff_subset)
      (hcard n E hER)
  obtain ⟨T₀, hT₀trans, hT₀card⟩ :=
    exists_small_transversal_of_matchingNumber_le
      hHnonempty hHcard hnmatch
  let U : Finset ℕ := H.biUnion id
  let T : Finset ℕ := T₀ ∩ U
  have hTtrans : IsTransversal H T := by
    intro D hDH
    obtain ⟨x, hx⟩ := hT₀trans D hDH
    obtain ⟨hxD, hxT₀⟩ := Finset.mem_inter.mp hx
    refine ⟨x, Finset.mem_inter.mpr ⟨hxD,
      Finset.mem_inter.mpr ⟨hxT₀, ?_⟩⟩⟩
    exact Finset.mem_biUnion.mpr ⟨D, hDH, hxD⟩
  have hTA : ∀ x ∈ T, x ∈ A := by
    intro x hxT
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    have hxE : x ∈ E := by
      rw [← hEF] at hxD
      exact (Finset.mem_sdiff.mp hxD).1
    exact hRA n E hER x hxE
  have hTF : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    obtain ⟨D, hDH, hxD⟩ :=
      Finset.mem_biUnion.mp (Finset.mem_inter.mp hxT).2
    obtain ⟨E, hER, hEF⟩ :=
      Finset.mem_image.mp (Finset.mem_erase.mp hDH).2
    rw [← hEF] at hxD
    exact (Finset.mem_sdiff.mp hxD).2 hxF
  exact ⟨n, T, hn, hnS, hTA, hTF,
    le_trans (Finset.card_le_card Finset.inter_subset_left) hT₀card,
    hTtrans⟩

/-- The stronger outside-transversal output implies the coarser statement
that the protected core together with the moving part destroys the target. -/
theorem boundedMovingTransversals_of_outsideTransversals
    {A : Set ℕ} {R : SupportFamily}
    (hnonempty : SupportsNonempty R)
    (hmoving : HasBoundedMovingOutsideTransversals R A) :
    HasBoundedMovingTransversals R A := by
  intro F hFA
  obtain ⟨m, hm⟩ := hmoving F hFA
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hTA, hTF, hTcard, hTtrans⟩ := hm N
  refine ⟨n, T, hn, hTA, hTF, hTcard, ?_⟩
  intro E hER
  by_cases hEFempty : E \ F = ∅
  · obtain ⟨x, hxE⟩ := hnonempty n E hER
    have hxF : x ∈ F := by
      by_contra hxF
      have : x ∈ E \ F := Finset.mem_sdiff.mpr ⟨hxE, hxF⟩
      rw [hEFempty] at this
      simp at this
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, hxE, by
      exact Finset.mem_coe.mpr (Finset.mem_union_left T hxF)⟩
  · have hDmem :
        E \ F ∈ outsideSupportHypergraph R F n := by
      apply Finset.mem_erase.mpr
      exact ⟨hEFempty, Finset.mem_image.mpr ⟨E, hER, rfl⟩⟩
    obtain ⟨x, hx⟩ := hTtrans (E \ F) hDmem
    obtain ⟨hxEF, hxT⟩ := Finset.mem_inter.mp hx
    apply Set.not_disjoint_iff.mpr
    exact ⟨x, (Finset.mem_sdiff.mp hxEF).1, by
      exact Finset.mem_coe.mpr (Finset.mem_union_right F hxT)⟩

/-- If late supports cannot be trapped in the protected core, a bounded
outside transversal is already a transversal without adjoining that core. -/
theorem boundedEscapingTransversals_of_outsideTransversals
    {A : Set ℕ} {R : SupportFamily}
    (hescape : SupportsEventuallyEscapeFiniteCores R)
    (hmoving : HasBoundedMovingOutsideTransversals R A) :
    HasBoundedEscapingTransversals R A := by
  intro F hFA
  obtain ⟨m, hmovingF⟩ := hmoving F hFA
  obtain ⟨K, hK⟩ := hescape F
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hTA, hTF, hTcard, hTtrans⟩ :=
    hmovingF (max N K)
  refine ⟨n, T, le_trans (le_max_left N K) hn,
    hTA, hTF, hTcard, ?_⟩
  intro E hER
  have hEF : (E \ F).Nonempty :=
    hK n (le_trans (le_max_right N K) hn) E hER
  have hDmem :
      E \ F ∈ outsideSupportHypergraph R F n := by
    apply Finset.mem_erase.mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp hEF,
      Finset.mem_image.mpr ⟨E, hER, rfl⟩⟩
  obtain ⟨x, hx⟩ := hTtrans (E \ F) hDmem
  obtain ⟨hxEF, hxT⟩ := Finset.mem_inter.mp hx
  apply Set.not_disjoint_iff.mpr
  exact ⟨x, (Finset.mem_sdiff.mp hxEF).1,
    Finset.mem_coe.mpr hxT⟩

/-- If the support family is eventually nonempty, an escaping transversal can
be chosen nonempty while avoiding any prescribed finite set. -/
theorem exists_nonempty_escapingTransversal
    {A : Set ℕ} {R : SupportFamily}
    (heventual : HasEventuallySurvivingSupport R ∅)
    (hmoving : HasBoundedEscapingTransversals R A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (N : ℕ) :
    ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.Nonempty ∧
      DestroysAt R (T : Set ℕ) n := by
  obtain ⟨K, hK⟩ := heventual
  obtain ⟨m, hm⟩ := hmoving F hFA
  obtain ⟨n, T, hn, hTA, hTF, hTcard, hdestroy⟩ :=
    hm (max N K)
  have hnN : N ≤ n := le_trans (le_max_left N K) hn
  have hnK : K ≤ n := le_trans (le_max_right N K) hn
  obtain ⟨E, hER, hEempty⟩ := hK n hnK
  have hTnonempty : T.Nonempty := by
    by_contra hnot
    have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    apply (hdestroy E hER)
    rw [hTempty]
    simp
  exact ⟨n, T, hnN, hTA, hTF, hTnonempty, hdestroy⟩

/-- The nonempty extension lemma in a structure-valued form suitable for
dependent recursive choice. -/
theorem nonempty_escapingTransversalWitness
    {A : Set ℕ} {R : SupportFamily}
    (heventual : HasEventuallySurvivingSupport R ∅)
    (hmoving : HasBoundedEscapingTransversals R A)
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) (N : ℕ) :
    Nonempty (EscapingTransversalWitness R A F N) := by
  obtain ⟨n, T, hn, hTA, hTF, hTnonempty, hdestroy⟩ :=
    exists_nonempty_escapingTransversal
      heventual hmoving F hFA N
  exact ⟨⟨n, T, hn, hTA, hTF, hTnonempty, hdestroy⟩⟩

/-- Repeatedly protect all previously chosen vertices.  The escaping property
then yields infinitely many pairwise-disjoint nonempty transversals. -/
theorem exists_escapingTransversalSequence
    {A : Set ℕ} {R : SupportFamily}
    (heventual : HasEventuallySurvivingSupport R ∅)
    (hmoving : HasBoundedEscapingTransversals R A) :
    Nonempty (EscapingTransversalSequence R A) := by
  classical
  let State := {p : ℕ × Finset ℕ // (p.2 : Set ℕ) ⊆ A}
  let initial : State := ⟨(0, ∅), by simp⟩
  let chooseWitness : (s : State) →
      EscapingTransversalWitness R A s.1.2 (s.1.1 + 1) :=
    fun s => Classical.choice
      (nonempty_escapingTransversalWitness
        heventual hmoving s.1.2 s.2 (s.1.1 + 1))
  let advance : State → State := fun s =>
    ⟨((chooseWitness s).n, s.1.2 ∪ (chooseWitness s).T), by
      intro x hx
      obtain hx | hx := Finset.mem_union.mp hx
      · exact s.2 hx
      · exact (chooseWitness s).subset x hx⟩
  let state : ℕ → State := fun i =>
    Nat.rec initial (fun _ s => advance s) i
  let witness (i : ℕ) := chooseWitness (state i)
  let U (i : ℕ) : Finset ℕ := (state i).1.2
  let ns (i : ℕ) : ℕ := (witness i).n
  let Ts (i : ℕ) : Finset ℕ := (witness i).T
  have hstate_succ : ∀ i, state (i + 1) = advance (state i) := by
    intro i
    simp [state]
  have hU_succ : ∀ i, U (i + 1) = U i ∪ Ts i := by
    intro i
    change (state (i + 1)).1.2 =
      (state i).1.2 ∪ (witness i).T
    rw [hstate_succ]
  have hlast_succ : ∀ i, (state (i + 1)).1.1 = ns i := by
    intro i
    rw [hstate_succ]
  have hU_step : ∀ i, U i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact Finset.subset_union_left
  have hU_mono : Monotone U :=
    monotone_nat_of_le_succ hU_step
  have hT_into_next : ∀ i, Ts i ⊆ U (i + 1) := by
    intro i
    rw [hU_succ]
    exact Finset.subset_union_right
  have hns_strict : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro i
    calc
      ns i = (state (i + 1)).1.1 := (hlast_succ i).symm
      _ < ns (i + 1) :=
        Nat.lt_of_succ_le (witness (i + 1)).lower
  have hTs_disjoint : Pairwise fun i j => Disjoint (Ts i) (Ts j) := by
    intro i j hij
    by_cases hijlt : i < j
    · have hTiUj : Ts i ⊆ U j :=
        fun x hx => hU_mono (Nat.succ_le_of_lt hijlt)
          (hT_into_next i hx)
      rw [Finset.disjoint_left]
      intro x hxi hxj
      exact Finset.disjoint_left.mp (witness j).disjoint
        hxj (hTiUj hxi)
    · have hjilt : j < i := by omega
      have hTjUi : Ts j ⊆ U i :=
        fun x hx => hU_mono (Nat.succ_le_of_lt hjilt)
          (hT_into_next j hx)
      rw [Finset.disjoint_left]
      intro x hxi hxj
      exact Finset.disjoint_left.mp (witness i).disjoint
        hxi (hTjUi hxj)
  exact ⟨⟨ns, Ts, hns_strict,
    fun i => (witness i).subset,
    hTs_disjoint,
    fun i => (witness i).nonempty,
    fun i => (witness i).destroys⟩⟩

/-- Pairwise-disjoint nonempty finite sets inside `A` can be completed to a
finite-block partition of all of `A`.  Each leftover vertex `x` is attached
only to block `x`. -/
theorem EscapingTransversalSequence.exists_finiteBlockPartition
    {A : Set ℕ} {R : SupportFamily}
    (S : EscapingTransversalSequence R A) :
    ∃ F : ℕ → Finset ℕ,
      IsFiniteBlockPartition A F ∧
      ∀ i, S.T i ⊆ F i := by
  classical
  let C : Set ℕ := ⋃ i, ((S.T i : Finset ℕ) : Set ℕ)
  let F : ℕ → Finset ℕ := fun i =>
    S.T i ∪ (if i ∈ A ∧ i ∉ C then {i} else ∅)
  have P : IsFiniteBlockPartition A F := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      obtain ⟨x, hx⟩ := S.nonempty i
      exact ⟨x, Finset.mem_union_left _ hx⟩
    · intro i j hij
      rw [Finset.disjoint_left]
      intro x hxi hxj
      by_cases hi : i ∈ A ∧ i ∉ C <;>
        by_cases hj : j ∈ A ∧ j ∉ C
      · have hxi' : x ∈ S.T i ∪ {i} := by
          simpa [F, hi] using hxi
        have hxj' : x ∈ S.T j ∪ {j} := by
          simpa [F, hj] using hxj
        rcases Finset.mem_union.mp hxi' with hxiT | hxiS
        · rcases Finset.mem_union.mp hxj' with hxjT | hxjS
          · exact Finset.disjoint_left.mp (S.disjoint hij) hxiT hxjT
          · have hxjEq : x = j := Finset.mem_singleton.mp hxjS
            apply hj.2
            rw [← hxjEq]
            exact Set.mem_iUnion.mpr ⟨i, hxiT⟩
        · have hxiEq : x = i := Finset.mem_singleton.mp hxiS
          rcases Finset.mem_union.mp hxj' with hxjT | hxjS
          · apply hi.2
            rw [← hxiEq]
            exact Set.mem_iUnion.mpr ⟨j, hxjT⟩
          · have hxjEq : x = j := Finset.mem_singleton.mp hxjS
            exact hij (hxiEq.symm.trans hxjEq)
      · have hxi' : x ∈ S.T i ∪ {i} := by
          simpa [F, hi] using hxi
        have hxjT : x ∈ S.T j := by
          simpa [F, hj] using hxj
        rcases Finset.mem_union.mp hxi' with hxiT | hxiS
        · exact Finset.disjoint_left.mp (S.disjoint hij) hxiT hxjT
        · have hxiEq : x = i := Finset.mem_singleton.mp hxiS
          apply hi.2
          rw [← hxiEq]
          exact Set.mem_iUnion.mpr ⟨j, hxjT⟩
      · have hxiT : x ∈ S.T i := by
          simpa [F, hi] using hxi
        have hxj' : x ∈ S.T j ∪ {j} := by
          simpa [F, hj] using hxj
        rcases Finset.mem_union.mp hxj' with hxjT | hxjS
        · exact Finset.disjoint_left.mp (S.disjoint hij) hxiT hxjT
        · have hxjEq : x = j := Finset.mem_singleton.mp hxjS
          apply hj.2
          rw [← hxjEq]
          exact Set.mem_iUnion.mpr ⟨i, hxiT⟩
      · have hxiT : x ∈ S.T i := by
          simpa [F, hi] using hxi
        have hxjT : x ∈ S.T j := by
          simpa [F, hj] using hxj
        exact Finset.disjoint_left.mp (S.disjoint hij) hxiT hxjT
    · intro x
      constructor
      · intro hxA
        by_cases hxC : x ∈ C
        · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxC
          exact ⟨i, Finset.mem_union_left _ hxi⟩
        · refine ⟨x, ?_⟩
          simp [F, hxA, hxC]
      · rintro ⟨i, hxi⟩
        by_cases hi : i ∈ A ∧ i ∉ C
        · have hxi' : x ∈ S.T i ∪ {i} := by
            simpa [F, hi] using hxi
          rcases Finset.mem_union.mp hxi' with hxiT | hxiS
          · exact S.subset i x hxiT
          · have hxiEq : x = i := Finset.mem_singleton.mp hxiS
            exact hxiEq ▸ hi.1
        · have hxiT : x ∈ S.T i := by
            simpa [F, hi] using hxi
          exact S.subset i x hxiT
  exact ⟨F, P, fun i => Finset.subset_union_left⟩

/-- Proposition 3, in the coarse form used by the translation lemma. -/
theorem boundedMovingTransversals_of_failsFiniteCoreMatching
    {A : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hnonempty : SupportsNonempty R)
    (hcard : SupportsCardAtMost R r)
    (hfail : FailsFiniteCoreMatching R A) :
    HasBoundedMovingTransversals R A :=
  boundedMovingTransversals_of_outsideTransversals hnonempty
    (boundedMovingOutsideTransversals_of_failsFiniteCoreMatching
      hRA hcard hfail)

/-- Conversely, bounded outside-core moving transversals rule out matching
growth outside every finite core. -/
theorem failsFiniteCoreMatching_of_boundedMovingOutsideTransversals
    {A : Set ℕ} {R : SupportFamily}
    (hmoving : HasBoundedMovingOutsideTransversals R A) :
    FailsFiniteCoreMatching R A := by
  intro F hFA hgrowth
  obtain ⟨m, hmovingF⟩ := hmoving F hFA
  obtain ⟨N, hN⟩ := hgrowth m
  obtain ⟨n, T, hn, _hTA, _hTF, hTcard, hTtrans⟩ :=
    hmovingF N
  have hedges :
      ∀ E ∈ outsideSupportHypergraph R F n, E.Nonempty := by
    intro E hEH
    exact Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hEH).1
  have hmatching :=
    matchingNumber_le_card_of_transversal hedges hTtrans
  exact (not_lt_of_ge (le_trans hmatching hTcard)) (hN n hn)

/- Conversely, recurrent bounded outside transversals along `S` rule out
eventual matching growth along that same target set. -/
theorem failsFiniteCoreMatchingAlong_of_boundedMovingOutsideTransversalsAlong
    {A S : Set ℕ} {R : SupportFamily}
    (hmoving : HasBoundedMovingOutsideTransversalsAlong R A S) :
    FailsFiniteCoreMatchingAlong R A S := by
  intro F hFA hgrowth
  obtain ⟨m, hmovingF⟩ := hmoving F hFA
  obtain ⟨N, hN⟩ := hgrowth m
  obtain ⟨n, T, hn, hnS, _hTA, _hTF, hTcard, hTtrans⟩ :=
    hmovingF N
  have hedges :
      ∀ E ∈ outsideSupportHypergraph R F n, E.Nonempty := by
    intro E hEH
    exact Finset.nonempty_iff_ne_empty.mpr
      (Finset.mem_erase.mp hEH).1
  have hmatching :=
    matchingNumber_le_card_of_transversal hedges hTtrans
  exact (not_lt_of_ge (le_trans hmatching hTcard))
    (hN n hn hnS)

/-- Under the natural support hypotheses, failure of finite-core matching is
equivalent to the strong bounded-moving-outside-transversal structure. -/
theorem failsFiniteCoreMatching_iff_boundedMovingOutsideTransversals
    {A : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r) :
    FailsFiniteCoreMatching R A ↔
      HasBoundedMovingOutsideTransversals R A :=
  ⟨boundedMovingOutsideTransversals_of_failsFiniteCoreMatching
      hRA hcard,
    failsFiniteCoreMatching_of_boundedMovingOutsideTransversals⟩

/- The relative matching dichotomy is exact: failure of growth along `S` is
equivalent to bounded moving transversals recurrent in `S`. -/
theorem failsFiniteCoreMatchingAlong_iff_boundedMovingOutsideTransversalsAlong
    {A S : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r) :
    FailsFiniteCoreMatchingAlong R A S ↔
      HasBoundedMovingOutsideTransversalsAlong R A S :=
  ⟨boundedMovingOutsideTransversalsAlong_of_failsFiniteCoreMatchingAlong
      hRA hcard,
    failsFiniteCoreMatchingAlong_of_boundedMovingOutsideTransversalsAlong⟩

/- Exhaustive relative matching dichotomy.  Unlike the unrestricted version,
the bad branch is recurrent in `S`; the complementary branch gives matching
growth along `S` outside one finite core. -/
theorem exists_finiteCore_outsideMatchingAlong_or_boundedMovingAlong
    {A S : Set ℕ} {R : SupportFamily} {r : ℕ}
    (hRA : SupportsIn R A)
    (hcard : SupportsCardAtMost R r) :
    (∃ F : Finset ℕ, (F : Set ℕ) ⊆ A ∧
      OutsideMatchingTendsToInfinityAlong R F S) ∨
      HasBoundedMovingOutsideTransversalsAlong R A S := by
  by_cases hfail : FailsFiniteCoreMatchingAlong R A S
  · exact Or.inr <|
      boundedMovingOutsideTransversalsAlong_of_failsFiniteCoreMatchingAlong
        hRA hcard hfail
  · left
    unfold FailsFiniteCoreMatchingAlong at hfail
    push Not at hfail
    exact hfail

/- Unrestricted eventual matching growth implies growth along every target
set.  The converse is intentionally unavailable. -/
theorem outsideMatchingAlong_of_outsideMatching
    {R : SupportFamily} {F : Finset ℕ} {S : Set ℕ}
    (hgrowth : OutsideMatchingTendsToInfinity R F) :
    OutsideMatchingTendsToInfinityAlong R F S := by
  intro j
  obtain ⟨N, hN⟩ := hgrowth j
  exact ⟨N, fun n hn _hnS => hN n hn⟩

/-- If the entire support hypergraph is a matching, any finite set destroying
the target has at least as many vertices as there are supports. -/
theorem card_supports_le_card_of_matching_of_destroysAt
    {R : SupportFamily} {n : ℕ} {T : Finset ℕ}
    (hnonempty : ∀ E ∈ R n, E.Nonempty)
    (hmatching : IsMatching (R n))
    (hdestroy : DestroysAt R (T : Set ℕ) n) :
    (R n).card ≤ T.card := by
  have htrans : IsTransversal (R n) T := by
    intro E hER
    obtain ⟨x, hxE, hxT⟩ :=
      Set.not_disjoint_iff.mp (hdestroy E hER)
    exact ⟨x, Finset.mem_inter.mpr
      ⟨hxE, Finset.mem_coe.mp hxT⟩⟩
  exact le_trans
    (card_le_matchingNumber (fun _ hE => hE) hmatching)
    (matchingNumber_le_card_of_transversal hnonempty htrans)

/-- Abstract form of the translation lemma: a transversal for a successor
support hypergraph at `n` is a transversal for the predecessor support
hypergraph at `n - a`, provided `a` lies outside the transversal and `a ≤ n`.
-/
def SuccessorTransversalsDescend
    (Rk Rsucc : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ S : Finset ℕ, ∀ n,
    DestroysAt Rsucc (S : Set ℕ) n →
      ∀ a ∈ A, a ∉ S → a ≤ n →
        DestroysAt Rk (S : Set ℕ) (n - a)

/-- The exact predecessor consequence of bounded moving successor
transversals. -/
def HasBoundedMovingPredecessorTransversals
    (Rk : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      ∀ a ∈ A, a ∉ F ∪ T → a ≤ n →
        DestroysAt Rk (((F ∪ T : Finset ℕ) : Set ℕ)) (n - a)

/-- The stronger predecessor output when the moving part alone is a
successor transversal. -/
def HasBoundedEscapingPredecessorTransversals
    (Rk : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ⊆ A →
    ∃ m, ∀ N, ∃ n T,
      N ≤ n ∧
      (∀ x ∈ T, x ∈ A) ∧
      Disjoint T F ∧
      T.card ≤ m ∧
      ∀ a ∈ A, a ∉ T → a ≤ n →
        DestroysAt Rk (T : Set ℕ) (n - a)

/-- Proposition 3 plus the repaired translation lemma imply bounded moving
predecessor transversals. -/
theorem boundedMovingPredecessorTransversals
    {A : Set ℕ} {Rk Rsucc : SupportFamily}
    (hmoving : HasBoundedMovingTransversals Rsucc A)
    (hdescend : SuccessorTransversalsDescend Rk Rsucc A) :
    HasBoundedMovingPredecessorTransversals Rk A := by
  intro F hFA
  obtain ⟨m, hm⟩ := hmoving F hFA
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hTA, hTF, hcard, hdestroy⟩ := hm N
  refine ⟨n, T, hn, hTA, hTF, hcard, ?_⟩
  intro a haA haS han
  exact hdescend (F ∪ T) n hdestroy a haA haS han

/-- Escaping successor transversals descend without needing the protected
core in the deletion set. -/
theorem boundedEscapingPredecessorTransversals
    {A : Set ℕ} {Rk Rsucc : SupportFamily}
    (hmoving : HasBoundedEscapingTransversals Rsucc A)
    (hdescend : SuccessorTransversalsDescend Rk Rsucc A) :
    HasBoundedEscapingPredecessorTransversals Rk A := by
  intro F hFA
  obtain ⟨m, hm⟩ := hmoving F hFA
  refine ⟨m, ?_⟩
  intro N
  obtain ⟨n, T, hn, hTA, hTF, hcard, hdestroy⟩ := hm N
  refine ⟨n, T, hn, hTA, hTF, hcard, ?_⟩
  intro a haA haT han
  exact hdescend T n hdestroy a haA haT han

/-- Finite avoidability is the missing polarity needed by compactness: for one
partition and threshold, every finite set of target integers is simultaneously
survivable by some selector. -/
def HasFiniteSelectorAvoidability
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∃ F, ∃ _P : IsFiniteBlockPartition A F, ∃ N,
    ∀ Q : Finset ℕ, (∀ n ∈ Q, N ≤ n) →
      ∃ s : BlockSelector F,
        ∀ n ∈ Q, ∃ E ∈ R n,
          Disjoint (E : Set ℕ) (selectedSet s)

/-- A simultaneous choice of one support for each target in a finite set. -/
abbrev FiniteSupportChoice
    (R : SupportFamily) (Q : Finset ℕ) :=
  ∀ q : {n // n ∈ Q}, {E // E ∈ R q.1}

/-- The finite union of all supports selected for the targets in `Q`. -/
def finiteSupportChoiceUnion
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) : Finset ℕ :=
  Q.attach.biUnion fun q => (c q).1

/-- A selected support is contained in the union of the finite support
choice. -/
theorem finiteSupportChoice_subset_union
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) (q : {n // n ∈ Q}) :
    (c q).1 ⊆ finiteSupportChoiceUnion c := by
  intro x hx
  apply Finset.mem_biUnion.mpr
  exact ⟨q, by simp, hx⟩

/- If every selected support avoids a finite core `T`, their entire support
union avoids `T`. -/
theorem finiteSupportChoiceUnion_disjoint
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) {T : Finset ℕ}
    (hdisjoint : ∀ q : {n // n ∈ Q},
      Disjoint ((c q).1 : Set ℕ) (T : Set ℕ)) :
    Disjoint (finiteSupportChoiceUnion c : Set ℕ) (T : Set ℕ) := by
  rw [Set.disjoint_left]
  intro x hxU hxT
  obtain ⟨q, _hqattach, hxE⟩ :=
    Finset.mem_biUnion.mp (Finset.mem_coe.mp hxU)
  exact Set.disjoint_left.mp (hdisjoint q)
    (Finset.mem_coe.mpr hxE) hxT

/- Coordinated supports avoiding a nonempty transversal core cannot cover a
block containing that core.  This is the exact finite-exception repair step
needed from the anchor-containing alternative. -/
theorem block_difference_supportChoiceUnion_nonempty_of_coreDisjoint
    {F : ℕ → Finset ℕ} {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) {i : ℕ} {T : Finset ℕ}
    (hcore : T ⊆ F i) (hT : T.Nonempty)
    (hdisjoint : ∀ q : {n // n ∈ Q},
      Disjoint ((c q).1 : Set ℕ) (T : Set ℕ)) :
    (F i \ finiteSupportChoiceUnion c).Nonempty := by
  obtain ⟨x, hxT⟩ := hT
  refine ⟨x, Finset.mem_sdiff.mpr ⟨hcore hxT, ?_⟩⟩
  intro hxU
  exact Set.disjoint_left.mp
    (finiteSupportChoiceUnion_disjoint c hdisjoint)
    (Finset.mem_coe.mpr hxU) (Finset.mem_coe.mpr hxT)

/- A fixed finite selector certificate has an exact dual consequence: every
choice of one support for each certified target has a union containing one
whole block. -/
theorem exists_block_subset_supportChoiceUnion_of_certificate
    {F : ℕ → Finset ℕ} {R : SupportFamily}
    {Q : Finset ℕ}
    (hcert : ∀ s : BlockSelector F,
      ∃ n ∈ Q, DestroysAt R (selectedSet s) n)
    (c : FiniteSupportChoice R Q) :
    ∃ i, F i ⊆ finiteSupportChoiceUnion c := by
  classical
  by_contra hnone
  push Not at hnone
  have hdiff : ∀ i, (F i \ finiteSupportChoiceUnion c).Nonempty := by
    intro i
    rw [Finset.sdiff_nonempty]
    exact hnone i
  choose pick hpick using hdiff
  let s : BlockSelector F := fun i =>
    ⟨pick i, (Finset.mem_sdiff.mp (hpick i)).1⟩
  obtain ⟨n, hnQ, hdestroy⟩ := hcert s
  let q : {m // m ∈ Q} := ⟨n, hnQ⟩
  apply hdestroy (c q).1 (c q).2
  rw [Set.disjoint_left]
  intro x hxE hxs
  obtain ⟨i, hi⟩ := hxs
  have hxU : x ∈ finiteSupportChoiceUnion c :=
    finiteSupportChoice_subset_union c q hxE
  have hpickU := (Finset.mem_sdiff.mp (hpick i)).2
  change pick i = x at hi
  exact hpickU (hi ▸ hxU)

/- A certificate may be completely localized in one block.  If every
possible element selected from block `i` has a destruction witness in `Q`,
then `Q` certifies every global selector, independently of all other blocks. -/
theorem selectorCertificate_of_one_block_pointwise
    {F : ℕ → Finset ℕ} {R : SupportFamily} {Q : Finset ℕ} {i : ℕ}
    (hpoint : ∀ x ∈ F i, ∃ n ∈ Q,
      DestroysAt R ({x} : Set ℕ) n) :
    ∀ s : BlockSelector F,
      ∃ n ∈ Q, DestroysAt R (selectedSet s) n := by
  intro s
  obtain ⟨n, hnQ, hn⟩ := hpoint (s i).1 (s i).2
  refine ⟨n, hnQ, hn.mono ?_⟩
  intro x hx
  have hxs : x = (s i).1 := by simpa using hx
  exact hxs ▸ ⟨i, rfl⟩

/- If all supports have cardinality at most `r`, the union of a finite support
choice has cardinality at most `r * |Q|`. -/
theorem finiteSupportChoiceUnion_card_le
    {R : SupportFamily} {Q : Finset ℕ} {r : ℕ}
    (hcard : SupportsCardAtMost R r)
    (c : FiniteSupportChoice R Q) :
    (finiteSupportChoiceUnion c).card ≤ r * Q.card := by
  classical
  calc
    (finiteSupportChoiceUnion c).card ≤
        ∑ q ∈ Q.attach, (c q).1.card := Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q.attach, r := by
      gcongr with q hq
      exact hcard q.1 (c q).1 (c q).2
    _ = r * Q.card := by simp [Nat.mul_comm]

/- Quantitatively, a certificate with target set `Q` can only work if every
support choice covers some block of size at most `r * |Q|`. -/
theorem exists_small_covered_block_of_certificate
    {F : ℕ → Finset ℕ} {R : SupportFamily} {r : ℕ}
    (hcard : SupportsCardAtMost R r)
    {Q : Finset ℕ}
    (hcert : ∀ s : BlockSelector F,
      ∃ n ∈ Q, DestroysAt R (selectedSet s) n)
    (c : FiniteSupportChoice R Q) :
    ∃ i, F i ⊆ finiteSupportChoiceUnion c ∧
      (F i).card ≤ r * Q.card := by
  obtain ⟨i, hi⟩ :=
    exists_block_subset_supportChoiceUnion_of_certificate hcert c
  exact ⟨i, hi,
    le_trans (Finset.card_le_card hi)
      (finiteSupportChoiceUnion_card_le hcard c)⟩

/-- For every finite support choice, only finitely many blocks can be wholly
covered by its union. -/
theorem finite_indices_blocks_covered_by_supportChoice
    {A : Set ℕ} {F : ℕ → Finset ℕ} {R : SupportFamily}
    (P : IsFiniteBlockPartition A F)
    {Q : Finset ℕ} (c : FiniteSupportChoice R Q) :
    Set.Finite {i | F i ⊆ finiteSupportChoiceUnion c} :=
  P.finite_indices_blocks_subset (finiteSupportChoiceUnion c)

/-- The finite support-union formulation of selector avoidability: for one
finite-block partition, every finite collection of late targets admits chosen
supports whose union contains no entire block. -/
def HasFiniteBlockSupportUnionAvoidance
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∃ F, ∃ _P : IsFiniteBlockPartition A F, ∃ N,
    ∀ Q : Finset ℕ, (∀ n ∈ Q, N ≤ n) →
      ∃ c : FiniteSupportChoice R Q,
        ∀ i, (F i \ finiteSupportChoiceUnion c).Nonempty

/-- Avoiding whole blocks by a finite support union lets us choose a selector
outside that union, so all selected supports survive simultaneously. -/
theorem finiteSelectorAvoidability_of_blockSupportUnionAvoidance
    {A : Set ℕ} {R : SupportFamily}
    (havoid : HasFiniteBlockSupportUnionAvoidance R A) :
    HasFiniteSelectorAvoidability R A := by
  classical
  obtain ⟨F, P, N, hfinite⟩ := havoid
  refine ⟨F, P, N, ?_⟩
  intro Q hQN
  obtain ⟨c, hc⟩ := hfinite Q hQN
  choose pick hpick using hc
  let s : BlockSelector F := fun i =>
    ⟨pick i, (Finset.mem_sdiff.mp (hpick i)).1⟩
  refine ⟨s, ?_⟩
  intro n hnQ
  let q : {m // m ∈ Q} := ⟨n, hnQ⟩
  refine ⟨(c q).1, (c q).2, ?_⟩
  rw [Set.disjoint_left]
  intro x hxE hxs
  obtain ⟨i, hi⟩ := hxs
  have hxU : x ∈ finiteSupportChoiceUnion c :=
    finiteSupportChoice_subset_union c q hxE
  have hpickU := (Finset.mem_sdiff.mp (hpick i)).2
  change pick i = x at hi
  rw [← hi] at hxU
  exact hpickU hxU

/-- Conversely, supports surviving a selector have a union that omits the
selected element of every block. -/
theorem blockSupportUnionAvoidance_of_finiteSelectorAvoidability
    {A : Set ℕ} {R : SupportFamily}
    (havoid : HasFiniteSelectorAvoidability R A) :
    HasFiniteBlockSupportUnionAvoidance R A := by
  classical
  obtain ⟨F, P, N, hfinite⟩ := havoid
  refine ⟨F, P, N, ?_⟩
  intro Q hQN
  obtain ⟨s, hs⟩ := hfinite Q hQN
  have hex :
      ∀ q : {n // n ∈ Q},
        ∃ E, E ∈ R q.1 ∧
          Disjoint (E : Set ℕ) (selectedSet s) := by
    intro q
    obtain ⟨E, hER, hdisj⟩ := hs q.1 q.2
    exact ⟨E, hER, hdisj⟩
  choose support hsupportR hsupportDisj using hex
  let c : FiniteSupportChoice R Q := fun q =>
    ⟨support q, hsupportR q⟩
  refine ⟨c, ?_⟩
  intro i
  refine ⟨(s i).1, Finset.mem_sdiff.mpr ⟨(s i).2, ?_⟩⟩
  intro hselectedUnion
  obtain ⟨q, hqattach, hxq⟩ :=
    Finset.mem_biUnion.mp hselectedUnion
  apply Set.disjoint_left.mp (hsupportDisj q) hxq
  exact ⟨i, rfl⟩

/-- Finite selector avoidability is exactly finite blockwise avoidance by a
union of chosen supports. -/
theorem finiteBlockSupportUnionAvoidance_iff_finiteSelectorAvoidability
    {A : Set ℕ} {R : SupportFamily} :
    HasFiniteBlockSupportUnionAvoidance R A ↔
      HasFiniteSelectorAvoidability R A :=
  ⟨finiteSelectorAvoidability_of_blockSupportUnionAvoidance,
    blockSupportUnionAvoidance_of_finiteSelectorAvoidability⟩

/-- Finite avoidability is equivalent to failure of a finite selector
certificate. -/
theorem finiteSelectorAvoidability_iff_exists_failedCertificate
    {A : Set ℕ} {R : SupportFamily} :
    HasFiniteSelectorAvoidability R A ↔
      ∃ F, ∃ _P : IsFiniteBlockPartition A F,
        ∃ N, ¬ HasFiniteSelectorCertificate R F N := by
  constructor
  · rintro ⟨F, P, N, havoid⟩
    refine ⟨F, P, N, ?_⟩
    rintro ⟨Q, hQN, hQcert⟩
    obtain ⟨s, hs⟩ := havoid Q hQN
    obtain ⟨n, hnQ, hdestroy⟩ := hQcert s
    obtain ⟨E, hER, hdisj⟩ := hs n hnQ
    exact (hdestroy E hER) hdisj
  · rintro ⟨F, P, N, hfail⟩
    refine ⟨F, P, N, ?_⟩
    intro Q hQN
    by_contra hno
    push Not at hno
    apply hfail
    refine ⟨Q, hQN, ?_⟩
    intro s
    have hs := hno s
    obtain ⟨n, hnQ, hnsurvive⟩ := hs
    refine ⟨n, hnQ, ?_⟩
    intro E hER
    exact hnsurvive E hER

/-- Finite selector avoidability is exactly the negation of strong infinite
deletion. -/
theorem finiteSelectorAvoidability_iff_not_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily} :
    HasFiniteSelectorAvoidability R A ↔
      ¬ StrongInfiniteDeletion R A :=
  finiteSelectorAvoidability_iff_exists_failedCertificate.trans
    not_strongInfiniteDeletion_iff_exists_failedCertificate.symm

/-- The finite-block target and the coherent-choice target are equivalent. -/
theorem finiteSelectorAvoidability_iff_exists_tailChoice_noncofiniteUnion
    {A : Set ℕ} {R : SupportFamily} :
    HasFiniteSelectorAvoidability R A ↔
      ∃ N, ∃ c : TailSupportChoice R N,
        (A \ tailChoiceUnion c).Infinite :=
  finiteSelectorAvoidability_iff_not_strongInfiniteDeletion.trans
    exists_tailChoice_noncofiniteUnion_iff_not_strongInfiniteDeletion.symm

/-- Compactness converts finite selector avoidability into one genuinely
removable selector. -/
theorem removableBlockSelector_of_finiteSelectorAvoidability
    {A : Set ℕ} {R : SupportFamily}
    (havoid : HasFiniteSelectorAvoidability R A) :
    AdmitsRemovableBlockSelector R A := by
  rw [admitsRemovableBlockSelector_iff_exists_failedCertificate]
  exact finiteSelectorAvoidability_iff_exists_failedCertificate.mp havoid

/-- The finite support-union condition therefore produces the desired
removable block selector directly. -/
theorem removableBlockSelector_of_blockSupportUnionAvoidance
    {A : Set ℕ} {R : SupportFamily}
    (havoid : HasFiniteBlockSupportUnionAvoidance R A) :
    AdmitsRemovableBlockSelector R A :=
  removableBlockSelector_of_finiteSelectorAvoidability
    (finiteSelectorAvoidability_of_blockSupportUnionAvoidance havoid)

/-- This proposition isolates the unresolved combinatorial step without hiding
its quantifiers.  Proving it for additive representation hypergraphs would
establish the proposed contrapositive. -/
def MovingTransversalsYieldFiniteAvoidability
    (Rk Rsucc : SupportFamily) (A : Set ℕ) : Prop :=
  HasBoundedMovingTransversals Rsucc A →
  SuccessorTransversalsDescend Rk Rsucc A →
  HasFiniteSelectorAvoidability Rk A

/-- Once the unresolved moving-transversal implication is supplied,
compactness produces the desired removable selector. -/
theorem removableBlockSelector_of_movingTransversals
    {A : Set ℕ} {Rk Rsucc : SupportFamily}
    (hkey : MovingTransversalsYieldFiniteAvoidability Rk Rsucc A)
    (hmoving : HasBoundedMovingTransversals Rsucc A)
    (hdescend : SuccessorTransversalsDescend Rk Rsucc A) :
    AdmitsRemovableBlockSelector Rk A :=
  removableBlockSelector_of_finiteSelectorAvoidability
    (hkey hmoving hdescend)

end Erdos881
