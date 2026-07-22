import Erdos881.Lemmas

/-!
# Finite-block compactness for strong infinite deletion

This file formalizes the finite-block characterization from the investigation.
The representation data are packaged as a finite hypergraph `R n` of supports
for every represented natural number `n`.
-/

open scoped BigOperators

namespace Erdos881

/-! ## Blocks, selectors, and destruction -/

/-- `F` is a partition of `A` into nonempty, finite, pairwise-disjoint blocks
indexed by the natural numbers.  Finiteness is built into `Finset`. -/
structure IsFiniteBlockPartition (A : Set ℕ) (F : ℕ → Finset ℕ) : Prop where
  nonempty : ∀ i, (F i).Nonempty
  disjoint : Pairwise fun i j => Disjoint (F i) (F j)
  mem_iff : ∀ x, x ∈ A ↔ ∃ i, x ∈ F i

/-- A selector chooses one element from each block. -/
abbrev BlockSelector (F : ℕ → Finset ℕ) := ∀ i, {x // x ∈ F i}

/-- The set chosen by a selector. -/
def selectedSet {F : ℕ → Finset ℕ} (s : BlockSelector F) : Set ℕ :=
  Set.range fun i => (s i).1

/-- `B` destroys `n` when it meets every representation support of `n`. -/
def DestroysAt (R : SupportFamily) (B : Set ℕ) (n : ℕ) : Prop :=
  ∀ E ∈ R n, ¬ Disjoint (E : Set ℕ) B

/- Destruction is monotone in the deleted set. -/
theorem DestroysAt.mono
    {R : SupportFamily} {B C : Set ℕ} {n : ℕ}
    (hBC : B ⊆ C) (hB : DestroysAt R B n) :
    DestroysAt R C n := by
  intro E hER hEC
  apply hB E hER
  rw [Set.disjoint_left] at hEC ⊢
  intro x hxE hxB
  exact hEC hxE (hBC hxB)

/-- Every support in `R` consists of vertices from `A`. -/
def SupportsIn (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ n E, E ∈ R n → ∀ x ∈ E, x ∈ A

/-- The strong infinite-deletion condition, stated for support hypergraphs. -/
def StrongInfiniteDeletion (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ B, B ⊆ A → B.Infinite →
    ∀ N, ∃ n, N ≤ n ∧ DestroysAt R B n

/- Every individual vertex has arbitrarily late destruction witnesses.  For
additive bases this is the support-hypergraph form of ordinary minimality at
the fixed order. -/
def HasArbitrarilyLateSingletonDestruction
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ N, ∃ n, N ≤ n ∧ DestroysAt R ({a} : Set ℕ) n

/-- All but finitely many vertices have arbitrarily late singleton
destruction witnesses.  The exceptional finite set is useful for
"finite-booster" constructions: the booster vertices need not themselves
have private witnesses. -/
def HasCofiniteSingletonDestruction
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∃ F : Finset ℕ, ∀ a ∈ A, a ∉ F →
    ∀ N, ∃ n, N ≤ n ∧ DestroysAt R ({a} : Set ℕ) n

/-- A finite set of integers certifies that every selector destroys at least
one integer in the set. -/
def HasFiniteSelectorCertificate
    (R : SupportFamily) (F : ℕ → Finset ℕ) (N : ℕ) : Prop :=
  ∃ S : Finset ℕ,
    (∀ n ∈ S, N ≤ n) ∧
      ∀ s : BlockSelector F, ∃ n ∈ S, DestroysAt R (selectedSet s) n

/- Every finite selector certificate contains a cardinal-minimal
subcertificate.  Minimality localizes its targets: for each `q` in the
subcertificate there is a selector which destroys `q` and no other target in
the same subcertificate. -/
theorem exists_minimal_targetLocalized_subcertificate
    {R : SupportFamily} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (hcert : ∀ s : BlockSelector F,
      ∃ q ∈ Q, DestroysAt R (selectedSet s) q) :
    ∃ Q₀ : Finset ℕ, Q₀ ⊆ Q ∧
      (∀ s : BlockSelector F,
        ∃ q ∈ Q₀, DestroysAt R (selectedSet s) q) ∧
      ∀ q ∈ Q₀, ∃ s : BlockSelector F,
        DestroysAt R (selectedSet s) q ∧
        ∀ q' ∈ Q₀, q' ≠ q →
          ¬ DestroysAt R (selectedSet s) q' := by
  classical
  let Cert : Finset ℕ → Prop := fun S =>
    ∀ s : BlockSelector F,
      ∃ q ∈ S, DestroysAt R (selectedSet s) q
  let candidates : Finset (Finset ℕ) := Q.powerset.filter Cert
  have hQcandidates : Q ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hcert⟩
  have hcandidates : candidates.Nonempty := ⟨Q, hQcandidates⟩
  obtain ⟨Q₀, hQ₀candidates, hminimalCard⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hQ₀Q : Q₀ ⊆ Q :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hQ₀candidates).1
  have hQ₀cert : Cert Q₀ :=
    (Finset.mem_filter.mp hQ₀candidates).2
  have heraseNotCert : ∀ q ∈ Q₀, ¬ Cert (Q₀.erase q) := by
    intro q hqQ₀ herase
    have heraseQ : Q₀.erase q ⊆ Q :=
      (Finset.erase_subset q Q₀).trans hQ₀Q
    have heraseCandidate : Q₀.erase q ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr heraseQ, herase⟩
    have hcardle := hminimalCard (Q₀.erase q) heraseCandidate
    have hcardlt : (Q₀.erase q).card < Q₀.card :=
      Finset.card_lt_card (Finset.erase_ssubset hqQ₀)
    exact (not_le_of_gt hcardlt) hcardle
  refine ⟨Q₀, hQ₀Q, hQ₀cert, ?_⟩
  intro q hqQ₀
  have hfail := heraseNotCert q hqQ₀
  change ¬ ∀ s : BlockSelector F,
    ∃ q' ∈ Q₀.erase q, DestroysAt R (selectedSet s) q' at hfail
  push Not at hfail
  obtain ⟨s, hs⟩ := hfail
  obtain ⟨r, hrQ₀, hrdestroy⟩ := hQ₀cert s
  have hrq : r = q := by
    by_contra hrq
    exact hs r (Finset.mem_erase.mpr ⟨hrq, hrQ₀⟩) hrdestroy
  subst r
  refine ⟨s, hrdestroy, ?_⟩
  intro q' hq'Q₀ hq'q
  exact hs q' (Finset.mem_erase.mpr ⟨hq'q, hq'Q₀⟩)

/-- A finite selector certificate remains target-localizable when it is only
required on a prescribed class of selectors.  This is the form needed when
each block has a smaller dedicated core and the argument only permits
selectors whose values lie in those cores. -/
theorem exists_minimal_targetLocalized_subcertificate_on
    {R : SupportFamily} {F : ℕ → Finset ℕ} {Q : Finset ℕ}
    (Good : BlockSelector F → Prop)
    (hcert : ∀ s : BlockSelector F, Good s →
      ∃ q ∈ Q, DestroysAt R (selectedSet s) q) :
    ∃ Q₀ : Finset ℕ, Q₀ ⊆ Q ∧
      (∀ s : BlockSelector F, Good s →
        ∃ q ∈ Q₀, DestroysAt R (selectedSet s) q) ∧
      ∀ q ∈ Q₀, ∃ s : BlockSelector F,
        Good s ∧
        DestroysAt R (selectedSet s) q ∧
        ∀ q' ∈ Q₀, q' ≠ q →
          ¬ DestroysAt R (selectedSet s) q' := by
  classical
  let Cert : Finset ℕ → Prop := fun S =>
    ∀ s : BlockSelector F, Good s →
      ∃ q ∈ S, DestroysAt R (selectedSet s) q
  let candidates : Finset (Finset ℕ) := Q.powerset.filter Cert
  have hQcandidates : Q ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hcert⟩
  have hcandidates : candidates.Nonempty := ⟨Q, hQcandidates⟩
  obtain ⟨Q₀, hQ₀candidates, hminimalCard⟩ :=
    Finset.exists_min_image candidates Finset.card hcandidates
  have hQ₀Q : Q₀ ⊆ Q :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hQ₀candidates).1
  have hQ₀cert : Cert Q₀ :=
    (Finset.mem_filter.mp hQ₀candidates).2
  have heraseNotCert : ∀ q ∈ Q₀, ¬ Cert (Q₀.erase q) := by
    intro q hqQ₀ herase
    have heraseQ : Q₀.erase q ⊆ Q :=
      (Finset.erase_subset q Q₀).trans hQ₀Q
    have heraseCandidate : Q₀.erase q ∈ candidates :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr heraseQ, herase⟩
    have hcardle := hminimalCard (Q₀.erase q) heraseCandidate
    have hcardlt : (Q₀.erase q).card < Q₀.card :=
      Finset.card_lt_card (Finset.erase_ssubset hqQ₀)
    exact (not_le_of_gt hcardlt) hcardle
  refine ⟨Q₀, hQ₀Q, hQ₀cert, ?_⟩
  intro q hqQ₀
  have hfail := heraseNotCert q hqQ₀
  change ¬ ∀ s : BlockSelector F, Good s →
    ∃ q' ∈ Q₀.erase q, DestroysAt R (selectedSet s) q' at hfail
  push Not at hfail
  obtain ⟨s, hsGood, hs⟩ := hfail
  obtain ⟨r, hrQ₀, hrdestroy⟩ := hQ₀cert s hsGood
  have hrq : r = q := by
    by_contra hrq
    exact hs r (Finset.mem_erase.mpr ⟨hrq, hrQ₀⟩) hrdestroy
  subst r
  refine ⟨s, hsGood, hrdestroy, ?_⟩
  intro q' hq'Q₀ hq'q
  exact hs q' (Finset.mem_erase.mpr ⟨hq'q, hq'Q₀⟩)

/-- The finite-certificate property quantified over every finite-block
partition and every lower threshold. -/
def FiniteBlockCertificateProperty
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∀ F, IsFiniteBlockPartition A F →
    ∀ N, HasFiniteSelectorCertificate R F N

/- Singleton witnesses can produce every finite-block certificate in a
completely localized way: the certificate only examines the element selected
from block zero and ignores all other blocks. -/
theorem finiteBlockCertificates_localized_of_singletonDestruction
    {A : Set ℕ} {R : SupportFamily}
    (hsingle : HasArbitrarilyLateSingletonDestruction R A) :
    FiniteBlockCertificateProperty R A := by
  classical
  intro F P N
  have hwitness : ∀ x, x ∈ F 0 → ∃ n,
      N ≤ n ∧ DestroysAt R ({x} : Set ℕ) n := by
    intro x hx
    apply hsingle x
    exact (P.mem_iff x).2 ⟨0, hx⟩
  choose target hlower hdestroy using hwitness
  let target' : {x // x ∈ F 0} → ℕ := fun x => target x.1 x.2
  let Q : Finset ℕ := (F 0).attach.image target'
  refine ⟨Q, ?_, ?_⟩
  · intro n hnQ
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hnQ
    exact hlower x.1 x.2
  · intro s
    let x := (s 0).1
    have hx : x ∈ F 0 := (s 0).2
    let x' : {y // y ∈ F 0} := ⟨x, hx⟩
    refine ⟨target' x', Finset.mem_image.mpr ⟨x', by simp, rfl⟩, ?_⟩
    apply (hdestroy x hx).mono
    intro y hy
    have hyx : y = x := by simpa using hy
    exact hyx ▸ ⟨0, rfl⟩

/- In particular, arbitrarily late singleton witnesses imply the strong
infinite-deletion property. -/
theorem strongInfiniteDeletion_of_singletonDestruction
    {A : Set ℕ} {R : SupportFamily}
    (hsingle : HasArbitrarilyLateSingletonDestruction R A) :
    StrongInfiniteDeletion R A := by
  intro B hBA hB N
  obtain ⟨a, haB⟩ := hB.nonempty
  obtain ⟨n, hn, hdestroy⟩ := hsingle a (hBA haB) N
  refine ⟨n, hn, hdestroy.mono ?_⟩
  intro x hx
  have hxa : x = a := by simpa using hx
  exact hxa ▸ haB

/- A finite exceptional set does not weaken the conclusion for infinite
deletions: every infinite deleted set contains a nonexceptional vertex. -/
theorem strongInfiniteDeletion_of_cofiniteSingletonDestruction
    {A : Set ℕ} {R : SupportFamily}
    (hsingle : HasCofiniteSingletonDestruction R A) :
    StrongInfiniteDeletion R A := by
  obtain ⟨F, hF⟩ := hsingle
  intro B hBA hB N
  have hnotSub : ¬ B ⊆ (F : Set ℕ) := by
    intro hBF
    exact hB (F.finite_toSet.subset hBF)
  obtain ⟨a, haB, haF⟩ := Set.not_subset.mp hnotSub
  have haFinset : a ∉ F := by simpa using haF
  obtain ⟨n, hn, hdestroy⟩ := hF a (hBA haB) haFinset N
  refine ⟨n, hn, hdestroy.mono ?_⟩
  intro x hx
  have hxa : x = a := by simpa using hx
  exact hxa ▸ haB

/-- A block partition admits a removable selector if deleting that selector
leaves a support for every sufficiently large integer. -/
def AdmitsRemovableBlockSelector
    (R : SupportFamily) (A : Set ℕ) : Prop :=
  ∃ F, ∃ _P : IsFiniteBlockPartition A F,
    ∃ s : BlockSelector F, ∃ N,
      ∀ n, N ≤ n → ∃ E ∈ R n, Disjoint (E : Set ℕ) (selectedSet s)

theorem IsFiniteBlockPartition.selector_injective
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F) :
    Function.Injective fun i => (s i).1 := by
  intro i j hij
  by_contra hne
  have hd := P.disjoint hne
  change Disjoint (F i) (F j) at hd
  change (s i).1 = (s j).1 at hij
  rw [Finset.disjoint_left] at hd
  apply hd (s i).2
  rw [hij]
  exact (s j).2

theorem IsFiniteBlockPartition.selectedSet_infinite
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F) :
    (selectedSet s).Infinite :=
  Set.infinite_range_of_injective (P.selector_injective s)

theorem IsFiniteBlockPartition.selectedSet_subset
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F) :
    selectedSet s ⊆ A := by
  rintro x ⟨i, rfl⟩
  exact (P.mem_iff _).2 ⟨i, (s i).2⟩

/-- A finite set can contain only finitely many entire blocks of a
finite-block partition. -/
theorem IsFiniteBlockPartition.finite_indices_blocks_subset
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (U : Finset ℕ) :
    Set.Finite {i | F i ⊆ U} := by
  classical
  let s : BlockSelector F := fun i =>
    ⟨(P.nonempty i).choose, (P.nonempty i).choose_spec⟩
  let pick : ℕ → ℕ := fun i => (s i).1
  have hpick_injective : Function.Injective pick :=
    P.selector_injective s
  have hpreimage : (pick ⁻¹' (U : Set ℕ)).Finite :=
    Set.Finite.preimage hpick_injective.injOn U.finite_toSet
  apply hpreimage.subset
  intro i hi
  exact hi (s i).2

/-! ## Finite dependence and openness -/

/-- A predicate on a product depends only on coordinates in `J`. -/
def DependsOnFinset
    {X : ℕ → Type*} (J : Finset ℕ) (p : (∀ i, X i) → Prop) : Prop :=
  ∀ s t, (∀ i ∈ J, s i = t i) → (p s ↔ p t)

/-- A predicate depending on finitely many discrete coordinates defines an
open subset of the product. -/
theorem isOpen_setOf_of_dependsOnFinset
    {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, DiscreteTopology (X i)]
    {J : Finset ℕ} {p : (∀ i, X i) → Prop}
    (hp : DependsOnFinset J p) :
    IsOpen {s | p s} := by
  rw [isOpen_pi_iff]
  intro s hs
  refine ⟨J, fun i => {s i}, ?_, ?_⟩
  · intro i hi
    exact ⟨isOpen_discrete _, Set.mem_singleton _⟩
  · intro t ht
    apply (hp s t ?_).1 hs
    intro i hi
    exact (Set.mem_singleton_iff.mp ((Set.mem_pi.mp ht) i hi)).symm

/-- The finite set of all vertices occurring in supports for `n`. -/
def supportVertices (R : SupportFamily) (n : ℕ) : Finset ℕ :=
  (R n).biUnion id

/-- The block containing a vertex of `A`.  Outside `A` the value is arbitrary. -/
noncomputable def blockIndex
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (x : ℕ) : ℕ := by
  classical
  exact if hx : x ∈ A then Classical.choose ((P.mem_iff x).1 hx) else 0

theorem IsFiniteBlockPartition.mem_blockIndex
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) {x : ℕ} (hx : x ∈ A) :
    x ∈ F (blockIndex P x) := by
  simp only [blockIndex, dif_pos hx]
  exact Classical.choose_spec ((P.mem_iff x).1 hx)

theorem IsFiniteBlockPartition.blockIndex_eq_of_mem
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) {x i : ℕ} (hxi : x ∈ F i) :
    blockIndex P x = i := by
  have hxA : x ∈ A := (P.mem_iff x).2 ⟨i, hxi⟩
  by_contra hne
  have hd := P.disjoint hne
  change Disjoint (F (blockIndex P x)) (F i) at hd
  rw [Finset.disjoint_left] at hd
  exact hd (P.mem_blockIndex hxA) hxi

/-- An infinite subset of a finite-block partition must meet infinitely many
blocks.  Equivalently, the block-index map has infinite image on that subset.
The only input is that every individual block is finite. -/
theorem IsFiniteBlockPartition.infinite_blockIndex_image
    {A L : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hLA : L ⊆ A) (hL : L.Infinite) :
    (blockIndex P '' L).Infinite := by
  by_contra himage
  apply hL
  apply Set.Finite.of_finite_fibers (blockIndex P)
    (Set.not_infinite.mp himage)
  intro i hiImage
  apply (F i).finite_toSet.subset
  rintro x ⟨hxL, hxIndex⟩
  have hxA : x ∈ A := hLA hxL
  have hxBlock : x ∈ F (blockIndex P x) :=
    P.mem_blockIndex hxA
  rw [hxIndex] at hxBlock
  exact hxBlock

/-- Every infinite subset of a finite-block partition can be thinned to an
infinite block transversal: no two retained points lie in the same block. -/
theorem IsFiniteBlockPartition.exists_infinite_blockTransversal
    {A L : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hLA : L ⊆ A) (hL : L.Infinite) :
    ∃ T, T ⊆ L ∧ T.Infinite ∧
      Set.InjOn (blockIndex P) T := by
  classical
  let I : Set ℕ := blockIndex P '' L
  have hI : I.Infinite := by
    simpa [I] using P.infinite_blockIndex_image hLA hL
  have hwitness : ∀ i, i ∈ I →
      ∃ x, x ∈ L ∧ blockIndex P x = i := by
    intro i hi
    simpa [I] using hi
  choose point hpointL hpointIndex using hwitness
  let pick : ℕ → ℕ := fun i =>
    if hi : i ∈ I then point i hi else 0
  have hpickL : ∀ i ∈ I, pick i ∈ L := by
    intro i hi
    simpa [pick, hi] using hpointL i hi
  have hpickIndex : ∀ i ∈ I, blockIndex P (pick i) = i := by
    intro i hi
    simpa [pick, hi] using hpointIndex i hi
  have hpickInj : Set.InjOn pick I := by
    intro i hi j hj hpickEq
    calc
      i = blockIndex P (pick i) := (hpickIndex i hi).symm
      _ = blockIndex P (pick j) := by rw [hpickEq]
      _ = j := hpickIndex j hj
  let T : Set ℕ := pick '' I
  have hTInfinite : T.Infinite := hI.image hpickInj
  have hTL : T ⊆ L := by
    rintro x ⟨i, hi, rfl⟩
    exact hpickL i hi
  have hindexInj : Set.InjOn (blockIndex P) T := by
    rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩ hindex
    have hij : i = j := by
      calc
        i = blockIndex P (pick i) := (hpickIndex i hi).symm
        _ = blockIndex P (pick j) := hindex
        _ = j := hpickIndex j hj
    subst j
    rfl
  exact ⟨T, hTL, hTInfinite, hindexInj⟩

/-- Removing one point from each of infinitely many distinct blocks does not
exhaust a partition whose blocks all contain at least two points.  Choosing
an alternate point in each used block gives an explicit infinite subset of
the residual reservoir. -/
theorem IsFiniteBlockPartition.infinite_diff_of_blockIndex_injective
    {A T : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hTA : T ⊆ A) (hT : T.Infinite)
    (hindexInj : Set.InjOn (blockIndex P) T)
    (hblockTwo : ∀ i, 2 ≤ (F i).card) :
    (A \ T).Infinite := by
  classical
  have haltExists : ∀ x, x ∈ T →
      ∃ y, y ∈ F (blockIndex P x) ∧ y ≠ x := by
    intro x hxT
    have hxA : x ∈ A := hTA hxT
    have hxBlock : x ∈ F (blockIndex P x) :=
      P.mem_blockIndex hxA
    by_contra hnone
    push Not at hnone
    have hsubset : F (blockIndex P x) ⊆ {x} := by
      intro y hy
      exact Finset.mem_singleton.mpr (hnone y hy)
    have hcard : (F (blockIndex P x)).card ≤ 1 := by
      simpa using Finset.card_le_card hsubset
    have htwo := hblockTwo (blockIndex P x)
    omega
  choose alt haltBlock haltNe using haltExists
  let pick : ℕ → ℕ := fun x =>
    if hx : x ∈ T then alt x hx else 0
  have hpickBlock : ∀ x ∈ T,
      pick x ∈ F (blockIndex P x) := by
    intro x hx
    simpa [pick, hx] using haltBlock x hx
  have hpickNe : ∀ x ∈ T, pick x ≠ x := by
    intro x hx
    simpa [pick, hx] using haltNe x hx
  have hpickIndex : ∀ x ∈ T,
      blockIndex P (pick x) = blockIndex P x := by
    intro x hx
    exact P.blockIndex_eq_of_mem (hpickBlock x hx)
  have hpickNotT : ∀ x ∈ T, pick x ∉ T := by
    intro x hx hpickT
    have heq : pick x = x :=
      hindexInj hpickT hx (hpickIndex x hx)
    exact hpickNe x hx heq
  have hpickA : ∀ x ∈ T, pick x ∈ A := by
    intro x hx
    exact (P.mem_iff (pick x)).2
      ⟨blockIndex P x, hpickBlock x hx⟩
  have hpickInj : Set.InjOn pick T := by
    intro x hx y hy hpickEq
    apply hindexInj hx hy
    calc
      blockIndex P x = blockIndex P (pick x) :=
        (hpickIndex x hx).symm
      _ = blockIndex P (pick y) := by rw [hpickEq]
      _ = blockIndex P y := hpickIndex y hy
  have hRange : (pick '' T).Infinite := hT.image hpickInj
  apply hRange.mono
  rintro y ⟨x, hx, rfl⟩
  exact ⟨hpickA x hx, hpickNotT x hx⟩

theorem IsFiniteBlockPartition.mem_selectedSet_iff
    {A : Set ℕ} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F) (s : BlockSelector F)
    {x : ℕ} :
    x ∈ selectedSet s ↔ (s (blockIndex P x)).1 = x := by
  constructor
  · rintro ⟨i, hi⟩
    have hidx : blockIndex P x = i := by
      apply P.blockIndex_eq_of_mem
      rw [← hi]
      exact (s i).2
    rw [hidx]
    exact hi
  · intro hx
    exact ⟨blockIndex P x, hx⟩

/-- Destruction at `n` depends only on the block coordinates containing
vertices of supports for `n`. -/
theorem destroysAt_dependsOnFinset
    {A : Set ℕ} {F : ℕ → Finset ℕ} {R : SupportFamily}
    (P : IsFiniteBlockPartition A F) (n : ℕ) :
    DependsOnFinset
      ((supportVertices R n).image (blockIndex P))
      (fun s : BlockSelector F => DestroysAt R (selectedSet s) n) := by
  intro s t hst
  constructor
  · intro hs E hER
    obtain ⟨x, hxE, hxs⟩ := Set.not_disjoint_iff.mp (hs E hER)
    apply Set.not_disjoint_iff.mpr
    refine ⟨x, hxE, ?_⟩
    rw [P.mem_selectedSet_iff t]
    rw [P.mem_selectedSet_iff s] at hxs
    have hidx : blockIndex P x ∈
        (supportVertices R n).image (blockIndex P) := by
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨E, hER, hxE⟩
    exact congrArg Subtype.val (hst _ hidx) ▸ hxs
  · intro ht E hER
    obtain ⟨x, hxE, hxt⟩ := Set.not_disjoint_iff.mp (ht E hER)
    apply Set.not_disjoint_iff.mpr
    refine ⟨x, hxE, ?_⟩
    rw [P.mem_selectedSet_iff s]
    rw [P.mem_selectedSet_iff t] at hxt
    have hidx : blockIndex P x ∈
        (supportVertices R n).image (blockIndex P) := by
      apply Finset.mem_image.mpr
      refine ⟨x, ?_, rfl⟩
      exact Finset.mem_biUnion.mpr ⟨E, hER, hxE⟩
    exact congrArg Subtype.val (hst _ hidx) |>.symm ▸ hxt

theorem isOpen_destroysAt_selectors
    {A : Set ℕ} {F : ℕ → Finset ℕ} {R : SupportFamily}
    (P : IsFiniteBlockPartition A F) (n : ℕ) :
    IsOpen {s : BlockSelector F | DestroysAt R (selectedSet s) n} :=
  isOpen_setOf_of_dependsOnFinset (destroysAt_dependsOnFinset P n)

theorem not_destroysAt_iff
    {R : SupportFamily} {B : Set ℕ} {n : ℕ} :
    ¬ DestroysAt R B n ↔
      ∃ E ∈ R n, Disjoint (E : Set ℕ) B := by
  simp only [DestroysAt, not_forall, not_not]
  aesop

/-! ## Compactness direction -/

/-- For a fixed block partition, a finite certificate exists exactly when
every selector destroys some integer above the threshold. -/
theorem hasFiniteSelectorCertificate_iff
    {A : Set ℕ} {F : ℕ → Finset ℕ} {R : SupportFamily}
    (P : IsFiniteBlockPartition A F) (N : ℕ) :
    HasFiniteSelectorCertificate R F N ↔
      ∀ s : BlockSelector F,
        ∃ n, N ≤ n ∧ DestroysAt R (selectedSet s) n := by
  constructor
  · rintro ⟨S, hSN, hS⟩ s
    obtain ⟨n, hnS, hdestroy⟩ := hS s
    exact ⟨n, hSN n hnS, hdestroy⟩
  · intro hall
    let I := {n : ℕ // N ≤ n}
    let V : I → Set (BlockSelector F) :=
      fun q => {s | DestroysAt R (selectedSet s) q.1}
    have hVopen : ∀ q, IsOpen (V q) := by
      intro q
      exact isOpen_destroysAt_selectors P q.1
    have hcover : (Set.univ : Set (BlockSelector F)) ⊆ ⋃ q, V q := by
      intro s hs
      obtain ⟨n, hn, hdestroy⟩ := hall s
      exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hdestroy⟩
    obtain ⟨t, ht⟩ :=
      isCompact_univ.elim_finite_subcover V hVopen hcover
    refine ⟨t.image fun q => q.1, ?_, ?_⟩
    · intro n hn
      obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp hn
      exact q.2
    · intro s
      have hs := ht (Set.mem_univ s)
      simp only [Set.mem_iUnion] at hs
      obtain ⟨q, hqt, hqV⟩ := hs
      exact ⟨q.1, Finset.mem_image.mpr ⟨q, hqt, rfl⟩, hqV⟩

/-- This is the exact target needed from a proposed contrapositive: failure of
one finite certificate is equivalent to a selector whose deletion preserves a
representation of every integer above the threshold. -/
theorem not_hasFiniteSelectorCertificate_iff_exists_removableSelector
    {A : Set ℕ} {F : ℕ → Finset ℕ} {R : SupportFamily}
    (P : IsFiniteBlockPartition A F) (N : ℕ) :
    ¬ HasFiniteSelectorCertificate R F N ↔
      ∃ s : BlockSelector F, ∀ n, N ≤ n →
        ∃ E ∈ R n, Disjoint (E : Set ℕ) (selectedSet s) := by
  rw [hasFiniteSelectorCertificate_iff P N]
  simp only [not_forall, not_exists, not_and_or, not_destroysAt_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro n hn
    rcases hs n with hnN | hsurvive
    · exact (hnN hn).elim
    · exact hsurvive
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro n
    by_cases hn : N ≤ n
    · exact Or.inr (hs n hn)
    · exact Or.inl hn

/-- Producing a removable block selector is exactly the same as making the
finite-certificate property fail for one partition and one threshold. -/
theorem admitsRemovableBlockSelector_iff_exists_failedCertificate
    {A : Set ℕ} {R : SupportFamily} :
    AdmitsRemovableBlockSelector R A ↔
      ∃ F, ∃ _P : IsFiniteBlockPartition A F,
        ∃ N, ¬ HasFiniteSelectorCertificate R F N := by
  constructor
  · rintro ⟨F, P, s, N, hs⟩
    refine ⟨F, P, N, ?_⟩
    exact (not_hasFiniteSelectorCertificate_iff_exists_removableSelector
      P N).2 ⟨s, hs⟩
  · rintro ⟨F, P, N, hfail⟩
    obtain ⟨s, hs⟩ :=
      (not_hasFiniteSelectorCertificate_iff_exists_removableSelector
        P N).1 hfail
    exact ⟨F, P, s, N, hs⟩

/-- Strong infinite deletion supplies a finite certificate for every
finite-block selector space. -/
theorem finiteBlockCertificates_of_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily}
    (hstrong : StrongInfiniteDeletion R A) :
    FiniteBlockCertificateProperty R A := by
  intro F P N
  let I := {n : ℕ // N ≤ n}
  let V : I → Set (BlockSelector F) :=
    fun q => {s | DestroysAt R (selectedSet s) q.1}
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    exact isOpen_destroysAt_selectors P q.1
  have hcover : (Set.univ : Set (BlockSelector F)) ⊆ ⋃ q, V q := by
    intro s hs
    obtain ⟨n, hn, hdestroy⟩ := hstrong (selectedSet s)
      (P.selectedSet_subset s) (P.selectedSet_infinite s) N
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hdestroy⟩
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover V hVopen hcover
  refine ⟨t.image fun q => q.1, ?_, ?_⟩
  · intro n hn
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp hn
    exact q.2
  · intro s
    have hs := ht (Set.mem_univ s)
    simp only [Set.mem_iUnion] at hs
    obtain ⟨q, hqt, hqV⟩ := hs
    exact ⟨q.1, Finset.mem_image.mpr ⟨q, hqt, rfl⟩, hqV⟩

/-- Strong deletion also supplies finite certificates on a block partition
of any infinite deletion reservoir `C ⊆ A`.  Consequently a finite retained
core may be omitted from every selector without weakening compactness. -/
theorem finiteBlockCertificates_on_subset_of_strongInfiniteDeletion
    {A C : Set ℕ} {R : SupportFamily}
    (hstrong : StrongInfiniteDeletion R A)
    (hCA : C ⊆ A)
    (F : ℕ → Finset ℕ) (P : IsFiniteBlockPartition C F) (N : ℕ) :
    HasFiniteSelectorCertificate R F N := by
  let I := {n : ℕ // N ≤ n}
  let V : I → Set (BlockSelector F) :=
    fun q => {s | DestroysAt R (selectedSet s) q.1}
  have hVopen : ∀ q, IsOpen (V q) := by
    intro q
    exact isOpen_destroysAt_selectors P q.1
  have hcover : (Set.univ : Set (BlockSelector F)) ⊆ ⋃ q, V q := by
    intro s hs
    obtain ⟨n, hn, hdestroy⟩ := hstrong (selectedSet s)
      (fun x hx => hCA (P.selectedSet_subset s hx))
      (P.selectedSet_infinite s) N
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, hdestroy⟩
  obtain ⟨t, ht⟩ :=
    isCompact_univ.elim_finite_subcover V hVopen hcover
  refine ⟨t.image fun q => q.1, ?_, ?_⟩
  · intro n hn
    obtain ⟨q, hqt, rfl⟩ := Finset.mem_image.mp hn
    exact q.2
  · intro s
    have hs := ht (Set.mem_univ s)
    simp only [Set.mem_iUnion] at hs
    obtain ⟨q, hqt, hqV⟩ := hs
    exact ⟨q.1, Finset.mem_image.mpr ⟨q, hqt, rfl⟩, hqV⟩

/-! ## Converse direction -/

/-- Every infinite `B ⊆ A` can be made the canonical selector of a partition
whose blocks have at most two elements: block `i` contains the `i`th element
of `B`, and additionally contains `i` itself when `i ∈ A \ B`. -/
theorem strongInfiniteDeletion_of_finiteBlockCertificates
    {A : Set ℕ} {R : SupportFamily}
    (hcert : FiniteBlockCertificateProperty R A) :
    StrongInfiniteDeletion R A := by
  intro B hBA hB N
  classical
  letI : Infinite B := hB.to_subtype
  letI : Denumerable B := Denumerable.ofEncodableOfInfinite B
  let e : ℕ ≃ B := (Denumerable.eqv B).symm
  let b : ℕ → ℕ := fun i => (e i).1
  have hbB : ∀ i, b i ∈ B := fun i => (e i).2
  have hbinj : Function.Injective b := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hbsurj : ∀ x ∈ B, ∃ i, b i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  let F : ℕ → Finset ℕ := fun i =>
    insert (b i) (if i ∈ A ∧ i ∉ B then {i} else ∅)
  have P : IsFiniteBlockPartition A F := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact ⟨b i, Finset.mem_insert_self _ _⟩
    · intro i j hij
      rw [Finset.disjoint_left]
      intro x hxi hxj
      by_cases hi : i ∈ A ∧ i ∉ B <;> by_cases hj : j ∈ A ∧ j ∉ B
      · simp [F, hi, hj] at hxi hxj
        rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
        · exact hij (hbinj (hxi.symm.trans hxj))
        · exact hj.2 (by
            rw [← hxj, hxi]
            exact hbB i)
        · exact hi.2 (by
            rw [← hxi, hxj]
            exact hbB j)
        · exact hij (hxi.symm.trans hxj)
      · simp [F, hi, hj] at hxi hxj
        rcases hxi with hxi | hxi
        · exact hij (hbinj (hxi.symm.trans hxj))
        · exact hi.2 (by
            rw [← hxi, hxj]
            exact hbB j)
      · simp [F, hi, hj] at hxi hxj
        rcases hxj with hxj | hxj
        · exact hij (hbinj (hxi.symm.trans hxj))
        · exact hj.2 (by
            rw [← hxj, hxi]
            exact hbB i)
      · simp [F, hi, hj] at hxi hxj
        exact hij (hbinj (hxi.symm.trans hxj))
    · intro x
      constructor
      · intro hxA
        by_cases hxB : x ∈ B
        · obtain ⟨i, hi⟩ := hbsurj x hxB
          exact ⟨i, Finset.mem_insert.mpr (Or.inl hi.symm)⟩
        · refine ⟨x, ?_⟩
          simp [F, hxA, hxB]
      · rintro ⟨i, hxi⟩
        by_cases hi : i ∈ A ∧ i ∉ B
        · simp [F, hi] at hxi
          rcases hxi with hxi | hxi
          · exact hBA (hxi ▸ hbB i)
          · exact hxi ▸ hi.1
        · simp [F, hi] at hxi
          exact hBA (hxi ▸ hbB i)
  let s : BlockSelector F := fun i =>
    ⟨b i, Finset.mem_insert_self _ _⟩
  have hsB : selectedSet s = B := by
    change Set.range b = B
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact hbB i
    · intro hx
      obtain ⟨i, hi⟩ := hbsurj x hx
      exact ⟨i, hi⟩
  obtain ⟨S, hSN, hS⟩ := hcert F P N
  obtain ⟨n, hnS, hdestroy⟩ := hS s
  rw [hsB] at hdestroy
  exact ⟨n, hSN n hnS, hdestroy⟩

/-- The exact finite-block compactness characterization. -/
theorem strongInfiniteDeletion_iff_finiteBlockCertificates
    {A : Set ℕ} {R : SupportFamily} :
    StrongInfiniteDeletion R A ↔ FiniteBlockCertificateProperty R A :=
  ⟨finiteBlockCertificates_of_strongInfiniteDeletion,
    strongInfiniteDeletion_of_finiteBlockCertificates⟩

/-- Negating strong deletion produces exactly one partition and threshold with
no finite selector certificate. -/
theorem not_strongInfiniteDeletion_iff_exists_failedCertificate
    {A : Set ℕ} {R : SupportFamily} :
    ¬ StrongInfiniteDeletion R A ↔
      ∃ F, ∃ _P : IsFiniteBlockPartition A F,
        ∃ N, ¬ HasFiniteSelectorCertificate R F N := by
  constructor
  · intro hnot
    by_contra hnoFailure
    apply hnot
    apply strongInfiniteDeletion_of_finiteBlockCertificates
    intro F P N
    by_contra hfail
    exact hnoFailure ⟨F, P, N, hfail⟩
  · rintro ⟨F, P, N, hfail⟩ hstrong
    exact hfail (finiteBlockCertificates_of_strongInfiniteDeletion
      hstrong F P N)

/-- A removable block selector is not merely sufficient but equivalent to
failure of strong infinite deletion. -/
theorem admitsRemovableBlockSelector_iff_not_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily} :
    AdmitsRemovableBlockSelector R A ↔
      ¬ StrongInfiniteDeletion R A :=
  admitsRemovableBlockSelector_iff_exists_failedCertificate.trans
    not_strongInfiniteDeletion_iff_exists_failedCertificate.symm

end Erdos881
