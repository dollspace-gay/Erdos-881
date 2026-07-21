import Erdos881.MovingTransversals

/-!
# Amplifying finite selector certificates

Strong infinite deletion is usually converted into a finite certificate which
forces one block of a finite-block partition to lie in the union of any
chosen certified supports.  Reapplying strong deletion on a sufficiently far
tail of the same partition amplifies this: a single finite certificate can
force arbitrarily many distinct covered blocks.

The proof is a finite-injury induction.  At one stage, the union of *all*
supports available at the current finite target set can cover only finitely
many blocks.  Start the next stage beyond all of them.  The block forced at
the next stage is therefore new, uniformly for every support choice.
-/

namespace Erdos881

/-- The union of every support available at one of the finitely many targets
in `Q`. -/
def allFiniteSupportsUnion (R : SupportFamily) (Q : Finset ℕ) : Finset ℕ :=
  Q.biUnion fun q => (R q).biUnion id

/-- The union of a particular finite support choice is contained in the
union of all available supports at the same targets. -/
theorem finiteSupportChoiceUnion_subset_allFiniteSupportsUnion
    {R : SupportFamily} {Q : Finset ℕ}
    (c : FiniteSupportChoice R Q) :
    finiteSupportChoiceUnion c ⊆ allFiniteSupportsUnion R Q := by
  intro x hx
  obtain ⟨q, _hqattach, hxE⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  refine ⟨q.1, q.2, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨(c q).1, (c q).2, hxE⟩

/-- Restrict a finite support choice to a smaller finite target set. -/
def restrictFiniteSupportChoice
    {R : SupportFamily} {P Q : Finset ℕ}
    (hPQ : P ⊆ Q) (c : FiniteSupportChoice R Q) :
    FiniteSupportChoice R P := fun p =>
  ⟨(c ⟨p.1, hPQ p.2⟩).1, (c ⟨p.1, hPQ p.2⟩).2⟩

/-- Restriction can only shrink the union of the selected supports. -/
theorem finiteSupportChoiceUnion_restrict_subset
    {R : SupportFamily} {P Q : Finset ℕ}
    (hPQ : P ⊆ Q) (c : FiniteSupportChoice R Q) :
    finiteSupportChoiceUnion (restrictFiniteSupportChoice hPQ c) ⊆
      finiteSupportChoiceUnion c := by
  intro x hx
  obtain ⟨p, _hpattach, hxE⟩ := Finset.mem_biUnion.mp hx
  apply Finset.mem_biUnion.mpr
  let q : {n // n ∈ Q} := ⟨p.1, hPQ p.2⟩
  refine ⟨q, by simp [q], ?_⟩
  exact hxE

/-- Strong deletion amplifies the usual one-block dual certificate to an
arbitrarily large family of distinct covered blocks.  The returned indices
can all be forced beyond any prescribed starting block.

This is the certificate form useful for the bounded-representation route:
to contradict strong deletion it is enough to find a uniform upper bound on
the number of blocks covered by some support choice for every finite `Q`. -/
theorem exists_manyCoveredBlocks_of_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hstrong : StrongInfiniteDeletion R A) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      ∀ c : FiniteSupportChoice R Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c := by
  classical
  intro M
  induction M with
  | zero =>
      intro start N
      refine ⟨∅, by simp, ?_⟩
      intro c
      exact ⟨∅, by simp⟩
  | succ M ih =>
      intro start N
      let C : Set ℕ := {x | ∃ i, x ∈ F (start + i)}
      let G : ℕ → Finset ℕ := fun i => F (start + i)
      have hCA : C ⊆ A := by
        intro x hx
        obtain ⟨i, hxi⟩ := hx
        exact (P.mem_iff x).2 ⟨start + i, hxi⟩
      have PG : IsFiniteBlockPartition C G := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          exact P.nonempty (start + i)
        · intro i j hij
          apply P.disjoint
          omega
        · intro x
          simp only [C, G, Set.mem_setOf_eq]
      obtain ⟨Q₀, hQ₀N, hcert₀⟩ :=
        finiteBlockCertificates_on_subset_of_strongInfiniteDeletion
          hstrong hCA G PG N
      let U₀ : Finset ℕ := allFiniteSupportsUnion R Q₀
      have hcoveredFinite : Set.Finite {i | F i ⊆ U₀} :=
        P.finite_indices_blocks_subset U₀
      let J : Finset ℕ := hcoveredFinite.toFinset
      let next : ℕ := max start (J.sup id + 1)
      obtain ⟨Q₁, hQ₁N, hmany₁⟩ := ih next N
      let Q : Finset ℕ := Q₀ ∪ Q₁
      have hQ₀Q : Q₀ ⊆ Q := Finset.subset_union_left
      have hQ₁Q : Q₁ ⊆ Q := Finset.subset_union_right
      refine ⟨Q, ?_, ?_⟩
      · intro q hqQ
        rcases Finset.mem_union.mp hqQ with hqQ₀ | hqQ₁
        · exact hQ₀N q hqQ₀
        · exact hQ₁N q hqQ₁
      · intro c
        let c₀ : FiniteSupportChoice R Q₀ :=
          restrictFiniteSupportChoice hQ₀Q c
        let c₁ : FiniteSupportChoice R Q₁ :=
          restrictFiniteSupportChoice hQ₁Q c
        obtain ⟨j, hjcover⟩ :=
          exists_block_subset_supportChoiceUnion_of_certificate hcert₀ c₀
        let i₀ : ℕ := start + j
        have hi₀coverSmall : F i₀ ⊆ finiteSupportChoiceUnion c₀ := by
          exact hjcover
        have hi₀cover : F i₀ ⊆ finiteSupportChoiceUnion c :=
          hi₀coverSmall.trans
            (finiteSupportChoiceUnion_restrict_subset hQ₀Q c)
        have hi₀U₀ : F i₀ ⊆ U₀ :=
          hi₀coverSmall.trans
            (finiteSupportChoiceUnion_subset_allFiniteSupportsUnion c₀)
        have hi₀J : i₀ ∈ J := by
          exact hcoveredFinite.mem_toFinset.mpr hi₀U₀
        have hi₀leSup : i₀ ≤ J.sup id := by
          simpa using
            (Finset.le_sup (f := fun x : ℕ => x) hi₀J)
        have hi₀next : i₀ < next := by
          dsimp only [next]
          omega
        obtain ⟨I, hIcard, hIlower, hIcoverSmall⟩ := hmany₁ c₁
        have hIcover : ∀ i ∈ I,
            F i ⊆ finiteSupportChoiceUnion c := by
          intro i hiI
          exact (hIcoverSmall i hiI).trans
            (finiteSupportChoiceUnion_restrict_subset hQ₁Q c)
        have hi₀I : i₀ ∉ I := by
          intro hi₀I
          have hnexti₀ : next ≤ i₀ := hIlower i₀ hi₀I
          omega
        refine ⟨insert i₀ I, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hi₀I, hIcard]
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hiI
          · exact Nat.le_add_right start j
          · exact le_trans (le_max_left start (J.sup id + 1))
              (hIlower i hiI)
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hiI
          · exact hi₀cover
          · exact hIcover i hiI

/-- The amplified covered-block conclusion can be retained together with
the original selector-certificate property on the same finite target set.
Take the union of an amplified target set and one ordinary certificate;
restriction of support choices preserves all amplified covered blocks. -/
theorem exists_manyCoveredBlocks_and_certificate_of_strongInfiniteDeletion
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hstrong : StrongInfiniteDeletion R A) :
    ∀ M start N, ∃ Q : Finset ℕ,
      (∀ q ∈ Q, N ≤ q) ∧
      (∀ s : BlockSelector F, ∃ q ∈ Q,
        DestroysAt R (selectedSet s) q) ∧
      ∀ c : FiniteSupportChoice R Q,
        ∃ I : Finset ℕ,
          I.card = M ∧
          (∀ i ∈ I, start ≤ i) ∧
          ∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c := by
  classical
  intro M start N
  obtain ⟨Q₀, hQ₀N, hmany⟩ :=
    exists_manyCoveredBlocks_of_strongInfiniteDeletion
      P hstrong M start N
  obtain ⟨Q₁, hQ₁N, hcert⟩ :=
    finiteBlockCertificates_of_strongInfiniteDeletion
      hstrong F P N
  let Q : Finset ℕ := Q₀ ∪ Q₁
  have hQ₀Q : Q₀ ⊆ Q := Finset.subset_union_left
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_union.mp hq with hq₀ | hq₁
    · exact hQ₀N q hq₀
    · exact hQ₁N q hq₁
  · intro s
    obtain ⟨q, hqQ₁, hqdestroy⟩ := hcert s
    exact ⟨q, Finset.mem_union_right Q₀ hqQ₁, hqdestroy⟩
  · intro c
    let c₀ : FiniteSupportChoice R Q₀ :=
      restrictFiniteSupportChoice hQ₀Q c
    obtain ⟨I, hIcard, hIstart, hIcover₀⟩ := hmany c₀
    exact ⟨I, hIcard, hIstart, fun i hi =>
      (hIcover₀ i hi).trans
        (finiteSupportChoiceUnion_restrict_subset hQ₀Q c)⟩

/-- A uniform covered-block bound is the exact opposite polarity to the
amplified certificate.  For every finite late target set, it asks for one
support choice whose union cannot cover more than `M` blocks. -/
def HasUniformCoveredBlockSupportChoices
    (R : SupportFamily) (F : ℕ → Finset ℕ) : Prop :=
  ∃ M N, ∀ Q : Finset ℕ, (∀ q ∈ Q, N ≤ q) →
    ∃ c : FiniteSupportChoice R Q,
      ∀ I : Finset ℕ,
        (∀ i ∈ I, F i ⊆ finiteSupportChoiceUnion c) →
        I.card ≤ M

/-- A uniform upper bound on covered blocks contradicts strong infinite
deletion.  This packages the remaining arithmetic target independently of
the compactness/certificate argument. -/
theorem not_strongInfiniteDeletion_of_uniformCoveredBlockSupportChoices
    {A : Set ℕ} {R : SupportFamily} {F : ℕ → Finset ℕ}
    (P : IsFiniteBlockPartition A F)
    (hbound : HasUniformCoveredBlockSupportChoices R F) :
    ¬ StrongInfiniteDeletion R A := by
  rintro hstrong
  obtain ⟨M, N, hM⟩ := hbound
  obtain ⟨Q, hQN, hmany⟩ :=
    exists_manyCoveredBlocks_of_strongInfiniteDeletion
      P hstrong (M + 1) 0 N
  obtain ⟨c, hc⟩ := hM Q hQN
  obtain ⟨I, hIcard, _hIlower, hIcover⟩ := hmany c
  have hle : I.card ≤ M := hc I hIcover
  omega

end Erdos881
