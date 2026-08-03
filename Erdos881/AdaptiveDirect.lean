import Erdos881.ConeCollision
import Erdos881.GeneralOrderAttack

namespace Erdos881

open Classical

/-- Arbitrarily large clean extensions of one fixed finite prefix. -/
def HasLocalCleanSupply
    (A : Set ℕ) (h : ℕ) (F : Finset ℕ) : Prop :=
  ∀ M, ∃ b, b ∈ A ∧ b ∉ F ∧ M ≤ b ∧
    CleanlyRedundantAbove A h F b

/-- Beyond one bound, every surviving candidate owns a pinned target above
itself relative to the current prefix. -/
def HasAtomicPinnedTail
    (A : Set ℕ) (h : ℕ) (F : Finset ℕ) : Prop :=
  ∃ M, ∀ b, b ∈ A → b ∉ F → M ≤ b →
    ∃ n, b ≤ n ∧ PinnedAt A h F b n

/-- A clean extension is exactly another safe finite prefix. -/
theorem CleanlyRedundantAbove.exactBasis_diff_insert
    {A : Set ℕ} {h b : ℕ} {F : Finset ℕ}
    (hclean : CleanlyRedundantAbove A h F b) :
    IsExactTupleAsymptoticBasis
      (A \ ((insert b F : Finset ℕ) : Set ℕ)) h := by
  refine ⟨b, ?_⟩
  intro n hbn
  obtain ⟨v, hv, hsum⟩ := hclean n hbn
  refine ⟨v, fun i => ⟨(hv i).1, ?_⟩, hsum⟩
  intro hi
  rw [Finset.mem_coe, Finset.mem_insert] at hi
  rcases hi with hib | hiF
  · exact (hv i).2.2 hib
  · exact (hv i).2.1 hiF

theorem not_hasLocalCleanSupply_iff_atomicPinnedTail
    {A : Set ℕ} {h : ℕ} {F : Finset ℕ}
    (hsafe : IsExactTupleAsymptoticBasis
      (A \ (F : Set ℕ)) h) :
    ¬ HasLocalCleanSupply A h F ↔
      HasAtomicPinnedTail A h F := by
  classical
  constructor
  · intro hnot
    unfold HasLocalCleanSupply at hnot
    push Not at hnot
    obtain ⟨M₀, hM₀⟩ := hnot
    obtain ⟨T, hT⟩ := hsafe
    refine ⟨max M₀ T, ?_⟩
    intro b hbA hbF hbM
    have hnotclean : ¬ CleanlyRedundantAbove A h F b :=
      hM₀ b hbA hbF (le_trans (le_max_left _ _) hbM)
    unfold CleanlyRedundantAbove at hnotclean
    push Not at hnotclean
    obtain ⟨n, hbn, hstr⟩ := hnotclean
    have hstrInsert : StrandedAt A h (insert b F) n := by
      rintro ⟨v, hv, hsum⟩
      exact hstr v (fun i => by
        have hi := (hv i).2
        rw [Finset.mem_insert] at hi
        push Not at hi
        exact ⟨(hv i).1, hi.2, hi.1⟩) hsum
    have hnotStrandedF : ¬ StrandedAt A h F n := by
      intro hstrF
      obtain ⟨v, hv, hsum⟩ := hT n
        (le_trans (le_max_right _ _) (le_trans hbM hbn))
      exact hstrF ⟨v, fun i =>
        ⟨(hv i).1, fun hiF => (hv i).2
          (Finset.mem_coe.mpr hiF)⟩, hsum⟩
    rcases stranded_insert_split hstrInsert with hstrF | hpin
    · exact (hnotStrandedF hstrF).elim
    · exact ⟨n, hbn, hpin⟩
  · rintro ⟨M, htail⟩ hsupply
    obtain ⟨b, hbA, hbF, hbM, hclean⟩ := hsupply M
    obtain ⟨n, hbn, hpin⟩ := htail b hbA hbF hbM
    obtain ⟨v, hv, hsum⟩ := hclean n hbn
    obtain ⟨i, hi⟩ := hpin.2 v
      (fun i => ⟨(hv i).1, (hv i).2.1⟩) hsum
    exact (hv i).2.2 hi

/-- Dichotomy form used by the recursive construction. -/
theorem safePrefix_cleanSupply_or_atomicPinnedTail
    {A : Set ℕ} {h : ℕ} {F : Finset ℕ}
    (hsafe : IsExactTupleAsymptoticBasis
      (A \ (F : Set ℕ)) h) :
    HasLocalCleanSupply A h F ∨
      HasAtomicPinnedTail A h F := by
  classical
  by_cases hsupply : HasLocalCleanSupply A h F
  · exact Or.inl hsupply
  · exact Or.inr
      ((not_hasLocalCleanSupply_iff_atomicPinnedTail hsafe).mp hsupply)

/-- Safety excludes the old fixed pin case when the pin lies in the deleted
prefix and its background obstruction is contained in that prefix.  It does
not exclude fixed pins outside `F`. -/
theorem safePrefix_excludes_fixedPinCase
    {A : Set ℕ} {h : ℕ} {F : Finset ℕ}
    (hsafe : IsExactTupleAsymptoticBasis
      (A \ (F : Set ℕ)) h) :
    ¬ ∃ f, f ∈ F ∧ ∃ G : Finset ℕ,
      G ⊆ F ∧ f ∉ G ∧
      ∀ M, ∃ n, M ≤ n ∧ PinnedAt A h G f n := by
  rintro ⟨f, hfF, G, hGF, _hfG, hpins⟩
  obtain ⟨T, hT⟩ := hsafe
  obtain ⟨n, hn, hpin⟩ := hpins T
  obtain ⟨v, hv, hsum⟩ := hT n hn
  obtain ⟨i, hi⟩ := hpin.2 v (fun i =>
    ⟨(hv i).1, fun hiG => (hv i).2
      (Finset.mem_coe.mpr (hGF hiG))⟩) hsum
  exact (hv i).2 (Finset.mem_coe.mpr (hi ▸ hfF))

/-! ## Marker-preserving cone descent -/

/-- A finite support transversal is a destroyer for the additive support hypergraph at its
covered target. -/
theorem HasSupportTransversalAt.destroys_additiveSupportFamily
    {A : Set ℕ} {h : ℕ} {H : Finset ℕ} {q : ℕ}
    (hhub : HasSupportTransversalAt A h H q) :
    DestroysAt (additiveSupportFamily A h) (H : Set ℕ) q := by
  rw [destroysAt_additiveSupportFamily_iff]
  rintro ⟨v, hv, hvsum⟩
  obtain ⟨i, hi⟩ := hhub.2 v (fun i => (hv i).1) hvsum
  exact (hv i).2 (by simpa using hi)

/-- If one represented support meets the support transversal exactly at `b`, minimizing the
support transversal destroyer cannot discard `b`. -/
theorem HasSupportTransversalAt.exists_minimalDestroyer_containing
    {A : Set ℕ} {h q b : ℕ} {H E : Finset ℕ}
    (hhub : HasSupportTransversalAt A h H q)
    (hER : E ∈ additiveSupportFamily A h q)
    (hprivate : E ∩ H = {b}) :
    ∃ D : Finset ℕ,
      D ⊆ H ∧ b ∈ D ∧
      IsInclusionMinimalDestroyer
        (additiveSupportFamily A h) D q := by
  obtain ⟨D, hDH, hDminimal⟩ :=
    exists_inclusionMinimalDestroyer_subset
      hhub.destroys_additiveSupportFamily
  have hbD : b ∈ D := by
    obtain ⟨y, hyE, hyD⟩ :=
      Set.not_disjoint_iff.mp (hDminimal.1 E hER)
    have hyH : y ∈ H := hDH (Finset.mem_coe.mp hyD)
    have hySingleton : y ∈ ({b} : Finset ℕ) := by
      rw [← hprivate]
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_coe.mp hyE, hyH⟩
    have hyb : y = b := by simpa using hySingleton
    exact hyb ▸ Finset.mem_coe.mp hyD
  exact ⟨D, hDH, hbD, hDminimal⟩

/-- A pinned successor target is either the pure diagonal `(k+1) * b`, or
removing a nondiagonal summand leaves a base-order support whose unique hit
on the cone support transversal is the moving marked element `b`. -/
theorem PinnedAt.diagonal_or_privatePredecessorSupport
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ} {b n : ℕ}
    (hpin : PinnedAt A (k + 1) F b n) :
    n = (k + 1) * b ∨
      ∃ x E,
        x ∈ A ∧ x ∉ insert b F ∧
        x ≤ n ∧
        E ∈ additiveSupportFamily A k (n - x) ∧
        E ∩ insert b F = {b} := by
  classical
  obtain ⟨v, hv, hvsum⟩ := hpin.1
  have hsurvive :
      ∃ E ∈ additiveSupportFamily A (k + 1) n,
        Disjoint (E : Set ℕ) (F : Set ℕ) := by
    apply exists_surviving_additiveSupport_iff.mpr
    exact ⟨v, fun i =>
      ⟨(hv i).1, fun hiF =>
        (hv i).2 (Finset.mem_coe.mp hiF)⟩, hvsum⟩
  obtain ⟨R, hRR, hRF⟩ := hsurvive
  obtain ⟨w, hwA, hwsum, hRw⟩ :=
    mem_additiveSupportFamily_iff.mp hRR
  have hwF : ∀ i, (w i).1 ∉ F := by
    intro i hiF
    exact Set.disjoint_left.mp hRF
      (Finset.mem_coe.mpr (hRw.symm ▸
        mem_tupleSupport_iff.mpr ⟨i, rfl⟩))
      (Finset.mem_coe.mpr hiF)
  obtain ⟨j, hjb⟩ :=
    hpin.2 (fun i => (w i).1)
      (fun i => ⟨hwA i, hwF i⟩) hwsum
  have hbR : b ∈ R := by
    rw [← hRw]
    exact mem_tupleSupport_iff.mpr ⟨j, hjb⟩
  by_cases hRsingleton : R = {b}
  · left
    calc
      n = ∑ i, (w i).1 := hwsum.symm
      _ = ∑ _i : Fin (k + 1), b := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hwiR : (w i).1 ∈ R := by
          rw [← hRw]
          exact mem_tupleSupport_iff.mpr ⟨i, rfl⟩
        rw [hRsingleton] at hwiR
        simpa using hwiR
      _ = (k + 1) * b := by simp
  · right
    have hxexists : ∃ x ∈ R, x ≠ b := by
      by_contra hnone
      push Not at hnone
      apply hRsingleton
      apply Finset.Subset.antisymm
      · intro y hyR
        have hyb : y = b := hnone y hyR
        simp [hyb]
      · intro y hy
        have hyb : y = b := by simpa using hy
        simpa [hyb] using hbR
    obtain ⟨x, hxR, hxb⟩ := hxexists
    have hxA : x ∈ A :=
      additiveSupportFamily_supportsIn
        A (k + 1) n R hRR x hxR
    have hxle : x ≤ n :=
      additiveSupportFamily_supportsBounded
        A (k + 1) n R hRR x hxR
    have hxF : x ∉ F := by
      intro hxFin
      exact Set.disjoint_left.mp hRF
        (Finset.mem_coe.mpr hxR)
        (Finset.mem_coe.mpr hxFin)
    have hxSupportTransversal : x ∉ insert b F := by
      rw [Finset.mem_insert]
      push Not
      exact ⟨hxb, hxF⟩
    obtain ⟨E, hER, hReq⟩ :=
      additiveSupport_remove_hit_succ hRR hxR
    have hbE : b ∈ E := by
      rw [hReq] at hbR
      rcases Finset.mem_insert.mp hbR with hbx | hbE
      · exact (hxb hbx.symm).elim
      · exact hbE
    have hEF : Disjoint (E : Set ℕ) (F : Set ℕ) := by
      rw [Set.disjoint_left]
      intro y hyE hyF
      exact Set.disjoint_left.mp hRF
        (Finset.mem_coe.mpr (by
          rw [hReq]
          exact Finset.mem_insert_of_mem
            (Finset.mem_coe.mp hyE))) hyF
    have hprivate : E ∩ insert b F = {b} := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyE, hySupportTransversal⟩ := Finset.mem_inter.mp hy
        rcases Finset.mem_insert.mp hySupportTransversal with hyb | hyF
        · simp [hyb]
        · exact (Set.disjoint_left.mp hEF
            (Finset.mem_coe.mpr hyE)
            (Finset.mem_coe.mpr hyF)).elim
      · intro hy
        have hyb : y = b := by simpa using hy
        subst y
        exact Finset.mem_inter.mpr
          ⟨hbE, Finset.mem_insert_self b F⟩
    exact ⟨x, E, hxA, hxSupportTransversal, hxle, hER, hprivate⟩

theorem pinned_target_diagonal_or_markedMinimalDestroyer_rankFork
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    {b n N₀ : ℕ}
    (hk : 1 < k)
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) F b n)
    (hbLarge : N₀ ≤ b) :
    n = (k + 1) * b ∨
      ∃ x D,
        x ∈ A ∧ x ∉ insert b F ∧
        D.Nonempty ∧ D ⊆ insert b F ∧ b ∈ D ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A k) D (n - x) ∧
        ((∃ ℓ q,
            1 < ℓ ∧ ℓ < k ∧
            (additiveSupportFamily A ℓ q).Nonempty ∧
            DestroysAt
              (additiveSupportFamily A ℓ)
              (D : Set ℕ) q) ∨
          ∃ diagonal : Finset ℕ,
            diagonal ⊆ D ∧
            diagonal.card ≤ 1 ∧
            ∀ d ∈ D, d ∉ diagonal →
              ∃ core : Finset ℕ,
                core ∈ additiveSupportFamily A (k - 1)
                  ((n - x) - d) ∧
                Disjoint (core : Set ℕ) (D : Set ℕ) ∧
                insert d core ∈
                  additiveSupportFamily A k (n - x) ∧
                insert d core ∩ D = {d}) := by
  obtain hdiag | ⟨x, E, hxA, hxSupportTransversal, hxle, hER, hprivate⟩ :=
    hpin.diagonal_or_privatePredecessorSupport
  · exact Or.inl hdiag
  · right
    have hbE : b ∈ E := by
      have : b ∈ E ∩ insert b F := by
        rw [hprivate]
        simp
      exact (Finset.mem_inter.mp this).1
    have hbTarget : b ≤ n - x :=
      additiveSupportFamily_supportsBounded
        A k (n - x) E hER b hbE
    have hxn : x + N₀ ≤ n := by omega
    have hhub : HasSupportTransversalAt A k (insert b F) (n - x) :=
      pinned_cone_has_support_transversal hcov hpin hxA hxSupportTransversal hxn
    obtain ⟨D, hDSupportTransversal, hbD, hDminimal⟩ :=
      hhub.exists_minimalDestroyer_containing hER hprivate
    have hDnonempty : D.Nonempty := ⟨b, hbD⟩
    have hfork :=
      minimalAdditiveDestroyer_nontrivialRankDescent_or_privateCores_off_oneDiagonal
        hk hDminimal
    exact ⟨x, D, hxA, hxSupportTransversal, hDnonempty,
      hDSupportTransversal, hbD, hDminimal, hfork⟩

/-! ## Prefix-cleared, target-controlled marked cones -/

/-- A lower-rank descent which was already caused by the old prefix.  The
second destruction conjunct records that this is the actual descent returned
for the marked destroyer, rather than an unrelated old-prefix obstruction. -/
def HasOldPrefixNontrivialRankDescent
    (A : Set ℕ) (k : ℕ) (F D : Finset ℕ) : Prop :=
  ∃ ℓ t,
    1 < ℓ ∧ ℓ < k ∧
    (additiveSupportFamily A ℓ t).Nonempty ∧
    DestroysAt
      (additiveSupportFamily A ℓ) (F : Set ℕ) t ∧
    DestroysAt
      (additiveSupportFamily A ℓ) (D : Set ℕ) t

/-- A genuinely new lower-rank descent: the marked destroyer contradicts the
target, the old prefix does not, and the target lies above the requested
bound. -/
def HasPrefixClearedCofinalNontrivialRankDescent
    (A : Set ℕ) (k : ℕ) (F D : Finset ℕ) (L : ℕ) : Prop :=
  ∃ ℓ t,
    1 < ℓ ∧ ℓ < k ∧ L ≤ t ∧
    (additiveSupportFamily A ℓ t).Nonempty ∧
    ¬ DestroysAt
      (additiveSupportFamily A ℓ) (F : Set ℕ) t ∧
    DestroysAt
      (additiveSupportFamily A ℓ) (D : Set ℕ) t

/-- The structured right case of the nontrivial-rank fork. -/
def HasPrivateCoresOffOneDiagonal
    (A : Set ℕ) (k q : ℕ) (D : Finset ℕ) : Prop :=
  ∃ diagonal : Finset ℕ,
    diagonal ⊆ D ∧
    diagonal.card ≤ 1 ∧
    ∀ d ∈ D, d ∉ diagonal →
      ∃ core : Finset ℕ,
        core ∈ additiveSupportFamily A (k - 1) (q - d) ∧
        Disjoint (core : Set ℕ) (D : Set ℕ) ∧
        insert d core ∈ additiveSupportFamily A k q ∧
        insert d core ∩ D = {d}

/-- The pointwise fork at the unique fresh marker.  Multiple occurrences of
`b` give a genuinely prefix-cleared cofinal rank descent; one occurrence
leaves a private predecessor core; all occurrences give the diagonal. -/
def HasMarkedPointCofinalRankFork
    (A : Set ℕ) (k : ℕ) (F D : Finset ℕ)
    (b q L : ℕ) : Prop :=
  q = k * b ∨
    HasPrefixClearedCofinalNontrivialRankDescent A k F D L ∨
    ∃ core : Finset ℕ,
      core ∈ additiveSupportFamily A (k - 1) (q - b) ∧
      Disjoint (core : Set ℕ) (D : Set ℕ) ∧
      insert b core ∈ additiveSupportFamily A k q ∧
      insert b core ∩ D = {b}

/-- The old prefix already destroys one predecessor cone of the pinned
target. -/
def HasOldPrefixCone
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ) (b n : ℕ) : Prop :=
  ∃ x,
    x ∈ A ∧ x ∉ insert b F ∧
    DestroysAt
      (additiveSupportFamily A k) (F : Set ℕ) (n - x)

/-- A predecessor cone with exactly one point of its minimal destroyer
outside the old prefix, together with the prefix-split rank fork. -/
def HasCofinalMarkedConeRankFork
    (A : Set ℕ) (k : ℕ) (F : Finset ℕ)
    (b n L : ℕ) : Prop :=
  ∃ x D,
    x ∈ A ∧ x ∉ insert b F ∧
    x ≤ n ∧
    L ≤ n - x ∧
    D.Nonempty ∧ D ⊆ insert b F ∧
    b ∈ D ∧ D \ F = {b} ∧
    IsInclusionMinimalDestroyer
      (additiveSupportFamily A k) D (n - x) ∧
    HasMarkedPointCofinalRankFork A k F D b (n - x) L

/-- A pin belongs to the represented set and cannot belong to the prefix
avoided by its surviving representation. -/
theorem PinnedAt.pin_mem_and_not_mem_prefix
    {A : Set ℕ} {h : ℕ} {F : Finset ℕ} {b n : ℕ}
    (hpin : PinnedAt A h F b n) :
    b ∈ A ∧ b ∉ F := by
  obtain ⟨v, hv, hsum⟩ := hpin.1
  obtain ⟨i, hi⟩ := hpin.2 v hv hsum
  exact ⟨hi ▸ (hv i).1, fun hbF =>
    (hv i).2 (hi ▸ hbF)⟩

theorem markedMinimalDestroyer_prefixSplit_rankFork
    {A : Set ℕ} {k q : ℕ} {F D : Finset ℕ}
    {b L : ℕ}
    (hk : 1 < k)
    (hLb : L ≤ b)
    (hDdiff : D \ F = {b})
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A k) D q) :
    HasOldPrefixNontrivialRankDescent A k F D ∨
      HasPrefixClearedCofinalNontrivialRankDescent A k F D L ∨
      HasPrivateCoresOffOneDiagonal A k q D := by
  classical
  obtain hdescent | hprivate :=
    minimalAdditiveDestroyer_nontrivialRankDescent_or_privateCores_off_oneDiagonal
      hk hminimal
  · obtain ⟨ℓ, t, hℓtwo, hℓk, hrepresented, hDdestroy⟩ :=
      hdescent
    by_cases hFdestroy : DestroysAt
        (additiveSupportFamily A ℓ) (F : Set ℕ) t
    · exact Or.inl
        ⟨ℓ, t, hℓtwo, hℓk, hrepresented,
          hFdestroy, hDdestroy⟩
    · right
      left
      obtain ⟨E, hER, hEF⟩ :=
        not_destroysAt_iff.mp hFdestroy
      obtain ⟨y, hyE, hyD⟩ :=
        Set.not_disjoint_iff.mp (hDdestroy E hER)
      have hyF : y ∉ F := by
        intro hyF
        exact Set.disjoint_left.mp hEF hyE
          (Finset.mem_coe.mpr hyF)
      have hyDiff : y ∈ D \ F :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_coe.mp hyD, hyF⟩
      rw [hDdiff] at hyDiff
      have hyb : y = b := Finset.mem_singleton.mp hyDiff
      have hbE : b ∈ E := by
        exact Finset.mem_coe.mp (hyb ▸ hyE)
      have hbt : b ≤ t :=
        additiveSupportFamily_supportsBounded
          A ℓ t E hER b hbE
      exact ⟨ℓ, t, hℓtwo, hℓk,
        hLb.trans hbt, hrepresented, hFdestroy, hDdestroy⟩
  · exact Or.inr (Or.inr hprivate)

theorem markedMinimalDestroyer_cofinalRankDescent_or_privateCore
    {A : Set ℕ} {k q : ℕ} {F D : Finset ℕ}
    {b L : ℕ}
    (hk : 1 < k)
    (hLb : L ≤ b)
    (hbF : b ∉ F)
    (hbD : b ∈ D)
    (hminimal : IsInclusionMinimalDestroyer
      (additiveSupportFamily A k) D q) :
    HasMarkedPointCofinalRankFork A k F D b q L := by
  classical
  obtain ⟨E, hEmem, hEprivate⟩ :=
    hminimal.exists_uniqueHitSupport hbD
  have hbE : b ∈ E := by
    have hbInter : b ∈ E ∩ D := by
      rw [hEprivate]
      simp
    exact (Finset.mem_inter.mp hbInter).1
  have hEDestroyed :
      ¬ Disjoint (E : Set ℕ) (D : Set ℕ) := by
    exact Set.not_disjoint_iff.mpr
      ⟨b, Finset.mem_coe.mpr hbE,
        Finset.mem_coe.mpr hbD⟩
  obtain ⟨hits, j, t, core, hhitsNonempty,
      hlength, _hjk, hhits, hcoreMem, hcoreD,
      htarget, hEeq⟩ :=
    destroyed_additiveSupport_has_strictSurvivingCoreDecomposition
      hEmem hEDestroyed
  have hhitsPos : 0 < hits.length :=
    List.length_pos_iff.mpr hhitsNonempty
  have hhitEq : ∀ y ∈ hits, y = b := by
    intro y hyHits
    have hyE : y ∈ E := by
      rw [hEeq, foldr_insert_eq_toFinset_union]
      exact Finset.mem_union_left core
        (List.mem_toFinset.mpr hyHits)
    have hyD : y ∈ D :=
      Finset.mem_coe.mp (hhits y hyHits).2
    have hyPrivate : y ∈ ({b} : Finset ℕ) := by
      rw [← hEprivate]
      exact Finset.mem_inter.mpr ⟨hyE, hyD⟩
    simpa using hyPrivate
  have hhitsRep :
      hits = List.replicate hits.length b :=
    List.eq_replicate_iff.mpr ⟨rfl, hhitEq⟩
  have hhitsSum : hits.sum = hits.length * b := by
    rw [hhitsRep, List.sum_replicate]
    simp
  by_cases hhitsFull : hits.length = k
  · left
    have hjzero : j = 0 := by omega
    have htzero : t = 0 := by
      rw [hjzero] at hcoreMem
      exact
        (additiveSupportFamily_zero_target_and_support
          hcoreMem).1
    calc
      q = hits.sum + t := htarget
      _ = hits.length * b := by
        rw [htzero, Nat.add_zero, hhitsSum]
      _ = k * b := by rw [hhitsFull]
  · have hhitsStrict : hits.length < k := by omega
    by_cases hhitsOne : hits.length = 1
    · right
      right
      have hj : j = k - 1 := by omega
      have hhitsList : hits = [b] := by
        rw [hhitsRep, hhitsOne]
        simp
      have hcoreMem' :
          core ∈ additiveSupportFamily A (k - 1) t := by
        simpa only [hj] using hcoreMem
      have htarget' : q = b + t := by
        rw [htarget, hhitsList]
        simp
      have hEeq' : E = insert b core := by
        simpa only [hhitsList] using hEeq
      have hdiff : q - b = t := by omega
      exact ⟨core, hdiff ▸ hcoreMem', hcoreD,
        hEeq' ▸ hEmem, hEeq' ▸ hEprivate⟩
    · right
      left
      have hhitsTwo : 1 < hits.length := by omega
      let H : Finset ℕ :=
        hits.foldr (fun y G => insert y G) ∅
      have hHmem :
          H ∈ additiveSupportFamily A hits.length hits.sum := by
        exact list_foldr_mem_additiveSupportFamily
          (fun y hy => (hhits y hy).1)
      have hHnonempty :
          (additiveSupportFamily A hits.length hits.sum).Nonempty :=
        ⟨H, hHmem⟩
      have hHdestroy :
          DestroysAt
            (additiveSupportFamily A hits.length)
            (D : Set ℕ) hits.sum :=
        complementarySurvivingCore_forces_hitTargetDestroyer
          hminimal hlength htarget hcoreMem hcoreD
      have hHF : Disjoint (H : Set ℕ) (F : Set ℕ) := by
        rw [Set.disjoint_left]
        intro y hyH hyF
        have hyHfin : y ∈ H := Finset.mem_coe.mp hyH
        have hyHitsFin : y ∈ hits.toFinset := by
          dsimp only [H] at hyHfin
          rw [foldr_insert_eq_toFinset_union] at hyHfin
          simpa using hyHfin
        have hyb : y = b :=
          hhitEq y (List.mem_toFinset.mp hyHitsFin)
        exact hbF (hyb ▸ Finset.mem_coe.mp hyF)
      have hFsurvive :
          ¬ DestroysAt
            (additiveSupportFamily A hits.length)
            (F : Set ℕ) hits.sum :=
        not_destroysAt_iff.mpr ⟨H, hHmem, hHF⟩
      have hbTarget : b ≤ hits.sum := by
        rw [hhitsSum]
        exact Nat.le_mul_of_pos_left b hhitsPos
      exact ⟨hits.length, hits.sum,
        hhitsTwo, hhitsStrict, hLb.trans hbTarget,
        hHnonempty, hFsurvive, hHdestroy⟩

theorem HasSupportTransversalAt.oldPrefix_or_cofinalMarkedMinimalDestroyerRankFork
    {A : Set ℕ} {k q : ℕ} {F : Finset ℕ}
    {b L : ℕ}
    (hk : 1 < k)
    (hhub : HasSupportTransversalAt A k (insert b F) q)
    (hbF : b ∉ F)
    (hLb : L ≤ b) :
    DestroysAt
        (additiveSupportFamily A k) (F : Set ℕ) q ∨
      ∃ D : Finset ℕ,
        L ≤ q ∧
        D.Nonempty ∧ D ⊆ insert b F ∧
        b ∈ D ∧ D \ F = {b} ∧
        IsInclusionMinimalDestroyer
          (additiveSupportFamily A k) D q ∧
        HasMarkedPointCofinalRankFork A k F D b q L := by
  classical
  by_cases hFold : DestroysAt
      (additiveSupportFamily A k) (F : Set ℕ) q
  · exact Or.inl hFold
  · right
    obtain ⟨D, hDSupportTransversal, hDminimal⟩ :=
      exists_inclusionMinimalDestroyer_subset
        hhub.destroys_additiveSupportFamily
    have hbD : b ∈ D := by
      by_contra hbD
      apply hFold
      intro S hSR
      obtain ⟨y, hyS, hyD⟩ :=
        Set.not_disjoint_iff.mp (hDminimal.1 S hSR)
      have hySupportTransversal := hDSupportTransversal (Finset.mem_coe.mp hyD)
      rcases Finset.mem_insert.mp hySupportTransversal with hyb | hyF
      · exact (hbD (hyb ▸ Finset.mem_coe.mp hyD)).elim
      · exact Set.not_disjoint_iff.mpr
          ⟨y, hyS, Finset.mem_coe.mpr hyF⟩
    have hDdiff : D \ F = {b} := by
      ext y
      constructor
      · intro hyDiff
        obtain ⟨hyD, hyF⟩ := Finset.mem_sdiff.mp hyDiff
        rcases Finset.mem_insert.mp (hDSupportTransversal hyD) with hyb | hyF'
        · simp [hyb]
        · exact (hyF hyF').elim
      · intro hyb
        have hyb' : y = b := by simpa using hyb
        subst y
        exact Finset.mem_sdiff.mpr ⟨hbD, hbF⟩
    obtain ⟨E, hER, hEF⟩ :=
      not_destroysAt_iff.mp hFold
    obtain ⟨y, hyE, hyD⟩ :=
      Set.not_disjoint_iff.mp (hDminimal.1 E hER)
    have hyF : y ∉ F := by
      intro hyF
      exact Set.disjoint_left.mp hEF hyE
        (Finset.mem_coe.mpr hyF)
    have hyDiff : y ∈ D \ F :=
      Finset.mem_sdiff.mpr
        ⟨Finset.mem_coe.mp hyD, hyF⟩
    rw [hDdiff] at hyDiff
    have hyb : y = b := Finset.mem_singleton.mp hyDiff
    have hbE : b ∈ E :=
      Finset.mem_coe.mp (hyb ▸ hyE)
    have hbq : b ≤ q :=
      additiveSupportFamily_supportsBounded
        A k q E hER b hbE
    have hrank :=
      markedMinimalDestroyer_cofinalRankDescent_or_privateCore
        hk hLb hbF hbD hDminimal
    exact ⟨D, hLb.trans hbq, ⟨b, hbD⟩,
      hDSupportTransversal, hbD, hDdiff, hDminimal, hrank⟩

theorem pinned_target_diagonal_or_oldPrefixCone_or_cofinalMarkedConeRankFork
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    {b n N₀ L : ℕ}
    (hk : 1 < k)
    (hcov : ∀ m, N₀ ≤ m → ∃ w : Fin k → ℕ,
      (∀ i, w i ∈ A) ∧ ∑ i, w i = m)
    (hpin : PinnedAt A (k + 1) F b n)
    (hbLarge : N₀ ≤ b)
    (hLb : L ≤ b) :
    n = (k + 1) * b ∨
      HasOldPrefixCone A k F b n ∨
      HasCofinalMarkedConeRankFork A k F b n L := by
  classical
  obtain hdiag | ⟨x, E, hxA, hxSupportTransversal, hxle, hER, hprivate⟩ :=
    hpin.diagonal_or_privatePredecessorSupport
  · exact Or.inl hdiag
  · right
    have hbE : b ∈ E := by
      have hbInter : b ∈ E ∩ insert b F := by
        rw [hprivate]
        simp
      exact (Finset.mem_inter.mp hbInter).1
    have hbTarget : b ≤ n - x :=
      additiveSupportFamily_supportsBounded
        A k (n - x) E hER b hbE
    have hxn : x + N₀ ≤ n := by omega
    have hhub : HasSupportTransversalAt A k (insert b F) (n - x) :=
      pinned_cone_has_support_transversal hcov hpin hxA hxSupportTransversal hxn
    have hbF : b ∉ F := hpin.pin_mem_and_not_mem_prefix.2
    obtain hFold | ⟨D, hLtarget, hDnonempty,
        hDSupportTransversal, hbD, hDdiff, hDminimal, hrank⟩ :=
      hhub.oldPrefix_or_cofinalMarkedMinimalDestroyerRankFork
        hk hbF hLb
    · exact Or.inl ⟨x, hxA, hxSupportTransversal, hFold⟩
    · exact Or.inr ⟨x, D, hxA, hxSupportTransversal, hxle, hLtarget,
        hDnonempty, hDSupportTransversal, hbD, hDdiff, hDminimal, hrank⟩

theorem HasAtomicPinnedTail.cofinal_markedConeRankFork
    {A : Set ℕ} {k : ℕ} {F : Finset ℕ}
    (hk : 1 < k)
    (hbasis : IsExactTupleAsymptoticBasis A k)
    (htail : HasAtomicPinnedTail A (k + 1) F) :
    ∀ L, ∃ b n,
      b ∈ A ∧ b ∉ F ∧ L ≤ b ∧ b ≤ n ∧
      PinnedAt A (k + 1) F b n ∧
      (n = (k + 1) * b ∨
        HasOldPrefixCone A k F b n ∨
        HasCofinalMarkedConeRankFork A k F b n L) := by
  classical
  obtain ⟨M, hM⟩ := htail
  have hunbounded := hbasis.unboundedOutside F
  obtain ⟨N₀, hcov⟩ := hbasis
  intro L
  obtain ⟨b, hbA, hbF, hbLarge⟩ :=
    hunbounded (max M (max N₀ L))
  have hbM : M ≤ b := (le_max_left _ _).trans hbLarge
  have hbN₀ : N₀ ≤ b :=
    (le_max_left N₀ L).trans
      ((le_max_right M (max N₀ L)).trans hbLarge)
  have hbL : L ≤ b :=
    (le_max_right N₀ L).trans
      ((le_max_right M (max N₀ L)).trans hbLarge)
  obtain ⟨n, hbn, hpin⟩ := hM b hbA hbF hbM
  have hout :=
    pinned_target_diagonal_or_oldPrefixCone_or_cofinalMarkedConeRankFork
      hk hcov hpin hbN₀ hbL
  exact ⟨b, n, hbA, hbF, hbL, hbn, hpin, hout⟩

end Erdos881
