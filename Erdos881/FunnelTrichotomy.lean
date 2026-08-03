import Erdos881.PinnedMirror
import Erdos881.GuardianBridge

namespace Erdos881

/-- `B` destroys `m` at order three over `A`, in elementary form: a
representation exists, and every representation meets `B`.  This
generalizes `IsPrivateTriple` (`B = {a}`) and `IsPairDestroyer`
(`B = {u, v}`) to arbitrary deletion sets. -/
def DestroyedBySet (A B : Set ℕ) (m : ℕ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m) ∧
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x ∈ B ∨ y ∈ B ∨ z ∈ B

/-- The order-two shadow: fixing any representation part outside `B`,
the remaining pair must meet `B`.  With `x = 0` this says every
two-term representation of a destroyed target meets `B`; with general
`x ∈ A \ B` it covers the whole translated family `m - x`. -/
theorem DestroyedBySet.shadow {A B : Set ℕ} {m x y z : ℕ}
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) (hy : y ∈ A) (hz : z ∈ A)
    (hsum : x + y + z = m) :
    y ∈ B ∨ z ∈ B := by
  rcases hdes.2 x hx y hy z hz hsum with h | h | h
  · exact absurd h hxB
  · exact Or.inl h
  · exact Or.inr h

/-- Elementary destruction from the tuple form: a target with a
representation but no surviving tuple in `A \ B` is destroyed by `B`. -/
theorem destroyedBySet_of_no_surviving_tuple {A B : Set ℕ} {m : ℕ}
    (hrep : ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m)
    (hno : ¬ ∃ v : Fin 3 → ℕ, (∀ i, v i ∈ A \ B) ∧ ∑ i, v i = m) :
    DestroyedBySet A B m := by
  refine ⟨hrep, ?_⟩
  intro x hx y hy z hz hsum
  by_contra hne
  push Not at hne
  refine hno ⟨![x, y, z], ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all [Set.mem_diff]
  · simpa [Fin.sum_univ_three] using hsum

theorem DestroyedBySet.transversal_family_trichotomy {A B : Set ℕ} {N₀ m : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m) (hm : N₀ ≤ m) :
    (∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m) ∨
    (∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) ∨
    (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
      ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
        (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
        (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z)) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov m hm
  have hB := hdes.shadow h0 h0B hy hz (by omega)
  by_cases hyB : y ∈ B
  · by_cases hzB : z ∈ B
    · by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
          x' = y ∨ y' = y ∨ z' = y ∨ x' = z ∨ y' = z ∨ z' = z
      · exact Or.inr (Or.inl ⟨y, hyB, z, hzB, hdes.1, htr⟩)
      · push Not at htr
        obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3, h4, h5, h6⟩ :=
          htr
        exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inl hyB, x', hx',
          y', hy', z', hz', hsum',
          fun _ => ⟨h1, h2, h3⟩, fun _ => ⟨h4, h5, h6⟩⟩)
    · by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
          x' = y ∨ y' = y ∨ z' = y
      · exact Or.inl ⟨y, hyB, hy, hdes.1, htr⟩
      · push Not at htr
        obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3⟩ := htr
        exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inl hyB, x', hx',
          y', hy', z', hz', hsum',
          fun _ => ⟨h1, h2, h3⟩, fun hzB' => absurd hzB' hzB⟩)
  · have hzB : z ∈ B := hB.resolve_left hyB
    by_cases htr : ∀ x' ∈ A, ∀ y' ∈ A, ∀ z' ∈ A, x' + y' + z' = m →
        x' = z ∨ y' = z ∨ z' = z
    · exact Or.inl ⟨z, hzB, hz, hdes.1, htr⟩
    · push Not at htr
      obtain ⟨x', hx', y', hy', z', hz', hsum', h1, h2, h3⟩ := htr
      exact Or.inr (Or.inr ⟨y, hy, z, hz, hyz, Or.inr hzB, x', hx',
        y', hy', z', hz', hsum',
        fun hyB' => absurd hyB' hyB, fun _ => ⟨h1, h2, h3⟩⟩)

theorem DestroyedBySet.diffuse_witness_pair {A B : Set ℕ} {N₀ m : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m) (hm : N₀ ≤ m)
    (hsing : ¬ ∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m)
    (hpair : ¬ ∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂ ∧ b₁ ∈ A ∧ b₂ ∈ A ∧ b₁ ≤ m ∧ b₂ ≤ m := by
  rcases hdes.transversal_family_trichotomy h0 h0B hcov hm with h | h | h
  · exact absurd h hsing
  · exact absurd h hpair
  obtain ⟨y, hy, z, hz, hyz, hB, x', hx', y', hy', z', hz', hsum',
    havoidy, havoidz⟩ := h
  obtain ⟨b₂, hb₂B, hb₂A, hb₂rep⟩ :
      ∃ b₂ ∈ B, b₂ ∈ A ∧ (b₂ = x' ∨ b₂ = y' ∨ b₂ = z') := by
    rcases hdes.2 x' hx' y' hy' z' hz' hsum' with h' | h' | h'
    · exact ⟨x', h', hx', Or.inl rfl⟩
    · exact ⟨y', h', hy', Or.inr (Or.inl rfl)⟩
    · exact ⟨z', h', hz', Or.inr (Or.inr rfl)⟩
  rcases hB with hyB | hzB
  · have hne : b₂ ≠ y := by
      obtain ⟨e1, e2, e3⟩ := havoidy hyB
      rcases hb₂rep with rfl | rfl | rfl <;> assumption
    exact ⟨y, hyB, b₂, hb₂B, hne.symm, hy, hb₂A, by omega,
      by rcases hb₂rep with rfl | rfl | rfl <;> omega⟩
  · have hne : b₂ ≠ z := by
      obtain ⟨e1, e2, e3⟩ := havoidz hzB
      rcases hb₂rep with rfl | rfl | rfl <;> assumption
    exact ⟨z, hzB, b₂, hb₂B, hne.symm, hz, hb₂A, by omega,
      by rcases hb₂rep with rfl | rfl | rfl <;> omega⟩

theorem DestroyedBySet.translate_two_support_card_le
    {A B : Set ℕ} [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {m x : ℕ}
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) :
    ((Finset.range (m + 1)).filter
        fun y => y ∈ A ∧ x + y ≤ m ∧ m - x - y ∈ A).card ≤
      2 * ((Finset.range (m + 1)).filter fun b => b ∈ B).card := by
  set S := (Finset.range (m + 1)).filter
    fun y => y ∈ A ∧ x + y ≤ m ∧ m - x - y ∈ A with hS
  set T := (Finset.range (m + 1)).filter fun b => b ∈ B with hT
  set g : ℕ → ℕ := fun y => if y ∈ B then y else m - x - y with hg
  have hmem : ∀ y ∈ S, g y ∈ T := by
    intro y hy
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hy
    obtain ⟨hyr, hyA, hxy, hyz⟩ := hy
    have hside := hdes.shadow hx hxB hyA hyz (by omega)
    simp only [hT, hg, Finset.mem_filter, Finset.mem_range]
    by_cases hyB : y ∈ B
    · rw [if_pos hyB]
      exact ⟨hyr, hyB⟩
    · rw [if_neg hyB]
      rcases hside with h | h
      · exact absurd h hyB
      · exact ⟨by omega, h⟩
  have hfiber : ∀ b ∈ T, (S.filter fun y => g y = b).card ≤ 2 := by
    intro b _hb
    have hsub : (S.filter fun y => g y = b) ⊆ {b, m - x - b} := by
      intro y hy
      simp only [hS, hg, Finset.mem_filter, Finset.mem_range] at hy
      obtain ⟨⟨hyr, hyA, hxy, hyz⟩, hgy⟩ := hy
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hyB : y ∈ B
      · rw [if_pos hyB] at hgy
        exact Or.inl hgy
      · rw [if_neg hyB] at hgy
        right
        omega
    calc (S.filter fun y => g y = b).card
        ≤ ({b, m - x - b} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := by
          refine le_trans (Finset.card_insert_le _ _) ?_
          simp
  calc S.card
      = ∑ b ∈ T, (S.filter fun y => g y = b).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _b ∈ T, 2 := Finset.sum_le_sum hfiber
    _ = 2 * T.card := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- `n` is two-destroyed by the set `B`: every two-term representation
meets it. -/
def TwoDestroyedBySet (A B : Set ℕ) (n : ℕ) : Prop :=
  ∀ y ∈ A, ∀ z ∈ A, y + z = n → y ∈ B ∨ z ∈ B

/-- An undeleted element is never two-destroyed: its zero-augmented
representation avoids `B`. -/
theorem not_twoDestroyedBySet_of_mem_diff {A B : Set ℕ} {n : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B) (hn : n ∈ A) (hnB : n ∉ B) :
    ¬ TwoDestroyedBySet A B n := fun h => by
  rcases h 0 h0 n hn (by omega) with h' | h'
  · exact h0B h'
  · exact hnB h'

theorem DestroyedBySet.fork_trichotomy_elt {A B : Set ℕ} {N₀ m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hx : x ∈ A) (hxB : x ∉ B) (hxm : x + N₀ ≤ m) :
    ∃ u ∈ B, u ≤ m - x ∧
      (m - x - u ∈ B ∨
        (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  have hside := hdes.shadow hx hxB hy hz (by omega)
  rcases hside with hyB | hzB
  · refine ⟨y, hyB, by omega, ?_⟩
    by_cases hzB : z ∈ B
    · exact Or.inl (by
        have : m - x - y = z := by omega
        exact this ▸ hzB)
    · refine Or.inr ⟨by
        have : m - x - y = z := by omega
        exact this ▸ hz, ?_⟩
      intro s hs t ht hst
      by_contra hne
      push Not at hne
      rcases hdes.2 s hs t ht z hz (by omega) with h | h | h
      · exact hne.1 h
      · exact hne.2 h
      · exact hzB h
  · refine ⟨z, hzB, by omega, ?_⟩
    by_cases hyB : y ∈ B
    · exact Or.inl (by
        have : m - x - z = y := by omega
        exact this ▸ hyB)
    · refine Or.inr ⟨by
        have : m - x - z = y := by omega
        exact this ▸ hy, ?_⟩
      intro s hs t ht hst
      by_contra hne
      push Not at hne
      rcases hdes.2 s hs t ht y hy (by omega) with h | h | h
      · exact hne.1 h
      · exact hne.2 h
      · exact hyB h

theorem cofinal_transversal_family_trichotomy_of_deletionFailure
    {A B : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hfail : ¬ IsExactTupleAsymptoticBasis (A \ B) 3) :
    ∀ N, ∃ m, N ≤ m ∧
      ((∃ u ∈ B, u ∈ A ∧ IsPrivateTriple A u m) ∨
      (∃ u ∈ B, ∃ v ∈ B, IsPairDestroyer A u v m) ∨
      (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z))) := by
  intro N
  rw [IsExactTupleAsymptoticBasis] at hfail
  push Not at hfail
  obtain ⟨m, hmN, hno⟩ := hfail (max N N₀)
  have hm₀ : N₀ ≤ m := le_trans (le_max_right _ _) hmN
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov m hm₀
  have hdes : DestroyedBySet A B m :=
    destroyedBySet_of_no_surviving_tuple
      ⟨0, h0, y, hy, z, hz, by omega⟩
      (fun ⟨v, hv, hs⟩ => hno v hv hs)
  exact ⟨m, le_trans (le_max_left _ _) hmN,
    hdes.transversal_family_trichotomy h0 h0B hcov hm₀⟩

/-- Order-three destruction shadows to order two: with `0` undeleted,
a destroyed target is also two-destroyed.  Consequently the
counterexample's demand *at order two* — every infinite deletion
two-destroys cofinally — is exactly the ℵ₀-minimality hypothesis of
Erdős 881, granted for free: the whole content of the problem lives
in whether positive three-term representations can repair the
mandated two-destruction. -/
theorem DestroyedBySet.twoDestroyed {A B : Set ℕ} {m : ℕ}
    (hdes : DestroyedBySet A B m) (h0 : 0 ∈ A) (h0B : 0 ∉ B) :
    TwoDestroyedBySet A B m := by
  intro y hy z hz hyz
  rcases hdes.2 0 h0 y hy z hz (by omega) with h | h | h
  · exact absurd h h0B
  · exact Or.inl h
  · exact Or.inr h

theorem anchor_abundance_of_two_packages {A : Set ℕ}
    {c₁ w₁ w₁' c₂ w₂ w₂' : ℕ}
    (h₁ : c₁ ∈ A ∧ 0 < c₁ ∧ w₁ ∈ A ∧ w₁' ∈ A ∧
      w₁ + w₁' = 2 * c₁ ∧ w₁ ≠ c₁)
    (h₂ : c₂ ∈ A ∧ 0 < c₂ ∧ w₂ ∈ A ∧ w₂' ∈ A ∧
      w₂ + w₂' = 2 * c₂ ∧ w₂ ≠ c₂)
    (hdisj : c₁ ≠ c₂ ∧ c₁ ≠ w₂ ∧ c₁ ≠ w₂' ∧ w₁ ≠ c₂ ∧ w₁ ≠ w₂ ∧
      w₁ ≠ w₂' ∧ w₁' ≠ c₂ ∧ w₁' ≠ w₂ ∧ w₁' ≠ w₂') :
    ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g := by
  intro g
  obtain ⟨hc₁, hc₁0, hw₁, hw₁', hs₁, hn₁⟩ := h₁
  obtain ⟨hc₂, hc₂0, hw₂, hw₂', hs₂, hn₂⟩ := h₂
  by_cases hg : g = c₁ ∨ g = w₁ ∨ g = w₁'
  · exact ⟨c₂, hc₂, hc₂0, by omega, w₂, hw₂, w₂', hw₂',
      hs₂, hn₂, by omega, by omega⟩
  · push Not at hg
    exact ⟨c₁, hc₁, hc₁0, by omega, w₁, hw₁, w₁', hw₁',
      hs₁, hn₁, by omega, by omega⟩

theorem DestroyedBySet.concentration {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] {N₀ m n : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hcard : ((Finset.range (m + 1)).filter fun b => b ∈ B).card * n <
      ((Finset.range (m + 1)).filter
        fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m).card) :
    ∃ u ∈ B, ∃ S : Finset ℕ, n < S.card ∧
      ∀ x ∈ S, x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m ∧
        (m - x - u ∈ B ∨
          (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
  classical
  set X := (Finset.range (m + 1)).filter
    fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m with hX
  set T := (Finset.range (m + 1)).filter fun b => b ∈ B with hT
  have hpick : ∀ x ∈ X, ∃ u, u ∈ B ∧ u ≤ m - x ∧
      (m - x - u ∈ B ∨
        (m - x - u ∈ A ∧ TwoDestroyedBySet A B (u + x))) := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨u, huB, hum, hland⟩ :=
      hdes.fork_trichotomy_elt hcov hx.2.1 hx.2.2.1 hx.2.2.2
    exact ⟨u, huB, hum, hland⟩
  choose f hfB hfle hfland using hpick
  -- total function for the pigeonhole
  let g : ℕ → ℕ := fun x => if hx : x ∈ X then f x hx else 0
  have hmaps : ∀ x ∈ X, g x ∈ T := by
    intro x hx
    simp only [g, dif_pos hx]
    simp only [hT, Finset.mem_filter, Finset.mem_range]
    have h1 := hfB x hx
    have h2 := hfle x hx
    have hx' := hx
    simp only [hX, Finset.mem_filter, Finset.mem_range] at hx'
    exact ⟨by omega, h1⟩
  obtain ⟨u, huT, hufib⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  refine ⟨u, by
      simp only [hT, Finset.mem_filter] at huT
      exact huT.2, X.filter fun x => g x = u, hufib, ?_⟩
  intro x hx
  simp only [Finset.mem_filter] at hx
  obtain ⟨hxX, hgx⟩ := hx
  have hx' := hxX
  simp only [hX, Finset.mem_filter, Finset.mem_range] at hx'
  have hland := hfland x hxX
  have hgeq : f x hxX = u := by
    simpa [g, dif_pos hxX] using hgx
  rw [hgeq] at hland
  exact ⟨hx'.2.1, hx'.2.2.1, hx'.2.2.2, hland⟩

theorem DestroyedBySet.translate_exit {A B : Set ℕ}
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] {N₀ m n : ℕ}
    (h0 : 0 ∈ A) (h0B : 0 ∉ B)
    (hcov : PairCovers A N₀)
    (hdes : DestroyedBySet A B m)
    (hcard : ((Finset.range (m + 1)).filter fun b => b ∈ B).card * n <
      ((Finset.range (m + 1)).filter
        fun x => x ∈ A ∧ x ∉ B ∧ x + N₀ ≤ m).card) :
    ∃ u ∈ B, ∃ S : Finset ℕ, n < S.card ∧
      ∀ x ∈ S, x ∈ A ∧ x ∉ B ∧
        (m - x - u ∈ B ∨ u + x ∈ B ∨ u + x ∉ A) := by
  obtain ⟨u, huB, S, hScard, hS⟩ :=
    hdes.concentration hcov hcard
  refine ⟨u, huB, S, hScard, ?_⟩
  intro x hx
  obtain ⟨hxA, hxB, hxm, hland⟩ := hS x hx
  refine ⟨hxA, hxB, ?_⟩
  rcases hland with h | ⟨hwA, htwo⟩
  · exact Or.inl h
  · by_cases huxA : u + x ∈ A
    · by_cases huxB : u + x ∈ B
      · exact Or.inr (Or.inl huxB)
      · exact absurd htwo
          (not_twoDestroyedBySet_of_mem_diff h0 h0B huxA huxB)
    · exact Or.inr (Or.inr huxA)

theorem anchor_abundance_of_doubling {A : Set ℕ}
    (h0 : 0 ∈ A)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite)
    (hnz : ∃ c ∈ A, 0 < c ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ 0 < w ∧ 0 < w') :
    ∀ g, ∃ c ∈ A, 0 < c ∧ c ≠ g ∧ ∃ w ∈ A, ∃ w' ∈ A,
      w + w' = 2 * c ∧ w ≠ c ∧ w ≠ g ∧ w' ≠ g := by
  intro g
  rcases Nat.eq_zero_or_pos g with hg0 | hg0
  · obtain ⟨c, hc, hc0, w, hw, w', hw', hww, hwc, hw0, hw'0⟩ := hnz
    exact ⟨c, hc, hc0, by omega, w, hw, w', hw', hww, hwc,
      by omega, by omega⟩
  · obtain ⟨c, hcmem, hcg⟩ := hdb.exists_gt g
    obtain ⟨hcA, h2cA, hc0⟩ := hcmem
    exact ⟨c, hcA, hc0, by omega, 0, h0, 2 * c, h2cA,
      by omega, by omega, by omega, by omega⟩

theorem zero_required_element_no_element_gap {A : Set ℕ} {N₀ m₁ m₂ x : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁)
    (hd : m₂ - m₁ ∈ A) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m₁ - x) (by omega)
  have hw : m₁ - x ∈ A := by
    rcases h1.2 x hx y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m₁ - x := by omega
      exact this ▸ hz
    · have : y = m₁ - x := by omega
      exact this ▸ hy
  rcases h2.2 x hx (m₁ - x) hw (m₂ - m₁) hd (by omega) with h | h | h <;>
    omega

theorem zero_required_element_target_not_elt {A : Set ℕ} {N₀ m₁ m₂ x : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂) (hsep : m₁ + N₀ ≤ m₂)
    (hm₁A : m₁ ∈ A) (hm₁0 : 0 < m₁)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m₂ - m₁) (by omega)
  have hd : m₂ - m₁ ∈ A := by
    rcases h2.2 m₁ hm₁A y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m₂ - m₁ := by omega
      exact this ▸ hz
    · have : y = m₂ - m₁ := by omega
      exact this ▸ hy
  exact zero_required_element_no_element_gap hcov h1 h2 hlt hx hx0 hxm hxlt hd

theorem zero_required_element_hole {A : Set ℕ} {N₀ m₁ m₂ m₃ x y z : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (h3 : IsPrivateTriple A 0 m₃)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁)
    (hy : y ∈ A) (hy0 : 0 < y) (hym : y + N₀ ≤ m₂) (hylt : y < m₂)
    (hz : z ∈ A) (hz0 : 0 < z)
    (hsum : (m₁ - x) + (m₂ - y) + z = m₃) :
    False := by
  obtain ⟨y₁, hy₁, z₁, hz₁, hyz₁⟩ := hcov (m₁ - x) (by omega)
  have hw₁ : m₁ - x ∈ A := by
    rcases h1.2 x hx y₁ hy₁ z₁ hz₁ (by omega) with h | h | h
    · omega
    · have : z₁ = m₁ - x := by omega
      exact this ▸ hz₁
    · have : y₁ = m₁ - x := by omega
      exact this ▸ hy₁
  obtain ⟨y₂, hy₂, z₂, hz₂, hyz₂⟩ := hcov (m₂ - y) (by omega)
  have hw₂ : m₂ - y ∈ A := by
    rcases h2.2 y hy y₂ hy₂ z₂ hz₂ (by omega) with h | h | h
    · omega
    · have : z₂ = m₂ - y := by omega
      exact this ▸ hz₂
    · have : y₂ = m₂ - y := by omega
      exact this ▸ hy₂
  rcases h3.2 (m₁ - x) hw₁ (m₂ - y) hw₂ z hz hsum with h | h | h <;>
    omega

/-- A singleton private required element is a pair destroyer with itself. -/
theorem IsPrivateTriple.isPairDestroyer_self {A : Set ℕ} {u m : ℕ}
    (h : IsPrivateTriple A u m) : IsPairDestroyer A u u m := by
  refine ⟨h.1, ?_⟩
  intro x hx y hy z hz hsum
  rcases h.2 x hx y hy z hz hsum with h' | h' | h' <;> tauto

theorem hasCofinalPairTransversalFamilies_of_diffuse_free {A : Set ℕ} {N₀ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hfail : ∀ B ⊆ A, B.Infinite →
      ¬ IsExactTupleAsymptoticBasis (A \ B) 3)
    (hnodiffuse : ∀ B ⊆ A, 0 ∉ B → B.Infinite → ∃ N, ∀ m, N ≤ m →
      ¬ (∃ y ∈ A, ∃ z ∈ A, y + z = m ∧ (y ∈ B ∨ z ∈ B) ∧
        ∃ x' ∈ A, ∃ y' ∈ A, ∃ z' ∈ A, x' + y' + z' = m ∧
          (y ∈ B → x' ≠ y ∧ y' ≠ y ∧ z' ≠ y) ∧
          (z ∈ B → x' ≠ z ∧ y' ≠ z ∧ z' ≠ z))) :
    HasCofinalPairTransversalFamilies A := by
  intro B hBA hBinf N
  set B' := B \ {0} with hB'
  have hB'A : B' ⊆ A := fun x hx => hBA hx.1
  have hB'inf : B'.Infinite := hBinf.diff (Set.finite_singleton 0)
  have h0B' : 0 ∉ B' := fun h => h.2 rfl
  obtain ⟨N₁, hN₁⟩ := hnodiffuse B' hB'A h0B' hB'inf
  obtain ⟨m, hm, htri⟩ :=
    cofinal_transversal_family_trichotomy_of_deletionFailure h0 h0B' hcov
      (hfail B' hB'A hB'inf) (max N N₁)
  rcases htri with ⟨u, huB, _, hpriv⟩ | ⟨u, huB, v, hvB, hdes⟩ | hdiff
  · exact ⟨m, le_trans (le_max_left _ _) hm, u, huB.1, u, huB.1,
      hpriv.isPairDestroyer_self⟩
  · exact ⟨m, le_trans (le_max_left _ _) hm, u, huB.1, v, hvB.1, hdes⟩
  · exact absurd hdiff (hN₁ m (le_trans (le_max_right _ _) hm))

theorem zero_residue_structure {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (x : ℕ) (hx : x ∈ A) (hx0 : 0 < x) :
    ∀ N, ∃ m₁ m₂, N ≤ m₁ ∧ m₁ + N₀ ≤ m₂ ∧
      IsPrivateTriple A 0 m₁ ∧ IsPrivateTriple A 0 m₂ ∧
      (x + N₀ ≤ m₁ → x < m₁ → (m₂ - m₁ ∉ A ∧ (0 < m₁ → m₁ ∉ A))) := by
  intro N
  obtain ⟨m₁, hm₁N, h1⟩ := hres N
  obtain ⟨m₂, hm₂N, h2⟩ := hres (m₁ + N₀ + 1)
  refine ⟨m₁, m₂, hm₁N, by omega, h1, h2, ?_⟩
  intro hxm hxlt
  constructor
  · intro hd
    exact zero_required_element_no_element_gap hcov h1 h2 (by omega)
      hx hx0 hxm hxlt hd
  · intro hm₁0 hm₁A
    exact zero_required_element_target_not_elt hcov h1 h2 (by omega)
      (by omega) hm₁A hm₁0 hx hx0 hxm hxlt

theorem zero_gap_interior_element {A : Set ℕ} {N₀ m₁ m₂ x : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂) (hgap : m₁ + N₀ ≤ m₂)
    (hx : x ∈ A) (hx0 : 0 < x) (hxm : x + N₀ ≤ m₁) (hxlt : x < m₁) :
    ∃ z ∈ A, 0 < z ∧ z < m₂ - m₁ ∧ m₁ + z ∈ A := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m₂ - m₁) (by omega)
  -- neither part can vanish
  have hy0 : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h | h
    · exfalso
      have hzd : z = m₂ - m₁ := by omega
      exact zero_required_element_no_element_gap hcov h1 h2 hlt hx hx0 hxm
        hxlt (hzd ▸ hz)
    · exact h
  have hz0 : 0 < z := by
    rcases Nat.eq_zero_or_pos z with h | h
    · exfalso
      have hyd : y = m₂ - m₁ := by omega
      exact zero_required_element_no_element_gap hcov h1 h2 hlt hx hx0 hxm
        hxlt (hyd ▸ hy)
    · exact h
  -- lift the y-part through the higher mirror
  obtain ⟨y₂, hy₂, z₂, hz₂, hyz₂⟩ := hcov (m₂ - y) (by omega)
  have hlift : m₂ - y ∈ A := by
    rcases h2.2 y hy y₂ hy₂ z₂ hz₂ (by omega) with h | h | h
    · omega
    · have : z₂ = m₂ - y := by omega
      exact this ▸ hz₂
    · have : y₂ = m₂ - y := by omega
      exact this ▸ hy₂
  refine ⟨z, hz, hz0, by omega, ?_⟩
  have : m₁ + z = m₂ - y := by omega
  exact this ▸ hlift

theorem zero_mirror_primitive {A : Set ℕ} {N₀ m p : ℕ}
    (hcov : PairCovers A N₀)
    (hm : IsPrivateTriple A 0 m)
    (hp : p ∈ A) (hp0 : 0 < p) (hpm : p + N₀ ≤ m)
    (_hprim : ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = p ∧ 0 < s ∧ 0 < t) :
    (m - p ∈ A) ∧
    ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = m - p ∧ 0 < s ∧ 0 < t := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - p) (by omega)
  have hmem : m - p ∈ A := by
    rcases hm.2 p hp y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m - p := by omega
      exact this ▸ hz
    · have : y = m - p := by omega
      exact this ▸ hy
  refine ⟨hmem, ?_⟩
  rintro ⟨s, hs, t, ht, hst, hs0, ht0⟩
  rcases hm.2 p hp s hs t ht (by omega) with h | h | h <;> omega

theorem zero_targets_translate_primitives {A : Set ℕ} {N₀ m₁ m₂ p : ℕ}
    (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A 0 m₁) (h2 : IsPrivateTriple A 0 m₂)
    (hlt : m₁ < m₂)
    (hp : p ∈ A) (hp0 : 0 < p) (hpm : p + N₀ ≤ m₁) (hplt : p < m₁)
    (hgap : m₁ + N₀ ≤ m₂)
    (hprim : ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = p ∧ 0 < s ∧ 0 < t) :
    (p + (m₂ - m₁) ∈ A) ∧
    ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = p + (m₂ - m₁) ∧ 0 < s ∧ 0 < t := by
  obtain ⟨hq, hqprim⟩ :=
    zero_mirror_primitive hcov h1 hp hp0 hpm hprim
  have hq0 : 0 < m₁ - p := by omega
  have hqm : (m₁ - p) + N₀ ≤ m₂ := by omega
  obtain ⟨hr, hrprim⟩ :=
    zero_mirror_primitive hcov h2 hq hq0 hqm hqprim
  have he : m₂ - (m₁ - p) = p + (m₂ - m₁) := by omega
  exact ⟨he ▸ hr, he ▸ hrprim⟩

theorem cofinal_primitives_of_zero_residue {A : Set ℕ} {N₀ p : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hp : p ∈ A) (hp0 : 0 < p)
    (hprim : ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = p ∧ 0 < s ∧ 0 < t) :
    ∀ K, ∃ q, K ≤ q ∧ q ∈ A ∧ 0 < q ∧
      ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = q ∧ 0 < s ∧ 0 < t := by
  intro K
  induction K with
  | zero => exact ⟨p, Nat.zero_le _, hp, hp0, hprim⟩
  | succ K ih =>
      obtain ⟨q, hKq, hqA, hq0, hqprim⟩ := ih
      obtain ⟨m₁, hm₁, h1⟩ := hres (q + N₀ + 1)
      obtain ⟨m₂, hm₂, h2⟩ := hres (m₁ + N₀ + 1)
      obtain ⟨hmem, hprim'⟩ :=
        zero_targets_translate_primitives hcov h1 h2 (by omega)
          hqA hq0 (by omega) (by omega) (by omega) hqprim
      exact ⟨q + (m₂ - m₁), by omega, hmem, by omega, hprim'⟩

theorem zero_target_window_primitive {A : Set ℕ} {N₀ m a : ℕ}
    (hcov : PairCovers A N₀)
    (hm : IsPrivateTriple A 0 m)
    (ha : a ∈ A) (ha0 : 0 < a) (ham : a + N₀ ≤ m) (halt : a < m) :
    ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = a ∧ 0 < s ∧ 0 < t := by
  rintro ⟨s, hs, t, ht, hst, hs0, ht0⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - a) (by omega)
  have hmir : m - a ∈ A := by
    rcases hm.2 a ha y hy z hz (by omega) with h | h | h
    · omega
    · have : z = m - a := by omega
      exact this ▸ hz
    · have : y = m - a := by omega
      exact this ▸ hy
  rcases hm.2 s hs t ht (m - a) hmir (by omega) with h | h | h <;> omega

theorem zero_residue_sum_free {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) :
    ∀ a ∈ A, 0 < a →
      ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = a ∧ 0 < s ∧ 0 < t := by
  intro a ha ha0
  obtain ⟨m, hm, hpriv⟩ := hres (a + N₀ + 1)
  exact zero_target_window_primitive hcov hpriv ha ha0 (by omega)
    (by omega)

theorem zero_residue_exact_partition {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) :
    ∀ n, N₀ ≤ n →
      (n ∈ A ↔ ¬ ∃ s ∈ A, ∃ t ∈ A, s + t = n ∧ 0 < s ∧ 0 < t) := by
  intro n hn
  constructor
  · intro hnA
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · rintro ⟨s, hs, t, ht, hst, hs0, ht0⟩
      omega
    · exact zero_residue_sum_free hcov hres n hnA hn0
  · intro hnorep
    obtain ⟨y, hy, z, hz, hyz⟩ := hcov n hn
    rcases Nat.eq_zero_or_pos y with hy0 | hy0
    · have : z = n := by omega
      exact this ▸ hz
    · rcases Nat.eq_zero_or_pos z with hz0 | hz0
      · have : y = n := by omega
        exact this ▸ hy
      · exact absurd ⟨y, hy, z, hz, hyz, hy0, hz0⟩ hnorep

theorem sumfree_element_support {A : Set ℕ} {N₀ n : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hn : n ∈ A) (hn0 : 0 < n) :
    ∀ y ∈ A, ∀ z ∈ A, y + z = n → y = 0 ∨ z = 0 := by
  intro y hy z hz hyz
  by_contra hne
  push Not at hne
  exact zero_residue_sum_free hcov hres n hn hn0
    ⟨y, hy, z, hz, hyz, by omega, by omega⟩

theorem sumfree_element_triple {A : Set ℕ} {N₀ n x : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m)
    (hn : n ∈ A) (hx : x ∈ A) (hx0 : 0 < x)
    (hxn : x + N₀ ≤ n) (hxlt : x < n) :
    ∃ s ∈ A, ∃ t ∈ A, 0 < s ∧ 0 < t ∧ x + s + t = n := by
  have hnx : n - x ∉ A ∨ n - x = 0 := by
    rcases Nat.eq_zero_or_pos (n - x) with h | h
    · exact Or.inr h
    · left
      intro hmem
      exact zero_residue_sum_free hcov hres n hn (by omega)
        ⟨x, hx, n - x, hmem, by omega, hx0, h⟩
  have hnx0 : 0 < n - x := by omega
  rcases hnx with hnxA | h
  · have hpair : ∃ s ∈ A, ∃ t ∈ A, s + t = n - x ∧ 0 < s ∧ 0 < t := by
      by_contra hno
      exact hnxA
        ((zero_residue_exact_partition hcov hres (n - x)
          (by omega)).mpr hno)
    obtain ⟨s, hs, t, ht, hst, hs0, ht0⟩ := hpair
    exact ⟨s, hs, t, ht, hs0, ht0, by omega⟩
  · omega

theorem zero_residue_no_doubling {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hres : ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m) :
    ¬ ∃ c, c ∈ A ∧ 2 * c ∈ A ∧ 0 < c := by
  rintro ⟨c, hc, h2c, hc0⟩
  exact zero_residue_sum_free hcov hres (2 * c) h2c (by omega)
    ⟨c, hc, c, hc, by omega, hc0, hc0⟩

/-- Doubling supply contradicts the zero residue. -/
theorem not_zero_residue_of_doubling {A : Set ℕ} {N₀ : ℕ}
    (hcov : PairCovers A N₀)
    (hdb : {c | c ∈ A ∧ 2 * c ∈ A ∧ 0 < c}.Infinite) :
    ¬ ∀ N, ∃ m, N ≤ m ∧ IsPrivateTriple A 0 m := by
  intro hres
  obtain ⟨c, hcmem, -⟩ := hdb.exists_gt 0
  exact zero_residue_no_doubling hcov hres
    ⟨c, hcmem.1, hcmem.2.1, hcmem.2.2⟩

end Erdos881
