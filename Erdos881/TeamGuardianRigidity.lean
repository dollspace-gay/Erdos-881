import Erdos881.GuardianRigidity

/-!
# Rigidity of order-three guardian teams

A target `m` is *team-guarded* by `{p, q}` when every exact three-term
representation of `m` uses `p` or `q`, and genuinely so: neither guardian
suffices alone.  With `p < q` the two channels sit at `D_p = m - p` and
`D_q = m - q`, and against an order-two covering hypothesis the landscape
is again rigid:

* `desert`       : `A ∩ (D_p, m - N₀)` contains only `p` and `q`;
* `bimirror`     : below the smaller channel `D_q`, every element reflects
  through one of the two channels (`z ↦ D_p - z` or `z ↦ D_q - z`);
* `upper_mirror` : in the mid-zone `(D_q, D_p)`, only the `p`-channel is
  available, so reflection there is single-channel;
* `forced_translate` : covered numbers high above `2*D_p` are a guardian
  plus an element.

The centerpiece is `no_big_guardian_above_sparse_window`: a big singleton
guardian cannot sit above *any* four-integer window containing at most two
elements — which is exactly what a lower desert provides, singleton or
team.  `no_big_guardian_above_team` instantiates it: the singleton
mechanism cannot restart above a guardian team.

Finite evidence (`scripts/probe_team_guardians.py`,
`scripts/probe_team_rigidity_and_gaps.py`): team-guarded targets and even
3-cliques of mutual guardianship exist at a single scale, but no stacked
two-scale configuration was found in exhaustive sweeps, and the three
rigidity predictions above hold on every team instance checked.
-/

namespace Erdos881

/-- `m` is genuinely team-guarded by `{p, q}`: it has an exact three-term
representation, every representation uses `p` or `q`, and each guardian is
avoidable individually. -/
def IsTeamPrivateTriple (A : Set ℕ) (p q m : ℕ) : Prop :=
  (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x + y + z = m) ∧
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = m →
      x = p ∨ y = p ∨ z = p ∨ x = q ∨ y = q ∨ z = q) ∧
    (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x + y + z = m ∧ x ≠ p ∧ y ≠ p ∧ z ≠ p) ∧
    (∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A,
      x + y + z = m ∧ x ≠ q ∧ y ≠ q ∧ z ≠ q)

/-- Team desert: above the larger channel `D_p = m - p`, the only elements
below `m - N₀` are the guardians themselves. -/
theorem IsTeamPrivateTriple.desert {A : Set ℕ} {N₀ p q m : ℕ}
    (hcov : PairCovers A N₀)
    (hteam : IsTeamPrivateTriple A p q m)
    (hp : 0 < p) (hpq : p < q)
    {z : ℕ} (hz : z ∈ A) (hlow : m < p + z) (hhigh : z + N₀ ≤ m) :
    z = p ∨ z = q := by
  by_contra hne
  push Not at hne
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hteam.2.1 z hz u hu v hv (by omega) with h | h | h | h | h | h <;>
    omega

/-- Bi-mirror: below the smaller channel `D_q = m - q`, every non-guardian
element reflects through one of the two channels. -/
theorem IsTeamPrivateTriple.bimirror {A : Set ℕ} {N₀ p q m : ℕ}
    (hcov : PairCovers A N₀)
    (hteam : IsTeamPrivateTriple A p q m)
    (hpq : p < q) (hqN : N₀ ≤ q)
    {z : ℕ} (hz : z ∈ A) (hzq : z + q < m) (hzp : z ≠ p) (hzq' : z ≠ q) :
    (∃ w ∈ A, p + z + w = m) ∨ (∃ w ∈ A, q + z + w = m) := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hteam.2.1 z hz u hu v hv (by omega) with h | h | h | h | h | h
  · exact absurd h hzp
  · exact Or.inl ⟨v, hv, by omega⟩
  · exact Or.inl ⟨u, hu, by omega⟩
  · exact absurd h hzq'
  · exact Or.inr ⟨v, hv, by omega⟩
  · exact Or.inr ⟨u, hu, by omega⟩

/-- Mid-zone mirror: strictly between the channels only the `p`-channel
can absorb a representation, so reflection there is single-channel. -/
theorem IsTeamPrivateTriple.upper_mirror {A : Set ℕ} {N₀ p q m : ℕ}
    (hcov : PairCovers A N₀)
    (hteam : IsTeamPrivateTriple A p q m)
    (hpq : p < q)
    {z : ℕ} (hz : z ∈ A) (hzlow : m < q + z) (hzhigh : z + p + N₀ ≤ m)
    (hzp : z ≠ p) (hzq : z ≠ q) :
    ∃ w ∈ A, p + z + w = m := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov (m - z) (by omega)
  rcases hteam.2.1 z hz u hu v hv (by omega) with h | h | h | h | h | h
  · exact absurd h hzp
  · exact ⟨v, hv, by omega⟩
  · exact ⟨u, hu, by omega⟩
  · exact absurd h hzq
  · omega
  · omega

/-- Team forced translate: a covered number strictly above `2*D_p` and at
least `N₀` below `m` is one of the guardians plus an element. -/
theorem IsTeamPrivateTriple.forced_translate {A : Set ℕ} {N₀ p q m : ℕ}
    (hcov : PairCovers A N₀)
    (hteam : IsTeamPrivateTriple A p q m)
    (hp : 0 < p) (hpq : p < q) (hqm : q ≤ m)
    {n : ℕ} (hn : N₀ ≤ n) (hn2 : 2 * (m - p) < n) (hnm : n + N₀ ≤ m) :
    ∃ t ∈ A, p + t = n ∨ q + t = n := by
  obtain ⟨u, hu, v, hv, huv⟩ := hcov n hn
  rcases Nat.lt_or_ge (m - p) u with hu1 | hu1
  · rcases hteam.desert hcov hp hpq hu (by omega) (by omega) with h | h
    · exact ⟨v, hv, Or.inl (by omega)⟩
    · exact ⟨v, hv, Or.inr (by omega)⟩
  · rcases Nat.lt_or_ge (m - p) v with hv1 | hv1
    · rcases hteam.desert hcov hp hpq hv (by omega) (by omega) with h | h
      · exact ⟨u, hu, Or.inl (by omega)⟩
      · exact ⟨u, hu, Or.inr (by omega)⟩
    · omega

/-- **No big guardian above a sparse window.**  A big-guardian private
pair cannot sit above any window of four consecutive integers containing
at most two elements of `A`.  Either the guardian is low, and the mirror
below its co-representative manufactures a guardian-free representation;
or it is near its boundary, and the forced-translate window floods three
distinct integers of the sparse window into `A`. -/
theorem no_big_guardian_above_sparse_window {A : Set ℕ} {N₀ a m g e₁ e₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hpriv : IsPrivateTriple A a m)
    (hbig : m < 2 * a) (hN : N₀ + a ≤ m)
    (hwin : ∀ z ∈ A, g < z → z < g + 4 → z = e₁ ∨ z = e₂)
    (hgN : N₀ ≤ g)
    (hsep : g + 4 + N₀ + a ≤ m) :
    False := by
  have ha : 0 < a := by omega
  obtain ⟨M₂, hM₂A, hM₂⟩ := hpriv.corep_mem h0 hcov ha (by omega)
  by_cases hcase : a + g < 2 * M₂
  · by_cases hjA : (a - M₂) ∈ A
    · rcases hpriv.2 M₂ hM₂A M₂ hM₂A _ hjA (by omega) with h | h | h <;> omega
    · have hn'' : N₀ ≤ 2 * M₂ - a := by omega
      obtain ⟨u, hu, v, hv, huv⟩ := hcov _ hn''
      rcases Nat.eq_zero_or_pos u with hu0 | hu0
      · obtain ⟨w, hw, hws⟩ :=
          hpriv.mirror h0 hcov hbig hN hv (by omega) (by omega)
        have hwe : w = a - M₂ := by omega
        exact hjA (hwe ▸ hw)
      rcases Nat.eq_zero_or_pos v with hv0 | hv0
      · obtain ⟨w, hw, hws⟩ :=
          hpriv.mirror h0 hcov hbig hN hu (by omega) (by omega)
        have hwe : w = a - M₂ := by omega
        exact hjA (hwe ▸ hw)
      obtain ⟨wu, hwu, hwus⟩ :=
        hpriv.mirror h0 hcov hbig hN hu hu0 (by omega)
      obtain ⟨wv, hwv, hwvs⟩ :=
        hpriv.mirror h0 hcov hbig hN hv hv0 (by omega)
      rcases hpriv.2 wu hwu wv hwv M₂ hM₂A (by omega) with h | h | h <;> omega
  · have key : ∀ j, g < j → j < g + 4 → j ∈ A := by
      intro j hj1 hj2
      obtain ⟨t, ht, hts⟩ :=
        hpriv.forced_translate h0 hcov ha (by omega)
          (n := j + a) (by omega) (by omega) (by omega)
      have hte : t = j := by omega
      exact hte ▸ ht
    have h1 := hwin _ (key (g + 1) (by omega) (by omega)) (by omega) (by omega)
    have h2 := hwin _ (key (g + 2) (by omega) (by omega)) (by omega) (by omega)
    have h3 := hwin _ (key (g + 3) (by omega) (by omega)) (by omega) (by omega)
    omega

/-- **A big guardian cannot restart above a small guardian either.**  The
small guardian's desert is completely empty, so it is a sparse window par
excellence. -/
theorem no_big_guardian_above_small_guardian
    {A : Set ℕ} {N₀ a₁ m₁ a₂ m₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (h1 : IsPrivateTriple A a₁ m₁) (ha₁ : 0 < a₁)
    (hsmall : 2 * a₁ < m₁) (hN1 : N₀ + a₁ ≤ m₁)
    (h2 : IsPrivateTriple A a₂ m₂)
    (hbig2 : m₂ < 2 * a₂) (hN2 : N₀ + a₂ ≤ m₂)
    (hsize : N₀ + 4 ≤ a₁)
    (hsep : m₁ + a₂ ≤ m₂) :
    False :=
  no_big_guardian_above_sparse_window (g := m₁ - a₁) (e₁ := 0) (e₂ := 0)
    h0 hcov h2 hbig2 hN2
    (fun z hz hg1 hg2 =>
      (h1.small_desert h0 hcov ha₁ hsmall hz (by omega) (by omega)).elim)
    (by omega) (by omega)

/-- **The singleton mechanism cannot restart above a guardian team.**  A
big-guardian private pair strictly above a genuine team configuration is
contradictory: the team desert is the sparse window the upper guardian
cannot tolerate. -/
theorem no_big_guardian_above_team {A : Set ℕ} {N₀ p₁ q₁ m₁ a₂ m₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hteam : IsTeamPrivateTriple A p₁ q₁ m₁)
    (hp : 0 < p₁) (hpq : p₁ < q₁)
    (h2 : IsPrivateTriple A a₂ m₂)
    (hbig2 : m₂ < 2 * a₂) (hN2 : N₀ + a₂ ≤ m₂)
    (hsize : N₀ + 4 ≤ p₁) (hm₁ : p₁ + N₀ ≤ m₁)
    (hsep : m₁ + a₂ ≤ m₂) :
    False := by
  refine no_big_guardian_above_sparse_window (g := m₁ - p₁)
    (e₁ := p₁) (e₂ := q₁) h0 hcov h2 hbig2 hN2 ?_ (by omega) (by omega)
  intro z hz hg1 hg2
  exact hteam.desert hcov hp hpq hz (by omega) (by omega)

end Erdos881
