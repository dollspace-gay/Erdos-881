import Erdos881.TeamGraphRamsey

/-!
# The pinning lemma and pinned mirrors

The Cassaigne–Plagne two-destroyer engine, transplanted to team edges.
For a target `m` destroyed by the pair `{u, v}` (every exact three-term
representation meets the pair), the bimirror of an element `x` forks
between the two channels `m - u - x` and `m - v - x`.  The *pinning
lemma* kills a channel: if `u + x` has a two-term representation
avoiding both guards, the `u`-channel cannot be realized — substituting
the representation for `u + x` inside `m = u + x + (m - u - x)` would
produce a guard-free representation of the destroyed target.

Consequences, all verified numerically first
(`scripts/probe_pinned_forks.py`: 25 824 channel instances, zero
violations; `scripts/probe_pinned_mirror.py`):

* `IsPairDestroyer.pinned_mirror` — with the `u`-channel pinned shut,
  the fork *must* realize the `v`-channel: a perfect one-channel mirror
  `x ↦ (m - v) - x` into `A`;
* `IsPairDestroyer.double_pin_desert` — an element whose two cross-sums
  both admit avoiding representations cannot exist below a destroyed
  target: both channels die and the bimirror has nowhere to go;
* `TwoRedundant` — the pin supplier: `u` is 2-redundant when every
  large integer has a two-term representation avoiding `u`.  By
  Erdős–Graham/Grekos finiteness of essential elements (literature,
  not yet formalized) all but finitely many elements of any order-two
  basis are 2-redundant.  For `x` below `v - u`, an avoiding
  representation of `u + x` automatically avoids `v` as well, so a
  2-redundant `u` pins *every* fork of its high edges;
* `IsPairDestroyer.pinned_level` / `cofinal_pinned_levels` — a
  2-redundant clique vertex with clear targets manufactures element
  mirror levels `m - v ∈ A` cofinally, the raw material of the
  verified mirror endgame (`MirrorPeriodicity`, `UnboundedMirrorGaps`).

The lab shows the triangle route this replaces is dead as stated:
separated team triangles exist inside full covering sets
(`SeparatedTriangle.lean`), so no proof can kill one triple by guard
separation alone.  The pinned-mirror route needs no triangle at all.
-/

namespace Erdos881

/-- Desert under destruction alone: an element strictly above the
larger channel `m - u` and at least `N₀` below `m` is one of the two
guards.  (`IsTeamPrivateTriple.desert` restated for a bare
`IsPairDestroyer`, whose hypotheses are all the proof ever used.) -/
theorem IsPairDestroyer.desert {A : Set ℕ} {N₀ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hu : 0 < u) (huv : u < v)
    {z : ℕ} (hz : z ∈ A) (hlow : m < u + z) (hhigh : z + N₀ ≤ m) :
    z = u ∨ z = v := by
  by_contra hne
  push Not at hne
  obtain ⟨y, hy, w, hw, hyw⟩ := hcov (m - z) (by omega)
  rcases hdes.2 z hz y hy w hw (by omega) with h | h | h | h | h | h <;>
    omega

/-- **The pinning lemma.**  If `u + x` has a two-term representation
`s + t` avoiding both guards of a destroyed target `m`, then the
`u`-channel of `x`'s bimirror is dead: `m - u - x ∈ A` would give
`m = s + t + (m - u - x)`, a representation avoiding the pair. -/
theorem IsPairDestroyer.pinned {A : Set ℕ} {u v m x s t : ℕ}
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hs : s ∈ A) (ht : t ∈ A) (hsum : s + t = u + x)
    (hsu : s ≠ u) (hsv : s ≠ v) (htu : t ≠ u) (htv : t ≠ v)
    (hroom : x + 2 * v < m)
    (hw : m - u - x ∈ A) :
    False := by
  have h := hdes.2 s hs t ht (m - u - x) hw (by omega)
  omega

/-- **The pinned mirror.**  With the `u`-channel pinned shut, the fork
must realize the `v`-channel: `m - v - x ∈ A`. -/
theorem IsPairDestroyer.pinned_mirror {A : Set ℕ} {N₀ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v) (hxm : x + N₀ ≤ m)
    (hrep : ∃ s ∈ A, ∃ t ∈ A,
      s + t = u + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hroom : x + 2 * v < m) :
    m - v - x ∈ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ := hrep
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (m - x) (by omega)
  rcases hdes.2 x hx y hy z hz (by omega) with h | h | h | h | h | h
  · exact absurd h hxu
  · have hw : m - u - x ∈ A := by
      have hz' : z = m - u - x := by omega
      exact hz' ▸ hz
    exact (hdes.pinned huv hs ht hst hsu hsv htu htv hroom hw).elim
  · have hw : m - u - x ∈ A := by
      have hy' : y = m - u - x := by omega
      exact hy' ▸ hy
    exact (hdes.pinned huv hs ht hst hsu hsv htu htv hroom hw).elim
  · exact absurd h hxv
  · have hz' : z = m - v - x := by omega
    exact hz' ▸ hz
  · have hy' : y = m - v - x := by omega
    exact hy' ▸ hy

/-- **Double-pin desert.**  An element whose cross-sums with *both*
guards admit avoiding two-term representations cannot sit below a
destroyed target: both channels of its bimirror are dead. -/
theorem IsPairDestroyer.double_pin_desert {A : Set ℕ} {N₀ u v m x : ℕ}
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxv : x ≠ v) (hxm : x + N₀ ≤ m)
    (hrepu : ∃ s ∈ A, ∃ t ∈ A,
      s + t = u + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hrepv : ∃ s ∈ A, ∃ t ∈ A,
      s + t = v + x ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v)
    (hroom : x + 2 * v < m) :
    False := by
  have hmv := hdes.pinned_mirror hcov huv hx hxu hxv hxm hrepu hroom
  obtain ⟨s, hs, t, ht, hst, hsu, hsv, htu, htv⟩ := hrepv
  have h := hdes.2 s hs t ht (m - v - x) hmv (by omega)
  omega

/-- `u` is *2-redundant above `N₁`*: every integer from `N₁` on has a
two-term representation avoiding `u`.  Equivalently, `A \ {u}` is still
an asymptotic order-two covering set.  By Erdős–Graham/Grekos, all but
finitely many elements of an order-two basis are 2-redundant. -/
def TwoRedundant (A : Set ℕ) (u N₁ : ℕ) : Prop :=
  ∀ n, N₁ ≤ n → ∃ s ∈ A, ∃ t ∈ A, s + t = n ∧ s ≠ u ∧ t ≠ u

/-- For `x` below the window `v - u`, an avoiding representation of
`u + x` supplied by 2-redundancy automatically avoids `v` as well, so
the pinned mirror fires with no further hypotheses on `v`. -/
theorem TwoRedundant.pinned_mirror {A : Set ℕ} {N₀ N₁ u v m x : ℕ}
    (hred : TwoRedundant A u N₁)
    (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v)
    (hx : x ∈ A) (hxu : x ≠ u) (hxm : x + N₀ ≤ m)
    (hN₁ : N₁ ≤ u + x) (hwin : u + x < v)
    (hroom : x + 2 * v < m) :
    m - v - x ∈ A := by
  obtain ⟨s, hs, t, ht, hst, hsu, htu⟩ := hred (u + x) hN₁
  exact hdes.pinned_mirror hcov huv hx hxu (by omega) hxm
    ⟨s, hs, t, ht, hst, hsu, by omega, htu, by omega⟩ hroom

/-- The corep of a pinned edge is an element: taking `x = 0` in the
pinned mirror forces `m - v ∈ A`. -/
theorem TwoRedundant.corep_mem {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (hred : TwoRedundant A u N₁)
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v)
    (hN₀ : N₀ ≤ m) (hN₁ : N₁ ≤ u) (hroom : 2 * v < m) :
    m - v ∈ A := by
  have h := hred.pinned_mirror hcov hdes huv h0 (by omega) (by omega)
    (by omega) (by omega) (by omega)
  simpa using h

/-- **The pinned level.**  A clear destroyed target of an edge whose
low guard is 2-redundant yields an element mirror level: the corep
`m - v` is an element, and every element of the window below `v - u`
reflects through it into `A`. -/
theorem IsPairDestroyer.pinned_level {A : Set ℕ} {N₀ N₁ u v m : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes : IsPairDestroyer A u v m)
    (hu0 : 0 < u) (huv : u < v)
    (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear : 3 * v ≤ m) :
    m - v ∈ A ∧
      ∀ x ∈ A, x ≠ u → u + x < v → m - v - x ∈ A := by
  refine ⟨hred.corep_mem h0 hcov hdes hu0 huv (by omega) hN₁ (by omega),
    ?_⟩
  intro x hx hxu hwin
  exact hred.pinned_mirror hcov hdes huv hx hxu (by omega) (by omega)
    hwin (by omega)

/-- The pair `{u, v}` is *jointly 2-redundant above `N₂`*: every
integer from `N₂` on has a two-term representation avoiding both.
Equivalently, `A \ {u, v}` still pair-covers asymptotically. -/
def TwoRedundantPair (A : Set ℕ) (u v N₂ : ℕ) : Prop :=
  ∀ n, N₂ ≤ n → ∃ s ∈ A, ∃ t ∈ A,
    s + t = n ∧ s ≠ u ∧ s ≠ v ∧ t ≠ u ∧ t ≠ v

/-- **The hugging bound.**  A jointly 2-redundant pair can only destroy
targets below `4 * v + N₀ + 4`: any higher target leaves the larger
covering part of `2 * v + 2` stranded in the double-pin desert.
Contrapositive: an edge with a *clear* target is pair-2-essential —
deleting its two guards must break asymptotic pair-covering. -/
theorem IsPairDestroyer.hugging_of_pairRedundant
    {A : Set ℕ} {N₀ N₂ u v m : ℕ}
    (hcov : PairCovers A N₀)
    (hpair : TwoRedundantPair A u v N₂)
    (hdes : IsPairDestroyer A u v m)
    (huv : u < v) (hN₀ : N₀ ≤ v) (hN₂ : N₂ ≤ v)
    (hbig : 4 * v + N₀ + 4 ≤ m) :
    False := by
  obtain ⟨y, hy, z, hz, hyz⟩ := hcov (2 * v + 2) (by omega)
  have hkill : ∀ w ∈ A, v < w → w ≤ 2 * v + 2 → False := by
    intro w hw hvw hwv
    have hrepu := hpair (u + w) (by omega)
    have hrepv := hpair (v + w) (by omega)
    exact hdes.double_pin_desert hcov huv hw (by omega) (by omega)
      (by omega) hrepu hrepv (by omega)
  rcases Nat.le_total y z with h | h
  · exact hkill z hz (by omega) (by omega)
  · exact hkill y hy (by omega) (by omega)

/-- **Pinned levels compose to a forward translation.**  Two clear
pinned edges of the same 2-redundant guard, the second window wide
enough to catch the first level, translate every good element of the
first window upward by the level gap — the windowed analog of
`IsReflectionLevel.translation`, from destruction alone. -/
theorem pinned_translation {A : Set ℕ} {N₀ N₁ u v₁ m₁ v₂ m₂ : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hred : TwoRedundant A u N₁)
    (hdes₁ : IsPairDestroyer A u v₁ m₁)
    (hdes₂ : IsPairDestroyer A u v₂ m₂)
    (hu0 : 0 < u) (huv₁ : u < v₁)
    (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear₁ : 3 * v₁ ≤ m₁) (hclear₂ : 3 * v₂ ≤ m₂)
    (hwide : m₁ - v₁ + u < v₂)
    {x : ℕ} (hx : x ∈ A) (hxu : x ≠ u) (hwin : u + x < v₁)
    (hdef : m₁ - v₁ - x ≠ u) :
    x + ((m₂ - v₂) - (m₁ - v₁)) ∈ A := by
  have huv₂ : u < v₂ := by omega
  have hy : m₁ - v₁ - x ∈ A :=
    (hdes₁.pinned_level h0 hcov hred hu0 huv₁ hN₀ hN₁ hclear₁).2
      x hx hxu hwin
  have hz : m₂ - v₂ - (m₁ - v₁ - x) ∈ A :=
    (hdes₂.pinned_level h0 hcov hred hu0 huv₂ hN₀ hN₁ hclear₂).2
      (m₁ - v₁ - x) hy hdef (by omega)
  have he : m₂ - v₂ - (m₁ - v₁ - x) = x + ((m₂ - v₂) - (m₁ - v₁)) := by
    omega
  exact he ▸ hz

/-- **Cofinal pinned levels.**  A 2-redundant vertex of an infinite
team clique whose edges admit clear targets (`3 * v ≤ m`) manufactures
element mirror levels cofinally — the raw material of the verified
mirror endgame.  The clearance hypothesis is the new open residue: the
alternative is targets hugging their guards cofinally, a regime with
its own desert structure. -/
theorem cofinal_pinned_levels {A L : Set ℕ} {N₀ N₁ u : ℕ}
    (h0 : 0 ∈ A) (hcov : PairCovers A N₀)
    (hL : L.Infinite)
    (hred : TwoRedundant A u N₁)
    (hu0 : 0 < u) (hN₀ : N₀ ≤ u) (hN₁ : N₁ ≤ u)
    (hclear : ∀ v ∈ L, u < v →
      ∃ m, 3 * v ≤ m ∧ IsPairDestroyer A u v m) :
    ∀ K, ∃ v m, K ≤ v ∧ u < v ∧ 3 * v ≤ m ∧ K ≤ m - v ∧
      m - v ∈ A ∧ ∀ x ∈ A, x ≠ u → u + x < v → m - v - x ∈ A := by
  intro K
  obtain ⟨v, hvL, hv⟩ := hL.exists_gt (max K u)
  have hKv : K < v := lt_of_le_of_lt (le_max_left _ _) hv
  have huv : u < v := lt_of_le_of_lt (le_max_right _ _) hv
  obtain ⟨m, hm, hdes⟩ := hclear v hvL huv
  obtain ⟨hcorep, hmirror⟩ :=
    hdes.pinned_level h0 hcov hred hu0 huv hN₀ hN₁ hm
  exact ⟨v, m, by omega, huv, hm, by omega, hcorep, hmirror⟩

end Erdos881
