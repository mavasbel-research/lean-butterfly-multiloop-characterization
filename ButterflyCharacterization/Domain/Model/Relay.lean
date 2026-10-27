import ButterflyCharacterization.Domain.Abstractions.Operator

/-!
# The relay operators, eqs. (2) and (3)

The counterclockwise relay `R_{α,β}` with switching values `α > β` (eq. (2)) in closed form:
the output is `+1` if the input has exceeded `α` and not gone below `β` since, `−1` if it has
gone below `β` and not exceeded `α` since, and the initial value `r₀` otherwise. The theorems
below show that this function satisfies every line of (2) and is a hysteresis operator
(Definition 2.4). The clockwise relay (3) is its negative.
-/

open Set Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- Some time `s ∈ [0, t]` had `P (u s)`, and `Q (u r)` held from `s` to `t`. -/
def Persists (P Q : ℝ → Prop) (u : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ s ∈ Icc 0 t, P (u s) ∧ ∀ r ∈ Icc s t, Q (u r)

/-- The input exceeded `α` and has not gone below `β` since. -/
def SwitchedUp (α β : ℝ) (u : ℝ → ℝ) (t : ℝ) : Prop := Persists (α < ·) (β ≤ ·) u t

/-- The input went below `β` and has not exceeded `α` since. -/
def SwitchedDown (α β : ℝ) (u : ℝ → ℝ) (t : ℝ) : Prop := Persists (· < β) (· ≤ α) u t

open Classical in
/-- **Eq. (2)**, the counterclockwise relay `R_{α,β}(u, r₀)`. -/
noncomputable def ccwRelay (α β r₀ : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  if SwitchedUp α β u t then 1 else if SwitchedDown α β u t then -1 else r₀

variable {α β r₀ : ℝ} {u : ℝ → ℝ} {t : ℝ}

theorem not_up_and_down : ¬ (SwitchedUp α β u t ∧ SwitchedDown α β u t) := by
  rintro ⟨⟨s₁, hs₁, h₁, k₁⟩, ⟨s₂, hs₂, h₂, k₂⟩⟩
  rcases le_total s₁ s₂ with h | h
  · have := k₁ s₂ ⟨h, hs₂.2⟩; linarith
  · have := k₂ s₁ ⟨h, hs₁.2⟩; linarith

/-- First line of (2). -/
theorem ccwRelay_of_gt (hab : β < α) (ht : 0 ≤ t) (hu : α < u t) : ccwRelay α β r₀ u t = 1 := by
  have : SwitchedUp α β u t := ⟨t, ⟨ht, le_rfl⟩, hu, fun r hr => by
    rw [show r = t from le_antisymm hr.2 hr.1]; linarith⟩
  simp [ccwRelay, this]

/-- Second line of (2). -/
theorem ccwRelay_of_lt (hab : β < α) (ht : 0 ≤ t) (hu : u t < β) : ccwRelay α β r₀ u t = -1 := by
  have h1 : ¬ SwitchedUp α β u t := fun ⟨s, hs, _, k⟩ => by
    have := k t ⟨hs.2, le_rfl⟩; linarith
  have h2 : SwitchedDown α β u t := ⟨t, ⟨ht, le_rfl⟩, hu, fun r hr => by
    rw [show r = t from le_antisymm hr.2 hr.1]; linarith⟩
  simp [ccwRelay, h1, h2]

theorem switchedUp_iff_of_band {t₀ : ℝ} (hle : t₀ ≤ t)
    (hband : ∀ r ∈ Icc t₀ t, β ≤ u r ∧ u r ≤ α) :
    SwitchedUp α β u t ↔ SwitchedUp α β u t₀ := by
  constructor
  · rintro ⟨s, hs, hα, k⟩
    have hst : s ≤ t₀ := by
      by_contra h
      have := (hband s ⟨(not_le.mp h).le, hs.2⟩).2; linarith
    exact ⟨s, ⟨hs.1, hst⟩, hα, fun r hr => k r ⟨hr.1, hr.2.trans hle⟩⟩
  · rintro ⟨s, hs, hα, k⟩
    refine ⟨s, ⟨hs.1, hs.2.trans hle⟩, hα, fun r hr => ?_⟩
    rcases le_total r t₀ with h | h
    · exact k r ⟨hr.1, h⟩
    · exact (hband r ⟨h, hr.2⟩).1

theorem switchedDown_iff_of_band {t₀ : ℝ} (hle : t₀ ≤ t)
    (hband : ∀ r ∈ Icc t₀ t, β ≤ u r ∧ u r ≤ α) :
    SwitchedDown α β u t ↔ SwitchedDown α β u t₀ := by
  constructor
  · rintro ⟨s, hs, hβ, k⟩
    have hst : s ≤ t₀ := by
      by_contra h
      have := (hband s ⟨(not_le.mp h).le, hs.2⟩).1; linarith
    exact ⟨s, ⟨hs.1, hst⟩, hβ, fun r hr => k r ⟨hr.1, hr.2.trans hle⟩⟩
  · rintro ⟨s, hs, hβ, k⟩
    refine ⟨s, ⟨hs.1, hs.2.trans hle⟩, hβ, fun r hr => ?_⟩
    rcases le_total r t₀ with h | h
    · exact k r ⟨hr.1, h⟩
    · exact (hband r ⟨h, hr.2⟩).2

/-- Third line of (2), as memory: while the input stays in the band `[β, α]`, the output
does not change. -/
theorem ccwRelay_memory {t₀ : ℝ} (hle : t₀ ≤ t)
    (hband : ∀ r ∈ Icc t₀ t, β ≤ u r ∧ u r ≤ α) :
    ccwRelay α β r₀ u t = ccwRelay α β r₀ u t₀ := by
  have hu := switchedUp_iff_of_band hle hband
  have hd := switchedDown_iff_of_band hle hband
  unfold ccwRelay
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- Fourth line of (2): at `t = 0` in the band, the output is `r₀`. -/
theorem ccwRelay_zero (h : β ≤ u 0 ∧ u 0 ≤ α) : ccwRelay α β r₀ u 0 = r₀ := by
  have hI : ∀ s ∈ Icc (0:ℝ) 0, s = 0 := fun s hs => le_antisymm hs.2 hs.1
  have h1 : ¬ SwitchedUp α β u 0 := fun ⟨s, hs, hα, _⟩ => by
    rw [hI s hs] at hα; linarith [h.2]
  have h2 : ¬ SwitchedDown α β u 0 := fun ⟨s, hs, hβ, _⟩ => by
    rw [hI s hs] at hβ; linarith [h.1]
  simp [ccwRelay, h1, h2]

theorem ccwRelay_causal : IsCausal (ccwRelay α β r₀) := by
  intro u₁ u₂ τ heq t ht
  have e : ∀ r ∈ Icc 0 t, u₁ r = u₂ r := fun r hr => heq r ⟨hr.1, hr.2.trans ht.2⟩
  have hu : SwitchedUp α β u₁ t ↔ SwitchedUp α β u₂ t := by
    constructor <;> rintro ⟨s, hs, h, k⟩
    · refine ⟨s, hs, (e s hs) ▸ h, fun r hr => ?_⟩
      rw [← e r ⟨hs.1.trans hr.1, hr.2⟩]; exact k r hr
    · refine ⟨s, hs, (e s hs).symm ▸ h, fun r hr => ?_⟩
      rw [e r ⟨hs.1.trans hr.1, hr.2⟩]; exact k r hr
  have hd : SwitchedDown α β u₁ t ↔ SwitchedDown α β u₂ t := by
    constructor <;> rintro ⟨s, hs, h, k⟩
    · refine ⟨s, hs, (e s hs) ▸ h, fun r hr => ?_⟩
      rw [← e r ⟨hs.1.trans hr.1, hr.2⟩]; exact k r hr
    · refine ⟨s, hs, (e s hs).symm ▸ h, fun r hr => ?_⟩
      rw [e r ⟨hs.1.trans hr.1, hr.2⟩]; exact k r hr
  unfold ccwRelay
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem _root_.ButterflyCharacterization.Domain.Abstractions.TimeTransformation.nonneg (φ : TimeTransformation) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ φ.toFun t := φ.map_zero ▸ φ.monotoneOn (mem_Ici.mpr le_rfl) ht ht

theorem _root_.ButterflyCharacterization.Domain.Abstractions.TimeTransformation.surjOn (φ : TimeTransformation) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ y ∈ Icc (φ.toFun a) (φ.toFun b), ∃ x ∈ Icc a b, φ.toFun x = y := fun _ hy =>
  intermediate_value_Icc hab (φ.continuousOn.mono fun _ hx => ha.trans hx.1) hy

theorem persists_comp (P Q : ℝ → Prop) (φ : TimeTransformation) {t : ℝ} (ht : 0 ≤ t) :
    Persists P Q (u ∘ φ.toFun) t ↔ Persists P Q u (φ.toFun t) := by
  constructor
  · rintro ⟨s, hs, hP, hQ⟩
    refine ⟨φ.toFun s, ⟨φ.nonneg hs.1, φ.monotoneOn hs.1 ht hs.2⟩, hP, fun y hy => ?_⟩
    obtain ⟨x, hx, rfl⟩ := φ.surjOn hs.1 hs.2 y hy
    exact hQ x hx
  · rintro ⟨s', hs', hP, hQ⟩
    obtain ⟨s, hs, rfl⟩ := φ.surjOn le_rfl ht s' (φ.map_zero.symm ▸ hs')
    refine ⟨s, hs, hP, fun r hr => hQ _ ⟨φ.monotoneOn hs.1 (hs.1.trans hr.1) hr.1,
      φ.monotoneOn (hs.1.trans hr.1) ht hr.2⟩⟩

theorem ccwRelay_rateIndependent : IsRateIndependent (ccwRelay α β r₀) := by
  intro u φ t ht
  have hu := persists_comp (u := u) (α < ·) (β ≤ ·) φ ht
  have hd := persists_comp (u := u) (· < β) (· ≤ α) φ ht
  unfold ccwRelay SwitchedUp SwitchedDown
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The relay is a hysteresis operator (Definition 2.4). -/
theorem ccwRelay_hysteresis : IsHysteresisOperator (ccwRelay α β r₀) :=
  ⟨ccwRelay_causal, ccwRelay_rateIndependent⟩

/-- Third line of (2) as stated: for continuous `u`, in the band at `t > 0` the output equals
its left limit `R(t⁻)` — it is constant on some interval `(t - ε, t)` and equal to `R(t)`. -/
theorem ccwRelay_left_limit (hab : β < α) (hu : ContinuousAt u t) (ht : 0 < t)
    (hband : β ≤ u t ∧ u t ≤ α) :
    ∀ᶠ r in 𝓝[<] t, ccwRelay α β r₀ u r = ccwRelay α β r₀ u t := by
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hu ((α - β) / 2) (by linarith)
  set a := max (t - δ) 0 with ha_def
  have ha : a < t := max_lt (by linarith) ht
  have close : ∀ r ∈ Ioc a t, |u r - u t| < (α - β) / 2 := fun r hr => by
    have h1 : t - δ < r := lt_of_le_of_lt (le_max_left _ _) hr.1
    have := hcont (x := r) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hr.2])
    rwa [Real.dist_eq] at this
  have nonneg : ∀ r, a < r → 0 ≤ r := fun r hr => ((le_max_right _ _).trans_lt hr).le
  by_cases hup : ∃ s ∈ Ioo a t, α < u s
  · obtain ⟨s, hs, hsα⟩ := hup
    have hβ : ∀ r ∈ Ioc a t, β ≤ u r := fun r hr => by
      have h1 := close r hr
      have h2 := close s ⟨hs.1, hs.2.le⟩
      rw [abs_lt] at h1 h2
      linarith
    have key : ∀ r ∈ Icc s t, ccwRelay α β r₀ u r = 1 := fun r hr => by
      have : SwitchedUp α β u r := ⟨s, ⟨nonneg s hs.1, hr.1⟩, hsα,
        fun q hq => hβ q ⟨hs.1.trans_le hq.1, hq.2.trans hr.2⟩⟩
      simp [ccwRelay, this]
    filter_upwards [Ioo_mem_nhdsLT hs.2] with r hr
    rw [key r ⟨hr.1.le, hr.2.le⟩, key t ⟨hs.2.le, le_rfl⟩]
  · by_cases hdn : ∃ s ∈ Ioo a t, u s < β
    · obtain ⟨s, hs, hsβ⟩ := hdn
      have hα : ∀ r ∈ Ioc a t, u r ≤ α := fun r hr => by
        have h1 := close r hr
        have h2 := close s ⟨hs.1, hs.2.le⟩
        rw [abs_lt] at h1 h2
        linarith
      have key : ∀ r ∈ Icc s t, ccwRelay α β r₀ u r = -1 := fun r hr => by
        have hd : SwitchedDown α β u r := ⟨s, ⟨nonneg s hs.1, hr.1⟩, hsβ,
          fun q hq => hα q ⟨hs.1.trans_le hq.1, hq.2.trans hr.2⟩⟩
        have hn : ¬ SwitchedUp α β u r := fun h => not_up_and_down ⟨h, hd⟩
        simp [ccwRelay, hd, hn]
      filter_upwards [Ioo_mem_nhdsLT hs.2] with r hr
      rw [key r ⟨hr.1.le, hr.2.le⟩, key t ⟨hs.2.le, le_rfl⟩]
    · simp only [not_exists, not_and, not_lt] at hup hdn
      filter_upwards [Ioo_mem_nhdsLT ha] with r hr
      refine (ccwRelay_memory hr.2.le fun q hq => ?_).symm
      rcases hq.2.lt_or_eq with h | h
      · exact ⟨hdn q ⟨hr.1.trans_le hq.1, h⟩, hup q ⟨hr.1.trans_le hq.1, h⟩⟩
      · exact h ▸ hband

/-- **Eq. (3)**, the clockwise relay: `R̃_{α,β}(u, r₀) = −R_{α,β}(u, r₀)` (§II-B). -/
noncomputable def cwRelay (α β r₀ : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ := -ccwRelay α β r₀ u t

theorem ccwRelay_values (hr₀ : r₀ = 1 ∨ r₀ = -1) : ccwRelay α β r₀ u t = 1 ∨ ccwRelay α β r₀ u t = -1 := by
  unfold ccwRelay
  split_ifs <;> simp_all

/-! ### Forgetting the past, and periodicity -/

/-- `Persists`, restricted to witnesses after `c`. -/
def PersistsFrom (c : ℝ) (P Q : ℝ → Prop) (u : ℝ → ℝ) (t : ℝ) : Prop :=
  ∃ s ∈ Icc c t, P (u s) ∧ ∀ r ∈ Icc s t, Q (u r)

/-- After a time `c` with `u c < β`, only switch-ups after `c` count. -/
theorem switchedUp_iff_from {c : ℝ} (hc : 0 ≤ c) (hct : c ≤ t) (huc : u c < β) :
    SwitchedUp α β u t ↔ PersistsFrom c (α < ·) (β ≤ ·) u t := by
  constructor
  · rintro ⟨s, hs, hP, hQ⟩
    refine ⟨s, ⟨?_, hs.2⟩, hP, hQ⟩
    by_contra h
    have := hQ c ⟨(not_le.mp h).le, hct⟩
    exact absurd huc (not_lt.mpr this)
  · rintro ⟨s, hs, hP, hQ⟩
    exact ⟨s, ⟨hc.trans hs.1, hs.2⟩, hP, hQ⟩

/-- After a time `c` with `u c < β`, a switch-down may be taken after `c`. -/
theorem switchedDown_iff_from {c : ℝ} (hc : 0 ≤ c) (hct : c ≤ t) (huc : u c < β) :
    SwitchedDown α β u t ↔ PersistsFrom c (· < β) (· ≤ α) u t := by
  constructor
  · rintro ⟨s, hs, hP, hQ⟩
    rcases le_total c s with h | h
    · exact ⟨s, ⟨h, hs.2⟩, hP, hQ⟩
    · exact ⟨c, ⟨le_rfl, hct⟩, huc, fun r hr => hQ r ⟨h.trans hr.1, hr.2⟩⟩
  · rintro ⟨s, hs, hP, hQ⟩
    exact ⟨s, ⟨hc.trans hs.1, hs.2⟩, hP, hQ⟩

theorem persistsFrom_shift {T c : ℝ} (P Q : ℝ → Prop) (hu : Function.Periodic u T) :
    PersistsFrom (c + T) P Q u (t + T) ↔ PersistsFrom c P Q u t := by
  constructor
  · rintro ⟨s, hs, hP, hQ⟩
    refine ⟨s - T, ⟨by linarith [hs.1], by linarith [hs.2]⟩, by rwa [hu.sub_eq], fun r hr => ?_⟩
    rw [← hu r]
    exact hQ (r + T) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  · rintro ⟨s, hs, hP, hQ⟩
    refine ⟨s + T, ⟨by linarith [hs.1], by linarith [hs.2]⟩, by rwa [hu s], fun r hr => ?_⟩
    rw [← hu.sub_eq r]
    exact hQ (r - T) ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- For a `T`-periodic input, once the input has been below `β` (at `c`), the relay output
is `T`-periodic. -/
theorem ccwRelay_periodic {T c : ℝ} (hT : 0 ≤ T) (hu : Function.Periodic u T) (hc : 0 ≤ c)
    (huc : u c < β) (hct : c ≤ t) : ccwRelay α β r₀ u (t + T) = ccwRelay α β r₀ u t := by
  have huc' : u (c + T) < β := by rwa [hu c]
  have hU : SwitchedUp α β u (t + T) ↔ SwitchedUp α β u t := by
    rw [switchedUp_iff_from (by linarith) (by linarith) huc', persistsFrom_shift _ _ hu,
      ← switchedUp_iff_from hc hct huc]
  have hD : SwitchedDown α β u (t + T) ↔ SwitchedDown α β u t := by
    rw [switchedDown_iff_from (by linarith) (by linarith) huc', persistsFrom_shift _ _ hu,
      ← switchedDown_iff_from hc hct huc]
  unfold ccwRelay
  split_ifs <;> first | rfl | (exfalso; tauto)

end ButterflyCharacterization.Domain.Model
