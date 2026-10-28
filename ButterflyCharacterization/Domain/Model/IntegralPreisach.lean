import ButterflyCharacterization.Domain.Model.Branches

/-!
# The Preisach operator (4)

`[P(u, L₀)](t) = ∬_P μ(α, β) [R_{α,β}(u, r_{α,β}(L₀))](t) dα dβ`

with `P = {(α, β) | α > β}`. A point of `ℝ × ℝ` is `(α, β)`; the weight `μ` is Lebesgue
integrable and vanishes off `P`; the initial relay states `r₀(α, β) ∈ [−1, 1]` depend
measurably on `(α, β)` (the paper's interface `L₀` fixes them; for the output on a period with
`T ≤ t₁` only the relays that never switch remember them).

Proved here:

* `output_hysteresis`: `P` is a hysteresis operator (Definition 2.4);
* `relay_eq_closed`: every relay over a period with `T ≤ t₁` has a closed form that is
  jointly measurable in `((α, β), t)` (`measurable_closed`);
* `area`: on any hysteresis loop, `A = ∬ μ(α, β) · 2(α − β)` over the switching relays
  `u_min < β`, `α < u_max` — the formula `A = 2 ∬_{P₁} μ (α − β)` of the proof of Thm. 3.3,
  obtained by Fubini from Lemma 3.1.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- The Preisach operator (4): weight `μ`, initial states `r₀`. -/
structure IntegralPreisach where
  μ : ℝ × ℝ → ℝ
  integrable : Integrable μ
  vanishes_off : ∀ p : ℝ × ℝ, p.1 ≤ p.2 → μ p = 0
  r₀ : ℝ × ℝ → ℝ
  r₀_measurable : Measurable r₀
  r₀_bound : ∀ p, |r₀ p| ≤ 1

namespace IntegralPreisach

variable (P : IntegralPreisach)

/-- Eq. (4). -/
noncomputable def output : SignalOperator :=
  fun u t => ∫ p, P.μ p * ccwRelay p.1 p.2 (P.r₀ p) u t

theorem output_hysteresis : IsHysteresisOperator P.output := by
  refine ⟨fun u₁ u₂ τ h t ht => ?_, fun u φ t ht => ?_⟩
  · exact integral_congr_ae (ae_of_all _ fun p => by
      simp only [ccwRelay_causal u₁ u₂ τ h t ht])
  · exact integral_congr_ae (ae_of_all _ fun p => by
      simp only [ccwRelay_rateIndependent u φ t ht])

/-- Integrand of the loop area of one relay: `2(α − β)` if it switches, else `0`. -/
noncomputable def switchArea (m M : ℝ) (p : ℝ × ℝ) : ℝ :=
  if m < p.2 ∧ p.1 < M then 2 * (p.1 - p.2) else 0

/-- `∬ μ(α, β) · 2(α − β)` over the relays that switch between `m` and `M`. -/
noncomputable def areaOf (m M : ℝ) : ℝ := ∫ p, P.μ p * switchArea m M p

end IntegralPreisach

/-! ### Closed form of a relay over a period -/

variable (I : SimplePeriodicInput)

/-- The relay output over `[t₁, t₁ + T]` (for `T ≤ t₁`): `relayUp` before `t₂`, `relayDown`
after, with the frozen value of a never-switching relay replaced by its initial state. -/
noncomputable def relayClosed (α β r t : ℝ) : ℝ :=
  if t ≤ I.t₂ then
    (if α < I.u t then 1 else if I.umin < β then -1 else if α < I.umax then 1 else r)
  else
    (if I.u t < β then -1 else if α < I.umax then 1 else if I.umin < β then -1 else r)

variable {I}

theorem relay_eq_closed {α β r t : ℝ} (hab : β < α) (hT : I.T ≤ I.t₁)
    (ht : t ∈ Icc I.t₁ (I.t₁ + I.T)) : ccwRelay α β r I.u t = relayClosed I α β r t := by
  have hz : ¬ I.umin < β → ¬ α < I.umax → ccwRelay α β r I.u 0 = r := fun h1 h2 =>
    ccwRelay_zero ⟨(not_lt.mp h1).trans (I.bounds 0).1, (I.bounds 0).2.trans (not_lt.mp h2)⟩
  unfold relayClosed
  by_cases h : t ≤ I.t₂
  · rw [ite_eq_left h, relay_rising hab hT ⟨ht.1, h⟩]
    unfold relayUp
    split_ifs <;> first | rfl | exact hz (by assumption) (by assumption)
  · rw [ite_eq_right h, relay_falling hab ⟨(not_le.mp h).le, ht.2⟩]
    unfold relayDown
    split_ifs <;> first | rfl | exact hz (by assumption) (by assumption)

theorem abs_relayClosed_le {α β r t : ℝ} (hr : |r| ≤ 1) : |relayClosed I α β r t| ≤ 1 := by
  unfold relayClosed
  split_ifs <;> first | exact hr | norm_num

theorem measurable_closed (P : IntegralPreisach) :
    Measurable fun z : ℝ × (ℝ × ℝ) => relayClosed I z.2.1 z.2.2 (P.r₀ z.2) z.1 := by
  have mu : Measurable fun z : ℝ × (ℝ × ℝ) => I.u z.1 := I.continuous.measurable.comp measurable_fst
  have ma : Measurable fun z : ℝ × (ℝ × ℝ) => z.2.1 := measurable_snd.fst
  have mb : Measurable fun z : ℝ × (ℝ × ℝ) => z.2.2 := measurable_snd.snd
  have mr : Measurable fun z : ℝ × (ℝ × ℝ) => P.r₀ z.2 := P.r₀_measurable.comp measurable_snd
  have c1 := measurableSet_lt (f := fun _ : ℝ × (ℝ × ℝ) => I.umin) measurable_const mb
  have c2 := measurableSet_lt (g := fun _ : ℝ × (ℝ × ℝ) => I.umax) ma measurable_const
  unfold relayClosed
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ ?_
  · exact Measurable.ite (measurableSet_lt ma mu) measurable_const
      (Measurable.ite c1 measurable_const (Measurable.ite c2 measurable_const mr))
  · exact Measurable.ite (measurableSet_lt mu mb) measurable_const
      (Measurable.ite c2 measurable_const (Measurable.ite c1 measurable_const mr))

/-- One relay's time integral over the period, from Lemma 3.1. -/
theorem integral_closed {α β r : ℝ} (hab : β < α) (hT : I.T ≤ I.t₁) :
    ∫ t in Ioc I.t₁ (I.t₁ + I.T), relayClosed I α β r t * I.u' t =
      -(if I.umin < β ∧ α < I.umax then 2 * (α - β) else 0) := by
  have hle : I.t₁ ≤ I.t₁ + I.T := by linarith [I.period_pos]
  rw [← lemma3_1 (r₀ := r) I hab hT, signedArea, I.deriv_eq, neg_neg,
    ← intervalIntegral.integral_of_le hle]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hle] at ht
  simp only [relay_eq_closed hab hT ht]

namespace IntegralPreisach

variable (P : IntegralPreisach)

/-- The loop area over a period with `T ≤ t₁`. -/
theorem area_of_late (hT : I.T ≤ I.t₁) : loopArea P.output I = P.areaOf I.umin I.umax := by
  have hle : I.t₁ ≤ I.t₁ + I.T := by linarith [I.period_pos]
  set S := Ioc I.t₁ (I.t₁ + I.T)
  set f : ℝ → ℝ × ℝ → ℝ := fun t p => I.u' t * P.μ p * relayClosed I p.1 p.2 (P.r₀ p) t
  -- the relays agree with the closed form, the weight vanishes off the Preisach plane
  have hpt : ∀ t ∈ S, ∀ p : ℝ × ℝ,
      P.μ p * ccwRelay p.1 p.2 (P.r₀ p) I.u t * I.u' t = f t p := fun t ht p => by
    by_cases hp : p.2 < p.1
    · simp only [f, relay_eq_closed hp hT (Ioc_subset_Icc_self ht)]; ring
    · simp only [f, P.vanishes_off p (not_lt.mp hp)]; ring
  -- integrability on the product
  have hu' : Integrable I.u' (volume.restrict S) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp (I.continuous_deriv.intervalIntegrable _ _)
  have hg := hu'.mul_prod P.integrable
  have hf : Integrable (Function.uncurry f) ((volume.restrict S).prod volume) := by
    refine hg.mono ?_ (ae_of_all _ fun z => ?_)
    · exact hg.aestronglyMeasurable.mul (measurable_closed (I := I) P).aestronglyMeasurable
    · simp only [Function.uncurry, f, norm_mul, Real.norm_eq_abs]
      have := abs_relayClosed_le (I := I) (α := z.2.1) (β := z.2.2) (t := z.1) (P.r₀_bound z.2)
      nlinarith [abs_nonneg (I.u' z.1), abs_nonneg (P.μ z.2),
        mul_nonneg (abs_nonneg (I.u' z.1)) (abs_nonneg (P.μ z.2))]
  rw [loopArea, signedArea, I.deriv_eq, intervalIntegral.integral_of_le hle]
  have step1 : ∫ t in S, P.output I.u t * I.u' t = ∫ t in S, ∫ p, f t p :=
    setIntegral_congr_fun measurableSet_Ioc fun t ht => by
      simp only [output]
      rw [← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun p => hpt t ht p)
  rw [step1, integral_integral_swap hf, areaOf, ← integral_neg]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  show -∫ t in S, I.u' t * P.μ p * relayClosed I p.1 p.2 (P.r₀ p) t = P.μ p * switchArea I.umin I.umax p
  by_cases hp : p.2 < p.1
  · have e : ∀ t, I.u' t * P.μ p * relayClosed I p.1 p.2 (P.r₀ p) t =
        P.μ p * (relayClosed I p.1 p.2 (P.r₀ p) t * I.u' t) := fun t => by ring
    simp only [e, integral_const_mul]
    rw [show S = Ioc I.t₁ (I.t₁ + I.T) from rfl, integral_closed hp hT, switchArea]
    split_ifs <;> ring
  · simp only [P.vanishes_off p (not_lt.mp hp)]
    simp

/-- **Area of a Preisach loop.** On any hysteresis loop of the Preisach operator (4),
`A = ∬ μ(α, β) · 2(α − β)` over the relays with `u_min < β` and `α < u_max`. -/
theorem area {tp : ℝ} (h : IsHysteresisLoop P.output I tp) :
    loopArea P.output I = P.areaOf I.umin I.umax := by
  have hT : I.shift.T ≤ I.shift.t₁ := by
    show I.T ≤ I.t₁ + I.T
    linarith [I.start_nonneg]
  rw [← FinitePreisach.loopArea_shift h, P.area_of_late hT, FinitePreisach.shift_umin,
    FinitePreisach.shift_umax]

end IntegralPreisach

end ButterflyCharacterization.Domain.Model
