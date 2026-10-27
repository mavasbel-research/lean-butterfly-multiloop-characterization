import ButterflyCharacterization.Domain.Model.RelayLoop

/-!
# Finite Preisach operators and the sign of their loops (§II-C, §III)

The Preisach operator (4) integrates relays `R_{α,β}` over the Preisach plane with a weighting
function `μ`. Its finite counterpart is a weighted sum of `n` relays. This file proves for it:

* it is a hysteresis operator (Definition 2.4);
* its loop area is `A = 2 Σ wᵢ (αᵢ − βᵢ)` over the relays that switch (`u_min < βᵢ`,
  `αᵢ < u_max`), the finite form of `A = 2 ∬_{P₁} μ (α − β)` used in the proof of Thm. 3.3;
* §III: with nonnegative weights no loop is clockwise; with nonpositive weights none is
  counterclockwise.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- A finite Preisach operator: relays `R_{αᵢ,βᵢ}` (`αᵢ > βᵢ`) with weights `wᵢ` and initial
states `r₀ᵢ`. -/
structure FinitePreisach (n : ℕ) where
  α : Fin n → ℝ
  β : Fin n → ℝ
  ordered : ∀ i, β i < α i
  w : Fin n → ℝ
  r₀ : Fin n → ℝ

namespace FinitePreisach

variable {n : ℕ} (P : FinitePreisach n)

/-- The relay `i`. -/
noncomputable def relay (i : Fin n) : SignalOperator := ccwRelay (P.α i) (P.β i) (P.r₀ i)

/-- The operator `u ↦ Σᵢ wᵢ R_{αᵢ,βᵢ}(u, r₀ᵢ)`. -/
noncomputable def output : SignalOperator := fun u t => ∑ i, P.w i * P.relay i u t

theorem output_hysteresis : IsHysteresisOperator P.output := by
  refine ⟨fun u₁ u₂ τ h t ht => ?_, fun u φ t ht => ?_⟩
  · exact Finset.sum_congr rfl fun i _ => by rw [relay, ccwRelay_causal u₁ u₂ τ h t ht]
  · exact Finset.sum_congr rfl fun i _ => by rw [relay, ccwRelay_rateIndependent u φ t ht]

/-- The relays that switch under the input: `u_min < βᵢ` and `αᵢ < u_max`. -/
noncomputable def switching (I : SimplePeriodicInput) : Finset (Fin n) := by
  classical exact Finset.univ.filter fun i => I.umin < P.β i ∧ P.α i < I.umax

/-- Loop area of a finite Preisach operator over a period with `t₁ ≥ T`:
`A = 2 Σ_{switching} wᵢ (αᵢ − βᵢ)`. -/
theorem area_of_late (I : SimplePeriodicInput) (hT : I.T ≤ I.t₁) :
    loopArea P.output I = 2 * ∑ i ∈ P.switching I, P.w i * (P.α i - P.β i) := by
  classical
  have hint : ∀ i ∈ Finset.univ, IntervalIntegrable
      (fun τ => P.w i * P.relay i I.u τ * I.u' τ) volume I.t₁ (I.t₁ + I.T) := fun i _ => by
    simpa [mul_assoc, relay] using (relay_integrable (r₀ := P.r₀ i) I (P.ordered i) hT).const_mul (P.w i)
  have hterm : ∀ i, -∫ τ in I.t₁..I.t₁ + I.T, P.w i * P.relay i I.u τ * I.u' τ =
      P.w i * (if I.umin < P.β i ∧ P.α i < I.umax then 2 * (P.α i - P.β i) else 0) := fun i => by
    rw [← lemma3_1 (r₀ := P.r₀ i) I (P.ordered i) hT, signedArea, I.deriv_eq]
    simp only [mul_assoc, intervalIntegral.integral_const_mul, relay]
    ring
  rw [loopArea, signedArea, I.deriv_eq]
  unfold output
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum hint, ← Finset.sum_neg_distrib]
  simp only [hterm, switching, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-! ### Shifting the period -/

/-- The same input with the period `[t₁, t₁ + T]` moved one period later. -/
def _root_.ButterflyCharacterization.Domain.Abstractions.SimplePeriodicInput.shift
    (I : SimplePeriodicInput) : SimplePeriodicInput where
  u := I.u
  u' := I.u'
  T := I.T
  t₁ := I.t₁ + I.T
  t₂ := I.t₂ + I.T
  period_pos := I.period_pos
  periodic := I.periodic
  hasDerivAt := I.hasDerivAt
  continuous_deriv := I.continuous_deriv
  start_nonneg := by linarith [I.start_nonneg, I.period_pos]
  t₁_lt_t₂ := by linarith [I.t₁_lt_t₂]
  t₂_lt := by linarith [I.t₂_lt]
  rising := fun a ha b hb hab => by
    rw [← I.periodic.sub_eq a, ← I.periodic.sub_eq b]
    exact I.rising ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  falling := fun a ha b hb hab => by
    rw [← I.periodic.sub_eq a, ← I.periodic.sub_eq b]
    exact I.falling ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)

theorem deriv_periodic (I : SimplePeriodicInput) (x : ℝ) : I.u' (x + I.T) = I.u' x := by
  have h : HasDerivAt (fun y => I.u (y + I.T)) (I.u' (x + I.T)) x :=
    (I.hasDerivAt (x + I.T)).comp_add_const x I.T
  have hfun : (fun y => I.u (y + I.T)) = I.u := funext I.periodic
  rw [hfun] at h
  exact h.unique (I.hasDerivAt x)

/-- On a hysteresis loop (Definition 2.5), the area does not depend on which period is used. -/
theorem loopArea_shift {Φ : SignalOperator} {I : SimplePeriodicInput} {tp : ℝ}
    (h : IsHysteresisLoop Φ I tp) : loopArea Φ I.shift = loopArea Φ I := by
  have hd : deriv I.u = I.u' := funext fun x => (I.hasDerivAt x).deriv
  simp only [loopArea, signedArea, SimplePeriodicInput.shift, hd]
  congr 1
  rw [← intervalIntegral.integral_comp_add_right (fun τ => Φ I.u τ * I.u' τ) I.T]
  refine intervalIntegral.integral_congr fun τ hτ => ?_
  have hτ' : I.t₁ ≤ τ := by
    rw [uIcc_of_le (by linarith [I.period_pos])] at hτ
    exact hτ.1
  show Φ I.u (τ + I.T) * I.u' (τ + I.T) = Φ I.u τ * I.u' τ
  rw [deriv_periodic, h.2.2.1 τ (h.2.1.trans hτ')]

theorem shift_umin (I : SimplePeriodicInput) : I.shift.umin = I.umin := I.periodic I.t₁
theorem shift_umax (I : SimplePeriodicInput) : I.shift.umax = I.umax := I.periodic I.t₂

/-- Loop area of a finite Preisach operator on any hysteresis loop. -/
theorem area (I : SimplePeriodicInput) {tp : ℝ} (h : IsHysteresisLoop P.output I tp) :
    loopArea P.output I = 2 * ∑ i ∈ P.switching I, P.w i * (P.α i - P.β i) := by
  have hT : I.shift.T ≤ I.shift.t₁ := by
    show I.T ≤ I.t₁ + I.T
    linarith [I.start_nonneg]
  rw [← loopArea_shift h, P.area_of_late I.shift hT]
  simp only [switching, shift_umin, shift_umax]

/-- §III: a finite Preisach operator with nonnegative weights has no clockwise loop. -/
theorem not_clockwise_of_nonneg (hw : ∀ i, 0 ≤ P.w i) : ¬ ExhibitsClockwise P.output := by
  rintro ⟨I, tp, h, hA⟩
  rw [P.area I h] at hA
  have : 0 ≤ ∑ i ∈ P.switching I, P.w i * (P.α i - P.β i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by linarith [P.ordered i])
  linarith

/-- §III: a finite Preisach operator with nonpositive weights has no counterclockwise loop. -/
theorem not_counterclockwise_of_nonpos (hw : ∀ i, P.w i ≤ 0) :
    ¬ ExhibitsCounterclockwise P.output := by
  rintro ⟨I, tp, h, hA⟩
  rw [P.area I h] at hA
  have : ∑ i ∈ P.switching I, P.w i * (P.α i - P.β i) ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (hw i) (by linarith [P.ordered i])
  linarith

end FinitePreisach

end ButterflyCharacterization.Domain.Model
