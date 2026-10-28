import ButterflyCharacterization.Domain.Model.Theorem33

/-!
# Corollary 3.4 for the Preisach operator (4)

The reflection about `B = {α + β = κ}` that maps the Preisach plane to itself is
`refl κ (α, β) = (κ − β, κ − α)`. It preserves Lebesgue measure on `ℝ²`.

* `corollary3_4`: if `μ ∘ refl κ = −μ`, every hysteresis loop with `u_min + u_max = κ` has
  zero area;
* `antisymWitness`: `μ = 𝟙_{(0,1)×(−1,0)} − 𝟙_{(1,2)×(0,1)}` is antisymmetric about
  `α + β = 1`, and with the input `[−1, 2]` it is a butterfly hysteresis operator.
-/

open Set MeasureTheory
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- Reflection about `α + β = κ`. -/
def refl (κ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (κ - p.2, κ - p.1)

theorem refl_eq (κ : ℝ) (p : ℝ × ℝ) : refl κ p = (κ, κ) - p.swap := rfl

/-- The reflection preserves the integral. -/
theorem integral_comp_refl (κ : ℝ) (g : ℝ × ℝ → ℝ) : ∫ p, g (refl κ p) = ∫ p, g p := by
  have h1 : ∫ p, g (refl κ p) = ∫ p : ℝ × ℝ, (fun z => g ((κ, κ) - z)) p.swap := rfl
  rw [h1, Measure.volume_eq_prod, integral_prod_swap (fun z => g ((κ, κ) - z)),
    ← Measure.volume_eq_prod, integral_sub_left_eq_self g volume (κ, κ)]

theorem switchArea_refl {m M κ : ℝ} (h : m + M = κ) (p : ℝ × ℝ) :
    IntegralPreisach.switchArea m M (refl κ p) = IntegralPreisach.switchArea m M p := by
  have hc : (m < κ - p.1 ∧ κ - p.2 < M) ↔ (m < p.2 ∧ p.1 < M) :=
    ⟨fun h1 => ⟨by linarith [h1.2], by linarith [h1.1]⟩,
      fun h1 => ⟨by linarith [h1.2], by linarith [h1.1]⟩⟩
  simp only [IntegralPreisach.switchArea, refl, hc]
  split_ifs <;> ring

namespace IntegralPreisach

variable (P : IntegralPreisach)

/-- **Corollary 3.4** (Preisach operator (4)). If `μ` is antisymmetric with respect to
`α + β = κ` and the loop's extremes satisfy `u_min + u_max = κ`, its signed area is zero. -/
theorem corollary3_4 (κ : ℝ) (hμ : ∀ p, P.μ (refl κ p) = -P.μ p) {I : SimplePeriodicInput}
    {tp : ℝ} (h : IsHysteresisLoop P.output I tp) (hκ : I.umin + I.umax = κ) :
    loopArea P.output I = 0 := by
  rw [P.area h, areaOf]
  set A := ∫ p, P.μ p * switchArea I.umin I.umax p
  have : A = -A := by
    conv_lhs => rw [show A = ∫ p, P.μ p * switchArea I.umin I.umax p from rfl,
      ← integral_comp_refl κ]
    rw [← integral_neg]
    exact integral_congr_ae (ae_of_all _ fun p => by
      simp only [hμ, switchArea_refl hκ]; ring)
  linarith

end IntegralPreisach

/-! ### A witness -/

/-- `Q₊ = (0, 1) × (−1, 0)`. -/
def Qplus : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioo (-1) 0

/-- `Q₋ = (1, 2) × (0, 1)`, the reflection of `Q₊` about `α + β = 1`. -/
def Qminus : Set (ℝ × ℝ) := Ioo 1 2 ×ˢ Ioo 0 1

theorem refl_mem_Qplus (p : ℝ × ℝ) : refl 1 p ∈ Qplus ↔ p ∈ Qminus := by
  simp only [refl, Qplus, Qminus, mem_prod, mem_Ioo]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem refl_mem_Qminus (p : ℝ × ℝ) : refl 1 p ∈ Qminus ↔ p ∈ Qplus := by
  simp only [refl, Qplus, Qminus, mem_prod, mem_Ioo]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem measurableSet_Qplus : MeasurableSet Qplus := measurableSet_Ioo.prod measurableSet_Ioo
theorem measurableSet_Qminus : MeasurableSet Qminus := measurableSet_Ioo.prod measurableSet_Ioo

theorem volume_box_ne_top (a b c d : ℝ) : volume (Ioo a b ×ˢ Ioo c d) ≠ ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The weight `𝟙_{Q₊} − 𝟙_{Q₋}`. -/
noncomputable def witnessMu (p : ℝ × ℝ) : ℝ := Qplus.indicator 1 p - Qminus.indicator 1 p

theorem witnessMu_refl (p : ℝ × ℝ) : witnessMu (refl 1 p) = -witnessMu p := by
  classical
  simp only [witnessMu, indicator_apply, refl_mem_Qplus, refl_mem_Qminus, Pi.one_apply]
  ring

theorem integrable_box (a b c d : ℝ) :
    Integrable ((Ioo a b ×ˢ Ioo c d).indicator (1 : ℝ × ℝ → ℝ)) :=
  (integrable_indicator_iff (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
    (integrableOn_const (volume_box_ne_top a b c d))

/-- The Preisach operator with weight `𝟙_{Q₊} − 𝟙_{Q₋}` and all relays initially `−1`. -/
noncomputable def antisymWitness : IntegralPreisach where
  μ := witnessMu
  integrable := (integrable_box 0 1 (-1) 0).sub (integrable_box 1 2 0 1)
  vanishes_off p hp := by
    have h1 : p ∉ Qplus := fun h => by
      simp only [Qplus, mem_prod, mem_Ioo] at h; linarith [h.1.1, h.2.2]
    have h2 : p ∉ Qminus := fun h => by
      simp only [Qminus, mem_prod, mem_Ioo] at h; linarith [h.1.1, h.2.2]
    simp [witnessMu, indicator_of_notMem h1, indicator_of_notMem h2]
  r₀ := fun _ => -1
  r₀_measurable := measurable_const
  r₀_bound _ := by norm_num

/-- At level `υ = 0` under the input `[−1, 2]`, `Ω_0 ∩ supp μ = Q₊`, so `∬_{Ω_0} μ = 1`. -/
theorem antisymWitness_omega : antisymWitness.omegaWeight (-1) 2 0 = 1 := by
  classical
  have e : ∀ p : ℝ × ℝ, antisymWitness.μ p * omegaInd (-1) 2 0 p = Qplus.indicator 1 p :=
    fun ⟨a, b⟩ => by
      by_cases hp : (a, b) ∈ Qplus
      · have hm : (a, b) ∉ Qminus := fun h => by
          simp only [Qplus, Qminus, mem_prod, mem_Ioo] at hp h; linarith [hp.2.2, h.2.1]
        simp only [Qplus, mem_prod, mem_Ioo] at hp
        have hΩ : -1 < b ∧ a < 2 ∧ b ≤ 0 ∧ 0 ≤ a :=
          ⟨hp.2.1, by linarith [hp.1.2], hp.2.2.le, hp.1.1.le⟩
        simp [antisymWitness, witnessMu, omegaInd, hΩ, indicator_of_notMem hm, Qplus, hp]
      · by_cases hm : (a, b) ∈ Qminus
        · simp only [Qminus, mem_prod, mem_Ioo] at hm
          have hΩ : ¬ (-1 < b ∧ a < 2 ∧ b ≤ 0 ∧ 0 ≤ a) := fun h => by linarith [h.2.2.1, hm.2.1]
          simp [omegaInd, hΩ, indicator_of_notMem hp]
        · simp [antisymWitness, witnessMu, indicator_of_notMem hp, indicator_of_notMem hm]
  rw [IntegralPreisach.omegaWeight, integral_congr_ae (ae_of_all _ e),
    integral_indicator_one measurableSet_Qplus, measureReal_def, Qplus,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  norm_num

/-- The antisymmetric witness is a butterfly hysteresis operator (Corollary 3.4 at work). -/
theorem antisymWitness_isButterfly : IsButterflyOperator antisymWitness.output := by
  have h : (-1 : ℝ) < 2 := by norm_num
  obtain ⟨hl, -⟩ := antisymWitness.cosine_loop h (υ := 0) (by norm_num)
    (by rw [antisymWitness_omega]; norm_num)
  refine ⟨antisymWitness.output_hysteresis, _, _, hl, ?_⟩
  exact antisymWitness.corollary3_4 1 witnessMu_refl hl
    (by rw [cosineInput_umin, cosineInput_umax]; norm_num)

end ButterflyCharacterization.Domain.Model
