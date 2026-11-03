import ButterflyCharacterization.Domain.Model.Corollary34
import ButterflyCharacterization.Domain.Model.IntegralMultiloop

/-!
# A non-vacuity witness for integral Theorem 4.7

The antisymmetric integral witness from `Corollary34.lean` has a positive rectangle
`Qplus = (0, 1) × (-1, 0)` and its negative reflection `Qminus = (1, 2) × (0, 1)`.
For input extremes `[-1, 2]`, its switching-band integral is `1/2` at `-1/2`, zero at
`1/2`, and `-1/2` at `3/2`. It therefore satisfies the three local hypotheses of the integral
Theorem 4.7.
-/

open Set MeasureTheory
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-! ### Switching-band calculations -/

/-- The part of `Qplus` that switches at level `-1/2`. -/
def QplusLow : Set (ℝ × ℝ) := Ioo 0 1 ×ˢ Ioc (-1) (-1 / 2)

theorem measurableSet_QplusLow : MeasurableSet QplusLow := measurableSet_Ioo.prod measurableSet_Ioc

/-- The integral switching-band weight at `-1/2` is the area of `QplusLow`. -/
theorem antisymWitness_omega_low : antisymWitness.omegaWeight (-1) 2 (-1 / 2) = 1 / 2 := by
  classical
  have hLow : QplusLow ⊆ Qplus := by
    rintro ⟨a, b⟩ h
    simp only [QplusLow, Qplus, mem_prod, mem_Ioo, mem_Ioc] at h ⊢
    rcases h with ⟨ha, hb, hle⟩
    exact ⟨ha, hb, by linarith⟩
  have e : ∀ p : ℝ × ℝ, antisymWitness.μ p * omegaInd (-1) 2 (-1 / 2) p =
      QplusLow.indicator 1 p := fun ⟨a, b⟩ => by
    by_cases hp : (a, b) ∈ Qplus
    · have hm : (a, b) ∉ Qminus := fun h => by
        simp only [Qplus, Qminus, mem_prod, mem_Ioo] at hp h
        linarith [hp.2.2, h.2.1]
      simp only [Qplus, mem_prod, mem_Ioo] at hp
      by_cases hb : b ≤ -1 / 2
      · have hΩ : -1 < b ∧ a < 2 ∧ b ≤ -1 / 2 ∧ -1 / 2 ≤ a :=
          ⟨by linarith [hp.2.1], by linarith [hp.1.2], hb, by linarith [hp.1.1]⟩
        have hR : (a, b) ∈ QplusLow := ⟨hp.1, by simpa using ⟨hp.2.1, hb⟩⟩
        have hQ : (a, b) ∈ Qplus := by simpa [Qplus] using hp
        simp [antisymWitness, witnessMu, omegaInd, hΩ, indicator_of_notMem hm,
          indicator_of_mem hQ, hR]
      · have hΩ : ¬ (-1 < b ∧ a < 2 ∧ b ≤ -1 / 2 ∧ -1 / 2 ≤ a) := by
          rintro ⟨-, -, hbeta, -⟩
          exact hb hbeta
        have hR : (a, b) ∉ QplusLow := fun h => hb ((show b ∈ Ioc (-1) (-1 / 2) from h.2).2)
        simp [antisymWitness, witnessMu, omegaInd, hΩ, indicator_of_notMem hm, hR]
    · by_cases hm : (a, b) ∈ Qminus
      · simp only [Qminus, mem_prod, mem_Ioo] at hm
        have hΩ : ¬ (-1 < b ∧ a < 2 ∧ b ≤ -1 / 2 ∧ -1 / 2 ≤ a) := fun h => by
          linarith [h.2.1, hm.2.1]
        have hR : (a, b) ∉ QplusLow := fun h => hp (hLow h)
        simp [antisymWitness, witnessMu, omegaInd, hΩ, indicator_of_notMem hp, hR]
      · have hR : (a, b) ∉ QplusLow := fun h => hp (hLow h)
        simp [antisymWitness, witnessMu, indicator_of_notMem hp, indicator_of_notMem hm, hR]
  rw [IntegralPreisach.omegaWeight, integral_congr_ae (ae_of_all _ e),
    integral_indicator_one measurableSet_QplusLow, measureReal_def, QplusLow,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioc]
  norm_num

/-- Reflection about `α + β = 1` maps the switching band at `υ` to the band at `1 - υ`. -/
theorem omegaInd_refl (υ : ℝ) (p : ℝ × ℝ) :
    omegaInd (-1) 2 (1 - υ) (refl 1 p) = omegaInd (-1) 2 υ p := by
  have h :
      (-1 < 1 - p.1 ∧ 1 - p.2 < 2 ∧ 1 - p.1 ≤ 1 - υ ∧ 1 - υ ≤ 1 - p.2) ↔
        (-1 < p.2 ∧ p.1 < 2 ∧ p.2 ≤ υ ∧ υ ≤ p.1) := by
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  simp only [omegaInd, refl, h]

/-- The reflection changes the sign of the switching-band integral. -/
theorem antisymWitness_omega_refl (υ : ℝ) :
    antisymWitness.omegaWeight (-1) 2 (1 - υ) = -antisymWitness.omegaWeight (-1) 2 υ := by
  rw [IntegralPreisach.omegaWeight, IntegralPreisach.omegaWeight, ← integral_neg]
  conv_lhs => rw [← integral_comp_refl 1]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  change witnessMu (refl 1 p) * omegaInd (-1) 2 (1 - υ) (refl 1 p) =
    -(witnessMu p * omegaInd (-1) 2 υ p)
  rw [witnessMu_refl, omegaInd_refl]
  ring

/-- The central switching-band integral is zero by antisymmetry. -/
theorem antisymWitness_omega_mid : antisymWitness.omegaWeight (-1) 2 (1 / 2) = 0 := by
  have h := antisymWitness_omega_refl (1 / 2)
  norm_num at h ⊢
  linarith

/-- The switching-band integral at `3/2` is the negative reflection of the value at `-1/2`. -/
theorem antisymWitness_omega_high : antisymWitness.omegaWeight (-1) 2 (3 / 2) = -1 / 2 := by
  have h := antisymWitness_omega_refl (-1 / 2)
  rw [antisymWitness_omega_low] at h
  norm_num at h ⊢
  linarith

/-- The integral Preisach witness satisfies all hypotheses of Theorem 4.7. -/
theorem antisymWitness_isMultiloop : IsMultiloopOperator antisymWitness.output := by
  refine antisymWitness.theorem4_7 (β₀ := -1) (aLo := -1 / 2) (a₁ := 1 / 2)
    (aHi := 3 / 2) (α₀ := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_
  · exact antisymWitness_omega_mid
  · rw [antisymWitness_omega_low]
    norm_num
  · rw [antisymWitness_omega_high]
    norm_num

end ButterflyCharacterization.Domain.Model
