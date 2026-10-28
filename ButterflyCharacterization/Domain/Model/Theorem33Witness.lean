import ButterflyCharacterization.Domain.Model.Theorem33Moments
import ButterflyCharacterization.Domain.Model.Corollary34

/-!
# A weight satisfying every hypothesis of `theorem3_3_moments`

With `β₁ = 0`, `α₁ = 1`, `s = 1`:

* `f₊(α, β) = α⁻² · 𝟙{α > 1} · 𝟙{1/2 < β < 1}` (positive, integrable, but
  `∬ f₊ (α − β) = ∞`: the upper partial moment (5) is unbounded);
* `f₋ = f₊ ∘ refl 1` (its mirror about `α + β = 1`, in `{β < 0, α < 1/2}`);
* a bump `𝟙_{Q₀}`, `Q₀ = (5/8, 7/8) × (1/8, 3/8)`, inside the triangle `{0 < β, α < 1}`, so
  that every input range `[m, M] ⊇ [0, 1]` gives a loop (`∬_{Ω_{1/2}} μ = area Q₀ ≠ 0`);

`μ = f₊ − f₋ + 𝟙_{Q₀}` is `≥ 0` on `{β > 0, α ≥ 1}`, `≤ 0` on `{β ≤ 0, α < 1}`, and
`μ (α − β)` is not integrable on either region. `butterflyWitness_isButterfly` applies
`theorem3_3_moments`.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- Integrability is preserved by the reflection about `α + β = κ`. -/
theorem integrable_comp_refl {h : ℝ × ℝ → ℝ} (hh : Integrable h) (κ : ℝ) :
    Integrable fun p => h (refl κ p) := by
  have h1 : Integrable (fun z : ℝ × ℝ => h ((κ, κ) - z)) := hh.comp_sub_left (κ, κ)
  rw [Measure.volume_eq_prod] at h1 ⊢
  exact h1.swap

/-- `α⁻² 𝟙{α > 1}`. -/
noncomputable def tailA (a : ℝ) : ℝ := (Ioi 1).indicator (fun x : ℝ => x ^ (-2 : ℝ)) a

/-- `𝟙{1/2 < β < 1}`. -/
noncomputable def stripB (b : ℝ) : ℝ := (Ioo (1 / 2) 1).indicator (fun _ => (1 : ℝ)) b

/-- `f₊(α, β) = α⁻² 𝟙{α > 1} 𝟙{1/2 < β < 1}`. -/
noncomputable def fPlus (p : ℝ × ℝ) : ℝ := tailA p.1 * stripB p.2

theorem tailA_nonneg (a : ℝ) : 0 ≤ tailA a := by
  unfold tailA indicator; split_ifs with h
  · exact Real.rpow_nonneg (le_of_lt (lt_trans one_pos h)) _
  · exact le_rfl

theorem stripB_nonneg (b : ℝ) : 0 ≤ stripB b := by
  unfold stripB indicator; split_ifs <;> norm_num

theorem fPlus_nonneg (p : ℝ × ℝ) : 0 ≤ fPlus p := mul_nonneg (tailA_nonneg _) (stripB_nonneg _)

theorem fPlus_eq_zero {p : ℝ × ℝ} (h : ¬ (1 < p.1 ∧ 1 / 2 < p.2 ∧ p.2 < 1)) : fPlus p = 0 := by
  unfold fPlus
  by_cases ha : 1 < p.1
  · have hb : p.2 ∉ Ioo (1 / 2 : ℝ) 1 := fun hb => h ⟨ha, hb.1, hb.2⟩
    rw [show stripB p.2 = 0 from indicator_of_notMem hb _, mul_zero]
  · have ha' : p.1 ∉ Ioi (1 : ℝ) := ha
    rw [show tailA p.1 = 0 from indicator_of_notMem ha' _, zero_mul]

theorem integrable_fPlus : Integrable fPlus := by
  have hA : Integrable tailA := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)
  have hB : Integrable stripB := (integrable_indicator_iff measurableSet_Ioo).mpr
    (integrableOn_const (by simp [Real.volume_Ioo]))
  have := hA.mul_prod hB
  rw [← Measure.volume_eq_prod] at this
  exact this

/-- `Q₀ = (5/8, 7/8) × (1/8, 3/8)`. -/
def Q0 : Set (ℝ × ℝ) := Ioo (5 / 8) (7 / 8) ×ˢ Ioo (1 / 8) (3 / 8)

theorem measurableSet_Q0 : MeasurableSet Q0 := measurableSet_Ioo.prod measurableSet_Ioo

/-- The weight `μ = f₊ − f₊ ∘ refl 1 + 𝟙_{Q₀}`. -/
noncomputable def wMu (p : ℝ × ℝ) : ℝ := fPlus p - fPlus (refl 1 p) + Q0.indicator 1 p

theorem fPlus_refl_eq_zero_of_pos {p : ℝ × ℝ} (h : 0 < p.2) : fPlus (refl 1 p) = 0 :=
  fPlus_eq_zero fun h' => by simp only [refl] at h'; linarith [h'.1]

theorem Q0_indicator_eq_zero {p : ℝ × ℝ} (h : ¬ (5 / 8 < p.1 ∧ p.1 < 7 / 8 ∧ 1 / 8 < p.2 ∧ p.2 < 3 / 8)) :
    Q0.indicator (1 : ℝ × ℝ → ℝ) p = 0 :=
  indicator_of_notMem (fun hq => h ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩) _

/-- The Preisach operator with weight `wMu` and all relays initially `−1`. -/
noncomputable def butterflyWitness : IntegralPreisach where
  μ := wMu
  integrable := (integrable_fPlus.sub (integrable_comp_refl integrable_fPlus 1)).add
    ((integrable_indicator_iff measurableSet_Q0).mpr (integrableOn_const
      (volume_box_ne_top _ _ _ _)))
  vanishes_off p hp := by
    have h1 : fPlus p = 0 := fPlus_eq_zero fun h => by linarith [h.1, h.2.2]
    have h2 : fPlus (refl 1 p) = 0 := fPlus_eq_zero fun h => by
      simp only [refl] at h; linarith [h.1, h.2.2]
    have h3 := Q0_indicator_eq_zero (p := p) fun h => by linarith [h.1, h.2.2.2]
    simp only [wMu, h1, h2, h3]; ring
  r₀ := fun _ => -1
  r₀_measurable := measurable_const
  r₀_bound _ := by norm_num

/-- On `U = {β > 0, α ≥ 1}`, `μ = f₊`. -/
theorem wMu_upper {p : ℝ × ℝ} (hb : 0 < p.2) (ha : 1 ≤ p.1) : wMu p = fPlus p := by
  have h3 := Q0_indicator_eq_zero (p := p) fun h => by linarith [h.2.1]
  simp only [wMu, fPlus_refl_eq_zero_of_pos hb, h3]; ring

/-- On `L = {β ≤ 0, α < 1}`, `μ = −f₊ ∘ refl 1`. -/
theorem wMu_lower {p : ℝ × ℝ} (hb : p.2 ≤ 0) (ha : p.1 < 1) : wMu p = -fPlus (refl 1 p) := by
  have h1 : fPlus p = 0 := fPlus_eq_zero fun h => by linarith [h.1]
  have h3 := Q0_indicator_eq_zero (p := p) fun h => by linarith [h.2.2.1]
  simp only [wMu, h1, h3]; ring

/-- `∬_U f₊ (α − β) = ∞`: the slice at any `β₀ ∈ (1/2, 1)` dominates `α⁻¹/2` on `(2, ∞)`. -/
theorem not_integrable_upper_moment :
    ¬ Integrable ({p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1}.indicator fun p => fPlus p * (p.1 - p.2)) := by
  intro hi
  set G := {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1}.indicator fun p => fPlus p * (p.1 - p.2)
  rw [Measure.volume_eq_prod] at hi
  have hae := hi.prod_left_ae
  have hpos : (volume : Measure ℝ) (Ioo (1 / 2) 1) ≠ 0 := by
    rw [Real.volume_Ioo]; norm_num
  obtain ⟨b, hb, hint⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hae)
  have hb1 : (1 / 2 : ℝ) < b := hb.1
  have hb2 : b < 1 := hb.2
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi 2) := by
    refine Integrable.mono' (hint.restrict.const_mul 2) ?_ ?_
    · exact (measurable_inv.aestronglyMeasurable).restrict
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun x (hx : 2 < x) => ?_
      have hx0 : 0 < x := by linarith
      have hmem : (x, b) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1} := ⟨by linarith, by linarith⟩
      have hval : G (x, b) = x ^ (-2 : ℝ) * (x - b) := by
        simp only [G, indicator_of_mem hmem, fPlus, tailA, stripB,
          indicator_of_mem (show x ∈ Ioi (1 : ℝ) by simp only [mem_Ioi]; linarith),
          indicator_of_mem (show b ∈ Ioo (1 / 2 : ℝ) 1 from hb)]
        ring
      have hrp : x ^ (-2 : ℝ) = (x ^ 2)⁻¹ := by
        rw [Real.rpow_neg hx0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [hval, hrp, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
      rw [show (x ^ 2)⁻¹ * (x - b) = (x - b) / x ^ 2 by ring, mul_div_assoc']
      rw [inv_eq_one_div, div_le_div_iff₀ hx0 (by positivity)]
      nlinarith
  exact not_integrableOn_Ioi_inv hinv

theorem moment_upper :
    ¬ IntegrableOn (fun p => butterflyWitness.μ p * (p.1 - p.2)) {p | 0 < p.2 ∧ 1 ≤ p.1} := by
  intro h
  have hE : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_const measurable_fst)
  rw [← integrable_indicator_iff hE] at h
  apply not_integrable_upper_moment
  refine h.congr (ae_of_all _ fun p => ?_)
  by_cases hp : p ∈ {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1}
  · simp only [indicator_of_mem hp]
    show wMu p * _ = _
    rw [wMu_upper hp.1 hp.2]
  · simp only [indicator_of_notMem hp]

theorem moment_lower :
    ¬ IntegrableOn (fun p => butterflyWitness.μ p * (p.1 - p.2)) {p | p.2 ≤ 0 ∧ p.1 < 1} := by
  intro h
  have hE : MeasurableSet {p : ℝ × ℝ | p.2 ≤ 0 ∧ p.1 < 1} :=
    (measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_lt measurable_fst measurable_const)
  rw [← integrable_indicator_iff hE] at h
  apply not_integrable_upper_moment
  refine ((integrable_comp_refl h 1).neg).congr (ae_of_all _ fun p => ?_)
  have hiff : refl 1 p ∈ {p : ℝ × ℝ | p.2 ≤ 0 ∧ p.1 < 1} ↔ p ∈ {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1} := by
    simp only [refl, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  by_cases hp : p ∈ {p : ℝ × ℝ | 0 < p.2 ∧ 1 ≤ p.1}
  · have hq := hiff.mpr hp
    simp only [Pi.neg_apply, indicator_of_mem hq, indicator_of_mem hp]
    show -(wMu (refl 1 p) * _) = _
    rw [wMu_lower hq.1 hq.2, show refl 1 (refl 1 p) = p by simp [refl]]
    simp only [refl]; ring
  · have hq : refl 1 p ∉ {p : ℝ × ℝ | p.2 ≤ 0 ∧ p.1 < 1} := fun h => hp (hiff.mp h)
    simp only [Pi.neg_apply, indicator_of_notMem hq, indicator_of_notMem hp, neg_zero]

/-- At level `1/2`, only the bump `Q₀` is in `Ω_{1/2}`: `∬_{Ω_{1/2}} μ = 1/16`. -/
theorem butterflyWitness_omega {m M : ℝ} (hm : m ≤ 0) (hM : 1 ≤ M) :
    butterflyWitness.omegaWeight m M (1 / 2) = 1 / 16 := by
  classical
  have e : ∀ p : ℝ × ℝ, butterflyWitness.μ p * omegaInd m M (1 / 2) p = Q0.indicator 1 p :=
    fun p => by
      show wMu p * _ = _
      by_cases hq : p ∈ Q0
      · obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hq
        have hΩ : m < p.2 ∧ p.1 < M ∧ p.2 ≤ 1 / 2 ∧ 1 / 2 ≤ p.1 :=
          ⟨by linarith, by linarith, by linarith, by linarith⟩
        have h1 : fPlus p = 0 := fPlus_eq_zero fun h => by linarith [h.1]
        have h2 := fPlus_refl_eq_zero_of_pos (p := p) (by linarith)
        simp only [wMu, omegaInd, hΩ, and_self, ite_true, h1, h2,
          indicator_of_mem (show p ∈ Q0 from ⟨⟨a1, a2⟩, b1, b2⟩)]
        norm_num
      · rw [indicator_of_notMem hq]
        unfold omegaInd
        split_ifs with hΩ
        · have h1 : fPlus p = 0 := fPlus_eq_zero fun h => by linarith [h.2.1, hΩ.2.2.1]
          have h2 : fPlus (refl 1 p) = 0 := fPlus_eq_zero fun h => by
            simp only [refl] at h; linarith [h.2.2, hΩ.2.2.2]
          simp only [wMu, h1, h2, indicator_of_notMem hq]; ring
        · ring
  rw [IntegralPreisach.omegaWeight, integral_congr_ae (ae_of_all _ e),
    integral_indicator_one measurableSet_Q0, measureReal_def, Q0, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  norm_num

/-- **Theorem 3.3 is not vacuous**: `butterflyWitness` meets every hypothesis of
`theorem3_3_moments` (`β₁ = 0`, `α₁ = 1`, `s = 1`) and is a butterfly hysteresis operator. -/
theorem butterflyWitness_isButterfly : IsButterflyOperator butterflyWitness.output := by
  refine butterflyWitness.theorem3_3_moments (β₁ := 0) (α₁ := 1) (s := 1) one_pos one_ne_zero
    (fun p hb ha => ?_) (fun p hb ha => ?_) moment_upper moment_lower
    (fun m M hm hM => ⟨1 / 2, ⟨by linarith, by linarith⟩, ?_⟩)
  · show 0 ≤ 1 * wMu p
    rw [one_mul, wMu_upper hb ha]; exact fPlus_nonneg p
  · show 1 * wMu p ≤ 0
    rw [one_mul, wMu_lower hb ha]; linarith [fPlus_nonneg (refl 1 p)]
  · rw [butterflyWitness_omega hm hM]; norm_num

end ButterflyCharacterization.Domain.Model
