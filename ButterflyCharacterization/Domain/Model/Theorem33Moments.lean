import ButterflyCharacterization.Domain.Model.Theorem33

/-!
# Theorem 3.3: the area limits from the sign of `μ` and the moment conditions

The proof of Theorem 3.3 extends the input range beyond `[β₁, α₁]`:

* raising `u_max = λ > α₁` adds the relays of `P₁₊^{ext,λ} = {β > β₁, α₁ ≤ α < λ}`, and the
  area grows by `h(λ) = 2 ∬_{P₁₊^{ext,λ}} μ (α − β)`;
* lowering `u_min = λ < β₁` adds the relays of `P₁₋^{ext,λ} = {λ < β ≤ β₁, α < α₁}`.

If `μ` has one sign `s` on `{β > β₁, α ≥ α₁}` and the opposite sign on `{β ≤ β₁, α < α₁}`
(the two-sided weight with a decreasing boundary `B` through `(α₁, β₁)`, either orientation),
and the first moments `∬ μ (α − β)` over these two regions are unbounded (`μ (α − β)` is not
integrable there — the role of (5)–(6)), then `s · A → +∞` as `u_max → ∞` and `s · A → −∞` as
`u_min → −∞` (monotone convergence), so the areas of `[β₁, M]` and `[m, α₁]` eventually have
opposite signs and `theorem3_3_of_signs` gives a zero-area loop.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- A nonnegative family of integrable functions, increasing in `λ`, converging pointwise along
`ℕ` to a non-integrable limit: the integrals tend to `+∞`. -/
theorem tendsto_integral_of_not_integrable {g : ℝ → ℝ × ℝ → ℝ} {F : ℝ × ℝ → ℝ}
    (hi : ∀ L, Integrable (g L)) (hnn : ∀ L p, 0 ≤ g L p) (hmono : ∀ p, Monotone fun L => g L p)
    (hlim : ∀ p, Tendsto (fun n : ℕ => g n p) atTop (𝓝 (F p)))
    (hF : AEStronglyMeasurable F volume) (hni : ¬ Integrable F) :
    Tendsto (fun L => ∫ p, g L p) atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone
    (fun a b hab => integral_mono (hi a) (hi b) fun p => hmono p hab) fun C => ?_
  by_contra hcon
  push Not at hcon
  have lim := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun n : ℕ => fun p => ENNReal.ofReal (g n p)) (F := fun p => ENNReal.ofReal (F p))
    (fun n => (hi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (ae_of_all _ fun p i j hij => ENNReal.ofReal_le_ofReal (hmono p (Nat.cast_le.mpr hij)))
    (ae_of_all _ fun p => (ENNReal.continuous_ofReal.tendsto _).comp (hlim p))
  have hle : ∀ n : ℕ, ∫⁻ p, ENNReal.ofReal (g n p) ≤ ENNReal.ofReal C := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (ae_of_all _ (hnn n))]
    exact ENNReal.ofReal_le_ofReal (hcon n).le
  have hFle : ∫⁻ p, ENNReal.ofReal (F p) ≤ ENNReal.ofReal C := le_of_tendsto' lim hle
  have hFnn : 0 ≤ᵐ[volume] F :=
    ae_of_all _ fun p => ge_of_tendsto' (hlim p) fun n => hnn n p
  exact hni ⟨hF, (hasFiniteIntegral_iff_ofReal hFnn).mpr (hFle.trans_lt ENNReal.ofReal_lt_top)⟩

namespace IntegralPreisach

variable (P : IntegralPreisach)

theorem switchArea_sub_right {β₁ α₁ M : ℝ} (h : α₁ ≤ M) (p : ℝ × ℝ) :
    switchArea β₁ M p - switchArea β₁ α₁ p =
      if β₁ < p.2 ∧ α₁ ≤ p.1 ∧ p.1 < M then 2 * (p.1 - p.2) else 0 := by
  have e : (p.1 < α₁) ↔ ¬ α₁ ≤ p.1 := not_le.symm
  unfold switchArea
  by_cases hb : β₁ < p.2 <;> by_cases ha : α₁ ≤ p.1 <;> by_cases hM : p.1 < M <;>
    first | (simp [e, hb, ha, hM]; linarith) | simp [e, hb, ha, hM]

theorem switchArea_sub_left {β₁ α₁ m : ℝ} (h : m ≤ β₁) (p : ℝ × ℝ) :
    switchArea m α₁ p - switchArea β₁ α₁ p =
      if m < p.2 ∧ p.2 ≤ β₁ ∧ p.1 < α₁ then 2 * (p.1 - p.2) else 0 := by
  have e : (p.2 ≤ β₁) ↔ ¬ β₁ < p.2 := not_lt.symm
  unfold switchArea
  by_cases hb : β₁ < p.2 <;> by_cases hm : m < p.2 <;> by_cases ha : p.1 < α₁ <;>
    first | (simp [e, hb, hm, ha]; linarith) | simp [e, hb, hm, ha]

theorem integrable_term (m M : ℝ) : Integrable fun p => P.μ p * switchArea m M p :=
  (P.integrable.abs.mul_const (2 * |M - m|)).mono (P.aesm_switch m M)
    (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact (P.abs_mu_switchArea_le m M p).trans (le_abs_self _))

theorem areaOf_sub (m M m' M' : ℝ) :
    P.areaOf m M - P.areaOf m' M' =
      ∫ p, P.μ p * (switchArea m M p - switchArea m' M' p) := by
  rw [areaOf, areaOf, ← integral_sub (P.integrable_term m M) (P.integrable_term m' M')]
  simp only [mul_sub]

/-- `μ (α − β)` is a.e.-strongly measurable. -/
theorem aesm_moment : AEStronglyMeasurable (fun p => P.μ p * (p.1 - p.2)) volume :=
  P.integrable.aestronglyMeasurable.mul
    (measurable_fst.sub measurable_snd).aestronglyMeasurable

/-- The sign condition makes `s μ (α − β) ≥ 0` on a region where `s μ ≥ 0`. -/
theorem nonneg_moment {s : ℝ} {p : ℝ × ℝ} (hμ : 0 ≤ s * P.μ p) :
    0 ≤ s * P.μ p * (2 * (p.1 - p.2)) := by
  by_cases hp : p.2 < p.1
  · exact mul_nonneg hμ (by linarith)
  · rw [P.vanishes_off p (not_lt.mp hp)]; simp

theorem not_integrable_of_moment {s : ℝ} (hs : s ≠ 0) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E)
    (h : ¬ IntegrableOn (fun p => P.μ p * (p.1 - p.2)) E) :
    ¬ Integrable (E.indicator fun p => s * P.μ p * (2 * (p.1 - p.2))) := by
  intro hi
  rw [integrable_indicator_iff hE] at hi
  apply h
  have := hi.const_mul (1 / (2 * s))
  refine this.congr (ae_of_all _ fun p => ?_)
  field_simp

/-- **Raising `u_max`.** If `s μ ≥ 0` on `{β > β₁, α ≥ α₁}` and `μ (α − β)` is not integrable
there, then `s · A(β₁, M) → +∞` as `M → ∞`. -/
theorem tendsto_areaOf_right {β₁ α₁ s : ℝ} (hs : s ≠ 0)
    (hsign : ∀ p : ℝ × ℝ, β₁ < p.2 → α₁ ≤ p.1 → 0 ≤ s * P.μ p)
    (hmom : ¬ IntegrableOn (fun p => P.μ p * (p.1 - p.2)) {p | β₁ < p.2 ∧ α₁ ≤ p.1}) :
    Tendsto (fun M => s * P.areaOf β₁ M) atTop atTop := by
  set E : Set (ℝ × ℝ) := {p | β₁ < p.2 ∧ α₁ ≤ p.1}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_const measurable_fst)
  set g : ℝ → ℝ × ℝ → ℝ := fun L p =>
    s * P.μ p * (switchArea β₁ (max L α₁) p - switchArea β₁ α₁ p)
  have hg : ∀ L p, g L p =
      if β₁ < p.2 ∧ α₁ ≤ p.1 ∧ p.1 < max L α₁ then s * P.μ p * (2 * (p.1 - p.2)) else 0 :=
    fun L p => by
      simp only [g, switchArea_sub_right (le_max_right L α₁) p]
      split_ifs <;> ring
  have hint : ∀ L, ∫ p, g L p = s * (P.areaOf β₁ (max L α₁) - P.areaOf β₁ α₁) := fun L => by
    rw [P.areaOf_sub β₁ (max L α₁) β₁ α₁, ← integral_const_mul]
    congr 1; funext p; simp only [g]; ring
  have key : Tendsto (fun L => ∫ p, g L p) atTop atTop := by
    refine tendsto_integral_of_not_integrable (F := E.indicator fun p => s * P.μ p * (2 * (p.1 - p.2)))
      (fun L => ?_) (fun L p => ?_) (fun p a b hab => ?_) (fun p => ?_) ?_
      (P.not_integrable_of_moment hs hE hmom)
    · exact (((P.integrable_term β₁ (max L α₁)).sub (P.integrable_term β₁ α₁)).const_mul s).congr
        (ae_of_all _ fun p => by simp only [g, Pi.sub_apply]; ring)
    · rw [hg]
      split_ifs with h
      · exact P.nonneg_moment (hsign p h.1 h.2.1)
      · exact le_rfl
    · simp only [hg]
      by_cases h1 : β₁ < p.2 ∧ α₁ ≤ p.1 ∧ p.1 < max a α₁
      · have h2 : β₁ < p.2 ∧ α₁ ≤ p.1 ∧ p.1 < max b α₁ :=
          ⟨h1.1, h1.2.1, h1.2.2.trans_le (max_le_max_right α₁ hab)⟩
        rw [ite_eq_left h1, ite_eq_left h2]
      · rw [ite_eq_right h1]
        split_ifs with h2
        · exact P.nonneg_moment (hsign p h2.1 h2.2.1)
        · exact le_rfl
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop p.1] with n hn
      rw [hg]
      by_cases h : β₁ < p.2 ∧ α₁ ≤ p.1
      · rw [indicator_of_mem (show p ∈ E from h), ite_eq_left ⟨h.1, h.2, lt_max_of_lt_left hn⟩]
      · rw [indicator_of_notMem (show p ∉ E from h), ite_eq_right fun h' => h ⟨h'.1, h'.2.1⟩]
    · exact (((P.aesm_moment.const_mul (2 * s)).congr (ae_of_all _ fun p => by ring)).indicator hE)
  have e : (fun L => ∫ p, g L p) =ᶠ[atTop] fun M => s * P.areaOf β₁ M - s * P.areaOf β₁ α₁ := by
    filter_upwards [eventually_ge_atTop α₁] with M hM
    rw [hint, max_eq_left hM]; ring
  have := (tendsto_atTop_add_const_left _ (s * P.areaOf β₁ α₁) (key.congr' e))
  exact this.congr fun M => by ring

/-- **Lowering `u_min`.** If `s μ ≥ 0` on `{β ≤ β₁, α < α₁}` and `μ (α − β)` is not integrable
there, then `s · A(m, α₁) → +∞` as `m → −∞`. -/
theorem tendsto_areaOf_left {β₁ α₁ s : ℝ} (hs : s ≠ 0)
    (hsign : ∀ p : ℝ × ℝ, p.2 ≤ β₁ → p.1 < α₁ → 0 ≤ s * P.μ p)
    (hmom : ¬ IntegrableOn (fun p => P.μ p * (p.1 - p.2)) {p | p.2 ≤ β₁ ∧ p.1 < α₁}) :
    Tendsto (fun m => s * P.areaOf m α₁) atBot atTop := by
  set E : Set (ℝ × ℝ) := {p | p.2 ≤ β₁ ∧ p.1 < α₁}
  have hE : MeasurableSet E := (measurableSet_le measurable_snd measurable_const).inter
    (measurableSet_lt measurable_fst measurable_const)
  set g : ℝ → ℝ × ℝ → ℝ := fun L p =>
    s * P.μ p * (switchArea (min (-L) β₁) α₁ p - switchArea β₁ α₁ p)
  have hg : ∀ L p, g L p =
      if min (-L) β₁ < p.2 ∧ p.2 ≤ β₁ ∧ p.1 < α₁ then s * P.μ p * (2 * (p.1 - p.2)) else 0 :=
    fun L p => by
      simp only [g, switchArea_sub_left (min_le_right (-L) β₁) p]
      split_ifs <;> ring
  have hint : ∀ L, ∫ p, g L p = s * (P.areaOf (min (-L) β₁) α₁ - P.areaOf β₁ α₁) := fun L => by
    rw [P.areaOf_sub (min (-L) β₁) α₁ β₁ α₁, ← integral_const_mul]
    congr 1; funext p; simp only [g]; ring
  have key : Tendsto (fun L => ∫ p, g L p) atTop atTop := by
    refine tendsto_integral_of_not_integrable (F := E.indicator fun p => s * P.μ p * (2 * (p.1 - p.2)))
      (fun L => ?_) (fun L p => ?_) (fun p a b hab => ?_) (fun p => ?_) ?_
      (P.not_integrable_of_moment hs hE hmom)
    · exact (((P.integrable_term (min (-L) β₁) α₁).sub (P.integrable_term β₁ α₁)).const_mul
        s).congr (ae_of_all _ fun p => by simp only [g, Pi.sub_apply]; ring)
    · rw [hg]
      split_ifs with h
      · exact P.nonneg_moment (hsign p h.2.1 h.2.2)
      · exact le_rfl
    · simp only [hg]
      by_cases h1 : min (-a) β₁ < p.2 ∧ p.2 ≤ β₁ ∧ p.1 < α₁
      · have h2 : min (-b) β₁ < p.2 ∧ p.2 ≤ β₁ ∧ p.1 < α₁ :=
          ⟨(min_le_min_right β₁ (neg_le_neg hab)).trans_lt h1.1, h1.2.1, h1.2.2⟩
        rw [ite_eq_left h1, ite_eq_left h2]
      · rw [ite_eq_right h1]
        split_ifs with h2
        · exact P.nonneg_moment (hsign p h2.2.1 h2.2.2)
        · exact le_rfl
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (-p.2)] with n hn
      rw [hg]
      by_cases h : p.2 ≤ β₁ ∧ p.1 < α₁
      · rw [indicator_of_mem (show p ∈ E from h),
          ite_eq_left ⟨min_lt_of_left_lt (by linarith), h.1, h.2⟩]
      · rw [indicator_of_notMem (show p ∉ E from h), ite_eq_right fun h' => h ⟨h'.2.1, h'.2.2⟩]
    · exact (((P.aesm_moment.const_mul (2 * s)).congr (ae_of_all _ fun p => by ring)).indicator hE)
  have key' := key.comp tendsto_neg_atBot_atTop
  have e : (fun L => ∫ p, g L p) ∘ Neg.neg =ᶠ[atBot]
      fun m => s * P.areaOf m α₁ - s * P.areaOf β₁ α₁ := by
    filter_upwards [eventually_le_atBot β₁] with m hm
    simp only [Function.comp, hint, neg_neg, min_eq_left hm]; ring
  have := tendsto_atTop_add_const_left _ (s * P.areaOf β₁ α₁) (key'.congr' e)
  exact this.congr fun m => by ring

/-- **Theorem 3.3** (Preisach operator (4)), with the hypotheses its proof uses. Let
`β₁ < α₁` and `s ≠ 0` (the orientation of the two-sided weight). If

* `s μ ≥ 0` on `{β > β₁, α ≥ α₁}` and `s μ ≤ 0` on `{β ≤ β₁, α < α₁}` (the two extended
  regions of the proof, on the two sides of a decreasing boundary `B` through `(α₁, β₁)`),
* `μ (α − β)` is not integrable on either region (unbounded first moments, (5)–(6)),
* every input range containing `[β₁, α₁]` has a level `υ` with `∬_{Ω_υ} μ ≠ 0`,

then `P` is a butterfly hysteresis operator. -/
theorem theorem3_3_moments {β₁ α₁ s : ℝ} (h₁ : β₁ < α₁) (hs : s ≠ 0)
    (hup : ∀ p : ℝ × ℝ, β₁ < p.2 → α₁ ≤ p.1 → 0 ≤ s * P.μ p)
    (hlow : ∀ p : ℝ × ℝ, p.2 ≤ β₁ → p.1 < α₁ → s * P.μ p ≤ 0)
    (h5 : ¬ IntegrableOn (fun p => P.μ p * (p.1 - p.2)) {p | β₁ < p.2 ∧ α₁ ≤ p.1})
    (h6 : ¬ IntegrableOn (fun p => P.μ p * (p.1 - p.2)) {p | p.2 ≤ β₁ ∧ p.1 < α₁})
    (hgap : ∀ m M, m ≤ β₁ → α₁ ≤ M → ∃ υ ∈ Icc m M, P.omegaWeight m M υ ≠ 0) :
    IsButterflyOperator P.output := by
  have tr := P.tendsto_areaOf_right hs hup h5
  have tl := P.tendsto_areaOf_left (s := -s) (neg_ne_zero.mpr hs)
    (fun p h1 h2 => by have := hlow p h1 h2; linarith) h6
  obtain ⟨M₀, hM, hα⟩ := ((tendsto_atTop.mp tr 0).and (eventually_ge_atTop α₁)).exists
  obtain ⟨m₀, hm, hβ⟩ := ((tendsto_atTop.mp tl 0).and (eventually_le_atBot β₁)).exists
  refine P.theorem3_3_of_signs h₁ hβ hα ?_ hgap
  have hs2 : 0 < s * s := mul_self_pos.mpr hs
  have : s * s * (P.areaOf m₀ α₁ * P.areaOf β₁ M₀) ≤ 0 := by nlinarith
  nlinarith

end IntegralPreisach

end ButterflyCharacterization.Domain.Model
