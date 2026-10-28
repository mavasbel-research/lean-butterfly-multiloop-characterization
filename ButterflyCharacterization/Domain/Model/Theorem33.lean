import ButterflyCharacterization.Domain.Model.IntegralPreisach
import ButterflyCharacterization.Domain.Model.CosineInput

/-!
# Theorem 3.3 for the Preisach operator (4)

* `branchForm`: on a period with `T ≤ t₁` the integral operator has branches
  `y±(υ) = ∬ μ · (relay level-closed form)`, and `y⁺(υ) − y⁻(υ) = −2 ∬_{Ω_υ} μ`;
* `continuousOn_areaOf_right`, `continuousOn_areaOf_left`: the loop area depends continuously
  on `u_max` and on `u_min` (dominated convergence; the lines `α = λ`, `β = λ` are null);
* `theorem3_3`: if the area of `[β₁, α₁]` can be pushed to `+∞` by raising `u_max` and to
  `−∞` by lowering `u_min`, and every input range `[m, M] ⊇ [β₁, α₁]` gives a non-degenerate
  loop, then `P` is a butterfly hysteresis operator.

The paper derives the two limits from the sign of μ and the moment conditions (5)–(6); that
derivation is not formalized here, so the limits are hypotheses of `theorem3_3`.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- Relay output on the ascending branch at level `υ`, initial state `r`. -/
noncomputable def upClosed (m M υ α β r : ℝ) : ℝ :=
  if α < υ then 1 else if m < β then -1 else if α < M then 1 else r

/-- Relay output on the descending branch at level `υ`, initial state `r`. -/
noncomputable def downClosed (m M υ α β r : ℝ) : ℝ :=
  if υ < β then -1 else if α < M then 1 else if m < β then -1 else r

theorem relayUp_eq {I : SimplePeriodicInput} {α β r υ : ℝ} :
    relayUp I α β r υ = upClosed I.umin I.umax υ α β r := by
  unfold relayUp upClosed
  split_ifs with h1 h2 h3 <;> try rfl
  exact ccwRelay_zero ⟨(not_lt.mp h2).trans (I.bounds 0).1, (I.bounds 0).2.trans (not_lt.mp h3)⟩

theorem relayDown_eq {I : SimplePeriodicInput} {α β r υ : ℝ} :
    relayDown I α β r υ = downClosed I.umin I.umax υ α β r := by
  unfold relayDown downClosed
  split_ifs with h1 h2 h3 <;> try rfl
  exact ccwRelay_zero ⟨(not_lt.mp h3).trans (I.bounds 0).1, (I.bounds 0).2.trans (not_lt.mp h2)⟩

theorem abs_upClosed_le {m M υ α β r : ℝ} (hr : |r| ≤ 1) : |upClosed m M υ α β r| ≤ 1 := by
  unfold upClosed; split_ifs <;> first | exact hr | norm_num

theorem abs_downClosed_le {m M υ α β r : ℝ} (hr : |r| ≤ 1) : |downClosed m M υ α β r| ≤ 1 := by
  unfold downClosed; split_ifs <;> first | exact hr | norm_num

/-- Indicator of `Ω_υ`: switching relays (`m < β`, `α < M`) whose band contains `υ`. -/
noncomputable def omegaInd (m M υ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if m < p.2 ∧ p.1 < M ∧ p.2 ≤ υ ∧ υ ≤ p.1 then 1 else 0

namespace IntegralPreisach

variable (P : IntegralPreisach)

/-- Ascending branch. -/
noncomputable def yUp (m M υ : ℝ) : ℝ := ∫ p, P.μ p * upClosed m M υ p.1 p.2 (P.r₀ p)

/-- Descending branch. -/
noncomputable def yDown (m M υ : ℝ) : ℝ := ∫ p, P.μ p * downClosed m M υ p.1 p.2 (P.r₀ p)

/-- `∬_{Ω_υ} μ`. -/
noncomputable def omegaWeight (m M υ : ℝ) : ℝ := ∫ p, P.μ p * omegaInd m M υ p

theorem integrable_bdd {g : ℝ × ℝ → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ p, |g p| ≤ c) :
    Integrable fun p => P.μ p * g p :=
  P.integrable.mul_bdd hg.aestronglyMeasurable (ae_of_all _ fun p => by
    rw [Real.norm_eq_abs]; exact hc p)

theorem measurable_upClosed (m M υ : ℝ) :
    Measurable fun p : ℝ × ℝ => upClosed m M υ p.1 p.2 (P.r₀ p) := by
  unfold upClosed
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
      (Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
        P.r₀_measurable))

theorem measurable_downClosed (m M υ : ℝ) :
    Measurable fun p : ℝ × ℝ => downClosed m M υ p.1 p.2 (P.r₀ p) := by
  unfold downClosed
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
    (Measurable.ite (measurableSet_lt measurable_fst measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
        P.r₀_measurable))

theorem measurable_omegaInd (m M υ : ℝ) : Measurable (omegaInd m M υ) := by
  unfold omegaInd
  refine Measurable.ite ?_ measurable_const measurable_const
  exact ((measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_le measurable_const measurable_fst))))

variable {I : SimplePeriodicInput}

theorem output_eq_up (hT : I.T ≤ I.t₁) {x : ℝ} (hx : x ∈ Icc I.t₁ I.t₂) :
    P.output I.u x = P.yUp I.umin I.umax (I.u x) :=
  integral_congr_ae (ae_of_all _ fun p => by
    by_cases hp : p.2 < p.1
    · simp only [relay_rising hp hT hx, relayUp_eq]
    · simp only [P.vanishes_off p (not_lt.mp hp), zero_mul])

theorem output_eq_down {x : ℝ} (hx : x ∈ Icc I.t₂ (I.t₁ + I.T)) :
    P.output I.u x = P.yDown I.umin I.umax (I.u x) :=
  integral_congr_ae (ae_of_all _ fun p => by
    by_cases hp : p.2 < p.1
    · simp only [relay_falling hp hx, relayDown_eq]
    · simp only [P.vanishes_off p (not_lt.mp hp), zero_mul])

theorem output_periodic (hT : I.T ≤ I.t₁) {t : ℝ} (ht : I.t₁ ≤ t) :
    P.output I.u (t + I.T) = P.output I.u t :=
  integral_congr_ae (ae_of_all _ fun p => by
    by_cases hp : p.2 < p.1
    · simp only [relay_periodic (α := p.1) (β := p.2) (r₀ := P.r₀ p) hT ht]
    · simp only [P.vanishes_off p (not_lt.mp hp), zero_mul])

/-- The branch form of (4) on a period with `T ≤ t₁`. -/
noncomputable def branchForm (hT : I.T ≤ I.t₁) : BranchForm P.output I where
  yUp := P.yUp I.umin I.umax
  yDown := P.yDown I.umin I.umax
  rising _ hx := P.output_eq_up hT hx
  falling _ hx := P.output_eq_down hx
  periodic _ ht := P.output_periodic hT ht

/-- The branch gap: `y⁺(υ) − y⁻(υ) = −2 ∬_{Ω_υ} μ`. -/
theorem yUp_sub_yDown {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    P.yUp I.umin I.umax υ - P.yDown I.umin I.umax υ = -2 * P.omegaWeight I.umin I.umax υ := by
  rw [yUp, yDown, omegaWeight, ← integral_sub (P.integrable_bdd (P.measurable_upClosed _ _ _)
      fun p => abs_upClosed_le (P.r₀_bound p))
    (P.integrable_bdd (P.measurable_downClosed _ _ _) fun p => abs_downClosed_le (P.r₀_bound p)),
    ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  by_cases hp : p.2 < p.1
  · have g := relayUp_sub_relayDown (I := I) (r₀ := P.r₀ p) hp hυ
    rw [relayUp_eq, relayDown_eq] at g
    simp only [← mul_sub, g, omegaInd]
    split_ifs <;> ring
  · simp only [P.vanishes_off p (not_lt.mp hp)]
    ring

/-- Definition 2.5 holds as soon as `∬_{Ω_υ} μ ≠ 0` at one level. -/
theorem isHysteresisLoop (hT : I.T ≤ I.t₁) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax)
    (hΩ : P.omegaWeight I.umin I.umax υ ≠ 0) : IsHysteresisLoop P.output I I.t₁ :=
  (P.branchForm hT).isHysteresisLoop hυ fun h => hΩ (by
    have gap := P.yUp_sub_yDown hυ
    have h' : P.yUp I.umin I.umax υ = P.yDown I.umin I.umax υ := h
    linarith)

/-! ### Continuity of the loop area in the input extremes -/

theorem measurable_switchArea (m M : ℝ) : Measurable (switchArea m M) := by
  unfold switchArea
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_fst measurable_const))
    ((measurable_fst.sub measurable_snd).const_mul 2) measurable_const

theorem abs_switchArea_le {m M : ℝ} {p : ℝ × ℝ} (hp : p.2 < p.1) :
    |switchArea m M p| ≤ 2 * |M - m| := by
  unfold switchArea
  split_ifs with h
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith [h.1, h.2])]
    linarith [h.1, h.2]
  · simp [abs_nonneg]

/-- `|μ · switchArea| ≤ |μ| · 2|M − m|` everywhere (`μ` vanishes off the Preisach plane). -/
theorem abs_mu_switchArea_le (m M : ℝ) (p : ℝ × ℝ) :
    |P.μ p * switchArea m M p| ≤ |P.μ p| * (2 * |M - m|) := by
  rw [abs_mul]
  by_cases hp : p.2 < p.1
  · exact mul_le_mul_of_nonneg_left (abs_switchArea_le hp) (abs_nonneg _)
  · rw [P.vanishes_off p (not_lt.mp hp)]; simp

theorem aesm_switch (m M : ℝ) :
    AEStronglyMeasurable (fun p => P.μ p * switchArea m M p) volume :=
  P.integrable.aestronglyMeasurable.mul (measurable_switchArea m M).aestronglyMeasurable

theorem null_fst (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.1 = c} = 0 := by
  have : {p : ℝ × ℝ | p.1 = c} = {c} ×ˢ univ := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem null_snd (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.2 = c} = 0 := by
  have : {p : ℝ × ℝ | p.2 = c} = univ ×ˢ {c} := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- The area is continuous in `u_max`. -/
theorem continuous_areaOf_right (m : ℝ) : Continuous fun M => P.areaOf m M := by
  refine continuous_iff_continuousAt.mpr fun M₀ => ?_
  refine continuousAt_of_dominated (bound := fun p => |P.μ p| * (2 * (|M₀ - m| + 1)))
    (Eventually.of_forall fun M => P.aesm_switch m M)
    ?_ (P.integrable.abs.mul_const _) ?_
  · filter_upwards [Metric.ball_mem_nhds M₀ one_pos] with M hM
    refine ae_of_all _ fun p => ?_
    rw [Real.norm_eq_abs]
    refine (P.abs_mu_switchArea_le m M p).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    have : |M - M₀| < 1 := hM
    have := abs_sub_abs_le_abs_sub (M - m) (M₀ - m)
    rw [show M - m - (M₀ - m) = M - M₀ by ring] at this
    linarith
  · have hnull : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ M₀ := by
      rw [ae_iff]; simpa using null_fst M₀
    filter_upwards [hnull] with p hp
    refine ContinuousAt.mul continuousAt_const ?_
    unfold switchArea
    rcases lt_or_gt_of_ne hp with h | h
    · refine (continuousAt_const (y := if m < p.2 then 2 * (p.1 - p.2) else 0)).congr ?_
      filter_upwards [lt_mem_nhds h] with M hM
      by_cases hm : m < p.2 <;> simp [hm, hM]
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [gt_mem_nhds h] with M hM
      have : ¬ p.1 < M := not_lt.mpr hM.le
      simp [this]

/-- The area is continuous in `u_min`. -/
theorem continuous_areaOf_left (M : ℝ) : Continuous fun m => P.areaOf m M := by
  refine continuous_iff_continuousAt.mpr fun m₀ => ?_
  refine continuousAt_of_dominated (bound := fun p => |P.μ p| * (2 * (|M - m₀| + 1)))
    (Eventually.of_forall fun m => P.aesm_switch m M)
    ?_ (P.integrable.abs.mul_const _) ?_
  · filter_upwards [Metric.ball_mem_nhds m₀ one_pos] with m hm
    refine ae_of_all _ fun p => ?_
    rw [Real.norm_eq_abs]
    refine (P.abs_mu_switchArea_le m M p).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
    have : |m - m₀| < 1 := hm
    have := abs_sub_abs_le_abs_sub (M - m) (M - m₀)
    rw [show M - m - (M - m₀) = -(m - m₀) by ring, abs_neg] at this
    linarith
  · have hnull : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ m₀ := by
      rw [ae_iff]; simpa using null_snd m₀
    filter_upwards [hnull] with p hp
    refine ContinuousAt.mul continuousAt_const ?_
    unfold switchArea
    rcases lt_or_gt_of_ne hp with h | h
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [lt_mem_nhds h] with m hm
      have : ¬ m < p.2 := not_lt.mpr hm.le
      simp [this]
    · refine (continuousAt_const (y := if p.1 < M then 2 * (p.1 - p.2) else 0)).congr ?_
      filter_upwards [gt_mem_nhds h] with m hm
      by_cases hM : p.1 < M <;> simp [hM, hm]

/-! ### Theorem 3.3 -/

/-- Loop of the cosine input `[m, M]`: if it is non-degenerate, its area is `areaOf m M`. -/
theorem cosine_loop {m M : ℝ} (h : m < M) {υ : ℝ} (hυ : υ ∈ Icc m M)
    (hΩ : P.omegaWeight m M υ ≠ 0) :
    IsHysteresisLoop P.output (cosineInput m M h) (cosineInput m M h).t₁ ∧
      loopArea P.output (cosineInput m M h) = P.areaOf m M := by
  have hT : (cosineInput m M h).T ≤ (cosineInput m M h).t₁ := le_refl _
  have em := cosineInput_umin m M h
  have eM := cosineInput_umax m M h
  refine ⟨P.isHysteresisLoop hT (by rw [em, eM]; exact hυ) (by rw [em, eM]; exact hΩ), ?_⟩
  rw [P.area_of_late hT, em, eM]

/-- **Theorem 3.3** (Preisach operator (4)). Let `β₁ < α₁`. Suppose raising `u_max` drives the
loop area of `[β₁, u_max]` to `+∞`, lowering `u_min` drives that of `[u_min, α₁]` to `−∞`
(the role of (5)–(6) and the two-sided sign in the paper's proof), and every input range containing `[β₁, α₁]` has a level `υ` with
`∬_{Ω_υ} μ ≠ 0` (Definition 2.5's two-point condition). Then `P` is a butterfly hysteresis
operator. -/
theorem theorem3_3 {β₁ α₁ : ℝ} (h₁ : β₁ < α₁)
    (hup : Tendsto (fun M => P.areaOf β₁ M) atTop atTop)
    (hdown : Tendsto (fun m => P.areaOf m α₁) atBot atBot)
    (hgap : ∀ m M, m ≤ β₁ → α₁ ≤ M → ∃ υ ∈ Icc m M, P.omegaWeight m M υ ≠ 0) :
    IsButterflyOperator P.output := by
  rcases le_or_gt (P.areaOf β₁ α₁) 0 with hA | hA
  · obtain ⟨b, hb⟩ := (tendsto_atTop.mp hup 0).exists_forall_of_atTop
    have hc : α₁ ≤ max b α₁ := le_max_right _ _
    obtain ⟨M, ⟨hM1, -⟩, hM⟩ := intermediate_value_Icc hc
      (P.continuous_areaOf_right β₁).continuousOn ⟨hA, hb _ (le_max_left _ _)⟩
    have hlt : β₁ < M := h₁.trans_le hM1
    obtain ⟨υ, hυ, hΩ⟩ := hgap β₁ M le_rfl hM1
    obtain ⟨hl, harea⟩ := P.cosine_loop hlt hυ hΩ
    exact ⟨P.output_hysteresis, _, _, hl, harea.trans hM⟩
  · obtain ⟨b, hb⟩ := (tendsto_atBot.mp hdown 0).exists_forall_of_atBot
    have hc : min b β₁ ≤ β₁ := min_le_right _ _
    have hβ : P.areaOf β₁ α₁ ∈ Icc (P.areaOf (min b β₁) α₁) (P.areaOf β₁ α₁) := ⟨(hb _ (min_le_left _ _)).trans hA.le, le_rfl⟩
    obtain ⟨m, ⟨-, hm1⟩, hm⟩ := intermediate_value_Icc hc
      (P.continuous_areaOf_left α₁).continuousOn ⟨hb _ (min_le_left _ _), hA.le⟩
    have hlt : m < α₁ := hm1.trans_lt h₁
    obtain ⟨υ, hυ, hΩ⟩ := hgap m α₁ hm1 le_rfl
    obtain ⟨hl, harea⟩ := P.cosine_loop hlt hυ hΩ
    exact ⟨P.output_hysteresis, _, _, hl, harea.trans hm⟩

end IntegralPreisach

end ButterflyCharacterization.Domain.Model
