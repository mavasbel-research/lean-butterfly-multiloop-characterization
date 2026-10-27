import ButterflyCharacterization.Domain.Abstractions.Loop

/-!
# Signed area (1) and simple periodic inputs: basic facts

* `signedArea_eq_green`: on a closed `C¹` curve, `−∫ y u̇ = ½ ∫ (u ẏ − y u̇)`, i.e. the
  definition used here is eq. (1).
* the range of a simple periodic input, the integral of `y u̇` over a piece where `y` is
  constant, and the last times at which the input is below `α` (rising) / above `β` (falling).
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- On a closed `C¹` curve, `−∫ y u̇` is eq. (1), `½∫ (u ẏ − y u̇)`. -/
theorem signedArea_eq_green {u y u' y' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hy : ∀ x, HasDerivAt y (y' x) x)
    (hu' : Continuous u') (hy' : Continuous y') (hua : u a = u b) (hya : y a = y b) :
    signedArea u y a b = (1 / 2) * ∫ τ in a..b, (u τ * deriv y τ - y τ * deriv u τ) := by
  have du : deriv u = u' := funext fun x => (hu x).deriv
  have dy : deriv y = y' := funext fun x => (hy x).deriv
  have cu : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have cy : Continuous y := continuous_iff_continuousAt.mpr fun x => (hy x).continuousAt
  have parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (fun x _ => hu x) (fun x _ => hy x) (hu'.intervalIntegrable _ _) (hy'.intervalIntegrable _ _)
  rw [signedArea, du, dy, intervalIntegral.integral_sub (f := fun τ => u τ * y' τ)
    (g := fun τ => y τ * u' τ) ((cu.mul hy').intervalIntegrable _ _)
    ((cy.mul hu').intervalIntegrable _ _), parts]
  have hc : ∫ x in a..b, u' x * y x = ∫ x in a..b, y x * u' x := by
    congr 1; funext x; ring
  rw [hc, hua, hya]
  ring

theorem signedArea_neg (u y : ℝ → ℝ) (a b : ℝ) :
    signedArea u (fun τ => -y τ) a b = -signedArea u y a b := by
  simp [signedArea, intervalIntegral.integral_neg]

end ButterflyCharacterization.Domain.Model

namespace ButterflyCharacterization.Domain.Abstractions.SimplePeriodicInput

variable (I : SimplePeriodicInput)

theorem continuous : Continuous I.u :=
  continuous_iff_continuousAt.mpr fun x => (I.hasDerivAt x).continuousAt

theorem deriv_eq : deriv I.u = I.u' := funext fun x => (I.hasDerivAt x).deriv

theorem end_eq : I.u (I.t₁ + I.T) = I.umin := I.periodic I.t₁

theorem bounds_on_period {t : ℝ} (ht : t ∈ Icc I.t₁ (I.t₁ + I.T)) :
    I.umin ≤ I.u t ∧ I.u t ≤ I.umax := by
  have h₁ := I.t₁_lt_t₂
  have h₂ := I.t₂_lt
  rcases le_total t I.t₂ with h | h
  · exact ⟨I.rising ⟨le_rfl, h₁.le⟩ ⟨ht.1, h⟩ ht.1, I.rising ⟨ht.1, h⟩ ⟨h₁.le, le_rfl⟩ h⟩
  · refine ⟨?_, I.falling ⟨le_rfl, h₂.le⟩ ⟨h, ht.2⟩ h⟩
    rw [← I.end_eq]
    exact I.falling ⟨h, ht.2⟩ ⟨h₂.le, le_rfl⟩ ht.2

theorem bounds (t : ℝ) : I.umin ≤ I.u t ∧ I.u t ≤ I.umax := by
  obtain ⟨y, hy, hxy⟩ := I.periodic.exists_mem_Ico I.period_pos t I.t₁
  rw [hxy]
  exact I.bounds_on_period ⟨hy.1, hy.2.le⟩

/-- `∫ y u̇` over a piece where `y` is the constant `c`. -/
theorem integral_piece {y : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hy : ∀ τ ∈ Ioc a b, y τ = c) :
    IntervalIntegrable (fun τ => y τ * I.u' τ) volume a b ∧
      ∫ τ in a..b, y τ * I.u' τ = c * (I.u b - I.u a) := by
  have heq : EqOn (fun τ => c * I.u' τ) (fun τ => y τ * I.u' τ) (uIoc a b) := fun τ hτ => by
    rw [uIoc_of_le hab] at hτ
    simp [hy τ hτ]
  refine ⟨((continuous_const.mul I.continuous_deriv).intervalIntegrable a b).congr heq, ?_⟩
  rw [← intervalIntegral.integral_congr_ae (ae_of_all _ fun τ hτ => heq hτ),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => I.hasDerivAt x)
      (I.continuous_deriv.intervalIntegrable _ _)]


variable {α β : ℝ}

/-- An output that is constant over a period encloses no area. -/
theorem area_of_const {y : ℝ → ℝ} {c : ℝ} (hy : ∀ τ ∈ Ioc I.t₁ (I.t₁ + I.T), y τ = c) :
    IntervalIntegrable (fun τ => y τ * I.u' τ) volume I.t₁ (I.t₁ + I.T) ∧
      signedArea I.u y I.t₁ (I.t₁ + I.T) = 0 := by
  have p := I.integral_piece (by linarith [I.period_pos]) hy
  refine ⟨p.1, ?_⟩
  rw [signedArea, I.deriv_eq, p.2, I.end_eq, umin]
  ring

/-- The last time in `[t₁, t₂]` at which the input is at most `α`. -/
theorem rising_switch (hlo : I.umin ≤ α) (hhi : α < I.umax) :
    ∃ s ∈ Ico I.t₁ I.t₂, I.u s = α ∧ (∀ τ ∈ Icc I.t₁ s, I.u τ ≤ α) ∧
      ∀ τ ∈ Ioc s I.t₂, α < I.u τ := by
  set S := Icc I.t₁ I.t₂ ∩ {τ | I.u τ ≤ α}
  have hS : IsClosed S := isClosed_Icc.inter (isClosed_le I.continuous continuous_const)
  have hbdd : BddAbove S := bddAbove_Icc.mono inter_subset_left
  have hmem := hS.csSup_mem ⟨I.t₁, ⟨le_rfl, I.t₁_lt_t₂.le⟩, hlo⟩ hbdd
  set s := sSup S
  have hgt : ∀ τ ∈ Ioc s I.t₂, α < I.u τ := fun τ hτ => by
    by_contra h
    exact absurd (le_csSup hbdd ⟨⟨hmem.1.1.trans hτ.1.le, hτ.2⟩, not_lt.mp h⟩) (not_le.mpr hτ.1)
  have hlt : s < I.t₂ := lt_of_le_of_ne hmem.1.2 fun h => by
    have := hmem.2; rw [h] at this; exact absurd hhi (not_lt.mpr this)
  have hge : α ≤ I.u s := by
    have hcl : closure (Ioc s I.t₂) ⊆ {τ | α ≤ I.u τ} :=
      closure_minimal (fun τ hτ => (hgt τ hτ).le) (isClosed_le continuous_const I.continuous)
    rw [closure_Ioc hlt.ne] at hcl
    exact hcl ⟨le_rfl, hlt.le⟩
  refine ⟨s, ⟨hmem.1.1, hlt⟩, le_antisymm hmem.2 hge, fun τ hτ => ?_, hgt⟩
  exact (I.rising ⟨hτ.1, hτ.2.trans hlt.le⟩ ⟨hmem.1.1, hlt.le⟩ hτ.2).trans hmem.2

/-- The last time in `[t₂, t₁ + T]` at which the input is at least `β`. -/
theorem falling_switch (hlo : I.umin < β) (hhi : β ≤ I.umax) :
    ∃ s ∈ Ico I.t₂ (I.t₁ + I.T), I.u s = β ∧ (∀ τ ∈ Icc I.t₂ s, β ≤ I.u τ) ∧
      ∀ τ ∈ Ioc s (I.t₁ + I.T), I.u τ < β := by
  set S := Icc I.t₂ (I.t₁ + I.T) ∩ {τ | β ≤ I.u τ}
  have hS : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const I.continuous)
  have hbdd : BddAbove S := bddAbove_Icc.mono inter_subset_left
  have hmem := hS.csSup_mem ⟨I.t₂, ⟨le_rfl, I.t₂_lt.le⟩, hhi⟩ hbdd
  set s := sSup S
  have hlt' : ∀ τ ∈ Ioc s (I.t₁ + I.T), I.u τ < β := fun τ hτ => by
    by_contra h
    exact absurd (le_csSup hbdd ⟨⟨hmem.1.1.trans hτ.1.le, hτ.2⟩, not_lt.mp h⟩) (not_le.mpr hτ.1)
  have hlt : s < I.t₁ + I.T := lt_of_le_of_ne hmem.1.2 fun h => by
    have : β ≤ I.u (I.t₁ + I.T) := h ▸ hmem.2
    rw [I.end_eq] at this; exact absurd hlo (not_lt.mpr this)
  have hle : I.u s ≤ β := by
    have hcl : closure (Ioc s (I.t₁ + I.T)) ⊆ {τ | I.u τ ≤ β} :=
      closure_minimal (fun τ hτ => (hlt' τ hτ).le) (isClosed_le I.continuous continuous_const)
    rw [closure_Ioc hlt.ne] at hcl
    exact hcl ⟨le_rfl, hlt.le⟩
  refine ⟨s, ⟨hmem.1.1, hlt⟩, le_antisymm hle hmem.2, fun τ hτ => ?_, hlt'⟩
  exact hmem.2.trans (I.falling ⟨hτ.1, hτ.2.trans hlt.le⟩ ⟨hmem.1.1, hlt.le⟩ hτ.2)

end ButterflyCharacterization.Domain.Abstractions.SimplePeriodicInput
