import ButterflyCharacterization.Domain.Model.Branches
import ButterflyCharacterization.Domain.Model.CosineInput

/-!
# Butterfly operators: Theorem 3.3 (analytic step), Corollary 3.4, a witness

* `theorem3_3_step_max`, `theorem3_3_step_min`: the two cases of the last step of the proof of
  Theorem 3.3 — the intermediate value theorem applied to the extra area `h(λ)`.
* `corollary3_4`: for a finite Preisach operator whose weights are antisymmetric under the
  reflection about `B = {α + β = κ}`, every hysteresis loop with `u_min + u_max = κ` has zero
  area.
* `corollary3_4_paper_input_counterexample`: the input rule printed in the paper,
  `u_max = −u_min + 2κ`, does not give zero area for such an operator.
* `twoRelay_isButterfly`: a finite Preisach operator that is a butterfly operator
  (Definition 2.7), with every condition of Definitions 2.4, 2.5, 2.7 proved.
-/

open Set Filter Topology Real
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

/-- Proof of Theorem 3.3, case `A₋ > A₊`: the maximum is raised to `λ > α₁`, adding the area
`2 h(λ)` with `h` continuous, `h(α₁) = 0`, `h(λ) → ∞` (from the moment condition (5)). Some
`α₂ ≥ α₁` gives total area `0`. -/
theorem theorem3_3_step_max (Ap Am α₁ : ℝ) (h : ℝ → ℝ) (hc : ContinuousOn h (Ici α₁))
    (h0 : h α₁ = 0) (hinf : Tendsto h atTop atTop) (hdom : Ap < Am) :
    ∃ α₂, α₁ ≤ α₂ ∧ 2 * (Ap - Am) + 2 * h α₂ = 0 := by
  obtain ⟨b, hb⟩ := (tendsto_atTop.mp hinf (Am - Ap)).exists_forall_of_atTop
  have hcα : α₁ ≤ max b α₁ := le_max_right _ _
  have hhc : Am - Ap ≤ h (max b α₁) := hb _ (le_max_left _ _)
  obtain ⟨α₂, ⟨h1, -⟩, hα₂⟩ :=
    intermediate_value_Icc hcα (hc.mono Icc_subset_Ici_self) ⟨by rw [h0]; linarith, hhc⟩
  exact ⟨α₂, h1, by rw [hα₂]; ring⟩

/-- Proof of Theorem 3.3, case `A₊ > A₋`: the minimum is lowered to `λ < β₁`, adding the
area `2 h(λ)` with `h` continuous, `h(β₁) = 0`, `h(λ) → −∞` as `λ → −∞` (from (6)). -/
theorem theorem3_3_step_min (Ap Am β₁ : ℝ) (h : ℝ → ℝ) (hc : ContinuousOn h (Iic β₁))
    (h0 : h β₁ = 0) (hinf : Tendsto h atBot atBot) (hdom : Am < Ap) :
    ∃ β₂, β₂ ≤ β₁ ∧ 2 * (Ap - Am) + 2 * h β₂ = 0 := by
  obtain ⟨b, hb⟩ := (tendsto_atBot.mp hinf (Am - Ap)).exists_forall_of_atBot
  have hcβ : min b β₁ ≤ β₁ := min_le_right _ _
  have hhc : h (min b β₁) ≤ Am - Ap := hb _ (min_le_left _ _)
  obtain ⟨β₂, ⟨-, h2⟩, hβ₂⟩ :=
    intermediate_value_Icc hcβ (hc.mono Icc_subset_Iic_self) ⟨hhc, by rw [h0]; linarith⟩
  exact ⟨β₂, h2, by rw [hβ₂]; ring⟩

namespace FinitePreisach

variable {n : ℕ} (P : FinitePreisach n)

/-- **Corollary 3.4** (finite form). Suppose the relays and weights are antisymmetric under the
reflection `(α, β) ↦ (κ − β, κ − α)` about `B = {α + β = κ}`: an involution `σ` of the relays
with `α_{σ i} = κ − βᵢ`, `β_{σ i} = κ − αᵢ`, `w_{σ i} = −wᵢ`. Then every hysteresis loop whose
input satisfies `u_min + u_max = κ` encloses zero area. -/
theorem corollary3_4 (σ : Equiv.Perm (Fin n)) (κ : ℝ) (hα : ∀ i, P.α (σ i) = κ - P.β i)
    (hβ : ∀ i, P.β (σ i) = κ - P.α i) (hw : ∀ i, P.w (σ i) = -P.w i)
    {I : SimplePeriodicInput} {tp : ℝ} (hl : IsHysteresisLoop P.output I tp)
    (hκ : I.umin + I.umax = κ) : loopArea P.output I = 0 := by
  classical
  rw [P.area I hl]
  set f : Fin n → ℝ := fun i => P.w i * (P.α i - P.β i)
  have hmem : ∀ i, i ∈ P.switching I ↔ σ i ∈ P.switching I := fun i => by
    simp only [switching, Finset.mem_filter, Finset.mem_univ, true_and, hα, hβ]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hS := Finset.sum_equiv σ hmem (f := f) (g := fun j => -f j) fun i _ => by
    simp only [f, hw, hα, hβ]
    ring
  rw [Finset.sum_neg_distrib] at hS
  have : ∑ i ∈ P.switching I, f i = 0 := by linarith
  simp only [f] at this
  rw [this, mul_zero]

end FinitePreisach

/-! ### The input rule printed in Corollary 3.4 -/

/-- Two relays, antisymmetric about `α + β = 1` (`κ = 1`): `(1, −1)` with weight `1` and its
reflection `(2, 0)` with weight `−1`. -/
noncomputable def reflectedPair : FinitePreisach 2 where
  α := ![1, 2]
  β := ![-1, 0]
  ordered i := by fin_cases i <;> norm_num
  w := ![1, -1]
  r₀ := ![1, 1]

theorem reflectedPair_antisymmetric :
    ∀ i, reflectedPair.α (Equiv.swap 0 1 i) = 1 - reflectedPair.β i ∧
      reflectedPair.β (Equiv.swap 0 1 i) = 1 - reflectedPair.α i ∧
      reflectedPair.w (Equiv.swap 0 1 i) = -reflectedPair.w i := by
  intro i
  fin_cases i <;> simp [reflectedPair] <;> norm_num

/-- With the paper's rule `u_max = −u_min + 2κ` (`u_min = −1/2`, `u_max = 5/2`, `κ = 1`) the
loop area is `−4 ≠ 0`. -/
theorem corollary3_4_paper_input_counterexample :
    loopArea reflectedPair.output (cosineInput (-1 / 2) (5 / 2) (by norm_num)) = -4 := by
  classical
  rw [reflectedPair.area_of_late _ (le_refl _), FinitePreisach.switching, cosineInput_umin,
    cosineInput_umax, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [reflectedPair]

/-- With `u_min + u_max = κ` (`u_min = −2`, `u_max = 3`: both relays switch) the same
operator gives zero. -/
theorem corollary3_4_symmetric_input :
    loopArea reflectedPair.output (cosineInput (-2) 3 (by norm_num)) = 0 := by
  classical
  rw [reflectedPair.area_of_late _ (le_refl _), FinitePreisach.switching, cosineInput_umin,
    cosineInput_umax, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [reflectedPair]

/-! ### A butterfly operator -/

/-- Relays `(1/2, −1/2)` with weight `1` and `(3/5, −2/5)` with weight `−1`: equal widths,
opposite weights. -/
noncomputable def twoRelay : FinitePreisach 2 where
  α := ![1 / 2, 3 / 5]
  β := ![-1 / 2, -2 / 5]
  ordered i := by fin_cases i <;> norm_num
  w := ![1, -1]
  r₀ := ![1, 1]

/-- The input `−cos t` (from `−1` to `1`). -/
noncomputable def unitCosine : SimplePeriodicInput := cosineInput (-1) 1 (by norm_num)

theorem twoRelay_allSwitch : twoRelay.AllSwitch unitCosine := by
  intro i
  rw [unitCosine, cosineInput_umin, cosineInput_umax]
  fin_cases i <;> norm_num [twoRelay]

/-- At `υ = 11/20` only the second relay's band contains `υ`. -/
theorem twoRelay_omega : ∑ i ∈ twoRelay.omega (11 / 20), twoRelay.w i = -1 := by
  classical
  rw [FinitePreisach.omega, Finset.sum_filter, Fin.sum_univ_two]
  norm_num [twoRelay]

theorem twoRelay_isHysteresisLoop : IsHysteresisLoop twoRelay.output unitCosine unitCosine.t₁ :=
  FinitePreisach.isHysteresisLoop (υ := 11 / 20) twoRelay_allSwitch
    (by rw [unitCosine, cosineInput_umin, cosineInput_umax]; norm_num)
    (by rw [twoRelay_omega]; norm_num)

theorem twoRelay_loopArea : loopArea twoRelay.output unitCosine = 0 := by
  rw [FinitePreisach.area_allSwitch twoRelay_allSwitch twoRelay_isHysteresisLoop,
    Fin.sum_univ_two]
  norm_num [twoRelay]

/-- **Definition 2.7** is satisfiable by a Preisach-type operator: `twoRelay` is a butterfly
hysteresis operator. -/
theorem twoRelay_isButterfly : IsButterflyOperator twoRelay.output :=
  ⟨twoRelay.output_hysteresis, unitCosine, _, twoRelay_isHysteresisLoop, twoRelay_loopArea⟩

end ButterflyCharacterization.Domain.Model
