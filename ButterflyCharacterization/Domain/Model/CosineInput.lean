import ButterflyCharacterization.Domain.Abstractions.Loop

/-!
# A concrete simple periodic input

`u(t) = (m + M)/2 − (M − m)/2 · cos t`, with period `2π`, minimum `m` at `t₁ = 2π` and
maximum `M` at `t₂ = 3π`. The period `[2π, 4π]` starts after one full period, as Lemma 3.1
requires.
-/

open Set Real
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

theorem cos_antitoneOn_shift {x y : ℝ} (hx : x ∈ Icc (2 * π) (3 * π)) (hy : y ∈ Icc (2 * π) (3 * π))
    (hxy : x ≤ y) : cos y ≤ cos x := by
  rw [← cos_sub_two_pi x, ← cos_sub_two_pi y]
  exact strictAntiOn_cos.antitoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith)

theorem cos_monotoneOn_shift {x y : ℝ} (hx : x ∈ Icc (3 * π) (4 * π)) (hy : y ∈ Icc (3 * π) (4 * π))
    (hxy : x ≤ y) : cos x ≤ cos y := by
  have e : ∀ z, cos z = cos (4 * π - z) := fun z => by
    rw [show 4 * π - z = -z + 2 * π + 2 * π by ring, cos_add_two_pi, cos_add_two_pi, cos_neg]
  rw [e x, e y]
  exact strictAntiOn_cos.antitoneOn ⟨by linarith [hy.2], by linarith [hy.1]⟩
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (by linarith)

/-- The input `t ↦ (m + M)/2 − (M − m)/2 · cos t`. -/
noncomputable def cosineInput (m M : ℝ) (hmM : m < M) : SimplePeriodicInput where
  u t := (m + M) / 2 - (M - m) / 2 * cos t
  u' t := (M - m) / 2 * sin t
  T := 2 * π
  t₁ := 2 * π
  t₂ := 3 * π
  period_pos := by positivity
  periodic t := by simp only [cos_add_two_pi]
  hasDerivAt x := by
    have := ((hasDerivAt_cos x).const_mul ((M - m) / 2)).const_sub ((m + M) / 2)
    simpa using this
  continuous_deriv := continuous_const.mul continuous_sin
  start_nonneg := by positivity
  t₁_lt_t₂ := by linarith [pi_pos]
  t₂_lt := by linarith [pi_pos]
  rising x hx y hy hxy := by
    have := cos_antitoneOn_shift hx hy hxy
    have hk : 0 ≤ (M - m) / 2 := by linarith
    simp only
    nlinarith
  falling x hx y hy hxy := by
    have hx' : x ∈ Icc (3 * π) (4 * π) := ⟨hx.1, by linarith [hx.2]⟩
    have hy' : y ∈ Icc (3 * π) (4 * π) := ⟨hy.1, by linarith [hy.2]⟩
    have := cos_monotoneOn_shift hx' hy' hxy
    have hk : 0 ≤ (M - m) / 2 := by linarith
    simp only
    nlinarith

theorem cosineInput_umin (m M : ℝ) (hmM : m < M) : (cosineInput m M hmM).umin = m := by
  simp [SimplePeriodicInput.umin, cosineInput]
  ring

theorem cosineInput_umax (m M : ℝ) (hmM : m < M) : (cosineInput m M hmM).umax = M := by
  have : cos (3 * π) = -1 := by
    rw [show 3 * π = π + 2 * π by ring, cos_add_two_pi, cos_pi]
  simp [SimplePeriodicInput.umax, cosineInput, this]
  ring

end ButterflyCharacterization.Domain.Model
