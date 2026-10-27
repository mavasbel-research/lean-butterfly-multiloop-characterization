import ButterflyCharacterization.Domain.Model.Relay
import ButterflyCharacterization.Domain.Model.SignedArea

/-!
# Lemma 3.1 and Remark 3.2: the signed area of a relay loop

For the counterclockwise relay (2), `α > β`, and a simple periodic input, the loop area over
one period `[t₁, t₁ + T]` with `t₁ ≥ T` is `2(α − β)` if `u_min < β` and `u_max > α`, and
`0` otherwise. The proof follows the relay through the four pieces of the period on which
its output is constant and integrates `y u̇` on each.
-/

open Set MeasureTheory Filter Topology
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

variable {α β r₀ : ℝ}

/-- Lemma 3.1 together with the integrability of `y u̇` used for linear combinations. -/
theorem lemma3_1_aux (I : SimplePeriodicInput) (hab : β < α) (hT : I.T ≤ I.t₁) :
    IntervalIntegrable (fun τ => ccwRelay α β r₀ I.u τ * I.u' τ) volume I.t₁ (I.t₁ + I.T) ∧
    signedArea I.u (ccwRelay α β r₀ I.u) I.t₁ (I.t₁ + I.T) =
      if I.umin < β ∧ α < I.umax then 2 * (α - β) else 0 := by
  have h12 := I.t₁_lt_t₂
  have h23 := I.t₂_lt
  have h0 := I.start_nonneg
  split_ifs with h
  · obtain ⟨hβ, hα⟩ := h
    obtain ⟨s₁, hs₁, hus₁, hlow₁, hhigh₁⟩ := I.rising_switch (hβ.le.trans hab.le) hα
    obtain ⟨s₂, hs₂, hus₂, hhigh₂, hlow₂⟩ := I.falling_switch hβ (hab.le.trans hα.le)
    have p1 := I.integral_piece (y := ccwRelay α β r₀ I.u) (c := -1) hs₁.1 fun τ hτ => by
      have hd : SwitchedDown α β I.u τ := ⟨I.t₁, ⟨h0, hτ.1.le⟩, hβ, fun r hr =>
        hlow₁ r ⟨hr.1, hr.2.trans hτ.2⟩⟩
      have hn : ¬ SwitchedUp α β I.u τ := fun hu => not_up_and_down ⟨hu, hd⟩
      simp [ccwRelay, hd, hn]
    have p2 := I.integral_piece (y := ccwRelay α β r₀ I.u) (c := 1) hs₁.2.le fun τ hτ =>
      ccwRelay_of_gt hab (h0.trans (hs₁.1.trans hτ.1.le)) (hhigh₁ τ hτ)
    have p3 := I.integral_piece (y := ccwRelay α β r₀ I.u) (c := 1) hs₂.1 fun τ hτ => by
      have hu : SwitchedUp α β I.u τ := ⟨I.t₂, ⟨by linarith, hτ.1.le⟩, hα, fun r hr =>
        hhigh₂ r ⟨hr.1, hr.2.trans hτ.2⟩⟩
      simp [ccwRelay, hu]
    have p4 := I.integral_piece (y := ccwRelay α β r₀ I.u) (c := -1) hs₂.2.le fun τ hτ =>
      ccwRelay_of_lt hab (by linarith [hs₂.1, hτ.1]) (hlow₂ τ hτ)
    refine ⟨p1.1.trans (p2.1.trans (p3.1.trans p4.1)), ?_⟩
    rw [signedArea, I.deriv_eq, ← intervalIntegral.integral_add_adjacent_intervals p1.1
      (p2.1.trans (p3.1.trans p4.1)), ← intervalIntegral.integral_add_adjacent_intervals p2.1
      (p3.1.trans p4.1), ← intervalIntegral.integral_add_adjacent_intervals p3.1 p4.1,
      p1.2, p2.2, p3.2, p4.2, hus₁, hus₂, I.end_eq]
    simp only [SimplePeriodicInput.umin]
    ring
  · by_cases hβ : I.umin < β
    · have hα : I.umax ≤ α := not_lt.mp fun hα => h ⟨hβ, hα⟩
      refine I.area_of_const (c := -1) fun τ hτ => ?_
      have hd : SwitchedDown α β I.u τ := ⟨I.t₁, ⟨h0, hτ.1.le⟩, hβ, fun r _ =>
        (I.bounds r).2.trans hα⟩
      have hn : ¬ SwitchedUp α β I.u τ := fun hu => not_up_and_down ⟨hu, hd⟩
      simp [ccwRelay, hd, hn]
    · have hβ : β ≤ I.umin := not_lt.mp hβ
      by_cases hα : α < I.umax
      · refine I.area_of_const (c := 1) fun τ hτ => ?_
        have hs : I.u (I.t₂ - I.T) = I.umax := I.periodic.sub_eq I.t₂
        have hu : SwitchedUp α β I.u τ := ⟨I.t₂ - I.T, ⟨by linarith, by linarith [hτ.1]⟩,
          hs ▸ hα, fun r _ => hβ.trans (I.bounds r).1⟩
        simp [ccwRelay, hu]
      · have hα : I.umax ≤ α := not_lt.mp hα
        refine I.area_of_const (c := ccwRelay α β r₀ I.u 0) fun τ hτ =>
          ccwRelay_memory (by linarith [hτ.1]) fun r _ =>
            ⟨hβ.trans (I.bounds r).1, (I.bounds r).2.trans hα⟩

/-- **Lemma 3.1** (TAC 2022). For the counterclockwise relay (2) with `α > β` and a simple
periodic input, the signed area of one period `[t₁, t₁ + T]` with `t₁ ≥ T` (after the first
period, `t_p = T` as in the paper's proof) is `2(α − β)` if `u_min < β` and `u_max > α`,
and `0` otherwise. -/
theorem lemma3_1 (I : SimplePeriodicInput) (hab : β < α) (hT : I.T ≤ I.t₁) :
    signedArea I.u (ccwRelay α β r₀ I.u) I.t₁ (I.t₁ + I.T) =
      if I.umin < β ∧ α < I.umax then 2 * (α - β) else 0 :=
  (lemma3_1_aux I hab hT).2

theorem relay_integrable (I : SimplePeriodicInput) (hab : β < α) (hT : I.T ≤ I.t₁) :
    IntervalIntegrable (fun τ => ccwRelay α β r₀ I.u τ * I.u' τ) volume I.t₁ (I.t₁ + I.T) :=
  (lemma3_1_aux I hab hT).1

/-- **Remark 3.2.** The clockwise relay (3) encloses `−2(α − β)` under the same conditions. -/
theorem remark3_2 (I : SimplePeriodicInput) (hab : β < α) (hT : I.T ≤ I.t₁) :
    signedArea I.u (cwRelay α β r₀ I.u) I.t₁ (I.t₁ + I.T) =
      if I.umin < β ∧ α < I.umax then -(2 * (α - β)) else 0 := by
  rw [show cwRelay α β r₀ I.u = fun τ => -ccwRelay α β r₀ I.u τ from rfl, signedArea_neg,
    lemma3_1 I hab hT]
  split_ifs <;> simp

end ButterflyCharacterization.Domain.Model
