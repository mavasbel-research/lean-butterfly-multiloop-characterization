import ButterflyCharacterization.Domain.Model.Relay
import ButterflyCharacterization.Domain.Model.SignedArea

/-!
# Every relay over one period

For a simple periodic input and a period `[t₁, t₁ + T]` with `T ≤ t₁` (after the first
period, as in the proofs of Lemma 3.1 and Theorem 3.3), every relay `R_{α,β}` (`α > β`) has a
closed form in terms of the input level `υ = u(t)`:

* on the ascending branch `[t₁, t₂]`: `relayUp`;
* on the descending branch `[t₂, t₁ + T]`: `relayDown`.

The four kinds of relays are: switching (`u_min < β`, `α < u_max`), down-only
(`u_min < β`, `u_max ≤ α`: output `−1`), up-only (`β ≤ u_min`, `α < u_max`: output `+1`),
and never-switching (`β ≤ u_min`, `u_max ≤ α`: output frozen at its value at `t = 0`).
The output is `T`-periodic from `t₁`.
-/

open Set
open ButterflyCharacterization.Domain.Abstractions

namespace ButterflyCharacterization.Domain.Model

variable (I : SimplePeriodicInput) (α β r₀ : ℝ)

/-- Relay output on the ascending branch at input level `υ`. -/
noncomputable def relayUp (υ : ℝ) : ℝ :=
  if α < υ then 1 else if I.umin < β then -1 else if α < I.umax then 1
  else ccwRelay α β r₀ I.u 0

/-- Relay output on the descending branch at input level `υ`. -/
noncomputable def relayDown (υ : ℝ) : ℝ :=
  if υ < β then -1 else if α < I.umax then 1 else if I.umin < β then -1
  else ccwRelay α β r₀ I.u 0

variable {I α β r₀}

theorem relay_rising (hab : β < α) (hT : I.T ≤ I.t₁) {t : ℝ} (ht : t ∈ Icc I.t₁ I.t₂) :
    ccwRelay α β r₀ I.u t = relayUp I α β r₀ (I.u t) := by
  have h0 : 0 ≤ t := I.start_nonneg.trans ht.1
  unfold relayUp
  split_ifs with h1 h2 h3
  · exact ccwRelay_of_gt hab h0 h1
  · have hd : SwitchedDown α β I.u t := ⟨I.t₁, ⟨I.start_nonneg, ht.1⟩, h2,
      fun r hr => (I.rising ⟨hr.1, hr.2.trans ht.2⟩ ⟨ht.1, ht.2⟩ hr.2).trans (not_lt.mp h1)⟩
    have hn : ¬ SwitchedUp α β I.u t := fun hu => not_up_and_down ⟨hu, hd⟩
    simp [ccwRelay, hd, hn]
  · have hs : I.u (I.t₂ - I.T) = I.umax := I.periodic.sub_eq I.t₂
    have hu : SwitchedUp α β I.u t := ⟨I.t₂ - I.T,
      ⟨by linarith [I.t₁_lt_t₂], by linarith [I.t₂_lt, ht.1, I.period_pos]⟩, hs ▸ h3,
      fun r _ => (not_lt.mp h2).trans (I.bounds r).1⟩
    simp [ccwRelay, hu]
  · exact ccwRelay_memory h0 fun r _ =>
      ⟨(not_lt.mp h2).trans (I.bounds r).1, (I.bounds r).2.trans (not_lt.mp h3)⟩

theorem relay_falling (hab : β < α) {t : ℝ} (ht : t ∈ Icc I.t₂ (I.t₁ + I.T)) :
    ccwRelay α β r₀ I.u t = relayDown I α β r₀ (I.u t) := by
  have h0 : 0 ≤ t := I.start_nonneg.trans (I.t₁_lt_t₂.le.trans ht.1)
  unfold relayDown
  split_ifs with h1 h2 h3
  · exact ccwRelay_of_lt hab h0 h1
  · have hu : SwitchedUp α β I.u t := ⟨I.t₂, ⟨I.start_nonneg.trans I.t₁_lt_t₂.le, ht.1⟩, h2,
      fun r hr => (not_lt.mp h1).trans (I.falling ⟨hr.1, hr.2.trans ht.2⟩ ⟨ht.1, ht.2⟩ hr.2)⟩
    simp [ccwRelay, hu]
  · have hd : SwitchedDown α β I.u t := ⟨I.t₁, ⟨I.start_nonneg, I.t₁_lt_t₂.le.trans ht.1⟩, h3,
      fun r _ => (I.bounds r).2.trans (not_lt.mp h2)⟩
    have hn : ¬ SwitchedUp α β I.u t := fun hu => not_up_and_down ⟨hu, hd⟩
    simp [ccwRelay, hd, hn]
  · exact ccwRelay_memory h0 fun r _ =>
      ⟨(not_lt.mp h3).trans (I.bounds r).1, (I.bounds r).2.trans (not_lt.mp h2)⟩

/-- Every relay's output is `T`-periodic from `t₁` once `T ≤ t₁`. -/
theorem relay_periodic (hT : I.T ≤ I.t₁) {t : ℝ} (ht : I.t₁ ≤ t) :
    ccwRelay α β r₀ I.u (t + I.T) = ccwRelay α β r₀ I.u t := by
  by_cases hβ : I.umin < β
  · exact ccwRelay_periodic I.period_pos.le I.periodic I.start_nonneg hβ ht
  · have hβ : β ≤ I.umin := not_lt.mp hβ
    by_cases hα : α < I.umax
    · have up : ∀ s, I.t₁ ≤ s → ccwRelay α β r₀ I.u s = 1 := fun s hs => by
        have hu : SwitchedUp α β I.u s := ⟨I.t₂ - I.T,
          ⟨by linarith [I.t₁_lt_t₂], by linarith [I.t₂_lt, I.period_pos]⟩,
          (I.periodic.sub_eq I.t₂).symm ▸ hα, fun r _ => hβ.trans (I.bounds r).1⟩
        simp [ccwRelay, hu]
      rw [up t ht, up (t + I.T) (by linarith [I.period_pos])]
    · have hα : I.umax ≤ α := not_lt.mp hα
      have band : ∀ s, 0 ≤ s → ccwRelay α β r₀ I.u s = ccwRelay α β r₀ I.u 0 := fun s hs =>
        ccwRelay_memory hs fun r _ => ⟨hβ.trans (I.bounds r).1, (I.bounds r).2.trans hα⟩
      have h0 : 0 ≤ t := I.start_nonneg.trans ht
      rw [band t h0, band (t + I.T) (by linarith [I.period_pos])]

/-- The branch gap of one relay at level `υ ∈ [u_min, u_max]`: `−2` if the relay switches
and its band `[β, α]` contains `υ`, else `0`. -/
theorem relayUp_sub_relayDown (hab : β < α) {υ : ℝ} (hυ : υ ∈ Icc I.umin I.umax) :
    relayUp I α β r₀ υ - relayDown I α β r₀ υ =
      if I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α then -2 else 0 := by
  have h1 := hυ.1
  have h2 := hυ.2
  unfold relayUp relayDown
  by_cases hβ : I.umin < β <;> by_cases hα : α < I.umax
  · by_cases hu : α < υ
    · have hb : ¬ υ < β := fun h => by linarith
      have hc : ¬ (I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α) := fun h => by linarith [h.2.2.2]
      rw [ite_eq_right hc]; simp only [hu, hb, hβ, hα, ite_true, ite_false]; norm_num
    · by_cases hb : υ < β
      · have hc : ¬ (I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α) := fun h => by linarith [h.2.2.1]
        rw [ite_eq_right hc]; simp only [hu, hb, hβ, hα, ite_true, ite_false]; norm_num
      · have hc : I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α :=
          ⟨hβ, hα, not_lt.mp hb, not_lt.mp hu⟩
        rw [ite_eq_left hc]; simp only [hu, hb, hβ, hα, ite_true, ite_false]; norm_num
  · have hu : ¬ α < υ := fun h => by linarith
    have hc : ¬ (I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α) := fun h => hα h.2.1
    by_cases hb : υ < β <;> (rw [ite_eq_right hc]; simp only [hu, hb, hβ, hα, ite_true, ite_false]) <;> norm_num
  · have hb : ¬ υ < β := fun h => by linarith
    have hc : ¬ (I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α) := fun h => hβ h.1
    by_cases hu : α < υ <;> (rw [ite_eq_right hc]; simp only [hu, hb, hβ, hα, ite_true, ite_false]) <;> norm_num
  · have hb : ¬ υ < β := fun h => by linarith
    have hu : ¬ α < υ := fun h => by linarith
    have hc : ¬ (I.umin < β ∧ α < I.umax ∧ β ≤ υ ∧ υ ≤ α) := fun h => hβ h.1
    rw [ite_eq_right hc]; simp only [hu, hb, hβ, hα, ite_false]; norm_num

end ButterflyCharacterization.Domain.Model
