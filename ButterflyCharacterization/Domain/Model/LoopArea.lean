import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import ButterflyCharacterization.Domain.Model.ElementaryRelay
import ButterflyCharacterization.Domain.Abstractions.Loop

namespace ButterflyCharacterization.Domain.Model

noncomputable section

/-!
# Lemma 3.1: Elementary Relay Loop Signed Area
Formal proof of Lemma 3.1 from:
"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"
(IEEE TAC 2022, DOI: 10.1109/TAC.2021.3109533).
-/

/-- Signed loop area enclosed by an elementary relay R_{α,β} under periodic excitation [u_min, u_max].
    If the excitation encloses the threshold band [α, β], the relay traces a full loop.
    For Counterclockwise (α < β): A = 2 * (β - α).
    For Clockwise (α > β): A = -2 * (α - β) = 2 * (β - α).
    If thresholds are not fully enclosed, no switching cycle occurs, so A = 0. -/
def relaySignedArea (r : ElementaryRelay) (ext : ButterflyCharacterization.Domain.Abstractions.LoopExtrema) : ℝ :=
  match r.orientation with
  | RelayOrientation.Counterclockwise =>
      if ext.u_min ≤ r.alpha ∧ r.beta ≤ ext.u_max then
        2 * (r.beta - r.alpha)
      else
        0
  | RelayOrientation.Clockwise =>
      if ext.u_min ≤ r.beta ∧ r.alpha ≤ ext.u_max then
        -2 * (r.alpha - r.beta)
      else
        0

/-- Lemma 3.1 (Part 1): Counterclockwise relay loop signed area is strictly positive
    when the excitation interval encloses the switching thresholds (α < β). -/
theorem lemma3_1_relay_area_ccw_pos
    (alpha beta : ℝ)
    (h_order : alpha < beta)
    (ext : ButterflyCharacterization.Domain.Abstractions.LoopExtrema)
    (h_enclosed : ext.u_min ≤ alpha ∧ beta ≤ ext.u_max) :
    relaySignedArea ⟨alpha, beta, RelayOrientation.Counterclockwise⟩ ext = 2 * (beta - alpha) ∧
    0 < relaySignedArea ⟨alpha, beta, RelayOrientation.Counterclockwise⟩ ext := by
  have h_eq : relaySignedArea ⟨alpha, beta, RelayOrientation.Counterclockwise⟩ ext = 2 * (beta - alpha) := by
    simp [relaySignedArea, h_enclosed]
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have h_diff : 0 < beta - alpha := by linarith
  linarith

/-- Lemma 3.1 (Part 2): Clockwise relay loop signed area is strictly negative
    when the excitation interval encloses the switching thresholds (α > β). -/
theorem lemma3_1_relay_area_cw_neg
    (alpha beta : ℝ)
    (h_order : beta < alpha)
    (ext : ButterflyCharacterization.Domain.Abstractions.LoopExtrema)
    (h_enclosed : ext.u_min ≤ beta ∧ alpha ≤ ext.u_max) :
    relaySignedArea ⟨alpha, beta, RelayOrientation.Clockwise⟩ ext = -2 * (alpha - beta) ∧
    relaySignedArea ⟨alpha, beta, RelayOrientation.Clockwise⟩ ext < 0 := by
  have h_eq : relaySignedArea ⟨alpha, beta, RelayOrientation.Clockwise⟩ ext = -2 * (alpha - beta) := by
    simp [relaySignedArea, h_enclosed]
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have h_diff : 0 < alpha - beta := by linarith
  linarith

/-- Lemma 3.1 (Part 3): Invariance - An unenclosed relay yields exactly zero signed area. -/
theorem lemma3_1_relay_area_unenclosed_zero
    (r : ElementaryRelay)
    (ext : ButterflyCharacterization.Domain.Abstractions.LoopExtrema)
    (h_not_enclosed_ccw : r.orientation = RelayOrientation.Counterclockwise → ¬(ext.u_min ≤ r.alpha ∧ r.beta ≤ ext.u_max))
    (h_not_enclosed_cw : r.orientation = RelayOrientation.Clockwise → ¬(ext.u_min ≤ r.beta ∧ r.alpha ≤ ext.u_max)) :
    relaySignedArea r ext = 0 := by
  rcases r with ⟨alpha, beta, ori⟩
  cases ori with
  | Counterclockwise =>
      dsimp [relaySignedArea]
      have h_not := h_not_enclosed_ccw rfl
      split_ifs with h_enc
      · exact False.elim (h_not h_enc)
      · rfl
  | Clockwise =>
      dsimp [relaySignedArea]
      have h_not := h_not_enclosed_cw rfl
      split_ifs with h_enc
      · exact False.elim (h_not h_enc)
      · rfl

end

end ButterflyCharacterization.Domain.Model
