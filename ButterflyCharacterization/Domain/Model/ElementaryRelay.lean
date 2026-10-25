import Mathlib.Basic.Real.Basic
import ButterflyCharacterization.Domain.Abstractions.Loop

namespace ButterflyCharacterization.Domain.Model

noncomputable section

/-!
# Elementary Relay Operators (Counterclockwise and Clockwise)
Models the elementary switching operators R_{α,β} supporting Lemma 3.1 of IEEE TAC 2022.
-/

/-- Relay orientation: Standard counterclockwise (α < β) or inverted clockwise (α > β). -/
inductive RelayOrientation where
  | Counterclockwise
  | Clockwise
  deriving DecidableEq, Repr

/-- Elementary non-ideal relay R_{α, β} with specified threshold order. -/
structure ElementaryRelay where
  alpha : ℝ
  beta : ℝ
  orientation : RelayOrientation

/-- Relay switching state: -1 (negative/off) or +1 (positive/on). -/
inductive RelayState where
  | neg
  | pos
  deriving DecidableEq, Repr

/-- Transition rule for a Counterclockwise relay (α < β).
    u ≤ alpha => drops to -1
    u ≥ beta  => jumps to +1
    alpha < u < beta => retains previous state -/
def transitionCCW (alpha beta : ℝ) (u : ℝ) (s : RelayState) : RelayState :=
  if u ≤ alpha then RelayState.neg
  else if u ≥ beta then RelayState.pos
  else s

/-- Transition rule for a Clockwise relay (α > β).
    u ≥ alpha => drops to -1
    u ≤ beta  => jumps to +1
    beta < u < alpha => retains previous state -/
def transitionCW (alpha beta : ℝ) (u : ℝ) (s : RelayState) : RelayState :=
  if u ≥ alpha then RelayState.neg
  else if u ≤ beta then RelayState.pos
  else s

/-- General transition evaluation based on relay orientation. -/
def transition (r : ElementaryRelay) (u : ℝ) (s : RelayState) : RelayState :=
  match r.orientation with
  | RelayOrientation.Counterclockwise => transitionCCW r.alpha r.beta u s
  | RelayOrientation.Clockwise => transitionCW r.alpha r.beta u s

/-- State converted to numeric value: -1.0 or +1.0. -/
def stateToReal (s : RelayState) : ℝ :=
  match s with
  | RelayState.neg => -1
  | RelayState.pos => 1

end

end ButterflyCharacterization.Domain.Model
