import Mathlib

/-!
# Hysteresis operators: Definitions 2.1–2.4

IEEE TAC 67(7), 2022, "On the Characterization of Butterfly and Multiloop Hysteresis
Behavior", §II-A. Signals are functions `ℝ → ℝ` read on `ℝ₊ = [0, ∞)`; an operator maps an
input signal to an output signal.
-/

open Set Filter

namespace ButterflyCharacterization.Domain.Abstractions

/-- An operator between signals. -/
abbrev SignalOperator := (ℝ → ℝ) → ℝ → ℝ

/-- **Definition 2.1.** A time transformation: continuous, increasing (nondecreasing, as in
the paper's preliminaries), `φ(0) = 0`, and `φ(t) → ∞`. -/
structure TimeTransformation where
  toFun : ℝ → ℝ
  continuousOn : ContinuousOn toFun (Ici 0)
  monotoneOn : MonotoneOn toFun (Ici 0)
  map_zero : toFun 0 = 0
  tendsto_atTop : Tendsto toFun atTop atTop

/-- **Definition 2.2.** Rate independence: `Φ(u ∘ φ) = Φ(u) ∘ φ` on `ℝ₊`. -/
def IsRateIndependent (Φ : SignalOperator) : Prop :=
  ∀ (u : ℝ → ℝ) (φ : TimeTransformation) (t : ℝ), 0 ≤ t →
    Φ (u ∘ φ.toFun) t = Φ u (φ.toFun t)

/-- **Definition 2.3.** Causality: inputs equal on `[0, τ]` give outputs equal on `[0, τ]`. -/
def IsCausal (Φ : SignalOperator) : Prop :=
  ∀ (u₁ u₂ : ℝ → ℝ) (τ : ℝ), (∀ t ∈ Icc 0 τ, u₁ t = u₂ t) → ∀ t ∈ Icc 0 τ, Φ u₁ t = Φ u₂ t

/-- **Definition 2.4.** A hysteresis operator is causal and rate independent. -/
def IsHysteresisOperator (Φ : SignalOperator) : Prop := IsCausal Φ ∧ IsRateIndependent Φ

end ButterflyCharacterization.Domain.Abstractions
