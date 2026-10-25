import Mathlib.Basic.Real.Basic
import Mathlib.Order.Monotone.Basic

namespace ButterflyCharacterization.Domain.Abstractions

/-!
# Mathematical Foundations: Rate Independence and Causality
Formalization of Definitions 2.1 - 2.4 from:
"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"
(IEEE TAC 2022, DOI: 10.1109/TAC.2021.3109533).
-/

/-- Definition 2.1: Time Transformation.
    A continuous, strictly increasing function φ : ℝ → ℝ with φ(0) = 0. -/
structure TimeTransformation where
  toFun : ℝ → ℝ
  h_zero : toFun 0 = 0
  h_strict_mono : StrictMono toFun

/-- Coercion allowing TimeTransformation to be used as a function. -/
instance : CoeFun TimeTransformation (fun _ => ℝ → ℝ) where
  coe := TimeTransformation.toFun

/-- Rate-Independent Operator (Definition 2.2).
    An operator Φ on signals is rate independent if for any time transformation φ,
    Φ(u ∘ φ) = Φ(u) ∘ φ. -/
def IsRateIndependent (Phi : (ℝ → ℝ) → (ℝ → ℝ)) : Prop :=
  ∀ (u : ℝ → ℝ) (phi : TimeTransformation) (t : ℝ),
    Phi (fun s => u (phi s)) t = Phi u (phi t)

/-- Causal Operator (Definition 2.3).
    An operator Φ is causal if the output up to time τ depends only on the input
    values up to time τ. -/
def IsCausal (Phi : (ℝ → ℝ) → (ℝ → ℝ)) : Prop :=
  ∀ (u₁ u₂ : ℝ → ℝ) (tau : ℝ),
    (∀ t ≤ tau, u₁ t = u₂ t) → (∀ t ≤ tau, Phi u₁ t = Phi u₂ t)

/-- Definition 2.4: Hysteresis Operator.
    An operator Φ is a hysteresis operator if it is both causal and rate independent. -/
structure HysteresisOperator where
  Phi : (ℝ → ℝ) → (ℝ → ℝ)
  h_causal : IsCausal Phi
  h_rate_independent : IsRateIndependent Phi

end ButterflyCharacterization.Domain.Abstractions
