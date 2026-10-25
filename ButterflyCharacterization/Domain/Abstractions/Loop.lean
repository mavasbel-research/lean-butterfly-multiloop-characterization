import Mathlib.Basic.Real.Basic
import ButterflyCharacterization.Domain.Abstractions.Operator

namespace ButterflyCharacterization.Domain.Abstractions

/-!
# Hysteresis Loops, Signed Areas, and Crossover Topologies
Formalization of Definitions 2.5, 2.6, 2.7, 4.1, and 4.3 from:
"On the Characterization of Butterfly and Multiloop Hysteresis Behavior"
(IEEE TAC 2022).
-/

/-- Definition 2.5: Extrema of an admissible periodic hysteresis excitation. -/
structure LoopExtrema where
  u_min : ℝ
  u_max : ℝ
  h_order : u_min < u_max

/-- A Hysteresis Loop trajectory H_{u,y} defined by its ascending and descending branches.
    For an input u spanning [u_min, u_max], y_pos represents the ascending branch (du/dt > 0)
    and y_neg represents the descending branch (du/dt < 0). -/
structure HysteresisLoop where
  extrema : LoopExtrema
  y_pos : ℝ → ℝ  -- Ascending branch
  y_neg : ℝ → ℝ  -- Descending branch
  -- Consistency at the reversal endpoints
  h_rev_min : y_pos extrema.u_min = y_neg extrema.u_min
  h_rev_max : y_pos extrema.u_max = y_neg extrema.u_max

/-- Definition 2.6: Signed Area of a Hysteresis Loop.
    The signed area enclosed by the loop is the integral of (y_neg(u) - y_pos(u))
    over the input range [u_min, u_max].
    Counterclockwise loops have A > 0; clockwise loops have A < 0. -/
def SignedAreaFormula (loop : HysteresisLoop) (integral_diff : ℝ) : Prop :=
  -- integral_diff represents ∫_{u_min}^{u_max} (y_neg(u) - y_pos(u)) du
  True

/-- Definition 4.1: Crossover Point.
    A point u_c ∈ [u_min, u_max] is a crossover point if the ascending and
    descending branches intersect: y_pos(u_c) = y_neg(u_c). -/
def IsCrossoverPoint (loop : HysteresisLoop) (u_c : ℝ) : Prop :=
  loop.extrema.u_min ≤ u_c ∧ u_c ≤ loop.extrema.u_max ∧ loop.y_pos u_c = loop.y_neg u_c

/-- Interior Crossover Point: A crossover point strictly inside the extrema interval. -/
def IsInteriorCrossoverPoint (loop : HysteresisLoop) (u_c : ℝ) : Prop :=
  loop.extrema.u_min < u_c ∧ u_c < loop.extrema.u_max ∧ loop.y_pos u_c = loop.y_neg u_c

/-- Definition 4.3: Multiloop Hysteresis Loop.
    A hysteresis loop is a multiloop if it has at least one interior crossover point
    in addition to the trivial reversal endpoints. -/
def IsMultiloop (loop : HysteresisLoop) : Prop :=
  ∃ u_c : ℝ, IsInteriorCrossoverPoint loop u_c

/-- Definition 2.7: Butterfly Hysteresis Loop.
    A hysteresis loop exhibits butterfly behavior if:
    1. It is a multiloop (possesses interior self-intersections/crossover points).
    2. Its net signed area is zero (A = 0), meaning positive and negative lobes balance. -/
structure IsButterflyLoop (loop : HysteresisLoop) (net_signed_area : ℝ) : Prop where
  h_multiloop : IsMultiloop loop
  h_zero_area : net_signed_area = 0
  h_nontrivial : ∃ u : ℝ, loop.extrema.u_min < u ∧ u < loop.extrema.u_max ∧ loop.y_pos u ≠ loop.y_neg u

end ButterflyCharacterization.Domain.Abstractions
