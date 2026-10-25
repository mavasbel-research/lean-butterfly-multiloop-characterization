import ButterflyCharacterization.Domain.Abstractions.Ports
import ButterflyCharacterization.Domain.Abstractions.Loop

namespace ButterflyCharacterization.Domain.Services

/-!
# Butterfly and Multiloop Analysis Service
Core domain service implementing analytical detection algorithms for butterfly loops
and crossover manifolds.
-/

/-- Discrete point on a trajectory loop. -/
structure LoopPoint where
  u : Float
  y_pos : Float
  y_neg : Float

/-- Computes numerical signed area of a sampled hysteresis loop using the trapezoidal rule. -/
def computeSampledSignedArea (points : List LoopPoint) : Float :=
  match points with
  | [] => 0.0
  | [_] => 0.0
  | p1 :: p2 :: rest =>
      let du := p2.u - p1.u
      let diff1 := p1.y_neg - p1.y_pos
      let diff2 := p2.y_neg - p2.y_pos
      let areaStep := 0.5 * (diff1 + diff2) * du
      areaStep + computeSampledSignedArea (p2 :: rest)

/-- Detects sign changes (interior crossovers) in the branch difference across adjacent samples. -/
def countSampledCrossovers (points : List LoopPoint) : Nat :=
  match points with
  | [] => 0
  | [_] => 0
  | p1 :: p2 :: rest =>
      let d1 := p1.y_neg - p1.y_pos
      let d2 := p2.y_neg - p2.y_pos
      let crossed := if (d1 > 0.0 && d2 < 0.0) || (d1 < 0.0 && d2 > 0.0) then 1 else 0
      crossed + countSampledCrossovers (p2 :: rest)

/-- Analyzes a sampled trajectory loop to compute metrics and classify butterfly topology. -/
def analyzeSampledLoop (points : List LoopPoint) (areaTol : Float := 0.1) : ButterflyCharacterization.Domain.Abstractions.LoopMetrics :=
  let area := computeSampledSignedArea points
  let crossovers := countSampledCrossovers points
  let hasCross := crossovers > 0
  let isButt := hasCross && (Float.abs area ≤ areaTol)
  { netSignedArea := area
    hasCrossover := hasCross
    crossoverCount := crossovers
    isButterfly := isButt }

end ButterflyCharacterization.Domain.Services
