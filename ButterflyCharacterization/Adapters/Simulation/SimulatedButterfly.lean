import ButterflyCharacterization.Domain.Services.ButterflyAnalysisService

namespace ButterflyCharacterization.Adapters.Simulation

open ButterflyCharacterization.Domain.Services

/-!
# Simulated Butterfly Loop Generators
Computable simulation models of standard hysteresis loops, butterfly loops,
and multiloop systems for validation and testing.
-/

/-- Generates a synthetic Butterfly Loop where ascending and descending branches
    cross at u = 0, creating a symmetric figure-eight with net signed area = 0.
    By symmetry, Area(left lobe) = -Area(right lobe), so Net Area = 0. -/
def generateSymmetricButterfly (u_span : Float := 2.0) (steps : Nat := 100) : List LoopPoint :=
  let du := (2.0 * u_span) / (Float.ofNat steps)
  (List.range (steps + 1)).map fun i =>
    let u := -u_span + (Float.ofNat i) * du
    let lobe := (u * u) - 1.0
    let (y_pos, y_neg) :=
      if u < 0.0 then
        (lobe, -lobe)
      else
        (-lobe, lobe)
    { u := u, y_pos := y_pos, y_neg := y_neg }

/-- Generates a standard Counterclockwise Loop (positive Preisach loop) where
    y_neg(u) > y_pos(u) everywhere in the interior (no crossovers, strictly positive area). -/
def generateStandardCCWLoop (u_span : Float := 2.0) (steps : Nat := 100) : List LoopPoint :=
  let du := (2.0 * u_span) / (Float.ofNat steps)
  (List.range (steps + 1)).map fun i =>
    let u := -u_span + (Float.ofNat i) * du
    let gap := 1.0 - (u * u) / (u_span * u_span)
    let y_pos := u - 0.5 * gap
    let y_neg := u + 0.5 * gap
    { u := u, y_pos := y_pos, y_neg := y_neg }

end ButterflyCharacterization.Adapters.Simulation
