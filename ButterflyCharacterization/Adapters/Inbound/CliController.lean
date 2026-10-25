import ButterflyCharacterization.Domain.Abstractions.Ports
import ButterflyCharacterization.Domain.Services.ButterflyAnalysisService
import ButterflyCharacterization.Adapters.Simulation.SimulatedButterfly
import ButterflyCharacterization.Adapters.Outbound.ConsoleTelemetry

namespace ButterflyCharacterization.Adapters.Inbound

open ButterflyCharacterization.Domain.Abstractions
open ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Simulation
open ButterflyCharacterization.Adapters.Outbound

/-!
# Inbound CLI Controller
Handles command line interaction, trajectory analysis requests, and output formatting.
-/

/-- Float parser from string. -/
def parseFloatD (s : String) (dflt : Float) : Float :=
  match s.splitOn "." with
  | [intPart] =>
    match intPart.toNat? with
    | some n => Float.ofNat n
    | none => dflt
  | [intPart, fracPart] =>
    match intPart.toNat?, fracPart.toNat? with
    | some i, some f =>
      let len := fracPart.length
      let rec pow10 (k : Nat) : Float :=
        match k with
        | 0 => 1.0
        | k + 1 => 10.0 * pow10 k
      Float.ofNat i + (Float.ofNat f) / pow10 len
    | _, _ => dflt
  | _ => dflt

def runCliAnalysis (mode : String) (u_span : Float := 2.0) (steps : Nat := 100) : IO UInt32 := do
  logInfo s!"Executing Butterfly Loop Analysis: mode={mode}, span={u_span}, steps={steps}"
  let points :=
    if mode == "standard" then
      generateStandardCCWLoop u_span steps
    else
      generateSymmetricButterfly u_span steps

  let metrics := analyzeSampledLoop points
  IO.println "=========================================================="
  IO.println s!"   Loop Classification Results (IEEE TAC 2022 Characterization)"
  IO.println "=========================================================="
  IO.println s!"Net Signed Area A:       {metrics.netSignedArea}"
  IO.println s!"Has Crossovers:          {metrics.hasCrossover}"
  IO.println s!"Interior Crossover Count:{metrics.crossoverCount}"
  IO.println s!"Is Butterfly Loop:       {metrics.isButterfly}"
  IO.println "=========================================================="
  return 0

def runCli (args : List String) : IO UInt32 := do
  match args with
  | [] => runCliAnalysis "butterfly" 2.0 100
  | [mode] => runCliAnalysis mode 2.0 100
  | mode :: spanStr :: [] =>
      let span := parseFloatD spanStr 2.0
      runCliAnalysis mode span 100
  | mode :: spanStr :: stepsStr :: _ =>
      let span := parseFloatD spanStr 2.0
      let steps := stepsStr.toNat?.getD 100
      runCliAnalysis mode span steps

end ButterflyCharacterization.Adapters.Inbound
