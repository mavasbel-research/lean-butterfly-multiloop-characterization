import ButterflyCharacterization.Domain.Services.LoopAnalysisService
import ButterflyCharacterization.Adapters.Outbound.BuiltinEnsembles
import ButterflyCharacterization.Adapters.Outbound.ConsoleTelemetry

/-!
# Command-line driver (inbound adapter)

`butterfly_cli <ensemble> <u_min> <u_max> [samples]`, `butterfly_cli list`.
-/

namespace ButterflyCharacterization.Adapters.Inbound

open ButterflyCharacterization.Domain.Abstractions
open ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Outbound

/-- Parses `[-]digits[.digits]`. -/
def parseFloat? (s : String) : Option Float :=
  let (neg, body) : Bool × String :=
    if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let parts := body.splitOn "."
  let value : Option Float := match parts with
    | [i] => i.toNat?.map Nat.toFloat
    | [i, f] =>
      if f.isEmpty then none else
      match i.toNat?, f.toNat? with
      | some a, some b => some (a.toFloat + b.toFloat / (10 : Float) ^ f.length.toFloat)
      | _, _ => none
    | _ => none
  value.map fun v => if neg then -v else v

def usage : String := "usage: butterfly_cli list | butterfly_cli <ensemble> <u_min> <u_max> [samples]"

def runCli (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for n in ← EnsembleSourcePort.names (m := IO) do IO.println n
    return 0
  | name :: lo :: hi :: rest =>
    let samples? : Option Nat := match rest with
      | [] => some 1000
      | [k] => k.toNat?
      | _ => none
    match parseFloat? lo, parseFloat? hi, samples? with
    | some umin, some umax, some samples =>
      if !(umin < umax) then
        IO.eprintln "u_min must be smaller than u_max"
        return 1
      if samples < 4 then
        IO.eprintln "samples must be at least 4"
        return 1
      let ok ← runAnalysis (m := IO) name umin umax samples
      return if ok then 0 else 1
    | _, _, _ =>
      IO.eprintln usage
      return 1
  | _ =>
    IO.eprintln usage
    return 1

end ButterflyCharacterization.Adapters.Inbound
