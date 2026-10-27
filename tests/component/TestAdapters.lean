import ButterflyCharacterization

/-!
# Adapter tests (component tier, run by `lake exe run_tests`)

The outbound adapters through their ports: the built-in ensemble source and the console
report renderer.
-/

namespace Tests.Component

open ButterflyCharacterization.Domain.Abstractions ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Outbound

def check (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"[COMPONENT] {if ok then "PASS" else "FAIL"}: {label}"
  return ok

def run : IO Bool := do
  let names ← EnsembleSourcePort.names (m := IO)
  let c1 ← check "ensemble source lists 3 ensembles"
    (names == ["two-relay", "reflected-pair", "positive"])
  let found ← EnsembleSourcePort.find (m := IO) "two-relay"
  let c2 ← check "two-relay has relays (0.5,-0.5,+1) and (0.6,-0.4,-1)"
    (found.map (·.relays) == some [⟨0.5, -0.5, 1, 1⟩, ⟨0.6, -0.4, -1, 1⟩])
  let missing ← EnsembleSourcePort.find (m := IO) "nope"
  let c3 ← check "unknown ensemble is none" missing.isNone
  let r := analyze { ensemble := builtinEnsembles[2]!, umin := -1, umax := 1, samples := 100 }
  let lines := renderReport r
  let c4 ← check "report has 6 lines naming the ensemble"
    (lines.length == 6 && lines[0]! == "ensemble         : positive")
  return c1 && c2 && c3 && c4

end Tests.Component
