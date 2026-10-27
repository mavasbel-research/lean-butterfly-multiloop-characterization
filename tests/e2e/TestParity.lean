import ButterflyCharacterization

/-!
# Parity tests (e2e tier, run by `lake exe run_tests`)

The full use case `runAnalysis` through all three ports with the real adapters, then two
parities for every case:

1. `formulaArea` (Float) equals the value **proved in Lean** for the same operator and input
   (`twoRelay_loopArea`, `corollary3_4_paper_input_counterexample`,
   `corollary3_4_symmetric_input`, `singleRelay_area` in `tests/unit/TestStatements.lean`);
2. the simulated shoelace area approaches it: error ≤ 0.02 at 1000 samples, and smaller than
   at 100 samples unless both are ≤ 1e-9.
-/

namespace Tests.E2E

open ButterflyCharacterization.Domain.Abstractions ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Outbound

def check (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"[E2E] {if ok then "PASS" else "FAIL"}: {label}"
  return ok

/-- (ensemble, u_min, u_max, value proved in Lean, Lean theorem). -/
def cases : List (String × Float × Float × Float × String) :=
  [ ("two-relay", -1, 1, 0, "twoRelay_loopArea"),
    ("reflected-pair", -0.5, 2.5, -4, "corollary3_4_paper_input_counterexample"),
    ("reflected-pair", -2, 3, 0, "corollary3_4_symmetric_input"),
    ("positive", -1, 1, 2, "singleRelay_area") ]

def run : IO Bool := do
  let ok ← runAnalysis (m := IO) "two-relay" (-1) 1 200
  let mut all ← check "runAnalysis through the ports returns true" ok
  let bad ← runAnalysis (m := IO) "nope" (-1) 1 200
  all := (← check "runAnalysis on an unknown ensemble returns false" (!bad)) && all
  for (name, lo, hi, proved, thm) in cases do
    match builtinEnsembles.find? (·.name == name) with
    | none => all := (← check s!"ensemble {name} exists" false) && all
    | some e =>
      let r100 := analyze { ensemble := e, umin := lo, umax := hi, samples := 100 }
      let r1000 := analyze { ensemble := e, umin := lo, umax := hi, samples := 1000 }
      let err100 := Float.abs (r100.simulatedArea - proved)
      let err1000 := Float.abs (r1000.simulatedArea - proved)
      all := (← check s!"{name} [{lo}, {hi}]: formula area = {proved} ({thm})"
        (r1000.formulaArea == proved)) && all
      all := (← check s!"{name} [{lo}, {hi}]: simulated error {err100} → {err1000}"
        (err1000 ≤ 0.02 && (err1000 < err100 || err100 ≤ 1e-9))) && all
  return all

end Tests.E2E
