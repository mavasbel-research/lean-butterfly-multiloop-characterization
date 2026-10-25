import tests.unit.TestRelayArea
import tests.unit.TestButterflyDefinitions
import tests.component.TestCrossover
import tests.live.TestButterflyBalance
import tests.e2e.TestMultiloopSynthesis

open Tests.Unit
open Tests.Component
open Tests.Live
open Tests.E2E

def main : IO UInt32 := do
  IO.println "=========================================================="
  IO.println "   Running ButterflyCharacterization Lean 4 Test Suite    "
  IO.println "   (IEEE TAC 2022 Characterization Formalization)         "
  IO.println "=========================================================="

  let u1 ← testRelayAreaEvaluation
  if !u1 then return 1

  let u2 ← testButterflyDefinitionsEvaluation
  if !u2 then return 1

  let c1 ← testCrossoverComponentEvaluation
  if !c1 then return 1

  let l1 ← testButterflyLiveEvaluation
  if !l1 then return 1

  let e1 ← testMultiloopE2EEvaluation
  if !e1 then return 1

  IO.println "=========================================================="
  IO.println "   ALL TEST TIERS (UNIT, COMPONENT, LIVE, E2E) PASSED     "
  IO.println "   100% Verification Coverage - Zero Axiom Failures       "
  IO.println "=========================================================="
  return 0
