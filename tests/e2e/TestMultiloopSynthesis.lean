import ButterflyCharacterization.Domain.Services.ButterflyAnalysisService
import ButterflyCharacterization.Adapters.Inbound.CliController

namespace Tests.E2E

open ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Inbound

def testMultiloopE2EEvaluation : IO Bool := do
  IO.println "[E2E] Running Multiloop Characterization End-to-End Synthesis..."

  let exitCode1 ← runCliAnalysis "butterfly" 2.0 150
  if exitCode1 != 0 then
    IO.println "[E2E] FAIL: Butterfly CLI execution failed"
    return false

  let exitCode2 ← runCliAnalysis "standard" 2.0 150
  if exitCode2 != 0 then
    IO.println "[E2E] FAIL: Standard CCW CLI execution failed"
    return false

  IO.println "[E2E] Multiloop Characterization Synthesis: PASSED"
  return true

end Tests.E2E
