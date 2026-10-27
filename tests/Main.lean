import tests.component.TestAdapters
import tests.live.TestCli
import tests.e2e.TestParity

/-!
# Test runner

Build-time unit tier (`lake build Tests`): `tests/unit/AxiomAudit.lean`,
`tests/unit/TestStatements.lean`, `tests/unit/TestService.lean`.
Run-time tiers (`lake exe run_tests`, after `lake build butterfly_cli`): component, live, e2e.
-/

def main : IO UInt32 := do
  let c ← Tests.Component.run
  let l ← Tests.Live.run
  let e ← Tests.E2E.run
  if c && l && e then
    IO.println "ALL RUN-TIME TIERS PASSED (component, live, e2e)"
    return 0
  else
    IO.println "FAILURES (see FAIL lines above)"
    return 1
