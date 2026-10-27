import Lake
open Lake DSL

package "ButterflyCharacterization" where
  version := v!"0.1.0"
  keywords := #["math", "control", "hysteresis"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.linter.mathlibStandardSet, false⟩
  ]

require "leanprover-community" / "mathlib" @ git "v4.35.0"

@[default_target]
lean_lib «ButterflyCharacterization» where
  roots := #[`ButterflyCharacterization]

lean_lib «Tests» where
  srcDir := "."
  roots := #[
    `tests.support.AxiomAuditCore,
    `tests.unit.AxiomAudit,
    `tests.unit.TestStatements,
    `tests.unit.TestService,
    `tests.component.TestAdapters,
    `tests.live.TestCli,
    `tests.e2e.TestParity
  ]

lean_exe «run_tests» where
  root := `tests.Main

lean_exe «butterfly_cli» where
  root := `ButterflyCharacterization.Main
