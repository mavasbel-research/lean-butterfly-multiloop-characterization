import ButterflyCharacterization.Domain.Abstractions.Ports

/-!
# Console telemetry (outbound adapter for `TelemetryPort`)
-/

namespace ButterflyCharacterization.Adapters.Outbound

open ButterflyCharacterization.Domain.Abstractions

/-- The report as lines of text. -/
def renderReport (r : LoopReport) : List String :=
  [ s!"ensemble         : {r.ensemble}",
    s!"input            : u_min = {r.umin}, u_max = {r.umax}, {r.samples} samples/period",
    s!"switching relays : {r.switching}",
    s!"area, formula    : {r.formulaArea}   (2 Σ_switching w (α − β), FinitePreisach.area)",
    s!"area, simulated  : {r.simulatedArea}   (shoelace over the 2nd period)",
    s!"crossover levels : {r.crossoverLevels.length} sampled interior levels with Σ_Ω w = 0" ]

instance : TelemetryPort IO where
  info msg := IO.eprintln msg
  report r := (renderReport r).forM IO.println

end ButterflyCharacterization.Adapters.Outbound
