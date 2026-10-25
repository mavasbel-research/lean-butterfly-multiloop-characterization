import ButterflyCharacterization.Domain.Abstractions.Ports

namespace ButterflyCharacterization.Adapters.Outbound

open ButterflyCharacterization.Domain.Abstractions

/-!
# Console Telemetry Adapter
Implements ITelemetryPort to emit structured telemetry and analysis metrics to standard output.
-/

structure ConsoleTelemetry where

def logInfo (msg : String) : IO Unit :=
  IO.println s!"[BUTTERFLY-TELEMETRY] [INFO] {msg}"

def logMetric (name : String) (val : Float) : IO Unit :=
  IO.println s!"[BUTTERFLY-TELEMETRY] [METRIC] {name} = {val}"

instance : ITelemetryPort IO where
  logInfo := logInfo
  logMetric := logMetric

end ButterflyCharacterization.Adapters.Outbound
