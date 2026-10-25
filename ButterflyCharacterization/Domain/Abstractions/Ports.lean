import ButterflyCharacterization.Domain.Abstractions.Loop

namespace ButterflyCharacterization.Domain.Abstractions

/-!
# Inbound and Outbound Port Interfaces
Hexagonal Ports defining boundary interactions for butterfly loop analysis and detection.
-/

/-- Input specification for loop analysis requests. -/
structure LoopAnalysisRequest where
  u_min : Float
  u_max : Float
  samples : Nat

/-- Output telemetry metrics for analyzed loops. -/
structure LoopMetrics where
  netSignedArea : Float
  hasCrossover : Bool
  crossoverCount : Nat
  isButterfly : Bool

/-- Inbound Port: Interface for requesting butterfly and multiloop characterization. -/
class IButterflyAnalysisPort (m : Type → Type) where
  analyzeLoop : LoopAnalysisRequest → m LoopMetrics

/-- Outbound Port: Telemetry and audit logging. -/
class ITelemetryPort (m : Type → Type) where
  logInfo : String → m Unit
  logMetric : String → Float → m Unit

end ButterflyCharacterization.Domain.Abstractions
