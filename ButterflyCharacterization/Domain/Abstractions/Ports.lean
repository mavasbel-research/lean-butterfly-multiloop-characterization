/-!
# Ports of the executable analysis (hexagonal architecture)

The theorems live over `ℝ` in `Domain.Model`. The executable side simulates the same finite
Preisach operators with `Float` and reports numbers that can be compared with the theorems'
closed forms. Its boundary:

* inbound `LoopAnalysisPort`: analyse one ensemble under one input;
* outbound `EnsembleSourcePort`: where ensembles come from (built-in catalogue, …);
* outbound `TelemetryPort`: where reports go (console, …).

All three are type classes over a monad, implemented by adapters and wired in `Main`.
-/

namespace ButterflyCharacterization.Domain.Abstractions

/-- One relay `R_{α,β}` (`α > β`) with weight `w` and initial state `r₀`, in `Float`. -/
structure RelaySpec where
  α : Float
  β : Float
  w : Float
  r₀ : Float
  deriving Repr, BEq

/-- A finite Preisach operator, in `Float`. -/
structure EnsembleSpec where
  name : String
  relays : List RelaySpec
  deriving Repr, Inhabited

/-- An analysis request: the input `(m + M)/2 − (M − m)/2 · cos t`, sampled `samples` times
per period, simulated for two periods (the area is taken over the second). -/
structure AnalysisRequest where
  ensemble : EnsembleSpec
  umin : Float
  umax : Float
  samples : Nat
  deriving Repr

/-- The report. `formulaArea` is `2 Σ_{switching} wᵢ (αᵢ − βᵢ)` (`FinitePreisach.area`);
`simulatedArea` is the shoelace area of the simulated second period; `crossoverLevels` are the
sampled interior levels `υ` with `Σ_{Ω_υ} wᵢ = 0` (Lemma 4.4, finite form). -/
structure LoopReport where
  ensemble : String
  umin : Float
  umax : Float
  samples : Nat
  switching : Nat
  formulaArea : Float
  simulatedArea : Float
  crossoverLevels : List Float
  deriving Repr

/-- Inbound port: analyse a request. -/
class LoopAnalysisPort (m : Type → Type) where
  analyze : AnalysisRequest → m LoopReport

/-- Outbound port: look up an ensemble by name. -/
class EnsembleSourcePort (m : Type → Type) where
  names : m (List String)
  find : String → m (Option EnsembleSpec)

/-- Outbound port: publish a report or a message. -/
class TelemetryPort (m : Type → Type) where
  info : String → m Unit
  report : LoopReport → m Unit

end ButterflyCharacterization.Domain.Abstractions
