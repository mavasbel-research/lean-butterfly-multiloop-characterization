import ButterflyCharacterization.Domain.Abstractions.Ports

/-!
# Loop analysis service (`Float` mirror of the formalized model)

* `relayStep` is eq. (2) for one sample: `+1` if `u > α`, `−1` if `u < β`, else unchanged.
* `simulate` runs every relay over two periods of the cosine input.
* `shoelace` is the signed area (1) of the sampled second period, as a closed polygon.
* `formulaArea` and `crossoverLevels` evaluate the closed forms proved in `Domain.Model`.

Nothing here is proved: `Float` arithmetic rounds, and no error bound links these numbers
to the real-valued theorems. The tests compare them.
-/

namespace ButterflyCharacterization.Domain.Services

open ButterflyCharacterization.Domain.Abstractions

/-- `π` to double precision. -/
def piF : Float := 3.141592653589793

/-- Eq. (2) for one sample. -/
def relayStep (r : RelaySpec) (state u : Float) : Float :=
  if u > r.α then 1 else if u < r.β then -1 else state

/-- The input `(m + M)/2 − (M − m)/2 · cos t`. -/
def input (umin umax t : Float) : Float := (umin + umax) / 2 - (umax - umin) / 2 * Float.cos t

/-- Sample times `0, Δ, …, 2·2π` with `Δ = 2π / samples`. -/
def times (samples : Nat) : List Float :=
  (List.range (2 * samples + 1)).map fun k => 2 * piF * k.toFloat / samples.toFloat

/-- States of one relay along a list of input values (one state per value). -/
def relayTrace (r : RelaySpec) (us : List Float) : List Float :=
  (us.foldl (fun (acc : Float × List Float) u =>
    let s := relayStep r acc.1 u
    (s, s :: acc.2)) (r.r₀, [])).2.reverse

/-- The operator output `Σ wᵢ Rᵢ` along the input values. -/
def outputTrace (e : EnsembleSpec) (us : List Float) : List Float :=
  e.relays.foldl (fun acc r => List.zipWith (· + ·) acc ((relayTrace r us).map (r.w * ·)))
    (us.map fun _ => 0)

/-- Shoelace signed area of the closed polygon through the points. -/
def shoelace : List (Float × Float) → Float
  | [] => 0
  | p :: ps => 0.5 * (((p :: ps).zip (ps ++ [p])).map
      (fun q => q.1.1 * q.2.2 - q.2.1 * q.1.2)).foldl (· + ·) 0

/-- Relays that switch under the input (`u_min < β`, `α < u_max`). -/
def switchingRelays (req : AnalysisRequest) : List RelaySpec :=
  req.ensemble.relays.filter fun r => req.umin < r.β && r.α < req.umax

/-- `2 Σ_{switching} wᵢ (αᵢ − βᵢ)`. -/
def formulaArea (req : AnalysisRequest) : Float :=
  2 * (switchingRelays req).foldl (fun acc r => acc + r.w * (r.α - r.β)) 0

/-- `Σ_{Ω_υ} wᵢ` with `Ω_υ = {i | βᵢ ≤ υ ≤ αᵢ}`. -/
def omegaWeight (e : EnsembleSpec) (υ : Float) : Float :=
  e.relays.foldl (fun acc r => if r.β ≤ υ && υ ≤ r.α then acc + r.w else acc) 0

/-- Interior levels `u_min + k (u_max − u_min)/samples`, `0 < k < samples`, where
`Σ_{Ω_υ} wᵢ = 0`. -/
def crossoverLevels (req : AnalysisRequest) : List Float :=
  ((List.range req.samples).drop 1).filterMap fun k =>
    let υ := req.umin + (req.umax - req.umin) * k.toFloat / req.samples.toFloat
    if omegaWeight req.ensemble υ == 0 then some υ else none

/-- The full analysis. -/
def analyze (req : AnalysisRequest) : LoopReport :=
  let ts := times req.samples
  let us := ts.map (input req.umin req.umax)
  let ys := outputTrace req.ensemble us
  let second := (us.zip ys).drop req.samples
  { ensemble := req.ensemble.name
    umin := req.umin
    umax := req.umax
    samples := req.samples
    switching := (switchingRelays req).length
    formulaArea := formulaArea req
    simulatedArea := shoelace (second.take req.samples)
    crossoverLevels := crossoverLevels req }

/-- The service implements the inbound port in any monad. -/
instance {m : Type → Type} [Monad m] : LoopAnalysisPort m where
  analyze req := pure (analyze req)

/-- Application use case: look the ensemble up, analyse, publish. -/
def runAnalysis {m : Type → Type} [Monad m] [LoopAnalysisPort m] [EnsembleSourcePort m]
    [TelemetryPort m] (name : String) (umin umax : Float) (samples : Nat) : m Bool := do
  match ← EnsembleSourcePort.find name with
  | none =>
    TelemetryPort.info s!"unknown ensemble: {name}"
    return false
  | some e =>
    let r ← LoopAnalysisPort.analyze { ensemble := e, umin, umax, samples }
    TelemetryPort.report r
    return true

end ButterflyCharacterization.Domain.Services
