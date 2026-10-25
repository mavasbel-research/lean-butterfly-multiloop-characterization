import ButterflyCharacterization.Domain.Services.ButterflyAnalysisService
import ButterflyCharacterization.Adapters.Simulation.SimulatedButterfly

namespace Tests.Live

open ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Simulation

def testButterflyLiveEvaluation : IO Bool := do
  IO.println "=== [LIVE TEST] Butterfly Loop Zero-Area Balance (Theorem 3.3) ==="

  -- Generate high-resolution symmetric butterfly loop
  let butterflyPoints := generateSymmetricButterfly 2.0 200
  let metrics := analyzeSampledLoop butterflyPoints 0.05

  IO.println s!"✓ Sampled Butterfly Net Area: {metrics.netSignedArea}"
  IO.println s!"✓ Sampled Crossovers: {metrics.crossoverCount}"

  if !metrics.hasCrossover then
    IO.println "[LIVE] FAIL: Expected crossover detection in butterfly loop"
    return false

  if Float.abs metrics.netSignedArea > 0.05 then
    IO.println s!"[LIVE] FAIL: Net area {metrics.netSignedArea} exceeds tolerance"
    return false

  if !metrics.isButterfly then
    IO.println "[LIVE] FAIL: Loop not classified as butterfly"
    return false

  -- Contrast with standard CCW loop: must have NO crossovers and strictly positive area
  let ccwPoints := generateStandardCCWLoop 2.0 200
  let ccwMetrics := analyzeSampledLoop ccwPoints 0.01

  IO.println s!"✓ Standard CCW Loop Net Area: {ccwMetrics.netSignedArea}"
  if ccwMetrics.hasCrossover then
    IO.println "[LIVE] FAIL: Standard CCW loop should not have crossovers"
    return false

  if ccwMetrics.netSignedArea ≤ 0.1 then
    IO.println s!"[LIVE] FAIL: Expected positive net area for CCW loop, got {ccwMetrics.netSignedArea}"
    return false

  IO.println "✓ Live Butterfly Zero-Area Balance: PASSED (3/3 checks)"
  return true

end Tests.Live
