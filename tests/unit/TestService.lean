import ButterflyCharacterization

/-!
# Service tests (unit tier, checked at build time)

Every `Float` service function and the CLI's number parser, pinned with `#guard_msgs` on the
real output.
-/

open ButterflyCharacterization.Domain.Abstractions ButterflyCharacterization.Domain.Services
open ButterflyCharacterization.Adapters.Inbound ButterflyCharacterization.Adapters.Outbound

-- Eq. (2): up above α, down below β, memory on the closed band `[β, α]`, including both
-- endpoints in both states (strict switching).
/-- info: [1.000000, -1.000000, 1.000000, -1.000000, -1.000000, 1.000000] -/
#guard_msgs in
#eval [relayStep ⟨0.5, -0.5, 1, 1⟩ (-1) 0.6, relayStep ⟨0.5, -0.5, 1, 1⟩ 1 (-0.6),
  relayStep ⟨0.5, -0.5, 1, 1⟩ 1 0.5, relayStep ⟨0.5, -0.5, 1, 1⟩ (-1) (-0.5),
  relayStep ⟨0.5, -0.5, 1, 1⟩ (-1) 0.5, relayStep ⟨0.5, -0.5, 1, 1⟩ 1 (-0.5)]

/-- info: [some 1.250000, some (-0.500000), some 3.000000, none, none, none] -/
#guard_msgs in
#eval [parseFloat? "1.25", parseFloat? "-0.5", parseFloat? "3", parseFloat? "x",
  parseFloat? "1.", parseFloat? "-"]

-- `formulaArea` on `[−1, 1]`: two-relay `0`, reflected-pair `0` (no relay switches), positive `2`.
/-- info: [0.000000, 0.000000, 2.000000] -/
#guard_msgs in
#eval builtinEnsembles.map fun e => formulaArea { ensemble := e, umin := -1, umax := 1, samples := 10 }

-- Shoelace: counterclockwise unit square `1`, clockwise `−1`.
/-- info: (1.000000, -1.000000) -/
#guard_msgs in
#eval (shoelace [(0, 0), (1, 0), (1, 1), (0, 1)], shoelace [(0, 0), (0, 1), (1, 1), (1, 0)])

-- `relayTrace` follows the input; `omegaWeight` sums the weights of the bands containing υ.
/-- info: ([-1.000000, 1.000000, 1.000000, -1.000000], 0.000000, -1.000000) -/
#guard_msgs in
#eval (relayTrace ⟨0.5, -0.5, 1, -1⟩ [0, 0.7, 0, -0.7], omegaWeight builtinEnsembles[0]! 0,
  omegaWeight builtinEnsembles[0]! 0.55)
