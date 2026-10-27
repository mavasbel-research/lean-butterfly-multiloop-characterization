import ButterflyCharacterization.Domain.Abstractions.Ports

/-!
# Built-in ensembles (outbound adapter for `EnsembleSourcePort`)

`Float` copies of the ensembles whose properties are proved in `Domain.Model.Butterfly`:

| name | Lean (ℝ) counterpart |
|---|---|
| `two-relay` | `twoRelay`: butterfly and multiloop operator |
| `reflected-pair` | `reflectedPair`: antisymmetric about `α + β = 1` (Corollary 3.4) |
| `positive` | the first relay of `twoRelay` alone (weight `+1`, §III: counterclockwise) |
-/

namespace ButterflyCharacterization.Adapters.Outbound

open ButterflyCharacterization.Domain.Abstractions

def builtinEnsembles : List EnsembleSpec :=
  [ { name := "two-relay"
      relays := [⟨0.5, -0.5, 1, 1⟩, ⟨0.6, -0.4, -1, 1⟩] },
    { name := "reflected-pair"
      relays := [⟨1, -1, 1, 1⟩, ⟨2, 0, -1, 1⟩] },
    { name := "positive"
      relays := [⟨0.5, -0.5, 1, 1⟩] } ]

instance : EnsembleSourcePort IO where
  names := pure (builtinEnsembles.map (·.name))
  find n := pure (builtinEnsembles.find? (·.name == n))

end ButterflyCharacterization.Adapters.Outbound
