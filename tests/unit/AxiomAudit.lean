import ButterflyCharacterization
import tests.support.AxiomAuditCore

/-!
# Axiom audit (unit tier)

Fails the build unless every declaration of every `ButterflyCharacterization.*` module uses
only `propext`, `Classical.choice` and `Quot.sound` (no `sorry`, no added axiom, no
`native_decide`). The printed count is every non-internal constant of those modules.
-/

run_cmd AxiomAuditCore.audit `ButterflyCharacterization 15
