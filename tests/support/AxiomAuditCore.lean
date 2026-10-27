import Lean

/-!
# Axiom audit core

`AxiomAuditCore.audit` fails the elaboration of the file it runs in unless every checked
declaration depends only on Lean's three standard axioms. A `sorry` shows up as
`sorryAx`; an `axiom` someone added shows up under its own name.

It checks every non-internal constant of every imported module whose name starts with
`pre`, plus every constant declared in the current file. It reports how many it checked,
so the count can be compared with the number of declarations in those modules.
-/

open Lean Elab Command

namespace AxiomAuditCore

/-- The axioms a classical Mathlib proof may use. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Non-internal constants of the imported modules under `pre`, and how many modules. -/
def importedUnder (pre : Name) : CommandElabM (Array Name × Nat) := do
  let env ← getEnv
  let mut names : Array Name := #[]
  let mut modules : Nat := 0
  for i in [0:env.header.moduleNames.size] do
    unless pre.isPrefixOf env.header.moduleNames[i]! do continue
    modules := modules + 1
    for name in env.header.moduleData[i]!.constNames do
      unless name.isInternal do names := names.push name
  return (names, modules)

/-- Non-internal constants declared in the file being elaborated. -/
def declaredHere : CommandElabM (Array Name) := do
  let env ← getEnv
  return env.constants.map₂.foldl (init := #[]) fun acc name _ =>
    if name.isInternal then acc else acc.push name

/-- Each name that uses an axiom outside `standardAxioms`, with those axioms. -/
def offenders (names : Array Name) : CommandElabM (Array (Name × List Name)) := do
  let mut found : Array (Name × List Name) := #[]
  for name in names do
    let axioms ← liftCoreM <| collectAxioms name
    let extra := axioms.toList.filter (fun a => !standardAxioms.contains a)
    unless extra.isEmpty do found := found.push (name, extra)
  return found

/-- Fail unless every declaration under `pre` (and in this file) uses standard axioms only.
`minModules` guards against a misspelt prefix silently checking nothing. -/
def audit (pre : Name) (minModules : Nat) : CommandElabM Unit := do
  let (imported, modules) ← importedUnder pre
  if modules < minModules then
    throwError m!"expected at least {minModules} modules under {pre}, found {modules}"
  let names := imported ++ (← declaredHere)
  let bad ← offenders names
  unless bad.isEmpty do
    throwError m!"declarations using non-standard axioms: {bad.toList}"
  logInfo m!"axiom audit: {names.size} declarations in {modules} modules, all standard"

end AxiomAuditCore
