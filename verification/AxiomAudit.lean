import IQGTCore
/-!
Axiom audit: every declaration in the `IQGT` namespace may depend only on the three standard
axioms `propext`, `Classical.choice`, `Quot.sound`. Any `sorryAx` or user axiom fails this file.
-/
open Lean Elab Command

elab "#audit_iqgt" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    if (`IQGT).isPrefixOf n && !n.isInternal then
      count := count + 1
      let axs ← liftCoreM <| Lean.collectAxioms n
      for a in axs do
        unless ok.contains a do bad := bad.push (n, a)
  logInfo m!"IQGT axiom audit: {count} declarations checked, {bad.size} problems"
  unless bad.isEmpty do
    throwError m!"non-standard axioms found: {bad.toList}"

#audit_iqgt
