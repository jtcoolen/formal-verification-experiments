/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat
import Lean.Elab.Command

/-!
# ProtSat axiom audit

Rather than listing theorem names by hand (which silently rots as the library grows),
this walks every theorem in the ProtSat namespace in the imported environment and
reports any axiom other than Lean's three standard proof-theoretic axioms.

The point of the check: sorryAx would mean a proof is missing, and a user-declared
axiom would mean a proof was assumed.  Neither is acceptable here - the value of the
development is that the correspondence between symbolic attacks and satisfying
assignments is *proved*.

Run with:

    lake env lean Axioms.lean
-/

open Lean Elab Command

/-- The axioms we allow, spelled out so the check cannot silently widen. -/
private def allowed : List Name :=
  [Name.mkSimple "propext", Name.mkStr (Name.mkSimple "Classical") "choice",
   Name.mkStr (Name.mkSimple "Quot") "sound"]

/-- The root namespace to audit. -/
private def root : Name := Name.mkSimple "ProtSat"

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut flagged : Array (Name × Name) := #[]
  for (nm, ci) in env.constants.toList do
    if !root.isPrefixOf nm then continue
    match ci with
    | .thmInfo _ => pure ()
    | _ => continue
    count := count + 1
    let axioms ← liftCoreM <| collectAxioms nm
    for a in axioms do
      if !allowed.contains a then
        flagged := flagged.push (nm, a)
  logInfo m!"theorems audited in ProtSat.*: {count}"
  if flagged.isEmpty then
    logInfo "OK - every theorem depends only on propext, Classical.choice, Quot.sound"
    logInfo "    (no sorryAx, no user-declared axioms)"
  else
    for (nm, a) in flagged do
      logError m!"{nm} depends on {a}"
