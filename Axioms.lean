import Merkle
import Lean.Elab.Command

/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/

-- Axiom audit. Run:
--
--     lake env lean Axioms.lean
--
-- Rather than listing theorem names by hand (which silently rots as the library grows), this
-- walks every theorem in the `Merkle` namespace in the imported environment and reports any
-- axiom other than Lean's two standard proof-irrelevance axioms, `propext` and `Quot.sound`.
--
-- The point of the check: `sorryAx` would mean a proof is missing, and `Classical.choice` would
-- mean a proof quietly used excluded middle or decidability of propositional equality. Neither
-- is acceptable here - the whole value of the library is that the reductions are constructive
-- and the counting bounds are unconditional.

open Lean Elab Command

-- The two axioms we allow, spelled out so the check does not silently widen.
private def allowed : List Name := [``propext, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut flagged : Array (Name × Name) := #[]
  for (nm, ci) in env.constants.toList do
    if !(`Merkle).isPrefixOf nm && !(`Sha3).isPrefixOf nm then continue
    match ci with
    | .thmInfo _ => pure ()
    | _ => continue
    count := count + 1
    let axioms ← liftCoreM <| collectAxioms nm
    for a in axioms do
      if !allowed.contains a then
        flagged := flagged.push (nm, a)
  logInfo m!"theorems audited in Merkle.* / Sha3.*: {count}"
  if flagged.isEmpty then
    logInfo "OK - every theorem depends only on propext and Quot.sound"
    logInfo "      (no sorryAx, no Classical.choice)"
  else
    for (nm, a) in flagged do
      logError m!"{nm} depends on {a}"
