/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1

/-!
# Axiom audit

Run with `lake exe axioms`.  Every declaration of this development must depend
only on the standard foundational axioms of Lean.  `sorryAx` or any user-declared
axiom appearing below is a bug.
-/

#print axioms VerifiedLL1.Sym.finiteEnum
#print axioms VerifiedLL1.Grammar.wellFormed
#print axioms VerifiedLL1.MatchList.length_eq
#print axioms VerifiedLL1.MatchList.append
#print axioms VerifiedLL1.MatchList.split
#print axioms VerifiedLL1.MatchList.valid_of_mem
#print axioms VerifiedLL1.Valid.subtree_valid
#print axioms VerifiedLL1.derives_ctx
#print axioms VerifiedLL1.derives_append
#print axioms VerifiedLL1.derives_toks_inj
#print axioms VerifiedLL1.matchList_derives
#print axioms VerifiedLL1.valid_derives
#print axioms VerifiedLL1.substitute
#print axioms VerifiedLL1.derives_valid
#print axioms VerifiedLL1.tree_iff_derives
#print axioms VerifiedLL1.Grammar.language_iff_tree
#print axioms VerifiedLL1.valid_leftDerives
#print axioms VerifiedLL1.substitute_left
#print axioms VerifiedLL1.leftDerives_valid
#print axioms VerifiedLL1.tree_iff_leftDerives
#print axioms VerifiedLL1.derives_iff_leftDerives
#print axioms VerifiedLL1.leftDerives_imp_derives
#print axioms VerifiedLL1.Table.sound_of_check
#print axioms VerifiedLL1.parseSym_tok
#print axioms VerifiedLL1.sound_aux
#print axioms VerifiedLL1.parseForest_sound
#print axioms VerifiedLL1.parseSym_sound
#print axioms VerifiedLL1.parse_ok
#print axioms VerifiedLL1.parse_sound
#print axioms VerifiedLL1.Examples.Circuits.M_sound
#print axioms VerifiedLL1.Examples.Circuits.parse_hcx_ok
#print axioms VerifiedLL1.Examples.Circuits.parse_hcx_sound
#print axioms VerifiedLL1.Examples.Circuits.parse_bad_err
#print axioms VerifiedLL1.Examples.Toy.wellFormed
#print axioms VerifiedLL1.Examples.Toy.tree_ab_valid
#print axioms VerifiedLL1.Examples.Toy.not_valid_pb
#print axioms VerifiedLL1.Examples.Toy.not_language_H_a
#print axioms VerifiedLL1.Examples.Loop.M_correct
#print axioms VerifiedLL1.Examples.Loop.not_progressing
#print axioms VerifiedLL1.Examples.Loop.not_cycleFree
#print axioms VerifiedLL1.Examples.Loop.never_accepts_a
#print axioms VerifiedLL1.Examples.Loop.never_accepts_nil
#print axioms VerifiedLL1.Examples.Continuation.not_complete_strong

-- Phase 4
#print axioms VerifiedLL1.Fixpoint.iterP_stable
#print axioms VerifiedLL1.Fixpoint.iterP_closed
#print axioms VerifiedLL1.nullableP_mono
#print axioms VerifiedLL1.nullable_sound
#print axioms VerifiedLL1.nullable_complete
#print axioms VerifiedLL1.nullable_iff
#print axioms VerifiedLL1.nullableSet_iff
#print axioms VerifiedLL1.nullable_eps_tree
#print axioms VerifiedLL1.Examples.Toy.nullableSet_eq
#print axioms VerifiedLL1.Examples.Toy.not_nullable_u

-- Phase 3
#print axioms VerifiedLL1.monotone
#print axioms VerifiedLL1.parseSym_mono
#print axioms VerifiedLL1.parseForest_mono
#print axioms VerifiedLL1.nodeCode_child
#print axioms VerifiedLL1.complete_core
#print axioms VerifiedLL1.complete_of_match
#print axioms VerifiedLL1.language_imp_accepts
#print axioms VerifiedLL1.parse_ok_imp_language
#print axioms VerifiedLL1.never_accepts_of_not_language
#print axioms VerifiedLL1.parse_ok_imp_shape
#print axioms VerifiedLL1.language_iff_accepts

def main : IO Unit := do
  IO.println "The axiom audit above is produced when this module is built."
  IO.println "Re-run it with:  lake env lean Axioms.lean"
  IO.println "No declaration may depend on sorryAx or on a user-declared axiom."
