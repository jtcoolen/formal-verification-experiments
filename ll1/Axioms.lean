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
#print axioms VerifiedLL1.firstP_mono
#print axioms VerifiedLL1.firstListTest_sound
#print axioms VerifiedLL1.first_sound
#print axioms VerifiedLL1.first_backwards
#print axioms VerifiedLL1.first_complete
#print axioms VerifiedLL1.first_iff
#print axioms VerifiedLL1.first_eof_iff_nullable

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

-- Phase 4: FIRST at list level
#print axioms VerifiedLL1.firstList_iff
#print axioms VerifiedLL1.Grammar.FirstList.backwards_derives
#print axioms VerifiedLL1.Grammar.FirstList.append_decomp
#print axioms VerifiedLL1.Grammar.FirstList.append_left_of_null

-- Phase 4: REACH
#print axioms VerifiedLL1.occursP_mono
#print axioms VerifiedLL1.occurs_sound
#print axioms VerifiedLL1.occurs_complete
#print axioms VerifiedLL1.occurs_iff
#print axioms VerifiedLL1.occurs_stable
#print axioms VerifiedLL1.not_occurs_of_absent

-- Phase 4: FOLLOW
#print axioms VerifiedLL1.followP_mono
#print axioms VerifiedLL1.follow_sound
#print axioms VerifiedLL1.follow_complete
#print axioms VerifiedLL1.follow_iff
#print axioms VerifiedLL1.follow_eof_iff
#print axioms VerifiedLL1.follow_stable
#print axioms VerifiedLL1.Grammar.followSym_of_reachable
#print axioms VerifiedLL1.Grammar.followSym_start

-- Phase 5: SELECT / LL(1) / generation
#print axioms VerifiedLL1.Grammar.select_iff
#print axioms VerifiedLL1.Grammar.ll1Check_iff
#print axioms VerifiedLL1.Grammar.select_of_derives
#print axioms VerifiedLL1.Grammar.genTable_get
#print axioms VerifiedLL1.Grammar.genTable_sound
#print axioms VerifiedLL1.Grammar.genTable_adequate
#print axioms VerifiedLL1.Grammar.genTable_complete
#print axioms VerifiedLL1.Grammar.genTable_correct
#print axioms VerifiedLL1.Grammar.leftCorner_iff
#print axioms VerifiedLL1.Grammar.lcReach_iff
#print axioms VerifiedLL1.Grammar.noLeftRecursion_iff
#print axioms VerifiedLL1.Grammar.lcRank_lt
#print axioms VerifiedLL1.Grammar.genTable_progressing
#print axioms VerifiedLL1.Grammar.generated_language_iff
#print axioms VerifiedLL1.Grammar.generated_accepts_tree

-- Phase 5 instances
#print axioms VerifiedLL1.Examples.Toy.toy_ll1
#print axioms VerifiedLL1.Examples.Toy.toy_no_left_recursion
#print axioms VerifiedLL1.Examples.Circuits.circ_ll1
#print axioms VerifiedLL1.Examples.Circuits.circ_no_left_recursion
#print axioms VerifiedLL1.Examples.Circuits.gen_parse_empty
#print axioms VerifiedLL1.Examples.Toy.toy_end_to_end
#print axioms VerifiedLL1.Examples.Toy.toy_accepts_ab
#print axioms VerifiedLL1.Examples.Circuits.circ_end_to_end
#print axioms VerifiedLL1.Examples.Circuits.gen_parse_hcx
#print axioms VerifiedLL1.Examples.Loop.loop_not_ll1

def main : IO Unit := do
  IO.println "The axiom audit above is produced when this module is built."
  IO.println "Re-run it with:  lake env lean Axioms.lean"
  IO.println "No declaration may depend on sorryAx or on a user-declared axiom."
