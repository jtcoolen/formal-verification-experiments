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

-- Phase 6: circuit DSL with payloads, AST and printer
#print axioms VerifiedLL1.Examples.QCircuits.qc_ll1
#print axioms VerifiedLL1.Examples.QCircuits.qc_no_left_recursion
#print axioms VerifiedLL1.Examples.QCircuits.qc_end_to_end
#print axioms VerifiedLL1.Examples.QCircuits.valid_progTree
#print axioms VerifiedLL1.Examples.QCircuits.yield_progTree
#print axioms VerifiedLL1.Examples.QCircuits.progOf_progTree
#print axioms VerifiedLL1.Examples.QCircuits.language_printProg
#print axioms VerifiedLL1.Examples.QCircuits.round_trip
#print axioms VerifiedLL1.Examples.QCircuits.accepts_hq1
#print axioms VerifiedLL1.Examples.QCircuits.accepts_hcx


-- Phase 5 addendum: exact-tree completeness, unambiguity, the Ll1-only language theorem
#print axioms VerifiedLL1.Grammar.reachable_append
#print axioms VerifiedLL1.parseForest_success_unique
#print axioms VerifiedLL1.parse_success_unique
#print axioms VerifiedLL1.Grammar.genTable_get_of_select
#print axioms VerifiedLL1.Grammar.generated_parseForest_of_match
#print axioms VerifiedLL1.Grammar.generated_parse_tree
#print axioms VerifiedLL1.Grammar.parseTree_unique
#print axioms VerifiedLL1.Grammar.generated_language_iff_ll1

-- Phase 5.2: LL(1) + reduced => no left recursion
#print axioms VerifiedLL1.Grammar.Productive
#print axioms VerifiedLL1.Grammar.Reduced
#print axioms VerifiedLL1.Grammar.derives_toks_of_reachable
#print axioms VerifiedLL1.HeadSteps.derives
#print axioms VerifiedLL1.HeadSteps.trans
#print axioms VerifiedLL1.Grammar.select_of_first
#print axioms VerifiedLL1.Grammar.FirstList.of_atLookahead
#print axioms VerifiedLL1.headSteps_stop_length_unique
#print axioms VerifiedLL1.headSteps_of_match
#print axioms VerifiedLL1.headSteps_of_leftCorner
#print axioms VerifiedLL1.headSteps_of_lcReach
#print axioms VerifiedLL1.Grammar.noLeftRecursion_aux
#print axioms VerifiedLL1.Grammar.noLeftRecursion_of_ll1
#print axioms VerifiedLL1.Grammar.noLeftRecursion_of_ll1Check

-- Phase 5.2: why the structural hypotheses are needed, and one real instantiation
#print axioms VerifiedLL1.Examples.LeftRecUnreachable.ll1
#print axioms VerifiedLL1.Examples.LeftRecUnreachable.leftrec
#print axioms VerifiedLL1.Examples.LeftRecUnreachable.not_reduced
#print axioms VerifiedLL1.Examples.LeftRecUnproductive.ll1
#print axioms VerifiedLL1.Examples.LeftRecUnproductive.leftrec
#print axioms VerifiedLL1.Examples.LeftRecUnproductive.not_reduced
#print axioms VerifiedLL1.Examples.ToyReduced.toy_reduced
#print axioms VerifiedLL1.Examples.ToyReduced.toy_no_left_recursion_from_ll1

-- Phase 5.2: every shape of left-cycle is detected
#print axioms VerifiedLL1.Examples.DirectLR.direct_lr
#print axioms VerifiedLL1.Examples.DirectLR.direct_not_ll1
#print axioms VerifiedLL1.Examples.IndirectLR.indirect_lr
#print axioms VerifiedLL1.Examples.IndirectLR.indirect_not_ll1
#print axioms VerifiedLL1.Examples.EpsCycleLR.eps_lr
#print axioms VerifiedLL1.Examples.EpsCycleLR.eps_not_ll1
#print axioms VerifiedLL1.Examples.NullPrefixLR.np_lr
#print axioms VerifiedLL1.Examples.NullPrefixLR.np_ll1

-- Phase 5.3: reachable selected cycles are impossible
#print axioms VerifiedLL1.headSteps_lift_derives1
#print axioms VerifiedLL1.headAt_of_derives
#print axioms VerifiedLL1.headSteps_stop_of_first
#print axioms VerifiedLL1.selectedLCPath_trace
#print axioms VerifiedLL1.selLCFirst_uniform_stop
#print axioms VerifiedLL1.selPathF_uniform_stop
#print axioms VerifiedLL1.selPathE_erases
#print axioms VerifiedLL1.noSelPathF_cycle
#print axioms VerifiedLL1.noSelPathE_cycle
#print axioms VerifiedLL1.Grammar.noSelectedLCCycle
#print axioms VerifiedLL1.Grammar.reachableSelectedLCAcyclic
#print axioms VerifiedLL1.Examples.UnreachableSelectedCycle.not_occurs_U
#print axioms VerifiedLL1.Examples.UnreachableSelectedCycle.selLCPath_U_U
#print axioms VerifiedLL1.Examples.UnreachableSelectedCycle.never_parses_b
#print axioms VerifiedLL1.headSteps_stop_length_unique_free
#print axioms VerifiedLL1.Grammar.FirstList.of_atLookahead_free
-- Phase 5.5: the classical LL(1) characterization
#print axioms VerifiedLL1.hole_locate
#print axioms VerifiedLL1.leftDerives_head_of_derives
#print axioms VerifiedLL1.classical_word_first
#print axioms VerifiedLL1.classical_word_erased
#print axioms VerifiedLL1.Grammar.classicalLL1_of_ll1
#print axioms VerifiedLL1.Grammar.ll1Check_iff_classicalLL1
#print axioms VerifiedLL1.Examples.ToyReduced.toy_classicalLL1
#print axioms VerifiedLL1.Examples.ToyReduced.toy_selected_acyclic
-- Phase 5.6: parser execution invariants
#print axioms VerifiedLL1.parseForest_reachable_suffix
#print axioms VerifiedLL1.reachable_of_table_entry
#print axioms VerifiedLL1.parse_ok_suffix
#print axioms VerifiedLL1.parseForest_ok_suffix
#print axioms VerifiedLL1.parseSym_ok_suffix
#print axioms VerifiedLL1.selectedLC_of_empty_prefix_parse
-- Phase 5.4: checked generation
#print axioms VerifiedLL1.Grammar.conflictList_eq_nil_iff
#print axioms VerifiedLL1.Grammar.generate_eq_ok_iff
#print axioms VerifiedLL1.Grammar.generate_iff_Ll1
#print axioms VerifiedLL1.Grammar.generate_ok
#print axioms VerifiedLL1.Grammar.generate_conflict
#print axioms VerifiedLL1.Grammar.generate_not_ok
#print axioms VerifiedLL1.bad_conflict
#print axioms VerifiedLL1.good_ll1
-- Phase 5.7: the executable fuel bound and the total generated parser
#print axioms VerifiedLL1.chain_occurs
#print axioms VerifiedLL1.chain_path
#print axioms VerifiedLL1.chain_nodup
#print axioms VerifiedLL1.length_le_of_mem_of_nodup
#print axioms VerifiedLL1.Grammar.chainBdd_universal
#print axioms VerifiedLL1.Grammar.allOccurs_of_production
#print axioms VerifiedLL1.budget_of_get
#print axioms VerifiedLL1.budget_of_allOccurs
#print axioms VerifiedLL1.fuel_not_outOfFuel
#print axioms VerifiedLL1.parse_ne_fuel
#print axioms VerifiedLL1.Grammar.parseGenerated_ne_outOfFuel
#print axioms VerifiedLL1.Grammar.parseGenerated_ok_imp
#print axioms VerifiedLL1.Grammar.parseGenerated_imp_ok
#print axioms VerifiedLL1.Grammar.parseGenerated_iff
#print axioms VerifiedLL1.Grammar.fuelFor_bound
#print axioms VerifiedLL1.Grammar.decideMembership_iff
#print axioms VerifiedLL1.Grammar.parseGenerated_tree_unique
#print axioms VerifiedLL1.Examples.FuelChecks.E_ok
#print axioms VerifiedLL1.Examples.FuelChecks.R_ok
#print axioms VerifiedLL1.Examples.FuelChecks.RR_ok
#print axioms VerifiedLL1.Examples.FuelChecks.U_ok
#print axioms VerifiedLL1.Examples.FuelChecks.U_cycle
-- Phase 4.0b: the memoized Boolean-list backend
#print axioms VerifiedLL1.Memo.lookup_map
#print axioms VerifiedLL1.Memo.tabulate_map
#print axioms VerifiedLL1.Memo.step_map
#print axioms VerifiedLL1.Memo.eq_of_map_beq
#print axioms VerifiedLL1.Memo.loop_map
#print axioms VerifiedLL1.Memo.iterBits_eq_map_iterP
#print axioms VerifiedLL1.Memo.iterMemo_eq_iterP
#print axioms VerifiedLL1.Memo.iterMemo_closed
#print axioms VerifiedLL1.Memo.iterMemo_stable
#print axioms VerifiedLL1.MemoTest.nullable_eq_iterMemo
#print axioms VerifiedLL1.MemoTest.occurs_eq_iterMemo
#print axioms VerifiedLL1.MemoTest.first_eq_iterMemo
#print axioms VerifiedLL1.MemoTest.follow_eq_iterMemo
#print axioms VerifiedLL1.MemoTest.qll1Check_eq
#print axioms VerifiedLL1.MemoTest.qll1Check_true

-- Phase 4.0c: the bridges tying each analysis to the memoized backend
#print axioms VerifiedLL1.Grammar.follow_eq_iterP
#print axioms VerifiedLL1.Grammar.follow_fun_eq
#print axioms VerifiedLL1.Grammar.nullable_eq_iterMemo
#print axioms VerifiedLL1.Grammar.occurs_eq_iterMemo
#print axioms VerifiedLL1.Grammar.first_eq_iterMemo
#print axioms VerifiedLL1.Grammar.lcReach_eq_iterP
#print axioms VerifiedLL1.Grammar.lcReach_fun_eq

-- Phase 6 addendum: canonical-tree inversion and extraction of parser output
#print axioms VerifiedLL1.Examples.QCircuits.match_tok_inv
#print axioms VerifiedLL1.Examples.QCircuits.match_var_inv
#print axioms VerifiedLL1.Examples.QCircuits.valid_qubit_canonical
#print axioms VerifiedLL1.Examples.QCircuits.valid_instr_canonical
#print axioms VerifiedLL1.Examples.QCircuits.valid_instrs_canonical
#print axioms VerifiedLL1.Examples.QCircuits.valid_prog_canonical
#print axioms VerifiedLL1.Examples.QCircuits.progOfTree_total
#print axioms VerifiedLL1.Examples.QCircuits.printProg_toAST
#print axioms VerifiedLL1.Examples.QCircuits.parse_printProg
#print axioms VerifiedLL1.Examples.QCircuits.progOfTree_of_parse_success
#print axioms VerifiedLL1.Examples.QCircuits.round_trip_extract
#print axioms VerifiedLL1.Examples.QCircuits.round_trip_empty
#print axioms VerifiedLL1.Examples.QCircuits.round_trip_all_forms
#print axioms VerifiedLL1.Examples.QCircuits.parse_hq1_fuel20
#print axioms VerifiedLL1.Examples.QCircuits.parse_hcx_fuel60
#print axioms VerifiedLL1.Examples.QCircuits.parse_output_canonical
#print axioms VerifiedLL1.Examples.QCircuits.unique_empty_tree
#print axioms VerifiedLL1.Examples.QCircuits.same_tree_at_any_fuel

def main : IO Unit := do
  IO.println "The axiom audit above is produced when this module is built."
  IO.println "Re-run it with:  lake env lean Axioms.lean"
  IO.println "No declaration may depend on sorryAx or on a user-declared axiom."