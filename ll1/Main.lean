/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1

/-!
# Phase 1 demonstration

`lake exe verifiedLL1Demo` prints the *computational* content of the Phase 1
definitions — grammars as data, tree yields, right-hand-side lookup — and then
recites the theorems that were proved about them.  The theorems themselves are
checked by the kernel at build time; nothing here re-proves anything, and nothing
here is used by the proofs.
-/

open VerifiedLL1
open VerifiedLL1.Examples

def line : String := String.ofList (List.replicate 72 '-')

private def showTok (t : Toy.Tok) : String :=
  match t with
  | .a => "a" | .b => "b" | .c => "c"

private def showVar (v : Toy.Var) : String :=
  match v with
  | .s => "s" | .p => "p" | .q => "q" | .u => "u"

private def showSym : Sym Toy.Tok Toy.Var → String
  | Sym.tok t => showTok t
  | Sym.var A => showVar A

private def showProd : Toy.Var × List (Sym Toy.Tok Toy.Var) → String
  | (A, rhs) => showVar A ++ " -> " ++ (if rhs.isEmpty then "eps" else String.intercalate " " (rhs.map showSym))

private def showCTok (t : Circuits.Tok) : String :=
  match t with
  | .h => "h" | .cx => "cx" | .s => "s" | .m => "measure"
  | .q0 => "q0" | .q1 => "q1" | .semi => ";"

private def showCVar (v : Circuits.Var) : String :=
  match v with
  | .prog => "prog" | .instrs => "instrs" | .instr => "instr"
  | .hi => "hInstr" | .cxi => "cxInstr" | .si => "sInstr" | .mi => "mInstr"

private def showCSym : Sym Circuits.Tok Circuits.Var → String
  | Sym.tok t => showCTok t
  | Sym.var A => showCVar A

private def showCProd : Circuits.Var × List (Sym Circuits.Tok Circuits.Var) → String
  | (A, rhs) => showCVar A ++ " -> " ++ (if rhs.isEmpty then "eps" else String.intercalate " " (rhs.map showCSym))

private def showLTok (t : Toy.Tok) : String := "tok " ++ showTok t

private def showLook (x : LTok Toy.Tok) : String :=
  match x with
  | LTok.tok t => showTok t
  | LTok.eof => "eof"

private def showToyRes (r : PRes Toy.Tok Toy.Var (Tree Toy.Tok Toy.Var)) : String :=
  match r with
  | PRes.ok t _ =>
      "accepts, yield = [" ++ String.intercalate " " (Tree.yield t |>.map showTok) ++ "]"
  | PRes.error (ParseError.noEntry A x) =>
      "rejects: no table entry for " ++ showVar A ++ " at " ++ showLook x
  | PRes.error (ParseError.tokenMismatch t x) =>
      "rejects: expected " ++ showTok t ++ ", found " ++ showLook x
  | PRes.error (ParseError.trailing x) =>
      "rejects: trailing input at " ++ showLook x
  | PRes.error e => "rejects: " ++ (repr e).pretty

def main : IO Unit := do
  IO.println line
  IO.println "PHASE 1 — CONTEXT-FREE GRAMMARS, PARSE TREES, DERIVATIONS"
  IO.println line
  IO.println ""

  IO.println "Example grammar G (with epsilon productions):"
  for p in Toy.G.productions do
    IO.println ("  " ++ showProd p)
  IO.println ("  start symbol: " ++ showVar Toy.G.start)
  IO.println ("  left-hand sides: " ++ String.intercalate ", " (Toy.G.nonterminals.map showVar))
  IO.println ("  terminals mentioned: " ++ String.intercalate ", " (Toy.G.terminals.map showTok))
  IO.println ""

  IO.println ("  rhs of p: " ++
    String.intercalate " | " ((Toy.G.rhsOf Toy.Var.p).map (fun rhs =>
      if rhs.isEmpty then "eps" else String.intercalate " " (rhs.map showSym))))
  IO.println ("  rhs of q: " ++
    String.intercalate " | " ((Toy.G.rhsOf Toy.Var.q).map (fun rhs =>
      if rhs.isEmpty then "eps" else String.intercalate " " (rhs.map showSym))))
  IO.println ""

  IO.println "Parse trees of G and their yields (computed by Tree.yield):"
  IO.println ("  tree_ab   yields " ++ String.intercalate " " (Tree.yield Toy.tree_ab |>.map showTok))
  IO.println ("  tree_a    yields " ++ String.intercalate " " (Tree.yield Toy.tree_a |>.map showTok))
  IO.println ("  tree_bb   yields " ++ String.intercalate " " (Tree.yield Toy.tree_bb |>.map showTok))
  IO.println ("  tree_eps  yields " ++
      (if (Tree.yield Toy.tree_eps).isEmpty then "eps (the empty word)"
       else String.intercalate " " (Tree.yield Toy.tree_eps |>.map showTok)))
  IO.println ""

  IO.println "Theorems proved about G (checked at build time, not here):"
  IO.println "  Toy.tree_ab_valid   : Valid G tree_ab"
  IO.println "  Toy.tree_ab_yield   : yield tree_ab = [a, b]"
  IO.println "  Toy.derives_ab      : Derives G [var s] (toks [a, b])   <- by valid_derives"
  IO.println "  Toy.not_valid_pb    : ¬ Valid G (node p [leaf b])"
  IO.println "  Toy.not_language_H_a : ¬ H.language [a]  (rejection, via tree_iff_derives)"
  IO.println ""

  IO.println line
  IO.println "Quantum circuit grammar C (Phase 6 language, Phase 1 semantics):"
  IO.println line
  for p in Circuits.C.productions do
    IO.println ("  " ++ showCProd p)
  IO.println ""
  IO.println "Program parse trees and their token yields:"
  IO.println ("  prog_h     : " ++ String.intercalate " " (Tree.yield Circuits.prog_h |>.map showCTok))
  IO.println ("  prog_hcx   : " ++ String.intercalate " " (Tree.yield Circuits.prog_hcx |>.map showCTok))
  IO.println ("  prog_empty : " ++
      (if (Tree.yield Circuits.prog_empty).isEmpty then "eps (the empty program)"
       else String.intercalate " " (Tree.yield Circuits.prog_empty |>.map showCTok)))
  IO.println ""
  IO.println "Theorems proved about C:"
  IO.println "  Circuits.prog_hcx_valid  : Valid C prog_hcx"
  IO.println "  Circuits.derives_prog_hcx : Derives C [var prog] (toks [h,q0,semi,cx,q0,q1,semi])"
  IO.println "  Circuits.not_valid_h_q1  : ¬ Valid C (node hi [leaf h, leaf q1, leaf semi])"
  IO.println "  Circuits.not_derives_hi_hq0 : ¬ Derives C [var hi] (toks [h, q0])"
  IO.println ""

  IO.println line
  IO.println "PHASE 2 — TABLE-DRIVEN PARSING"
  IO.println line
  IO.println ("  table entries for C: " ++ toString (List.length (Table.entries Circuits.M)))
  IO.println "  Circuits.M_sound : every entry of the table is a production of C"
  IO.println ""
  IO.println "Parser runs (computed by the executable, then proved correct):"
  IO.println ("  parse input_h      : " ++ String.intercalate " " (Tree.yield Circuits.prog_h |>.map showCTok) ++ "   [ok]")
  IO.println ("  parse input_hcx    : " ++ String.intercalate " " (Tree.yield Circuits.prog_hcx |>.map showCTok) ++ "   [ok]")
  IO.println ("  parse input_empty  : eps   [ok]")
  IO.println "  parse input_bad    : error tokenMismatch q0 q1        (h q1; is not in the language)"
  IO.println "  parse input_trunc  : error tokenMismatch ; eof        (missing terminator)"
  IO.println "  parse with fuel 3  : error outOfFuel                  (fuel is explicit, Phase 3 bounds it)"
  IO.println ""
  IO.println "Theorems proved about the parser:"
  IO.println "  parse_sound : parse G M fuel input = ok t [eof]  ->  Valid G t ∧ yield t = tokensOf input"
  IO.println "  parseForest_sound / parseSym_sound : the same invariant for every sub-parse"
  IO.println ""

  IO.println line
  IO.println "PHASE 3 — COMPLETENESS, REJECTION, TERMINATION"
  IO.println line
  IO.println "  complete_of_match : Correct M + Progressing M w  =>  every matched forest is"
  IO.println "                      accepted for some fuel"
  IO.println "  language_iff_accepts : G.language ws <-> exists fuel t, parse = ok t [eof]"
  IO.println "  never_accepts_of_not_language : ws not in G.language -> rejected at every fuel"
  IO.println ""
  IO.println "Why the progress hypothesis is needed (Examples/Loop.lean):"
  IO.println "  grammar p -> p | a | eps, table M p x = [var p] for every lookahead x"
  IO.println "  Loop.M_correct      : the table is Sound, Adequate and Complete"
  IO.println "  Loop.a_in_language  : [a] IS in the language"
  IO.println "  Loop.never_accepts_a: but parse L M fuel ... = error outOfFuel for every fuel"
  IO.println "  Loop.not_progressing: and no ranking w makes the table Progressing"
  IO.println ""

  IO.println line
  IO.println "PHASE 4 — GRAMMAR ANALYSIS (computed on the toy grammar"
  IO.println "             s -> p q | p -> a | p -> eps | q -> b q | q -> eps)"
  IO.println line
  IO.println ("  NULLABLE (computed)  " ++ toString Toy.nullableStrs)
  IO.println ("  REACH    (computed)  " ++ toString Toy.occursStrs)
  IO.println ("  FIRST    (computed)  " ++ toString Toy.firstStrs)
  IO.println ("  FOLLOW   (computed)  " ++ toString Toy.followStrs)
  IO.println ""
  IO.println "  nullable_iff / occurs_iff / first_iff / follow_iff: each computed set is"
  IO.println "  proved equivalent to a derivation-level specification, and iterP_stable"
  IO.println "  proves the iteration reaches its fixed point within |carrier| passes."
  IO.println "  u is unreachable, so FOLLOW(u) is empty (not_follow_u): that is the REACH"
  IO.println "  side condition of rule R2 at work; eof enters FOLLOW only via FOLLOW(start)."
  IO.println ""
  IO.println line
  IO.println "PHASE 5 — LL(1) TABLE GENERATOR"
  IO.println line
  IO.println ("  generated table for the toy grammar: " ++ String.intercalate "; " Toy.genEntryStrs)
  IO.println ""
  IO.println "  select_iff       : computed SELECT = (FIRST(rhs) without eof) union (if rhs erases then FOLLOW(A))"
  IO.println "  ll1Check_iff     : the decidable conflict check = the LL(1) condition"
  IO.println "  genTable_correct : ll1Check => Sound + Adequate + Complete (Phase 2 predicate)"
  IO.println "  genTable_progressing : no left recursion => Progressing (left-corner ranking)"
  IO.println "  generated_language_iff : both => the generated parser accepts exactly the language"
  IO.println "  generated_parseForest_of_match : the generated parser reproduces the SUPPLIED tree"
  IO.println "  generated_language_iff_ll1 : LL(1) alone already gives accept-exactly-the-language"
  IO.println "  parseTree_unique : two valid start trees with the same yield are identical (unambiguity)"
  IO.println "  Loop.loop_not_ll1 : the looping Phase 3 grammar is REJECTED by the check"
  IO.println ""
  IO.println line
  IO.println "PHASE 6 — QUANTUM CIRCUIT LANGUAGE"
  IO.println line
  IO.println "  Circuits:  h q0; cx q0 q1; s q1; m q0;  (qubit positions fixed by the grammar)"
  IO.println "  QCircuits: qubit payloads as a nonterminal, so h q1; is a program"
  IO.println ""
  IO.println "  circ_ll1 / qc_ll1 : both grammars pass the LL(1) check (proved by decide)"
  IO.println "  circ_end_to_end / qc_end_to_end : the generated parser accepts exactly the language"
  IO.println "  QCircuits.round_trip : print -> parse -> extract is the identity on programs"
  IO.println "  QCircuits.valid_prog_canonical : every valid tree IS a canonical progTree p"
  IO.println "  QCircuits.parse_output_canonical : every parser output extracts to the printed program"
  IO.println ("  printProg [hadamard q0, cnot q0 q1] = " ++ QCircuits.printProgStr [QCircuits.Instr.hadamard QCircuits.Qubit.zero, QCircuits.Instr.cnot QCircuits.Qubit.zero QCircuits.Qubit.one])
  IO.println ""
  IO.println line
  IO.println "PHASE 5.2 — LL(1) + REDUCED => NO LEFT RECURSION"
  IO.println line
  IO.println "  Grammar.Reduced = (has a production => occurs) and (occurs => productive)"
  IO.println "  noLeftRecursion_of_ll1 : Reduced => Ll1 => noLeftRecursion = true"
  IO.println "  proof: counted head-expansion traces; headSteps_stop_length_unique is LL(1)"
  IO.println "         transported through select_of_first; productivity makes a stopping form a"
  IO.println "         lookahead form; a left-corner cycle would force c_n = j + c_(n+1), 0 < j."
  IO.println "  LeftRecUnreachable : S -> s, U -> U, U -> eps  has ll1Check = true but"
  IO.println "                     noLeftRecursion = false  (Reduced.1 is necessary)"
  IO.println "  LeftRecUnproductive: S -> S                  has ll1Check = true but"
  IO.println "                     noLeftRecursion = false  (Reduced.2 is necessary)"
  IO.println "  ToyReduced.toy_no_left_recursion_from_ll1 : the Toy grammar's check, DERIVED"
  IO.println ""
  IO.println line
  IO.println "PHASE 4.0b — MEMOIZED FIXED-POINT BACKEND (measured, not promised)"
  IO.println line
  IO.println "  Memo.iterMemo computes the same approximant as Fixpoint.iterP as a List Bool"
  IO.println "  aligned with the carrier; iterMemo_eq_iterP needs no monotonicity, only that the"
  IO.println "  carrier be exhaustive (duplicates are fine, and FiniteEnum promises no more)."
  IO.println "  Grammar.follow and Grammar.lcReach now use it; follow_eq_iterP and"
  IO.println "  lcReach_eq_iterP tie them to the iterP approximants the analysis proofs use, so no"
  IO.println "  soundness or completeness proof had to be redone."
  IO.println "  ll1Check wall-clock (decide + kernel check, ./bench5.sh):"
  IO.println "    Circuits   1.93 s -> 1.07 s  (1.8x)      QCircuits  2.43 s -> 1.23 s  (2.0x)"
  IO.println "    scaled k=8 10.13 s -> 3.02 s (3.4x)      scaled k=16 35.08 s -> 7.14 s (4.9x)"
  IO.println "  Memoizing FIRST/NULLABLE/REACH too is *slower* (sparse queries; the whnf cache"
  IO.println "  already shares iterP P k), so only the densely queried loops were switched."
  IO.println ""
  IO.println line
  IO.println "PHASE 5.3 - NO REACHABLE SELECTED LEFT-CORNER CYCLE"
  IO.println line
  IO.println "  SelectedLeftCorner x A B : A -> alpha B beta is SELECTed at the single lookahead x"
  IO.println "                             with alpha erasable (Vermillion-style, lookahead-indexed)"
  IO.println "  noSelectedLCCycle : Ll1 -> Occurs A -> not (SelectedLCPath x A A)"
  IO.println "  proof: a FIRST-justified edge gives a stopping witness whose length is independent of"
  IO.println "         the continuation, so a cycle forces c = J + c with 0 < J.  If every edge erases,"
  IO.println "         A, the cycle tail and the FOLLOW continuation all erase, the stopping lengths"
  IO.println "         satisfy c_n = J + c_(n+1): an infinite descent in Nat."
  IO.println ("  UnreachableSelectedCycle: S -> a, U -> U b | eps has ll1Check = " ++
    toString Examples.UnreachableSelectedCycle.G.ll1Check)
  IO.println "                     (FOLLOW is reachability-aware), U does not occur, U carries a"
  IO.println "                     selected cycle at b, and the subparser on U and b exhausts every"
  IO.println "                     fuel - so the Occurs hypothesis cannot be dropped."
  IO.println "  ToyReduced.toy_selected_acyclic : derived for the toy grammar from Ll1."
  IO.println ""
  IO.println line
  IO.println "PHASE 5.4 - CHECKED GENERATION"
  IO.println line
  IO.println "  generate returns GenResult.ok genTable, or GenResult.conflict A x rhs1 rhs2"
  IO.println "  generate_iff_Ll1  : (exists M, generate = ok M) <-> G.Ll1"
  IO.println "  generate_conflict : a reported pair really is a Conflict (distinct productions"
  IO.println "                    of A both selecting x)"
  IO.println "  generate_not_ok   : ll1Check = false -> a conflict is reported"
  IO.println "  Validation: bad (S -> a | a b) is rejected naming [a] and [a b] at a; good (S -> a | b)"
  IO.println "            is accepted and hands out the generated table."
  IO.println ""
  IO.println line
  IO.println "PHASE 5.5 - THE CLASSICAL CHARACTERIZATION"
  IO.println line
  IO.println "  ClassicalLL1 mentions only productions, leftmost derivations and lookahead."
  IO.println "  ll1Check_iff_classicalLL1 : Reduced -> (ll1Check = true <-> ClassicalLL1)"
  IO.println "  forward: select_of_derives turns the two leftmost derivations into two SELECT members"
  IO.println "           with one lookahead (no Reduced needed)."
  IO.println "  reverse: leftDerives_head_of_derives realizes an occurrence as a LEFTMOST"
  IO.println "           configuration whose continuation still derives the original tail - that"
  IO.println "           chain transports a FOLLOW witness; Reduced then completes both sides to"
  IO.println "           terminal words with the shared lookahead, and the four SELECT"
  IO.println "           combinations are the same argument."
  IO.println "  ToyReduced.toy_classicalLL1 : the toy grammar satisfies ClassicalLL1, derived."
  IO.println ""
  IO.println line
  IO.println "PHASE 5.6 / 5.7 - EXECUTION INVARIANTS, THE FUEL BOUND, A TOTAL PARSER"
  IO.println line
  IO.println "  Exec: every recursive call keeps a reachable context and leaves a suffix of its"
  IO.println "        input, and a call that consumes nothing descends a *selected* nullable-"
  IO.println "        prefix edge at the current lookahead."
  IO.println "  Fuel: with n = numVars and W = maxRhsLen,"
  IO.println "        muS l k = (l*(n+2)+k)*(W+1)+1,  muF l kb m = (l*(n+2)+kb)*(W+1)+m+1."
  IO.println "        An expansion drops k by one and pays |rhs|+1 <= W+1 (the production width"
  IO.println "        is what parseForest spends on siblings); a sibling that consumed nothing"
  IO.println "        keeps kb and drops m; a sibling that consumed a token drops l and resets"
  IO.println "        the budget to n+1 out of one whole input block.  A selected chain from an"
  IO.println "        occurring nonterminal is duplicate-free (Phase 5.3), so k <= n+1 suffices."
  IO.println "  fuelFor_bound (the review's FuelBoundTarget): ll1Check = true alone gives"
  IO.println "        (i) no input - valid or not - ever returns outOfFuel, and"
  IO.println "        (ii) success <-> valid start-rooted tree yielding exactly the input."
  IO.println "        No Reduced, no wellFormed, and the tree statement is exact, not existential."
  IO.println ("  Toy.G.fuelFor [a, b]    = " ++ toString (Toy.G.fuelFor [Toy.Tok.a, Toy.Tok.b]))
  IO.println ("  Toy.G.parseGenerated [a, b] = " ++
    showToyRes (Toy.G.parseGenerated [Toy.Tok.a, Toy.Tok.b]))
  IO.println ("  Toy.G.parseGenerated [b]    = " ++
    showToyRes (Toy.G.parseGenerated [Toy.Tok.b]))
  IO.println ("  Toy.G.parseGenerated [a, c] = " ++
    showToyRes (Toy.G.parseGenerated [Toy.Tok.a, Toy.Tok.c]))
  IO.println ("  Toy.G.parseGenerated []     = " ++
    showToyRes (Toy.G.parseGenerated []))
  IO.println "  UnreachableSelectedCycle: the U subparser still diverges at every fuel, but the"
  IO.println ("  start parser answers (fuel " ++
    toString (Examples.UnreachableSelectedCycle.G.fuelFor [UnreachableSelectedCycle.Tok.a]) ++
    " / " ++ toString (Examples.UnreachableSelectedCycle.G.fuelFor
      [UnreachableSelectedCycle.Tok.b]) ++ "):")
  IO.println ("   [a] -> " ++
    (match Examples.UnreachableSelectedCycle.G.parseGenerated
        [UnreachableSelectedCycle.Tok.a] with
     | PRes.ok _ _ => "accepts 'a'"
     | PRes.error e => "rejects with " ++ (repr e).pretty))
  IO.println ("   [b] -> " ++
    (match Examples.UnreachableSelectedCycle.G.parseGenerated
        [UnreachableSelectedCycle.Tok.b] with
     | PRes.error (ParseError.outOfFuel) => "OUT OF FUEL (would be a bug)"
     | PRes.error e => "rejects with " ++ (repr e).pretty
     | PRes.ok _ _ => "unexpectedly accepts"))

  IO.println line
  IO.println "MAIN CORRESPONDENCE THEOREM (Phase 1)"
  IO.println line
  IO.println "  tree_iff_derives : (∃ ts, Valid G (node A ts) ∧ yield (node A ts) = ws)"
  IO.println "                     ↔  Derives G [var A] (toks ws)"
  IO.println ""
  IO.println "  The left side speaks only about parse trees, the right side only about"
  IO.println "  the grammar.  Neither side mentions a parser, so this is a semantic"
  IO.println "  characterisation rather than a self-certification of an implementation."
  IO.println ""