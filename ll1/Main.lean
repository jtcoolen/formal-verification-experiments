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
  IO.println "MAIN CORRESPONDENCE THEOREM (Phase 1)"
  IO.println line
  IO.println "  tree_iff_derives : (∃ ts, Valid G (node A ts) ∧ yield (node A ts) = ws)"
  IO.println "                     ↔  Derives G [var A] (toks ws)"
  IO.println ""
  IO.println "  The left side speaks only about parse trees, the right side only about"
  IO.println "  the grammar.  Neither side mentions a parser, so this is a semantic"
  IO.println "  characterisation rather than a self-certification of an implementation."
  IO.println ""
