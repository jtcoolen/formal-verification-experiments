/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import VerifiedLL1.Parser

/-!
# Phase 1.5 — the grammar of a small quantum circuit language

The token alphabet carries the instruction keywords, the two qubit identifiers and
the statement terminator; qubit *payloads* are still token kinds, not structured
data.  This is the grammar that Phase 6 will hand to the generated parser; here it
serves as a non-trivial instance of the Phase 1 semantics.

```text
prog   → instrs
instrs → instr instrs | ε
instr  → hi | cxi | si | mi
hi     → h  q0 semi
cxi    → cx q0 q1 semi
si     → s  q1 semi
mi     → m  q0 semi
```

Every instruction ends in `semi`, and `instrs` lists the instructions, so the
empty program is accepted (via `instrs ⇒ ε`).
-/

namespace VerifiedLL1.Examples.Circuits

/-- Instruction keywords, qubit identifiers and the statement terminator. -/
inductive Tok where
  | h | cx | s | m | q0 | q1 | semi
  deriving DecidableEq, Repr

inductive Var where
  | prog | instrs | instr | hi | cxi | si | mi
  deriving DecidableEq, Repr

open Tok Var Sym Tree

/-- The circuit grammar. -/
def C : Grammar Tok Var where
  productions :=
    [ (prog,   [var instrs])
    , (instrs, [var instr, var instrs])
    , (instrs, [])
    , (instr,  [var hi])
    , (instr,  [var cxi])
    , (instr,  [var si])
    , (instr,  [var mi])
    , (hi,     [tok h,  tok q0, tok semi])
    , (cxi,    [tok cx, tok q0, tok q1, tok semi])
    , (si,     [tok s,  tok q1, tok semi])
    , (mi,     [tok m,  tok q0, tok semi]) ]
  start := prog

/-- Skip one element of a membership proof. -/
private theorem skip {p q : Var × List (Sym Tok Var)} {xs} (h : p ∈ xs) : p ∈ q :: xs :=
  List.Mem.tail q h

theorem mem_prog : (prog, [var instrs]) ∈ C.productions := List.Mem.head _
theorem mem_seq : (instrs, [var instr, var instrs]) ∈ C.productions := skip (List.Mem.head _)
theorem mem_eps : (instrs, []) ∈ C.productions := skip (skip (List.Mem.head _))
theorem mem_ih : (instr, [var hi]) ∈ C.productions := skip (skip (skip (List.Mem.head _)))
theorem mem_icx : (instr, [var cxi]) ∈ C.productions :=
  skip (skip (skip (skip (List.Mem.head _))))
theorem mem_is : (instr, [var si]) ∈ C.productions :=
  skip (skip (skip (skip (skip (List.Mem.head _)))))
theorem mem_im : (instr, [var mi]) ∈ C.productions :=
  skip (skip (skip (skip (skip (skip (List.Mem.head _))))))
theorem mem_hi : (hi, [tok h, tok q0, tok semi]) ∈ C.productions :=
  skip (skip (skip (skip (skip (skip (skip (List.Mem.head _)))))))
theorem mem_cxi : (cxi, [tok cx, tok q0, tok q1, tok semi]) ∈ C.productions :=
  skip (skip (skip (skip (skip (skip (skip (skip (List.Mem.head _))))))))
theorem mem_si : (si, [tok s, tok q1, tok semi]) ∈ C.productions :=
  skip (skip (skip (skip (skip (skip (skip (skip (skip (List.Mem.head _)))))))))
theorem mem_mi : (mi, [tok m, tok q0, tok semi]) ∈ C.productions :=
  skip (skip (skip (skip (skip (skip (skip (skip (skip (skip (List.Mem.head _))))))))))

section Instructions

/-- The parse tree of the instruction `h q0;`. -/
def hInstr : Tree Tok Var := node hi [leaf h, leaf q0, leaf semi]

/-- The children of `hi` match its right-hand side `h q0 semi`. -/
theorem matchHi : MatchList C [var hi] [hInstr] :=
  MatchList.var mem_hi
    (MatchList.tok (MatchList.tok (MatchList.tok MatchList.nil)))
    MatchList.nil

/-- The parse tree of the instruction `cx q0 q1;`. -/
def cxInstr : Tree Tok Var := node cxi [leaf cx, leaf q0, leaf q1, leaf semi]

/-- The children of `cxi` match `cx q0 q1 semi`. -/
theorem matchCxi : MatchList C [var cxi] [cxInstr] :=
  MatchList.var mem_cxi
    (MatchList.tok (MatchList.tok (MatchList.tok (MatchList.tok MatchList.nil))))
    MatchList.nil

/-- `instrs ⇒ ε`, as a node with no children. -/
theorem matchEpsNode : MatchList C [var instrs] [node instrs []] :=
  MatchList.var mem_eps MatchList.nil MatchList.nil

/-- `instrs ⇒ instr instrs` with the single instruction `h q0;`. -/
theorem matchSeqHi :
    MatchList C [var instr, var instrs] [node instr [hInstr], node instrs []] :=
  MatchList.var mem_ih matchHi matchEpsNode

/-- `instrs ⇒ instr instrs` with the single instruction `cx q0 q1;`. -/
theorem matchSeqCxi :
    MatchList C [var instr, var instrs] [node instr [cxInstr], node instrs []] :=
  MatchList.var mem_icx matchCxi matchEpsNode

end Instructions

section Programs

/-- The parse tree of the program `h q0;`. -/
def prog_h : Tree Tok Var :=
  node prog [node instrs [node instr [hInstr], node instrs []]]

theorem prog_h_valid : Valid C prog_h :=
  Valid.mk mem_prog (MatchList.var mem_seq matchSeqHi MatchList.nil)

theorem prog_h_yield : yield prog_h = [h, q0, semi] := by
  simp [prog_h, hInstr, Tree.yield_node, Tree.yieldForest_cons, Tree.yield_leaf]

/-- The parse tree of the program `h q0; cx q0 q1;`. -/
def prog_hcx : Tree Tok Var :=
  node prog [node instrs [node instr [hInstr],
                          node instrs [node instr [cxInstr], node instrs []]]]

/-- `instrs ⇒ instr instrs` where the tail is the `cx` instruction. -/
theorem matchTailCxi : MatchList C [var instrs]
    [node instrs [node instr [cxInstr], node instrs []]] :=
  MatchList.var mem_seq matchSeqCxi MatchList.nil

theorem prog_hcx_valid : Valid C prog_hcx :=
  Valid.mk mem_prog
    (MatchList.var mem_seq
      (MatchList.var mem_ih matchHi matchTailCxi) MatchList.nil)

theorem prog_hcx_yield : yield prog_hcx = [h, q0, semi, cx, q0, q1, semi] := by
  simp [prog_hcx, hInstr, cxInstr, Tree.yield_node, Tree.yieldForest_cons, Tree.yield_leaf]

/-- The empty program. -/
def prog_empty : Tree Tok Var := node prog [node instrs []]

theorem prog_empty_valid : Valid C prog_empty :=
  Valid.mk mem_prog matchEpsNode

theorem prog_empty_yield : yield prog_empty = [] := by
  simp [prog_empty, Tree.yield_node, Tree.yieldForest_cons]

end Programs

section Derivations

theorem derives_prog_h : Derives C [var prog] (toks [h, q0, semi]) := by
  rw [← prog_h_yield]; exact valid_derives prog_h_valid

theorem derives_prog_hcx :
    Derives C [var prog] (toks [h, q0, semi, cx, q0, q1, semi]) := by
  rw [← prog_hcx_yield]; exact valid_derives prog_hcx_valid

theorem derives_empty : Derives C [var prog] (toks []) := by
  rw [← prog_empty_yield]; exact valid_derives prog_empty_valid

theorem language_prog_hcx : C.language [h, q0, semi, cx, q0, q1, semi] := derives_prog_hcx

/-- The same program derived **leftmost**: this is the shape of derivation that a
predictive parser produces, and it is obtained from the parse tree, not assumed. -/
theorem leftDerives_prog_hcx :
    LeftDerives C [var prog] (toks [h, q0, semi, cx, q0, q1, semi]) :=
  tree_iff_leftDerives.mp ⟨_, prog_hcx_valid, prog_hcx_yield⟩

/-- And the general derivation we already had is equivalent. -/
theorem left_of_derives_prog_hcx :
    LeftDerives C [var prog] (toks [h, q0, semi, cx, q0, q1, semi]) :=
  (derives_iff_leftDerives (A := prog) (ws := [h, q0, semi, cx, q0, q1, semi])).mp
    derives_prog_hcx

theorem language_empty : C.language [] := derives_empty

end Derivations

section Counterexamples

/-- `h q1;` is not an instruction of the language: the `h` gate acts on `q0`. -/
theorem not_valid_h_q1 : ¬ Valid C (node hi [leaf h, leaf q1, leaf semi]) := by
  intro h
  obtain ⟨rhs, hp, hm⟩ := h
  have hrhs : rhs = [tok h, tok q0, tok semi] := by simpa [C, Prod.mk.injEq] using hp
  subst hrhs
  obtain ⟨t1, ht1, r1⟩ := MatchList.eq_leaf_cons hm
  cases ht1
  obtain ⟨t2, ht2, r2⟩ := MatchList.eq_leaf_cons r1
  cases ht2

/-- A statement written without its terminator is not a valid instruction tree:
there is *no* forest of children making `node hi ts` valid with yield `h q0`. -/
theorem not_valid_hi_hq0 :
    ¬ ∃ ts, Valid C (node hi ts) ∧ Tree.yield (node hi ts) = [h, q0] := by
  rintro ⟨ts, hv, hy⟩
  obtain ⟨rhs, hp, hm⟩ := hv
  have hrhs : rhs = [tok h, tok q0, tok semi] := by simpa [C, Prod.mk.injEq] using hp
  subst hrhs
  obtain ⟨t1, ht1, r1⟩ := MatchList.eq_leaf_cons hm
  subst ht1
  obtain ⟨t2, ht2, r2⟩ := MatchList.eq_leaf_cons r1
  subst ht2
  obtain ⟨t3, ht3, r3⟩ := MatchList.eq_leaf_cons r2
  subst ht3
  have hnil : t3 = [] := MatchList.eq_nil r3
  subst hnil
  simp [Tree.yield_node, Tree.yieldForest_cons, Tree.yield_leaf] at hy

/-- The same rejection stated on the derivation side: `hi ⇒* h q0` is impossible.
By the correspondence theorem this is equivalent to the previous statement, not
an extra assumption. -/
theorem not_derives_hi_hq0 : ¬ Derives C [var hi] (toks [h, q0]) := by
  intro hd
  obtain ⟨ts, hv, hy⟩ := derives_valid hd
  exact not_valid_hi_hq0 ⟨ts, hv, hy⟩

end Counterexamples

section Computations

#eval C.nonterminals
#eval C.terminals
#eval yield prog_h
#eval yield prog_hcx
#eval yield prog_empty

end Computations



/-!
## Phase 2 slice — a hand-written predictive table for `C`

The table below is what Phase 5 will *compute*; writing it by hand here gives an
executable check that the parser really parses this language, and an instance of
the soundness theorem at a concrete input.
-/

open LTok

/-- A predictive table for the circuit grammar. -/
def M : Table Tok Var := ⟨
  [ (prog,   (LTok.tok h,  [var instrs]))
  , (prog,   (LTok.tok cx, [var instrs]))
  , (prog,   (LTok.tok s,  [var instrs]))
  , (prog,   (LTok.tok m,  [var instrs]))
  , (prog,   (LTok.eof,    [var instrs]))
  , (instrs, (LTok.tok h,  [var instr, var instrs]))
  , (instrs, (LTok.tok cx, [var instr, var instrs]))
  , (instrs, (LTok.tok s,  [var instr, var instrs]))
  , (instrs, (LTok.tok m,  [var instr, var instrs]))
  , (instrs, (LTok.eof,    []))
  , (instr,  (LTok.tok h,  [var hi]))
  , (instr,  (LTok.tok cx, [var cxi]))
  , (instr,  (LTok.tok s,  [var si]))
  , (instr,  (LTok.tok m,  [var mi]))
  , (hi,     (LTok.tok h,  [tok h,  tok q0, tok semi]))
  , (cxi,    (LTok.tok cx, [tok cx, tok q0, tok q1, tok semi]))
  , (si,     (LTok.tok s,  [tok s,  tok q1, tok semi]))
  , (mi,     (LTok.tok m,  [tok m,  tok q0, tok semi])) ] ⟩

/-- Every entry of `M` is a production of `C`: the table is `Sound` in the sense of
Phase 2.  Checked by exhaustion over the finite alphabets. -/
theorem M_sound : M.Sound C :=
  Table.sound_of_check C M (by decide)

/-- The token stream of `h q0;`. -/
def input_h : List (LTok Tok) :=
  [LTok.tok h, LTok.tok q0, LTok.tok semi, LTok.eof]

/-- The token stream of `h q0; cx q0 q1;`. -/
def input_hcx : List (LTok Tok) :=
  [LTok.tok h, LTok.tok q0, LTok.tok semi, LTok.tok cx, LTok.tok q0, LTok.tok q1,
   LTok.tok semi, LTok.eof]

/-- The token stream of the empty program. -/
def input_empty : List (LTok Tok) := [LTok.eof]

theorem wf_input_h : WellFormedInput input_h := ⟨[h, q0, semi], rfl⟩
theorem wf_input_hcx : WellFormedInput input_hcx := ⟨[h, q0, semi, cx, q0, q1, semi], rfl⟩
theorem wf_input_empty : WellFormedInput input_empty := ⟨[], rfl⟩

/-- **The parser runs.**  With 40 units of fuel the parser reconstructs exactly the
parse tree we built by hand in Phase 1. -/
theorem parse_hcx_ok : Parser.parse C M 40 input_hcx = PRes.ok prog_hcx [LTok.eof] := rfl

theorem parse_h_ok : Parser.parse C M 20 input_h = PRes.ok prog_h [LTok.eof] := rfl

theorem parse_empty_ok : Parser.parse C M 5 input_empty = PRes.ok prog_empty [LTok.eof] := rfl

/-- **Soundness instantiated.**  The tree the parser produced is valid, and its
yield is the whole input — an instance of the proved theorem, not a test. -/
theorem parse_hcx_sound :
    Valid C prog_hcx ∧ Tree.yield prog_hcx = tokensOf input_hcx :=
  parse_sound M_sound wf_input_hcx parse_hcx_ok

theorem parse_h_sound :
    Valid C prog_h ∧ Tree.yield prog_h = tokensOf input_h :=
  parse_sound M_sound wf_input_h parse_h_ok

/-- **A malformed program is rejected with a structured error**: `h q1;` asks for
the terminal `q0` and finds `q1`. -/
def input_bad : List (LTok Tok) :=
  [LTok.tok h, LTok.tok q1, LTok.tok semi, LTok.eof]

theorem parse_bad_err :
    Parser.parse C M 40 input_bad =
      PRes.error (ParseError.tokenMismatch q0 (LTok.tok q1)) := rfl

/-- A program that ends in the middle of an instruction is rejected: the table has
no entry for the pending terminal at end of input. -/
def input_truncated : List (LTok Tok) :=
  [LTok.tok h, LTok.tok q0, LTok.eof]

theorem parse_truncated_err :
    Parser.parse C M 40 input_truncated =
      PRes.error (ParseError.tokenMismatch semi LTok.eof) := rfl

/-- Insufficient fuel is reported as such rather than looping: this is the
behaviour Phase 3 replaces with a computable bound. -/
theorem parse_hcx_out_of_fuel :
    Parser.parse C M 3 input_hcx = PRes.error ParseError.outOfFuel := rfl

#eval Parser.parse C M 40 input_hcx
#eval Parser.parse C M 40 input_bad
#eval tokensOf input_hcx
