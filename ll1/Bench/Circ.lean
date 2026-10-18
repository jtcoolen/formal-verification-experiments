import Bench.MemoGrow

/-!
# The scaled circuit-grammar family

The QCircuits example grammar, but with k qubit tokens instead of two:

    prog    -> instrs
    instrs  -> instr instrs | eps
    instr   -> hgate | cxgate | sgate | mgate
    hgate   -> h  qubit semi
    cxgate  -> cx qubit qubit semi
    sgate   -> s  qubit semi
    mgate   -> m  qubit semi
    qubit   -> q0 | q1 | ... | q(k-1)

The nonterminal alphabet is fixed (Fin 8) while the terminal alphabet is Fin (k+5), so the
FIRST carrier has (2k+13)*2 elements and the FOLLOW carrier 8*(k+2): the analyses scale
with the size of the token alphabet, which is what makes them worth memoizing.  The grammar
is LL(1) for every k (the qubit productions have disjoint one-token FIRST sets, and instrs
separates on the four gate keywords), so the conflict check is a real computation that
succeeds.
-/

open VerifiedLL1

namespace Bench

/-- The scaled circuit grammar with k qubit tokens.  Terminals: 0 = h, 1 = cx, 2 = s,
3 = m, 4 = semi, 5+i = q_i.  Nonterminals: 0 = prog, 1 = instrs, 2 = instr, 3 = hgate,
4 = cxgate, 5 = sgate, 6 = mgate, 7 = qubit. -/
def circ (k : Nat) : Grammar (Fin (k+5)) (Fin 8) where
  productions :
    List (Fin 8 × List (Sym (Fin (k+5)) (Fin 8))) :=
    [ (0, [Sym.var 1]), (1, [Sym.var 2, Sym.var 1]), (1, []), (2, [Sym.var 3]), (2, [Sym.var 4]),
      (2, [Sym.var 5]), (2, [Sym.var 6]), (3, [Sym.tok 0, Sym.var 7, Sym.tok 4]),
      (4, [Sym.tok 1, Sym.var 7, Sym.var 7, Sym.tok 4]),
      (5, [Sym.tok 2, Sym.var 7, Sym.tok 4]), (6, [Sym.tok 3, Sym.var 7, Sym.tok 4]) ] ++
      (List.finRange k).map fun i => (7, [Sym.tok ⟨i.val + 5, by omega⟩])
  start := 0

end Bench
