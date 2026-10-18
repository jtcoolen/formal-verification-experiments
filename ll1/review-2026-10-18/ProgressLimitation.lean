import VerifiedLL1.Examples.LeftRecChecks
open VerifiedLL1
open VerifiedLL1.Examples.LeftRecUnproductive
open Tok Var
namespace ReviewProbe

def M : Table Tok Var where
  entries := [(S, (LTok.tok s, [Sym.var S])), (S, (LTok.eof, [Sym.var S]))]

theorem get_M (x : LTok Tok) : M.get S x = some [Sym.var S] := by
  cases x with
  | tok t => cases t <;> rfl
  | eof => rfl

theorem correct : M.Correct G := by
  refine ⟨Table.sound_of_check G M (by decide), ?_, ?_⟩
  · intro A x rhs hget cont u v hR hlook hder
    cases A
    have hh : rhs = [Sym.var S] := Option.some.inj (hget.symm.trans (get_M x))
    simpa [hh] using hder
  · intro A cont u v hR hex
    cases A
    obtain ⟨rhs, hp, hd⟩ := hex
    have hh : rhs = [Sym.var S] := by simpa [G] using hp
    exact ⟨[Sym.var S], get_M _, by simpa [hh] using hd⟩

theorem progressing : Table.Progressing G M (fun _ => 0) := by
  intro A x rhs hget pre t post ws rest B hm hy hall hr hl
  cases A
  have hh : rhs = [Sym.var S] := Option.some.inj (hget.symm.trans (get_M x))
  subst rhs
  exact False.elim (not_productive ⟨Tree.yieldForest (pre ++ t :: post), matchList_derives hm⟩)

theorem loops : ∀ (f : Nat) (x : LTok Tok) (xs : List (LTok Tok)),
    Parser.parseForest M f [Sym.var S] (x :: xs) = PRes.error ParseError.outOfFuel ∧
    Parser.parseSym M f (Sym.var S) (x :: xs) = PRes.error ParseError.outOfFuel := by
  intro f
  induction f with
  | zero => intro x xs; exact ⟨by simp [Parser.parseForest], by simp [Parser.parseSym]⟩
  | succ f ih =>
    intro x xs
    refine ⟨?_, ?_⟩
    · rw [parseForest_cons, (ih x xs).2]
      simp [pbind]
    · rw [parseSym_var]
      simp only [get_M x, (ih x xs).1]

#print axioms correct
#print axioms progressing
#print axioms loops
end ReviewProbe
