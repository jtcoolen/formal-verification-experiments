import VerifiedLL1.SelectedLC
open VerifiedLL1
universe u v
example {T : Type u} {N : Type v} {G : Grammar T N} {x : LTok T} {A B : N}
    (h : G.SelectedLCPath x A B) : True := by
  induction h with
  | @single A B he => trivial
  | @tail A B C hpath he ih => trivial

example {T : Type u} {N : Type v} {G : Grammar T N} {x : LTok T} {A B : N}
    (h : G.SelectedLCPath x A B) : True := by
  induction h with
  | single he => trivial
  | tail hpath he ih => trivial

example {T : Type u} {N : Type v} {G : Grammar T N} {x : LTok T} {A B : N}
    (h : G.SelPathF x A B) : True := by
  induction h with
  | @single A B hf => trivial
  | @pre A B C hpath hf => trivial
  | @tail A B C hp he ih => trivial