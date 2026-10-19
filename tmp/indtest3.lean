inductive Path : Nat -> Nat -> Prop where
  | single {a b} : Nat -> Path a b
  | pre {a b c} : Path a b -> Nat -> Path a c
  | tail {a b c} : Path a b -> Nat -> Path a c

example (h : Path a b) : True := by
  induction h with
  | @single a b n => trivial
  | @pre a b c h1 n => trivial
  | @tail a b c h1 n ih => trivial

example (h : Path a b) : True := by
  induction h with
  | single n => trivial
  | pre h1 n => trivial
  | tail h1 n ih => trivial