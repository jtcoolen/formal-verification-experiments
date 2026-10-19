import VerifiedLL1.LeftRec
open VerifiedLL1
inductive Path : Nat -> Nat -> Prop where
  | single {a b} : Nat -> Path a b
  | tail {a b c} : Path a b -> Nat -> Path b c -> Path a c

example (h : Path a b) : True := by
  induction h with
  | single n => trivial
  | @tail a b c h1 n h2 ih => trivial

example (h : Path a b) : True := by
  induction h with
  | single n => trivial
  | tail h1 n h2 ih => trivial