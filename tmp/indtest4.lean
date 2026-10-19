inductive Path : Nat -> Nat -> Prop where
  | single {a b} : Nat -> Path a b
  | tail {a b c} : Path a b -> Nat -> Path a c

example (h : Path a b) : ∃ z, z = a + b := by
  induction h with
  | @single a b n => exact ⟨a + b, rfl⟩
  | @tail a b c h1 n ih => exact ⟨a + c, rfl⟩

example (h : Path a b) : ∃ z, z = a + b := by
  induction h with
  | single n => exact ⟨a + a, rfl⟩
  | tail h1 n ih => exact ⟨a + a, rfl⟩