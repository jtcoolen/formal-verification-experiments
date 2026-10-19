import ProtSat

#check @dif_pos
#check @dif_neg
#check @if_pos

inductive V where | a : Nat -> V | b : Bool -> V

def dd (n : Nat) : V :=
  if h : n = 0 then V.a 1 else V.b (n > 1)

theorem t1 (n : Nat) (h : n = 0) : dd n = V.a 1 := by rw [dd, if_pos h]
theorem t2 (n : Nat) (h : n = 0) : dd n = V.a 1 := by rw [dd, dif_pos h]
theorem t3 (n : Nat) (h : ¬ n = 0) : dd n = V.b (n > 1) := by rw [dd, if_neg h]
theorem t4 (n : Nat) (h : ¬ n = 0) : dd n = V.b (n > 1) := by rw [dd, dif_neg h]
theorem t5 (n : Nat) (h : n = 0) : dd n = V.a 1 := by simp [dd, h]
theorem t6 (n : Nat) (h : ¬ n = 0) : dd n = V.b (n > 1) := by simp [dd, h]

-- Bool-ite in a nested def, peeled by rw + simp
def ff (l : List Nat) : V :=
  if l.isEmpty then V.b false else if l.length = 0 then V.a 0 else V.a 1
theorem t7 (l : List Nat) (h1 : l.isEmpty = true) : ff l = V.b false := by
  rw [ff, h1]
  simp
theorem t8 (l : List Nat) (h1 : l.isEmpty = false) (h2 : l.length = 0 = false) : ff l = V.a 1 := by
  rw [ff, h1, h2]
  simp
