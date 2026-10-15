import Quantum.Semantics
import Mathlib.Algebra.Group.Defs
open Quantum
#check @add_left_neg
#check @neg_add_self
#check @sub_self
example (x : ℝ) : -x + x = 0 := by ring
example (x : ℝ) : x + -x = 0 := by ring
