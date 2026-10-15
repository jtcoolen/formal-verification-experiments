import Quantum.Optimizer
open Quantum Quantum.Opt
set_option maxHeartbeats 400000000
def k0 : Fin 3 := ⟨0, by decide⟩
def k1 : Fin 3 := ⟨1, by decide⟩
def k2 : Fin 3 := ⟨2, by decide⟩
def cx3 : Gate 3 := Gate.cx k0 k1 (by decide)
def sg : List (Gate n) -> Circuit n
  | [] => Circuit.one
  | [g] => Circuit.gate g
  | g :: gs => Circuit.seq (Circuit.gate g) (sg gs)
def cI : Circuit 3 := sg [cx3, Gate.x k2, cx3]
def afterG {n : Nat} (g : Gate n) : Ctx n -> Ctx n := fun k => Ctx.seqL (Circuit.gate g) k
def beforeC {n : Nat} (d : Circuit n) : Ctx n -> Ctx n := fun k => Ctx.seqR k d
#eval cI
#eval Ctx.fill (afterG cx3 Ctx.hole) (Circuit.seq (Circuit.gate (Gate.x k2)) (Circuit.gate cx3))
#eval applyStep cI { ruleId := "disjoint", args := [Arg.g (Gate.x k2), Arg.g cx3], ctx := afterG cx3 Ctx.hole, backward := false }
#eval applyStep (Circuit.seq cx3 (Circuit.seq cx3 (Circuit.gate (Gate.x k2)))) { ruleId := "cxcx", args := [Arg.q k0, Arg.q k1], ctx := beforeC (Circuit.gate (Gate.x k2)) Ctx.hole, backward := false }
#eval (rules 3).map fun r => r.id
#eval findRule 3 "disjoint"
