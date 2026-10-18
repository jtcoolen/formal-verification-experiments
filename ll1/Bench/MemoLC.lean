import Bench.Circ
import VerifiedLL1.MemoAnalyses

open VerifiedLL1

namespace Bench.MemoLC

variable {T : Type} {N : Type} [DecidableEq T] [DecidableEq N] [FiniteEnum T] [FiniteEnum N]

/-- The left-recursion check with the left-corner closure memoized once per source. -/
def nlrMemo (G : Grammar T N) : Bool :=
  (FiniteEnum.elems (α := N)).all fun A =>
    (FiniteEnum.elems (α := N)).all fun B => !(G.leftCorner A B && G.lcReachMemo B A)

theorem nlrMemo_eq (G : Grammar T N) : nlrMemo G = G.noLeftRecursion := by
  unfold nlrMemo Grammar.noLeftRecursion
  simp only [Grammar.lcReach_eq_iterMemo]

end Bench.MemoLC
