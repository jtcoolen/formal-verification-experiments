/-
Copyright (c) 2026 Formally Verified Examples.
Licensed under the MIT License. See the file LICENSE in the project root for
license information.
-/
import ProtSat.Complete
import ProtSat.Represent

/-!
# ProtSat: the universe is subterm-closed by construction

## Why this module exists

`Complete.univSub` asks that every subterm of every universe message is itself a universe message:

    univSub sh : Prop := ∀ t ∈ sh.U, ∀ u ∈ subtermsL t, u ∈ sh.U

It used to be carried as a hypothesis named `hsub` by `Complete.encoding_complete` and by every
bridge that consumes it - `Correspondence`, `CheckedSafe`, `Sound`, `Refute`, `AuthGap`,
`Query`, `Analyzer`, `EndToEnd`, `Differential` - and each of those sites discharged it by
`decide` on a concrete protocol, which proved the fact about an example and said nothing about
the construction.

But the construction is the reason it is true. `Bounded.univ` is built as

    (closeOne P.agents (domainKeys P.agents))^[B.rounds] (subtermClosureL (seeds P)) |>.eraseDups

whose base is subterm-closed by `Bounded.subtermClosureL_closed`, whose seeds already contain every
agent and every domain key, and whose one round only ever builds `pair x y`, `encS m k`, `encA m a`
and `hash m` out of messages the round already has - so the subterms of anything it adds were
already present. Subterm-closure is therefore a theorem of the universe, not a condition the user
must arrange.

## Where the proof lives

The generic theorem is

    Complete.univSub_shapeOf : ∀ (P : Protocol) (B : Bounds), univSub (shapeOf P B)

together with the `SubtermClosed* development that builds it. It lives in `ProtSat/Complete.lean`,
inside `namespace ProtSat.Complete`, next to the `univSub` definition it discharges: this module
imports `ProtSat.Complete`, so the lemma cannot live here without a cycle. What this module keeps
is the narrative and the concrete instances - the generic theorem applied, in place of the `decide`
gates it makes redundant.

## What was deleted with the hypothesis

Every `hsub` parameter is gone from the downstream signatures. The concrete `decide` gates that
used to discharge it - `AuthGap.hsub`, `AuthGap.hsub2`, `EndToEnd.hsub_safe`, `EndToEnd.qg_hsub`,
`Differential.leak_hsub` - were deleted rather than kept as cross-checks: they proved the same
closed fact the generic theorem now proves for *every* protocol, and a `decide` over a concrete
universe adds no independent evidence once the structural argument is checked. The examples below
are the surviving spot-checks that the generic statement really does read off the same shapes.

## What this does not do

It says nothing about the other two shape conditions. `Encode.univClosed` is a genuine bound-
adequacy property - a too-small universe is exactly what it rules out, and the analyser reports it
as `boundsTooSmall` rather than proving it. And `Complete.SecretsOK` is half bound-adequacy (a
declared secret the CNF cannot name makes the violation clause empty, which is what
`AuthGap.violationLits_nonempty` is about) and half provable; splitting it is separate work.
The generic-shape helpers in `Complete.lean` (`dedInstsOf_complete`, `dedIx_exists`, `rdEv_lt`,
`sat_evOh`, `sat_oneHot`, `sat_ded`, `sat_knSupport`) still take `univSub sh` for an *abstract*
shape: that hypothesis is not removable there, because a bare `Shape` may carry any universe at
all, and the enumeration is only complete for a subterm-closed one.
-/

namespace ProtSat.Closure

open ProtSat Term Bounded Complete Encode

/-! ### Instances: the generic theorem, applied -/

/-- The guarded-style protocol of `Represent`: the generic theorem discharges what an instance
proof would otherwise reach by `decide`. -/
example : univSub (shapeOf Represent.plainP { steps := 2, rounds := 1 }) :=
  univSub_shapeOf _ _

/-- And on a protocol with a nonce domain and a pairing expression, so the universe is not just a
handful of atoms: the condition is doing work here, and the theorem still discharges it. -/
example : univSub (shapeOf ExprDomain.boundsP ExprDomain.boundsB) := univSub_shapeOf _ _

end ProtSat.Closure
