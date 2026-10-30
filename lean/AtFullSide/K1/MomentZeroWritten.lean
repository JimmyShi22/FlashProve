-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/MomentZeroWritten.lean: two closed facts on the written plan of the full size, each
decided by evaluation in Lean's kernel, each with a control that fails.

  1  maskRow_momentW   at each of the 25 links of the written shape, the first message that has a mask row
     is sent at the link's moment 0
  2  testSeatsW   the written list of seats has the seat (77 + τ, t) for τ < 5 and t < 2

What for. The sender of a link's moment 0 is the opening (link 0) or the code switch into the link
(links 1 to 24). So fact 1 says whose lot bears the link's mask row. The like for the link's matrices is
arrayMoment_written (Honest/K5/Law/ReachAtHead.lean).

Limits. Written values alone: that a plan under the library's head has this shape and list of seats is
other files' matter. This file proves nothing about completeness, soundness or hiding.
-/
import Johnson.Desc.ReqLit.Full
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (seatsAllFull)

/-- Link l's messages in a shape. -/
def msgsOfLink (s : OnBytes.Params.ReqShape) (l : Nat) : List OnBytes.Params.ReqMessage :=
  ((s.link[l]?).map (·.messages)).getD []

/-- The first message of link l that has a mask row is there, and is of moment t. -/
def maskRowAtMoment (s : OnBytes.Params.ReqShape) (t l : Nat) : Bool :=
  ((msgsOfLink s l).find? fun y => y.shape.maskRows != 0).any fun y => y.moment == t

set_option maxRecDepth 1000000 in
/-- **The mask row's message is of moment 0, at all 25 links.** A control: at moment 1, at none. -/
theorem maskRow_momentW :
    ((List.range 25).all (maskRowAtMoment shapeFull 0)) = true ∧
      ((List.range 25).any (maskRowAtMoment shapeFull 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The proximity test's ten seats are in the written list.** A control: the seat (98, 0) is not. -/
theorem testSeatsW :
    ((List.range 5).all fun τ => (List.range 2).all fun t =>
      (seatsAllFull.find? fun q => q.j == 77 + τ && q.t == t).isSome) = true ∧
      (seatsAllFull.find? fun q => q.j == 98 && q.t == 0).isSome = false := by
  decide +kernel

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.maskRow_momentW
#print axioms ProofFile.Honest.K1.testSeatsW
