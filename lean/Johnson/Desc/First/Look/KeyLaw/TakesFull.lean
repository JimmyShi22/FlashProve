-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/TakesFull.lean: AT THE PUBLIC FILES IN SCOPE WHAT ALL LOOKUPS TAKE OF
THE TWO MESSAGES' MASK ENTRIES FITS THEIR MASK ROWS: RoomFor (Takes.lean) at the sized key's values,
at the matrix's size that the shape of the test on the table gives. From InScope and the planner's
yes alone: at the written sizes (key_eq_at_scope, Johnson/Goal/PlanValues/KeyFullAtScope.lean) it is
evaluated in Lean's kernel.

Main names:
  room_full: at the written sizes of a key of full size. takes_full: the two numbers: 34,885 and 48.
  room_full_no: a trial: with one mask row less at the own message it fails.
  room_at_scope: THE LAW IN SCOPE.

Limits. One size. That the values which a key file's description reads are the sized key's is not
shown here.

-/
import Johnson.Goal.PlanValues.KeyFullAtScope
import Johnson.Desc.First.Look.KeyLaw.Takes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params OnBytes.Plan
open Lk6.AtPlan (keyFull)

theorem room_full : RoomFor keyFull.ranges.x (Wf.matrixOf keyFull.once.shape) keyFull.codes
    keyFull.once.input.shape := by
  decide +kernel

theorem takes_full :
    takesO keyFull.ranges.x.messageId (Wf.matrixOf keyFull.once.shape) keyFull.ranges.x.lookups =
      34885 ∧
    takesK keyFull.ranges.x.messageId (Wf.matrixOf keyFull.once.shape) keyFull.ranges.x.lookups =
      48 := by
  decide +kernel

/-- A trial that the test can say no. -/
theorem room_full_no : ¬ takesO keyFull.ranges.x.messageId (Wf.matrixOf keyFull.once.shape)
    keyFull.ranges.x.lookups ≤ (keyFull.ranges.x.message.shape.maskRows - 1) *
      2 ^ (keyFull.codes.mask.getD keyFull.ranges.x.message.shape.maskCode default).logEll := by
  decide +kernel

/-- **At every three public files in scope what all lookups take fits.** -/
theorem room_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    RoomFor p.chains.made.sized.key.ranges.x (Wf.matrixOf p.chains.made.sized.key.once.shape)
      p.chains.made.sized.key.codes p.chains.made.sized.key.once.input.shape := by
  rw [Lk6.AtPlan.key_eq_at_scope hZ hp]
  exact room_full

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.room_full
#print axioms VerifiableInference.Desc.K3.KeyLaw.takes_full
#print axioms VerifiableInference.Desc.K3.KeyLaw.room_full_no
#print axioms VerifiableInference.Desc.K3.KeyLaw.room_at_scope
