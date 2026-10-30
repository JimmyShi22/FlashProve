-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/NumsOf.lean: the three closed facts `Nums` (Reads/RunIsAtBorder.lean) from what
the goals' scope gives of the output head's numbers.

What is shown.
  `nums_of_numbers`: `Nums X` from `Numbers X` (Johnson/Goal/Meaning/HeadCondScope.lean), from "the
    floor is 27" and from "the layout has at most six calls". The first is the conclusion of
    `numbers_in_scope` (the same file); the second that of `keyFloor_in_scope`
    (Johnson/Goal/Meaning/HeadForInScope.lean).
  `nums_in_scope`: **`Nums X` at the public values that the program makes of public files in the
    goals' scope**, under the one premise on the number of calls.

Limits. "At most six calls" is a premise: no theorem beneath this file states it. The full size
alone. Nothing on soundness.


-/
import Johnson.Desc.Reads.RunIsAtBorder
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Goal.Meaning.HeadForInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head

/-- The three closed facts, from the numbers in scope. -/
theorem nums_of_numbers {X : OnBytes.Model.Verify.Public}
    (N : VerifiableInference.Desc.Kinds.Head.Law.InScope.Numbers X)
    (kf : OnBytes.Model.Head.keyFloor X.hS = 27) (h6 : X.HLy.calls.size ≤ 6) : Nums X := by
  have hls : X.hS.ls = 6 := by
    show X.hS.la - X.hS.lt = 6
    rw [N.la, N.lt]
  refine ⟨h6, ?_, ?_⟩
  · rw [hls, N.lt, kf]
    decide
  · have e0 : (letI := sizesOf X.hS; Norm.lNI) = 0 := rfl
    have e1 : (letI := sizesOf X.hS; Norm.lPd) = 13 := by
      show clog2 X.hS.d = 13
      rw [N.d]
      decide
    show X.hS.ls ≤ (letI := sizesOf X.hS; Norm.lNI) + (letI := sizesOf X.hS; Norm.lPd)
    rw [hls, e0, e1]
    decide

/-- **The three closed facts in the goals' scope.** -/
theorem nums_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (h6 : X.HLy.calls.size ≤ 6) : Nums X :=
  nums_of_numbers (VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope hZ hR h)
    (Meaning.HeadS.keyFloor_in_scope hZ hR h) h6

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.nums_of_numbers
#print axioms VerifiableInference.Reads.AtSeat.nums_in_scope
