-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6DoorMore.lean: two more facts on the light test planK6Door
(Johnson/Desc/Kinds/PlanK6Door.lean): a fifth consequence of its acceptance, and a negative test for
it.

What is proved.
  named_of_C, named_of_door   acceptance by planK6C, or by planK6Door at the plain arguments,
          implies namedOnce arr N 24 n = true: exactly one oracle message of the output head's
          segment has the number n of the message that holds the mask row. No premise on the layout:
          Meaning.laidThere is not needed here.
  lateView v k      the View v in which every oracle message of the segment with the number k is
          sent later than in the segment's first sending.
  k6_plant_moment   at the written View of the full size so changed, at k := 145, the test rejects.
          Lean's kernel evaluates it.
  k6_plant_one      the change touches one of the 167 oracle messages.

Why only this test can reject that change. Of planK6Door's arguments the change touches sent0 alone
(which oracle messages the segment sends first). padsDoor (Johnson/Desc/Kinds/PadsDoor.lean) has no
such argument; the library's test on the request's layout (OnBytes.reqLayoutOk) and the test that
every label's array is in the layout read the codes, the shape, the layout and the labels. So none
of these can tell the changed input from the honest one. THIS IS AN ARGUMENT FROM THE TESTS'
ARGUMENTS, IN WORDS: no theorem states it, and nothing is said of the other entries of the list of
public tests.

Not proved here. No altered public FILE is given: the negative test is a changed View. Nothing on
soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6ViewFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem namedOnce)

section
variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ) (n rb : ℕ)

theorem named_of_C (h : planK6C cs arr msR N Wp lay6 num n rb = true) :
    namedOnce arr N 24 n = true := by
  unfold planK6C at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- **Acceptance by the light test: exactly one oracle message of the head's segment has n.** -/
theorem named_of_door
    (h : planK6Door cs lay6 (Meaning.sizesOf Wp 24).NM Wp.hS.NHf Wp.H.ns (Meaning.labAt Wp 24) num
      arr (N.group 24) (N.sent 24 0) (plainOf msR) n rb = true) :
    namedOnce arr N 24 n = true :=
  named_of_C cs arr msR N Wp lay6 num n rb ((planK6C_door cs arr msR N Wp lay6 num n rb).trans h)

end

/-- Every oracle message of the segment with the number k is sent later than in the first sending.
-/
def lateView (v : View) (k : Nat) : View :=
  { v with mems := v.mems.map fun y =>
      if y.inGroup && y.num == k then { y with atZero := false } else y }

/-- **The negative test.** -/
theorem k6_plant_moment : planK6V (lateView viewFull 145) 145 0 = false := by
  decide +kernel

/-- The change touches one of the 167 oracle messages. -/
theorem k6_plant_one :
    ((viewFull.mems.zip (lateView viewFull 145).mems).filter fun x =>
      Decidable.decide (x.1 ≠ x.2)).length = 1 := by
  decide +kernel

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.named_of_door
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.k6_plant_moment
