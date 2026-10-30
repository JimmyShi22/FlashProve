--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Rec/MaskEllB.lean: THE PREMISE hell OF forms_pins (Johnson/Road/K4/FormsAtPins.lean:
"the number of slots nV is at most the length of the segment's mask row, maskEllP A") AS A TEST WITH
CODE ON THREE PUBLIC LETTERS, WITH ITS LAW. WHY A NEW DEFINITION: maskEllP
(Johnson/Road/K4/Rec/PinsBools.lean) takes a whole structure PinPlan, of which it reads the fields
D, rad and link alone; the other three fields have no term at the caller, so a run would have to
make them up.

  `maskEllAt D rad link`: the text of maskEllP at the three letters: the length of the code of the
    mask rows of the first message of segment link that has mask rows; 0 where there is none.
  `maskEllP_is`: maskEllP A = maskEllAt A.D A.rad A.link: by unfolding.
  `slotsFitB D rad link n`: THE TEST: n ≤ maskEllAt D rad link.
  **`hell_of_B`**: THE LAW: where the test accepts at A's three fields and nV: nV ≤ maskEllP A: hell
    to the letter. Premise: the accept: EVALUATED NOWHERE YET.
  `slotsFitB_succ`, `slotsFitB_none`: THE TEST CAN REJECT: it rejects one more than the length; and
    every positive number where no message of the segment has mask rows.
Limits. The test has been evaluated at no public parameters. It says nothing on what lies in the
mask row. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Rec.PinsBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open Johnson.Pack
open VerifiableInference.Desc.First.Look (Sent sigListCalls messagesAt keptAt)

/-- The length of the segment's mask row, at the three letters that maskEllP reads. -/
def maskEllAt (D : Sent) (rad : OnBytes.OracleShape → ℕ) (link : ℕ) : ℕ :=
  match (messagesAt D link).findIdx? fun x => x.shape.maskRows != 0 with
  | none => 0
  | some mI =>
    if member : (keptAt D link).length + mI < (sigListCalls D rad link).length then
      (pMask D.codes ((sigListCalls D rad link).get ⟨_, member⟩).1).ell
    else 0

/-- maskEllP reads three fields alone. -/
theorem maskEllP_is {Cells : Type} (A : PinPlan Cells) :
    maskEllP A = maskEllAt A.D A.rad A.link := rfl

/-- **THE TEST**: n slots fit the segment's mask row. -/
def slotsFitB (D : Sent) (rad : OnBytes.OracleShape → ℕ) (link n : ℕ) : Bool :=
  decide (n ≤ maskEllAt D rad link)

/-- **THE LAW**: hell of forms_pins. -/
theorem hell_of_B {Cells : Type} {A : PinPlan Cells} {nV : ℕ}
    (h : slotsFitB A.D A.rad A.link nV = true) : nV ≤ maskEllP A :=
  of_decide_eq_true h

/-- The test rejects one more than the length. -/
theorem slotsFitB_succ (D : Sent) (rad : OnBytes.OracleShape → ℕ) (link : ℕ) :
    slotsFitB D rad link (maskEllAt D rad link + 1) = false :=
  decide_eq_false (Nat.not_succ_le_self _)

/-- Where no message of the segment has mask rows the test rejects every positive number. -/
theorem slotsFitB_none (D : Sent) (rad : OnBytes.OracleShape → ℕ) (link n : ℕ)
    (h : ((messagesAt D link).findIdx? fun x => x.shape.maskRows != 0) = none) :
    slotsFitB D rad link (n + 1) = false := by
  have e : maskEllAt D rad link = 0 := by
    unfold maskEllAt
    rw [h]
  unfold slotsFitB
  rw [e]
  exact decide_eq_false (Nat.not_succ_le_zero n)

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.maskEllP_is
#print axioms OnBytes.Road.K4.Rec.hell_of_B
#print axioms OnBytes.Road.K4.Rec.slotsFitB_succ
#print axioms OnBytes.Road.K4.Rec.slotsFitB_none
