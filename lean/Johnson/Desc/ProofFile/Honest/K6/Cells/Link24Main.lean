-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Cells/Link24Main.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): A
CLOSED TEST AT THE WRITTEN LIST OF THE CODE SWITCHES' PLACES (`K2.Law.placesW`,
Honest/K2/Law/PlacesWritten.lean), ON THE MAIN ROWS OF THE MESSAGE THAT HOLDS THE HEAD's OWN ARRAYS;
AND A CLOSED FACT ON THE WRITTEN REQUEST. On public data alone. Two definitions; five theorems.

  `atLink24Main`            A PUBLIC TEST: five things at a place with link 24; nothing at another
  `atLink24MainW`           it accepts at each place of the written list
  `moreMainOthers`          for the control alone: a place with one main row more in each message
  `atLink24MainW_can_fail`  a control: next to the written list it says no
  `atLink24Main_gives`      what its yes gives at a place with link 24
  `msgNo24W`                in the written request the first message of moment 0 of link 24 is
                            message 0
  `msgNo24W_other`          a weak control: see its docstring

In the manner of the switch's authors' `atLink24` (Honest/K2/Law/Link24Written.lean), which tests
five OTHER numbers at the same place.

Why. The law on what the switch's text answers at a main row's entry
(Honest/K2/Law/MainTxt.lean) writes the message's number as 1 + the kept members + m and asks the
row below the message's main rows and the place below its main code's length, in the place's own
letters. The library's law on where a layout's arrays lie (Johnson/Goal/Meaning/LaidInside.lean)
speaks in the plan's letters, which under the library's head are the written ones.

What it is not.
  * WRITTEN VALUES: that the package's files give them is another hypothesis's matter.
  * By evaluation in Lean's kernel; replayed by no independent checker.
  * The two shapes are compared in the fields that are spent (main rows; the main code's length),
    not as whole records.
  * The control reaches ONE of the five limbs: see its docstring.
  * No coin, no witness, no run.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.Link24Written
import Johnson.Desc.ProofFile.Honest.LaidData
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

open ProofFile.Honest.K2 (SwitchPlace switchSent)
open ProofFile.Honest.K2.Law (placesW)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- **A PUBLIC TEST**: at a place with link 24: one kept member (so that message 2 of the sending is
the next segment's own message 0); that message has as many main rows as message 0 of link 24 of the
written request; its main code is as long as that message's in the written codes; its main rows are
over the base field; it is sampled. Nothing at another place. -/
def atLink24Main (p : SwitchPlace) : Bool :=
  p.link != 24 ||
    (p.sizes.kept.length == 1 &&
      ((switchSent p.sizes p.others).getD 2 default).shape.mainRows ==
        ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default).shape.mainRows &&
      (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD 2 default).shape.code
        default).ell ==
        (proofSizedFull.codes.base.getD
          ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default).shape.code
          default).ell &&
      ((switchSent p.sizes p.others).getD 2 default).shape.mainDeg != 3 &&
      ((switchSent p.sizes p.others).getD 2 default).shape.answers != 0)

set_option maxRecDepth 1000000 in
/-- **The test accepts at each place of the written list.** By evaluation in Lean's kernel. -/
theorem atLink24MainW : (placesW.all atLink24Main) = true := by decide +kernel

/-- For a control: one main row more in each message of the field others. -/
def moreMainOthers (p : SwitchPlace) : SwitchPlace :=
  { p with others := p.others.map fun x =>
      { x with shape := { x.shape with mainRows := x.shape.mainRows + 1 } } }

set_option maxRecDepth 1000000 in
/-- **A control: the test can say no next to the written list**: at the one place with link 24, with
one main row more in each message of the field others. IT REACHES THE SECOND LIMB ALONE. -/
theorem atLink24MainW_can_fail :
    (((placesW.filter fun p => p.link == 24).map moreMainOthers).all atLink24Main) = false := by
  decide +kernel

/-- What the test's yes gives at a place with link 24. -/
theorem atLink24Main_gives {p : SwitchPlace} (hp : atLink24Main p = true) (hl : p.link = 24) :
    p.sizes.kept.length = 1 ∧
      ((switchSent p.sizes p.others).getD 2 default).shape.mainRows =
        ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default).shape.mainRows ∧
      (p.sizes.codes.base.getD ((switchSent p.sizes p.others).getD 2 default).shape.code
        default).ell =
        (proofSizedFull.codes.base.getD
          ((proofSizedFull.request.link.getD 24 default).messages.getD 0 default).shape.code
          default).ell ∧
      ((switchSent p.sizes p.others).getD 2 default).shape.mainDeg ≠ 3 ∧
      ((switchSent p.sizes p.others).getD 2 default).shape.answers ≠ 0 := by
  unfold atLink24Main at hp
  rw [hl] at hp
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hp
  exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

set_option maxRecDepth 1000000 in
/-- A CLOSED FACT: in the written request the first message of moment 0 of link 24 is message 0. By
evaluation in Lean's kernel. -/
theorem msgNo24W : msgNo proofSizedFull.request 24 0 0 = some 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A WEAK CONTROL: at the next number the answer is not message 0. It holds as well where there is
no second message of moment 0: it shows only that the fact above is not true of every number. -/
theorem msgNo24W_other : msgNo proofSizedFull.request 24 0 1 ≠ some 0 := by decide +kernel

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.atLink24MainW
#print axioms ProofFile.Honest.K6.atLink24MainW_can_fail
#print axioms ProofFile.Honest.K6.atLink24Main_gives
#print axioms ProofFile.Honest.K6.msgNo24W
#print axioms ProofFile.Honest.K6.msgNo24W_other
