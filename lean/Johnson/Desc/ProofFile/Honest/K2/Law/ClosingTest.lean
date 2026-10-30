-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingTest.lean: the kind "the code switch" (K2): THE LIGHT
CLOSING TEST (`closingOkLight`, Honest/K2/Law/ClosingLight.lean) AT ONE PLACE OF THE CLOSED LIST
(`placesW`, `segsW`, Honest/K2/Law/PlacesWritten.lean), AS A TEST BY THE PLACE's NUMBER IN THE LIST;
WHAT ITS YES SAYS; AND A CONTROL. So that Lean's kernel can be asked place by place: at place number
i the test walks i + 1 segments, and one theorem for all 25 wants more memory than one for each.
Definitions with code; three statements with their proofs.

  `closingAt` the light closing test at the place number i of the closed list; yes beyond the list's
                    end
  `all_at`, `closingAt_says` within the list its yes is the light test's yes at that member
  `refusalAt` the words in which the light closing refuses at a place; nothing where it returns
  `closing_can_fail` CONTROL, by Lean's kernel: at the first place with its kept shapes struck the
                    light closing refuses, IN THE WORDS "a switch's kept members are not those that
                    the fold in front left": so the walk itself has returned and the last comparison
                    fails

By: the definitions · `noKept` (Honest/K2/Law/PublicAtWritten.lean).

Limits. The test is shown of no place here: the 25 files' worth of yeses stand in
Honest/K2/Law/ClosingW0.lean to ClosingW4.lean. ONE CLOSED FACT BY LEAN's KERNEL, replayed by no
independent checker. A public test at zeros: nothing on what a closing leaves, nothing on a run. The
full size alone. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- **The light closing test at the place number i of the closed list.** -/
def closingAt (i : Nat) : Bool :=
  ((placesW.drop i).take 1).all fun p => closingOkLight freshTable (segsW.take p.link) p

/-- A test on the one member at a number of a list. -/
theorem all_at {α : Type} (l : List α) (f : α → Bool) {i : Nat} (hi : i < l.length)
    (h : ((l.drop i).take 1).all f = true) : f l[i] = true := by
  rw [List.drop_eq_getElem_cons hi] at h
  simp only [List.take_succ_cons, List.take_zero, List.all_cons, List.all_nil, Bool.and_true] at h
  exact h

/-- Within the list its yes is the light test's yes at that member. -/
theorem closingAt_says {i : Nat} (hi : i < placesW.length) (h : closingAt i = true) :
    closingOkLight freshTable (segsW.take placesW[i].link) placesW[i] = true :=
  all_at placesW (fun p => closingOkLight freshTable (segsW.take p.link) p) hi h

/-- The words in which the light closing refuses at a place. -/
def refusalAt (p : SwitchPlace) : Option String :=
  match closingLightFor freshTable (segsW.take p.link) p.sizes.kept
      (Stretch.carried p.carries (shapeZerosAll p.carries)) with
  | .ok _ => none
  | .error e => some e

set_option maxRecDepth 1000000 in
/-- **The test can fail, and for the reason that matters.** -/
theorem closing_can_fail : ((placesW.take 1).map noKept).map refusalAt =
    [some "a switch's kept members are not those that the fold in front left"] := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.all_at
#print axioms ProofFile.Honest.K2.Law.closingAt_says
#print axioms ProofFile.Honest.K2.Law.closing_can_fail
