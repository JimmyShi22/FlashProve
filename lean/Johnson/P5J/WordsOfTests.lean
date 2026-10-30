-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/WordsOfTests.lean: THE 24 EQUATIONS "READER AND OWNER READ ONE ARRAY" AT THE CLOSED s AND
    seat, AT EVERY WITNESS, IN SCOPE, FROM
TESTS WITH CODE AS FAR AS THEY STAND IN A BUILD NOT HELD AGAINST WHAT SHIPS: a joining of
    `words_at_plan_by` (HidAtPlan.lean) with
`seatsNamed_of_C` (SeatsNamedC.lean) and `sizesOf_beyond` (HidAtPlan.lean): so that Lean says that
    the two fit (two functions bear the
name seatBy).
  `seatsNamed_at_plan`: laidThere · seatsNamedC ⟹ `SeatsNamed` at seatBy (fLay layout num) X
      (sizesOf X); and, in scope,
    at seatsOf X (sizesOf X) layout num (`seatsNamed_seatsOf`): the fence hN of `hidAtPlan`.
  **`words_of_tests`**: in scope: laidThere · seatsNamedC · `GroupsSeated` · `PadsFree` (in the form
      in which a cheap
    test in other files ends) ⟹ OneWord ∧ HeadWord at the tower's own reading of every witness.
Limits. No test has run in the builds on which this file was written. `PadsFree` and `GroupsSeated`
    stay conditions here: their tests' laws stand in
files that were not in the build on which this file was written. The full size alone.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.HidAtPlan
import Johnson.P5J.SeatsNamedC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Model.Verify (publicOf)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (SeatsNamed GroupsSeated MsgT Mem)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- The two tests give `SeatsNamed` at the one function of the label. -/
theorem seatsNamed_at_plan {layout : ReqLayout} {num arr : ℕ → ℕ → ℕ} {N : Numbers}
    (T : laidThere X (sizesOf X) layout = true)
    (hC : seatsNamedC X (sizesOf X) layout num arr N = true) :
    SeatsNamed arr N (sizesOf X) (seatBy (fLay layout num) X (sizesOf X)) :=
  seatsNamed_of_C T hC (sizesOf_beyond X)

/-- In scope: at the seats off the layout: the fence hN of `hidAtPlan`. -/
theorem seatsNamed_seatsOf (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {layout : ReqLayout} {num arr : ℕ → ℕ → ℕ} {N : Numbers}
    (T : laidThere X (sizesOf X) layout = true)
    (hC : seatsNamedC X (sizesOf X) layout num arr N = true) :
    SeatsNamed arr N (sizesOf X) (seatsOf X (sizesOf X) layout num) := by
  rw [seatsOf_is_seatBy hZ hR h layout num]
  exact seatsNamed_at_plan T hC

/-- **THE 24 EQUATIONS FROM TESTS, AS FAR AS THEY LIE HERE.** -/
theorem words_of_tests {Cells Tok : Type} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {N : Numbers} {layout : ReqLayout} {num : ℕ → ℕ → ℕ}
    (T : laidThere X (sizesOf X) layout = true)
    (hC : seatsNamedC X (sizesOf X) layout num arr N = true) (hG : GroupsSeated ms N)
    (hP : PadsFree cs arr ms N (sizesOf X) (seatBy (fLay layout num) X (sizesOf X)) X)
    (w : Wit Cells Tok MsgT) :
    OneWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) ∧
      HeadWord X (ownQ cs arr ms N (sizesOf X) (seatsOf X (sizesOf X) layout num) w) :=
  words_at_plan_by hZ hR h layout num (seatsNamed_at_plan T hC) hG hP w

end P5J

#print axioms P5J.seatsNamed_at_plan
#print axioms P5J.seatsNamed_seatsOf
#print axioms P5J.words_of_tests
