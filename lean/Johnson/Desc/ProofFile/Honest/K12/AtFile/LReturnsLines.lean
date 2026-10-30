-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LReturnsLines.lean: one of the three premises of
`carryRows_returns` (ClosingReturns.lean: the sender's text in the job of the first chain's closing
proximity test returns), the one on the carrying message's shape, at the full size. A closed line of
Lean's kernel at the library's written values.

  `carryShapeTest`, `shapeFits_of_test`   `K2.ShapeFits` (Honest/K2/Law/Counts.lean) at a message on
                                which no table rides, as a Bool
  `carryShape_written`          THE CLOSED LINE: at the written finish of the code switch the test
                                says yes at the carrying message
  `carryShape_written_no`       a control: at a table of codes without main codes it says no
  `carryShape_written_no_room`  a control: where every main code's message has the length 0 it says
                                no
  `carryShape_at_head`          under the library's head (`P5J.AtMg`), at the blank ground, at the
                                finish that is there

Limits.
- The full size alone: the library's written values.
- The two other premises of `carryRows_returns`, on the closing at zeros and on the public instance,
  are not touched.
- Two controls. Alone a "false" could come of a lacking finish; the closed line shows that one is
  there. Which clause refuses at a control is not stated.
- Nothing on what the rows are. Nothing on completeness, on soundness or on hiding.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open P5J (TS)

/-- `K2.ShapeFits` at a message on which no table rides: its two clauses that say something. -/
def carryShapeTest (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Bool :=
  VerifiableInference.Desc.Own.sentShapeFits codes s &&
    decide ((K1.stepsOf codes s (K2.rideAs s none)).pad ≤ (codes.base.getD s.code default).ell)

theorem shapeFits_of_test {codes : OnBytes.Codes} {s : OnBytes.OracleShape}
    (h : carryShapeTest codes s = true) : K2.ShapeFits codes s none := by
  unfold carryShapeTest at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2, fun _ hn => nomatch hn⟩

set_option maxRecDepth 1000000 in
/-- **The closed line**: at the written finish the carrying message's shape passes the test. -/
theorem carryShape_written :
    finishW.any (fun p => carryShapeTest p.sizes.codes (shapeL p)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: the place's table of codes without its main codes. -/
theorem carryShape_written_no :
    finishW.any (fun p => carryShapeTest { p.sizes.codes with base := #[] } (shapeL p)) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A second control: every main code's message has the length 0. -/
theorem carryShape_written_no_room :
    finishW.any (fun p => carryShapeTest
      { p.sizes.codes with base := p.sizes.codes.base.map fun c => { c with ell := 0 } }
      (shapeL p)) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **Under the head, at the blank ground, at the finish.** -/
theorem carryShape_at_head (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) : K2.ShapeFits pl.sizes.codes (shapeL pl) none := by
  have e : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h hG]
  have hw := carryShape_written
  rw [← e, hf] at hw
  exact shapeFits_of_test hw

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carryShapeTest
#print axioms ProofFile.Honest.K12.AtProof.shapeFits_of_test
#print axioms ProofFile.Honest.K12.AtProof.carryShape_written
#print axioms ProofFile.Honest.K12.AtProof.carryShape_written_no
#print axioms ProofFile.Honest.K12.AtProof.carryShape_written_no_room
#print axioms ProofFile.Honest.K12.AtProof.carryShape_at_head
