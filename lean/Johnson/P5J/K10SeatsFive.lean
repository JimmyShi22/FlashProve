-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K10SeatsFive.lean (kind K10): THE PREMISE seats OF K10HXFive.lean (link 0, the
five-list), DRAWN AT THE CLOSED CONSTANT, AT seat := seatFiveAt (At.pseats Zp) (the term:
Johnson/LPFE1R/PlanSevenFive.lean); AND SO THE FIELD hX OF `K10Heavy` AT LINK 0, AT THE FIVE-LIST,
WITH NO PREMISE OF ITS OWN ON THE STATE. Statements and proofs: a join; one kernel line with a
negative line.

The road. Each of the five-list's seats is the seat of a member of the six-list with a main row
(`five_in_six`: BY THE KERNEL, at the written plan's seats); the five-list's number of a member is
the place of its seat in the plan's list of seats, as the six-list's is: so the sentence at the
five-list is the sentence of K10SeatsAt.lean (`AtMgA.seats_at`, l = 0) at that member.

What is said.
  `five_in_six`: for every i of the five-list there is a j of the six-list, with a main row, with
    seatFive i = seatK10 loSix P5T.psFull 0 j. `five_in_six_off`: THE NEGATIVE LINE: the six-list's
    member without a main row has a seat that is none of the five.
  `AtMgA.seats_five`: **the premise.** `AtMgA.hX_five_paid`: **the field at link 0.**

PREMISES. As K10SeatsAt.lean's and K10HXFive.lean's: h : AtMgA OnBytes.secondHashFunction .. · hLd · **Fo :
FoldFacts (a sentence on all reached states: a premise here)** · hp · hM, hZ at the five-list ·
hM₆, hZ₆ at the six-list.

Limits. AtMgA and FoldFacts are premises. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P5J.K10SeatsAt
import Johnson.P5J.K10HXFive
import Johnson.LPFE1R.PlanSevenFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks seatK10 loFive loSix kbFive
  seatFive noFiveAt)
open VerifiableInference.Desc.LinkJoin (loAt gsAt seatFiveAt)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: each of the five seats is the seat of a member of the six with a main row. -/
theorem five_in_six : ∀ i : Fin loFive.length, ∃ j : Fin loSix.length,
    memMain loSix j ∧ seatFive i = seatK10 loSix P5T.psFull 0 j := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: a member of the six without a main row has none of the five seats. -/
theorem five_in_six_off : ∃ j : Fin loSix.length, ¬ memMain loSix j ∧
    ∀ i : Fin loFive.length, seatFive i ≠ seatK10 loSix P5T.psFull 0 j := by decide +kernel

/-- **seats AT THE FIVE-LIST, AT THE CONSTANT.** -/
theorem AtMgA.seats_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps) :
    ∀ s, XK h 0 s → ∀ i, memMain loFive i →
      seatBy noFirst s.1.2.book (noFiveAt (At.seats Zp) (At.pseats Zp) i) =
        some (seatFiveAt (At.pseats Zp) i) := by
  intro s hX i _
  have e1 : At.pseats Zp = P5T.psFull := h.toAtMg.laid.seats h.toAtMg.scope
  obtain ⟨j, hj, e⟩ := five_in_six i
  have hs := h.seats_at Ld hLd Fo 0 (by omega) s hX j hj
  have e' : seatK10 (loAt 0) (At.pseats Zp) 0 j = seatFiveAt (At.pseats Zp) i := by
    rw [e1]
    exact e.symm
  rw [e'] at hs
  have e2 : VerifiableInference.Desc.First.Close.noK10 (At.seats Zp) (loAt 0) (At.pseats Zp) 0 j =
      noFiveAt (At.seats Zp) (At.pseats Zp) i := congrArg (At.seats Zp).idxOf e'
  rw [e2] at hs
  exact hs

/-- **K10Heavy's FIELD hX AT LINK 0, AT THE FIVE-LIST, WITH NO PREMISE OF ITS OWN ON THE STATE.** -/
theorem AtMgA.hX_five_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (p : Place) (hp : At.ps[ixK10 0]? = some p)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) (loFive.get i).1 = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt 0).get i).1 = (stageOf (gsAt 0) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) →
      RowAsks (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) kbFive
        (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
        (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
          (noFiveAt (At.seats Zp) (At.pseats Zp)))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 0))
        (noFiveAt (At.seats Zp) (At.pseats Zp)) a.1 :=
  h.hX_five Ld Fo p hp hM hZ hM₆ hZ₆ _ (h.seats_five Ld hLd Fo)

end P5J

#print axioms P5J.five_in_six
#print axioms P5J.five_in_six_off
#print axioms P5J.AtMgA.seats_five
#print axioms P5J.AtMgA.hX_five_paid
