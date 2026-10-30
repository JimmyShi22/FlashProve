-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/HingeFiveAtMg.lean (kind K10): "THE HINGE" OF K10's LAW AT LINK 0, MOVED FROM THE SIX-LIST TO THE FIVE-LIST, AT THE CONSTANT's OWN LETTERS; WITH THE ONE CLOSED FACT ON THE TWO NUMBERINGS THAT THE MOVE ASKS.
A definition, closed facts by the kernel, theorems: calls.

Why. K10's law at link 0 is typed over the five-list (the 0th written list's messages with a main row: `loFive`, LinkZeroFive.lean). `AtMg.hinge_zero` (HingeAtMgZero.lean beside this file) stands at the six-list.
`shapesAre_five_of_six` (Johnson/Desc/First/Close/Law/ShapesFiveOfSix.lean) moves `ShapesAre` from the one to the other under hno: the two numberings give the members the same numbers, in order.
`noFive_is` (FiveAtFull.lean) says one side of it, at the written seats.

What is said.
  `noFiveAt seats ps`: the five-list's numbering at any list of seats and any plan's seats; at the written ones it is `noFive` (FiveAtFull.lean): `noFiveAt_written`: by rfl.
  `hno_written` [BY THE KERNEL]: (membersOf loFive).map noFive = (membersOf loSix).map (noK10 seatsPlanW loSix P5T.psFull 0). `hno_other`: against link 1's numbering of the six-list's places it fails.
  `AtMg.hno`: **the same at the constant's letters** (At.seats Zp, At.pseats Zp): every o.
  `AtMg.hinge_five`, `AtMg.hinge_five_at_border`: **THE HINGE AT LINK 0 AT THE FIVE-LIST**: `ShapesAre` of the state's statement, the frame's group, loFive, kbFive and noFiveAt at the constant's letters.

PREMISES of the last two: as `AtMg.hinge_zero`'s: AtMg at OnBytes.secondHashFunction · FoldFacts at h.rch with hM · reached · no mark.
Limits. AtMg and FoldFacts are premises. WHAT OF THE HEAD IS SPENT, BY NAME, AS FAR AS TRACED: OF
THE PROOF FILE's ENTRY TESTS (Johnson/Desc/Laid/ProofAsks.lean: numbered as in its head), BEYOND THE
FIRST EIGHT: what `AtMg.hinge_zero` spends (TEST 10, `cutRow`, and TEST 9, `madeRow`, three times),
and TEST 9 once more in `AtMg.hno` (`LaidAt.seats`: the seats are the written ones). Moved into the
head, not paid. Nothing on soundness.

-/
import Johnson.P5J.HingeAtMgZero
import Johnson.Desc.First.Close.Law.ShapesFiveOfSix

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Close
open OnBytes

/-- **The five-list's numbering**, at any list of seats and any plan's seats. -/
def noFiveAt (seats : List (ℕ × ℕ)) (ps : List P5T.PSeat) : Fin loFive.length → ℕ := fun i =>
  seats.idxOf ((seatsMain loSix (seatsOfLink ps 0)).getD i.val (0, 0))

theorem noFiveAt_written : noFiveAt seatsPlanW P5T.psFull = noFive := rfl

set_option maxRecDepth 1000000 in
/-- **(W) The two numberings give the members the same numbers, in order.** -/
theorem hno_written :
    (membersOf loFive).map noFive =
      (membersOf loSix).map (noK10 seatsPlanW loSix P5T.psFull 0) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** Against link 1's numbering of the same places they differ. -/
theorem hno_other :
    decide ((membersOf loFive).map noFive =
      (membersOf loSix).map (noK10 seatsPlanW loSix P5T.psFull 1)) = false := by decide +kernel

end VerifiableInference.Desc.First.Close

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First (Numbers ModelPart FoldFacts FoldData)
open VerifiableInference.Desc.First.Close (rdK ShapesAre membersOf noK10 seatsPlanW loFive loSix
  kbFive kbSix noFive noFiveAt noFiveAt_written hno_written shapesAre_five_of_six)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **hno AT THE CONSTANT's LETTERS.** -/
theorem AtMg.hno {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) :
    (membersOf loFive).map (noFiveAt (At.seats Zp) (At.pseats Zp)) =
      (membersOf loSix).map (noK10 (At.seats Zp) loSix (At.pseats Zp) 0) := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  rw [e1, e2, noFiveAt_written]
  exact hno_written

/-- **THE HINGE AT LINK 0, AT THE FIVE-LIST.** -/
theorem AtMg.hinge_five (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch 12 a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) :=
  fun Gr hGr => shapesAre_five_of_six h.hno (h.hinge_zero FF hM a hr hu Gr hGr)

/-- **THE SAME AT THE NUMBER OF THE CONSTANT's OWN LIST OF PLACES.** -/
theorem AtMg.hinge_five_at_border (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps 0 + 3) a) (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) :=
  fun Gr hGr => shapesAre_five_of_six h.hno (h.hinge_zero_at_border FF hM a hr hu Gr hGr)

end P5J

#print axioms VerifiableInference.Desc.First.Close.hno_written
#print axioms VerifiableInference.Desc.First.Close.hno_other
#print axioms P5J.AtMg.hno
#print axioms P5J.AtMg.hinge_five
#print axioms P5J.AtMg.hinge_five_at_border
