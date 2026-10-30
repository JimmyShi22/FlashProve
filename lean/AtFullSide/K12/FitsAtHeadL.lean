-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/FitsAtHeadL.lean: UNDER THE LIBRARY's HEAD (`P5J.AtMg`), AT THE BLANK GROUND: the
code switch has its finish (`finishAt`, Johnson/Desc/ProofFile/Honest/K12/AtProof/JobL.lean), and
the public test `fitsL` of the lot at the first chain's proximity test says yes there, at the
planner's own numbers. So that lot, with the filled door (`lotAtDoor`, AtProof/LotAtDoor.lean),
gives just one half. One definition; six theorems.

  `fitsL_of_reads`   `fitsLs` reads of the test's parameters the numbers and the place alone
  `finishW`        the finish among the code switch's places at the library's written values
  `fitsL_written`  THE CLOSED FACT, by Lean's kernel: a finish is there, and all sixteen clauses say
                 yes
  `fitsL_written_no`   a control, by Lean's kernel: at another test's stages the test says no
  `places_head`    under the head, at the blank ground, `K2.switchPlaces` is `K2.Law.placesW`
  `fitsL_head_L`, `halves_head_L`   the laws

By what. Of the test's parameters: `numbersL_at_head` (AtProof/LotAtDoor.lean), `nums_head_L`
(AtFullSide/K12/RestTiesAtHeadL.lean), `placeL_of_four`
(Johnson/Desc/ProofFile/Honest/K12/Blind/AtHandAtFinish.lean): under the head the numbers and the
place are those of the written `piLFull` (Johnson/Desc/K12/Law/PlacesFull.lean). Of the sender's
place: `K2.Law.switchPlaces_is` and `K2.Law.placesW`
(Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean, by the authors of the code switch's honest
side): `K2.switchPlaces` is one text at what two look-ups return; `IM.prep_pinned`
(Johnson/IMR/SendsPinned.lean) with `pins_at_head`
(Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean), and `spots_at_head`
(Johnson/AtFull/Shape/LinkNumbersAtHead.lean), make both look-ups the written values: the road of
`membersL_185` (AtFullSide/K12/TiesAtHeadL.lean). Then two evaluations in Lean's kernel.

Kin. `K2.Law.places_at_head` (PlacesWritten.lean): the same equation under the head at the format's
second hash function and the opening. By their authors' letter, `fits_at_head` (K2/Law/PublicAtHead.lean,
not in the library) says under these that each place's own sending passes the shared sending's
public test (`placeFits`, K2/Law/PlanAsks.lean); it is not called here. How many of the sixteen
clauses it would give has not been looked at; most tie the test's numbers to the sender's, of which
that file does not speak.

Limits.
- The full size alone: the library's written values.
- At the blank ground (hG): `prep_pinned`'s own premise. It is the ground at which the frame's
  `onlineProverFromPublicFiles` makes its filling.
- That a ground as in hG is there is not shown here; the library concludes it elsewhere
  (`blank_returns_pub`, Johnson/AtFull/Desc/BlankReturns.lean; `IM.Open.blank`,
  Johnson/IMR/SeatOpen.lean).
- The control bends the stages alone: the clauses that read the other numbers and the place have
  none. Which clauses say no there is not stated: an evaluation outside the library named seven.
- That the lot gives a half says nothing on whether its two parts play, return or are accepted: they
  cannot refuse.
- That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
  (`head_of_live`, Johnson/P5J/HeadOfLive.lean, then `toAtMg`: that theorem's head is `AtMgA`); that
  these three hold together, at two named sets of public files (`headMember_named`,
  AtFullSide/Top/HeadMemberAtGap.lean).
- In the side library, since `nums_head_L` is. One limit is raised at the two closed facts:
  maxRecDepth to 1000000.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.RestTiesAtHeadL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.AtFull.Shape.LinkNumbersAtHead
import Johnson.Desc.First.Att.Door.Law.K5CondOfHead
import Johnson.IMR.SendsPinned
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12 T12)
open H2K.Member (piLFull piWFull)
open P5J (TS)

variable {V W₀ Rc Tr X : Type}

/-! ## 1 What the test reads of the test's parameters -/

/-- `fitsLs` reads of the test's parameters the numbers and the place alone. -/
theorem fitsL_of_reads {q q' : P12} (hn : q.nums = q'.nums) (hp : q.place = q'.place)
    (p : K2.SwitchPlace) : fitsL q p = fitsL q' p := by
  simp only [fitsL, fitsLs, hn, hp]

/-! ## 2 The closed facts, at the library's written values -/

/-- The first of the code switch's places at the written values (`K2.Law.placesW`,
Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean) without a link: the finish. -/
def finishW : Option K2.SwitchPlace := K2.Law.placesW.find? fun p => p.place.link.isNone

set_option maxRecDepth 1000000 in
/-- **The closed fact**: there is a finish, and the public test says yes at it, at the written place
of the first chain's proximity test. -/
theorem fitsL_written : finishW.any (fitsL piLFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The control: the written place with the stages of the test on W's side in the place of its own
(first stage (5, 1) for (1, 0)); the place is kept, so that it is the clauses on the stage that say
no. Alone this "false" could come of a lacking finish; `fitsL_written` shows that one is there. -/
theorem fitsL_written_no : finishW.any (fitsL { piLFull with
    nums := { piLFull.nums with stages := piWFull.nums.stages } }) = false := by decide +kernel

/-! ## 3 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under the head, at the blank ground, the code switch's places are the written ones. A sister of
`K2.Law.places_at_head` (PlacesWritten.lean), which has the opening, at the format's second hash function,
where this has hG, at every o. -/
theorem places_head (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    K2.switchPlaces Zp G = K2.Law.placesW := by
  have hp : P1K2.prepOf Zp G = IM.prepW :=
    IM.prep_pinned h.laid.pub (H2K5.Door.pins_at_head h).1 hG
  have hs : ProofFile.spotsOf Zp.cuts = some Johnson.AtFull.Desc.spotsWritten :=
    Johnson.AtFull.Shape.spots_at_head h
  rw [K2.Law.switchPlaces_is, hp, hs]
  rfl

/-- **UNDER THE HEAD, AT THE BLANK GROUND: THE FINISH IS THERE, AND THE LOT's PUBLIC TEST SAYS
YES.** -/
theorem fitsL_head_L (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) :
    ∃ pl, finishAt Zp G = some pl ∧ fitsL (H2U.p12OfMade Zp.made) pl = true := by
  have e : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h hG]
  have hw := fitsL_written
  cases hf : finishW with
  | none =>
    rw [hf] at hw
    cases hw
  | some pl =>
    rw [hf] at hw
    refine ⟨pl, e.trans hf, ?_⟩
    rw [fitsL_of_reads (q' := piLFull) (by rw [numbersL_at_head h]; exact Light.nums_head_L h)
      (by rw [numbersL_at_head h]; exact Blind.placeL_of_four Np) pl]
    exact hw

/-- So the lot with the filled door gives just one half there. -/
theorem halves_head_L (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (D : ProofFile.Pub → Ground → RowDataOf ProofFile.Inst)
    (readers : ProofFile.Pub → Ground → Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : ProofFile.Pub → Ground → K2.Closing) :
    ∃ pl, finishAt Zp G = some pl ∧
      (lotAtDoor D readers closing : HLot V (Local W₀ Rc ProofFile.Inst Tr) X).halves Zp G =
        [proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) (D Zp G) (readers Zp G)
                           (closing Zp G) pl)] := by
  obtain ⟨pl, hf, hfit⟩ := fitsL_head_L h hG
  exact ⟨pl, hf, halves_lotAtDoor D readers closing Zp G pl hf hfit⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.fitsL_of_reads
#print axioms ProofFile.Honest.K12.AtProof.finishW
#print axioms ProofFile.Honest.K12.AtProof.fitsL_written
#print axioms ProofFile.Honest.K12.AtProof.fitsL_written_no
#print axioms ProofFile.Honest.K12.AtProof.places_head
#print axioms ProofFile.Honest.K12.AtProof.fitsL_head_L
#print axioms ProofFile.Honest.K12.AtProof.halves_head_L
