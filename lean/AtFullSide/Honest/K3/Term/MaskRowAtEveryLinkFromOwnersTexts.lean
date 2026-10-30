-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/K3/Term/MaskRowAtEveryLinkFromOwnersTexts.lean: the honest side of the kind "lookup"
(K3), at the full size: the lookups' one sentence `ScriptLaysEveryLinksMaskRow`
(Honest/K3/Term/MaskRowFromScript.lean) from `OwnMsgs` at the 25 senders' own whole-message texts.

Why. `ScriptLaysEveryLinksMaskRow` speaks in the letters of the book's maker: the owner and the start
that `ownerOf` returns at the written description, up to each lookup's last slot.
Honest/K3/Term/MaskRowOwnerAtTheWrittenBook.lean has the named premise at each link at a written owner
and start, up to 8192 entries. Here the two are joined: `ownerOf`'s 25 returns are written rows
(`rawRows_written`, AtFullSide/K14/RawFactsWritten.lean), whose owners and starts
are the written ones; and every lookup's last slot lies below 8191, under the head alone.

  `ownerOfIsTheWrittenRow`       what `ownerOf` returns at a link below 25 is the written row
  `writtenRowsBearWrittenOwners`, `writtenRowsBearWrittenOwnersBent`   a closed fact on the 25 rows; its control
  `lookupSlotsWritten`, `lookupSlotsFitTheMaskRow`   first + slots ≤ 8191 at every site
  `scriptLaysEveryLinksMaskRowFromOwnersTexts`   THE SENTENCE

Limits. Those of the files called hold here. At the full size, at the earlier hash. `OwnMsgs` at the owners' texts and `SwitchTextsAnswer` are premises: no Script is
laid here, and K2's three conditions are shown at no place. Nothing is claimed on soundness,
completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowOwnerAtTheWrittenBook
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Sites
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import AtFullSide.Honest.K3.Term.LookupThreeTestsUnderTheHeadAlone
import AtFullSide.K14.RawFactsWritten
import AtFullSide.K14.RawK3Sites

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.AtFull.Lots.K3 (sortOf firstW)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K1 (firstFold placeJob PlaceIn)
open ProofFile.Honest.K2 (switchPlaces)
open AtFullSide.K14 (rawRowsW rawRows_written rawRowsW_numbers k3Face)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open OnBytes.Maker (WholeD)

/-! ## 1 What `ownerOf` returns -/

/-- At a link below 25, what the book's maker finds as the owner of the link's mask row is the
written row of that link. -/
theorem ownerOfIsTheWrittenRow {l : Nat} (hl : l < 25) {r : MsgAt}
    (hOwner : ProofFile.Honest.ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1
      (WP.second.blocksInOrder.flatMap (·.rounds)) s!"link {l}, moment 0" isMaskRowMsg = some r) :
    (l, r) ∈ rawRowsW := by
  have hm : l ∈ rawRowsW.map (·.1) := by
    rw [rawRowsW_numbers]
    exact List.mem_range.2 hl
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
  obtain rfl : x.2 = r := Option.some.inj ((rawRows_written x hx).symm.trans hOwner)
  exact hx

/-- The 25 written rows' owners and starts are the written functions of the link. -/
theorem writtenRowsBearWrittenOwners : (rawRowsW.all fun x =>
    decide (x.2.owner = maskRowOwnerWritten x.1) && x.2.base.e == maskRowStartWritten x.1) =
      true := by
  decide

/-- BENT: with every start raised by one the test rejects every row. -/
theorem writtenRowsBearWrittenOwnersBent : (rawRowsW.any fun x =>
    decide (x.2.owner = maskRowOwnerWritten x.1) && x.2.base.e + 1 == maskRowStartWritten x.1) =
      false := by
  decide

/-! ## 2 The lookups' slots lie inside the row -/

/-- At the written numbers a lookup's last slot lies below 8191. -/
theorem lookupSlotsWritten : ((List.range 4).all fun σ => [false, true].all fun d =>
    decide (firstW σ d + (k3Face (vdW σ d).1 (vdW σ d).2).slots ≤ 8191)) = true := by
  decide +kernel

/-- **At every site, under the head alone: the lookup's last slot lies below 8191.** By the written
first scalar and the written levels, both under the head (`lookupFirstScalarIsWrittenUnderTheHead`,
`lookupLevelsAreWrittenUnderTheHead`, of this house's lot on the seat). -/
theorem lookupSlotsFitTheMaskRow {Z : VerifierAndGoals.PublicFiles} {D r Zp Np cF x}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    s.p.first + s.at_.face.slots ≤ 8191 := by
  have n1 := lookupFirstScalarIsWrittenUnderTheHead h s hs
  obtain ⟨n2, n3⟩ := lookupLevelsAreWrittenUnderTheHead h s hs
  obtain ⟨hf, -⟩ := FastLaw.sites_ok Zp s hs
  have e : s.at_.face.slots = (k3Face s.shape.v s.shape.d).slots := by
    rw [hf]
    rfl
  rw [e, n1, n2, n3]
  exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 lookupSlotsWritten _
    (List.mem_range.2 (sortOf_lt _))) s.digits (by cases s.digits <;> simp))

/-! ## 3 The sentence -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE LOOKUPS' ONE SENTENCE, FROM `OwnMsgs` AT THE 25 SENDERS' OWN WHOLE-MESSAGE TEXTS**, at the
book of whatever `onlineProverFromPublicFiles` returns, at every Script over that book. CONDITIONAL on: the head; hA; hOpening, at message number 0 of the opening; hSwitches, at
each switch that leads into a link below 25, at the message by `maskRowMessageInSwitch`; hAnswer,
K2's three conditions. challengesInFront, messageNumber, challengesRead: letters, by the link. -/
theorem scriptLaysEveryLinksMaskRowFromOwnersTexts
    (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Xi Tr Xj Y Cells Tok : Type} {Q : Script A.B (Local W₀ Rc Xi Tr) Cells Tok MsgT}
    {valid : Local W₀ Rc Xi Tr → Prop} {challengesInFront messageNumber challengesRead : Nat → Nat}
    (wit : Local W₀ Rc Xi Tr → PlaceIn Xj) (own₀ : Y) (first : Nat) (openingData : RowDataOf Xj)
    (hOpening : OwnMsgs Q valid (challengesInFront 0) (messageNumber 0) (challengesRead 0)
      (K1.msgTxt 0 wit
        (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) openingData) own₀ 0))
    (switchData : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub)
    (hAnswer : SwitchTextsAnswer A.B switchData lay segs valid (switchPlaces A.Z A.G))
    (hSwitches : ∀ p ∈ switchPlaces A.Z A.G, p.link < 25 →
      OwnMsgs Q valid (challengesInFront p.link) (messageNumber p.link) (challengesRead p.link)
        (K2.switchMsgTxt 0 switchData readers (K2.lotClosingAt lay segs) p
          (maskRowMessageInSwitch p.link))) :
    ScriptLaysEveryLinksMaskRow Q valid Zp challengesInFront messageNumber := by
  intro s hs r hOwner
  have hl := ProofFile.Honest.K3.Law.AtThr.link_lt_head h s hs
  have t := List.all_eq_true.1 writtenRowsBearWrittenOwners _ (ownerOfIsTheWrittenRow hl hOwner)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  rw [t.1, t.2]
  exact scriptLaysOwnersCoinsAtEveryLink h hA wit own₀ first openingData hOpening switchData readers
    lay segs hAnswer hSwitches s.link hl _
    (Nat.le_trans (lookupSlotsFitTheMaskRow h s hs) (by decide))

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.ownerOfIsTheWrittenRow
#print axioms AtFullSide.Honest.K3.Term.writtenRowsBearWrittenOwners
#print axioms AtFullSide.Honest.K3.Term.writtenRowsBearWrittenOwnersBent
#print axioms AtFullSide.Honest.K3.Term.lookupSlotsWritten
#print axioms AtFullSide.Honest.K3.Term.lookupSlotsFitTheMaskRow
#print axioms AtFullSide.Honest.K3.Term.scriptLaysEveryLinksMaskRowFromOwnersTexts
