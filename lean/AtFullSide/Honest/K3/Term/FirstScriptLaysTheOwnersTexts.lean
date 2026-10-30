-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER's BOOK AND AT K1's AUTHORS' CLOSED SCRIPT `firstScriptAt`.
AtFullSide/Honest/K3/Term/FirstScriptLaysTheOwnersTexts.lean: the honest side of the kind "lookup" (K3):
fields 5, 6 and 7 of `LookupsAskOfTheScript` (Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean) at the
first chain's Script at the base prover (`firstScriptAt`, AtFullSide/K1/FirstScript.lean), with every
letter that the sheet left a binder AT ITS VALUE; and, from them, the lookups' one sentence on the mask
rows at that Script.

THE VALUES, read off `firstScriptAt`'s text. The public part: A.Z. openingsLens := `witB` I A.Z ·
openingsOwnState := () · openingsFirstNumber := `lotNo` secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩ · openingsData :=
`lotData` S A.Z A.G (these four: `jobTwoAt` S A.Z A.G) · switchesData := `widerRows` S A.Z A.G · readers :=
`readersB` I A.Z · layout := A.G.first.layout · segments := `K2.segmentsOf` A.Z A.G (these two:
`closingB` A.Z A.G) · challengesRead := `challengesReadByTheMaskRowsSender` cF.

  `challengesReadByTheMaskRowsSender`     by the link: the rounds in front of the sender of its mask row
  `firstScriptLaysTheOpeningsText`        FIELD 5
  `firstScriptLaysTheSwitchesTexts`       FIELD 6
  `switchTextsAnswerAtTheBaseBook`        FIELD 7, at the sizes `Sz.ref`, under three named hypotheses
  `firstScriptLaysEveryLinksMaskRow`      `ScriptLaysEveryLinksMaskRow` at `firstScriptAt`, under the same three

THE THREE NAMED HYPOTHESES THAT STAY, each with its payer.
  closingsReturnAtZeros          K2's public test `closingOk` at each switch: K2's authors'
                                 `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean) has it under the head;
                                 it is not called here
  bookHandsEverySwitchItsCoins   at the book A.B the frame hands each switch's part its coins
                                 (`K2.handed`): K2's authors' `handed_at_book`, not at hand here
  validInputsStartWell           each valid input's public instance passes the description's own test
                                 `okStart`: on the letter valid: whoever lays the thread's valid

By calls: `tie_k1_first`, `ownMsgs_switch_first` (AtFullSide/K1/FirstScript.lean, K1's authors') ·
`publicOk_at_head`
(Honest/K5/Law/PublicOkPaid.lean, K5's authors') · this house's `openingsNumberIsThePlansNumber`,
`switchNumberIsThePlansNumber`, `maskRowMessageAtASwitchUnderTheHead`,
`scriptLaysEveryLinksMaskRowFromOwnersTexts`.

Limits. CONDITIONAL on the head at the public part A.Z and on the maker's return at the base filling.
The base prover's filling, not the honest prover's. The full size and the earlier hash alone. Nothing
is claimed on soundness, completeness, hiding or any other property of a protocol.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.Honest.K3.Term.MaskRowAtEveryLinkFromOwnersTexts
import Johnson.Desc.ProofFile.Honest.K3.Term.WhatTheLookupsAskOfTheScript
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowMessageIsFirstSentByItsSwitch
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K1 (firstPar gpOf parGF)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.FirstThread (OwnMsgs)
open ProofFile.Honest.K1 (firstScriptAt witB readersB LocB jobTwoAt lotNo lotData firstFold placeJob)
open ProofFile.Honest.K2 (switchPlaces)
open P5J (AtMgA TS F0T)

/-- **By the link: how many challenges the text of the sender of the link's mask row is handed**: the
rounds of the first chain in front of that sender: the opening, number 2 of the flat list, at link 0;
the switch at the written owner's place at a later link. -/
def challengesReadByTheMaskRowsSender (cF : Chain TS ProofFile.Cl) (link : Nat) : Nat :=
  if link = 0 then 0 + roundsTo cF.blocksInOrder 2
  else 0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder (maskRowOwnerWritten link).place)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FIELD 5 AT `firstScriptAt`.** Under the head and the maker's return alone, at every valid. -/
theorem firstScriptLaysTheOpeningsText (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (valid : LocB W₀ → Prop) :
    OwnMsgs (firstScriptAt I S Op A cF) valid (challengesHeardAtTheLookup cF 0 false)
      (maskRowMessageNumber A.Z 0) (challengesReadByTheMaskRowsSender cF 0)
      (K1.msgTxt 0 (witB I A.Z)
        (placeJob (firstPar A.G.first (gpOf A.Z)) (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩)
          (firstFold A.G.first) (lotData S A.Z A.G)) () 0) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have eP : firstPar A.G.first (gpOf A.Z) = parGF := by
    rw [eG]
    exact VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)
  have hsize : 0 < (jobTwoAt S A.Z A.G).P.sent.size := by
    show 0 < (firstPar A.G.first (gpOf A.Z)).sent.size
    rw [eP]
    exact openingHoldsMaskRowWritten.1
  have t := (K1.tie_k1_first h hA valid (y := (2, jobTwoAt S A.Z A.G))
    (K1.mem_k1MembersW.2 (.inl (K1.mem_k1Members.2 (.inl rfl))))).1 0 hsize
  have number : P5J.At.arr A.Z (K1.seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P 0).1
      (K1.seatAtMember cF.blocksInOrder 2 (jobTwoAt S A.Z A.G).P 0).2 = maskRowMessageNumber A.Z 0 := by
    show P5J.At.arr A.Z (K1.seatAtMember cF.blocksInOrder 2 (firstPar A.G.first (gpOf A.Z)) 0).1
      (K1.seatAtMember cF.blocksInOrder 2 (firstPar A.G.first (gpOf A.Z)) 0).2 = _
    rw [eG]
    exact openingsNumberIsThePlansNumber h O
  rw [number] at t
  intro k w hd hv hN
  exact t k w hd hv (Nat.le_trans (by
    rw [Nat.zero_add]
    exact roundsTo_mono cF.blocksInOrder 2 (borderOf 0 false) (by decide)) hN)

/-- **FIELD 6 AT `firstScriptAt`.** Under the head and the maker's return alone, at every valid. -/
theorem firstScriptLaysTheSwitchesTexts (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (valid : LocB W₀ → Prop) :
    ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
      OwnMsgs (firstScriptAt I S Op A cF) valid (challengesHeardAtTheLookup cF place.link false)
        (maskRowMessageNumber A.Z place.link) (challengesReadByTheMaskRowsSender cF place.link)
        (K2.switchMsgTxt 0 (widerRows S A.Z A.G) (readersB I A.Z)
          (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) place
          (maskRowMessageInSwitch place.link)) := by
  intro place hp hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨h1, hn, hfirst, hplace⟩ := maskRowMessageAtASwitchUnderTheHead h O (p := place)
    (by rw [← eG]; exact hp) hl
  have t := K1.ownMsgs_switch_first (I := I) (S := S) (Op := Op) h hA valid
    (challengesHeardAtTheLookup cF place.link false) hp hn hfirst
  have number : K2.switchNum A.Z place (maskRowMessageInSwitch place.link) =
      maskRowMessageNumber A.Z place.link := switchNumberIsThePlansNumber h place h1 hl
  have read : challengesReadByTheMaskRowsSender cF place.link =
      0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder place.place) := by
    unfold challengesReadByTheMaskRowsSender
    rw [if_neg (by omega), hplace]
  rw [number] at t
  rw [read]
  exact t

/-- **FIELD 7 AT THE BASE PROVER's BOOK**, at the sizes `Sz.ref`. CONDITIONAL on the head, the maker's
return and the three named hypotheses of the file's head. -/
theorem switchTextsAnswerAtTheBaseBook (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {valid : LocB W₀ → Prop}
    (closingsReturnAtZeros : ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true)
    (bookHandsEverySwitchItsCoins : ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
      ∀ k : Coins A.B, (K2.handed 0 place k).isSome = true)
    (validInputsStartWell : ∀ input, valid input →
      (F0T OnBytes.secondHashFunction A.Z Np cF).okStart input.x = true) :
    SwitchTextsAnswer A.B (widerRows Sz.ref A.Z A.G) A.G.first.layout (K2.segmentsOf A.Z A.G) valid
      (switchPlaces A.Z A.G) := by
  intro place hp hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  exact ⟨closingsReturnAtZeros place hp hl, bookHandsEverySwitchItsCoins place hp hl,
    fun input isValid => K5.publicOk_at_head h (by rw [eG]; exact O.blank)
      (validInputsStartWell input isValid) place hp⟩

/-- **THE LOOKUPS' ONE SENTENCE ON THE MASK ROWS, AT `firstScriptAt`**, at the sizes `Sz.ref`.
CONDITIONAL on the head, the maker's return and the three named hypotheses of the file's head. No
premise on the Script. -/
theorem firstScriptLaysEveryLinksMaskRow (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) =
      .ok A)
    {valid : LocB W₀ → Prop}
    (closingsReturnAtZeros : ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true)
    (bookHandsEverySwitchItsCoins : ∀ place ∈ switchPlaces A.Z A.G, place.link < 25 →
      ∀ k : Coins A.B, (K2.handed 0 place k).isSome = true)
    (validInputsStartWell : ∀ input, valid input →
      (F0T OnBytes.secondHashFunction A.Z Np cF).okStart input.x = true) :
    ScriptLaysEveryLinksMaskRow (firstScriptAt I Sz.ref Op A cF) valid A.Z
      (fun link => challengesHeardAtTheLookup cF link false) (maskRowMessageNumber A.Z) :=
  scriptLaysEveryLinksMaskRowFromOwnersTexts h hA
    (challengesRead := challengesReadByTheMaskRowsSender cF) (witB I A.Z) ()
    (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (lotData Sz.ref A.Z A.G)
    (firstScriptLaysTheOpeningsText h hA valid) (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
    A.G.first.layout (K2.segmentsOf A.Z A.G)
    (switchTextsAnswerAtTheBaseBook h hA closingsReturnAtZeros bookHandsEverySwitchItsCoins
      validInputsStartWell)
    (firstScriptLaysTheSwitchesTexts h hA valid)

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.challengesReadByTheMaskRowsSender
#print axioms AtFullSide.Honest.K3.Term.firstScriptLaysTheOpeningsText
#print axioms AtFullSide.Honest.K3.Term.firstScriptLaysTheSwitchesTexts
#print axioms AtFullSide.Honest.K3.Term.switchTextsAnswerAtTheBaseBook
#print axioms AtFullSide.Honest.K3.Term.firstScriptLaysEveryLinksMaskRow
