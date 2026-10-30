-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER's FIRST SCRIPT: NOT THE HONEST PROVER's FILLING: Q := `firstScriptAt` I Sz.ref Op A cF.
AtFullSide/Honest/K3/Term/FirstScriptLaysTheCells.lean: the honest side of the kind "lookup" (K3):
FIELDS 1, 2 AND 4 of `LookupsAskOfTheScript` (Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean) at the
closed Script of AtFullSide/K1/FirstScript.lean, A any return of the maker at the base filling, at
the readers `readersB` I A.Z and the index's reader I.weights A.Z; the public part is A.Z. By calls
of the Script's authors' laws. No definition; four theorems.

  `baseBookHandsEverySwitchItsCoins`     at the maker's book each switch's part is handed its
                                         coins: TWO premises
  `firstScriptLaysTheCellsAtEveryLink`   FIELD 1, cellsAreLaid: FOUR premises
  `firstScriptsReadersReadTheTrace`      FIELD 2, readersReadTheTrace: no premise: by definition
  `firstScriptsStoredCellsAreTheIndex`   FIELD 4, storedCellsAreTheIndex: TWO premises

THE PREMISES; this file shows none of them:
  atHead         the library's hypothesis `P5J.AtMgA`, at the earlier hash, AT THE PUBLIC PART A.Z
  makerReturns   `onlineProverFromPublicFiles` returns A at `onlineProverPartsInUse` I secondHashFunction Sz.ref Op
  validInputsStartWell (field 1)   ON THE VALID INPUTS' PUBLIC INSTANCES: the description's own test
                 `okStart`
  closingsReturnAtZeros (field 1)  ON PUBLIC DATA: `K2.closingOk` at EVERY place of `K2.switchPlaces`
                 A.Z A.G: THE END OF `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean) TO THE LETTER, at
                 A.G: that law has it from the head alone. It is not called here.
                 MIND: FirstScriptLaysTheOwnersTexts.lean has
                 a premise of the same name that binds the places with a link below 25 alone; this
                 one binds every place, as `laysFilling_switches` asks, and gives that one
  validInputsHoldTheHonestTrace (field 4)   ON THE INPUT: spent for ONE thing: outside the stored
                 table's rows and columns the index's reader answers 0, as the letters' reader
                 does. Inside the table the field holds by the Script's definition, at every input
THE NUMBER OF CHALLENGES in field 1 is written out: roundsTo cF.blocksInOrder (borderOf link false): it is
`challengesHeardAtTheLookup` cF link false by that definition's text; the structure's file is not
imported.
SHOWN: at link 0: `laysFilling_opening` (AtFullSide/K1/LaysAtOpening.lean), whose bound on the number
is paid: the rounds in front of member number 2 stand in front of the first lookup. At the links 1
to 24: `laysFilling_switches` (AtFullSide/K1/LaysAtSwitches.lean), at every number. Of the three
premises that it leaves open TWO ARE PAID BY CALLS, at every place: `K2.handed` answers:
`handed_at_book` (AtFullSide/K2/HandedAtTheBook.lean), at the book that `atPure_book` and
`sends_written_at_files` name · `K2.publicOk`: `publicOk_at_head` (Honest/K5/Law/PublicOkPaid.lean),
from validInputsStartWell. The third is closingsReturnAtZeros.

Limits. The seat and "heard" of field 1 are the authors': `firstSeat` at link 0, `K2.switchSeat`
behind; "no challenge has been heard". At valid := fun _ => False fields 1 and 4 say nothing. Main
rows alone. Fields 3, 5, 6, 7 are not here. The full size and the sizes Sz.ref alone. Nothing on
soundness, completeness, hiding or any other property of a protocol.
-/
import AtFullSide.K1.LaysAtOpening
import AtFullSide.K2.HandedAtTheBook
import Johnson.Desc.ProofFile.Honest.K5.Law.PublicOkPaid
import Johnson.Desc.ProofFile.Honest.K14.BookAtPure
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest.K3.Term
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB laysFilling_opening laysFilling_switches)
open ProofFile.Honest.K5 (LaysFilling)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}

/-- **AT THE MAKER's BOOK EACH SWITCH's PART IS HANDED ITS COINS, at all coins of a run.** General in
the filling. Conditional on the head at A.Z and the maker's return. `handed_at_book` at the book that
the maker makes. -/
theorem baseBookHandsEverySwitchItsCoins {Rc Tr X₀ X : Type} {filling : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (atHead : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x₀)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL filling = .ok A) :
    ∀ place ∈ K2.switchPlaces A.Z A.G, ∀ k : Coins A.B, (K2.handed 0 place k).isSome = true := by
  intro place placeIsListed k
  obtain ⟨base, blocks, opened⟩ := atHead.laid.opened
  obtain ⟨-, groundIs, -⟩ := atPure_at_laid_ground atHead.laid opened.blank makerReturns
  obtain ⟨-, -, descriptionIsMade, -⟩ := atPure_ok makerReturns
  have descriptionIs : A.F = P5J.F0T OnBytes.secondHashFunction A.Z Np cF :=
    Except.ok.inj (descriptionIsMade.symm.trans atHead.laid.value)
  obtain ⟨_, _, _, _, _, _, _, sendingsAreRead, bookIsMade⟩ := atPure_book makerReturns
  obtain ⟨_, sendingsAre⟩ :=
    ProofFile.Honest.K14.sends_written_at_files atHead.scope atHead.laid sendingsAreRead
  simp only [List.cons.injEq, and_true] at sendingsAre
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := sendingsAre
  rw [descriptionIs] at bookIsMade
  rw [groundIs] at placeIsListed
  exact AtFullSide.K2.handed_at_book atHead opened bookIsMade placeIsListed k

/-- **FIELD 1 AT THE FIRST SCRIPT: at each of the 25 links the messages of moment 0 hold what the
frame's filling lays in their main rows**, from the challenges heard in front of the link's lookup on
the calls. Conditional on the head at A.Z, the maker's return, validInputsStartWell and
closingsReturnAtZeros. -/
theorem firstScriptLaysTheCellsAtEveryLink (atHead : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x₀)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (valid : LocB W₀ → Prop)
    (validInputsStartWell : ∀ input, valid input →
      (P5J.F0T OnBytes.secondHashFunction A.Z Np cF).okStart input.x = true)
    (closingsReturnAtZeros : ∀ place ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true) :
    ∀ link, link < 25 → ∃ (seat : MsgAddr → Option (Nat × Nat)) (heard : MsgAddr → Nat),
      LaysFilling atHead (firstScriptAt I Sz.ref Op A cF) valid
        (roundsTo cF.blocksInOrder (borderOf link false)) (readersB I A.Z) seat heard link := by
  intro link linkBelow
  rcases Nat.eq_zero_or_pos link with linkIsTheFirst | linkIsLater
  · subst linkIsTheFirst
    refine ⟨_, _, laysFilling_opening atHead makerReturns valid ?_⟩
    rw [Nat.zero_add]
    exact roundsTo_mono cF.blocksInOrder _ _ (by decide)
  · obtain ⟨base, blocks, opened⟩ := atHead.laid.opened
    obtain ⟨-, groundIs, -⟩ := atPure_at_laid_ground atHead.laid opened.blank makerReturns
    exact ⟨_, _, laysFilling_switches atHead makerReturns valid _
      (baseBookHandsEverySwitchItsCoins atHead makerReturns)
      closingsReturnAtZeros
      (fun place placeIsListed input isValid =>
        K5.publicOk_at_head atHead (by rw [groundIs]; exact opened.blank)
          (validInputsStartWell input isValid) place placeIsListed)
      linkIsLater linkBelow⟩

/-- **FIELD 2 AT THE FIRST SCRIPT's READERS: as cells they read the input's own trace.** By
definition. -/
theorem firstScriptsReadersReadTheTrace (input : LocB W₀) :
    (readersB I A.Z input).cells = input.trace :=
  rfl

/-- **FIELD 4 AT THE FIRST SCRIPT: the stored table's entries, as the letters read them off the
witness, are the index's reader's**, at every row and column. Conditional on the head at A.Z and on
validInputsHoldTheHonestTrace, which is spent outside the table alone. -/
theorem firstScriptsStoredCellsAreTheIndex (atHead : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x₀)
    (valid : LocB W₀ → Prop)
    (validInputsHoldTheHonestTrace : ∀ input, valid input →
      ∃ index request, InputHoldsTheHonestTrace A.Z (I.weights A.Z) input index request) :
    ScriptCellsAreTheIndexWeights (firstScriptAt I Sz.ref Op A cF) atHead.𝔇.l3 valid 0
      fun input => (I.weights A.Z input.w₀).entry := by
  intro k input heard isValid _ row column
  show VerifiableInference.Desc.First.Look.Stored.wOfC
    (VerifiableInference.Desc.First.Look.Stored.msgWc
      ((firstScriptAt I Sz.ref Op A cF).wit k input heard)) row column = _
  unfold VerifiableInference.Desc.First.Look.Stored.wOfC
  by_cases inside : row < OnBytes.Flat.numsFull.rows ∧ column < P5J.colsAt OnBytes.Flat.numsFull
  · rw [dif_pos inside]
    rfl
  · rw [dif_neg inside]
    obtain ⟨index, request, holds⟩ := validInputsHoldTheHonestTrace input isValid
    have entryIsZero : OnBytes.HonestTrace.entryZ index row column = 0 :=
      OnBytes.HonestTrace.entryZ_out index fun within => inside ⟨within.1, by
        have columnsAre : P5J.colsAt OnBytes.Flat.numsFull = 2 ^ Inst.Model.Layout.kRef :=
          congrArg (2 ^ ·) OnBytes.Flat.full_columns
        rw [columnsAre]
        exact within.2⟩
    show (0 : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E ((I.weights A.Z input.w₀).entry row column)
    rw [holds.weightsAreTheIndex]
    show (0 : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E
      ((OnBytes.HonestTrace.entryZ index row column : ℤ) : Cb.Gl.F)
    rw [entryIsZero]
    simp

end AtFullSide.Honest.K3.Term

#print axioms AtFullSide.Honest.K3.Term.baseBookHandsEverySwitchItsCoins
#print axioms AtFullSide.Honest.K3.Term.firstScriptLaysTheCellsAtEveryLink
#print axioms AtFullSide.Honest.K3.Term.firstScriptsReadersReadTheTrace
#print axioms AtFullSide.Honest.K3.Term.firstScriptsStoredCellsAreTheIndex
