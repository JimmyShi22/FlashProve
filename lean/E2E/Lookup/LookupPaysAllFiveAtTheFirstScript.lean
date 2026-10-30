-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT THE BASE PROVER: NOT THE HONEST PROVER's FILLING: onlineFilling is this one read through tableCoins; the crossing is not here.
E2E/Lookup/LookupPaysAllFiveAtTheFirstScript.lean: the honest side of the kind "lookup" (K3).
CONDITIONAL. NO PREMISE ON WHAT THE SCRIPT HOLDS IS LEFT; ONE PUBLIC TEST IS, closingsReturnAtZeros:
the structure `LookupsAskOfTheScript` (Honest/K3/Term/WhatTheLookupsAskOfTheScript.lean) is shown at
the senders' own Script `firstScriptAt` (AtFullSide/K1/FirstScript.lean), field by field, by calls.
Then, at a return A of the base maker `ProofFile.Honest.Term.baseMaker files` (E2E/BaseMaker.lean) and at
the first chain's thread `firstThread` (Honest/Thread/TheFirstThread.lean) whose Script is that one:
the debt `ExchangeS` and all five statements that a lookup owes, at each of the fifty borders
`borderOf l d`, l below 25. No definition; three theorems.

  `firstScriptMeetsWhatTheLookupsAsk`   five premises; the letters I and Op are variables
      `LookupsAskOfTheScript` at `firstScriptAt I Sz.ref Op A cF`, at closed letters
  `lookupExchangeAtTheFirstThreadAtTheFirstScript`   five premises, listed below
      `ExchangeS (firstThread …) Said (borderOf l d)`
  `lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript`   the same five premises
      `FiveAtBorder (firstThread …) Said fall (borderOf l d)`, at every fall

THE FIVE PREMISES of `firstScriptMeetsWhatTheLookupsAsk`: closingsReturnAtZeros, as below; atHead,
the library's hypothesis `P5J.AtMgA` at A.Z; makerReturns, at the base filling at I, the earlier
hash, `Sz.ref` and Op; validInputsStartWell, each valid input's instance passes the description's
test okStart; validInputsHoldTheHonestTrace, each valid input holds the honest trace of a served
request, at the reader I.weights A.Z.

THE FIVE PREMISES of the two tops, each under its name. None is shown in this file.
  1  makerReturns                  `baseMaker files` returns A
  2  headAtTheReturn               `HeadAtReturn`: the library's hypothesis `P5J.AtMgA` at A.Z
  3  scriptIsTheFirstScript        an equation on the letter parts: its Script is `firstScriptAt`
                                   at `matrixInput`, `Sz.ref`, `openHonest`, A and the head's first
                                   chain
  4  saidGivesWordsBelowThePrime   Said gives `SaidOk`
  5  closingsReturnAtZeros         ON PUBLIC DATA: at every switch's place the closing's test says
                                   yes at zeros: the end of `K2.Law.closing_at_head`
                                   (Honest/K2/Law/ClosingAtHead.lean) at A.Z and A.G. That law's
                                   files are NOT imported here: they cost more than a ride of ours
                                   holds

WHO PAYS WHICH FIELD.
  1 cellsAreLaid · 2 readersReadTheTrace · 4 storedCellsAreTheIndex
      `firstScriptLaysTheCellsAtEveryLink`, `firstScriptsReadersReadTheTrace`,
      `firstScriptsStoredCellsAreTheIndex` (AtFullSide/Honest/K3/Term/FirstScriptLaysTheCells.lean)
  3 digitsAreLaid
      `ProofFile.Honest.K1.digitsSentence_paid` (AtFullSide/K1/FrontAtDigits.lean), at the ground A.G,
      which is the one that `blankBy` makes (`atPure_ok`)
  5 openingsTextIsLaid · 6 switchesTextsAreLaid · 7 switchTextsAnswer
      `firstScriptLaysTheOpeningsText`, `firstScriptLaysTheSwitchesTexts`,
      `switchTextsAnswerAtTheBaseBook`
      (AtFullSide/Honest/K3/Term/FirstScriptLaysTheOwnersTexts.lean); the last one's two public
      premises: premise 5, and `baseBookHandsEverySwitchItsCoins` (FirstScriptLaysTheCells.lean)
At the tops the valid inputs are `ReadyInput`: its first clause is okStart, and the trace is
`readyInputsAtTheBaseMakerHoldTheHonestTrace` (E2E/Lookup/LookupPaysAllFiveAtTheBaseMaker.lean).

Limits. The two tops are implications from `ThrS` and the member's step: no state is shown to meet
these at any border. That their five premises can hold together is not shown here. The elder row
`proverSideOfLookupInChainAtOneOwner`. The full size alone. Nothing
on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.LookupPaysAllFiveAtTheBaseMaker
import AtFullSide.Honest.K3.Term.FirstScriptLaysTheCells
import AtFullSide.Honest.K3.Term.FirstScriptLaysTheOwnersTexts
import AtFullSide.K1.FrontAtDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term
open AtFullSide.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread)
open ProofFile.Honest.K1 (LocB firstScriptAt witB readersB lotNo lotData digitsSentence_paid)
open ProofFile.Honest.Term (baseMaker matrixInput)

/-! ## 1 The structure at the senders' own Script -/

section AnyIndex
variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE SENDERS' OWN SCRIPT MEETS ALL THAT THE LOOKUPS ASK OF A SCRIPT.** Conditional on the head
at A.Z, the maker's return at the base filling, the public test closingsReturnAtZeros, and two
premises on the valid inputs: they start well, and they hold the honest trace of a served request.
-/
theorem firstScriptMeetsWhatTheLookupsAsk (atHead : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x₀)
    (makerReturns : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (closingsReturnAtZeros : ∀ place ∈ K2.switchPlaces A.Z A.G,
      K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true)
    (valid : LocB W₀ → Prop)
    (validInputsStartWell : ∀ input, valid input →
      (F0T OnBytes.secondHashFunction A.Z Np cF).okStart input.x = true)
    (validInputsHoldTheHonestTrace : ∀ input, valid input →
      ∃ index request, InputHoldsTheHonestTrace A.Z (I.weights A.Z) input index request) :
    LookupsAskOfTheScript atHead makerReturns (firstScriptAt I Sz.ref Op A cF) valid
      (I.weights A.Z) (readersB I A.Z) (witB I A.Z) ()
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (lotData Sz.ref A.Z A.G)
      (widerRows Sz.ref A.Z A.G) A.G.first.layout (K2.segmentsOf A.Z A.G)
      (challengesReadByTheMaskRowsSender cF) :=
    { cellsAreLaid :=
        firstScriptLaysTheCellsAtEveryLink atHead makerReturns valid validInputsStartWell
          closingsReturnAtZeros
      readersReadTheTrace := firstScriptsReadersReadTheTrace
      digitsAreLaid := fun ground isTheBlankGround link linkBelow => by
        obtain rfl : A.G = ground :=
          Option.some.inj ((atPure_ok makerReturns).2.1.symm.trans isTheBlankGround)
        exact digitsSentence_paid atHead makerReturns valid _ linkBelow
      storedCellsAreTheIndex :=
        firstScriptsStoredCellsAreTheIndex atHead valid validInputsHoldTheHonestTrace
      openingsTextIsLaid := firstScriptLaysTheOpeningsText atHead makerReturns valid
      switchesTextsAreLaid := firstScriptLaysTheSwitchesTexts atHead makerReturns valid
      switchTextsAnswer :=
        switchTextsAnswerAtTheBaseBook atHead makerReturns
          (fun place placeIsListed _ => closingsReturnAtZeros place placeIsListed)
          (fun place placeIsListed _ =>
            baseBookHandsEverySwitchItsCoins atHead makerReturns place placeIsListed)
          validInputsStartWell }

end AnyIndex

/-! ## 2 At the base maker and the first thread -/

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
  (makerReturns : baseMaker files = .ok A)
  (headAtTheReturn : HeadAtReturn files A) (parts : FirstThreadParts A)
  (scriptIsTheFirstScript : parts.script =
    firstScriptAt matrixInput Sz.ref openHonest A headAtTheReturn.firstChain)
  (closingsReturnAtZeros : ∀ place ∈ K2.switchPlaces A.Z A.G,
    K2.closingOk K2.freshTable ((K2.segmentsOf A.Z A.G).take place.link) place = true)
  (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

include makerReturns scriptIsTheFirstScript closingsReturnAtZeros in
/-- **`ExchangeS` AT EACH OF THE LOOKUPS' FIFTY BORDERS OF THE FIRST THREAD, AT THE SENDERS' OWN
SCRIPT.** Conditional on the five premises that this file's head lists. -/
theorem lookupExchangeAtTheFirstThreadAtTheFirstScript
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (l : Nat) (linkBelow : l < 25) (d : Bool) :
    ExchangeS (firstThread headAtTheReturn parts w) Said (borderOf l d) := by
  have met := firstScriptMeetsWhatTheLookupsAsk headAtTheReturn.head makerReturns
    closingsReturnAtZeros (ReadyInput headAtTheReturn.description A.H) (fun _ ready => ready.1)
    (readyInputsAtTheBaseMakerHoldTheHonestTrace makerReturns headAtTheReturn)
  rw [← scriptIsTheFirstScript] at met
  exact lookupExchangeAtTheFirstThreadOfTheBaseMaker makerReturns headAtTheReturn parts w Said
    saidGivesWordsBelowThePrime met l linkBelow d

include makerReturns scriptIsTheFirstScript closingsReturnAtZeros in
/-- **ALL FIVE STATEMENTS THAT A LOOKUP OWES, AT EACH OF THE FIFTY BORDERS OF THE FIRST THREAD, AT
THE SENDERS' OWN SCRIPT.** Conditional on the same five premises. -/
theorem lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (l : Nat) (linkBelow : l < 25) (d : Bool) :
    FiveAtBorder (firstThread headAtTheReturn parts w) Said fall (borderOf l d) := by
  have met := firstScriptMeetsWhatTheLookupsAsk headAtTheReturn.head makerReturns
    closingsReturnAtZeros (ReadyInput headAtTheReturn.description A.H) (fun _ ready => ready.1)
    (readyInputsAtTheBaseMakerHoldTheHonestTrace makerReturns headAtTheReturn)
  rw [← scriptIsTheFirstScript] at met
  exact lookupPaysAllFiveAtTheFirstThreadOfTheBaseMaker makerReturns headAtTheReturn parts w Said
    saidGivesWordsBelowThePrime met fall l linkBelow d

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.firstScriptMeetsWhatTheLookupsAsk
#print axioms AtPublicFiles.Lookup.lookupExchangeAtTheFirstThreadAtTheFirstScript
#print axioms AtPublicFiles.Lookup.lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript
