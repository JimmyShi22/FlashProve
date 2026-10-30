-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FiveAtFirstThread.lean: the five debts of the code switch at each of its 25 members, at
the first thread as it is written, over the prover that the maker returns at the base filling, with
the written Script of the first chain in the script's place.

  k2_five_first_of   FiveAtBorder at each member of the kind, under K2Asks

The premises are the maker's return, the head at that return, hOk (what the laws read of Said) and
hK: K2Asks at each opening and each form of the script's letters.

Limits. Where the maker does not return, or no head stands at the return, the theorem holds of
nothing.
-/
import AtFullSide.K2.FiveAtBase
import AtFullSide.K1.FirstScriptIsSenders
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Base
open VerifiableInference.Desc (Chain Block Place KindName)
open P5J (TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open AtPublicFiles.AtFiles
open ProofFile.Honest
open ProofFile.Honest.K1
open ProofFile.Honest.Term
open ProofFile.Honest.FirstThread

set_option maxHeartbeats 4000000 in
/-- **The five debts at each member of the kind, at the first thread with the written Script**, under
K2Asks. -/
theorem k2_five_first_of {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hp : parts.script =
      firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A hd.firstChain)
    (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hK : ∀ (Bs : ProofFile.PureBase) (base : List (Block TS ProofFile.Cl))
      (_ : IM.Open OnBytes.secondHashFunction files.pol files.lay files.KL
        (F0T OnBytes.secondHashFunction A.Z hd.places hd.firstChain) A.Z Bs base hd.firstChain
        (seatZ A.Z hd.places) (secondAt A.Z hd.places))
      (S : ScriptLetters matrixInput A A.Z Bs hd.firstChain Unit Unit),
      K2Asks hd.head matrixInput A Bs (K1.PlaceIn ProofFile.Inst) Unit S.Q
        (fallsAfterBatching (firstFalls A parts.numbers) hd.firstChain) 0 hd.description.t₁
        hd.description.t₂ 339 (ReadyInput hd.description A.H)
        (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
        (kpBy (firstClauses hd)) w Said)
    {b : Nat} {q : Place} (hb : P5J.At.ps[b]? = some q) (hq : q.kind = KindName.K2) :
    FiveAtBorder (firstThread hd parts w) Said fall b := by
  obtain ⟨Bs, base, O⟩ := hd.head.laid.opened
  obtain ⟨pl, -, h6, -⟩ := firstScript_written_head (I := matrixInput)
    (S := OnBytes.HonestTrace.Sz.ref) (Op := openHonest) hd.head hA
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground hd.head.laid O.blank hA
  have eS : seatGround A = Bs.G₀ := seatGround_of_base O.made
  obtain ⟨pl', hf, e⟩ := otherSenders_at_head (I := matrixInput)
    (S := OnBytes.HonestTrace.Sz.ref) (Op := openHonest) (cF := hd.firstChain) hd.head hA
  obtain ⟨S, eQ⟩ : ∃ S : ScriptLetters matrixInput A A.Z Bs hd.firstChain Unit Unit,
      S.Q = firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A hd.firstChain := by
    refine ⟨{ no := lotNo OnBytes.secondHashFunction A.Z
              Dd := K13.wDataAt openHonest.pile
              cellsQ := cellsB matrixInput A.Z
              tokQ := tokB
              own₀ := ()
              rest := noTree
              ch := 0
              Jt := testJobAt matrixInput OnBytes.HonestTrace.Sz.ref A.Z A.G pl'
              stages := testJob_six hd.head pl'
              own₂ := ()
              n₀ := roundsTo hd.firstChain.blocksInOrder 354
              ok := testOk
              codes := pl'.sizes.codes
              sh := fun τ => shapeAtSeat A.Z (77 + τ) 0
              sh₁ := fun τ => shapeAtSeat A.Z (77 + τ) 1
              rest₂ := noTree
              Oth := otherSendersAt matrixInput OnBytes.HonestTrace.Sz.ref A hd.firstChain
              share := ?_ }, ?_⟩
    · rw [← eG, show rowsAt A.Z Bs = K2.withSwitchData OnBytes.HonestTrace.Sz.ref
        (K1.lotData OnBytes.HonestTrace.Sz.ref) A.Z A.G from by rw [eG]]
      exact e
    · rw [firstScript_is_record hd hA]
      unfold SendersRecord.script
      rw [eS]
      rfl
  have e2 : parts.script = S.Q := hp.trans eQ.symm
  show FiveAtBorder (baseLetters hd.head A parts.script
    (fallsAfterBatching (firstFalls A parts.numbers) hd.firstChain) 0 hd.description.t₁
    hd.description.t₂ 339 (ReadyInput hd.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses hd)) w).thread Said fall b
  rw [e2]
  exact k2_five matrixInput openHonest hA hd.head O S _ 0 _ _ _ nextSlotBehindTheHead
    (digitsStand A.Z) (heardByAttention A.Z) (seatGround A) P1L20.bearing
    (K11.parOf A.Z (seatGround A)) (H2U.p12OfMade A.Z.made)
    (VerifiableInference.Desc.K13.whereOf A.Z) w Said fall hOk (hK Bs base O S) hb hq

end AtFullSide.K2.Base

#print axioms AtFullSide.K2.Base.k2_five_first_of
