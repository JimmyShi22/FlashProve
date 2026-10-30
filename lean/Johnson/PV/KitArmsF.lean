-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE TEXT THAT IT TWINS IS VerifyVFastStepsD.lean's: WHETHER IT SERVES IS FOR A RUN TO SHOW.

Johnson/PV/KitArmsF.lean: THE KEY FILE's AND THE PROOF FILE's ARMS OF THE FAST FORM **AT THE KIT
  MADE FOR A RUN** (ckPT .two: Johnson/RunOne/DrawT.lean) IN THE LIBRARY's KIT's PLACE (ckP .two),
  THE FULL SIZE; WITH ONE EQUATION EACH TO THE ARM THAT IT TWINS (VerifyVFastStepsD.lean): by
  ckPT_eq : ckPT f = ckP f.
WHY (DrawT.lean's own head): «(ckP f).dr e k u reads the draws through the block sampler of the
  round, which is made for counting … At a round with very many entries that does not end in any
  useful time. The format's Fmt.drawRound walks a row of words once.» The forms for
a run (Johnson/RunOne/) go through
  ckPT; armTE | armBE call verifyWholeX at ckP.
THE MAKE (the manner of AskProof.lean's KitLets): what of verifyWholeX's arguments is typed over
  the kit (chal · embS · embP · the proof string) is one record KitW C; it is carried along an
  equation of kits (KitW.to: the identity at a run); runW C A … := verifyWholeX C … .
  runW_kit : runW C' (A.to h) … = runW C A …  (h : C' = C): by subst
  **armTET | armBET** · **armTET_eq | armBET_eq : … = armTE | armBE …**: no premise.
WHETHER THE KIT IS WHAT KEEPS armB FROM ENDING IS A GUESS UNTIL A RUN HAS SHOWN IT. No soundness.


-/
import Johnson.Top.Fire.Code.VerifyVFastStepsD
import Johnson.RunOne.DrawT
import Johnson.PV.KitCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (bodyS SOf)
open Johnson.RunOne (ckPT ckPT_eq)

variable {X : Type} (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull)
  (sT sB : Params.LinBindingShape) (early : X → X)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (K salt : ℕ)

local notation "LKe" => linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) ds frS.P.T.a xs dec
local notation "ALe" => _root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) ds)
local notation "LV" => LvOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "AT" => aTOf DK DP runK runP rK rP sB.logLeaves early LKe
local notation "CV" => carrierV LV (List Bool) AT ALe

/-- **The key's arm, at the kit made for a run.** -/
def armTET (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (cm : Dig 256) (rcd : RecFull)
    (fT : FileIn) (πT : OneProtocolProof 256 (batTV LV AT)) : Bool :=
  (W4K.runW (C := ckPT .two)
    ((⟨chalP .two K, SCode.emb _ (scWhole salt (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
        ByteArray.empty), id, πT⟩ :
      W4K.KitW (ckP .two) K (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty CV silK runK
          Tag.test).to (ckPT_eq .two))
    p.sMT p.sFS (fun _ => none) (bodyS frS.P.T.a salt).embE sT.logLeaves
    (cm :: codeA (v := frS.P.v) (s := 1) rcd.2) rcd (ownOfCarrier (DK.at frS.P.T.a) fT.k)
    (listedOfCarrier (DK.at frS.P.T.a).a fT.k)).det F

/-- **It is armTE (VerifyVFastStepsD.lean).** -/
theorem armTET_eq (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (cm : Dig 256) (rcd : RecFull)
    (fT : FileIn) (πT : OneProtocolProof 256 (batTV LV AT)) :
    armTET DK DP runK runP rK rP sT sB early ds xs dec K salt p F cm rcd fT πT =
      armTE DK DP runK runP rK rP sT sB early ds xs dec K salt p F cm rcd fT πT := by
  unfold armTET
  rw [W4K.runW_kit]
  rfl

/-- **The proof's arm, at the kit made for a run.** -/
def armBET (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (x : X) (e : EntryIn)
    (fB : FileIn) (πB : OneProtocolProof 256 (LV).bat) : Bool :=
  (W4K.runW (C := ckPT .two)
    ((⟨chalP .two K, SCode.emb _ (scWhole salt (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
        ByteArray.empty), id, πB⟩ :
      W4K.KitW (ckP .two) K (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty CV silP runP
          Tag.onl).to (ckPT_eq .two))
    p.sMT p.sFS (fun a : X × RecFull => some (some a.1, r₀, r₀)) (bodyS frS.P.T.a salt).embE
        sB.logLeaves
    (e.cm :: e.cm :: codeA (v := frS.P.v) (s := 1) e.rcd.2) (x, e.rcd)
    (ownOfCarrier (DP.at frS.P.T.a) fB.k) (listedOfCarrier (DP.at frS.P.T.a).a fB.k)).det F

/-- **It is armBE (VerifyVFastStepsD.lean).** -/
theorem armBET_eq (r₀ : (LV).Rec) (p : Params) (F : Fam (typedOracleFamily 256 (K + 1) CV)) (x : X) (e : EntryIn)
    (fB : FileIn) (πB : OneProtocolProof 256 (LV).bat) :
    armBET DK DP runK runP rK rP sB early ds xs dec K salt r₀ p F x e fB πB =
      armBE DK DP runK runP rK rP sB early ds xs dec K salt r₀ p F x e fB πB := by
  unfold armBET
  rw [W4K.runW_kit]
  rfl

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.armTET_eq
#print axioms VerifiableInference.OnPublicFiles.SlotsBehindCutD.armBET_eq
