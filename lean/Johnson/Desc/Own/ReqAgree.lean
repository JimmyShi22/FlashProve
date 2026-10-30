-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/ReqAgree.lean: the description's own tests on a request's plan
(Johnson/Desc/Own/Req.lean) say just what the hand-written program's tests of OnBytes/Iop/Prox.lean,
Req.lean and ReqRows.lean say, at all arguments: nineteen equations, one for each.
A YARDSTICK BESIDE: no block imports this file. It says nothing on whether the tests ask enough.
No soundness is claimed.

-/
import Johnson.Desc.Own.Req
import Johnson.Desc.Own.LinAgree
import Johnson.Desc.Own.SendAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape IoppStage LaidBlock ReqArray ReqLayout)

theorem stageFits_eq (s : IoppStage) :
    stageFits s = stageOk s := rfl

theorem stageFits_fun : stageFits = stageOk := funext stageFits_eq

theorem stageFitsAt_eq (codes : Codes) (answers : Nat) (before : Option IoppStage)
    (s : IoppStage) (last : Bool) :
    stageFitsAt codes answers before s last = ioppStageOk codes answers before s last := by
  unfold stageFitsAt ioppStageOk
  simp only [twoPower_eq, codeFits_eq, stageFits_eq, maskFits] <;> rfl

theorem stagesFitFrom_eq (codes : Codes) (answers : Nat) :
    ∀ (b : Option IoppStage) (l : List IoppStage),
      stagesFitFrom codes answers b l = ioppStagesOk codes answers b l
  | _, [] => rfl
  | _, s :: rest => by
    simp only [stagesFitFrom, ioppStagesOk, stageFitsAt_eq,
      stagesFitFrom_eq codes answers (some s) rest]

theorem stagesFit_eq (codes : Codes) (stages : List IoppStage) (answers : Nat) :
    stagesFit codes stages answers = ioppOk codes stages answers := by
  unfold stagesFit ioppOk
  simp only [stagesFitFrom_eq] <;> rfl

theorem reqMessageFits_eq (m : ReqMessage) :
    reqMessageFits m = reqMessageOk m := by
  unfold reqMessageFits reqMessageOk
  simp only [shapeSound_eq, noticeOk] <;> rfl

theorem reqMessageFits_fun : reqMessageFits = reqMessageOk := funext reqMessageFits_eq

theorem momentsFit_eq : ∀ (t : Nat) (l : List ReqMessage), momentsFit t l = reqMomentsOk t l
  | _, [] => rfl
  | _, m :: ms => by simp only [momentsFit, reqMomentsOk, momentsFit_eq m.moment ms]

theorem reqLinkFits_eq (l : ReqLink) :
    reqLinkFits l = reqLinkOk l := by
  unfold reqLinkFits reqLinkOk
  simp only [reqMessageFits_fun, momentsFit_eq] <;> rfl

theorem reqShapeFits_eq (s : ReqShape) :
    reqShapeFits s = reqShapeOk s := by
  unfold reqShapeFits reqShapeOk
  simp only [shapeSound_eq, stageFits_fun, reqLinkFits_eq, noticeOk] <;> rfl

theorem reqFits_eq (codes : Codes) (s : ReqShape) :
    reqFits codes s = reqOk codes s := by
  unfold reqFits reqOk
  simp only [stagesFit_eq, reqShapeFits_eq] <;> rfl

theorem laidEven_eq (first bits : Nat) :
    laidEven first bits = laidAligned first bits := rfl

theorem laidBlockFits_eq (b : LaidBlock) (tableRowBits tablePlaceBits : Nat) :
    laidBlockFits b tableRowBits tablePlaceBits = laidBlockOk b tableRowBits tablePlaceBits := by
  unfold laidBlockFits laidBlockOk
  simp only [laidEven_eq] <;> rfl

theorem laidMeets_eq (a aBits b bBits : Nat) :
    laidMeets a aBits b bBits = laidMeet a aBits b bBits := rfl

theorem noTwo_eq {α : Type} (r : α → α → Bool) : ∀ l : List α, noTwo r l = noPair r l
  | [] => rfl
  | _ :: l => by simp only [noTwo, noPair, noTwo_eq r l]

theorem laidMatrixFits_eq (a : ReqArray) (tableRowBits tablePlaceBits : Nat) :
    laidMatrixFits a tableRowBits tablePlaceBits = laidMatrixOk a tableRowBits tablePlaceBits := by
  unfold laidMatrixFits laidMatrixOk
  simp only [laidBlockFits_eq, laidMeets_eq, noTwo_eq] <;> rfl

theorem laidFits_eq (matrices : List ReqArray) (tableRowBits tablePlaceBits : Nat) :
    laidFits matrices tableRowBits tablePlaceBits =
      laidOk matrices tableRowBits tablePlaceBits := by
  unfold laidFits laidOk
  simp only [laidMeets_eq, noTwo_eq, laidMatrixFits_eq] <;> rfl

theorem reqArrayFits_eq (a : ReqArray) :
    reqArrayFits a = reqArrayOk a := by
  unfold reqArrayFits reqArrayOk
  simp only [laidEven_eq] <;> rfl

theorem reqArrayFits_fun : reqArrayFits = reqArrayOk := funext reqArrayFits_eq

theorem laidHolds_eq (b : LaidBlock) (rowBits index : Nat) :
    laidHolds b rowBits index = laidCovers b rowBits index := rfl

theorem reqMessageLaid_eq (codes : Codes) (o : OracleShape) (inIt : List ReqArray) :
    reqMessageLaid codes o inIt = reqMessageLayoutOk codes o inIt := by
  unfold reqMessageLaid reqMessageLayoutOk
  simp only [padMade_eq, laidFits_eq, laidHolds_eq] <;> rfl

theorem reqLayoutFits_eq (codes : Codes) (s : ReqShape) (layout : ReqLayout) :
    reqLayoutFits codes s layout = reqLayoutOk codes s layout := by
  unfold reqLayoutFits reqLayoutOk
  simp only [noTwo_eq, reqArrayFits_fun, reqMessageLaid_eq] <;> rfl

end VerifiableInference.Desc.Own
