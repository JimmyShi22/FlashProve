-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/GuardCarrierT.lean: the guarded verdict along lists at an outside parser's carrier
(verifyGuardCarrier, OnBytes/Maker/ListedCarrierGuard.lean) taken apart into three parts, in a form
made for a run, with the equation: all three parts say yes exactly where the verdict is yes.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. A file that runs the verdict should print why it is a no. The verdict has three parts: a string
is laid of the carrier; the salt of the slot's leaf fits (rsaltFit,
OnBytes/Maker/Page/GuardVerify.lean); the guarded run of the verifier along lists returns yes. Here
they are one record of plain data, made by one walk: the run stands behind the first two. The run is
runGuardT (Johnson/RunOne/GuardT.lean): the page's test by conditions, the answers as bytes first.

Main definitions.
  CarrierParts: laid, fit, guarded (no value: a query without a written string, or not reached).
  CarrierParts.yes: laid, fit, and guarded is "yes".
  partsCarrierT: the parts at a carrier.
  partsCarrierAtT: the parts at a carrier and the binding tree's shape s from the plan: laid says
    that File.toBPrfAt lays a string.
Main theorems.
  partsCarrierT_yes: (partsCarrierT ..).yes = verifyGuardCarrier .. . No premise. With
    verifyGuardCarrier_is: it is the guarded verdict of the compiled verifier verifyOneProtocol at the
    carrier's string, and no where no string is laid.
  partsCarrierAtT_yes: the like for partsCarrierAtT and verifyGuardCarrierAt.
The letter R (RunJ P, Johnson/RunOne/FamT.lean) holds two functions with a proof each; RunJ.plain P
is one at every page, so it is no premise.

Limits. partsCarrierT stands at File.toBPrf: it is for equations; what is run on a stranger's
carrier is partsCarrierAtT, at File.toBPrfAt. Those of ListedCarrierGuard.lean and GuardT.lean: a
yes is a yes under the page's family.
Where no string is laid, fit is false and was not asked; where fit is false the guarded run is not
made: guarded is none there too.
What an evaluator computes how often is a fact about the compiler: nothing on time or memory is a
theorem. Nothing has been run here. Nothing on soundness. The program does not import this file.


-/
import Johnson.RunOne.GuardT
import OnBytes.Maker.ListedCarrierGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The three parts of the guarded verdict at a carrier. -/
structure CarrierParts where
  /-- a proof string is laid of the carrier -/
  laid : Bool
  /-- the field rsalt has 8 sR + 64 bits and ends in the word of the leaf's index; false also where
  no string is laid: the test was not reached -/
  fit : Bool
  /-- the guarded run's value; none: a query had no written string, or the run was not reached -/
  guarded : Option Bool

/-- All three say yes. -/
def CarrierParts.yes (p : CarrierParts) : Bool := p.laid && p.fit && p.guarded.getD false

variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  {I X : Type} {L : BatchProtocolWithLeafBody I X} (sMT sFS : ℕ) (t : _root_.Compile.Tag)
  (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
  (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
  (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
  (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
  (P : Page.PageJ L (K + 1)) (R : Johnson.RunOne.RunJ P) (O : ByteArray → ByteArray)

/-- **The parts of the guarded verdict at a carrier**, at File.toBPrf: for equations. -/
def partsCarrierT : CarrierParts :=
  match k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3 with
  | none => ⟨false, false, none⟩
  | some π =>
    if Page.rsaltFit P.sR depthReq π then
      ⟨true, true, Johnson.RunOne.runGuardT P R O
        (verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
          (ownOfCarrier D k) (listedOfCarrier D.a k))⟩
    else ⟨true, false, none⟩

/-- **All three parts say yes exactly where the guarded verdict at the carrier is yes.** -/
theorem partsCarrierT_yes :
    (partsCarrierT C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x k cfg
      pF pJ p3 P R O).yes =
      verifyGuardCarrier C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x
        k cfg pF pJ p3 P O := by
  unfold partsCarrierT verifyGuardCarrier
  cases k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3 with
  | none => rfl
  | some π =>
    show CarrierParts.yes (if Page.rsaltFit P.sR depthReq π = true then _ else _) =
      verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        (ownOfCarrier D k) (listedOfCarrier D.a k) P O
    unfold verifyGuardC verifyGuardCG verifyWholeCR
    by_cases hf : Page.rsaltFit P.sR depthReq π = true
    · rw [if_pos hf, if_pos hf, Johnson.RunOne.runGuardT_eq]
      rfl
    · rw [if_neg hf, if_neg hf]
      rfl

/-- **The parts at a carrier and the binding tree's shape, for a run.** -/
def partsCarrierAtT (s : Params.LinBindingShape) : CarrierParts :=
  match k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3 with
  | none => ⟨false, false, none⟩
  | some π =>
    if Page.rsaltFit P.sR s.logLeaves π then
      ⟨true, true, Johnson.RunOne.runGuardT P R O
        (verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves cms x
          π (ownOfCarrier D k) (listedOfCarrier D.a k))⟩
    else ⟨true, false, none⟩

/-- **All three parts say yes exactly where the guarded verdict at the carrier and the shape is
yes.** -/
theorem partsCarrierAtT_yes (s : Params.LinBindingShape) :
    (partsCarrierAtT C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE cms x k cfg pF pJ
      p3 P R O s).yes =
      verifyGuardCarrierAt C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s cms x k
        cfg pF pJ p3 P O := by
  unfold partsCarrierAtT verifyGuardCarrierAt
  cases k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3 with
  | none => rfl
  | some π =>
    show CarrierParts.yes (if Page.rsaltFit P.sR s.logLeaves π = true then _ else _) =
      verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves cms x π
        (ownOfCarrier D k) (listedOfCarrier D.a k) P O
    unfold verifyGuardC verifyGuardCG verifyWholeCR
    by_cases hf : Page.rsaltFit P.sR s.logLeaves π = true
    · rw [if_pos hf, if_pos hf, Johnson.RunOne.runGuardT_eq]
      rfl
    · rw [if_neg hf, if_neg hf]
      rfl

end OnBytes.Maker

#print axioms OnBytes.Maker.partsCarrierT_yes
#print axioms OnBytes.Maker.partsCarrierAtT_yes
