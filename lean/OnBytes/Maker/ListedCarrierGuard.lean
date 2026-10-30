-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedCarrierGuard.lean: at the string that is laid of an outside parser's carrier
(File.toBPrf, OnBytes/Maker/CarrierTyping.lean), with the two lists taken off the same carrier
(OnBytes/Maker/ListedCarrier.lean), the guarded verdict along lists (verifyGuardC,
OnBytes/Maker/ListedWholeGuard.lean) is the guarded verdict of the compiled verifier (verifyGuard,
OnBytes/Maker/Page/GuardVerify.lean) at the file's own wire record and at that very string.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

It joins verifyGuardC_eq_self (OnBytes/Maker/ListedWholeGuard.lean) with listedOK_carrier and
ext_listed_carrier (OnBytes/Maker/ListedCarrierLaws.lean), which pay its two premises.

Main definition. verifyGuardCarrier: one term of a carrier: the string is laid of the carrier, with
the number of the binding tree's leaves 2 ^ depthReq; where none is laid the verdict is no; else
verifyGuardC at that string and the two lists off the same carrier.
  verifyGuardCarrierAt: the same at the string that File.toBPrfAt lays at the binding tree's shape s
from the plan; the depth of the binding tree is the shape's.
Main theorems.
  verifyGuardCarrier_eq: the equation at a string that has been laid.
  verifyGuardCarrier_is: verifyGuardCarrier is: no where no string is laid, else verifyGuard at the
    string.
  verifyGuardCarrierAt_is: the like for verifyGuardCarrierAt and File.toBPrfAt.

Why. verifyGuardC cuts the string to the lists before it judges. At the lists off the carrier the
cut takes nothing away, so the verdict is that on the string itself, its strict format included.

Limits. verifyGuardCarrier stands at File.toBPrf: it is for equations; the term to cite for a run on
a stranger's carrier is verifyGuardCarrierAt, at File.toBPrfAt, which also holds the carrier's
fields on the binding tree and its trees' numbers against the plan. These are terms to cite, not to
run: through verifyGuardC they stand at okJ P and gJ P O, which an evaluator makes anew at every bit
read; the form for a run is partsCarrierAtT (Johnson/RunOne/GuardCarrierT.lean).
verifyGuardCarrier_eq has one premise: a string has been laid of the carrier, the same k of which
the two lists are made; the two laws "_is" have none. One k and one D are laid once. The page P,
cfg, the depth or the shape, sMT, sFS, cms and the plain parts pF, pJ, p3 stay the caller's letters,
and nothing here says that P.sR is the shape's number of salt bytes, that P.cfg is cfg, that P.key
and P.proof are made of D, or that pF, pJ, p3 are made of k: a term at a plan lays them once
(Johnson/RunOne/AskProof.lean does, for the proof file at the small size). Of these letters pF, pJ,
p3 are made of the carrier by a caller, and cms, at the proof file, of the table that the entry file
names: they are the prover's word and part of what is judged. The others are the plan's or the
user's. The carrier is the prover's: the equations hold for every carrier, and say nothing on
whether the verdict is yes. The limits of ListedWholeGuard.lean, Guard.lean and GuardVerify.lean
hold here: a yes is a yes under the page's family. Nothing on time or memory. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWholeGuard
import OnBytes.Maker.ListedCarrierLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable {TF TJ T3 Xi : Type} (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-- **At the carrier's string the guarded verdict along the lists off the carrier is the guarded
verdict of the compiled verifier.** -/
theorem verifyGuardCarrier_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (places : ℕ) (pF : TF) (pJ : TJ) (p3 : T3)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : k.toBPrf C D tF tJ t3 silent run cfg places pF pJ p3 = some π)
    (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        (ownOfCarrier D k) (listedOfCarrier D.a k) P O =
      Page.verifyGuard P O sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π :=
  verifyGuardC_eq_self C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
    (ownOfCarrier D k) (listedOfCarrier D.a k) P O
    (listedOK_carrier C K chal D tF tJ t3 silent run k cfg places pF pJ p3 π h)
    (ext_listed_carrier C D tF tJ t3 silent run k cfg places pF pJ p3 π h)

/-- **The guarded verdict along lists, at a carrier.** -/
def verifyGuardCarrier (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) : Bool :=
  (k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3).elim false fun π =>
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
      (ownOfCarrier D k) (listedOfCarrier D.a k) P O

/-- **It is the guarded verdict of the compiled verifier at the carrier's string; no where no string
is laid.** -/
theorem verifyGuardCarrier_is (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardCarrier C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x k
        cfg pF pJ p3 P O =
      (k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3).elim false fun π =>
        Page.verifyGuard P O sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
          (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π := by
  unfold verifyGuardCarrier
  cases e : k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3 with
  | none => rfl
  | some π =>
    exact verifyGuardCarrier_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE
      depthReq cms x k cfg (2 ^ depthReq) pF pJ p3 π e P O

/-- **The guarded verdict along lists, at a carrier and the binding tree's shape.** -/
def verifyGuardCarrierAt (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) : Bool :=
  (k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3).elim false fun π =>
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves cms x π
      (ownOfCarrier D k) (listedOfCarrier D.a k) P O

/-- **It is the guarded verdict of the compiled verifier at the string of File.toBPrfAt; no where
that lays none.** -/
theorem verifyGuardCarrierAt_is (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardCarrierAt C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s cms x k cfg
        pF pJ p3 P O =
      (k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3).elim false fun π =>
        Page.verifyGuard P O sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
          (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE s.logLeaves cms x π := by
  unfold verifyGuardCarrierAt
  cases e : k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3 with
  | none => rfl
  | some π =>
    exact verifyGuardCarrier_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE
      s.logLeaves cms x k cfg (2 ^ s.logLeaves) pF pJ p3 π
      (toBPrf_of_At C D tF tJ t3 silent run k cfg s pF pJ p3 π e) P O

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyGuardCarrier_eq
#print axioms OnBytes.Maker.verifyGuardCarrier_is
#print axioms OnBytes.Maker.verifyGuardCarrierAt_is
