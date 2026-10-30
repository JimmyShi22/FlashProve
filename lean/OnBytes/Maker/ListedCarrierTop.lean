-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedCarrierTop.lean: at the string that is laid of an outside parser's carrier
(File.toBPrf, OnBytes/Maker/CarrierTyping.lean), with the two lists taken off the same carrier
(OnBytes/Maker/ListedCarrier.lean, ownOfCarrier, listedOfCarrier), the verifier along lists
(OnBytes/Maker/ListedWhole.lean, verifyWholeL) is the compiled verifier of one slot
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, verifyOneProtocol) at the file's own wire record, as a tree of
queries.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

It joins verifyWholeL_eq (OnBytes/Maker/ListedWholeTop.lean) with listedOK_carrier and
ext_listed_carrier (OnBytes/Maker/ListedCarrierLaws.lean), which pay its two premises.

Main definition. verifyCarrier: one term of a carrier: the string is laid of the carrier, with the
number of the binding tree's leaves 2 ^ depthReq; where none is laid the answer is no, with no
query; else verifyWholeL at that string and the two lists off the same carrier. So a caller lays the
carrier and the data once, not at three places.
  verifyCarrierAt: the same at the string that File.toBPrfAt lays at the binding tree's shape s from
the plan; the depth of the binding tree is the shape's.
Main theorems.
  verifyCarrier_eq: the equation at a string that has been laid.
  verifyCarrier_is: verifyCarrier is: no where no string is laid, else verifyOneProtocol at the string.
  verifyCarrierAt_is: the like for verifyCarrierAt and File.toBPrfAt.

Why. A run along the lists then speaks for the compiled verifier at the very string that the carrier
gives, its strict format included: nothing is cut away first. Both sides stand at one carrier L of
the typed oracles and one wire record: a run at a carrier L of no theorem speaks for verifyOneProtocol there.

Limits. verifyCarrier stands at File.toBPrf: it is for equations. Of a carrier's fields on the
binding tree File.toBPrf tests the number of places alone, and it walks every entry of trees; a term
that is run on a stranger's carrier stands at File.toBPrfAt (verifyCarrierAt). NEITHER TERM IS A
VERDICT. They are verifyOneProtocol, and once the chain has joined verifyOneProtocol tests the length of the field
rsalt nowhere (the head of OnBytes/Maker/Page/Guard.lean says what follows under a page's family). A
run that is to be leant on goes through the guard: the law to cite is verifyGuardCarrierAt_is
(OnBytes/Maker/ListedCarrierGuard.lean). verifyCarrier_eq has one premise: a string has been laid of
the carrier, the same k of which the two lists are made; the two laws "_is" have none. Of a string
that comes from elsewhere nothing is said. That a string is laid of any carrier is not shown here.
One k and one D are laid once; the plain parts pF, pJ, p3 of the three silent rounds, cfg, the depth
or the shape, sMT, sFS and cms stay the caller's letters, and that pF, pJ, p3 are made of the same k
is the caller's doing. The laws hold at every carrier, read by Carrier.read or not. The carrier is
the prover's: the equations say nothing on whether the verifier accepts. Nothing on time or memory.
Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWholeTop
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

/-- **At the carrier's string the verifier along the lists off the carrier is the compiled
verifier.** -/
theorem verifyCarrier_eq (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (places : ℕ) (pF : TF) (pJ : TJ) (p3 : T3)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch)
    (h : k.toBPrf C D tF tJ t3 silent run cfg places pF pJ p3 = some π) :
    verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        (ownOfCarrier D k) (listedOfCarrier D.a k) =
      verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π :=
  verifyWholeL_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
    (ownOfCarrier D k) (listedOfCarrier D.a k)
    (listedOK_carrier C K chal D tF tJ t3 silent run k cfg places pF pJ p3 π h)
    (ext_listed_carrier C D tF tJ t3 silent run k cfg places pF pJ p3 π h)

/-- **The verifier of a whole file along lists, at a carrier.** -/
def verifyCarrier (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) : TypedOracleComputation 256 (K + 1) L Bool :=
  (k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3).elim (pure false) fun π =>
    verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
      (ownOfCarrier D k) (listedOfCarrier D.a k)

/-- **It is the compiled verifier at the carrier's string; no where no string is laid.** -/
theorem verifyCarrier_is (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) :
    verifyCarrier C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x k cfg
        pF pJ p3 =
      (k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3).elim (pure false) fun π =>
        verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
          (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π := by
  unfold verifyCarrier
  cases e : k.toBPrf C D tF tJ t3 silent run cfg (2 ^ depthReq) pF pJ p3 with
  | none => rfl
  | some π =>
    exact verifyCarrier_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq
      cms x k cfg (2 ^ depthReq) pF pJ p3 π e

/-- **The verifier of a whole file along lists, at a carrier and the binding tree's shape.** -/
def verifyCarrierAt (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) :
    TypedOracleComputation 256 (K + 1) L Bool :=
  (k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3).elim (pure false) fun π =>
    verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves cms x π
      (ownOfCarrier D k) (listedOfCarrier D.a k)

/-- **It is the compiled verifier at the string of File.toBPrfAt; no where that lays none.** -/
theorem verifyCarrierAt_is (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (s : Params.LinBindingShape) (cms : List (Dig 256))
    (x : Xi) (k : Carrier.File) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) :
    verifyCarrierAt C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s cms x k cfg pF pJ
        p3 =
      (k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3).elim (pure false) fun π =>
        verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
          (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE s.logLeaves cms x π := by
  unfold verifyCarrierAt
  cases e : k.toBPrfAt C D tF tJ t3 silent run cfg s pF pJ p3 with
  | none => rfl
  | some π =>
    exact verifyCarrier_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE s.logLeaves
      cms x k cfg (2 ^ s.logLeaves) pF pJ p3 π
      (toBPrf_of_At C D tF tJ t3 silent run k cfg s pF pJ p3 π e)

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyCarrier_eq
#print axioms OnBytes.Maker.verifyCarrier_is
#print axioms OnBytes.Maker.verifyCarrierAt_is
