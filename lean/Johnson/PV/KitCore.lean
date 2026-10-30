-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/KitCore.lean: FOR Johnson/PV/KitArmsS.lean | KitArmsF.lean: what of verifyWholeX's
  arguments is typed over the kit, as one record (KitW C: chal · embS · embP · the proof string);
  carried along an equation of kits (KitW.to: the identity at a run); runW A … := verifyWholeX C … ;
**runW_kit : runW (A.to h) … = runW A …** (h : C' = C): by subst. In the manner of AskProof.lean's
  KitLets. General in the kit, the data, the interface, the tag.


-/
import OnBytes.Maker.LessWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace W4K
open OnBytes.Maker TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch
    _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {I X : Type} (L : BatchProtocolWithLeafBody I X) {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool) (t : _root_.Compile.Tag)

/-- What of the verifier's arguments is typed over the kit. -/
structure KitW where
  chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k
  eS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L
  eP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann → PlainPart (shapeOf L t)
      (TypedOracleCompiler.Compile.Batch.annOf L t)
  π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch

variable {C K D tF tJ t3 L silent run t}

/-- Carried along an equation of kits. -/
def KitW.to {C' : CK} : (h : C' = C) → KitW C K D tF tJ t3 L silent run t → KitW C' K D tF tJ t3 L
    silent run t
  | rfl, A => A

/-- The verifier of a whole file along the lists, at a kit and its record. -/
def runW (A : KitW C K D tF tJ t3 L silent run t) (sMT sFS : ℕ) (xin : Xi → Option X) (embE : SgX →
    Body L)
    (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi) (own : Leaves) (listed : List (oneExternalString (2 ^ D.a)
        SgX).Pos) :
    TypedOracleComputation 256 (K + 1) L Bool :=
  verifyWholeX C K A.chal D tF tJ t3 silent run sMT sFS t A.eS A.eP xin embE depthReq cms x A.π own
      listed

/-- **One value at two kits that are one.** -/
theorem runW_kit {C' : CK} (h : C' = C) (A : KitW C K D tF tJ t3 L silent run t) (sMT sFS : ℕ)
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi) (own
        : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    runW (A.to h) sMT sFS xin embE depthReq cms x own listed = runW A sMT sFS xin embE depthReq cms
        x own listed := by
  subst h
  rfl

end W4K

#print axioms W4K.runW_kit
