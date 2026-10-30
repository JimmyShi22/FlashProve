-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeCut.lean: at the description of a whole file: the verifier along lists
(OnBytes/Maker/ListedWhole.lean, verifyWholeL) on the argument string cut to the lists
(OnBytes/TypedOracleCompiler/Compile/Batch/ListedCut.lean, OneProtocolProof.cutTo). A definition; it has code.

No soundness: a test. This module states nothing on soundness.

Main definition. verifyWholeC: verifyWholeL at π.cutTo (the file's rounds' wire records) (the stored
table's wiring less its list) own listed, and the same two lists. verifyWholeC_is: it is verifyBSC
at the file's values, by unfolding.

Limits. That it is the compiled verifier at the cut string: OnBytes/Maker/ListedWholeCutTop.lean.
Those of the two files named above. Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWhole
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The verifier of a whole file along the lists, on the string cut to the lists.** -/
def verifyWholeC (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) : TypedOracleComputation 256 (K + 1) L Bool :=
  verifyWholeL C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x
    (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) own listed

/-- It is verifyBSC at the file's values. -/
theorem verifyWholeC_is (sMT sFS : ℕ) (t : _root_.Compile.Tag)
    (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
    (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
    (listed : List (oneExternalString (2 ^ D.a) SgX).Pos) :
    verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed =
      verifyBSC sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) (nOpenW D) (maxDepthW D) embS embP xin embE
        depthReq cms x π own listed (fun _ ρ _ => rdWhole C D tF tJ t3 ρ)
        (fun _ ρ => rdEWhole C D tF tJ t3 ρ) := rfl

end OnBytes.Maker
