-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsThinFamProofs.lean: the proofs of the two statements of Run/RunIsThinFam.lean, with one
lemma (`famVerdict_eq`): the two functions of "what the parser gave" agree at every value if
`f s = bytesToDig (O s)` for all s.
-/
import Run.RunIsThinFam
import Run.RunIsThinProofs

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

theorem famVerdict_eq {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ)
    (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256) (f : ZKCP.Oracle 256)
    (O : List Bool → ByteArray) (h : ∀ s, f s = bytesToDig (O s)) (ivk : List (Dig 256)) (x : Y) :
    ∀ v : Option (OneProtocolProof 256 P.up),
      thinVerdict L sMT sFS t P wq embS embP xin embE depthReq m f ivk x v =
        famVerdict L sMT sFS t P wq embS embP xin embE depthReq m O ivk x v
  | none => rfl
  | some π =>
    congrArg (fun g =>
        verifyP (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin embE depthReq ivk x π)
      (famM_one K m O f h).symm

theorem run_fam :
    Spec.run_fam := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN f O ivk x b h =>
  (run_thin I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN f ivk x b).trans
    (congrArg PMF.pure (famVerdict_eq L sMT sFS t P wq embS embP xin embE depthReq m f O h ivk x _))

theorem run_fam_page :
    Spec.run_fam_page := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN ivk x b =>
  run_fam I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN (oBits ())
    oBy ivk x b fun _ => rfl

end Run
