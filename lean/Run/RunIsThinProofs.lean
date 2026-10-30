-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsThinProofs.lean: the proof of the statement of Run/RunIsThin.lean.
-/
import Run.RunIsThin
import Run.ThinTieProofs

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- the two functions of what the parser gave agree -/
theorem thinVerdict_eq {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ)
    (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (m : OracleCoding (Batch.spec 256 K L) 256) (f : ZKCP.Oracle 256)
    (ivk : List (Dig 256)) (x : Y) :
    ∀ v : Option (OneProtocolProof 256 P.up),
      verdictV m (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq) f ivk x v =
        thinVerdict L sMT sFS t P wq embS embP xin embE depthReq m f ivk x v
  | none => rfl
  | some π =>
    (thin_verify I X 256 K L (readBlocks m (famOne f)) Y E sMT sFS t P wq embS embP xin
      embE depthReq ivk x π).symm

theorem run_thin : Spec.run_thin := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq m sp T N hN f ivk x b =>
  (run_verifyBS I X K L sMT sFS t Y E P.up wq embS embP xin embE depthReq m
      sp T N hN f ivk x b).trans
    (congrArg PMF.pure (thinVerdict_eq L sMT sFS t P wq embS embP xin embE depthReq m f ivk x _))

end Run
