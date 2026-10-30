-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsPageProofs.lean: the proof of the statement of Run/RunIsPage.lean, with one lemma
(`pageVerdict_eq`): the two functions of "what the parser gave" agree at every value
(Run/ThinBits.lean: `verifyPB_eq`; Run/CodingThin.lean: `famC_famM`).

Main names (statements and hypotheses: Run/RunIsPage.lean):
  `run_page`: `ph_run` at the coding by the format's own strings, with `pageVerdict`.

`ph_run`: Run/ParserHash.lean: what the run of lenient parser, then compiled verifier, is at
`oBits ()` (Run/OracleBits.lean).

Notation:
  `famVerdict`: the plain verifier at the family that gives bytes first (Run/RunIsThinFam.lean);
  `pageVerdict`: the plain verifier with digests as bits, at the family `famC` (Run/RunIsPage.lean);
  `C`: the data of the encoding (`PageC`, Run/CodingPage.lean);
  `theImpl C`: the coding by the format's own strings, at the data `C` (Run/CodingPage.lean);
  `oBy`: the format's oracle asked at `toBytes s` for a bit string s, into bytes (Run/FamThin.lean;
  `toBytes`: Run/OracleBits.lean).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.RunIsPage
import Run.ParserHashProofs

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

theorem pageVerdict_eq {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ)
    (t : Tag) (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up)
    (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (ivk : List (Dig 256)) (x : Y) :
    ∀ v : Option (OneProtocolProof 256 P.up),
      famVerdict L sMT sFS t P wq embS embP xin embE depthReq (theImpl C) oBy ivk x v =
        pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x v
  | none => rfl
  | some π => by
      show verifyP (fun _ => L) (famM (fun _ => L) K (theImpl C) oBy) L.early L.late sMT sFS t P wq
          embS embP xin embE depthReq ivk x π =
        verifyPB (fun _ => L) (famC (fun _ => L) C oBy) L.early L.late sMT sFS t P wq embS embP
          xin embE depthReq ivk x π
      rw [verifyPB_eq, famC_famM]

theorem run_page : Spec.run_page := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b =>
  (ph_run I X K L Y E sMT sFS t P wq embS embP xin embE depthReq (theImpl C)
      sp T N hN ivk x b).trans
    (congrArg PMF.pure (pageVerdict_eq L sMT sFS t P wq embS embP xin embE depthReq C ivk x _))

end Run
