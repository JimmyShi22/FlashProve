-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsPageHProofs.lean: the proofs of the statements of Run/RunIsPageH.lean.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.RunIsPageH
import Run.RunIsPageProofs
import Run.LaxDomProofs

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

theorem run_pageH :
    Spec.run_pageH := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b hS =>
  (run_page I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b).trans
    (congrArg (fun v =>
        PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x (keep ivk v)))
      (lax_HO Y E P.up (sp x) T b hS))

theorem run_pageW :
    Spec.run_pageW := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b hS =>
  (run_pageH I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T.up N hN ivk x b hS).trans
    (congrArg (fun v =>
        PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x (keep ivk v)))
      (parseThin_parse (m := Id) _root_.Fmt.formatHash P (sp x) T b).2.1.symm)

theorem run_pageF :
    Spec.run_pageF := fun I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b hS =>
  (run_pageW I X K L Y E sMT sFS t P wq embS embP xin embE depthReq C sp T N hN ivk x b hS).trans
    (congrArg (fun v =>
        PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x (keep ivk v)))
      (laxFast_parse P (sp x) T b).1.symm)

end Run
