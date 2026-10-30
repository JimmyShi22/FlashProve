-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ThinBitsTieProofs.lean: the proof of the statement of Run/ThinBitsTie.lean: two equations, one
after the other (`verifyPB_eq`, Run/ThinBits.lean; `thin_verify`, Run/ThinTieProofs.lean). Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

`thin_bits`: `verifyPB` as the run of `Compile.Batch.verifyOneProtocol` (statement and hypotheses:
Run/ThinBitsTie.lean).
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.ThinBitsTie
import Run.ThinTieProofs

set_option autoImplicit false

namespace Run.Thin
open Iop Rom Compile Compile.Batch Run.Twin

theorem thin_bits :
    Spec.thin_bits := fun I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π =>
  (verifyPB_eq (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin
      embE depthReq cms x π).trans
    (thin_verify I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π)

end Run.Thin
