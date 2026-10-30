-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
TWO: OnBytes/TypedOracleCompiler/Run/ThinBitsTieProofs.lean: the library's file of the same name said again over the
sibling, as text: thin_bits, by the sibling's verifyPB_eq and thin_verify.

Run/ThinBitsTieProofs.lean: the proof of the statement of Run/ThinBitsTie.lean: two equations, one
after the other.

Terms: lean/GLOSSARY.md.

-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library: a test by Lean's evaluator, which
   leaves no declaration. So nothing that is checked of declarations is checked of such a run. No
   clause of a soundness theorem of this library speaks of a run. -/
import Run.ThinBitsTieProofs
import OnBytes.TypedOracleCompiler.Run.ThinBitsTie
import OnBytes.TypedOracleCompiler.Run.ThinTieProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Thin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Thin

theorem thin_bits :
    Spec.thin_bits := fun I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π =>
  (verifyPB_eq (fun _ => L) g L.early L.late sMT sFS t P wq embS embP xin
      embE depthReq cms x π).trans
    (thin_verify I X lam K L g Y E sMT sFS t P wq embS embP xin embE depthReq cms x π)

end TypedOracleCompiler.Run.Thin
