-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/ReqModel.lean: the tokens of a request.

One definition.

Limits: this file says nothing on protocols.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegAllProofs
import Cm.SegFFMat
import Cm.SegFFCellKeys
import Cm.SegFFCellIdnOK
import Cm.SegFFMatProofsE
import Cm.SegHeadAsm
import Cb.Req.ReqGlueProofsSeg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All
open Inst.Model.Layout (kRef hRef)

/-- the tokens of a request -/
def tokX (x : XI) : ℕ → ℕ := tokOf x.prompt

end Cm.Seg
