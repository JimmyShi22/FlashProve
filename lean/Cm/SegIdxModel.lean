-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxModel.lean: the number of hidden units of the (shared) feed-forward block of a layer
(`fOf`). The weight tensors of the model as index atoms: Cm/TargetSegIdxModel.lean.

Limits: this file says nothing on cells; no family is written here.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegIdxTensor
import Cb.Gen.Tensor
import Cm.RelBase
import Inst.Model.IndexM
import Inst.Model.FF.Trace
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Cb Blocks Finset Code Inst.Model Inst.Model.Layout

section Atoms
variable (L : ℕ)

/-- the number of hidden units of the (shared) feed-forward block of layer L -/
def fOf : ℕ := if hasExperts L then ppref.fe else ppref.f

end Atoms

end Cm
