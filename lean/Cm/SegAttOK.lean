-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttOK.lean: the proofs of the two statements of Cm/SegAtt.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

Main names:
  `keyVec_agree_spec`, `idnVal_agree_spec`: `Spec.keyVec_agree`, `Spec.idnVal_agree`, proved here
    from the lemmas of Cm/SegAttAgree.lean.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegAtt
import Cm.SegAttAgree
import Cm.ReqModel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All

theorem keyVec_agree_spec : Spec.keyVec_agree := fun scl u0 tb _ _ H c Y =>
  keyVec_agree H (scl := scl) u0 tb c Y
theorem idnVal_agree_spec : Spec.idnVal_agree := fun _ _ H _ hj => idnVal_agree H hj

end Cm.Seg
