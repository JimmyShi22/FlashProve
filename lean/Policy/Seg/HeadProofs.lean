-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadProofs.lean

The three statements of Policy/Seg/Head.lean, with their proofs: the conditions of the model's last
part are well formed, read only places that the layout lists for that part, and at integer matrices
say what the model's relation says.

This file puts the parts together: Policy/Seg/HeadSteps.lean (the statements of the steps),
HeadForms.lean (forms and public tables), HeadKeys.lean (the nine families of keys), HeadIdn.lean
(the 21 identities), HeadWf.lean (well-formedness and places), HeadAsm.lean (the assembly).
`headPol_holds`: the assembly over `Gl.E`. `headPol_wf`, `headPol_places`, `headPol_holds_int`: the
three.

Limits: those of the statements: nothing on the request's form r < e, on bounds of cells, or on
protocols.
-/
import Policy.Seg.HeadKeys
import Policy.Seg.HeadIdn
import Policy.Seg.HeadWf
import Policy.Seg.HeadAsm

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

theorem headPol_holds : Spec.headPol_holds :=
  headPol_holds_of headPol_key_live headPol_key_dead headPol_idn_val headPol_led_val

theorem headPol_wf : Spec.headPol_wf := segHeadPol_wf

theorem headPol_places : Spec.headPol_places := segHeadPol_places

theorem headPol_holds_int : Spec.headPol_holds_int := headPol_holds_int_of headPol_holds

end Policy
