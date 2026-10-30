-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerSide.lean

The relation pair with the cost ledger, at p = 2^64 - 2^32 + 1, as a relations' side (`RelSide`,
Cm/GlRefWfRel.lean).

`ledgerSide s pol` has the cells `Trace`, the two relations of Policy/Rel/LedgerRel.lean at the
table `ppOf s pol`, the honest trace and the fixed value of cells. The table s of scales has no
policy; the policy enters here.


Limits: this file does not say that the side meets `RelSide.OK`; Policy/Rel/LedgerLaws.lean does,
for a lawful s and a policy with `PolCond`. It says nothing on a protocol.
-/
import Cm.GlRefWfRel
import Policy.Rel.LedgerRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open Inst.Model Inst.Model.All

/-- The relations' side of the model whose head carries the cost ledger, at the table s of scales
and the policy pol, modulo the protocol's prime. -/
def ledgerSide (s : Cm.Scales) (pol : AcceptancePolicy) : Cm.WfGlR.RelSide where
  Cells := Trace
  Ryes := LedgerRel.Ryes Cb.Gl.p (ppOf s pol)
  Rno := LedgerRel.Rno Cb.Gl.p (ppOf s pol)
  trace := Cm.trace (ppOf s pol)
  cells0 := Cm.cells0

section
variable (s : Cm.Scales) (pol : AcceptancePolicy)

theorem ledgerSide_Cells : (ledgerSide s pol).Cells = Trace := rfl
theorem ledgerSide_Ryes : (ledgerSide s pol).Ryes = LedgerRel.Ryes Cb.Gl.p (ppOf s pol) := rfl
theorem ledgerSide_Rno : (ledgerSide s pol).Rno = LedgerRel.Rno Cb.Gl.p (ppOf s pol) := rfl
theorem ledgerSide_trace : (ledgerSide s pol).trace = Cm.trace (ppOf s pol) := rfl
theorem ledgerSide_cells0 : (ledgerSide s pol).cells0 = Cm.cells0 := rfl

end

end Policy
