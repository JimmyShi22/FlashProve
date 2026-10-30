-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AnswersFull.lean: the general statement on the out-of-domain (OOD) answers
(`answers_cells`, Johnson/Bind/Cpp/AnswersCells.lean), taken at the full size's numbers. A call.
Limits. Values in a field. No binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no correctness of extraction and no index privacy is
stated here. Nothing on any program.

-/
import Johnson.Bind.Cpp.AnswersCells
import Johnson.Bind.Cpp.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.answers OnBytes.K.IdTable.spellAns
  OnBytes.K.IdTable.spellSeedL honestMsgs cellWords cellEntry Cb.Ood.Sample.val

/-- The full size's shape is made of the full size's numbers. -/
theorem shapeFull_is :
    shapeFull = ⟨frS.P.T.a, frS.P.T.l, frS.P.T.r, frS.P.v, 1, 40⟩ := rfl

/-- At the full size's numbers. -/
theorem answers_full (M : Cells (frS.toDecR frZ 402653181) numsRef) (η : PadsOf frS 402653181)
    (T : Bind.Twin.Table)
    (hT1 : ∀ b e, e < 402653181 →
      T.entry b e = cellEntry frS frZ 402653181 numsRef M (fun _ _ => 0) b e)
    (hT2 : ∀ b k (hb : b < 2 ^ frS.P.v) (hk : k < frS.P.T.l - 402653181),
      toF (T.pad b k) = η ⟨b, hb⟩ ⟨k, hk⟩)
    (sd : frZ.D) :
    (OnBytes.K.IdTable.spellAns 11 1
        ((frS.toDecR frZ 402653181).ix.ZR.val sd
          (honestMsgs frS (cellWords frS frZ 402653181 numsRef M η)))).map OnBytes.E.triple =
      Bind.Twin.answers shapeFull T
        ((OnBytes.K.IdTable.spellSeedL 29 1 sd).map fun y =>
          (y.1.map OnBytes.E.triple, y.2.triple)) := by
  have h3 : 3 * 1 ≤ frS.P.T.l := by
    show 3 * 1 ≤ 402653184
    omega
  rw [shapeFull_is]
  exact answers_cells frS 402653181 29 1 40 numsRef fr_Z.2.symm h3 M η T hT1 hT2 sd

end Bind.Cpp

#print axioms Bind.Cpp.shapeFull_is
#print axioms Bind.Cpp.answers_full
