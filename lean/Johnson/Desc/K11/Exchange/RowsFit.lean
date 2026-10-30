-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Exchange/RowsFit.lean: the proof of `RowsFitAtHead`
(Johnson/Desc/K11/Exchange/RowsFitStatement.lean), to the letter. A lemma; none of the library's
goals.

How. The data's shape of the batch is the first chain's parameters' own (`d1At`,
Johnson/Top/H0/Fill/D1At.lean: by unfolding); under the head these parameters, as read back, are the
written ones (`first_written_in_scope`, Johnson/Goal/Numbers/MadeInScope.lean, at `pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean: as the library's own `AtMg.shape_written` calls them); at the
written shape the comparison of two numbers is closed: BY EVALUATION IN LEAN's KERNEL (`decide
+kernel`).

Limits. Those of the statement. The evaluation is one in Lean's own kernel. Nothing on any property.
-/
import Johnson.Desc.K11.Exchange.RowsFitStatement
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Exchange

/-- **Under the head the matrix's rows fit the bits that name a row.** -/
theorem rowsFitAtHead : RowsFitAtHead := by
  intro Z D r Zp Np cF x h
  have e : Zp.first.lin = _ :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
      (P5J.pins_of_laid h.scope h.laid).1).2.1
  show OnBytes.Flat.numsFull.rows ≤ 2 ^ Zp.first.lin.kRow
  rw [e]
  decide +kernel

end Johnson.Desc.First.ForkMerge.Exchange

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Exchange.rowsFitAtHead
