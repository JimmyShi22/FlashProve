-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/SlotsTo.lean: how many scalars the parts in front of a part of the row of
an attention segment's own rounds send (shapes, PartShape.scalars,
Johnson/Desc/K5/Honest/Faces.lean). One definition with code, and two small statements with their
proofs. What it is for, AND NOT SHOWN HERE (conditional statements on it:
Johnson/Desc/ProofFile/Honest/K5/Law/Slots.lean, Coins.lean): a scalar's number in the order of
sending is its slot's number in the verifier's ledger, counted from the first slot that the rounds
take; and it is the number of the coin that is spent for it.

  slotsTo x q      the scalars of the parts in front of part number q
  slotsTo_zero, slotsTo_next

Limits. Public numbers alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Faces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest

/-- **The scalars that the parts in front of part number q send.** -/
def slotsTo (x : OnBytes.Params.AttentionRounds) (q : Nat) : Nat :=
  (((shapes x).take q).map (·.scalars)).sum

theorem slotsTo_zero (x : OnBytes.Params.AttentionRounds) : slotsTo x 0 = 0 := rfl

/-- CONDITIONAL: s is part number q. -/
theorem slotsTo_next (x : OnBytes.Params.AttentionRounds) {q : Nat} {s : PartShape}
    (h : (shapes x)[q]? = some s) : slotsTo x (q + 1) = slotsTo x q + s.scalars := by
  unfold slotsTo
  rw [List.take_add_one, h, List.map_append, List.sum_append]
  simp

end H2K5.Honest

#print axioms H2K5.Honest.slotsTo_zero
#print axioms H2K5.Honest.slotsTo_next
