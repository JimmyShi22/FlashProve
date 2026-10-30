-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnW.lean: THE WRITTEN NUMBERS OF KIND K5's OWN ROUNDS AT THE FULL
SIZE, AND: THE TWO
LIGHT TESTS OF K5's ROW NEVER READ THE TWELFTH FIELD. A definition and two laws by rfl.
  `ownW`: eleven numbers (lt 10 · lgk 3 · pairs 20 · Lam 4 · planeMessages 2 · score [(17, 20),
    (14, 20)] · e 13 · valueM 16 · valueD 13 · attained 20 · bits 17); rows := 0 stands for nothing.
  `nRounds_rows`, `planOkOwn_rows`: `nRounds` and `planOkOwn` (K5RowBlock.lean) at a value with
    another number in the field rows are what they are at the value.
Limits. Nothing on the field rows. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5RowBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes

/-- The eleven written numbers; the field rows is filled by whoever reads it. -/
def ownW : Params.AttentionRounds :=
  { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14, 20)],
    e := 13, valueM := 16, valueD := 13, attained := 20, bits := 17, rows := 0 }

theorem nRounds_rows (x : Params.AttentionRounds) (r : ℕ) :
    nRounds { x with rows := r } = nRounds x := rfl

theorem planOkOwn_rows (x : Params.AttentionRounds) (r : ℕ) :
    planOkOwn { x with rows := r } = planOkOwn x := rfl

end H2K5.Row

#print axioms H2K5.Row.nRounds_rows
#print axioms H2K5.Row.planOkOwn_rows
