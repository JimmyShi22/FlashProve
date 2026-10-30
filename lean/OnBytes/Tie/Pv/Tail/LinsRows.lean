-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/LinsRows.lean: the Lean verifier's count of the linear claims of a lookup
against the number of rows of the typed lookup's last statement.

The plans of the sub-proofs count their linear claims with Forest.lins (OnBytes/Model/Forest.lean):
the claims that a lookup leaves and that read only mask entries; four more claims of the lookup
follow, three on the planes of the counts and one on the key vectors (HTailF2.linsF,
OnBytes/Model/Tail.lean). The typed lookup's last statement has Fo.nRows rows
(OnBytes/Tie/Pv/Lookup/Forest/FoOutLen.lean). The theorems that lay a link's claims in the
verifier's order ask that the caller's claims, one claim and these rows lie below the plan's number
of linear claims. To pay that from the plans' own sums one needs the two counts against each other.
Statements and proofs.

Main names:
  `lins_rows_of_pos`: Forest.lins h + 4 = 1 + Fo.nRows h where a key's number has at least one bit.
  `lins_rows`: so where the public numbers pass the test FoNums.ok.

Limits: at a shape whose keys' numbers have no bit the equation fails: the left side is then less by
one. Nothing on which claims or rows these are: two numbers are compared.
-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutLen
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Model

/-- The two counts, where a key's number has at least one bit. -/
theorem lins_rows_of_pos (h : Forest.Shape) (hv : 0 < h.v) :
    Forest.lins h + 4 = 1 + Fo.nRows h := by
  have e : FoNums.n = 30 := rfl
  unfold Forest.lins Fo.nRows FoNums.v'
  rw [e]
  omega

/-- The two counts, where the public numbers pass the test. -/
theorem lins_rows (h : Forest.Shape) (H : FoNums.ok h = true) :
    Forest.lins h + 4 = 1 + Fo.nRows h := by
  have hd : 10 ≤ h.dT := (Cb.Fo.ok_parts H).1.1
  have hv : 0 < h.v := by
    unfold Forest.Shape.v
    omega
  exact lins_rows_of_pos h hv

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.lins_rows_of_pos
#print axioms OnBytes.Tie.Pv.Tail.lins_rows
