-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyPack.lean: THE FURTHER TABLE OF A FOLDING STAGE, BY INDEX, MADE OF THE
COEFFICIENTS W: the library's packing (packed, Johnson/Prover/Link/FoldHolds.lean) as rows and
places by numbers; 0 where the stage has no room for it. Definition, statements and proofs.

  packedN s W     row number b, place j: packed s hl W at the vertex of b's lowest bits and j
  phiOf_packedN   a state whose further table is packedN s W has φOf s P = packed s hl W
  pairs_packedN   so Pairs s s.Z.l W (φOf s P): fold_V's premise hP
  packedN_row     at s.h = 0 the table has one row: the row's number is not read

Not shown here. Nothing on how W is chosen; nothing on what the table is for, or on what any
entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyState
import Johnson.Prover.Link.FoldHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- The packing of W, by numbers. -/
def packedN (s : Sg) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (b j : ℕ) : GE :=
  if h : s.h + 2 * s.g + 1 ≤ s.Z.l ∧ j < s.Z.l then
    packed s h.1 W (fun t => b.testBit t.val, ⟨j, h.2⟩)
  else 0

theorem phiOf_packedN (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)
    (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (P : PS) (hP : P.fM = packedN s W) :
    φOf s P = packed s hl W := by
  funext x
  show P.fM (Sz.rowNo x.1) x.2.val = _
  rw [hP]
  unfold packedN
  rw [dif_pos ⟨hl, x.2.isLt⟩]
  exact congrArg (packed s hl W) (Prod.ext (funext (testBit_rowNo x.1)) rfl)

theorem pairs_packedN (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)
    (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (P : PS) (hP : P.fM = packedN s W) :
    Pairs s s.Z.l W (φOf s P) := by
  rw [phiOf_packedN s hl W P hP]
  exact pairs_packed s hl W

/-- Where the stage has no row variable on the mask table, every row's number gives the one row. -/
theorem packedN_row (s : Sg) (h0 : s.h = 0) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (b : ℕ) :
    packedN s W b = packedN s W 0 := by
  funext j
  unfold packedN
  have e : (fun t : Fin s.h => b.testBit t.val) = fun t : Fin s.h => (0 : ℕ).testBit t.val :=
    funext fun t => absurd t.isLt (by omega)
  rw [e]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.packedN_row
#print axioms Johnson.Prover.Link.packedN
#print axioms Johnson.Prover.Link.phiOf_packedN
#print axioms Johnson.Prover.Link.pairs_packedN
