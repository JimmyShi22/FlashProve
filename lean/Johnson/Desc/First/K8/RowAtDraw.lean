-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/RowAtDraw.lean: THE SMALLNESS TEST: THE FIRST TABLE'S ROW AT THE NUMBER OF
EACH OF ITS TWENTY-FIVE DRAWS, AT THE FULL SIZE: what the sub-protocol closes, opens and reads. One
test with code; statements with their proofs.

Main names (namespace `VerifiableInference.Desc.First.K8`).
  `pieceAt l`: the piece's number behind the draw's: 5; at the output head's segment (24): 6.
    `rowAtB links ps l`: the test: at k := `drawAt l` (Johnson/Desc/First/K8/TiePromise.lean) the
    row `Sound.rowQ links ps k` has ins = [constr l small, tie l], outs = [forms l (pieceAt l)
    "small", constr l lookDigits], ctx = [pin l 0, pin l 1].
  `rowAtB_full`: it accepts at all twenty-five, at `Sound.linksFull` and its written list of places:
    BY LEAN'S KERNEL. **`row_at_draw_full`**: the three equations, for l ≤ 24.

Every "there is": none.
Limits. A closed fact on the table's text at the full size's list of segments; it says nothing of a
run. The row's other fields (lays, known, whose) are not said. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K8.TiePromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item flatPlacesOf)

/-- The piece's number behind the draw's. -/
def pieceAt (l : ℕ) : ℕ := if l = 24 then 6 else 5

/-- The test: the row at the draw's number of segment l closes, opens and reads just these. -/
def rowAtB (links : List ModelPart) (ps : List Place) (l : ℕ) : Bool :=
  decide ((rowQ links ps (drawAt l)).ins = [.constr l .small, .tie l]) &&
    decide ((rowQ links ps (drawAt l)).outs =
      [.forms l (pieceAt l) "small", .constr l .lookDigits]) &&
    decide ((rowQ links ps (drawAt l)).ctx = [.pin l 0, .pin l 1])

theorem rowAtB_full :
    ((List.range 25).all fun l => rowAtB linksFull (flatPlacesOf linksFull true) l) = true := by
  decide +kernel

/-- **THE ROW AT THE TWENTY-FIVE NUMBERS.** -/
theorem row_at_draw_full (l : ℕ) (hl : l ≤ 24) :
    (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).ins =
        [.constr l .small, .tie l] ∧
      (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).outs =
        [.forms l (pieceAt l) "small", .constr l .lookDigits] ∧
      (rowQ linksFull (flatPlacesOf linksFull true) (drawAt l)).ctx = [.pin l 0, .pin l 1] := by
  have h := List.all_eq_true.1 rowAtB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold rowAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.rowAtB_full
#print axioms VerifiableInference.Desc.First.K8.row_at_draw_full
