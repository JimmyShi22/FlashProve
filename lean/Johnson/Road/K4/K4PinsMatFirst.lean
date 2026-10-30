-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsMatFirst.lean: THE COMMITTED MATRIX THAT K4's VALUE IN THE FIRST GROUP READS
OFF THE PINNED PART OF A WITNESS IS THE WITNESS's CELLS, CUT. The twin of three theorems of
Johnson/Road/K4/K4PinsMat.lean, by their proofs; `rcQ` and `PinPlan.seat_mats_raw` name no value and
are taken as they stand. Small theorems, by unfolding. No draw, no count.

  `RefSeat.Wn_eqF`: at any seat U: the first group's value's committed matrix off a tuple t is U's
    matAt t inside the reference rows and columns (hRef, 2 ^ kRef), 0 outside: THE PREMISE hWn OF
    `emb_at_table` (Johnson/Road/K4/K4IdnFirst.lean), in its letters.
  `PinPlan.Wn_partF`: at `PinPlan.seatN` and the pinned part of a witness w: it is the letter rc at
    w's cells inside these rows and columns, 0 outside.
  `PinPlan.Wn_cellsF`: at rc := `rcQ rows cols`, at a row and a column inside both bounds, it IS the
    witness's cell.

Limits. K04_law IS NOT PROVED BY THIS. All limits of K4PinsMat.lean stand. No premise on the group
is asked. OBJECT: none of its own. USER: none here; meant: the line idn of `K4Lines` in the first
group. The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsMat
import Johnson.Road.K4.CloseRefFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (cellJ szOf)
open VerifiableInference.Desc.Sound (Mem MsgT)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

/-- The first group's value's committed matrix off a tuple, at any seat. -/
theorem RefSeat.Wn_eqF [scl : Scl] {M : Type} (U : RefSeat M S) (X : Public) (p : Par)
    (t : M) (r c : ℕ) :
    (U.atRecF X p).toLF.planF.Wn ((U.atRecF X p).toLF.planF.toPlan4.msg t) r c =
      if r < hRef ∧ c < 2 ^ kRef then U.matAt t r c else 0 := by
  rw [Plan4.Wn_msg]
  rfl

section
variable [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers) (tl : HTailF2)
  (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)

/-- At the pinned part of a witness: the letter rc at the witness's cells, cut. -/
theorem PinPlan.Wn_partF (w : Wit Cells Tok MsgT) (r c : ℕ) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toLF.planF.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toLF.planF.toPlan4.msg
          (partOf A.D.codes arr ms N m w)) r c =
      if r < hRef ∧ c < 2 ^ kRef then A.rc w.cells r c else 0 := by
  rw [RefSeat.Wn_eqF]
  show (if r < hRef ∧ c < 2 ^ kRef then A.mat (partOf A.D.codes arr ms N m w) r c else 0) = _
  rw [PinPlan.mat_some A (t := partOf A.D.codes arr ms N m w) (C := w.cells) rfl]

end

/-- **At cells that are a matrix: the first group's value's committed matrix is the witness's
cell**, at a row and a column inside both bounds. -/
theorem PinPlan.Wn_cellsF [scl : Scl] {Tok : Type} {rows cols : ℕ}
    (A : PinPlan (Fin rows → Fin cols → Cb.Gl.E)) (hrc : A.rc = rcQ rows cols) (n : ℕ)
    (N : Numbers) (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)
    (w : Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) {r c : ℕ} (hr : r < hRef)
    (hc : c < 2 ^ kRef) (hr' : r < rows) (hc' : c < cols) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toLF.planF.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRecF X p).toLF.planF.toPlan4.msg
          (partOf A.D.codes arr ms N m w)) r c = w.cells ⟨r, hr'⟩ ⟨c, hc'⟩ := by
  rw [PinPlan.Wn_partF, if_pos ⟨hr, hc⟩, hrc]
  unfold rcQ
  rw [dif_pos ⟨hr', hc'⟩]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.Wn_eqF
#print axioms OnBytes.Road.K4.PinPlan.Wn_partF
#print axioms OnBytes.Road.K4.PinPlan.Wn_cellsF
