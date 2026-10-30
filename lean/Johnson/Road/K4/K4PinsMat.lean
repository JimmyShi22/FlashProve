-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsMat.lean: THE COMMITTED MATRIX THAT K4's VALUE READS OFF THE PINNED PART OF A
WITNESS IS THE WITNESS's CELLS, CUT. Small theorems, by unfolding, for whoever ties the value's
matrix to what the stored table decodes to. No draw, no count.

  `RefSeat.Wn_eq`: at any seat U: the value's committed matrix off a tuple t is U's matAt t inside
    the reference rows and columns (hRef, 2 ^ kRef), 0 outside.
  `PinPlan.Wn_part`: at `PinPlan.seatN` and the pinned part of a witness w: it is the letter rc at
    w's cells inside these rows and columns, 0 outside.
  `rcQ rows cols`: the reading of cells that are a matrix on `Fin rows` and `Fin cols`: the entry
    inside, 0 outside.
  `PinPlan.Wn_cells`: so at rc := `rcQ rows cols`, at a row and a column inside both bounds, the
    value's committed matrix IS the witness's cell.
  `PinPlan.seat_mats_raw`: under `Covers` the seat's matrices (`RefSeat.mats`) are `PinPlan.raw`: at
    the seat: so at every value whose field mats is the seat's.

OBJECT: none of its own. USER: none yet; meant: the line idn of `K4Lines` in the first group (the
identity on the embedding reads the committed matrix). LETTERS, filled by nobody: every field of
`PinPlan`, what the seat hands through, rows, cols.

Limits. K04_law IS NOT PROVED BY THIS. NOTHING IS SAID OF WHAT THE STORED TABLE DECODES TO: that the
witness's cells are that matrix is the table's pin on the stored table (`pinWOf`,
Johnson/Desc/Sound/MeaningSig.lean): not called here. That rows and cols cover hRef and 2 ^ kRef is
not asked: outside them `rcQ` reads 0 in silence. The reference sizes alone.
-/
import Johnson.Road.K4.K4PinsWeights
import Johnson.Road.K4.K4PinsPlanes

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

/-- The value's committed matrix off a tuple, at any seat. -/
theorem RefSeat.Wn_eq [scl : Scl] {M : Type} (U : RefSeat M S) (X : Public) (p : Par)
    (hg : p.g < 12) (t : M) (r c : ℕ) :
    (U.atRec X p hg).plan.Wn ((U.atRec X p hg).plan.msg t) r c =
      if r < hRef ∧ c < 2 ^ kRef then U.matAt t r c else 0 := by
  rw [Plan4.Wn_msg]
  rfl

/-- The reading of cells that are a matrix on `Fin rows` and `Fin cols`. -/
def rcQ (rows cols : ℕ) (C : Fin rows → Fin cols → Cb.Gl.E) (r c : ℕ) : Cb.Gl.E :=
  if h : r < rows ∧ c < cols then C ⟨r, h.1⟩ ⟨c, h.2⟩ else 0

section
variable [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers) (tl : HTailF2)
  (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)

/-- At the pinned part of a witness: the letter rc at the witness's cells, cut. -/
theorem PinPlan.Wn_part (w : Wit Cells Tok MsgT) (r c : ℕ) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.msg
          (partOf A.D.codes arr ms N m w)) r c =
      if r < hRef ∧ c < 2 ^ kRef then A.rc w.cells r c else 0 := by
  rw [RefSeat.Wn_eq]
  show (if r < hRef ∧ c < 2 ^ kRef then A.mat (partOf A.D.codes arr ms N m w) r c else 0) = _
  rw [PinPlan.mat_some A (t := partOf A.D.codes arr ms N m w) (C := w.cells) rfl]

omit scl in
/-- Under `Covers` the seat's matrices are `PinPlan.raw`. -/
theorem PinPlan.seat_mats_raw (hC : Covers tl nM nR nC) (t : PinM Cells) :
    (A.seatN n N tl y nM nR nC n0 ns nx v7).mats t = A.raw tl t := by
  funext a r c
  show (if a < nM ∧ r < nR ∧ c < nC then A.raw tl t a r c else 0) = _
  by_cases hb : a < nM ∧ r < nR ∧ c < nC
  · rw [if_pos hb]
  · rw [if_neg hb]
    have e : cellJ (szOf tl) a r c = none := by
      cases hc : cellJ (szOf tl) a r c with
      | none => rfl
      | some j => exact absurd (hC a r c (by rw [hc]; rfl)) hb
    unfold PinPlan.raw
    rw [e]
    rfl

end

/-- **At cells that are a matrix: the value's committed matrix is the witness's cell**, at a row and
a column inside both bounds. -/
theorem PinPlan.Wn_cells [scl : Scl] {Tok : Type} {rows cols : ℕ}
    (A : PinPlan (Fin rows → Fin cols → Cb.Gl.E)) (hrc : A.rc = rcQ rows cols) (n : ℕ)
    (N : Numbers) (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par)
    (hg : p.g < 12) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)
    (w : Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) {r c : ℕ} (hr : r < hRef)
    (hc : c < 2 ^ kRef) (hr' : r < rows) (hc' : c < cols) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.msg
          (partOf A.D.codes arr ms N m w)) r c = w.cells ⟨r, hr'⟩ ⟨c, hc'⟩ := by
  rw [PinPlan.Wn_part, if_pos ⟨hr, hc⟩, hrc]
  unfold rcQ
  rw [dif_pos ⟨hr', hc'⟩]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.RefSeat.Wn_eq
#print axioms OnBytes.Road.K4.PinPlan.Wn_part
#print axioms OnBytes.Road.K4.PinPlan.seat_mats_raw
#print axioms OnBytes.Road.K4.PinPlan.Wn_cells
