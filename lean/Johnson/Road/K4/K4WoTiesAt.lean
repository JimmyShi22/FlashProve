-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4WoTiesAt.lean: TWO OF THE TIES OF `k4Lines_wo_at` (K4LinesWo.lean) AT TERMS: THE
VALUE's CELLS AT THE PINNED PART OF A WITNESS ARE THE MATRIX THAT THE PILE's READER MAKES OF THE
WITNESS's CELLS. Statements with proofs: unfoldings and calls; no new argument.

THE TWO READERS. The value's: `PinPlan.Wn_part` (K4PinsMat.lean): at the seat `A.seatN …`, at the
part `partOf … w`: the committed matrix at (r, c) is `A.rc w.cells r c` where r < hRef and c < 2 ^
kRef, and 0 outside; with A.rc := `rcQ rows cols`: the witness's cells inside both bounds, 0
outside. The pile's: `matOfCells nR k c` (Johnson/Desc/K13/Law/MatOfCells.lean): at row i and the
bits of the column's number: `cellAtNo c i C`: the same cells inside both bounds, 0 outside.

  `rcQ_eq_cellAtNo`: the two readings of cells by numbers are one function: by unfolding.
  `PinPlan.wo_zero`: the value's cells are 0 from row hRef on.
  `PinPlan.wo_mat`: `matOfCells hRef kRef w.cells i (lowBits kRef C)` is the value's cell at (i, C),
    for C < 2 ^ kRef.
  `PinPlan.woTies`: `WoTies lay hRef kRef …` at that seat and part, from three equations on the
    plan's numbers.

Limits. THE THREE EQUATIONS STAY PREMISES: lay = p.P.wsLay · hRef = lay.m0 · kRef = lay.lk: on
public numbers: the reference sizes alone. hrc (A.rc = `rcQ rows cols`) is a premise on the letter
A. THAT THE PILE's READER's MATRIX IS `matOfCells hRef kRef w.cells` IS NOT SAID HERE: by its
writers' word it is so by make at their reader with that term laid in; no filling lays it yet. THE
THIRD TIE, hmask, IS NOT TOUCHED: it cannot be met until the table's promise pins the ledger's next
entry (K4LinesWo.lean's Limits). Nothing on soundness.
-/
import Johnson.Road.K4.K4LinesWo
import Johnson.Road.K4.K4PinsMat
import Johnson.Desc.K13.Law.MatOfCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model (HTailF2 WsLay)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)
open VerifiableInference.Desc.K13.Law (lowBits cellAtNo matOfCells matOfCells_low)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

/-- The two readings of cells by numbers are one function. -/
theorem rcQ_eq_cellAtNo (rows cols : ℕ) (C : Fin rows → Fin cols → Cb.Gl.E) (r c : ℕ) :
    rcQ rows cols C r c = cellAtNo C r c := rfl

section
variable [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n : ℕ) (N : Numbers) (tl : HTailF2)
  (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
  (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m : ℕ)

/-- **The value's cells are 0 from row hRef on.** -/
theorem PinPlan.wo_zero (w : Wit Cells Tok MsgT) (j : ℕ) (hj : hRef ≤ j) (C : ℕ) :
    ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.full.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.full.msg
          (partOf A.D.codes arr ms N m w)) j C = 0 := by
  show ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.Wn
      (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.msg
        (partOf A.D.codes arr ms N m w)) j C = 0
  rw [PinPlan.Wn_part, if_neg fun h => absurd h.1 (Nat.not_lt.2 hj)]

end

section
variable [scl : Scl] {Tok : Type} {rows cols : ℕ} (A : PinPlan (Fin rows → Fin cols → Cb.Gl.E))
  (hrc : A.rc = rcQ rows cols) (n : ℕ) (N : Numbers) (tl : HTailF2) (y : Lay)
  (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (m : ℕ)

include hrc in
/-- **The pile's matrix of the witness's cells is the value's cells.** -/
theorem PinPlan.wo_mat (w : Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) (i : Fin hRef) (C : ℕ)
    (hC : C < 2 ^ kRef) :
    matOfCells hRef kRef w.cells i (lowBits kRef C) =
      ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.full.Wn
        (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.full.msg
          (partOf A.D.codes arr ms N m w)) i C := by
  rw [matOfCells_low hRef kRef w.cells i C hC]
  show _ = ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.Wn
      (((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg).plan.msg
        (partOf A.D.codes arr ms N m w)) i C
  rw [PinPlan.Wn_part, if_pos ⟨i.isLt, hC⟩, hrc]
  rfl

/-- **`WoTies` at the pinned seat and part**, from three equations on the plan's numbers. -/
theorem PinPlan.woTies {lay : WsLay} (hlay : lay = p.P.wsLay) (hm0 : hRef = lay.m0)
    (hlk : kRef = lay.lk) :
    WoTies (W := Wit (Fin rows → Fin cols → Cb.Gl.E) Tok MsgT) lay hRef kRef
      ((A.seatN n N tl y nM nR nC n0 ns nx v7).atRec X p hg) (partOf A.D.codes arr ms N m) p :=
  ⟨hlay, hm0, hlk, fun w j hj C => PinPlan.wo_zero A n N tl y nM nR nC n0 ns nx v7 X p hg arr ms m
    w j hj C⟩

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.rcQ_eq_cellAtNo
#print axioms OnBytes.Road.K4.PinPlan.wo_zero
#print axioms OnBytes.Road.K4.PinPlan.wo_mat
#print axioms OnBytes.Road.K4.PinPlan.woTies
