--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/WhBand.lean: THE WEIGHTS THAT THE OUTPUT HEAD's LAW READS OFF A WITNESS's
CELLS (whOf, Law/WhOf.lean: the output matrix in the index that the committed table holds) ARE A
HARNESS's READER OF THE TABLE's BAND OF 2 x 5,120 ROWS FROM ROW 3,065,840 ON: two signed bytes a
weight, in the rows o + k and o + 5,120 + k of column v. STATED AND PROVED: calls of the library's
landed Hof_weightsOf (Inst/Model/Head/Trace.lean), this house's whOf_holds and the flat road's
(Johnson/Flat/LedgerClaim.lean). AT THE REFERENCE SIZES ALONE (ppref, kRef: whOf's own).
A RELATIVE, THIS HOUSE's OWN, LANDED: Law/HeadWeightsMeet.lean's weights_stored: the lookup's
caller's reading of the same two bytes against whOf: it has "whOf w.cells k v = Hof i.mat k v" as a
step inside its proof; here that step stands as a statement, at all k and v, and goes on to bytes.
WHAT IT CANNOT GIVE, FIRST. · THAT THE CELLS HOLD AN INDEX (Holds M i): A PREMISE: it speaks of THE
WHOLE TABLE (every entry a signed byte; every pair of bytes of a two-byte weight within 2^12): where
the cells hold none whOf is 0, in silence · that any witness's cells are any file's bytes: hM is a
premise: the making of the witness. NO VALUE IS EVALUATED. Nothing on soundness or on hiding.
  whOfBand B      the reader in the law's letters: B q v: the band's row q, column v.
  whOf_index      whOf M = whOfBand at the index's own entries of the band.
  index_of_cell   where a cell of M is the cast of a signed byte, the index's entry there is that
                  byte.
  **whOf_band**   whOf M = whOfBand B, where M's cells of the band are the casts of B's signed
                  bytes.

-/
import Johnson.Desc.Kinds.Law.WhOf
import Inst.Model.Head.Trace

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Sym

open Inst.Model.Layout (kRef hRef)
open Inst.Model.Head (oH nD nV Hof Hof_weightsOf)
open VerifiableInference.OnPublicFiles.Flat (GE Holds digit_eq)

/-- A harness's reader of the output matrix's weights, at a letter for the band's bytes. -/
def whOfBand (B : Nat → Nat → Int) : Nat → Nat → Int := fun k v =>
  if k < nD ∧ v < nV then B k v + 256 * B (nD + k) v else 0

variable {rows cols : Nat}

/-- The weights are the reader at the index's own entries of the band. -/
theorem whOf_index (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i : Cm.Idx} (h : Holds M i) : whOf M = whOfBand fun q v => i.mat (oH + q) v := by
  rw [Came.whOf_holds hr hc h]
  funext k v
  unfold whOfBand
  by_cases hin : k < nD ∧ v < nV
  · rw [if_pos hin, Hof_weightsOf _ hin.1 hin.2]
    show i.mat (oH + k) v + 256 * i.mat (oH + 5120 + k) v =
      i.mat (oH + k) v + 256 * i.mat (oH + (5120 + k)) v
    rw [Nat.add_assoc]
  · rw [if_neg hin]
    exact if_neg hin

/-- Where a cell is the cast of a signed byte, the index's entry there is that byte. -/
theorem index_of_cell (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i : Cm.Idx} (h : Holds M i) (y c : Nat) (hy : y < rows) (hcc : c < cols) (b : Int)
    (hM : M ⟨y, hy⟩ ⟨c, hcc⟩ = ((b : Int) : GE)) (hb : -2 ^ 7 ≤ b ∧ b < 2 ^ 7) :
    i.mat y c = b :=
  digit_eq (i.wf.1 y (lt_of_lt_of_le hy hr) c (lt_of_lt_of_le hcc hc)) hb
    ((h.1 ⟨y, hy⟩ ⟨c, hcc⟩).symm.trans hM)

/-- **THE WEIGHTS OFF THE WITNESS's CELLS ARE THE HARNESS's READER OF THE BAND.** -/
theorem whOf_band (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i : Cm.Idx} (h : Holds M i) (B : Nat → Nat → Int) (hrows : oH + 2 * nD ≤ rows)
    (hcols : nV ≤ cols)
    (hM : ∀ q v (hq : q < 2 * nD) (hv : v < nV),
      M ⟨oH + q, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hq oH) hrows⟩
        ⟨v, Nat.lt_of_lt_of_le hv hcols⟩ = ((B q v : Int) : GE))
    (hb : ∀ q v, q < 2 * nD → v < nV → -2 ^ 7 ≤ B q v ∧ B q v < 2 ^ 7) :
    whOf M = whOfBand B := by
  rw [whOf_index hr hc h]
  funext k v
  unfold whOfBand
  by_cases hin : k < nD ∧ v < nV
  · have q0 : k < 2 * nD := by omega
    have q1 : nD + k < 2 * nD := by omega
    rw [if_pos hin, if_pos hin]
    show i.mat (oH + k) v + 256 * i.mat (oH + (nD + k)) v = B k v + 256 * B (nD + k) v
    rw [index_of_cell hr hc h (oH + k) v _ _ (B k v) (hM k v q0 hin.2) (hb k v q0 hin.2),
      index_of_cell hr hc h (oH + (nD + k)) v _ _ (B (nD + k) v) (hM (nD + k) v q1 hin.2)
        (hb (nD + k) v q1 hin.2)]
  · rw [if_neg hin, if_neg hin]

end VerifiableInference.Desc.Kinds.Head.Law.Sym

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Sym.whOf_index
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Sym.index_of_cell
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Sym.whOf_band
