-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY READER OF CELLS.
Johnson/Desc/ProofFile/Honest/K3/Term/TraceMatricesOfTheCells.lean: the honest side of the kind
"lookup" (K3): the integer matrices of a link, READ OFF A READER OF CELLS BY LABELS: so that the
letter `traceMatrices` of the named premises (Honest/K3/Term/ScriptHoldsTheHonestValues.lean) is a
closed term at the term's input.

  `traceMatricesOfTheCells`                 number in the link's list, row, column: the least residue in
                                            absolute value of the cell under the number's label
  `cellsByNumberAreTheCastsOfTheirIntegers` the library's `atNo` is its cast: AT EVERY READER OF CELLS
  `traceMatricesOfTheCellsAtATrace`         at the reader `cellOf X T` of a trace below 2 ^ 60 it is T's list

Limits. Nothing says that a reader of cells is honest or small. Nothing on any property.
-/
import Johnson.HonestTrace.FromCells
import Johnson.HonestTrace.Packed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (labelAt atNo cellOf NamesFit Tr atNo_cellOf valMinAbs_cast)

/-- **The integer matrices of a link, off a reader of cells by labels.** 0 where the number has no
label in the link's list. -/
def traceMatricesOfTheCells (X : OnBytes.Model.Verify.Public)
    (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (link : ℕ) : OnBytes.Road.Mats ℤ :=
  fun number row column =>
    match labelAt X link number with
    | some label => (cell link label row column).valMinAbs
    | none => 0

/-- **The library's reading of a cell by its number is the cast of that integer**: at every reader
of cells, every link, number, row and column. -/
theorem cellsByNumberAreTheCastsOfTheirIntegers (X : OnBytes.Model.Verify.Public)
    (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (link number row column : ℕ) :
    atNo X cell link number row column =
      ((traceMatricesOfTheCells X cell link number row column : ℤ) : Cb.Gl.E) := by
  unfold atNo traceMatricesOfTheCells
  cases labelAt X link number with
  | none => exact Int.cast_zero.symm
  | some label =>
    show algebraMap Cb.Gl.F Cb.Gl.E (cell link label row column) =
      (((cell link label row column).valMinAbs : ℤ) : Cb.Gl.E)
    rw [← map_intCast (algebraMap Cb.Gl.F Cb.Gl.E), ZMod.coe_valMinAbs]

/-- **At the reader of a trace by labels these are the trace's own matrices.** CONDITIONAL: the
names fit; the link is below 25; the trace's entries at the link are below 2 ^ 60 in absolute
value. -/
theorem traceMatricesOfTheCellsAtATrace {X : OnBytes.Model.Verify.Public} {T : Tr}
    (namesFit : NamesFit X T) {link : ℕ} (linkBelow : link < 25)
    (small : ∀ number row column, |T link number row column| < 2 ^ 60) :
    traceMatricesOfTheCells X (cellOf X T) link = T link := by
  funext number row column
  have e := atNo_cellOf namesFit linkBelow number row column
  unfold atNo at e
  unfold traceMatricesOfTheCells
  cases hl : labelAt X link number with
  | none => exact (namesFit.beyond link linkBelow number row column hl).symm
  | some label =>
    rw [hl] at e
    have e' : cellOf X T link label row column = ((T link number row column : ℤ) : Cb.Gl.F) :=
      (algebraMap Cb.Gl.F Cb.Gl.E).injective (by rw [map_intCast]; exact e)
    show (cellOf X T link label row column).valMinAbs = _
    rw [e', valMinAbs_cast (small number row column)]

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.traceMatricesOfTheCells
#print axioms ProofFile.Honest.K3.Term.cellsByNumberAreTheCastsOfTheirIntegers
#print axioms ProofFile.Honest.K3.Term.traceMatricesOfTheCellsAtATrace
