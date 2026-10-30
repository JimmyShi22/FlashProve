-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitDigitsTab.lean: the reader of the input at a lookup on the
digits of a smallness test, with tables of the cells, of the combinations and of the digits' rows,
made at each application of the reader. Definitions with code; no theorem. That the reader is
`fastAsk` (Honest/K3/WitDigitsFast.lean) is shown in Honest/K3/Law/DigitsTab.lean.

Terms. Honest/K3/GLOSSARY.md. In this file: a combination is `comb`
(Johnson/Desc/K8/Honest/Window.lean): of a row of cells of one matrix and a number u below tau, the
sum over the matrix's columns of a sampled entry times a cell. A digit is the low or the high part
of a combination. A row of cells is counted through all matrices of the place's list. A table of a
function is an array that stands for it (Honest/K3/Memo.lean).

Why. By the text of `fastAsk`, a program that evaluates it as it stands does three things again and
again (read in the text; no time is told here).
  A key is a digit, and a digit makes its combination from the cells: a sum over as many terms as
    the matrix has columns; the low and the high digit each do so; and so does each of the two walks
    over all places, for the keys and for the counts.
  Each term of a combination makes the list of the matrices' first columns anew (`entry`).
  For the counts, the row of a place's key is sought by `firstRow`
    (Johnson/HonestTrace/Counts.lean): a walk along the call's table from its first row on, at every
    place.

What is defined.
  (The tables of the cells and of the combinations, and the digit read off them, `cellTab`,
    `combTab` and `digitBy`, stand in Honest/K3/DigitsTabCore.lean.)
  `digitE`, `rowOfDigit`, `rowTab`: a number as an element of the extension field; for a call and a
    number n: `firstRow` of n as an element; its table.
  `hitsTab`: padding places and rows of the lookup's places, the rows off `rowTab`.
  `tabLookZ`: the text of `fastLookZ` at digits that are numbers, with `hitsTab`.
  `tabAsk`: the reader. All tables are bound in front of the structure that one application returns.

Imported. Honest/K3/WitDigitsFast.lean and what stands beneath it; Honest/K3/DigitsTabCore.lean, and
through it Honest/K3/Memo.lean.

Users. Honest/K3/Law/DigitsTab.lean; Honest/K3/WitDigitsTabGuards.lean [not in this library];
Honest/K3/WitTab.lean; Honest/K3/Tab/TabAll.lean.

Limits. That a table is made once is a matter of how a program evaluates the term: whoever applies
`tabAsk` binds its value once. The tables are made at every application, the table of the digits'
rows among them, though it depends on the public shape alone. A digit from 2 ^ kT on, or a call from
NC on, is not in that table: its row is then sought as before. Room: one number for each cell of the
place's matrices and one for each combination. How long anything takes is not said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitDigitsFast
import Johnson.Desc.ProofFile.Honest.K3.DigitsTabCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Hits padZ firstRow tabOf)
open OnBytes.DgP (digInCall)
open ProofFile.Honest.K8 (parOfTail cellsAtOf)
open VerifiableInference.Desc.First.K8 (Par firstColumns)
open VerifiableInference.Desc.First.K8.Honest (CellsAt comb allRows rowAt low high)

/-! ## 1 The rows for the counts -/

/-- A number as an element of the extension field, by way of the base field. -/
def digitE (n : ℕ) : Cb.Gl.E := algebraMap Cb.Gl.F Cb.Gl.E ((n : ℕ) : Cb.Gl.F)

/-- The first row of call c's table that holds the number n. -/
def rowOfDigit (h : OnBytes.Model.Forest.Shape) (c n : ℕ) : ℕ :=
  firstRow (tabOf Cb.Gl.E h c) (FoNums.kOf h c) (digitE n)

/-- Its table: call, then the numbers below 2 ^ kT. -/
def rowTab (h : OnBytes.Model.Forest.Shape) : Array (Array ℕ) :=
  Memo.tab2 h.NC (2 ^ h.kT) (rowOfDigit h)

/-- **Padding places and rows of the lookup's places**, of the digits dg as numbers; rt: the table
of the digits' rows. -/
def hitsTab (tl : HTailF2) (dg : ℕ → ℕ → ℕ) (rt : Array (Array ℕ)) : Hits where
  pad := padZ tl
  row := fun c i =>
    match digInCall tl c i with
    | some t => Memo.read2 rt (rowOfDigit tl.f9) c (dg t.2.2 (c * tl.mz + t.2.1))
    | none => FoNums.t0Of tl.f9 c

/-! ## 2 The reader -/

/-- **The digits of a smallness test, of the digits as numbers**: the text of `fastLookZ` with
`hitsTab`. -/
def tabLookZ (tl : HTailF2) (dg : ℕ → ℕ → ℕ) : LookIn :=
  let rt := rowTab tl.f9
  let H := hitsTab tl dg rt
  let A := countsOf tl.f9 H
  ⟨(lookZ tl fun u col => ((dg u col : ℕ) : Cb.Gl.F)).key,
   fun u j => ((bzFast tl H A ((OnBytes.DgP.portQ tl).bAt u j).2.1
     ((OnBytes.DgP.portQ tl).bAt u j).2.2 : ℕ) : Cb.Gl.E)⟩

/-- **The structure of the lookup on the digits of a link, with tables**: at the cells and at the
entries that round number rng sampled. -/
def tabAsk (X : OnBytes.Model.Verify.Public) (link rng : ℕ) (C : Cells)
    (heard : List Fmt.Drawn) : Hidden :=
  let tl := tlOf X link
  let P := parOfTail tl
  let R := cellsAtOf C (matsOwn X link)
  let A := (tritsAt heard rng).toArray
  let cel := cellTab P R
  let cmb := combTab P R A cel
  (tabLookZ tl (digitBy P (Memo.read2 cmb (combG P R A)))).hidden

end ProofFile.Honest.K3
