-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/DigitsTabCore.lean: the tables of the cells and of the combinations
of a smallness test, and a digit read off them. Definitions with code; no theorem. They stand in a
file of their own, with few imports, so that a program can have their loops as compiled code.

Terms. Honest/K3/GLOSSARY.md. In this file: a combination is `comb`
(Johnson/Desc/K8/Honest/Window.lean): of a row of cells of one matrix and a number u below tau, the
sum over the matrix's columns of a sampled entry times a cell. A digit is the low or the high part
of a combination. A row of cells is counted through all matrices of the place's list. A table of a
function is an array that stands for it (Honest/K3/Memo.lean).

What is defined.
  `combAt`: the text of `comb` with the matrix's first column, its number of columns and its row of
    cells handed in.
  `combG`: a combination by the row of cells as counted through all matrices; 0 beyond them.
  `cellTab`: the cells' tables: matrix, then row, then column. The cells' reader is handed in.
  `combTab`: the combinations' table: row of cells as counted through all matrices, then u.
  `digitBy`: the text of `digitAt` over a function that yields the combinations.

Imported. Johnson/Desc/K8/Honest/Window.lean and Honest/K3/Memo.lean, and what stands beneath the
first. Nothing of the frame; no other file of Honest/K3.

Users. Honest/K3/WitDigitsTab.lean (the reader) imports this file; Honest/K3/Law/DigitsTab.lean (the
equations) has it through that one.

Limits. Nothing here says that a table holds what it is named after: see
Honest/K3/Law/DigitsTab.lean. How long anything takes is not said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.K8.Honest.Window
import Johnson.Desc.ProofFile.Honest.K3.Memo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc.First.K8 (Par firstColumns)
open VerifiableInference.Desc.First.K8.Honest (CellsAt comb allRows rowAt low high)

/-- The text of `comb`: f0 the matrix's first column among all columns, k its number of columns,
row its row of cells. -/
def combAt (tau f0 k : Nat) (drawn : Array Int) (row : Nat → Int) (u : Nat) : Int :=
  (List.range k).foldl (fun z c => z + drawn.getD ((f0 + c) * tau + u) 0 * row c) 0

/-- A combination by the row of cells as counted through all matrices; 0 beyond them. -/
def combG (p : Par) (cell : CellsAt) (drawn : Array Int) (g u : Nat) : Int :=
  match rowAt p.ms 0 g with
  | some (mu, i) => comb p cell drawn mu i u
  | none => 0

/-- **The cells' tables**: matrix, then row, then column. -/
def cellTab (p : Par) (cell : CellsAt) : Array (Array (Array Int)) :=
  Memo.tab p.ks.length fun mu => Memo.tab2 (p.ms.getD mu 0) (p.ks.getD mu 0) (cell mu)

/-- **The combinations' table**: row of cells as counted through all matrices, then u. cel: the
cells' tables. A row's table of cells is taken out once for its tau combinations. cell: the cells'
reader, which `Memo.read` asks beyond a table's end: a table of cells that is too short costs time,
not truth. -/
def combTab (p : Par) (cell : CellsAt) (drawn : Array Int) (cel : Array (Array (Array Int))) :
    Array (Array Int) :=
  let fc := firstColumns p
  Memo.tab (allRows p) fun g =>
    match rowAt p.ms 0 g with
    | some (mu, i) =>
      let r := (cel.getD mu #[]).getD i #[]
      let f0 := fc.getD mu 0
      let k := p.ks.getD mu 0
      Memo.tab p.tau fun u => combAt p.tau f0 k drawn (Memo.read r (cell mu i)) u
    | none => Memo.tab p.tau fun _ => 0

/-- The text of `digitAt` over a function cg that yields the combinations, by the row of cells as
counted through all matrices. -/
def digitBy (p : Par) (cg : Nat → Nat → Int) (u col : Nat) : Nat :=
  let mz := allRows p
  let g := if col < mz then col else col - mz
  match rowAt p.ms 0 g with
  | some _ =>
    if u < p.tau then
      if col < mz then low (cg g u) else high (cg g u)
    else 0
  | none => 0

end ProofFile.Honest.K3
