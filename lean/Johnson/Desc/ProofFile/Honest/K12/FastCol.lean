-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastCol.lean: the column of a tree at a position, computed from
rows that are stored as arrays. Definitions only. Imports RunRows.lean alone, and no Mathlib.

A row's symbol at a position is the value of a polynomial whose coefficients are the row's tail and
then its message. `symE` (Fmt/M1Codes.lean) builds that list of coefficients again at every
position. Here the list is built once for each row, as an array, and each position only evaluates
it.

Each definition repeats one on lists, and FastColLaw.lean proves the two equal, for all arguments
and without hypothesis:
- `symA` at `rowArr` repeats `symE` (`symA_eq`).
- `colAt` at `colPrep` repeats `colOf` (Fmt/M1Own.lean), the column of a stage's tree
  (`colFast_eq`).
- `treeFast`, which is `treeAt` at `treePrep`, repeats `treeBy` (RunRows.lean), a tree given as a
  list of chosen rows (`treeFast_eq`).

How to call it. `colPrep` and `treePrep` return data: structures of arrays. Bind that value once,
before the function of the position is formed, and pass it to `colAt` or `treeAt` for each position:
`let D := colPrep s p`, then `colAt s first last D x` for every x. A partial application such as
`colAt s first last D` keeps D as it is. A definition that takes the position as one more argument
and calls `colPrep` in its body would build the arrays again at every position.

Limits.
- A second text, for speed, and the ground of ColW.lean. ColW.lean's limits say which theorems on a
  run are stated at the originals and which are not.
- It computes with random values too (the rows' tails, the mask rows, the fresh table) and keeps its
  originals' defaults, without a warning: `rowArr` fills a short or missing tail or message with 0
  and cuts a long one; `rowsArr` reads a missing tail, and `rowPrep` a missing row or tail, as
  empty; `rowSym` gives the element 0 at a row number out of range. `rowPrep` reads the rows and
  tails as `symBy` (RunRows.lean) does.
- `colPrep` builds the arrays for both values of `last`, so the rows of `PSt.P` are stored twice.
- Who calls it. `colTreeW` (ColW.lean) calls `colPrep`, and `runBy` calls `colTreeW` at `Seams.fast`
  (FastW.lean). `treeW` (ColW.lean) calls `treePrep`, and so `rowPrep`; `RunIn.ofRun` (RunJob.lean)
  builds the first trees by `treeW` at every `Seams`. So this file's readers of rows, tails, mask
  rows and the fresh table are part of such a run.
- Nothing is measured here.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Code Stage point cp fitL)
open Fmt.M1.Own (PSt words)

/-! ## 1 One row -/

/-- The coefficients of a row's polynomial: the tail, cut or padded with 0 to C.r entries, then the
message, cut or padded to C.l entries. -/
def rowArr (C : Code) (m rho : List E) : Array E :=
  (fitL Fld.zeroE C.r rho ++ fitL Fld.zeroE C.l m).toArray

/-- c_0 + c_1 z + c_2 z ^ 2 + ..., for the coefficients in A. It repeats `hornerE`
(Fmt/M1Codes.lean). -/
def hornerA (z : UInt64) (A : Array E) : E :=
  A.foldr (fun c acc => Fld.two.addE c (Fld.two.scaleE z acc)) Fld.zeroE

/-- The symbol at position x of the row with the coefficients A. -/
def symA (C : Code) (x : Nat) (A : Array E) : E := hornerA (point C.a x) A

/-- The coefficients of each row: row b is paired with tail b, as in `syms` (Fmt/M1Own.lean). -/
def rowsArr (C : Code) (rows tails : List (List E)) : List (Array E) :=
  (List.range rows.length).map fun b => rowArr C (rows.getD b []) (tails.getD b [])

/-- The symbols at position x of the rows with the coefficients As. -/
def symsA (C : Code) (x : Nat) (As : List (Array E)) : List E := As.map (symA C x)

/-! ## 2 The column of a stage's tree -/

/-- A stage's rows as arrays of coefficients. -/
structure ColData where
  /-- the main rows, under the main code -/
  main : List (Array E)
  /-- the mask rows, under the mask code -/
  mask : List (Array E)
  /-- the rows of `PSt.P` under the mask code: the fresh table at a stage that is not the last -/
  fresh : List (Array E)
  /-- the first row of `PSt.P` under the main code: the masking word's main row at a last stage -/
  word0 : List (Array E)
  /-- the other rows of `PSt.P` under the mask code: the masking word's mask row at a last stage -/
  word1 : List (Array E)

/-- The arrays for `colAt`. -/
def colPrep (s : Stage) (p : PSt) : ColData :=
  { main := rowsArr s.C p.M p.Rh, mask := rowsArr s.Z p.W p.Sg, fresh := rowsArr s.Z p.P p.Pi
    word0 := rowsArr s.C (p.P.take 1) (p.Pi.take 1)
    word1 := rowsArr s.Z (p.P.drop 1) (p.Pi.drop 1) }

/-- The column at position x. first and last are those of `colOf`. -/
def colAt (s : Stage) (first last : Bool) (D : ColData) (x : Nat) : List UInt64 :=
  if last then
    ((symsA s.C x D.main ++ symsA s.C x D.word0) ++
      (symsA s.Z (cp s.Z x) D.mask ++ symsA s.Z (cp s.Z x) D.word1)).flatMap words
  else
    (if first then ((symsA s.C x D.main).take 3).map (·.1)
        else (symsA s.C x D.main).flatMap words) ++
      (symsA s.Z (cp s.Z x) D.mask ++ symsA s.Z (cp s.Z x) D.fresh).flatMap words

/-! ## 3 A tree given as a list of chosen rows -/

/-- One chosen row. -/
structure RowData where
  /-- the row is a main row: its symbol is taken under the main code, at x itself -/
  main : Bool
  /-- the coefficients; none for a row number out of range -/
  arr : Option (Array E)
  /-- the symbol is written as its first word alone -/
  base : Bool

/-- The data of one chosen row. -/
def rowPrep (s : Stage) (p : PSt) (r : Sel) : RowData :=
  match r.kind with
  | .main =>
    ⟨true, if r.row < 2 ^ s.k then some (rowArr s.C (p.M.getD r.row []) (p.Rh.getD r.row []))
      else none, r.base⟩
  | .mask =>
    ⟨false, if r.row < 2 ^ s.h then some (rowArr s.Z (p.W.getD r.row []) (p.Sg.getD r.row []))
      else none, r.base⟩
  | .fresh =>
    ⟨false, if r.row < 2 ^ s.h then some (rowArr s.Z (p.P.getD r.row []) (p.Pi.getD r.row []))
      else none, r.base⟩

/-- The chosen row's symbol at position x; three words 0 for a row number out of range. -/
def rowSym (s : Stage) (x : Nat) (d : RowData) : E :=
  match d.arr with
  | none => Fld.zeroE
  | some A => if d.main then symA s.C x A else symA s.Z (cp s.Z x) A

/-- The stage and the chosen rows' data. -/
structure TreeData where
  s : Stage
  rows : List RowData

/-- The data for `treeAt`. -/
def treePrep (s : Stage) (T : Nat × List Sel) (p : PSt) : TreeData := ⟨s, T.2.map (rowPrep s p)⟩

/-- The column at position x: the chosen rows' symbols, one after the other, as words. -/
def treeAt (D : TreeData) (x : Nat) : List UInt64 :=
  D.rows.flatMap fun d => if d.base then [(rowSym D.s x d).1] else words (rowSym D.s x d)

/-- A tree, built from T as by `treeBy`. The data is built when the pair is built, and the column
function keeps it. -/
def treeFast (s : Stage) (T : Nat × List Sel) (p : PSt) : Tree := (T.1, treeAt (treePrep s T p))

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.rowArr
#print axioms ProofFile.Honest.K12.Light.hornerA
#print axioms ProofFile.Honest.K12.Light.symA
#print axioms ProofFile.Honest.K12.Light.rowsArr
#print axioms ProofFile.Honest.K12.Light.symsA
#print axioms ProofFile.Honest.K12.Light.ColData
#print axioms ProofFile.Honest.K12.Light.colPrep
#print axioms ProofFile.Honest.K12.Light.colAt
#print axioms ProofFile.Honest.K12.Light.RowData
#print axioms ProofFile.Honest.K12.Light.rowPrep
#print axioms ProofFile.Honest.K12.Light.rowSym
#print axioms ProofFile.Honest.K12.Light.TreeData
#print axioms ProofFile.Honest.K12.Light.treePrep
#print axioms ProofFile.Honest.K12.Light.treeAt
#print axioms ProofFile.Honest.K12.Light.treeFast
