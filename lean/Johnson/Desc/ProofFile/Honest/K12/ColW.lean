-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ColW.lean: the column of a tree at a position, computed from rows
that are stored as arrays, with the field's arithmetic on 64-bit words alone. Definitions only.
Imports FastCol.lean alone, and no Mathlib.

A row's symbol at a position is the value of the row's polynomial at a point z, computed by c + z *
acc for each coefficient c, from the last to the first. `symE` (Fmt/M1Codes.lean) and `symA`
(FastCol.lean) do that step with `Fld.two.addE` and `Fld.two.scaleE`, which compute through natural
numbers. `loopW` does it with `addF` and `mulF` (OnBytes/Field/Word.lean) and carries the three
words of acc as three arguments, so that a step builds no triple.

Each definition repeats one that exists, and ColWLaw.lean proves the two equal, as functions, for
all arguments and without hypothesis:
- `hornerW` repeats `hornerA` (FastCol.lean), and so `hornerE` (Fmt/M1Codes.lean) (`hornerW_eq`).
- `symW` at `rowArr` repeats `symE` (`symW_eq`).
- `colAtW` at `colPrep` repeats `colOf` (Fmt/M1Own.lean) (`colW_eq`); `colTreeW` is the pair of a
  stage's depth and that column function (`colTreeW_eq`).
- `treeW`, which is `treeAtW` at `treePrep`, repeats `treeBy` (RunRows.lean) (`treeW_eq`).

How to call it. `colTreeW` and `treeW` return a pair. The arrays are built when the pair is built,
and its column function keeps them. Bind the pair once and read its column function at each
position. The arrays themselves come from `colPrep` and `treePrep` (FastCol.lean).

Limits.
- A second text, for speed. `Seams.fast` (FastW.lean) calls `colTreeW`: theorems on a run are stated
  at `Seams.lib`, which has `colOf`, and reach `Seams.fast` by `fast_eq` (FastWLaw.lean).
  `RunIn.ofRun` (RunJob.lean) calls `treeW`, at every `Seams`, `Seams.lib` too: the theorems on
  `RunIn.ofRun` (`runJob_in`, `runJob_eq`, RunJobLaw.lean, and what rests on them) are stated with
  `treeW` inside, and their proof goes to `treeBy` by the theorem `treeW_eq`, not by unfolding.
- It computes with random values too: the rows' tails and the mask rows stand in the arrays. It
  keeps its originals' defaults, without a warning: a chosen row whose number is out of range counts
  as the element 0, as in `treeBy`. `loopW` reads its array with the default 0; called from
  `hornerW` it stays below the array's size, so that default is never taken.
- At `Fld.two` only, as `symE`.
- `point` (Fmt/M1Codes.lean), which is called once for each row and position, is used as it is.
- Nothing is measured here.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FastCol

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Code Stage point cp)
open Fmt.M1.Own (PSt words)
open OnBytes (addF mulF)

/-! ## 1 One row -/

/-- The steps for the coefficients number i - 1 down to 0. a0, a1, a2: the three words of the value
so far. -/
def loopW (z : UInt64) (A : Array E) : Nat → UInt64 → UInt64 → UInt64 → E
  | 0, a0, a1, a2 => (a0, a1, a2)
  | i + 1, a0, a1, a2 =>
    let c := A.getD i Fld.zeroE
    loopW z A i (addF c.1 (mulF z a0)) (addF c.2.1 (mulF z a1)) (addF c.2.2 (mulF z a2))

/-- c_0 + c_1 z + c_2 z ^ 2 + ..., for the coefficients in A. -/
def hornerW (z : UInt64) (A : Array E) : E := loopW z A A.size 0 0 0

/-- The symbol at position x of the row with the coefficients A. -/
def symW (C : Code) (x : Nat) (A : Array E) : E := hornerW (point C.a x) A

/-- The symbols at position x of the rows with the coefficients As. -/
def symsW (C : Code) (x : Nat) (As : List (Array E)) : List E := As.map (symW C x)

/-! ## 2 The column of a stage's tree -/

/-- The column at position x. first and last are those of `colOf`. -/
def colAtW (s : Stage) (first last : Bool) (D : ColData) (x : Nat) : List UInt64 :=
  if last then
    ((symsW s.C x D.main ++ symsW s.C x D.word0) ++
      (symsW s.Z (cp s.Z x) D.mask ++ symsW s.Z (cp s.Z x) D.word1)).flatMap words
  else
    (if first then ((symsW s.C x D.main).take 3).map (·.1)
        else (symsW s.C x D.main).flatMap words) ++
      (symsW s.Z (cp s.Z x) D.mask ++ symsW s.Z (cp s.Z x) D.fresh).flatMap words

/-- The tree that a code switch sends: the new stage's depth, and its column function. -/
def colTreeW (s : Stage) (last : Bool) (p : PSt) : Tree :=
  (s.C.a, colAtW s false last (colPrep s p))

/-! ## 3 A tree given as a list of chosen rows -/

/-- The chosen row's symbol at position x; three words 0 for a row number out of range. -/
def rowSymW (s : Stage) (x : Nat) (d : RowData) : E :=
  match d.arr with
  | none => Fld.zeroE
  | some A => if d.main then symW s.C x A else symW s.Z (cp s.Z x) A

/-- The column at position x: the chosen rows' symbols, one after the other, as words. -/
def treeAtW (D : TreeData) (x : Nat) : List UInt64 :=
  D.rows.flatMap fun d => if d.base then [(rowSymW D.s x d).1] else words (rowSymW D.s x d)

/-- A tree, built from T as by `treeBy`. -/
def treeW (s : Stage) (T : Nat × List Sel) (p : PSt) : Tree := (T.1, treeAtW (treePrep s T p))

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.loopW
#print axioms ProofFile.Honest.K12.Light.hornerW
#print axioms ProofFile.Honest.K12.Light.symW
#print axioms ProofFile.Honest.K12.Light.symsW
#print axioms ProofFile.Honest.K12.Light.colAtW
#print axioms ProofFile.Honest.K12.Light.colTreeW
#print axioms ProofFile.Honest.K12.Light.rowSymW
#print axioms ProofFile.Honest.K12.Light.treeAtW
#print axioms ProofFile.Honest.K12.Light.treeW
