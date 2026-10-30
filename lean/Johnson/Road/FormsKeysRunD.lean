-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunD.lean: the dictionary of cells of a feed-forward segment, evaluated on
made-up matrices at the layout of the full-size example.

Johnson/Road/FormsKeysDict.lean fills the library's one matrix of a segment from the verifier's list
of matrices (libM for one group, libOf for all groups). This file evaluates both sides of its
theorems at names of cells of every array.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof. This file holds no theorem.

How the library's side is computed. The library's own tM, ownFF, place, plFF, stack, slotFF and addr
(Cm/TargetSegFFAffPass.lean, Cm/SegLayout.lean, Inst/Model/FF/Index.lean) are evaluated as they
stand, at its reference sizes. No formula of the library is copied.

The numbers. The layout that the verifier's own polLayout returns for the lines of the full-size
example's parameter file (linesKF in Johnson/Road/FormsKeysRunK.lean). The groups 0, 1 and 11.
Made-up integer matrices with another number at every place (mzD). A list of 816 names (namesD): for
each of the 34 arrays of the matrices af, ad, ar, qa, xin, xout each of the four numbers of a name
at its least and its greatest value, the channel also in the middle. Where an array has one cell,
one instance or one channel a name stands in the list more than once.

What is run, and what is compared with what. All names are valid. Each comparison gives the list of
the library's matrices at whose names it fails.
 D1  tM g (libM y g Mz) against the verifier's cell in Mz: the conclusion of dict_valid.
 D2  tM g (libOf y Mz) against the verifier's cell in Mz g, at matrices in which the stream that
     comes into a group is not what went out of the group before.
 D3  the same at matrices in which it is (mzS): the conclusion of dict_all.
 The control, which must fail: D1 against the verifier's cells in matrices with ar and qa in each
 other's place (mzX).
What came out, and is held by the guard. D1 and D3 fail nowhere. D2 fails nowhere in group 0, and in
the groups 1 and 11 at the names of xin alone: there the library reads x8 of the group before. The
control fails at the names of ar and qa alone.

What stands between the two sides and is this file's own: mzD, mzS, mzX, namesD, failsD.

What is made up: the matrices. The lines of the parameter file are the shipped example's.

What is not claimed. Nothing is said of other names, groups or layouts. Both sides go through firstM
and mxNo: a wrong number there would not be seen. No proof is made or checked.
The program does not import this file.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.FormsKeysDict

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Verify (polLayout)
open OnBytes.Model.Layer (Lay)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Cell Arr Mx arrs)

/-! ## The made-up matrices and the names -/

/-- Made-up integer matrices of group g: another number at every place (numbers of matrices below
16, rows below 2^20, columns below 2^13). -/
def mzD (g : ℕ) : Mats ℤ := fun a r c => ((((g * 16 + a) * 2 ^ 20 + r) * 2 ^ 13 + c : ℕ) : ℤ)

/-- The same, but the matrix that comes into a later group holds what went out of the group
before. -/
def mzS (y : Lay) (g : ℕ) : Mats ℤ := fun a r c =>
  if a = firstM y 4 ∧ 0 < g then mzD (g - 1) (firstM y 5) r c else mzD g a r c

/-- mzD with the verifier's matrices ar and qa in each other's place. -/
def mzX (y : Lay) (g : ℕ) : Mats ℤ := fun a r c =>
  if a = firstM y 2 then mzD g (firstM y 3) r c
  else if a = firstM y 3 then mzD g (firstM y 2) r c else mzD g a r c

/-- Names of cells of every array of the six matrices: each of the four numbers at its least and
greatest value, the channel also in the middle. -/
def namesD : List Cell :=
  ([Mx.af, .ad, .ar, .qa, .xin, .xout].flatMap arrs).flatMap fun X =>
    [0, X.nCell - 1].flatMap fun k => [0, X.cnt DF - 1].flatMap fun n =>
      [0, X.width DF / 2, X.width DF - 1].flatMap fun j => [0, DF.T - 1].map fun i =>
        (⟨X, k, n, j, i⟩ : Cell)

/-- The matrices of the names at which a comparison fails, each once. -/
def failsD (f : Cell → Bool) : List Mx := ((namesD.filter fun c => !f c).map (·.X.mx)).eraseDups

/-! ## What is evaluated -/

/-- For the group g: all names are valid; D1: the matrices at which tM g (libM y g Mz) is not the
verifier's cell; D2: the same for libOf at matrices without the seam; D3: for libOf at matrices with
the seam; the control: D1 against the verifier's cells in matrices with ar and qa swapped. -/
def runD (y : Lay) (g : ℕ) : Bool × List Mx × List Mx × List Mx × List Mx :=
  (namesD.all fun c => decide (c.Valid DF),
    failsD fun c => Cm.Seg.TS.tM g (libM y g (mzD g)) c == cellsOf DF (cellsAt y (mzD g)) c,
    failsD fun c => Cm.Seg.TS.tM g (libOf y mzD) c == cellsOf DF (cellsAt y (mzD g)) c,
    failsD fun c => Cm.Seg.TS.tM g (libOf y (mzS y)) c == cellsOf DF (cellsAt y (mzS y g)) c,
    failsD fun c => Cm.Seg.TS.tM g (libM y g (mzD g)) c == cellsOf DF (cellsAt y (mzX y g)) c)

/-- The run at the lines of a parameter file, for the groups 0, 1 and 11; with the number of the
names. -/
def kitD (pol : ByteArray) :=
  match polLayout pol with
  | .ok x => some (namesD.length, [0, 1, 11].map (runD x.2))
  | .error _ => none

/-! ## The run -/

/- D1, D2, D3 and the control, for the groups 0, 1 and 11 -/
#guard kitD (textK linesKF) == some (816,
  [(true, [], [], [], [.ar, .qa]), (true, [], [.xin], [], [.ar, .qa]),
    (true, [], [.xin], [], [.ar, .qa])])

end OnBytes.Road
