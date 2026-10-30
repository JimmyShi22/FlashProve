-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPlaceCtl.lean: controls for the run of Johnson/Road/HeadPlaceRun.lean, and the
record FullH at the full-size example's shape.

A run that only ever says "true" shows little. Here the same functions are evaluated on numbers into
which a fault has been planted, and each must say "false". A line "#guard" is evaluated when this
file is compiled, by Lean's interpreter, and the compilation fails if the value is not true. It is a
run and no theorem.

The planted faults, each in what publicOf (OnBytes/Model/VerifyPublic.lean) returns at the files of
prover/examples/target_full_f2:
 1. the first features of the two tensors of the margins' digits exchanged in the layout: tensorsHP;
 2. the numbers of columns of hd and hr exchanged in the layout: cellsHP;
 3. one column more in a part of hf in the layout: cellsHP;
 4. hd and hr exchanged in the plan's list of matrices: orderHP and placesHP;
 5. no fault in the numbers, but the entries of a table taken run by run and then column by column:
    the order of the places.
Beside them, without a fault: the three numbers that meet in the stream's place. The head's list has
the borrowed stream under NHf + 3. The lender's list has it under the number iXO of matIx
(OnBytes/Model/LayerForms.lean). The library has it in slot 7 of segment 22 (Cm/SegLayout.lean). At
this example all three are 7. placesHP of Johnson/Road/HeadPlaceRun.lean compares the library's slot
with the first of them, the head's; that this is also the lender's number is a coincidence of the
example's sizes. The dictionary stackedH of Johnson/Road/HeadPlace.lean goes by the lender's number
(slotNo).

fullH_shapeHF is a theorem: the shape that Johnson/Road/HeadRunK.lean writes by hand from the lines
of the full-size example's parameter file has the nine numbers of FullH.

What is not claimed. A control shows that the function can tell this fault, no more. The program
does not import this file.
-/
import Johnson.Road.HeadPlaceRun
import Johnson.Road.HeadRunK

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (HFun HTailF2)
open OnBytes.Model.Verify (publicOf Public)
open OnBytes.Model.Head (Tables)

/-- The record FullH at the full-size example's shape. -/
theorem fullH_shapeHF : FullH shapeHF := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fault 1: the first features of the tensors d1 and d2 exchanged. -/
def fault1 (X : Public) : Public :=
  { X with HLy := { X.HLy with oD1 := X.HLy.oD2, oD2 := X.HLy.oD1 } }

/-- Fault 2: the columns of hd and hr exchanged in the layout. -/
def fault2 (X : Public) : Public :=
  { X with HLy := { X.HLy with kD := X.HLy.kR, kR := X.HLy.kD } }

/-- Fault 3: one column more in a part of hf. -/
def fault3 (X : Public) : Public := { X with HLy := { X.HLy with k := X.HLy.k + 1 } }

/-- Fault 4: hd and hr exchanged in the plan's list of matrices. -/
def fault4 (X : Public) : Public :=
  let ms := X.H.tl.mats
  let a := X.hS.NHf
  { X with H := { X.H with tl := { X.H.tl with
      mats := (ms.setIfInBounds a (ms.getD (a + 1) {})).setIfInBounds (a + 1) (ms.getD a {}) } } }

/-- The entries of a table, part by part, but run by run and then column by column. -/
def entriesSw (tl : HTailF2) (fns : List HFun) : List (Option ℕ) :=
  fns.flatMap fun Fn =>
    let M := tl.mats.getD Fn.mat {}
    (List.range (M.m / Fn.len)).flatMap fun sg =>
      (List.range M.k).map fun c => tl.tabAt Fn c sg

/-- Fault 5: whether, in that nesting, the places of the table hd@r_H are its entries in rising
order. -/
def order5 (X : Public) (t : Tables) : Bool :=
  (t.tab.filter fun e => e.1 == "hd@r_H").all fun (_, tb, len) =>
    entriesSw X.H.tl (partsHP t tb len) == (List.range len).map fun e => some (tb + e)

/-- The controls, and the three numbers of the stream. -/
def runCtl : Option (List Bool × ℕ × ℕ × ℕ) :=
  match publicOf (textK linesKF) (wordsK scalesKF) none with
  | .error _ => none
  | .ok X =>
    (tablesHP X).map fun t =>
      ([tensorsHP (fault1 X), cellsHP (fault2 X) t, cellsHP (fault3 X) t, (orderHP (fault4 X) t).1,
        placesHP (fault4 X) t, order5 X t],
        X.hS.NHf + 3, (Model.Layer.matIx X.y).iXO, slotNo X.y 7)

#guard runCtl == some ([false, false, false, false, false, false], 7, 7, 7)

#print axioms fullH_shapeHF

end OnBytes.Road.Hd
