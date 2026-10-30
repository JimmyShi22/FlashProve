-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysIdnWRun.lean: the theorems of Johnson/Road/FormsKeysIdnW.lean on the lines of
a norm and on the selectors' sums, evaluated on made-up numbers.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem: nothing that only a guard
shows can be used in a proof, and it speaks of these numbers alone. This file holds no theorem.

What is evaluated. The made-up shape hR8 with the calls pcR8, in both groups of layers, at the sizes
dimP hR8 = dimV hR8 16 and the table of scales sclOf of the made-up scale file; the environment, the
points and the made-up world of Johnson/Road/FormsKeysRunP.lean (withP): every cell is a made-up
number, and every entry of the reads holds what a true table holds of these cells, at the norms'
points too. On the verifier's side: its own row5At, ledCarry5, ledLines5, epsOf, twoM, shA and
sumForms, as they stand; a form is valued by evalP, which gives every slot the value 0. On the
library's side: its own idnVal, Wsum, prods and ext, through idnAt, wHat and pHat of
FormsKeysIdnW.lean, over the integers modulo the verifier's prime.

The marks, for each group.
 1. The verifier makes the row of every norm at the points named P_V and r_tV, and the sum of the
    selector's entries of every routed layer: the hypotheses "returns" of the theorems.
 2. (T-carry): all nine lines of all norms, with 0 under the slot.
 3. (T-line): all eight lines of all norms, with 0 under the seven slots.
 4. (T-shown): the four numbers of every norm's row at r_tV.
 5. (T-hot): every routed layer.
 6. A control: with the library's identity of the next norm in the place of the norm's own, mark 2
    fails.
 7. Some identity's extension is not 0: the made-up cells meet no identity, so the equations
    compared are not 0 = 0.

What is not run: any slot with a value other than 0; the tables from Holds (a theorem:
trueAt3_of_holds); any other shape. The program does not import this file.
-/
import Johnson.Road.FormsKeysIdnW
import Johnson.Road.FormsKeysRunP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Aff ledCarry5 ledLines5)
open OnBytes.Model.Layer (sumForms epsOf twoM)
open Inst.Model (Scl)
open Inst.Model.FFSeg (idnVal led)

/-- A point of the verifier's, read in KP. -/
def ptIW (z : Array E) : ℕ → KP := fun j => valF (z.getD j zeroE)

/-- True if the form's value in the made-up world lies in the base field and reads as x. -/
def isP (r : RunP) (a : Aff) (x : KP) : Bool := inBase (evalP r a) && valF (evalP r a) == x

/-- The marks, in one group. shift: 0; 1 for the control. -/
def idnWB (r : RunP) : List Bool :=
  let y := r.v.y
  let S : Scl := sclOf hR8 r.v.sc r.v.g y.Lam
  let D := dimP hR8
  let t := cellsP D
  let uP := ptIW r.H.PV
  let uR := ptIW r.H.tV.r
  let uz := ptIW r.H.ztF
  let hot (lm : ℕ) := sumForms y.h.NE fun e => (r.v.shA "sel" "zt" lm e).map fun a => (a, oneE)
  let carries (shift : ℕ) : Bool := (List.range y.NI).all fun ν =>
    match r.v.row5At "P_V" ν with
    | some row => (List.range 9).all fun s =>
      isP r (ledCarry5 row s (Aff.slot 0))
        (idnAt (scl := S) D t (ν + shift) uP s + (0 - wHat D t ν uP s))
    | none => false
  [(List.range y.NI).all (fun ν =>
      (r.v.row5At "P_V" ν).isSome && (r.v.row5At "r_tV" ν).isSome) &&
      (List.range y.LamM).all fun lm => (hot lm).isSome,
   carries 0,
   (List.range y.NI).all fun ν =>
    match r.v.row5At "P_V" ν with
    | some row => (List.range 8).all fun k =>
      isP r ((ledLines5 row ((Array.range 7).map fun x => Aff.slot (0 + x)) (epsOf y ν)
          (twoM r.v ν)).toList.getD k {})
        (idnAt (scl := S) D t ν uP (9 + k) +
          Hd.slack (fun _ => 0) (fun x => 0 - pHat D t ν uP x) (9 + k))
    | none => false,
   (List.range y.NI).all fun ν =>
    match r.v.row5At "r_tV" ν with
    | some row =>
      isP r row.a (Blocks.ext D.lT (fun i => Inst.Model.Ledger.sa (led t ν i)) uR) &&
      isP r row.b (Blocks.ext D.lT (fun i => Inst.Model.Ledger.sb (led t ν i)) uR) &&
      isP r row.Rlo (Blocks.ext D.lT (fun i => Inst.Model.Ledger.Rlo (led t ν i)) uR) &&
      isP r row.Rhi (Blocks.ext D.lT (fun i => Inst.Model.Ledger.Rhi (led t ν i)) uR)
    | none => false,
   (List.range y.LamM).all fun lm =>
    match hot lm with
    | some s => isP r (Aff.ofConst (negE oneE) + s)
        (Blocks.ext D.lT
          (fun i => idnVal (scl := S) D t (fun _ _ => 0) (fun _ => 0) (.j10 lm i)) uz)
    | none => false,
   !carries 1,
   (List.range y.NI).any fun ν => (List.range 17).any fun k => idnAt (scl := S) D t ν uP k != 0]

/- all marks, in both groups of layers -/
#guard withP false hR8 pcR8 idnWB == List.replicate 2 (List.replicate 7 true)

end OnBytes.Road
