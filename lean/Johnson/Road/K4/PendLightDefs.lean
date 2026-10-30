-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PendLightDefs.lean: A TEST ON THE PLAN THAT WALKS NO ARRAY, IN THE PLACE OF
"wsPending returns at the plan's leaving" (`rowB`, Johnson/Road/K4/Total/PlanRowDefs.lean).
DEFINITIONS ALONE: eight. The laws: Johnson/Road/K4/PendLight.lean: not imported here.

  `tabLen G` · `gamLen u`: how many coefficients the claim at zeros has on a group and on a unit,
    from the group's and the unit's numbers.
  `blockLens` · `coverB`: the lengths of the aligned blocks into which a stretch of rows is cut
    (`blockBits`, OnBytes/Iop/Lin.lean); they sum to the stretch's length.
  `spanFrom`: the first row of the units and the row after their last. `unitOkB`: one unit.
  **`pendB lay uis n S`**: every unit is in the layout · the layout's rows are the shape's · the
    units are n, and not none · first < last ≤ m0 ≤ 2 ^ kRow, kRow ≤ 62 · at each unit the
    coefficients are as many as its rows, and its rows end at last or before · the blocks cover the
    stretch.
  **`rowLightB P g n lin`**: pendB at the plan's own layout and units.

Limits. IT RUNS NEITHER wsPending NOR ANY ROUTINE THAT READS A MESSAGE: arithmetic on the layout's
units. Nothing on soundness.
-/
import Johnson.Road.K4.Total.PlanRowDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Pend

open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub)
open OnBytes.Params (LinShape)
open OnBytes.Desc.First.K4.Total (zeroFac unitsOf)

/-- The length of the table of the factor at zeros. -/
def tabLen (G : WsGrp) : Nat :=
  if G.cls == 'E' then G.o * 2 ^ ((zeroFac G).onRows G).pl.size
  else if G.aTaken then 1 else G.R

/-- The number of the coefficients of the claim at zeros on a unit. -/
def gamLen (u : WsUnit) : Nat := u.g.reverse.foldl (fun n G => n * tabLen G) u.nlw

/-- The lengths of the blocks of the stretch from row start on, at most fuel of them. -/
def blockLens (kRow firstRow size : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, start =>
    if firstRow + size ≤ start then []
    else 2 ^ blockBits kRow start (firstRow + size) kRow 0 ::
      blockLens kRow firstRow size fuel
        (start + 2 ^ blockBits kRow start (firstRow + size) kRow 0)

/-- The blocks' lengths sum to the stretch's. -/
def coverB (kRow firstRow size : Nat) : Bool :=
  (blockLens kRow firstRow size (2 * kRow + 2) firstRow).sum == size

/-- The first row of the units, and the row after their last; nothing at a unit that the layout
lacks. -/
def spanFrom (lay : WsLay) : List Nat → Nat × Nat → Option (Nat × Nat)
  | [], r => some r
  | ui :: l, r =>
    ((lay.U[ui]?).map fun u => (min r.1 u.off, max r.2 (u.off + u.rows))).bind (spanFrom lay l)

/-- At one unit: it is in the layout; the coefficients are as many as its rows; its rows end at
last or before. -/
def unitOkB (lay : WsLay) (last ui : Nat) : Bool :=
  match lay.U[ui]? with
  | none => false
  | some u => gamLen u == u.rows && decide (u.off + u.rows ≤ last)

/-- **THE LIGHT TEST.** -/
def pendB (lay : WsLay) (uis : List Nat) (n : Nat) (S : LinShape) : Bool :=
  match spanFrom lay uis (2 ^ 64 - 1, 0) with
  | none => false
  | some fl =>
    lay.m0 == S.matrixRows && !uis.isEmpty && uis.length == n && decide (fl.1 < fl.2) &&
      decide (fl.2 ≤ lay.m0) && decide (S.kRow ≤ 62) && decide (lay.m0 ≤ 2 ^ S.kRow) &&
      uis.all (unitOkB lay fl.2) && coverB S.kRow fl.1 (fl.2 - fl.1)

/-- The light test, as one test on the plan. -/
def rowLightB (P : Pub) (g n : Nat) (lin : LinShape) : Bool :=
  match unitsOf P g with
  | none => false
  | some uis => pendB P.wsLay uis n lin

end OnBytes.Road.K4.Pend
