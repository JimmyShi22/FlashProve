-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/TestsB.lean: the conditions of the laws on what a row means, as tests that can be
run.

Definitions with code alone; this file stands over OnBytes/Iop/Ground.lean and nothing else, so that
a run can call it. That each test gives its condition is shown in Johnson/Desc/Means/TestsLaw.lean.

Main definitions: groupOkB, rowInB, maskReadyB, layoutEqB, addRowAt, combineAt.

What is not claimed. Nothing is proved here.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- No member twice, every member there, a mark for each member, each member's rows under the
group's codes. -/
def groupOkB (S : Statement) (G : Group) : Bool :=
  distinctNats G.members.toList &&
  (G.members.toList.all fun o => decide (o < S.oracles.size)) &&
  (G.kept.size == G.members.size) &&
  (G.members.toList.all fun o =>
    match S.oracles[o]? with
    | some x => (x.shape.mainRows == 0 || x.shape.code == G.code) &&
        (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode)
    | none => true)

/-- Each summand of the row is on a table that a member of the group has, and within it. -/
def rowInB (S : Statement) (G : Group) (row : Row) : Bool :=
  (row.terms.toList.all fun t => Blk.placeOk S G t.oracle t.part t.v.vars 0) &&
  (row.units.toList.all fun u =>
    Blk.placeOk S G u.oracle u.part (S.tableBits u.oracle u.part) u.index) &&
  (row.runs.toList.all fun w => decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
    Blk.placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
      (w.first + w.step * (w.coeffs.size - 1))) &&
  (row.forms.toList.all fun f =>
    Blk.placeOk S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
      f.c.fits (S.tableBits f.oracle .main))

/-- The mask table of a group's row is not yet written out, or has its full length. -/
def maskReadyB (L : GroupLayout) (acc : GroupRow) : Bool :=
  acc.d.isEmpty || acc.d.size == 2 ^ (L.h + L.logEllZk)

/-- Two layouts are the same. -/
def layoutEqB (a b : GroupLayout) : Bool :=
  a.k == b.k && a.h == b.h && a.logEll == b.logEll && a.logEllZk == b.logEllZk &&
    a.members == b.members && a.kept == b.kept && a.mainFirst == b.mainFirst &&
    a.maskFirst == b.maskFirst

/-- The conditions of the law of the laying, for a row that is added to group g and a group's row
acc to which it would be carried. -/
def layAt (S : Statement) (g : Nat) (row : Row) (acc : GroupRow) : Bool :=
  match S.groups[g]?, S.layout g with
  | some G, some L => groupOkB S G && rowInB S G row && maskReadyB L acc
  | _, _ => false

/-- The same from a group's row without coefficients: for the place where a row is added. -/
def addRowAt (S : Statement) (g : Nat) (row : Row) : Bool := layAt S g row { group := g }

/-- The conditions of the law of the batching on group g, but for the rows: the group is there and
in order, and the layout handed in is the one that the statement gives. -/
def combineFrameAt (S : Statement) (g : Nat) (input : RunInput) : Bool :=
  match S.groups[g]?, S.layout g with
  | some G, some L => groupOkB S G && layoutEqB L input.layout
  | _, _ => false

/-- How many of the rows handed in pass rowInB. -/
def combineRowsAt (S : Statement) (g : Nat) (input : RunInput) : Nat :=
  match S.groups[g]? with
  | some G => (input.rows.toList.filter (rowInB S G)).length
  | none => 0

/-- All conditions of the law of the batching. -/
def combineAt (S : Statement) (g : Nat) (input : RunInput) : Bool :=
  combineFrameAt S g input && combineRowsAt S g input == input.rows.size

end OnBytes.Means
