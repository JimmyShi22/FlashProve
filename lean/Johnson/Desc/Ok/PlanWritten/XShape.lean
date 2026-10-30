-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/XShape.lean: the shape part of what the program `verify-on-bytes`'s
reader makes of the public files (`Verify.Public`, OnBytes/Model/VerifyPublic.lean), as far as named
tests on public data read it and no theorem gives it: a projection into plain numbers, truth values,
strings and lists. Definitions alone.

What it is for. That structure holds, by design, the eight free numbers of the parameter file, the
scales and public tables: it cannot be compared whole with a written value. Laws on the IOP as
written in Lean read of it lists and numbers that say how large things are and how they are named.
These are taken out here, so that a verifier's list of tests can hold them, whole, against one
written value (Johnson/Desc/Ok/PlanWritten/XShapeTest.lean).

Why tuples. The types of the structure's parts bear no decidable equality and no printer where they
are declared. A tuple of numbers, truth values, strings, options and lists has both from Lean's own
library: so the projection can be printed, and compared by `decide`, with no instance of ours.
`callView` and `forestView` take every field of their structures: so equal views give equal
structures (Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean).

Definitions.
  `callView c`, of a lookup's call (`Call`, OnBytes/Model/Frame.lean), its ten fields in their
    order: name, n, iota, k, kappa, fn, t0, tau, pub, heavy.
  `forestView s`, of a lookup's public numbers (`Forest.Shape`, OnBytes/Model/Forest.lean), its
    eleven fields in their order: the calls, dT, kT, NT, rK, NC, cK, iota, first, callOf, pub.
  `tailView t`, of the structure of one segment's approximate range proof (`HTailF2`,
    OnBytes/Model/Tail.lean): the number of its committed matrices (NM); for each matrix, in their
    order, its label (aId), rows (m) and columns (k) (`TMat`, Frame.lean); and the list that names
    each matrix's symbol array (gtTree), whole.
  `headView X`, of the head's plan (`X.H`, OnBytes/Model/HeadPlan.lean): nU; ns; and of its
    approximate range proof: funClosed, lidb, the two calls z1.call and z2.call, and f9.
  `xShapeOf X`: for each of the segments 0 to 24 `tailView` of the structure that stands there
    (`Look.tlAt`, Johnson/Desc/First/Look/Laid.lean; none where none stands); and `headView X`.

Limits. Whatever a test reads of the structure beyond these parts is not in the projection. 25
segments: the full size's number. Nothing on soundness.
-/
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model

/-- A call's ten fields. -/
abbrev CallView : Type :=
  String × Nat × Nat × Nat × Nat × Nat × Nat × Option (List UInt64) × List Nat ×
    List (List (Nat × Nat))

def callView (c : Call) : CallView :=
  (c.name, c.n, c.iota, c.k, c.kappa, c.fn, c.t0, c.tau.map (·.toList), c.pub.toList, c.heavy)

/-- The eleven fields of a lookup's public numbers. -/
abbrev ForestView : Type :=
  List CallView × Nat × Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × List Nat × List Nat

def forestView (s : Forest.Shape) : ForestView :=
  (s.calls.toList.map callView, s.dT, s.kT, s.NT, s.rK, s.NC, s.cK, s.iota.toList, s.first.toList,
    s.callOf.toList, s.pub.toList)

/-- Of one segment's approximate range proof: how many committed matrices; each one's label, rows
and columns; the list of the matrices' symbol arrays. -/
abbrev TailView : Type := Nat × List (Nat × Nat × Nat) × List Nat

def tailView (t : HTailF2) : TailView :=
  (t.NM, t.mats.toList.map fun x => (x.aId, x.m, x.k), t.gtTree.toList)

/-- Of the head's plan: nU, ns, funClosed, lidb, z1.call, z2.call, f9. -/
abbrev HeadView : Type := List Nat × Nat × Bool × Nat × CallView × CallView × ForestView

def headView (X : Verify.Public) : HeadView :=
  (X.H.nU.toList, X.H.ns, X.H.tl.funClosed, X.H.tl.lidb, callView X.H.tl.z1.call,
    callView X.H.tl.z2.call, forestView X.H.tl.f9)

/-- **The shape part**, in plain values. -/
abbrev XShape : Type := List (Option TailView) × HeadView

/-- **The projection.** -/
def xShapeOf (X : Verify.Public) : XShape :=
  ((List.range 25).map fun k => (Desc.First.Look.tlAt X k).map tailView, headView X)

end VerifiableInference.PlanWritten
