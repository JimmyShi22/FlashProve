-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/XShapeTest.lean: a test with code: the shape part of what the program
`verify-on-bytes`'s reader makes of the public files (`xShapeOf`, XShape.lean) is
the written one (`xShapeFull`, Johnson/G/XShapeLit.lean), compared whole. Definitions alone.

Why the comparison is written out. Each place of the projection's tuples has an equality from Lean's
own library, but Lean does not find one for the whole nested tuple by itself, and a file beneath a
verifier's list of tests holds definitions alone. So the tuples are compared place by place. That no
place is left out is a theorem (`sameXShape_iff`, Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean).

Definitions.
  `sameCallV`, `sameCallVs`, `sameForestV`, `sameHeadV`: two views of a call, two lists of such, two
    views of a lookup's public numbers, of the head's plan, are the same. `sameTailV`, `sameTailO`,
    `sameTails`: two views of a segment's approximate range proof, the same where none may stand,
    two lists of such. `sameXShape`: two whole projections.
  `xShapeIs X`: `sameXShape` of the projection and the written value. Bare: it asks at every key;
    the verifier's list of tests asks it at the full size's key alone.

Limits. A yes says nothing of what the projection leaves out. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.XShape
import Johnson.G.XShapeLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Model

/-- Two views of a call are the same: the ten places. -/
def sameCallV (a b : CallView) : Bool :=
  decide (a.1 = b.1) && decide (a.2.1 = b.2.1) && decide (a.2.2.1 = b.2.2.1) &&
    decide (a.2.2.2.1 = b.2.2.2.1) && decide (a.2.2.2.2.1 = b.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.1 = b.2.2.2.2.2.1) && decide (a.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.2.2 = b.2.2.2.2.2.2.2.2.2)

/-- Two lists of views of calls are the same: as long, and one by one. -/
def sameCallVs : List CallView → List CallView → Bool
  | [], [] => true
  | a :: as, b :: bs => sameCallV a b && sameCallVs as bs
  | _, _ => false

/-- Two views of a lookup's public numbers are the same: the eleven places. -/
def sameForestV (a b : ForestView) : Bool :=
  sameCallVs a.1 b.1 && decide (a.2.1 = b.2.1) && decide (a.2.2.1 = b.2.2.1) &&
    decide (a.2.2.2.1 = b.2.2.2.1) && decide (a.2.2.2.2.1 = b.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.1 = b.2.2.2.2.2.1) && decide (a.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.2.2.1 = b.2.2.2.2.2.2.2.2.2.1) &&
    decide (a.2.2.2.2.2.2.2.2.2.2 = b.2.2.2.2.2.2.2.2.2.2)

/-- Two views of the head's plan are the same: the seven places. -/
def sameHeadV (a b : HeadView) : Bool :=
  decide (a.1 = b.1) && decide (a.2.1 = b.2.1) && decide (a.2.2.1 = b.2.2.1) &&
    decide (a.2.2.2.1 = b.2.2.2.1) && sameCallV a.2.2.2.2.1 b.2.2.2.2.1 &&
    sameCallV a.2.2.2.2.2.1 b.2.2.2.2.2.1 && sameForestV a.2.2.2.2.2.2 b.2.2.2.2.2.2

/-- Two views of a segment's approximate range proof are the same: the three places. -/
def sameTailV (a b : TailView) : Bool :=
  decide (a.1 = b.1) && decide (a.2.1 = b.2.1) && decide (a.2.2 = b.2.2)

/-- The same where none may stand. -/
def sameTailO : Option TailView → Option TailView → Bool
  | none, none => true
  | some a, some b => sameTailV a b
  | _, _ => false

/-- Two lists of such are the same: as long, and one by one. -/
def sameTails : List (Option TailView) → List (Option TailView) → Bool
  | [], [] => true
  | a :: as, b :: bs => sameTailO a b && sameTails as bs
  | _, _ => false

/-- Two projections are the same. -/
def sameXShape (a b : XShape) : Bool := sameTails a.1 b.1 && sameHeadV a.2 b.2

/-- **The shape part is the written one.** Bare: it asks at every key. -/
def xShapeIs (X : Verify.Public) : Bool := sameXShape (xShapeOf X) Johnson.G.xShapeFull

end VerifiableInference.PlanWritten
