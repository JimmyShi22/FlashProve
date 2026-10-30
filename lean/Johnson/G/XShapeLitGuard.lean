-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/XShapeLitGuard.lean: one test at the build: Lean's evaluator reads the full size's three
shipped public files by the program `verify-on-bytes`'s own reader (`publicOf`,
OnBytes/Model/VerifyPublic.lean, at Johnson/G/KitFull.lean) and holds the shape part of what it
returns, whole, against the written value (`xShapeIs`, Johnson/Desc/Ok/PlanWritten/XShapeTest.lean;
`xShapeFull`, Johnson/G/XShapeLit.lean). In the pattern of Johnson/G/LayoutLitGuard.lean.

  `xShapeOk K`: the reader has returned, and the test says yes.
  One «#guard»: `xShapeOk` at these files. A pure value: nothing is read or printed.

What it adds. The written value was laid off one print, made on another road (the public part of the
IOP as written in Lean). Here the evaluator makes the projection anew in every build: a second
evaluation. The two roads are not independent: that road's reader, `publicOfO`, is a copy of
`publicOf`, line for line, with the hash as an argument (Johnson/Desc/Ok/PlanWritten/PublicAt.lean),
and at the second hash function the two are equal by a theorem (`publicOfO_older`,
Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean). So a yes shows that the program that laid the
written value did not slip, and that the reader still returns this projection at these files; an
error in the shared text stands on both roads.

Can it say no. By its make: `xShapeOk` says no at an error. That `xShapeIs` says yes just where the
projection is the written value is a theorem (`sameXShape_iff`, `xShape_of_is`, `xShape_no`,
Johnson/Desc/Ok/PlanWritten/XShapeLaws.lean), and the same file shows the comparison saying no at
two changed values (`no_tail`, `no_head`). No value at which this guard says no is shown in this
file.

Limits. An evaluator's answer, no theorem. At these three files alone, as Johnson/G/KitFull.lean
holds them: that the typed values are files of the repository is not tested here.
Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.XShapeTest
import Johnson.G.KitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

/-- The reader has returned, and the shape part of what it returned is the written one. -/
def xShapeOk (K : Except String OnBytes.Model.Verify.Public) : Bool :=
  match K with
  | .ok X => VerifiableInference.PlanWritten.xShapeIs X
  | .error _ => false

#guard xShapeOk
  (OnBytes.Model.Verify.publicOf KitFull.policy.toUTF8 KitFull.scales (some KitFull.layout.toUTF8))

end Johnson.G
