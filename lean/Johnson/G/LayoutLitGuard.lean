-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/LayoutLitGuard.lean: one test at the build: Lean's evaluator computes all that follows
from the full size's three shipped public files by the program `verify-on-bytes`'s own routine
(`planned`, OnBytes/Model/Verify.lean, at Johnson/G/KitFull.lean) and holds the layout of a
request's arrays in the first chain's parameters, as read back, whole, against the written layout
(`layoutFull`, Johnson/G/LayoutLit.lean). In the pattern of Johnson/G/SendsWrittenGuard.lean.

  `layoutOk K`: the routine has returned, and the field is the written value, by the types' own
    decidable equality.
  One «#guard»: `layoutOk` at these files. A pure value: nothing is read or printed.

What it adds. The written layout was laid off one print, made on another road (the public part of
the IOP as written in Lean). Here the evaluator makes the field anew in every build: a second
evaluation. The two roads are not independent: that road's planner is a copy of the library's text,
changed in a few lines (Johnson/Desc/ProofFile/PlanPlain.lean, whose head also tells how far
equations between copy and library are proved). So a yes shows that the program that laid the
written value did not slip, and that copy and library agree in this field at these files; an error
in the shared text stands on both roads.

Can it say no. By its make: `layoutOk` says no at an error, and `decide` of an equation says yes
only where the two values are equal. The same comparison says no at the written layout with one
number of one rectangle raised by 1 (`no_layout`, Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean). No
value at which the guard says no is shown in this file.

Limits. An evaluator's answer, no theorem. At these three files alone, as Johnson/G/KitFull.lean
holds them: that the typed values are files of the repository is not tested here.
Nothing on soundness.
-/
import Johnson.G.LayoutLit
import Johnson.G.KitFull
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

/-- The routine has returned, and the layout in the first chain's parameters is the written one. -/
def layoutOk (K : Except String OnBytes.Model.Verify.Planned) : Bool :=
  match K with
  | .ok p => decide (p.chains.proof.first.layout = layoutFull)
  | .error _ => false

#guard layoutOk
  (OnBytes.Model.Verify.planned KitFull.policy.toUTF8 KitFull.scales (some KitFull.layout.toUTF8))

end Johnson.G
