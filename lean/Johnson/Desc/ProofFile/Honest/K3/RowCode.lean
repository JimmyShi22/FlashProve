-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/RowCode.lean: a row of a lookup's joined table at a proof file's
lookup of shape h, computed from the shape's own numbers: two readings of the shape's array of
calls, one call of `Call.tauAt` (the row's number itself, or one entry of the call's stored table),
two numbers laid into elements, one `mulE` and one `addE`. One definition with code; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the joined table of a lookup of shape h has 2 ^ h.d
rows; row u belongs to call `FoNums.fT h u` and repeats a row of that call's own table; the shift
is the element theta that the verifier samples in the lookup's own first round ("LKP shift",
Honest/K3/Stages.lean).

What is defined.
  `Fast.rowCode h theta u`: (the call's table's row, a number) + (the call's number) * theta, on the
    program's elements. It is the library's closed form `Fo.tabF h`
    (OnBytes/Tie/Pv/Lookup/Forest/FoV.lean) with the program's `addE`, `mulE` and `ofNat` in the
    stead of the field's operations. Its body writes out the library's `FoNums.rowOf h u` (the call,
    the row) without calling it; `rowCode_up` (Honest/K3/FastLaw/RowCodeLaw.lean
    [not in this library]) ties the whole to `Fo.tabF`.

Why. `Fast.rowOfFace` (Honest/K3/JobsFast.lean) reads a row off the verifier's `Face.leaf` on a
corner, and at `faceOf h` that evaluates every call's table as a multilinear extension, for each row
anew.

Imported. The library's numbers of a lookup (OnBytes/Tie/Pv/Lookup/Port/FoNums.lean) and what stands
beneath it. Nothing of the frame.

Users. Honest/K3/FastLaw/RowCodeLaw.lean [not in this library] (the equations with `rowLib` and
`rowOfFace`); Honest/K3/RowCodeGuards.lean [not in this library] (tests);
Honest/K3/LotInstKeepCode.lean.

Limits. Nothing here says that this is the verifier's table: see Honest/K3/FastLaw/RowCodeLaw.lean
[not in this library]. From 2 ^ h.d on the function has values too; nothing is said of them. How
long a call takes is not said here.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Fast
open OnBytes (E addE mulE)
open OnBytes.Model (ofNat)

/-- **Row u of the joined table of a lookup of shape h, moved by its call's shift**: the call's
table's row plus the call's number times theta. -/
def rowCode (h : OnBytes.Model.Forest.Shape) (theta : E) (u : Nat) : E :=
  let c := FoNums.fT h u
  addE (ofNat (FoNums.tauN h c (u / 2 ^ h.cK % 2 ^ FoNums.kOf h c))) (mulE (ofNat c) theta)

end ProofFile.Honest.K3.Fast
