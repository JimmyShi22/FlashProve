-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPansRun.lean: a run: the hypotheses of the theorems on the order of the
verifier's panels hold together at a made-up shape.

Johnson/Road/FormsKeysPans.lean shows that the verifier's list of panels is the library's list pans,
member by member and in order (panels_of_lines, placed_are_pans). This file evaluates what these
theorems ask.

The line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and the
compilation fails if the value is not true. It is a run. It is no theorem, and it says nothing of
other numbers. This file holds no theorem.

What is run. withW of Johnson/Road/FormsKeysRunW.lean calls, at the shape hR8 with the eight lines
of calls pcR8 (Johnson/Road/FormsKeysRun8.lean), in every group of layers, the verifier's own
functions: layout, readsOf, the numbers of the calls with terms in the second token sumcheck as the
check of a layer sub-proof finds them (the names of readsOf, each looked up by callNo), panelsA and
panelsT, weightClaims. The panels and the claims are made from one environment there. It is false if
one of them does not return. On what they return, the guard evaluates: there are routed experts; the
layers with routed experts are as many as in the library's sizes dimOf hR8; the eight lines are the
library's (LinesAre, as a test); the calls of the second walk are 0, 1, 2, 5; and, though the
theorems conclude it, that the calls of the first walk are 0, 1, 2.

What is not run: any other shape; the two public example files. The program does not import this
file.
-/
import Johnson.Road.FormsKeysPans
import Johnson.Road.FormsKeysRunW

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (callsAC)
open Inst.Model.FFSeg (fams)

#guard withW hR8 pcR8 6 fun r =>
  r.ce.v.y.h.p3 && r.ce.v.y.LamM == (dimOf hR8).ne &&
    (r.ce.v.y.calls.toList.map fun cd => cd.segs.map (·.name)) ==
      ((List.finRange 8).map fun cc => (fams cc).map segName) &&
    r.TS == [0, 1, 2, 5] && callsAC r.ce.v.y == [0, 1, 2]

end OnBytes.Road
