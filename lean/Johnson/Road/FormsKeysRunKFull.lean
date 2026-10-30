-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysRunKFull.lean: one guard of Johnson/Road/FormsKeysRunK.lean: the run at the
bytes that that file has typed for the full-size example's two files.

A run, no theorem. The guard evaluates runKF of that file on the bytes of linesKF and scalesKF, with
no layout file: publicOf returns, and what that file's head lists under points 5 to 9 and under "At
the full-size example besides" comes out as written here. What the functions compare, what is cut at
the full size, what is made up and what is not claimed: that file's head.

It stands apart from that file so that no module costs much over a minute of Lean's time; it costs
about a minute itself. The program does not import this file.

-/
import Johnson.Road.FormsKeysRunK

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (Seg CallD PolScan fileWords HTailF2)
open OnBytes.Model.Verify (polLayout publicOf layerShape Public)
open OnBytes.Model.Layer (Env Lay Shape Scales Reads layout scalesOf scalesHeld noWrap readsOf
  tableAsks layTables pointsOf funsOf tailsOf)
open Inst.Model (tbRef)
open Inst.Model (rotaryOff KLFile)
open Inst.Model.FFSeg (Dim Fam fams call ord len LawfulW nFeatMx afCols nCol lRow mZ)

/-! ## The run -/

/- the lighter run -/
#guard (match runKF (textK linesKF) (wordsK scalesKF) with
  | .ok r => r ==
    (List.replicate 48 true, true, true, (131072, 0, 0), (131072, 50734, 65218), keysK, true,
      List.replicate 8 (true, 0), List.replicate 8 true, List.replicate 12 (true, true, true, true),
      [(true, true, 10, 31), (true, true, 10, 30)])
  | .error _ => false)

end OnBytes.Road
