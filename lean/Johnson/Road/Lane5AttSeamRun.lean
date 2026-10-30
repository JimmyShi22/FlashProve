-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttSeamRun.lean

The two public premises of linkOK_of_publicAt (Johnson/Road/Lane5AttSeamAt.lean) beside publicOf's
line hold of the record that publicOf returns on the parameter text linesKF and the scale words
scalesKF of Johnson/Road/FormsKeysRunK.lean: a run.

What a run is. A line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and
the build fails if it is false. It is no theorem.

What is run: the verifier's own "publicOf" on the bytes of the parameter text linesKF and the
scale words scalesKF of Johnson/Road/FormsKeysRunK.lean, with no layout file; no Lean code
compares them with files.
* Guard 1: it returns a record X; "Hd.PublicAt" holds of X.P; "attUsualK X" says true: at all twelve
  groups the usual call list, one shift, kFD = 16.
* Guard 2: the lines do hold the line that control 3 turns.
* Control 3: with the line "callA KR KR RM RD" turned to "callA KR KR RD RM" the test does not pass:
  publicOf refuses or attUsualK says false: the guard does not tell the two apart. The turned order
  is a case where, by the head of Johnson/Road/Lane5AttLaid.lean, the pieces lie the same: the
  control shows that the test is narrow, not that it catches a fault.
* Control 4: at the texts linesKS and scalesKS of the same file the test does not pass: publicOf
  refuses, PublicAt fails or attUsualK says false: the guard does not tell these apart.
No control turns kFD or a shift.

Not claimed: that "linesKF" and "scalesKF" are any files' contents (no Lean code compares them).
-/
import Johnson.Road.Lane5AttSeamAt
import Johnson.Road.FormsKeysRunK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.L5

open OnBytes.Model.Verify (publicOf)

/-- "Hd.PublicAt" and the test attUsualK, of the record that the verifier's "publicOf" returns on a
parameter file and a scale file, with no layout file; false where it refuses. -/
def attSeamK (pol KL : ByteArray) : Bool :=
  match publicOf pol KL none with
  | .ok X => decide (Hd.PublicAt X.P) && attUsualK X
  | .error _ => false

#guard attSeamK (textK linesKF) (wordsK scalesKF)
#guard linesKF.contains "callA KR KR RM RD"
#guard !attSeamK (textK (linesKF.map fun l =>
  if l == "callA KR KR RM RD" then "callA KR KR RD RM" else l)) (wordsK scalesKF)
#guard !attSeamK (textK linesKS) (wordsK scalesKS)

end OnBytes.Road.L5
