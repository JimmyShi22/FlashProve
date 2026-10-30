-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5PublicRun.lean

The public hypothesis "Hd.PublicAt" (HeadL5Pub.lean) holds of the full-size example's parameter
file: a short run.

Why: several theorems of Lane5TopPub.lean, Lane5TopPol.lean, HeadL5Pub.lean and HeadL5All.lean
stand under "publicOf pol KL lay = .ok X" and "Hd.PublicAt X.P". That publicOf returns on these
bytes, with no layout file, is the guard of FormsKeysRunKFull.lean. This file shows by a run that
"Hd.PublicAt" is not empty, and that it holds of the X.P of the record that publicOf returns on
these bytes.

What a run is. A line "#guard" is evaluated when this file is compiled, by Lean's interpreter, and
the build fails if it is false. It is no theorem.

What is run: the verifier's own "polLayout" on the bytes of "linesKF" (FormsKeysRunK.lean: the
full-size example's parameter file, written out). "publicOf" takes its P from that very call, in
its first line, and returns it as the field P (OnBytes/Model/VerifyPublic.lean: by reading; guard 4
does not lean on that reading).
* Guard 1: "Hd.PublicAt" holds of that P: the 46 numbers are the reference's, and the lines gcl and
  rcl are there.
* Control 2: at the small example's parameter file ("linesKS") it does not hold.
* Control 3: at the full-size lines with "sh 8" turned to "sh 7" it does not hold. In both
  controls: it does not hold, or polLayout refuses: the guard does not tell the two apart.
* Guard 4: the verifier's own "publicOf" on the bytes of "linesKF" and of the scale words
  "scalesKF", with no layout file, returns a record X, and "Hd.PublicAt" holds of X.P.

Not claimed: that "linesKF" and "scalesKF" are the shipped files' contents (no Lean code compares
them); the other public hypotheses of the theorems named above.
-/
import Johnson.Road.HeadL5Pub
import Johnson.Road.FormsKeysRunK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.L5

open OnBytes.Model.Verify (polLayout publicOf)

/-- "Hd.PublicAt" of what the verifier's "polLayout" returns on a parameter file; false where it
refuses. -/
def publicAtK (pol : ByteArray) : Bool :=
  match polLayout pol with
  | .ok (P, _) => decide (Hd.PublicAt P)
  | .error _ => false

#guard publicAtK (textK linesKF)
#guard !publicAtK (textK linesKS)
#guard linesKF.contains "sh 8"
#guard !publicAtK (textK (linesKF.map fun l => if l == "sh 8" then "sh 7" else l))

/-- "Hd.PublicAt" of the field P of the record that the verifier's "publicOf" returns on a parameter
file and a scale file, with no layout file; false where it refuses. -/
def publicAtX (pol KL : ByteArray) : Bool :=
  match publicOf pol KL none with
  | .ok X => decide (Hd.PublicAt X.P)
  | .error _ => false

#guard publicAtX (textK linesKF) (wordsK scalesKF)

end OnBytes.Road.L5
