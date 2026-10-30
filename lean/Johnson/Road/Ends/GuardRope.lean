-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/GuardRope.lean: a run at the parameter text linesKF and the scale words scalesKF
of Johnson/Road/FormsKeysRunK.lean, with no layout file. No Lean code compares linesKF and scalesKF
with files.
Runs ropeOK (Johnson/Road/Ends/AlgRope.lean), the one Bool from which AgreeT follows, at the
library's reference tables tbRef and reference sizes Dim.ref, on what the verifier's publicOf
returns on them: in every group of layers g, at L0 := g * Lam.
Two controls, faults of the tables, each to be false in every group: the library's tables read one
layer further on (tbNext); cosines and sines swapped (tbSwap). Neither stands at the end of a range.
What is read: no weight, no proof, no request, no token.
It is a run, by Lean's interpreter, when the file is compiled: no theorem; it can be used in no
proof; nothing is said of other files.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.Ends.AlgRope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Model.Verify (publicOf)
open Inst.Model (tbRef)
open Inst.Model.FFSeg (Dim)

/-- A fault: the reference tables, their rotary entries read one layer further on. -/
def tbNext : Inst.Model.Tables :=
  { tbRef with C := fun L i j => tbRef.C (L + 1) i j, S := fun L i j => tbRef.S (L + 1) i j }

/-- A fault: the reference tables, cosines and sines swapped. -/
def tbSwap : Inst.Model.Tables := { tbRef with C := tbRef.S, S := tbRef.C }

/-- For each group: its number, ropeOK at the reference tables, and at the two faults. -/
def ropeRun : Except String (ℕ × ℕ × List (ℕ × Bool × Bool × Bool)) :=
  match publicOf (textK linesKF) (wordsK scalesKF) none with
  | .ok X =>
    .ok (X.layers.y.NGr, X.layers.y.Lam, (List.range X.layers.y.NGr).map fun g =>
      (g, ropeOK X.layers Dim.ref tbRef (g * X.layers.y.Lam),
        ropeOK X.layers Dim.ref tbNext (g * X.layers.y.Lam),
        ropeOK X.layers Dim.ref tbSwap (g * X.layers.y.Lam)))
  | .error e => .error e

#guard (match ropeRun with
  | .ok (n, lam, l) => n == 12 && lam == 4 && l.length == 12 &&
      l.all fun x => x.2.1 && !x.2.2.1 && !x.2.2.2
  | .error _ => false)

end OnBytes.Road.Alg
