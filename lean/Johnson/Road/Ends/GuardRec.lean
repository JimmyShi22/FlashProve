-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/GuardRec.lean: a run of the test recordOneB (Johnson/Road/Ends/AlgBridgeOne.lean)
at the parameter text linesKF and the scale words scalesKF of Johnson/Road/FormsKeysRunK.lean, with
no layout file, in every group of layers. No Lean code compares linesKF and scalesKF with files.
Runs: X := what the verifier's publicOf returns on them; tablesB on X's layout, once (it does not
hang on the group); recordB X g for every group g of X: recordOneB X g is the two together. A
control: recordB at the number of groups (a group that is not there) is to be false. The control
turns the clause on g alone; ropeOK has controls in Johnson/Road/Ends/GuardRope.lean; tablesB has
none here; the other parts have none.
What is read: no weight, no proof, no request, no token.
It is a run, by Lean's interpreter, when the file is compiled: no theorem; usable in no proof;
nothing is said of other files.
-/
import Johnson.Road.FormsKeysRunK
import Johnson.Road.Ends.AlgBridgeOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Model.Verify (publicOf)

/-- The number of groups; tablesB; recordB in each group; recordB at the number of groups. -/
def recRun : Except String (ℕ × Bool × List Bool × Bool) :=
  match publicOf (textK linesKF) (wordsK scalesKF) none with
  | .ok X => .ok (X.y.NGr, tablesB X.layers.y, (List.range X.y.NGr).map (recordB X),
      recordB X X.y.NGr)
  | .error e => .error e

#guard (match recRun with
  | .ok (n, a, l, c) => n == 12 && a && l == List.replicate 12 true && !c
  | .error _ => false)

end OnBytes.Road.Alg
