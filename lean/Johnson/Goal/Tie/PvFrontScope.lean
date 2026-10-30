-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/PvFrontScope.lean: THE GOALS' OWN SCOPE TEST (VerifierAndGoals.InScope,
  Ladder.lean:306) AS THE FIRST ROW OF THE FULL-SIZE FRONT. It stands in the goals' verify()
  itself
(verify := verifyAt InScope, Ladder.lean:403-417). It pins the parameter file byte for byte but for
  eight numbers, and the layout file: so «sec 128», «sh 8», «sT 4» among others.
THE GOALS' SCOPE IS THE FULL SIZE's ALONE: at the small stored sets it says false.


-/
import Ladder
set_option autoImplicit false
namespace PV.Front

/-- The goals' own scope test, at three public files as bytes. -/
def scopeB (pol lay KL : ByteArray) : Bool := VerifierAndGoals.InScope ⟨pol, lay, KL⟩

/-- One line of a text file turned: none unless the old line stands exactly once (not as the first
  line). -/
def turnLine (b : ByteArray) (old new : String) : Option ByteArray :=
  match String.fromUTF8? b with
  | none => none
  | some s =>
    if (s.splitOn ("\n" ++ old ++ "\n")).length = 2 then
      some (s.replace ("\n" ++ old ++ "\n") ("\n" ++ new ++ "\n")).toUTF8
    else none

end PV.Front
