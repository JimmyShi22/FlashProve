-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Asks.lean: THE DOOR: the tests that the key file's laws ask of its description and
of what it is made of: a list, each test with the words under which it refuses. The verifier's piece
for the key file (Johnson/Desc/Key/Slot.lean) asks every test of this list, once, behind the
description's own tests and its data, and refuses at the first that says no. ONE DEFINITION.

What belongs here: a premise of a law on the key file that is a test with code on the arguments
below, that none of the description's own tests asks, and that no theorem gives at all public files
in scope. A premise that a theorem gives there is a theorem, and does not belong here.

THE RULE: A TEST IS ONLY EVER APPENDED, AT THE END OF THE LIST. No test is taken out, weakened or
moved. So the verifier can only get stricter by a change of this file. THIS FILE DECLARES ONE NAME,
`lawsAsk`, and nothing else: no second definition, no instance, notation, macro or attribute: files
that import it rely on that, and nothing here may turn what their text means. A test's own
definition stands in a file of its own, with all that it imports.
What such a file declares beside the test no program of this repository checks.
How the rule is held:
  Johnson/Desc/Key/AsksFirstTest.lean, AsksBothTests.lean: a list, written out anew, is
    a prefix of the list here, and what a yes of each new test gives;
  Johnson/Desc/Key/SlotPassesFirstTest.lean, SlotPassesBothTests.lean: the same of the piece itself:
    where it is laid, those tests have said yes;
  Johnson/Desc/Key/AsksOnly.lean: by Lean's environment: this module declares `lawsAsk`
    alone, and `lawsAsk` is replaced by no other code when it is compiled;
  no program of this repository reads this file's text.
All pins are modules of the library: every build compiles them over this file as it stands.
Each test comes with: the law that takes it as a premise; a plant that it alone refuses, where one
can be made; the honest files' yes at both sizes, run again; a line here that says which law needs
it.

THE ARGUMENTS. What the program has read of the public files (X), the layout file, the planner's
answer with the sendings (m), the description (F) and its data (D). NO PARAMETER FILE: the piece is
handed none, and a second source beside X would be tied to it by nobody. A test that wants the
parameter file's scan reads it off X or m, which hold it (`X.P`): so the test that the description's
rounds are the written ones is laid in its form on (m, F) (`PlanWritten.pinnedKeyAt`).

THE TESTS
  1 "a string of its parameter bytes has 2 ^ 64 bytes or more": `bytesFit m`
  (Johnson/Desc/Key/BytesFit.lean). No run can plant a no of it. Needed by: the library's
  `chainsOf_at` (OnBytes/Tie/ChainsAtCfg.lean), and so by every law of
  Johnson/Desc/Key/NoCfgAt.lean and NoCfgLive.lean that follows the makers to another digest.
  2 "its rounds are not the written ones": `PlanWritten.pinnedKeyAt m F`
  (Johnson/Desc/Ok/PlanWritten/Test.lean): at the full size's key, read off the parameter file's
  scan that m holds, the description's rounds, written out, and the depth of its table are the
  written ones; at every other key: yes. Needed by: the key file's half of `SeatLaid`
  (Johnson/Goal/Numbers/PlanWrittenRow.lean): in scope the laid data are the written data.

-/
import Johnson.Desc.Key.BytesFit
import Johnson.Desc.BlockSlot
import Johnson.Desc.Ok.PlanWritten.Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- **The tests that the laws ask**: of what the program has read of the public files, the layout
file, the planner's answer with the sendings, the description and its data. -/
def lawsAsk (_X : _root_.OnBytes.Model.Verify.Public) (_lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made)
    (F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi)
    (_D : _root_.OnBytes.Maker.WholeD) : _root_.List (_root_.String × _root_.Bool) :=
  [("a string of its parameter bytes has 2 ^ 64 bytes or more",
      _root_.VerifiableInference.Desc.Key.bytesFit m),
   ("its rounds are not the written ones",
      _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F)]

end VerifiableInference.Desc.Key
