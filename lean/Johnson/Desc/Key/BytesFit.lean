-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/BytesFit.lean: a test with code on what the planner has made: each of the seven
strings of parameter bytes is shorter than 2 ^ 64 bytes. Definitions only. It is the first test that
the door of the key file's piece lays (Johnson/Desc/Key/Asks.lean), whose rule holds it still.

Main names. chainNames: the seven chains' names. bytesFit m: the test.
Limits. No run can plant a no of it: no machine holds such a string. No theorem of it lies: a
string's length is unbounded in Lean. Its law is `bytesFit_iff` (Johnson/Desc/Key/AsksLaw.lean).
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Road

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- The seven chains' names. -/
def chainNames : _root_.List _root_.OnBytes.Model.Verify.ChainName :=
  [.keyOneTime, .keyShared, .keySecond, .link, .proofFirst, .proofShared, .proofSecond]

/-- Each of the seven strings of parameter bytes is shorter than 2 ^ 64 bytes. -/
def bytesFit (m : _root_.Johnson.G.OfPlan.Made) : _root_.Bool :=
  _root_.List.all _root_.VerifiableInference.Desc.Key.chainNames fun n =>
    _root_.Decidable.decide ((_root_.OnBytes.Model.Verify.Chains.bytes m.p.chains n).size < 2 ^ 64)

end VerifiableInference.Desc.Key
