-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/SlotPassesFirstTest.lean: A PIN ON THE PIECE ITSELF: where the
key file's piece (Johnson/Desc/Key/Slot.lean) is laid, the tests of `asksAt1` have said
yes, and what they mean holds, unless this file turns too. Compiled with the library. If the piece
came to ask a list without these tests, this file could not be proved.

Main names.
  laidOfMade_at1: where `keyDataAndDecisionOfPlannerAnswer X lay m` returns (D, r): at the description F that was made,
    every test of `asksAt1 X lay m F D` says yes.
  laidAt_bytes, laidFixed_bytes: where `keyDataAndDecisionAtDigest`, `keyDataAndDecisionAtFixedDigest` return: the maker has returned some m,
    and each of its seven strings of parameter bytes is shorter than 2 ^ 64 bytes.

Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.SlotIs
import Johnson.Desc.Key.AsksFirstTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- **Where the piece is laid, every test of `asksAt1` has said yes.** -/
theorem laidOfMade_at1 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made} {D : _root_.OnBytes.Maker.WholeD}
    {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionOfPlannerAnswer X lay m = .ok (D, r)) :
    ∃ F, _root_.VerifiableInference.Desc.Key.descriptionFromPlan m = .ok F ∧
      ∀ t ∈ _root_.VerifiableInference.Desc.Key.asksAt1 X lay m F D, t.2 = _root_.Bool.true := by
  obtain ⟨F, hF, -, ha⟩ := (_root_.VerifiableInference.Desc.Key.laidOfMade_iff X lay m D r).1 h
  exact ⟨F, hF, _root_.VerifiableInference.Desc.Key.yes_at1 ha⟩

/-- **Where the piece is laid at a digest, the seven strings are short.** -/
theorem laidAt_bytes {X : _root_.OnBytes.Model.Verify.Public} {lay cfg : _root_.ByteArray}
    {D : _root_.OnBytes.Maker.WholeD} {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtDigest X lay cfg = .ok (D, r)) :
    ∃ m, _root_.VerifiableInference.Desc.Key.madeAt X lay cfg = .ok m ∧
      ∀ n : _root_.OnBytes.Model.Verify.ChainName,
        (_root_.OnBytes.Model.Verify.Chains.bytes m.p.chains n).size < 2 ^ 64 := by
  obtain ⟨m, S, N, P, hm, -, -, -, -, -, -, -, ha, -, -⟩ :=
    _root_.VerifiableInference.Desc.Key.laidAt_is X lay cfg D r h
  exact ⟨m, hm, _root_.VerifiableInference.Desc.Key.gives_at1 ha⟩

/-- The same at the fixed digest. -/
theorem laidFixed_bytes {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {D : _root_.OnBytes.Maker.WholeD} {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest X lay = .ok (D, r)) :
    ∃ m, _root_.VerifiableInference.Desc.Key.madeAt X lay
        _root_.VerifiableInference.Desc.Key.fixedDigest = .ok m ∧
      ∀ n : _root_.OnBytes.Model.Verify.ChainName,
        (_root_.OnBytes.Model.Verify.Chains.bytes m.p.chains n).size < 2 ^ 64 :=
  _root_.VerifiableInference.Desc.Key.laidAt_bytes h

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.laidOfMade_at1
#print axioms VerifiableInference.Desc.Key.laidAt_bytes
#print axioms VerifiableInference.Desc.Key.laidFixed_bytes
