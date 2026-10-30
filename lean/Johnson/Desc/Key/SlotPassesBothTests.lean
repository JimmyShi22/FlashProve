-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/SlotPassesBothTests.lean: A PIN ON THE PIECE ITSELF: where the
key file's piece (Johnson/Desc/Key/Slot.lean) is laid, the tests of `asksAt2` have
said yes, unless this file turns too. It holds them by name: what they mean is AsksBothTests.lean's.

Main names.
  laidOfMade_at2: where `keyDataAndDecisionOfPlannerAnswer X lay m` returns (D, r): at the description F that was made,
    every test of `asksAt2 X lay m F D` says yes.
  laidAt_pinned, laidFixed_pinned: where `keyDataAndDecisionAtDigest`, `keyDataAndDecisionAtFixedDigest` return: the maker has returned some
    m, the description's maker some F whose data these are, and the written plan's test says yes at
    (m, F).

Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.SlotIs
import Johnson.Desc.Key.AsksBothTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- **Where the piece is laid, every test of `asksAt2` has said yes.** -/
theorem laidOfMade_at2 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made} {D : _root_.OnBytes.Maker.WholeD}
    {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionOfPlannerAnswer X lay m = .ok (D, r)) :
    ∃ F, _root_.VerifiableInference.Desc.Key.descriptionFromPlan m = .ok F ∧
      ∀ t ∈ _root_.VerifiableInference.Desc.Key.asksAt2 X lay m F D, t.2 = _root_.Bool.true := by
  obtain ⟨F, hF, -, ha⟩ := (_root_.VerifiableInference.Desc.Key.laidOfMade_iff X lay m D r).1 h
  exact ⟨F, hF, _root_.VerifiableInference.Desc.Key.yes_at2 ha⟩

/-- **Where the piece is laid at a digest, the written plan's test has said yes.** -/
theorem laidAt_pinned {X : _root_.OnBytes.Model.Verify.Public} {lay cfg : _root_.ByteArray}
    {D : _root_.OnBytes.Maker.WholeD} {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtDigest X lay cfg = .ok (D, r)) :
    ∃ m F, _root_.VerifiableInference.Desc.Key.madeAt X lay cfg = .ok m ∧
      _root_.VerifiableInference.Desc.Key.descriptionFromPlan m = .ok F ∧
      _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F = _root_.Bool.true ∧
      _root_.VerifiableInference.Desc.FileDescription.data F "key file" = .ok D := by
  unfold _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtDigest at h
  cases hm : _root_.VerifiableInference.Desc.Key.madeAt X lay cfg with
  | error e =>
    rw [hm] at h
    cases h
  | ok m =>
    rw [hm] at h
    obtain ⟨F, hF, hx, ha⟩ := (_root_.VerifiableInference.Desc.Key.laidOfMade_iff X lay m D r).1 h
    exact ⟨m, F, rfl, hF,
      _root_.VerifiableInference.Desc.Key.yes_at2 ha
        ("its rounds are not the written ones",
          _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F)
        (_root_.List.mem_cons_of_mem _ (_root_.List.mem_singleton.2 rfl)),
      ((_root_.VerifiableInference.Desc.Key.laidOfDesc_iff F D r).1 hx).2.2.2.1⟩

/-- The same at the fixed digest. -/
theorem laidFixed_pinned {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {D : _root_.OnBytes.Maker.WholeD} {r : _root_.VerifiableInference.Desc.Key.KeyRun}
    (h : _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest X lay = .ok (D, r)) :
    ∃ m F, _root_.VerifiableInference.Desc.Key.madeAt X lay
        _root_.VerifiableInference.Desc.Key.fixedDigest = .ok m ∧
      _root_.VerifiableInference.Desc.Key.descriptionFromPlan m = .ok F ∧
      _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F = _root_.Bool.true ∧
      _root_.VerifiableInference.Desc.FileDescription.data F "key file" = .ok D :=
  _root_.VerifiableInference.Desc.Key.laidAt_pinned h

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.laidOfMade_at2
#print axioms VerifiableInference.Desc.Key.laidAt_pinned
#print axioms VerifiableInference.Desc.Key.laidFixed_pinned
