-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/AsksBothTests.lean: A PIN ON THE LIST OF THE DOOR (Johnson/Desc/Key/Asks.lean).
This file writes out a list of two entry tests and checks that it is a prefix of the door's list. It
imports the door alone; no namespace is opened, and every constant is written from the root.

Main names.
  asksAt2, asksAt2_prefix: this list, written out anew, is a prefix of the door's list: one of
    these that is taken out or moved makes it fail, unless this file turns too.
  yes_at2: a yes of the door's list is a yes of this one.
  gives_at2: WHAT ITS SECOND TEST MEANS: a yes of the door's list gives: if the key off the
    parameter file's scan that m holds is the full size's, then the description's rounds, written
    out, are the written ones of the full size's key file, and the depth of its table is 32.

Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- Two entry tests, written out. -/
def asksAt2 (_X : _root_.OnBytes.Model.Verify.Public) (_lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made)
    (F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi)
    (_D : _root_.OnBytes.Maker.WholeD) : _root_.List (_root_.String × _root_.Bool) :=
  [("a string of its parameter bytes has 2 ^ 64 bytes or more",
      _root_.VerifiableInference.Desc.Key.bytesFit m),
   ("its rounds are not the written ones",
      _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F)]

/-- **The list `asksAt2` is a prefix of the door's list.** -/
theorem asksAt2_prefix (X : _root_.OnBytes.Model.Verify.Public) (lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made)
    (F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi)
    (D : _root_.OnBytes.Maker.WholeD) :
    _root_.VerifiableInference.Desc.Key.asksAt2 X lay m F D <+:
      _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D := by
  unfold _root_.VerifiableInference.Desc.Key.asksAt2 _root_.VerifiableInference.Desc.Key.lawsAsk
  simp

/-- A yes of the door's list is a yes of `asksAt2`. -/
theorem yes_at2 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made}
    {F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi}
    {D : _root_.OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D, t.2 = _root_.Bool.true) :
    ∀ t ∈ _root_.VerifiableInference.Desc.Key.asksAt2 X lay m F D, t.2 = _root_.Bool.true := by
  obtain ⟨l, hl⟩ := _root_.VerifiableInference.Desc.Key.asksAt2_prefix X lay m F D
  exact fun t ht => h t (hl ▸ _root_.List.mem_append_left l ht)

/-- **What the second test of `asksAt2` means.** -/
theorem gives_at2 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made}
    {F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi}
    {D : _root_.OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D, t.2 = _root_.Bool.true)
    (hk : (m.p.X.P.h.L, m.p.X.P.h.d, m.p.X.P.h.V) = ((48, 5120, 202048) : ℕ × ℕ × ℕ)) :
    _root_.Johnson.G.OfPlan.writtenOf "key file"
        (_root_.VerifiableInference.Desc.FileDescription.roundsDeclaredByBlocks F) = .ok _root_.Johnson.G.dryKeyFull ∧
      F.tableDepth = 32 := by
  have h1 : _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F = _root_.Bool.true :=
    _root_.VerifiableInference.Desc.Key.yes_at2 h
      ("its rounds are not the written ones",
        _root_.VerifiableInference.PlanWritten.pinnedKeyAt m F)
      (_root_.List.mem_cons_of_mem _ (_root_.List.mem_singleton.2 rfl))
  unfold _root_.VerifiableInference.PlanWritten.pinnedKeyAt
    _root_.VerifiableInference.PlanWritten.descPinnedKey
    _root_.VerifiableInference.PlanWritten.descPinned
    _root_.VerifiableInference.PlanWritten.declPinned at h1
  have hk' : _root_.VerifiableInference.PlanWritten.keyOf m =
      _root_.VerifiableInference.PlanWritten.fullKey := hk
  rw [if_pos hk'] at h1
  unfold _root_.VerifiableInference.PlanWritten.declIs at h1
  obtain ⟨h2, h3⟩ := _root_.Bool.and_eq_true_iff.1 h1
  refine ⟨?_, _root_.of_decide_eq_true h3⟩
  cases hw : _root_.Johnson.G.OfPlan.writtenOf "key file"
      (_root_.VerifiableInference.Desc.FileDescription.roundsDeclaredByBlocks F) with
  | error e =>
    rw [hw] at h2
    cases h2
  | ok x =>
    rw [hw] at h2
    exact _root_.congrArg _root_.Except.ok (_root_.of_decide_eq_true h2)

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.asksAt2_prefix
#print axioms VerifiableInference.Desc.Key.yes_at2
#print axioms VerifiableInference.Desc.Key.gives_at2
