-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/AsksFirstTest.lean: A PIN ON THE LIST OF THE DOOR (Johnson/Desc/Key/Asks.lean).
This file writes out a list of one entry test and checks that it is a prefix of the door's list. It
imports the door alone; no namespace is opened, and every constant is written from the root.

Main names.
  asksAt1, asksAt1_prefix: this list, written out anew, is a prefix of the door's list: its test,
    taken out or moved, makes it fail, unless this file turns too.
  yes_at1: a yes of the door's list is a yes of this one.
  gives_at1: WHAT ITS TEST MEANS: a yes of the door's list gives that each of the seven
    strings of parameter bytes is shorter than 2 ^ 64 bytes: a weakening below that makes it fail.

Limits. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- One entry test, written out. -/
def asksAt1 (_X : _root_.OnBytes.Model.Verify.Public) (_lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made)
    (_F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi)
    (_D : _root_.OnBytes.Maker.WholeD) : _root_.List (_root_.String × _root_.Bool) :=
  [("a string of its parameter bytes has 2 ^ 64 bytes or more",
      _root_.VerifiableInference.Desc.Key.bytesFit m)]

/-- **The list `asksAt1` is a prefix of the door's list.** -/
theorem asksAt1_prefix (X : _root_.OnBytes.Model.Verify.Public) (lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made)
    (F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi)
    (D : _root_.OnBytes.Maker.WholeD) :
    _root_.VerifiableInference.Desc.Key.asksAt1 X lay m F D <+:
      _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D := by
  unfold _root_.VerifiableInference.Desc.Key.asksAt1 _root_.VerifiableInference.Desc.Key.lawsAsk
  simp

/-- A yes of the door's list is a yes of `asksAt1`. -/
theorem yes_at1 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made}
    {F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi}
    {D : _root_.OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D, t.2 = _root_.Bool.true) :
    ∀ t ∈ _root_.VerifiableInference.Desc.Key.asksAt1 X lay m F D, t.2 = _root_.Bool.true := by
  obtain ⟨l, hl⟩ := _root_.VerifiableInference.Desc.Key.asksAt1_prefix X lay m F D
  exact fun t ht => h t (hl ▸ _root_.List.mem_append_left l ht)

/-- **What the test of `asksAt1` means.** -/
theorem gives_at1 {X : _root_.OnBytes.Model.Verify.Public} {lay : _root_.ByteArray}
    {m : _root_.Johnson.G.OfPlan.Made}
    {F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi}
    {D : _root_.OnBytes.Maker.WholeD}
    (h : ∀ t ∈ _root_.VerifiableInference.Desc.Key.lawsAsk X lay m F D, t.2 = _root_.Bool.true) :
    ∀ n : _root_.OnBytes.Model.Verify.ChainName,
      (_root_.OnBytes.Model.Verify.Chains.bytes m.p.chains n).size < 2 ^ 64 := by
  intro n
  have h1 : _root_.VerifiableInference.Desc.Key.bytesFit m = _root_.Bool.true :=
    _root_.VerifiableInference.Desc.Key.yes_at1 h
      ("a string of its parameter bytes has 2 ^ 64 bytes or more",
        _root_.VerifiableInference.Desc.Key.bytesFit m) (_root_.List.mem_singleton.2 rfl)
  unfold _root_.VerifiableInference.Desc.Key.bytesFit
    _root_.VerifiableInference.Desc.Key.chainNames at h1
  exact _root_.of_decide_eq_true (_root_.List.all_eq_true.1 h1 n (by cases n <;> simp))

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.asksAt1_prefix
#print axioms VerifiableInference.Desc.Key.yes_at1
#print axioms VerifiableInference.Desc.Key.gives_at1
