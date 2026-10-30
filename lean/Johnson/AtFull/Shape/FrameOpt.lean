-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FrameOpt.lean: TWO SMALL TOOLS FOR THE SEATS IN THE FRAME's OWN FORM: most of
our steps on shapes return an Option; the frame's letters take an Except. Definitions with their
laws.

  `optE g`: the step g as the frame takes it; `optE_ok`: it returns u just where g does.
  `liftO g` := liftQ (optE g): a step on the chain's shape alone that may refuse, on the whole
    (FrameLift.lean); `liftO_ok`: it returns y just where g returns some u at the first part and y
    is u with the makes as they were.

Limits. Tools alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape

/-- A step that may refuse, as the frame's letters take it. -/
def optE {α β : Type} (g : α → Option β) (a : α) : Except String β :=
  match g a with
  | some u => .ok u
  | none => .error "the step on shapes refuses"

theorem optE_ok {α β : Type} {g : α → Option β} {a : α} {u : β} :
    optE g a = .ok u ↔ g a = some u := by
  unfold optE
  cases g a with
  | none => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩
  | some v => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩

/-- A step on the chain's shape alone that may refuse, on the whole. -/
def liftO (g : ChainSh → Option ChainSh) : ShA → Except String ShA := liftQ (optE g)

theorem liftO_ok {g : ChainSh → Option ChainSh} {x y : ShA} :
    liftO g x = .ok y ↔ ∃ u, g x.1 = some u ∧ y = (u, x.2) := by
  unfold liftO liftQ
  cases h : g x.1 with
  | none =>
    rw [show optE g x.1 = .error "the step on shapes refuses" from by unfold optE; rw [h]]
    exact ⟨fun e => (by cases e), fun ⟨_, e, _⟩ => (by cases e)⟩
  | some v =>
    rw [optE_ok.2 h]
    exact ⟨fun e => (by cases e; exact ⟨v, rfl, rfl⟩), fun ⟨u, e, e'⟩ => (by cases e; rw [e']; rfl)⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.optE_ok
#print axioms Johnson.AtFull.Shape.liftO_ok
#print axioms Johnson.AtFull.Shape.optE
#print axioms Johnson.AtFull.Shape.liftO
