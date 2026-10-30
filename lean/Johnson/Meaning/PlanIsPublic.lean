-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanIsPublic.lean: the public part X of which the row on the meaning speaks
(Johnson/Goal/Meaning/Row.lean) is the one that a description's own plan holds.

The row's letters are those of the record X that the function publicOf returns on the public files
(OnBytes/Model/VerifyPublic.lean). A description of the proof file makes its plan from the same
three files by madeOf (Johnson/G/RoundsOfPlan.lean). madeOf's first step is planned
(OnBytes/Model/Verify.lean), and planned's first step is publicOf.

One theorem: public_of_made: where madeOf returns m on policy.txt, layout.txt and KL.bin, publicOf
has returned m.p.X on the same files. So the row's premise "publicOf has returned X" holds at X :=
m.p.X wherever the description has a plan at all.

What is not claimed. That a block of a description reads its shapes off m.p.X and nowhere else.
-/
import Johnson.G.RoundsOfPlan

set_option autoImplicit false

namespace Meaning

open OnBytes.Model.Verify (publicOf planned)

/-- A bind that returns has a first step that returns. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- What planned returns holds what publicOf has returned. -/
theorem public_of_planned {pol KL : ByteArray} {layout : Option ByteArray}
    {p : OnBytes.Model.Verify.Planned} (h : planned pol KL layout = .ok p) :
    publicOf pol KL layout = .ok p.X := by
  unfold planned at h
  obtain ⟨X, hX, h⟩ := bind_ok h
  obtain ⟨chains, _, h⟩ := bind_ok h
  obtain ⟨built, _, h⟩ := bind_ok h
  cases h
  exact hX

/-- **The plan's public part is publicOf's.** -/
theorem public_of_made {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made}
    (h : Johnson.G.OfPlan.madeOf pol lay KL = .ok m) : publicOf pol KL (some lay) = .ok m.p.X := by
  unfold Johnson.G.OfPlan.madeOf at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  obtain ⟨l, _, h⟩ := bind_ok h
  split at h
  · cases h
    exact public_of_planned hp
  · cases h

end Meaning

#print axioms Meaning.public_of_made
