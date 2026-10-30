-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/Joining.lean: JOININGS IN A ROW (Send.joinAll,
Johnson/Desc/Sending/Send.lean) ON THE ONE SHAPE OF STATEMENT, BOOK AND ROOTS: the routine and its
step on the shape commute. General laws; nothing is evaluated.

The form. (f x).map sh = fSh (sh x): one equation says both that f returns just where the step on
the shape returns, and that the shape behind is the step's value. It can be had because a joining
tests no value.

  `sq_of`: from the two laws of a routine on shapes (it carries; it returns) to that equation.
  **`joinP_core`**: one joining: by Ground.Sh.join_carries and join_returns
    (Johnson/Desc/Ground/Shape/Ground.lean), whose step joinS is called, not written anew.
  `joinAllS`, **`joinAll_core`**: joinings in a row.

Limits. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Shape.Sending
import Johnson.Desc.Sending.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open _root_.Desc.Plain (DState GPar groundG)
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh joinS)

variable {L : Type}

/-- From the two laws of a routine on shapes to one equation. -/
theorem sq_of {α β : Type} (f : Option α) (sh : α → β) (g : Option β)
    (c : ∀ a, f = some a → g = some (sh a)) (r : ∀ y, g = some y → ∃ a, f = some a) :
    f.map sh = g := by
  cases hf : f with
  | some a => exact (c a hf).symm
  | none =>
    cases hg : g with
    | none => rfl
    | some y =>
      obtain ⟨a, ha⟩ := r y hg
      rw [hf] at ha
      cases ha

/-- **The joining and its step on the core commute.** -/
theorem joinP_core (d : DState L) (g o : Nat) (kept : Bool) :
    (Ground.joinP d g o kept).map (fun d' => coreSh (coreOf d')) =
      joinS (coreSh (coreOf d)) g o kept :=
  sq_of _ _ _ (fun d' h => Ground.Sh.join_carries d d' g o kept h)
    (fun y h => Ground.Sh.join_returns d g o kept y h)

/-- Send.joinAll on the core. -/
def joinAllS (g : Nat) : List (ReqMessage × Nat) → CoreSh → Option CoreSh
  | [], h => some h
  | x :: l, h => (joinS h g x.2 (decide (0 < x.1.life))).bind (joinAllS g l)

theorem joinAll_core (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d : DState L),
    (Send.joinAll groundG p g l d).map (fun d' => coreSh (coreOf d')) =
      joinAllS g l (coreSh (coreOf d))
  | [], _ => rfl
  | x :: l, d => by
    show ((Ground.joinP d g x.2 (decide (0 < x.1.life))).bind (Send.joinAll groundG p g l)).map _ =
      (joinS (coreSh (coreOf d)) g x.2 (decide (0 < x.1.life))).bind (joinAllS g l)
    rw [← joinP_core]
    cases Ground.joinP d g x.2 (decide (0 < x.1.life)) with
    | none => rfl
    | some d₁ => exact joinAll_core p g l d₁

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.sq_of
#print axioms VerifiableInference.Desc.First.Shape.joinP_core
#print axioms VerifiableInference.Desc.First.Shape.joinAll_core
