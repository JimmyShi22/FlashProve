-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Shape/DoorMasks.lean: the loop by which the one equation takes its link's
mask entries (K9.takeN, Johnson/Desc/First/Batch/Text.lean), on the shape of a statement, a book of
trees and a number of roots (Ground.Sh.CoreSh, Johnson/Desc/Ground/Shape/Core.lean): one
function on shapes, and two laws. General laws; nothing is evaluated. No test on values stands in
this loop.

  `takeNS o n a acc`: the loop on shapes: n times the taking of the next free mask entry of message
    o (takeMaskS, Johnson/Desc/Ground/Shape/Ground.lean).
  **`takeN_carries`**: K9.takeN returns (l, d') from d: then takeNS returns (l, the shape of d')
    from the shape of d.
  **`takeN_returns`**: takeNS returns from the shape of d: then K9.takeN returns from d.

Limits. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Batch.Shape.DoorCut
import Johnson.Desc.Ground.Shape.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9.Shape
open OnBytes OnBytes.Model VerifiableInference.Desc
open VerifiableInference.Desc.Ground.Sh (CoreSh shD takeMaskS takeMask_carries takeMask_returns)

/-- **The loop on shapes.** -/
def takeNS (o : Nat) : Nat → CoreSh → List Nat → Option (List Nat × CoreSh)
  | 0, a, acc => some (acc.reverse, a)
  | n + 1, a, acc => (takeMaskS a o).bind fun x => takeNS o n x.2 (x.1 :: acc)

variable {X : Type}

theorem takeN_carries (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat) (y : List Nat × St X),
    takeN o n d acc = .ok y → takeNS o n (shD d) acc = some (y.1, shD y.2)
  | 0, d, acc, y, h => by
    obtain rfl : (acc.reverse, d) = y := Except.ok.inj h
    rfl
  | n + 1, d, acc, y, h => by
    have h' : (there "K9.mask-entry-free" (Ground.takeMaskP d o) >>= fun x =>
      takeN o n x.2 (x.1 :: acc)) = .ok y := h
    obtain ⟨x, hx, hy⟩ := (ans_bind _ _ _).1 h'
    have hx' := (there_ok _ _ _).1 hx
    have c := takeMask_carries d x.2 o x.1 hx'
    show (takeMaskS (shD d) o).bind (fun x => takeNS o n x.2 (x.1 :: acc)) = _
    rw [c]
    exact takeN_carries o n x.2 (x.1 :: acc) y hy

theorem takeN_returns (o : Nat) : ∀ (n : Nat) (d : St X) (acc : List Nat) (z : List Nat × CoreSh),
    takeNS o n (shD d) acc = some z → ∃ y, takeN o n d acc = .ok y
  | 0, d, acc, _, _ => ⟨(acc.reverse, d), rfl⟩
  | n + 1, d, acc, z, h => by
    have h' : (takeMaskS (shD d) o).bind (fun x => takeNS o n x.2 (x.1 :: acc)) = some z := h
    obtain ⟨w, hw, hz⟩ := Option.bind_eq_some_iff.1 h'
    obtain ⟨x, hx⟩ := takeMask_returns d o w hw
    have c := takeMask_carries d x.2 o x.1 hx
    obtain rfl : w = (x.1, shD x.2) := Option.some.inj (hw.symm.trans c)
    obtain ⟨y, hy⟩ := takeN_returns o n x.2 (x.1 :: acc) z hz
    refine ⟨y, ?_⟩
    show (there "K9.mask-entry-free" (Ground.takeMaskP d o) >>= fun x =>
      takeN o n x.2 (x.1 :: acc)) = .ok y
    rw [hx]
    exact hy

end VerifiableInference.Desc.K9.Shape

#print axioms VerifiableInference.Desc.K9.Shape.takeN_carries
#print axioms VerifiableInference.Desc.K9.Shape.takeN_returns
