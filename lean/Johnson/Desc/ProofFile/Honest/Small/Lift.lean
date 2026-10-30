-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Lift.lean proves two equations of parts, conditional on one
choice of set: the frame's two small parts (Honest/ForKinds.lean), written at any types V' W' Y and
seated by `Part.lift see wit get set` at set := fun x _ => x, are the frame's own parts at the types
V W X. The lens is the four functions see, wit, get and set; both equations are stated at that one
set. It is not a theorem on a distribution.

  `quietPart_lift`: the lifted part is `quietPart n`
  `scalarsPart_lift`: the lifted part is `scalarsPart name n` at the values read through wit and get

At every see, wit and get. So whatever is shown of the bare part (not lifted), at all types, is
shown of the part seated at that set.

The frame's terms that are used here (part, side, row, member, face, coin, run, book, fold and the
like): the head of Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a
caller opens it.

Limits. A lifted move hands on set x (get x), where the bare one hands on x: so, at a part that has
a move, the like equation fails wherever set x (get x) is not x, and would hold at every lens at
which it is: that is not stated here. `ExactMember` (Honest/Small/Field.lean) at every set:
Honest/Small/Quiet.lean, Scalars.lean. Nothing is claimed on any property of the protocol: not
soundness, completeness, binding, hiding or any other.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small

variable {V W X V' W' Y : Type}

/-- Conditional on set := fun x _ => x: the lifted part is `quietPart n`. -/
theorem quietPart_lift (see : V → V') (wit : W → W') (get : X → Y) (n : Nat) :
    (quietPart n : Part V' W' Y).lift see wit get (fun x _ => x) = quietPart n := by
  unfold Part.lift quietPart
  simp only [List.map_replicate]
  rfl

/-- Conditional on set := fun x _ => x: the lifted part is `scalarsPart name n` at the values read
through wit and get. -/
theorem scalarsPart_lift (see : V → V') (wit : W → W') (get : X → Y) (name : String) (n : Nat)
    (vals : W' → Front Y → List OnBytes.E) :
    (scalarsPart name n vals : Part V' W' Y).lift see wit get (fun x _ => x) =
      scalarsPart name n fun w fr => vals (wit w) ⟨fr.heard, get fr.own, fr.seen⟩ := rfl

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.quietPart_lift
#print axioms ProofFile.Honest.Small.scalarsPart_lift
