-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/LateBelow.lean: EVERY SLOT THAT ONE OF K4's TWO LISTINGS OF CLAIMS FILLS LATE
LIES BELOW THE LEDGER's NEXT, where the listing's windows end at or below that next. Statements with
their proofs: calls of `formsFront_past` | `formsBack_past` (Johnson/Road/K4/Slots/RunsSpare.lean):
from the ledger's next on a listing turns nothing: so no slot there is "free in front and filled
behind".

  `late_mem`: what a member of the list of late slots (`K9.lateOf`,
    Johnson/Desc/First/Batch/ReaderOf.lean) says of its slot.
  **`late_below_front`** | **`late_below_back`**: ∀ x ∈ K9.lateOf F G, x.1 < F.next.

Limits. That the windows end at or below the ledger's next is a premise. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Slots.RunsSpare
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (K9.lateOf)

/-- A late slot is free in front and filled behind. -/
theorem late_mem {F G : Fork} {x : ℕ × E × E} (h : x ∈ K9.lateOf F G) :
    ¬ Filled F x.1 ∧ Filled G x.1 := by
  unfold K9.lateOf at h
  obtain ⟨j, _, hx⟩ := List.mem_filterMap.1 h
  by_cases c : (!(F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos c] at hx
    obtain rfl := Option.some.inj hx
    rw [Bool.and_eq_true, Bool.not_eq_true'] at c
    exact ⟨fun q => by
      unfold Filled at q
      rw [c.1] at q
      exact absurd q (by decide), c.2⟩
  · rw [if_neg c] at hx
    exact nomatch hx

theorem late_below_of {F G : Fork} (h : ∀ j, F.next ≤ j → SameAt F G j) :
    ∀ x ∈ K9.lateOf F G, x.1 < F.next := by
  intro x hx
  obtain ⟨a, b⟩ := late_mem hx
  by_contra c
  exact a ((h x.1 (by omega)).1.1 b)

/-- **The late slots of the listing "front" lie below the ledger's next.** -/
theorem late_below_front {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork} {fs : Array Aff}
    (hF : Sized F) (h : formsFrontWith rows P g o F = some (fs, G))
    (w1 : o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ F.next)
    (w2 : o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next) :
    ∀ x ∈ K9.lateOf F G, x.1 < F.next :=
  late_below_of (formsFront_past hF h w1 w2).2.2

/-- **The late slots of the listing "back" lie below the ledger's next.** -/
theorem late_below_back {o : Own} {F G : Fork} {fs : Array Aff} (hF : Sized F)
    (h : formsBack o F = some (fs, G))
    (w : o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ F.next) :
    ∀ x ∈ K9.lateOf F G, x.1 < F.next :=
  late_below_of (formsBack_past hF h w).2.2

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.late_mem
#print axioms OnBytes.Desc.First.K4.Slots.late_below_of
#print axioms OnBytes.Desc.First.K4.Slots.late_below_front
#print axioms OnBytes.Desc.First.K4.Slots.late_below_back
