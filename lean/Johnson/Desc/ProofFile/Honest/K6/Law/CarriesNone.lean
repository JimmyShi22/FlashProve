-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/CarriesNone.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6): NOT
ONE OF ITS EIGHT PARTS STATES A CARRIED RUN: the field carries is the empty list at each, before the
row is seated and behind it. No definition; three theorems; no premise.

  `k6_carries_closed`     the eight lists, side by side: by unfolding
  `k6_carries_nil`        at every part of `headParts p at_`
  `k6_row_carries_nil`    at every part of the seated row `headRow wit p at_`

Why. The frame's lending walks a part's stated carried runs and the book's carrying entries at the
part's address in step, names first. A part that states none can name no other run there.

What it is not.
  * THAT THE BOOK HAS NO CARRYING ENTRY AT ONE OF K6's EIGHT ADDRESSES IS NOT SAID: where it had
    one, the lending would refuse the row for that.
  * Of the runs that the parts SPEND (six of the eight state some: names, order, counts) nothing is
    said here.
  * Nothing on any value, coin or run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par)

variable {W₀ Rc Tr X : Type}

/-- GENERAL. The eight parts' stated carried runs, side by side: none. -/
theorem k6_carries_closed (p : Head.Par) (at_ : Place) :
    (headParts p at_).map (·.carries) = [[], [], [], [], [], [], [], []] := rfl

/-- GENERAL. **No part of K6's row, before it is seated, states a carried run.** -/
theorem k6_carries_nil (p : Head.Par) (at_ : Place) :
    ∀ q ∈ headParts p at_, q.carries = [] := by
  intro q hq
  have h : q.carries ∈ (headParts p at_).map (·.carries) := List.mem_map.2 ⟨q, hq, rfl⟩
  rw [k6_carries_closed] at h
  simpa using h

/-- GENERAL. **Nor does a part of the seated row.** -/
theorem k6_row_carries_nil (wit : Local W₀ Rc Inst Tr → HeadAsk) (p : Head.Par) (at_ : Place) :
    ∀ q ∈ headRow (X := X) wit p at_, q.carries = [] := by
  intro q hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  exact k6_carries_nil p at_ q' hq'

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_carries_closed
#print axioms ProofFile.Honest.K6.k6_carries_nil
#print axioms ProofFile.Honest.K6.k6_row_carries_nil
