-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/KeyBack.lean: THE WAY BACK OF `arrOf_is_num` (Johnson/P5T/NumOfPlan.lean): WHATEVER SEAT
HAS THE NUMBER OF MESSAGE k OF LINK l HOLDS THAT MESSAGE OR A KEPT COPY OF IT. One theorem, one
negative test. On public data alone.
  `key_of_num`: p is the first of the list at its tree and tenant, and `arrOf` there is `numOfPlan
    ps l k`: then p's key is (0, l, k). (The place of a member in a list without repeats names the
    member; and a key that is not listed has "the number of keys", which no seat has: so that the
    key is listed need not be asked.)
  `needs_first`: the first premise cannot be dropped: at the empty list, and a seat p that is in no
    link's sending and has no role: `arrOf` at p's tree and tenant and `numOfPlan` at every (l, k)
    are both "the number of keys", and p's key is not (0, l, k).
Why. A reader takes the tenant of its own group that has a given number. `arrOf_is_num` says that a
copy of the message has the number; only the way back says that whatever has the number is a copy.
Nothing on soundness.

-/
import Johnson.P5T.NumOfPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- **Whatever seat has the number holds the message.** -/
theorem key_of_num (ps : List PSeat) (p : PSeat)
    (hf : (ps.find? fun q => q.j == p.j && q.t == p.t) = some p) (l k : Nat)
    (h : arrOf ps p.j p.t = numOfPlan ps l k) : keyOf p = (0, l, k) := by
  rw [arrOf_of_find ps p.j p.t p hf] at h
  unfold numOfPlan at h
  have h1 : keyOf p ∈ (ps.map keyOf).eraseDups :=
    List.mem_eraseDups.2 (List.mem_map.2 ⟨p, List.mem_of_find?_eq_some hf, rfl⟩)
  exact (List.idxOf_inj h1).1 h

/-- Negative test of the first premise: the numbers agree, the key is another. -/
theorem needs_first (p : PSeat) (hs : p.seg = none) (hr : p.role = .other) (l k : Nat) :
    arrOf [] p.j p.t = numOfPlan [] l k ∧ keyOf p ≠ (0, l, k) := by
  refine ⟨rfl, ?_⟩
  simp [keyOf, hs, hr]

end P5T

#print axioms P5T.key_of_num
#print axioms P5T.needs_first
