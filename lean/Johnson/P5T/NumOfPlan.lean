-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/NumOfPlan.lean: THE WITNESS's NUMBER OF A LINK's OWN MESSAGE, OFF THE PLAN's SEATS, AND
THAT `arrOf` (Johnson/P5T/PlanSeats.lean) IS THAT NUMBER AT THE MESSAGE's SEAT. One definition with
code, two theorems. It names no Mathlib.

  `numOfPlan ps l k`: the place of the key (0, l, k) (message k of link l's own list: the original
    and every kept copy alike: `keyOf`) among the seats' keys, each once, in the list's order.
  `arrOf_of_find`: at a seat (j, t) whose first holder in the list is p, `arrOf` is the place of p's
    key.
  `arrOf_is_num`: so, where p's key is (0, l, k), `arrOf ps j t = numOfPlan ps l k`.

Limits. BOTH MUST BE READ AT ONE LIST ps: at the composed filling: ALL THREE chains' (planSeatsAll Z
Z.D); at a seat or key of the first chain's list the numbers are those over that list alone
(Johnson/P5T/ArrAll.lean). That (0, l, k) is the numbering by which a request's array
names a message is said by nothing here. Where no seat of the list is (j, t), `arrOf` is the number
of keys: no message's number. Nothing on soundness.

-/
import Johnson.P5T.PlanSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T

/-- The witness's number of message k of link l: the place of its key among the seats' keys. -/
def numOfPlan (ps : List PSeat) (l k : Nat) : Nat := ((ps.map keyOf).eraseDups).idxOf (0, l, k)

/-- At a seat whose first holder in the list is p, `arrOf` is the place of p's key. -/
theorem arrOf_of_find (ps : List PSeat) (j t : Nat) (p : PSeat)
    (h : (ps.find? fun p => p.j == j && p.t == t) = some p) :
    arrOf ps j t = ((ps.map keyOf).eraseDups).idxOf (keyOf p) := by
  unfold arrOf
  simp only [h]

/-- Where that holder's key is an own message's, `arrOf` is `numOfPlan`. -/
theorem arrOf_is_num (ps : List PSeat) (j t l k : Nat) (p : PSeat)
    (h : (ps.find? fun p => p.j == j && p.t == t) = some p) (hk : keyOf p = (0, l, k)) :
    arrOf ps j t = numOfPlan ps l k := by
  rw [arrOf_of_find ps j t p h, hk]
  rfl

end P5T

#print axioms P5T.arrOf_of_find
#print axioms P5T.arrOf_is_num
