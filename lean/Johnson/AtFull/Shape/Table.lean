-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/Table.lean: THE TABLE OF THE FIRST CHAIN's 358 MEMBERS, BY NUMBER: a frame for
laying one thing at each member (a step on shapes; a test on values), and for reading it back at a
member's number. General in what is laid. It imports nothing.

The order is that of the proof file's own flat list in the goals' scope: number 0: the front; 14 l
+ 1 to 14 l + 14: link l, for l = 0 to 23; 337 to 352: the head's link; 353 to 357: the finish, the
proximity test, the memory's batching, W's sending, the seal.

  `LinkRow` (fourteen fields), `HeadRow` (sixteen), `BackRow` (five), each with its reader by place
    `.at`.
  **`table front links head back`** : Nat → α.
  `table_front`, **`table_link`** (l < 24, j < 14: at 14 l + j + 1 stands (links l).at j),
    **`table_head`** (j < 16: at 337 + j), **`table_back`** (at 353 + j).

Limits. A frame alone: that the member at a number IS of the kind that the field's name says is said
by no law here (the seats' laws tie each member to its number). THE TABLE HAS NO END: at every
number from 358 on it answers in silence with the seal's entry; a caller that walks one number too
far gets the seal's entry once more and no refusal: the bound is the caller's. The argument front
stands for what the chain calls its first member, not for the chain's field of that name. Nothing on
soundness, completeness or hiding.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape

/-- What stands at the fourteen members of one of the links 0 to 23, in their order. -/
structure LinkRow (α : Type) where
  laid : α
  /-- the link's first hearing member: at link 0 the opening, else the code switch; with the
  frame's "opened" behind it -/
  first : α
  lookCalls : α
  /-- the link's own rounds: the layers' or the attention's -/
  own : α
  reads : α
  draw : α
  digits : α
  lookDigits : α
  batch : α
  behind : α
  equation : α
  close : α
  shut : α
  cleared : α

/-- What stands at the sixteen members of the head's link. -/
structure HeadRow (α : Type) where
  laid : α
  reply : α
  switch : α
  lookCalls : α
  own : α
  reads : α
  draw : α
  digits : α
  lookDigits : α
  merge : α
  batch : α
  behind : α
  equation : α
  close : α
  shut : α
  cleared : α

/-- What stands at the five members behind the links. -/
structure BackRow (α : Type) where
  finish : α
  test : α
  batching : α
  sendW : α
  sealing : α

variable {α : Type}

/-- The row read by place, 0 to 13; every place beyond answers with the last field. -/
def LinkRow.at (r : LinkRow α) : Nat → α
  | 0 => r.laid | 1 => r.first | 2 => r.lookCalls | 3 => r.own | 4 => r.reads | 5 => r.draw
  | 6 => r.digits | 7 => r.lookDigits | 8 => r.batch | 9 => r.behind | 10 => r.equation
  | 11 => r.close | 12 => r.shut | _ => r.cleared

/-- The row read by place, 0 to 15; every place beyond answers with the last field. -/
def HeadRow.at (r : HeadRow α) : Nat → α
  | 0 => r.laid | 1 => r.reply | 2 => r.switch | 3 => r.lookCalls | 4 => r.own | 5 => r.reads
  | 6 => r.draw | 7 => r.digits | 8 => r.lookDigits | 9 => r.merge | 10 => r.batch
  | 11 => r.behind | 12 => r.equation | 13 => r.close | 14 => r.shut | _ => r.cleared

/-- The row read by place, 0 to 4; every place beyond answers with the last field, the seal's. -/
def BackRow.at (r : BackRow α) : Nat → α
  | 0 => r.finish | 1 => r.test | 2 => r.batching | 3 => r.sendW | _ => r.sealing

/-- **The table**: for each number of a member in the first chain's flat list (0 to 357) what stands
there: the front; fourteen at each of the links 0 to 23; sixteen at the head's link; five behind.
AT EVERY NUMBER FROM 358 ON IT ANSWERS WITH THE SEAL's ENTRY: it has no refusal. -/
def table (front : α) (links : Nat → LinkRow α) (head : HeadRow α) (back : BackRow α) (b : Nat) :
    α :=
  if b = 0 then front
  else if b < 337 then (links ((b - 1) / 14)).at ((b - 1) % 14)
  else if b < 353 then head.at (b - 337)
  else back.at (b - 353)

variable (front : α) (links : Nat → LinkRow α) (head : HeadRow α) (back : BackRow α)

/-- At 0 stands the front. -/
theorem table_front : table front links head back 0 = front := rfl

/-- At 14 l + j + 1 stands place j of link l's row. -/
theorem table_link (l j : Nat) (hl : l < 24) (hj : j < 14) :
    table front links head back (14 * l + j + 1) = (links l).at j := by
  unfold table
  rw [if_neg (by omega), if_pos (by omega), show (14 * l + j + 1 - 1) / 14 = l from by omega,
    show (14 * l + j + 1 - 1) % 14 = j from by omega]

/-- At 337 + j stands place j of the head's row. -/
theorem table_head (j : Nat) (hj : j < 16) :
    table front links head back (337 + j) = head.at j := by
  unfold table
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    show 337 + j - 337 = j from by omega]

/-- At 353 + j stands place j of the back row. No bound on j: from j = 5 on no member stands there,
and the law speaks of the seal's entry. -/
theorem table_back (j : Nat) :
    table front links head back (353 + j) = back.at j := by
  unfold table
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 353 + j - 353 = j from by omega]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.table_link
#print axioms Johnson.AtFull.Shape.table_head
#print axioms Johnson.AtFull.Shape.table_back
#print axioms Johnson.AtFull.Shape.table_front
#print axioms Johnson.AtFull.Shape.LinkRow
#print axioms Johnson.AtFull.Shape.HeadRow
#print axioms Johnson.AtFull.Shape.BackRow
#print axioms Johnson.AtFull.Shape.LinkRow.at
#print axioms Johnson.AtFull.Shape.HeadRow.at
#print axioms Johnson.AtFull.Shape.BackRow.at
#print axioms Johnson.AtFull.Shape.table
