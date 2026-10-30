-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Named.lean: THE SMALLNESS TEST: IN WHICH ORACLE MESSAGES, AND SO IN WHICH
TREES AND TENANTS, THE ARRAYS LIE THAT THE DRAWN MATRIX MULTIPLIES: FUNCTIONS WITH CODE OF WHAT THE
CARRIED RECORD HOLDS IN FRONT OF THE DRAW. DEFINITIONS. NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

Why. The laws on the block of the draw speak of a list of oracle messages (their shapes) and of each
one's seat (its tree's number and its place among the tree's tenants). These were letters. Here they
are read off four public things: the smallness test's record tl, the link's record L, the chain's
statement S and the book of trees. The reading is the running text's own: `Order.liesAt` and
`Order.namedNow` (Johnson/Desc/First/K8/Order.lean), which the step that closes the list of tables
asks in its guard of order.
  `arrays tl`: the arrays that the matrix multiplies: each matrix's array of symbols, and those of
    the four vectors of reads that are there: what `Order.orderOk` walks.
  `msgNow L t`: the number under which the statement has, NOW, the message in which array t lies. An
    array born at this link: the link's own list has it. AN ARRAY BORN AT AN EARLIER LINK: the copy
    that was sent anew at the last switch: so it lies in a tree of the PRESENT link.
  `msgs tl L`: these numbers, each once.
  `memberAt S book o`: the message's shape in the statement, and its tree and tenant in the book.
  `partAt book j t`, `arrOf book j t`: which message the book has at tenant t of tree j: the book's
    list of the tree's parts; the second is total: 0 where there is none: THE TEST ASKS THE FIRST.
  `members`, `listOf rad`, `seatsOf`, `numsOf`: the list of these, each with its number; the shapes,
    each with a radius; the seats; the numbers. rad IS A LETTER HERE, BUT NOT A FREE ONE WHERE A PIN
    IS SPENT: a pin passes between two lists of members only where seat and entry (shape, radius)
    are the same: so rad must then give each message the plan's own radius.
  `namedB p S book tl L`: ONE TEST: every array has a message now; the statement has it; the book
    has a place for it; ITS TREE IS AMONG THOSE THAT THE PLACE NAMES (`p.matsIn ++ p.readsIn`); and
    the book's list of that tree's parts has just this message at that tenant.
  `namedAt p s`: the test at a carried record: it reads tl, L, S and the book off s itself; where no
    link is open it says no.
  `ownNow L j`, `seatOwn book L j`: the arm "born at this link" by itself: the number under which
    the statement has, now, the link's own j-th message; its tree and tenant.
MIND. `msgs` is made by `filterMap` and `eraseDups`: AN ARRAY WITHOUT A MESSAGE FALLS OUT OF
`listOf` AND `seatsOf` IN SILENCE: the first clause of `namedB` alone holds it: so the lists are to
be spent under `namedB`. Two arrays that lie in one message share a member.
Limits. WHERE INSIDE its message an array's entries lie is not read here. That the record's L, S and
book in front of the block are a plan's is not said. A tree's number in the book is taken for its
number in the first chain's order of sending.

-/
import Johnson.Desc.First.K8.Order
import Johnson.Desc.First.K8.Hear
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Named
open OnBytes OnBytes.Model

/-- The arrays that the matrix multiplies. -/
def arrays (tl : HTailF2) : List Nat :=
  tl.gtTree.toList ++ (List.range 4).filterMap fun n => tl.ix.U.getD n none

/-- Under which number the statement has, now, the message in which an array lies. -/
def msgNow (L : LinkCtx) (t : Nat) : Option Nat :=
  (Order.liesAt L t).bind (Order.namedNow L.check.frame)

/-- The arm "born at this link" by itself: the link's own j-th message, as the statement has it
now. -/
def ownNow (L : LinkCtx) (j : Nat) : Option Nat :=
  match L.check.frame.next with
  | .laterOrClose => L.check.frame.own[j]?
  | _ => none

/-- Its tree and tenant. -/
def seatOwn (book : TreeBook) (L : LinkCtx) (j : Nat) : Option (Nat × Nat) :=
  (ownNow L j).bind fun o => book.place[o]?

/-- These numbers, each once. -/
def msgs (tl : HTailF2) (L : LinkCtx) : List Nat := ((arrays tl).filterMap (msgNow L)).eraseDups

/-- A message's shape, and its tree and tenant. -/
def memberAt (S : Statement) (book : TreeBook) (o : Nat) : Option (OracleShape × (Nat × Nat)) :=
  match S.oracles[o]?, book.place[o]? with
  | some x, some jt => some (x.shape, jt)
  | _, _ => none

/-- Which oracle message the book has at a tenant of a tree: the book's own list of the tree's
parts. -/
def partAt (book : TreeBook) (j t : Nat) : Option Nat := (book.trees[j]?).bind (·.parts[t]?)

/-- The same as a total function: 0 where there is none. -/
def arrOf (book : TreeBook) (j t : Nat) : Nat := (partAt book j t).getD 0

/-- The members: each message's number, shape and seat. -/
def members (S : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx) :
    List (Nat × OracleShape × (Nat × Nat)) :=
  (msgs tl L).filterMap fun o => (memberAt S book o).map fun m => (o, m)

/-- Their shapes, each with a radius. -/
def listOf (rad : OracleShape → Nat) (S : Statement) (book : TreeBook) (tl : HTailF2)
    (L : LinkCtx) : List (OracleShape × Nat) :=
  (members S book tl L).map fun m => (m.2.1, rad m.2.1)

/-- Their seats. -/
def seatsOf (S : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx) : List (Nat × Nat) :=
  (members S book tl L).map (·.2.2)

/-- Their numbers in the statement. -/
def numsOf (S : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx) : List Nat :=
  (members S book tl L).map (·.1)

/-- **The test.** -/
def namedB (p : Par) (S : Statement) (book : TreeBook) (tl : HTailF2) (L : LinkCtx) : Bool :=
  (arrays tl).all fun t =>
    match msgNow L t with
    | none => false
    | some o =>
      match memberAt S book o with
      | none => false
      | some m => (p.matsIn ++ p.readsIn).contains m.2.1 && partAt book m.2.1 m.2.2 == some o

/-- The test at a carried record. -/
def namedAt (p : Par) (s : S) : Bool :=
  match s.tl?, s.link? with
  | some tl, some L => namedB p s.st s.book tl L
  | _, _ => false

end VerifiableInference.Desc.First.K8.Named
