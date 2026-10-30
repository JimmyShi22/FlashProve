-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/TailHead.lean: behind the closing of the head's link: the tail of kind K10
at that link, as a block without a round at the first chain's carried record S
(Johnson/Desc/First/State.lean). Definitions alone.

ROUNDS. None. READS. Nothing.
DECIDES. It is the link's frame's `clearWith` (Johnson/Desc/First/Walk/Frame.lean: one text for all
links) at the head's own two readings of S:
  `countsHead`  the counts at the head's link's end, each under its name:
      K10.tail.head     the record stands inside the head's link, its sub-proof opened
      K10.tail.claims   as many claims were added as the plan counts
      K10.tail.weights  every claim of the plan has had its weight handed out
      K10.tail.folds    every matrix of the smallness test has had its call of the fold's sums
  `leftHead`    what the head's sub-proof left for its row.
clearWith then asks the frame's own (N: a link with its fork is open; W3: the last challenge was
drawn and the link is closed; W4: the sub-proof worked on the plan's list of arrays, at the plan's
sizes; W5: it left what the row is made of), makes the link's one pending row on the weight table
(Johnson/Desc/First/Pend/Row.lean: `pendingRowO`; a refusal under "ROW: " and the row's own word),
lays it at the end of the pile, and leaves the link. No test reads a value that was sent or drawn.
THE ROW IS MADE ONLY WHERE THE LINK's PUBLIC RECORD SAYS THAT THE LINK LEAVES ONE (X.fv): at
X.fv = false, the record's default, clearWith leaves the link with no row and says nothing; the
block's test on the plan does not ask X.fv. Who notices: the count of the pile against the plan's
rows, at the chain's end. K10.tail.head's clause "its sub-proof opened" cannot speak behind
clearWith's own N; its other arm (the record stands in another sort of link) can.
What is written: the pile (out.pending); one ledger of the statement's messages (the index masks':
an entry taken); the walk's state of the calls := the link's live copy; here := between two links.
SENDS. Nothing.

The counts are typed after the program `verify-on-bytes`'s lines at the end of the head's link
routine (OnBytes/Model/Head.lean); `weightsOut` and `foldsOut` are the frame's file's.

-/
import Johnson.Desc.First.Walk.Frame
import Johnson.Desc.First.Pend.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LinkPub clearWith weightsOut foldsOut)

/-- The counts at the head's link's end. -/
def countsHead (s : S) : Except String Unit :=
  match s.here with
  | .head a => do
    need "K10.tail.head" a.opened
    need "K10.tail.claims" (a.F.nClaim == a.F.planClaimsF)
    need "K10.tail.weights" (weightsOut a.F)
    need "K10.tail.folds" (foldsOut a.tl)
  | _ => .error "K10.tail.head"

/-- What the head's sub-proof left for its row. -/
def leftHead (s : S) : Option WsForkOut :=
  match s.here with
  | .head a => a.wo
  | _ => none

/-- **Behind the head's closing.** X: the link's public record. lay: the layout of the weight table.
lin: the shape of the test on it. -/
def tailHead (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) : S → Except String S :=
  clearWith X countsHead leftHead fun masks w claims os =>
    Pend.pendingRowO lay masks w claims lin os

/-- The block. l: the head's link. piece: its number inside the link. -/
def tailHeadBlock {Cl : Type} (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) (l piece : Nat) :
    Block S Cl :=
  { (roundlessBlock s!"behind the closing of link {l}" 1 (some l) piece (tailHead X lay lin) :
      Block S Cl) with place := ⟨1, some l, piece, .K10⟩ }

end VerifiableInference.Desc.First.Close
