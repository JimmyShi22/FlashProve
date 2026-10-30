-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Border.lean: what the last chain of a proof file takes of the two earlier chains'
ends, as two projections. Definitions with code. No theorem.

This chain has three names: "the last chain" and "the third chain" in these files, "the second
chain" in the format (Johnson/Desc/Block.lean: the field `second`; the refusal "the second chain's
start") and in `verify-on-bytes`.

Main names:
  `sharedOfEnd`: of `verify-on-bytes`'s record of the shared chain's end: the statement, the book,
    the shared point psi, Omega's number.
  `firstOfS`: of the first chain's last carried record (Johnson/Desc/First/State.lean): the
    statement, the book, the count of roots, the numbers of W, of the own group and of the mask by
    name, the pending rows; nothing where the record names no W.
  `startAtEnds`: the chain's start at these two.

Limits.
(1) The start is safe only beside the first chain's own last test (S.fin). `firstOfS` does not read
the record's mark (`failed`) or its debt (`rowsOwed`): a marked first record starts this chain as an
unmarked one does.
(2) `firstOfS` gives nothing unless the record stands behind the batching with W's number laid
(S.firstEnd?): there `S.rows` is the one row read off the claim.
(3) The record's count of roots is not compared with the format's own count.
(4) No law says that the two projections read the right fields.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.K14BatchLinearConstraintsSecondPart
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Third

/-- What the third chain takes of the shared chain's end, out of the program's record of it. -/
def sharedOfEnd (e : Proof.SharedEnd) : SharedOut :=
  { st := e.st, book := e.book, psi := e.lin.psi, omega := e.lin.omega }

/-- What the third chain takes of the first chain's last carried record. -/
def firstOfS (s : First.S) : Option FirstEnd₃ :=
  s.firstEnd?.map fun e =>
    { st := s.st, book := s.book, roots := s.roots, w := e.lin.w, own := e.lin.own
      mask := e.lin.mask, pending := s.rows }

/-- **The third chain's start, of the first chain's last record and the program's record of the
shared chain's end.** -/
def startAtEnds {XiPub : Type} (p : P₁₄) : XiPub → First.S → Proof.SharedEnd → Except String S₃ :=
  start₃F p firstOfS sharedOfEnd

end VerifiableInference.Desc.Third
