-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/ClosingHint.lean: the hint that this library's closed lines take, but for link 0's
(Layers/NoHint.lean). It is read at one member of a link alone, the closing, by closeGFH
(Johnson/AtFull/Shape/CloseHint.lean), the second text of the closing's step.
Beneath the closing step, mergeIdx sorts lists of numbers and keeps each number once. A hint is a
guess at such a result: a list of pairs (s, n), each standing for the n consecutive numbers from s
on (MergeIdxH.lean). It is meant to spare Lean's kernel the sort where the guess is right.
Limits. closeGFH is equal to the closing step at every hint, with no premise: so a wrong hint cannot
make a line false; it can make one long, since the sort is then run. That the hint is read, that a
sort is spared, or that this hint is right at a given link is stated nowhere. A hint that is far too
long may keep the kernel busy without end (MergeIdxH.lean). Nothing on soundness, completeness or
hiding.
-/

namespace ShapeLines

/-- The guess 0 to 19674, then 4194301 to 4194303, at every link. The argument is the link's number.
-/
def closingHint (_ : Nat) : List (Nat × Nat) := [(0, 19675), (4194301, 3)]

end ShapeLines
