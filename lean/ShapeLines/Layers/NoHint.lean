-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/NoHint.lean: the empty hint. Six of link 0's closed lines take a hint as an
argument, and one of them, on members 10 to 14, holds the closing step, member 12, whose second text
closeGFH (Johnson/AtFull/Shape/CloseHint.lean) is handed the hint. What a hint is:
ShapeLines/ClosingHint.lean.
Why link 0 has a hint of its own. The guess in ClosingHint.lean is meant for the lists of the later
links.
Limits. closeGFH is equal to the closing step at every hint, with no premise: so no hint can make a
line false. Whether the hint is read, and whether a sort is run, is stated nowhere. Nothing on
soundness, completeness or hiding.
-/

namespace ShapeLines

/-- No guess, at every link. The argument is the link's number. -/
def noHint (_ : Nat) : List (Nat × Nat) := []

end ShapeLines
