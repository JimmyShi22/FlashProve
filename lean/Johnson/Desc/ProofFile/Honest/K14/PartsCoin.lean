-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/PartsCoin.lean: kind K14: THE PART AT "SPLIT" NEVER LAYS A
PLACEHOLDER WHERE ITS COIN IS DUE. The element that it sends is written in Honest/K14/PartsFit.lean
(scalarAt) with the head of the list of the coins that it spends, and 0 as the value of an empty
list. By type that list has one member: so the 0 is never taken. (The part itself is the frame's
scalarsPart, which adds the list of its values and the list of its coins member by member:
says_split, Honest/K14/PartsFit.lean, says that its one move sends scalarAt.)

  coin_there      the head of the list of one coin is that coin
  scalarAt_coin   the element that the part sends (scalarAt, Honest/K14/PartsFit.lean), with the
                  coin written out

What is not claimed. Which coin the book lends. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The head of the list of one coin is that coin: the value for an empty list is never taken. -/
theorem coin_there (c : Cs ⟨0, 1⟩) (z : OnBytes.E) :
    (coinsE c).headD z = OnBytes.E.ofTriple (OnBytes.Slice.ofE (c.e 0)) := by
  simp [coinsE]

/-- The element that the part at "SPLIT" sends, with the coin written out. -/
theorem scalarAt_coin (A : Data) (c : (splitPart A).Coins) (t : State Ask Unit) :
    scalarAt A c t =
      OnBytes.Slice.toE (Desc.K14.Honest.muAtE A.S (elems (heardFrom t A.atPoint 1))
        (elems (heardFrom t A.atZeta 1)) t.input.rows
        (OnBytes.E.ofTriple (OnBytes.Slice.ofE (c.2.1.1.e 0)))).triple := by
  unfold scalarAt
  rw [coin_there]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.coin_there
#print axioms ProofFile.Honest.K14.scalarAt_coin
