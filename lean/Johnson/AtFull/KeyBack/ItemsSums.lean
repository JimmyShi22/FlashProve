-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ItemsSums.lean: THE BYTES OF THE FOUR LISTS OF ITEMS THAT configure SPELLS
BESIDE THE KEY's ONE-TIME CHAIN's (madeLinItems · madeEntryItems · madeFirstItems,
OnBytes/Model/ReadBackMade.lean), AS SUMS OF NUMBERS: general: at every value. Theorems with their
proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  lin_sum     the two items of a test on the table: an upper bound (size_spellLin is one)
  entry_sum   the two items of a copy's file's chain
  first_sum   the seven items of a proof file's first chain: it reads of the shapes x THE SPELLED
              LAYOUT's SIZE and the NUMBER of the identifiers alone
LIMITS. Sizes alone. No soundness is claimed. On hiding nothing.
-/
import Johnson.AtFull.KeyBack.SpellSizes
import Johnson.AtFull.KeyBack.ShortOfBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.KeyBack
open OnBytes OnBytes.Params

/-- What the four lists of stages of a test on the table count together. -/
def stagesOf (S : LinShape) : Nat :=
  S.testU.length + S.testOmega.length + S.testOwn.length + S.testOwnOmega.length

theorem lin_sum (codes : Codes) (S : LinShape) : itemsSize (madeLinItems codes S) ≤
    (16 + (Fmt.ascii "codes").size + (16 + 24 * codes.base.size + 24 * codes.mask.size)) +
      (16 + (Fmt.ascii "the test on the table").size + (1024 + 32 * stagesOf S)) := by
  have := size_spellLin S
  unfold itemsSize madeLinItems stagesOf
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fmt.size_item,
    size_spellCodes]
  omega

theorem entry_sum (z : Sized) : itemsSize (madeEntryItems z) =
    (16 + (Fmt.ascii "codes").size +
        (16 + 24 * z.entryCodes.base.size + 24 * z.entryCodes.mask.size)) +
      (16 + (Fmt.ascii "the link").size + (128 + 32 * z.link.shape.later.length)) := by
  unfold itemsSize madeEntryItems
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fmt.size_item,
    size_spellCodes, size_spellLink]
  omega

theorem first_sum (l : Lines) (x : Shapes) (z : Sized) : itemsSize (madeFirstItems l x z) =
    itemsSize (madeLinItems z.proof.codes z.proof.batch.shape) +
      ((16 + (Fmt.ascii "request's shape").size + (spellReq z.proof.request).size) +
        (16 + (Fmt.ascii "layout").size + (spellLayout x.layout).size) +
        (16 + (Fmt.ascii "links' identifiers").size + (8 + 8 * x.identifiers.length)) +
        (16 + (Fmt.ascii "pending rows").size + 8) +
        (16 + (Fmt.ascii "binding tree").size + 16)) := by
  have w : (spellWord x.sub.pendingRows).size = 8 := rfl
  unfold itemsSize madeFirstItems
  rw [List.map_append, List.sum_append]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Fmt.size_item,
    size_spellWords, size_spellBinding, w]
  omega

end AtFull.KeyBack

#print axioms AtFull.KeyBack.lin_sum
#print axioms AtFull.KeyBack.entry_sum
#print axioms AtFull.KeyBack.first_sum
