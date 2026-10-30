-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/WordAt.lean: WHAT THE FIRST CHAIN's READER OF A WITNESS's WORDS
(`wordsFirst`, Johnson/Desc/Sound/WordsAt.lean) GIVES AT A ROW AND A PLACE OF AN ORACLE MESSAGE
WHOSE SHAPE AND SEAT ARE KNOWN: the witness's table of that message (`Wit.tab`,
Johnson/Desc/Sound/MsgSig.lean). One statement with its proof: two calls. At letters; over the
library alone.

  `wordFirst_at_row` the statement st has the shape sh at the message o · the book B seats o at q
                    (`seatBy noFirst B o = some q`) · b < sh.rows part ⊢ `wordsFirst arr st B v o
                    part (b + j * 2 ^ ceilLog2 (sh.rows part)) = v.tab st.codes sh (arr q.1 q.2) q.1
                    q.2 (part == .mask) b j`. arr: the numbering of the seats; j: any place

Why. The claim on a code switch's carried rows reads words at indices of just this form. `Wit.tab`
reads, at a pad's places, the seat's own component of the witness, and elsewhere the message's,
which all copies share: this file stops in front of that split.

By, the library's: `wordsOn_idxOf` (Johnson/Top/H0/K2Caller/WordsNames.lean): the word at the index
"row + 2 ^ ceilLog2 rows * place" is the table's entry · `tab_at_new`
(Johnson/Top/H0/Tw/K2C/WordsAtNew.lean): the table at a message of known seat and shape: called at a
list of one entry · `wordsFirst_is` (Johnson/Desc/Sound/WordsAtPlan.lean). NEAR, NOT CALLED:
`tabFirst_at_book` (Johnson/Desc/Sound/HbookFirst.lean), `tabFirst_at_plan`, `tabFirst_at_door`
(Johnson/Desc/Sound/WordsAtDoor.lean):
the table by the book's place, under premises on the whole book · `words_at_new` (WordsAtNew.lean):
the like at a sending's typed entries · inside the proof of `words_tabQ`
(Johnson/Desc/First/Link/Law/TieThreeEq.lean) stands this equation at any index with a real row.

Limits. At letters: no state, no run and no witness is given. Nothing on which places a pad has. j
is not held below a code's length. Nothing on any property.
-/
import Johnson.Top.H0.K2Caller.WordsNames
import Johnson.Top.H0.Tw.K2C.WordsAtNew
import Johnson.Desc.Sound.WordsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsFirst_is tabAt seatBy noFirst)
open VerifiableInference.Desc.First.K2Caller (wordsOn_idxOf)
open VerifiableInference.Desc.First.K2 (tab_at_new)
open Johnson.Top.H (idxOf)

variable {Cells Tok : Type}

/-- **THE WORD AT A ROW AND A PLACE OF A MESSAGE**: what the reader of a witness's words gives at
the index "row + place * 2 ^ ceilLog2 rows" is the witness's table of that message, at its seat's
number, at that row and place. -/
theorem wordFirst_at_row (arr : Nat → Nat → Nat) (st : Statement) (B : TreeBook)
    (v : Wit Cells Tok MsgT) {o : Nat} {sh : OracleShape} {q : Nat × Nat}
    (hs : (st.oracles[o]?).map (·.shape) = some sh) (hq : seatBy noFirst B o = some q)
    (part : Part) {b : Nat} (hb : b < sh.rows part) (j : Nat) :
    wordsFirst arr st B v o part (b + j * 2 ^ ceilLog2 (sh.rows part)) =
      v.tab st.codes sh (arr q.1 q.2) q.1 q.2 (part == .mask) b j := by
  have ht : tabAt st.codes arr (seatBy noFirst B) st v o =
      v.tab st.codes sh (arr q.1 q.2) q.1 q.2 :=
    tab_at_new st.codes [(sh, 0)] (fun _ => q) arr v st B o ⟨0, Nat.zero_lt_one⟩ hq hs
  have h := wordsOn_idxOf st (tabAt st.codes arr (seatBy noFirst B) st v) o sh hs part (j + 1)
    (⟨b, hb⟩, ⟨j, Nat.lt_succ_self j⟩)
  have ei : b + j * 2 ^ ceilLog2 (sh.rows part) =
      idxOf (sh.rows part) (j + 1) (⟨b, hb⟩, ⟨j, Nat.lt_succ_self j⟩) := by
    unfold idxOf
    rw [Nat.mul_comm]
  rw [wordsFirst_is, ei, h, ht]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.wordFirst_at_row
