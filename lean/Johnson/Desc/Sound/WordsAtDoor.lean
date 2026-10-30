-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsAtDoor.lean: THE FIRST CHAIN's READER OF A ROW's WORDS, `wordsFirst`, ON THE
PROMISE's PUBLIC TESTS ALONE. One theorem with its proof: `tabFirst_at_plan`
(Johnson/Desc/Sound/WordsAtPlan.lean) with its three premises paid by the door's own lemmas
(Johnson/Desc/K12/Door/MsgShapes.lean: msgShape_at; DoorGives.lean: numbers_of_book0,
place_in_book).

  **`tabFirst_at_door`**: where "K12.msgShapes" (at the list M), "K12.bookInOrder" (at 0) and
    "K12.seatsCarried" (at the plan's list L) say yes of a statement st and a book B, the book has
    as many places as the statement has messages, and the plan's first places name trees below the
    book's number of trees (`placesBelowB`): for every message o of the statement: M has a shape sh
    at o, the book a place q, and the table that `wordsFirst` reads at o is `Wit.tab` at sh and q.

Limits. Book-keeping: nothing on soundness. That the four tests say yes at a border, and that the
book's number of places is the statement's number of messages there, is the promise's to carry.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsAtPlan
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement TreeBook OracleShape)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  msgShape_at numbers_of_book0 place_in_book)

/-- **The table that `wordsFirst` reads at a message of the statement, on the public tests alone.**
-/
theorem tabFirst_at_door {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (M : List OracleShape) (L : Laid)
    (st : Statement) (B : TreeBook) (roots : ℕ) (h₁ : msgShapesB M st = true)
    (h₂ : bookInOrderB 0 B roots = true) (h₃ : seatsCarriedB L B = true)
    (hs : B.place.size = st.oracles.size)
    (hb : placesBelowB L B.place.size B.trees.size = true) (w : Wit Cells Tok MsgT) (o : ℕ)
    (ho : o < st.oracles.size) :
    ∃ sh q, M[o]? = some sh ∧ B.place[o]? = some q ∧
      tabAt st.codes arr (seatBy noFirst B) st w o = w.tab st.codes sh (arr q.1 q.2) q.1 q.2 :=
  tabFirst_at_plan arr M st B (msgShape_at h₁) (numbers_of_book0 h₂) (place_in_book h₃ hs hb) w o ho

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabFirst_at_door
