-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/Seated.lean: THE DEFINITION Seated, BY ITSELF: what a yes of the plain ground's
receiving or adopting says of the book behind against the book in front. A definition on plain
data, over Johnson/Desc/Book/BookFits.lean alone: IT NAMES NO ROUTINE AND IMPORTS NO GROUND, so
that a file can speak of it without importing the ground. That the ground's two
routines give it: recvP_seat, adoptP_seat (Johnson/Desc/Book/BookFitsGround.lean).
-/
import Johnson.Desc.Book.BookFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes

/-- What a yes of the receiving or of the adopting says of the book behind, B', against the book in
front, B: n messages come in, the first with the number n0; lay: the layout; num, src: the number
and the source of the new tree number tau of the layout. -/
structure Seated (B B' : TreeBook) (n n0 : Nat) (lay : TreeLay) (num : Nat → Nat)
    (src : Nat → Fmt.Src) : Prop where
  /-- a message's part number is the number of earlier messages of this sending in its tree -/
  fits : LayFits n lay
  /-- statement and book were in step -/
  step : n0 = B.place.size
  /-- THE i-TH NEW MESSAGE IS SEATED AT the old number of trees + its tree in the layout, at its
  part -/
  new : ∀ i, i < n → B'.place[n0 + i]? = some (B.trees.size + lay.tree.getD i 0, lay.part.getD i 0)
  /-- every older place is as it was -/
  places : ∀ j, j < B.place.size → B'.place[j]? = B.place[j]?
  /-- every older tree is as it was -/
  trees : ∀ j, j < B.trees.size → B'.trees[j]? = B.trees[j]?
  /-- as many trees more as the layout has -/
  size : B'.trees.size = B.trees.size + lay.shapes.size
  /-- JUST n places more: so statement and book are in step again -/
  count : B'.place.size = B.place.size + n
  /-- EACH NEW TREE: its shape is the layout's; its number and source; its parts are just its
  messages of this sending, in the order of sending -/
  made : ∀ τ, τ < lay.shapes.size → ∃ t : Tree, B'.trees[B.trees.size + τ]? = some t ∧
    t.shape = lay.shapes.getD τ {} ∧ t.number = num τ ∧ t.src = src τ ∧
    t.parts.size = cnt lay.tree τ n ∧
    ∀ j, j < n → lay.tree.getD j 0 = τ → t.parts[cnt lay.tree τ j]? = some (n0 + j)

end VerifiableInference.Desc.Book
