-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Pile.lean: "EVERY PENDING CLAIM ON THE COMMITTED TABLE HOLDS" ACROSS A CODE
SWITCH, at the sentence that the composed meaning gives (`RowsTrue` at the reader through the
state's
own book, `rwBook`: Johnson/Desc/K13/Law/ReaderByBook.lean). One structure of Prop, five theorems. A
law file: no sub-protocol imports it.

Why. That claim is open from the start of a request's own rounds: every sub-protocol in front of the
one that closes it owes its going back. The sentence finds the index masks' message through the
state's own book: at a state of which nothing is known it reads whatever tenant that book names. So
both sides of the tie are asked INSIDE A FENCE on the state in front.

What is said.
  `IndexFence N M L s`: the eight public facts on the state s that the reader's own lemma
    (`reads_rows`) asks: the messages' shapes and the book's places are the listed ones; the book is
    in order and in step with the statement; the listed places name trees that the book holds; the
    index masks' message is there and sits at the plan's tenant; every pending claim names mask
    entries of that message alone.
  `seat_left`, `shape_left`: under `Left` (Left.lean) an earlier message sits where it sat and has
  its shape.
  `agree_left`: so the two states' readers agree on the matrix and on that message's mask entries.
  `pile_back`: THE STATEMENT's SIDE: the sentence behind gives the sentence in front.
  `pile_bears`: THE WITNESS's SIDE: the sentence in front bears a turn of pads (PadsTurn.lean) off
    the index masks' tenant: `reads_rows`, called.

Limits. (1) `IndexFence` IS A PREMISE: four of its facts are fields of the structure of facts on
reached states (Johnson/Desc/First/FoldFacts.lean: msgShapes, bookInOrder at first tree 0,
seatsCarried, pileMasks); three follow from the table's promise where the index masks' pin is open;
"the listed places name trees that the book holds" from bookFits and seatsCarried: THESE STEPS ARE
NOT TYPED HERE. (2) No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Top.H0.K2Ties.Left
import Johnson.Top.H0.K2Ties.PadsTurn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S Numbers Comp)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsBy_congr seatBy noFirst sameQ)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  place_in_book)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook AgreeAt maskCut tableSize_of_shape reads_rows
  pileMasksC_iff holds_congr)

/-- **The public facts on the state in front that the reader through the book asks.** -/
structure IndexFence (N : Numbers) (M : List OracleShape) (L : Laid) (s : S) : Prop where
  shapes : msgShapesB M s.st = true
  order : bookInOrderB 0 s.book s.roots = true
  seats : seatsCarriedB L s.book = true
  step : s.book.place.size = s.st.oracles.size
  below : placesBelowB L s.book.place.size s.book.trees.size = true
  there : s.out.indexMasks < s.st.oracles.size
  seat : s.book.place[s.out.indexMasks]? = some N.index
  masks : pileMasksC s = true

/-- Under `Left` an earlier message sits where it sat. -/
theorem seat_left {s s' : S} (hL : Left s s') (o : ℕ) (q : ℕ × ℕ) (hq : s.book.place[o]? = some q)
    (hz : q.1 < s.book.trees.size) : seatBy noFirst s'.book o = seatBy noFirst s.book o := by
  obtain ⟨t', e', n⟩ := hL.trees q.1 _ (Array.getElem?_eq_getElem hz)
  unfold seatBy
  rw [hq, hL.places o q hq]
  show (s'.book.trees[q.1]?).map _ = (s.book.trees[q.1]?).map _
  rw [e', Array.getElem?_eq_getElem hz]
  show some (noFirst q.1 t', q.2) = some (noFirst q.1 _, q.2)
  unfold noFirst
  rw [n]

/-- Under `Left` an earlier message has its shape. -/
theorem shape_left {s s' : S} (hL : Left s s') (o : ℕ) (ho : o < s.st.oracles.size) :
    (s'.st.oracles[o]?).map (·.shape) = (s.st.oracles[o]?).map (·.shape) := by
  obtain ⟨x', hx', e⟩ := hL.grows.2.2 o _ (Array.getElem?_eq_getElem ho)
  rw [hx', Array.getElem?_eq_getElem ho]
  exact congrArg some e.1

section
variable {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
  (mat : Cells → Fin nR → (Fin k → Bool) → GE)

/-- The two states' readers agree on the matrix and on an earlier message's mask entries. -/
theorem agree_left (z : Pp) {s s' : S} (hL : Left s s') (o : ℕ) (q : ℕ × ℕ)
    (ho : o < s.st.oracles.size) (hq : s.book.place[o]? = some q) (hz : q.1 < s.book.trees.size)
    (w : Wit Cells Tok MsgT) : AgreeAt o (rwBook arr mat (z, s') w) (rwBook arr mat (z, s) w) := by
  refine ⟨rfl, fun i => ?_⟩
  show maskCut s'.st (wordsFirst arr s'.st s'.book w) ⟨o, i⟩ =
    maskCut s.st (wordsFirst arr s.st s.book w) ⟨o, i⟩
  unfold maskCut
  dsimp only
  rw [tableSize_of_shape hL.grows.1 (shape_left hL o ho)]
  unfold wordsFirst
  rw [wordsBy_congr arr _ _ s.st s'.st w o o hL.grows.1 (seat_left hL o q hq hz)
    (shape_left hL o ho) .mask i]

/-- **The statement's side**: the sentence behind the switch gives the sentence in front. -/
theorem pile_back (N : Numbers) (M : List OracleShape) (L : Laid) (z : Pp) {s s' : S}
    (hL : Left s s') (hF : IndexFence N M L s) (w : Wit Cells Tok MsgT)
    (h : RowsTrue (rwBook arr mat (z, s')) s' w) : RowsTrue (rwBook arr mat (z, s)) s w := by
  intro r hr
  obtain ⟨q, hq, hz⟩ := place_in_book hF.seats hF.step hF.below _ hF.there
  exact (holds_congr _ ((pileMasksC_iff s).1 hF.masks r hr)
    (agree_left arr mat z hL _ q hF.there hq hz w)).1 (h r (by rw [hL.rows]; exact hr))

/-- **The witness's side**: the sentence in front bears a turn of pads off the index masks' tenant.
-/
theorem pile_bears (N : Numbers) (M : List OracleShape) (L : Laid) (z : Pp) {s : S}
    (hF : IndexFence N M L s) (T : List (ℕ × ℕ)) (hT : N.index ∉ T) (w w' : Wit Cells Tok MsgT)
    (hw : PadsTurn T w w') (h : RowsTrue (rwBook arr mat (z, s)) s w) :
    RowsTrue (rwBook arr mat (z, s)) s w' :=
  (reads_rows arr mat N M L z s hF.shapes hF.order hF.seats hF.step hF.below hF.there hF.seat
    hF.masks w w' (hw .cells fun _ _ c => nomatch c) (hw (.msg _) fun _ _ c => nomatch c)
    (hw (.pad N.index.1 N.index.2) fun x hx c => hT (by
      have e1 : N.index.1 = x.1 := by injection c
      have e2 : N.index.2 = x.2 := by injection c
      rw [show N.index = x from Prod.ext e1 e2]
      exact hx))).1 h

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.seat_left
#print axioms VerifiableInference.Desc.First.K2Ties.shape_left
#print axioms VerifiableInference.Desc.First.K2Ties.agree_left
#print axioms VerifiableInference.Desc.First.K2Ties.pile_back
#print axioms VerifiableInference.Desc.First.K2Ties.pile_bears
