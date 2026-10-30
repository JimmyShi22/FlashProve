-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsAt.lean: THE WORDS THAT A WITNESS GIVES, READ THROUGH A CHAIN's RECORD.
Definitions, and laws with their proofs.

THE TERM. A row of a statement speaks of words: a value for each message's number, table and index
(`Means.Words`, Johnson/Desc/Means/Says.lean). A witness holds messages by another count, and a pad
for
each seat (tree, part) (`Wit`, Johnson/Desc/Msg.lean). From the one to the other:
  the message's number o —(the record's book: `seatBy`, TabAt.lean)→ its seat —(the one
  accessor `Wit.tab`, MsgSig.lean, at o's shape: `tabAt`)→ its table
  —(`wordsOn`, Johnson/Desc/Means/ItemsTab.lean)→ words.

  `wordsOn_congr`: what `wordsOn` reads of a statement at a message is its shape alone.
  `wordsBy arr seatAt S w` := `wordsOn S (tabAt S.codes arr seatAt S w)`. **`wordsBy_congr`**: one
  table
    of codes, one seat, one shape: the same words, at both tables and every index.
  **`wordsFirst`, `wordsShared t₁`, `wordsLast t₁ t₂`**: at the first chain's statement and book, at
    the shared chain's, AT THE LAST CHAIN's RECORD (`S₃`, Johnson/Desc/Third/State.lean): closed terms.
  `seatBy_frame`: a later book that keeps o's place and its tree gives o the same seat.
  `BookedLast o s s'`: THE BOOK-KEEPING around the last chain's first block: seven clauses.
  **`words_older`** · **`words_omega`** · **`words_first`**: under `Says p s s'` and `BookedLast o s
  s'`: an
    older message has the same words through both records · Omega's copy's words through the record
    behind are Omega's through the shared chain's end · through the record in front a message has
    the words that it has through the first chain's own reading of that book. ALL THREE AT BOTH
    TABLES AND AT EVERY INDEX.

Limits. Nothing on soundness or on hiding. A tree's number through the file is taken from
`Tree.number` (`noFirst`, `noShared`, `noLast`); the first chain's table of joints takes the tree's
PLACE in the book: "number = place" is a premise wherever the two must meet; stated nowhere here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Means.ItemsTab
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.Third.Law.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement TreeBook Tree Part)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open OnBytes.Means (Words wordsOn realRows)
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄)
open VerifiableInference.Desc.Third.Law (Says BookSays Sharp extends_of_says)

/-! ## 1 The words under a map of seats -/

/-- What `wordsOn` reads of a statement at a message is its shape alone. -/
theorem wordsOn_congr {K : Type} [CommRing K] (S S' : Statement) (T T' : ℕ → Bool → ℕ → ℕ → K)
    (o o' : ℕ) (hx : (S'.oracles[o']?).map (·.shape) = (S.oracles[o]?).map (·.shape))
    (hT : T' o' = T o) (part : Part) (i : ℕ) :
    wordsOn S' T' o' part i = wordsOn S T o part i := by
  have hb : S'.rowBits o' part = S.rowBits o part ∧ realRows S' o' part = realRows S o part := by
    unfold Statement.rowBits realRows
    cases h : S.oracles[o]? with
    | none =>
      rw [h, Option.map_none, Option.map_eq_none_iff] at hx
      rw [hx]
      exact ⟨rfl, rfl⟩
    | some x =>
      rw [h, Option.map_some] at hx
      obtain ⟨x', h', e⟩ := Option.map_eq_some_iff.1 hx
      rw [h']
      dsimp only
      rw [e]
      exact ⟨rfl, rfl⟩
  unfold wordsOn
  rw [hb.1, hb.2, hT]

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **The words that the witness w gives at the statement S, the messages' seats by seatAt.** -/
def wordsBy (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (w : Wit Cells Tok MsgT) : Words GE :=
  wordsOn S (tabAt S.codes arr seatAt S w)

/-- **One code table, one seat, one shape: the same words.** -/
theorem wordsBy_congr (seatAt seatAt' : ℕ → Option (ℕ × ℕ)) (S S' : Statement)
    (w : Wit Cells Tok MsgT) (o o' : ℕ) (hc : S'.codes = S.codes) (hs : seatAt' o' = seatAt o)
    (hx : (S'.oracles[o']?).map (·.shape) = (S.oracles[o]?).map (·.shape)) (part : Part) (i : ℕ) :
    wordsBy arr seatAt' S' w o' part i = wordsBy arr seatAt S w o part i := by
  unfold wordsBy
  refine wordsOn_congr S S' _ _ o o' hx ?_ part i
  rw [hc]
  exact tabAt_congr S.codes arr seatAt seatAt' S S' w o o' hs hx

/-! ## 2 The three chains' terms -/

/-- At the first chain's statement and book. -/
def wordsFirst (st : Statement) (book : TreeBook) (w : Wit Cells Tok MsgT) : Words GE :=
  wordsBy arr (seatBy noFirst book) st w

/-- At the shared chain's statement and book. t₁: the number of the first chain's trees. -/
def wordsShared (t₁ : ℕ) (st : Statement) (book : TreeBook) (w : Wit Cells Tok MsgT) : Words GE :=
  wordsBy arr (seatBy (noShared t₁) book) st w

/-- **At the last chain's record.** t₁, t₂: the numbers of the first and of the shared chain's
trees. -/
def wordsLast (t₁ t₂ : ℕ) (s : S₃) (w : Wit Cells Tok MsgT) : Words GE :=
  wordsBy arr (seatBy (noLast t₁ t₂ s.loc.firstTree) s.book) s.st w

end

/-- A later book that keeps o's place and its tree there gives o the same seat. -/
theorem seatBy_frame (no : ℕ → Tree → ℕ) (B B' : TreeBook) (o : ℕ)
    (hp : B'.place[o]? = B.place[o]?)
    (ht : ∀ q, B.place[o]? = some q → B'.trees[q.1]? = B.trees[q.1]?) :
    seatBy no B' o = seatBy no B o := by
  unfold seatBy
  rw [hp]
  cases hq : B.place[o]? with
  | none => rfl
  | some q => rw [Option.bind_some, Option.bind_some, ht q hq]

/-! ## 3 The fence, and the three laws behind the last chain's first block -/

/-- **THE BOOK-KEEPING IN FRONT OF AND BEHIND THE BLOCK.** o: the shared chain's end. -/
structure BookedLast (o : SharedOut) (s s' : S₃) : Prop where
  /-- the border in front holds that end -/
  border : ∃ g, s.loc.border = some ⟨g, o⟩
  /-- the tree that is about to be taken over is the one that firstTree counts -/
  first : s.book.trees.size + 1 = s.loc.firstTree
  /-- one table of codes -/
  codes : o.st.codes = s.st.codes
  bookSays : BookSays s s'
  sharp : Sharp s s'
  /-- every place of the book in front names a tree that is there -/
  placed : ∀ (i : ℕ) (q : ℕ × ℕ), s.book.place[i]? = some q → q.1 < s.book.trees.size
  /-- in the shared chain's book Omega is part 0 of its tree -/
  tenant : ∀ q : ℕ × ℕ, o.book.place[o.omega]? = some q → q.2 = 0

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ)

theorem firstTree_of_says (p : P₁₄) (s s' : S₃) (h : Says p s s') :
    s'.loc.firstTree = s.loc.firstTree := by
  obtain ⟨_, _, _, _, _, hl, _⟩ := h
  rw [hl]

/-- **(older) An older message's words are the same through both records**: at both tables, at every
index. -/
theorem words_older (p : P₁₄) (o : SharedOut) (s s' : S₃) (h : Says p s s') (hB : BookedLast o s s')
    (w : Wit Cells Tok MsgT) (n : ℕ) (hn : n < s.st.oracles.size) (part : Part) (i : ℕ) :
    wordsLast arr t₁ t₂ s' w n part i = wordsLast arr t₁ t₂ s w n part i := by
  obtain ⟨_, _, _, _, _, _, _, hsz, _, _, _, fp, ft⟩ := hB.bookSays
  unfold wordsLast
  refine wordsBy_congr arr _ _ s.st s'.st w n n (extends_of_says p s s' h).codes ?_ ?_ part i
  · rw [firstTree_of_says p s s' h]
    exact seatBy_frame _ s.book s'.book n (fp n (hsz ▸ hn))
      fun q hq => ft q.1 (hB.placed n q hq)
  · rw [VerifiableInference.Desc.Third.Law.old_message_back p s s' h n hn]

/-- **(omega) Omega's copy's words through the record behind are Omega's words through the shared
chain's end**: at both tables, at every index. -/
theorem words_omega (p : P₁₄) (o : SharedOut) (s s' : S₃) (h : Says p s s') (hB : BookedLast o s s')
    (w : Wit Cells Tok MsgT) (part : Part) (i : ℕ) :
    wordsLast arr t₁ t₂ s' w s.st.oracles.size part i =
      wordsShared arr t₁ o.st o.book w o.omega part i := by
  obtain ⟨g, hg⟩ := hB.border
  obtain ⟨x, q, t, q', hx, hq, ht, _, hq', _, ⟨tO, htO, hnum, _⟩, _, _⟩ := hB.bookSays
  obtain rfl : (⟨g, o⟩ : Border) = x := Option.some.inj (hg.symm.trans hx)
  have eq' : q' = (s.book.trees.size, 0) := Option.some.inj (hq'.symm.trans hB.sharp.2.2.2)
  subst eq'
  have h' : Says p s s' := h
  obtain ⟨x₂, y, _, _, hx₂, _, hy, _, _, hO, _⟩ := h
  obtain rfl : (⟨g, o⟩ : Border) = x₂ := Option.some.inj (hg.symm.trans hx₂)
  unfold wordsLast wordsShared
  refine wordsBy_congr arr _ _ o.st s'.st w o.omega s.st.oracles.size
    ((extends_of_says p s s' h').codes.trans hB.codes.symm) ?_ ?_ part i
  · exact seat_taken t₁ t₂ s'.loc.firstTree o.book s'.book o.omega s.st.oracles.size q _ t tO hq ht
      hq' htO (by rw [firstTree_of_says p s s' h']; exact hB.first) hnum (hB.tenant q hq).symm
  · rw [hO, hy]
    rfl

/-- **(first) Through the record in front, a message of the first chain has the words that it has
through that chain's own book.** -/
theorem words_first (o : SharedOut) (s s' : S₃) (hB : BookedLast o s s') (w : Wit Cells Tok MsgT)
    (n : ℕ) (part : Part) (i : ℕ) :
    wordsLast arr t₁ t₂ s w n part i = wordsFirst arr s.st s.book w n part i := by
  unfold wordsLast wordsFirst
  refine wordsBy_congr arr _ _ s.st s.st w n n rfl ?_ rfl part i
  exact seat_older t₁ t₂ s.loc.firstTree s.book s.book n rfl (fun _ _ => rfl)
    fun q _ hq _ => by have := hB.placed n q hq; have := hB.first; omega

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.wordsOn_congr
#print axioms VerifiableInference.Desc.Sound.wordsBy_congr
#print axioms VerifiableInference.Desc.Sound.words_older
#print axioms VerifiableInference.Desc.Sound.words_omega
#print axioms VerifiableInference.Desc.Sound.words_first
