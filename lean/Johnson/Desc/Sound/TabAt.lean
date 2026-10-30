-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TabAt.lean: THE WITNESS's TABLE OF THE MESSAGE THAT HAS THE NUMBER o IN A CHAIN's
STATEMENT, UNDER THAT CHAIN's BOOK. Definitions, and laws with their proofs.





  `seatBy no B o`: the seat of the message number o under the book B: (its tree's number through the
    file, its place among that tree's parts). no: from a tree's place in the book and its entry to
    its number through the file: `noFirst`, `noShared t₁`, `noLast t₁ t₂ firstTree`.
  `seat_older` (W1), `seat_taken` (W2): an older message, and the message that is taken over, have
    one seat under the two books.
  `tabAt cs arr seatAt S w o`: the one accessor `Wit.tab` (MsgSig.lean) at the shape that S has for
    o and at o's seat; the zero table where o has no seat or S no such message. `tabAt_congr`.
  `tab_laid` (W3), `tab_other`: against `LaidBy` (Johnson/Desc/Sound/WordsLaw.lean).

Limits. Nothing on soundness or on hiding. General in the books: no book is named.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement TreeBook Tree)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

/-! ## 1 The seat of a message under a book -/

/-- **The seat of the message number o under the book B**: (its tree's number through the file, its
place among that tree's parts). no: from a tree's place in the book and its entry there to its
number through the file. Nothing where the book has no place for o, or no tree at that place. -/
def seatBy (no : ℕ → Tree → ℕ) (B : TreeBook) (o : ℕ) : Option (ℕ × ℕ) :=
  (B.place[o]?).bind fun q => (B.trees[q.1]?).map fun T => (no q.1 T, q.2)

/-- The first chain's book: a tree's own number. -/
def noFirst : ℕ → Tree → ℕ := fun _ T => T.number

/-- The shared chain's book: behind the first chain's t₁ trees. -/
def noShared (t₁ : ℕ) : ℕ → Tree → ℕ := fun _ T => t₁ + T.number

/-- The last chain's book, BY THE TREE's PLACE IN THE BOOK: in front of place firstTree - 1 stand
the
first chain's trees; at it the one tree that is taken over from the shared chain, with the number
that it has there; behind it the chain's own, numbered from firstTree on. -/
def noLast (t₁ t₂ firstTree : ℕ) : ℕ → Tree → ℕ := fun z T =>
  if z + 1 < firstTree then T.number
  else if z + 1 = firstTree then t₁ + T.number
  else t₁ + t₂ + (T.number - firstTree)

theorem seatBy_some (no : ℕ → Tree → ℕ) (B : TreeBook) (o : ℕ) (q : ℕ × ℕ) (T : Tree)
    (hq : B.place[o]? = some q) (hT : B.trees[q.1]? = some T) :
    seatBy no B o = some (no q.1 T, q.2) := by
  unfold seatBy
  rw [hq, Option.bind_some, hT, Option.map_some]

/-- **(W1), of the seats: AN OLDER MESSAGE.** Where the later book has the earlier book's place for
o
and its tree there, and that tree stands in front of the one that is taken over: one seat. -/
theorem seat_older (t₁ t₂ firstTree : ℕ) (B B' : TreeBook) (o : ℕ)
    (hp : B'.place[o]? = B.place[o]?)
    (ht : ∀ q, B.place[o]? = some q → B'.trees[q.1]? = B.trees[q.1]?)
    (hz : ∀ q T, B.place[o]? = some q → B.trees[q.1]? = some T → q.1 + 1 < firstTree) :
    seatBy (noLast t₁ t₂ firstTree) B' o = seatBy noFirst B o := by
  unfold seatBy
  rw [hp]
  cases hq : B.place[o]? with
  | none => rfl
  | some q =>
    rw [Option.bind_some, Option.bind_some, ht q hq]
    cases hT : B.trees[q.1]? with
    | none => rfl
    | some T =>
      rw [Option.map_some, Option.map_some]
      unfold noLast noFirst
      rw [if_pos (hz q T hq hT)]

/-- **(W2), of the seats: THE MESSAGE THAT IS TAKEN OVER.** n: its number in the last chain's
statement; o: in the shared chain's. Where its tree stands at place firstTree - 1 of the last
chain's
book with the number that it has in the shared chain's, and it is the same part of it: one seat. -/
theorem seat_taken (t₁ t₂ firstTree : ℕ) (B₂ B' : TreeBook) (o n : ℕ) (q q' : ℕ × ℕ) (T T' : Tree)
    (hq : B₂.place[o]? = some q) (hT : B₂.trees[q.1]? = some T) (hq' : B'.place[n]? = some q')
    (hT' : B'.trees[q'.1]? = some T') (hz : q'.1 + 1 = firstTree) (hn : T'.number = T.number)
    (hp : q'.2 = q.2) :
    seatBy (noLast t₁ t₂ firstTree) B' n = seatBy (noShared t₁) B₂ o := by
  rw [seatBy_some _ B' n q' T' hq' hT', seatBy_some _ B₂ o q T hq hT]
  unfold noLast noShared
  rw [if_neg (by omega), if_pos hz, hn, hp]

/-! ## 2 The table -/

section
variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **THE WITNESS's TABLE OF THE MESSAGE NUMBER o OF THE STATEMENT S**: the one accessor (`Wit.tab`,
Johnson/Desc/Sound/MsgSig.lean) at the shape that S has for o, at the seat that seatAt gives it and
at the number that arr gives that seat. The zero table where o has no seat or S no such message. -/
def tabAt (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (w : Wit Cells Tok MsgT) (o : ℕ) : MsgT :=
  match seatAt o, S.oracles[o]? with
  | some q, some x => w.tab cs x.shape (arr q.1 q.2) q.1 q.2
  | _, _ => fun _ _ _ => 0

/-- **One seat and one shape: one table.** -/
theorem tabAt_congr (seatAt seatAt' : ℕ → Option (ℕ × ℕ)) (S S' : Statement)
    (w : Wit Cells Tok MsgT) (o o' : ℕ) (hs : seatAt' o' = seatAt o)
    (hx : (S'.oracles[o']?).map (·.shape) = (S.oracles[o]?).map (·.shape)) :
    tabAt cs arr seatAt' S' w o' = tabAt cs arr seatAt S w o := by
  unfold tabAt
  rw [hs]
  cases seatAt o with
  | none => rfl
  | some q =>
    cases h : S.oracles[o]? with
    | none =>
      rw [h, Option.map_none, Option.map_eq_none_iff] at hx
      rw [hx]
    | some x =>
      rw [h, Option.map_some] at hx
      obtain ⟨x', h', e⟩ := Option.map_eq_some_iff.1 hx
      rw [h']
      show w.tab cs x'.shape _ _ _ = w.tab cs x.shape _ _ _
      rw [e]

/-- **(W3): WHERE THE MEMBERS' COMPONENTS ARE LAID FROM A TUPLE OF MESSAGES, THE TABLE AT A MEMBER's
NUMBER IS ITS MESSAGE.** o: a number of the statement that has the member's seat and shape. -/
theorem tab_laid (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (mine : List Mem)
    (c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (w w' : Wit Cells Tok MsgT)
    (h : LaidBy cs arr mine c w w') (x : Mem) (hx : x ∈ mine) (o : ℕ)
    (hs : seatAt o = some (seatOf x))
    (hsh : (S.oracles[o]?).map (·.shape) = some (x.1.l.get x.2).1) :
    tabAt cs arr seatAt S w' o = toMsgT cs x.1.l x.2 (c x) := by
  obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hsh
  unfold tabAt
  rw [hs, hy]
  funext mask row place
  show (if padB cs y.shape mask row place = true then
      w'.pad (seatOf x).1 (seatOf x).2 mask row place
    else w'.msg (arr (seatOf x).1 (seatOf x).2) mask row place) = _
  split
  · exact congrFun (congrFun (congrFun (h.2.2.2.2.1 x hx) mask) row) place
  · exact congrFun (congrFun (congrFun (h.2.2.1 x hx) mask) row) place

/-- A message whose seat and number are no member's keeps its table. -/
theorem tab_other (seatAt : ℕ → Option (ℕ × ℕ)) (S : Statement) (mine : List Mem)
    (c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (w w' : Wit Cells Tok MsgT)
    (h : LaidBy cs arr mine c w w') (o : ℕ)
    (hs : ∀ q, seatAt o = some q → q ∉ mine.map seatOf ∧ arr q.1 q.2 ∉ mine.map (numOf arr)) :
    tabAt cs arr seatAt S w' o = tabAt cs arr seatAt S w o := by
  unfold tabAt
  cases hq : seatAt o with
  | none => rfl
  | some q =>
    cases S.oracles[o]? with
    | none => rfl
    | some y =>
      funext mask row place
      show (if padB cs y.shape mask row place = true then w'.pad q.1 q.2 mask row place
        else w'.msg (arr q.1 q.2) mask row place) =
        (if padB cs y.shape mask row place = true then w.pad q.1 q.2 mask row place
        else w.msg (arr q.1 q.2) mask row place)
      rw [h.2.2.2.2.2 q.1 q.2 (hs q hq).1, h.2.2.2.1 _ (hs q hq).2]

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seat_older
#print axioms VerifiableInference.Desc.Sound.seat_taken
#print axioms VerifiableInference.Desc.Sound.tabAt_congr
#print axioms VerifiableInference.Desc.Sound.tab_laid
#print axioms VerifiableInference.Desc.Sound.tab_other
