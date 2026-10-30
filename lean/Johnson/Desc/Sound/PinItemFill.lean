-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PinItemFill.lean: THE PIN BY A DECODER WITH A SAMPLE AS A `PinItemP`. A
definition and theorems, proved.

`PinItemP` (Johnson/Desc/First/Att/K05PinP.lean) is the form in which the law of the attention's
kind takes "an item of a border that pins the world's part". Here it is filled with the pin of
Johnson/Desc/Sound/MsgSig.lean (`PinAt`: the record holds the member's sample, every leaf of its
word is shown, and the library's decoder, at the word off the strings and that sample, gives the
witness's message), at any list l of shapes with radii and any seats.
  `colAt_below`, `wordOf_below`, `wordsOf_below`, `shownAt_below` (proved): what `SameBelow` leaves
    alone: the column, the committed word, the member's word (equations); and "every leaf is shown"
    (one way: from y' to y), at a tree below the base.
  `pinAt_below` (proved): so a member's pin, where its tree lies below the base.
  `pinAt_same` (proved): two witnesses pinned at one member, record and strings have one message
    there.
  `pinItemOf`: **THE FILLING**: Rc := the record's oracle messages and its book; ok := True (a pin
    by a decoder fixes outright: the promise's slot is free); holds := every member of l is pinned;
    part := the witness's typed messages (`msgsOf`); fixes by `pinAt_same`; fenced by `pinAt_below`;
    lay: a premise: the seat's lay keeps the record's oracle messages and its book.
  `pinItemOf_ok` (proved, by unfolding): its clause on the promise holds everywhere.
Limits. smp (how a member's sample is read off the record's oracle messages and book), seat, arr, l
are letters. hlow: every member's tree lies below the base: a premise. hlay: a premise (at the
attention's seat:
`seatSO_keeps_oracles_book`, Johnson/Desc/First/Att/K05SeatKeepsPin.lean: not imported here). SILLY
FILLINGS ARE NOT SHUT OUT BY THE FORM: at smp := none nothing is pinned and the item is false of
every witness. Nothing says that a border's table hands this item. Called at no value.
(Where this and lean/THEOREM.md differ, the page
holds.) Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.First.Att.K05PinP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc.First.Att.P (SameBelow PinItemP Seat)

theorem colAt_below (F : Frame) (base : ℕ) (y y' : F.E.Str) (h : SameBelow F base y y') (j x : ℕ)
    (hj : j < base) : colAt F y' j x = colAt F y j x := by
  unfold colAt
  rw [h.2 j x hj]

theorem wordOf_below {Xi : Type} (G : FileDescription Xi) (F : Frame) (base : ℕ) (y y' : F.E.Str)
    (h : SameBelow F base y y') (j t : ℕ) (hj : j < base) :
    wordOf G (strsOf F y') j t = wordOf G (strsOf F y) j t := by
  funext x
  show (G.oracleAt j).bind (fun o => o.cut t (colAt F y' j x)) = _
  rw [colAt_below F base y y' h j x hj]
  rfl

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat : Fin l.length → ℕ × ℕ)

theorem wordsOf_below (F : Frame) (base : ℕ) (y y' : F.E.Str) (h : SameBelow F base y y')
    (i : Fin l.length) (hi : (seat i).1 < base) :
    wordsOf G cs l seat (strsOf F y') i = wordsOf G cs l seat (strsOf F y) i := by
  have e := wordOf_below G F base y y' h (seat i).1 (seat i).2 hi
  funext p
  cases p with
  | inl x =>
    funext r
    show rowAt _ (((wordOf G (strsOf F y') (seat i).1 (seat i).2 x.val).map (·.main)).getD [])
      r.1.val = rowAt _ (((wordOf G (strsOf F y) (seat i).1 (seat i).2 x.val).map (·.main)).getD [])
      r.1.val
    rw [e]
  | inr x =>
    funext r
    show rowAt false (((wordOf G (strsOf F y') (seat i).1 (seat i).2 x.val).map (·.mask)).getD [])
      r.1.val =
      rowAt false (((wordOf G (strsOf F y) (seat i).1 (seat i).2 x.val).map (·.mask)).getD [])
        r.1.val
    rw [e]

theorem shownAt_below (F : Frame) (base : ℕ) (y y' : F.E.Str) (h : SameBelow F base y y')
    (i : Fin l.length) (hi : (seat i).1 < base) (hs : ShownAt G cs l seat (strsOf F y') i) :
    ShownAt G cs l seat (strsOf F y) i := by
  intro x hx
  rw [← wordOf_below G F base y y' h _ _ hi]
  exact hs x hx

variable {A Cells Tok : Type} (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp)
  (arr : ℕ → ℕ → ℕ)

/-- A member's pin reads the strings at its own tree alone. -/
theorem pinAt_below (F : Frame) (base : ℕ) (y y' : F.E.Str) (h : SameBelow F base y y')
    (i : Fin l.length) (hi : (seat i).1 < base) (a : A) (w : Wit Cells Tok MsgT)
    (hp : PinAt G cs l seat smp arr i a (strsOf F y') w) :
    PinAt G cs l seat smp arr i a (strsOf F y) w := by
  obtain ⟨z, hz, hs, hd⟩ := hp
  refine ⟨z, hz, shownAt_below G cs l seat F base y y' h i hi hs, ?_⟩
  rw [← wordsOf_below G cs l seat F base y y' h i hi]
  exact hd

/-- Two witnesses pinned at one member, record and strings have one message there. -/
theorem pinAt_same (i : Fin l.length) (a : A) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (h : PinAt G cs l seat smp arr i a y w) (h' : PinAt G cs l seat smp arr i a y w') :
    msgsOf cs l seat arr w i = msgsOf cs l seat arr w' i := by
  obtain ⟨z, hz, -, hd⟩ := h
  obtain ⟨z', hz', -, hd'⟩ := h'
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  exact Option.some.inj (hd.symm.trans hd')

end

/-- **THE FILLING.** -/
def pinItemOf {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {Cells Tok : Type}
    (smp : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin l.length) →
      Option ((sigOf cs l).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (F : Frame) (st : Seat First.S) (base : ℕ)
    (hlow : ∀ i, (seat i).1 < base)
    (hlay : ∀ s h Gk s', st.lay s h Gk = some s' →
      (s'.st.oracles, s'.book) = (s.st.oracles, s.book)) :
    PinItemP F st base (Wit Cells Tok MsgT) (sigOf cs l).Msg where
  Rc := Array OnBytes.Oracle × OnBytes.TreeBook
  rc := fun s => (s.st.oracles, s.book)
  ok := fun _ _ => True
  holds := fun r y w => ∀ i, PinAt G cs l seat smp arr i r (strsOf F y) w
  part := fun w => msgsOf cs l seat arr w
  fixes := fun r y w w' _ h h' => funext fun i =>
    pinAt_same G cs l seat smp arr i r (strsOf F y) w w' (h i) (h' i)
  lay := hlay
  fenced := fun r y y' w hb h i =>
    pinAt_below G cs l seat smp arr F base y y' hb i (hlow i) r w (h i)

theorem pinItemOf_ok {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)
    (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) {Cells Tok : Type}
    (smp : Array OnBytes.Oracle × OnBytes.TreeBook → (i : Fin l.length) →
      Option ((sigOf cs l).om i).Smp)
    (arr : ℕ → ℕ → ℕ) (F : Frame) (st : Seat First.S) (base : ℕ)
    (hlow : ∀ i, (seat i).1 < base)
    (hlay : ∀ s h Gk s', st.lay s h Gk = some s' →
      (s'.st.oracles, s'.book) = (s.st.oracles, s.book)) (r) (y : F.E.Str) :
    (pinItemOf (Cells := Cells) (Tok := Tok) G cs l seat smp arr F st base hlow hlay).ok r y :=
  trivial

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pinAt_below
#print axioms VerifiableInference.Desc.Sound.pinAt_same
#print axioms VerifiableInference.Desc.Sound.pinItemOf
#print axioms VerifiableInference.Desc.Sound.pinItemOf_ok
