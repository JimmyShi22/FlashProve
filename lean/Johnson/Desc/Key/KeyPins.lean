-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyPins.lean: the key file's table of joints: the pin.
One definition and small theorems.

`Reading.enc` (Johnson/Desc/Msg.lean) is a relation. Members of `LaysReads` are built under stated
premises in KeyFillFamLays.lean (`fam_lays`) and KeyFillSrc.lean (`src_lays`); at other readings
none is shown. Nothing on soundness. (Where this and lean/THEOREM.md differ, the page holds.)

Other files' laws of a block take a letter, Pin a w, with two premises: (det) inside the promise, two
witnesses that are both pinned agree in what the block's rows read; (back) the pin goes back over the
block. Here that letter is filled by the table's own items, through the table's own relation.

  PinsAt ks cells     the pins of the witness's messages ks, and of the stored table where cells is
                      true: the table's relAt at just these items.
  pinsAt_of_rel       the relation at a border gives it, for the pins that are open there.
  table_fixed         one lemma a message: inside the promise, at an unmarked record, where pin k is
                      open: two witnesses that meet it name one table at message k's seat (pin_one,
                      Johnson/Desc/Msg.lean, at the promise's clause on collisions).
  read_fixed          so what the rows and named claims read of message k (KRead.of) is one, under
                      KeyTies.ReadsPinned.
  words_fixed         so the words at the statement's number of message k are one (KeyNums).
  cells_fixed | mat_fixed   two witnesses that meet pinT have one stored table's message.
  pins_det | pins_det_all   (det): what the rows read agrees. One term short of a kind's call: a kind's
                      (det) ends in its own agreement of its own reader (K13: AgreeAt idx (rw w) (rw w')):
                      that follows where rw factors through matOf and wordsOf and the state's own number
                      of the message is the plan's: no lemma here ends in it. pins_det_all is idle at
                      the first and the last chain at the real plans: at no border are all numbers of the
                      plan pinned and open.
  pin_of_pinsAt | pinW_of_pinsAt | noColl_of_on | hasSmp_of_on   the other road: for a kind that has
                      filled its pin in Msg.lean's own names: the table's items and promise in these names.
  pins_back           (back): where the reading's two letters agree at the two records and the
                      oracles that the pins read stay: KeyQuiet's rides_pin2 | rides_pinT2, item by item.
  pins_back'          the same under KeyLetters.PinsStay: the samples' agreement at the seats of ks alone.

At silly members. A marked record: the promise is free there: hence the premise that the record is
unmarked. Pin k not open: the promise holds nothing on collisions at k: hence hk. R.of := the bare
message: ReadsPinned fails wherever a pad's places are read: read_fixed is false without it. One seat
for all k: PinsAt [0, 1] pins one table twice: KeyTies.ArrOk forbids that, not this file.

For (back), who holds its premise: that the reading's letters agree at the two records (SamePins |
PinsStay) over a block's yes: at a block that draws (the batching) nobody holds it. (Where this
and lean/THEOREM.md differ, the page holds.)

What is not claimed: that anybody has a pin; that there is no collision; anything on a kind's typed
witness. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyNums
import Johnson.Desc.Key.KeyTies
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.Key.KeyLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)
  (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M))

/-- The items of the pins of the messages ks, and of the stored table where cells is true. -/
def pinItems (ks : List Nat) (cells : Bool) : List KItem :=
  ks.map KItem.pin ++ if cells then [KItem.pinT] else []

/-- **The kinds' letter, filled by the table's own items.** -/
def PinsAt (ks : List Nat) (cells : Bool) (a : P × S) (y : Strs) (w : Wit Cells Unit M) : Prop :=
  relAt F G at_ Mg (pinItems ks cells) a y w

theorem mem_pinItems_pin {ks : List Nat} {cells : Bool} {k : Nat} (h : k ∈ ks) :
    KItem.pin k ∈ pinItems ks cells :=
  List.mem_append_left _ (List.mem_map.2 ⟨k, h, rfl⟩)

theorem mem_pinItems_pinT {ks : List Nat} : KItem.pinT ∈ pinItems ks true :=
  List.mem_append_right _ (List.mem_singleton.2 rfl)

theorem of_mem_pinItems {ks : List Nat} {cells : Bool} {i : KItem} (h : i ∈ pinItems ks cells) :
    (∃ k ∈ ks, i = KItem.pin k) ∨ (cells = true ∧ i = KItem.pinT) := by
  rcases List.mem_append.1 h with h | h
  · obtain ⟨k, hk, e⟩ := List.mem_map.1 h
    exact Or.inl ⟨k, hk, e.symm⟩
  · cases cells with
    | true => exact Or.inr ⟨rfl, List.mem_singleton.1 h⟩
    | false => cases h

/-- **The relation at a border gives the pins that are open there.** -/
theorem pinsAt_of_rel {O : List KItem} {ks : List Nat} {cells : Bool} {a : P × S} {y : Strs}
    {w : Wit Cells Unit M} (h : relAt F G at_ Mg O a y w) (hk : ∀ k ∈ ks, KItem.pin k ∈ O)
    (hc : cells = true → KItem.pinT ∈ O) : PinsAt F G at_ Mg ks cells a y w := by
  intro i hi
  rcases of_mem_pinItems hi with ⟨k, hk', rfl⟩ | ⟨hc', rfl⟩
  · exact h _ (hk k hk')
  · exact h _ (hc hc')

/-- **One lemma a message**: inside the promise a pinned message's table is one. -/
theorem table_fixed {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {w w' : Wit Cells Unit M} {k : Nat} (hon : onAt F G at_ Mg shape free O a y)
    (hu : Mg.unmarked a) (hk : KItem.pin k ∈ O) (h : (KItem.pin k).holds F G at_ Mg a y w)
    (h' : (KItem.pin k).holds F G at_ Mg a y w') :
    msgOf G w (at_ k).1 (at_ k).2 = msgOf G w' (at_ k).1 (at_ k).2 := by
  rcases hon with hm | hon
  · exact absurd hu hm
  · exact pin_one F G _ _ a y w w' (hon.2.2.2 k (mem_pinned O k hk)) h h'

/-- So what the rows and the named claims read of message k is one. -/
theorem read_fixed {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {w w' : Wit Cells Unit M} {k : Nat} (R : KRead Cells M) {l : List Nat}
    (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a) (hk : KItem.pin k ∈ O)
    (h : (KItem.pin k).holds F G at_ Mg a y w) (h' : (KItem.pin k).holds F G at_ Mg a y w')
    (hr : ReadsPinned G at_ R l) (hl : k ∈ l) : R.of w k = R.of w' k := by
  rw [hr w k hl, hr w' k hl]
  exact table_fixed F G at_ Mg hon hu hk h h'

/-! ### The places of this file that open a notion of Johnson/Desc/Msg.lean. The table's own files hold
the like lemmas: KeyFrames.pinT_one (for cells_fixed) and KeyQuiet.rides_pin2_at | rides_pinT2_at
(for holds_pin_back | holds_pinT_back: the agreement asked at the one seat). -/

/-- Two witnesses that meet the stored table's pin have one stored table's message. -/
theorem cells_fixed {a : P × S} {y : Strs} {w w' : Wit Cells Unit M}
    (h : KItem.pinT.holds F G at_ Mg a y w) (h' : KItem.pinT.holds F G at_ Mg a y w') :
    w.cells = w'.cells := by
  obtain ⟨r, hr, hc⟩ := h
  obtain ⟨r', hr', hc'⟩ := h'
  have e : r' = r := Option.some.inj (hr'.symm.trans hr)
  rw [e] at hc'
  exact Option.some.inj (hc.symm.trans hc')

/-- Pin k goes back where the sample at its seat and its committed word stay. -/
theorem holds_pin_back {a a' : P × S} {y y' : Strs} {w : Wit Cells Unit M} {k : Nat}
    (e : G.smp a' (at_ k).1 (at_ k).2 = G.smp a (at_ k).1 (at_ k).2)
    (hw : wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2)
    (h : (KItem.pin k).holds F G at_ Mg a' y' w) : (KItem.pin k).holds F G at_ Mg a y w := by
  obtain ⟨o, z, h1, h2, h3⟩ := h
  exact ⟨o, z, h1, e.symm.trans h2, (member_congr F G o _ _ y y' z _ hw).1 h3⟩

/-- The stored table's pin goes back where its record and the cells' oracle stay. -/
theorem holds_pinT_back {a a' : P × S} {y y' : Strs} {w : Wit Cells Unit M}
    (e : G.recOf a' = G.recOf a) (hc : y'.cell = y.cell)
    (h : KItem.pinT.holds F G at_ Mg a' y' w) : KItem.pinT.holds F G at_ Mg a y w := by
  obtain ⟨r, h1, h2⟩ := h
  exact ⟨r, e.symm.trans h1, hc ▸ h2⟩

/-! ### FOR A KIND's FILLING: the table's items and promise, handed out IN Msg.lean's OWN NAMES: by
unfolding alone. A kind that has filled its letter Pin in these names (PinList.lean, not in this library:
PinL := PINW ∧ PIN at the seat of the index masks' message · onL := … ∧ NoColl at that seat) takes its
two premises from here: PinL from pinW_of_pinsAt and pin_of_pinsAt at seat idx := at_ 0; onL's second
half from noColl_of_on. -/

theorem pin_of_pinsAt {ks : List Nat} {cells : Bool} {a : P × S} {y : Strs} {w : Wit Cells Unit M}
    {k : Nat} (h : PinsAt F G at_ Mg ks cells a y w) (hk : k ∈ ks) :
    PIN F G (at_ k).1 (at_ k).2 a y w := h _ (mem_pinItems_pin hk)

theorem pinW_of_pinsAt {ks : List Nat} {a : P × S} {y : Strs} {w : Wit Cells Unit M}
    (h : PinsAt F G at_ Mg ks true a y w) : PINW G a y w := h _ mem_pinItems_pinT

theorem noColl_of_on {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {k : Nat} (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a)
    (hk : KItem.pin k ∈ O) : NoColl F G (at_ k).1 (at_ k).2 a y := by
  rcases hon with hm | hon
  · exact absurd hu hm
  · exact hon.2.2.2 k (mem_pinned O k hk)

theorem hasSmp_of_on {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {k : Nat} (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a)
    (hk : KItem.pin k ∈ O) : hasSmp G (at_ k).1 (at_ k).2 a = true := by
  rcases hon with hm | hon
  · exact absurd hu hm
  · exact List.all_eq_true.1 hon.2.1 k (mem_pinned O k hk)

/-- **(back), at the seats of ks alone** (KeyLetters.PinsStay: a in front, a' behind). -/
theorem pins_back' {ks : List Nat} {cells : Bool} {a a' : P × S} {y y' : Strs}
    {w : Wit Cells Unit M} (H : PinsStay G at_ ks a a')
    (hw : ∀ k ∈ ks, wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2)
    (hc : cells = true → y'.cell = y.cell) (h : PinsAt F G at_ Mg ks cells a' y' w) :
    PinsAt F G at_ Mg ks cells a y w := by
  intro i hi
  rcases of_mem_pinItems hi with ⟨k, hk, rfl⟩ | ⟨hc', rfl⟩
  · exact holds_pin_back F G at_ Mg (H.smp k hk) (hw k hk) (h _ hi)
  · exact holds_pinT_back F G at_ Mg H.recOf (hc hc') (h _ hi)

/-- **(back)**: the pins go back where the reading's letters and the oracles that they read stay. -/
theorem pins_back {ks : List Nat} {cells : Bool} {a a' : P × S} {y y' : Strs}
    {w : Wit Cells Unit M} (H : SamePins G a a')
    (hw : ∀ k ∈ ks, wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2)
    (hc : cells = true → y'.cell = y.cell) (h : PinsAt F G at_ Mg ks cells a' y' w) :
    PinsAt F G at_ Mg ks cells a y w := by
  intro i hi
  rcases of_mem_pinItems hi with ⟨k, hk, rfl⟩ | ⟨hc', rfl⟩
  · exact rides_pin2 F G _ _ a a' y y' w H (hw k hk) (h _ hi)
  · exact rides_pinT2 G a a' y y' w H (hc hc') (h _ hi)

end

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE) {XI P S Cells M Smp Rec : Type}
  (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec) (at_ : Where)
  (Mg : KMeaning P S (Wit Cells Unit M)) (K : KPlan) (R : KRead Cells M)

/-- So the words at the statement's number of message k are one. -/
theorem words_fixed {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {w w' : Wit Cells Unit M} {k o : Nat} {l : List Nat}
    (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a) (hk : KItem.pin k ∈ O)
    (h : (KItem.pin k).holds F G at_ Mg a y w) (h' : (KItem.pin k).holds F G at_ Mg a y w')
    (hr : ReadsPinned G at_ R l) (hl : k ∈ l) (hn : K.num o = some k) :
    wordsOf ρ K R w o = wordsOf ρ K R w' o := by
  rw [wordsOf_num ρ K R w hn, wordsOf_num ρ K R w' hn,
    read_fixed F G at_ Mg R hon hu hk h h' hr hl]

/-- The matrix, as the table reads it off the witness, is one. -/
theorem mat_fixed {a : P × S} {y : Strs} {w w' : Wit Cells Unit M}
    (h : KItem.pinT.holds F G at_ Mg a y w) (h' : KItem.pinT.holds F G at_ Mg a y w') :
    matOf K R w = matOf K R w' := by
  unfold matOf
  rw [cells_fixed F G at_ Mg h h']

/-- **(det), in the kinds' shape.** -/
theorem pins_det {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {w w' : Wit Cells Unit M} {ks : List Nat} {cells : Bool}
    (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a)
    (hO : ∀ k ∈ ks, KItem.pin k ∈ O) (hr : ReadsPinned G at_ R ks)
    (h : PinsAt F G at_ Mg ks cells a y w) (h' : PinsAt F G at_ Mg ks cells a y w') :
    (∀ o k, K.num o = some k → k ∈ ks → wordsOf ρ K R w o = wordsOf ρ K R w' o) ∧
      (cells = true → matOf K R w = matOf K R w') := by
  refine ⟨fun o k hn hk => ?_, fun hc => ?_⟩
  · exact words_fixed ρ F G at_ Mg K R hon hu (hO k hk) (h _ (mem_pinItems_pin hk))
      (h' _ (mem_pinItems_pin hk)) hr hk hn
  · subst hc
    exact mat_fixed F G at_ Mg K R (h _ mem_pinItems_pinT) (h' _ mem_pinItems_pinT)

/-- Where every number of the plan is a pinned message's, the words are one outright. -/
theorem pins_det_all {shape : S → Bool} {free : P × S → Strs → Prop} {O : List KItem} {a : P × S}
    {y : Strs} {w w' : Wit Cells Unit M} {ks : List Nat} {cells : Bool}
    (hon : onAt F G at_ Mg shape free O a y) (hu : Mg.unmarked a)
    (hO : ∀ k ∈ ks, KItem.pin k ∈ O) (hr : ReadsPinned G at_ R ks)
    (hall : ∀ o k, K.num o = some k → k ∈ ks)
    (h : PinsAt F G at_ Mg ks cells a y w) (h' : PinsAt F G at_ Mg ks cells a y w') :
    wordsOf ρ K R w = wordsOf ρ K R w' := by
  funext o
  cases hn : K.num o with
  | some k => exact (pins_det ρ F G at_ Mg K R hon hu hO hr h h').1 o k hn (hall o k hn)
  | none => rw [wordsOf_none ρ K R w hn, wordsOf_none ρ K R w' hn]

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.mem_pinItems_pin
#print axioms VerifiableInference.Desc.Key.mem_pinItems_pinT
#print axioms VerifiableInference.Desc.Key.of_mem_pinItems
#print axioms VerifiableInference.Desc.Key.pinsAt_of_rel
#print axioms VerifiableInference.Desc.Key.table_fixed
#print axioms VerifiableInference.Desc.Key.read_fixed
#print axioms VerifiableInference.Desc.Key.cells_fixed
#print axioms VerifiableInference.Desc.Key.pins_back
#print axioms VerifiableInference.Desc.Key.words_fixed
#print axioms VerifiableInference.Desc.Key.mat_fixed
#print axioms VerifiableInference.Desc.Key.pins_det
#print axioms VerifiableInference.Desc.Key.pins_det_all
#print axioms VerifiableInference.Desc.Key.holds_pin_back
#print axioms VerifiableInference.Desc.Key.holds_pinT_back
#print axioms VerifiableInference.Desc.Key.pins_back'
#print axioms VerifiableInference.Desc.Key.pin_of_pinsAt
#print axioms VerifiableInference.Desc.Key.pinW_of_pinsAt
#print axioms VerifiableInference.Desc.Key.noColl_of_on
#print axioms VerifiableInference.Desc.Key.hasSmp_of_on
