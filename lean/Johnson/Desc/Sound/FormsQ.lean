-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsQ.lean: four sentences of the table of joints of the proof file's first
chain: "the forms of a run are worth 0" (twice) and "the one equation's sum is 0" (twice), as
sentences on the carried record and the witness's tables. Definitions of type Prop, public tests
with code (in the storey below: Johnson/Desc/First/Batch/FormsIn.lean), and small theorems.

Why. The record `Meaning` (Johnson/Desc/First/Borders.lean) has four letters forms, formsT, totalB,
total. Johnson/Desc/Sound/BordersForms.lean fills them with the sentences of this file.

How the witness is read: one accessor, `tabQ`. rd: the witness's own reader: a seat (tree, tenant) ↦
that copy's table: mask row or main row, row, place. The record's book of trees says at which seat
oracle message number o of the record's statement sits. Entry J of a table of o is rd's table at
row J % 2 ^ R, place J / 2 ^ R, R the table's row bits (the row's bits are the low ones:
OnBytes/Iop/Ground.lean, `tableBits`). own: the seats that the sentence may read: a message that
sits elsewhere reads as 0; the public tests of Johnson/Desc/First/Batch/FormsIn.lean say that this
is asked nowhere.
  `dataQ`: the arrays' cells and the segment's mask row off these tables, by the plan's layout: kind
    K9's `dataOf` (Johnson/Desc/First/Batch/Law/AsRow.lean), called.

Two worlds (`World`, OnBytes/Model/HideLaws.lean). Under slot j both have
shown_j - factor_j * (entry j of the mask row). For the sum shown and factor are the ledger's
(`Fork.worldOf`, called). For the forms they are the ledger's too, but at a late slot: one that the
run itself fills only at the batching's place: there they are what the run's reader says that the
run will lay (`slotW`): at the earlier borders the ledger holds nothing under such a slot.
`slotW_filled`: where the slot is filled and the test `lateOk` holds, the two are one.
  `worldOwn`: for the forms: "entry i of row r of array t" is cell (r, i) of the witness's array
    itself: its own row.
  `worldSum`: for the sum: kind K9's `worldAt`: "row r" is a virtual row: the ledger's own
    weights coef on the array's rows.
Why two. The ledger's weights coef are empty until the step behind the adding lays them
(Johnson/Desc/First/TailClaims/Coefficients.lean); some are made of what the lookup on the digits
returned, some are powers of the batching's own draw. At every border at which an item "forms" is
open a world of virtual rows would read each entry as 0. So a form's meaning names no virtual row.

The sentences. Each says "a segment is open"; that it is segment m, whose seats own are, is the
promise's.
  `formsQ`: the run's reader gives its forms and late slots at the record; the late slots are free
    or hold just what it says (`lateOk`); each form names only what is there (`affIn`), and is worth
    0 in `worldOwn`.
  `formsTQ`: the same in front of the segment's second sending: own: the first sending's seats; the
    data are passed through `Stated.at1`; an entry may also name an array of the second sending
    (`entInT`).
  `totalQ`: the ledger's sum (`Fork.total`) is 0 in `worldSum`.
  `totalBQ`: the runs behind the batching return a record; there the ledger names only what is
    there (`totalIn`), and `totalQ` holds.
`totalQ_iff` writes `totalQ` out. It is meant to be, at kind K9's letter tab, "a part is there, and
oneK atS rho s s (dataAt atS s tab) = 0", in which that kind's law's rows end: a theorem
says so, at rho := `Reading.gl` and tab := `tabAt own rd s`: `total_iff`
(Johnson/Desc/First/Batch/Law/AtTable.lean, which imports this file:
it is not imported here).

For the promise: public tests, no witness in them (Johnson/Desc/First/Batch/FormsIn.lean; no
Mathlib, so that a run can evaluate them): `formsIn`, `formsInT`: the reader gives its forms, each
names only what is there: at every border at which the item is open: the block that closes the item
must deliver it, so the promise must hold it. `totalIn`: the ledger's sizes fit, the mask row and
every array are there, every virtual row has its weights: at total's borders alone (behind the runs
behind the batching). At totalB's border no promise can hold it: the weights are still empty, and
the runs behind are a later run, which may refuse: a block's promise behind must follow from its own
yes. So there the test stands inside the sentence, under its "there is a record that the runs
return".

What rides. `formsQ_rides`, `formsTQ_rides`: from the sentence at a later record of the segment to
the sentence at an earlier one, at one witness, where the test holds at the earlier record, the
reader gives one answer (for formsT also: the stated data agree at both records at the cells and the
mask row's entries that the forms name: a premise on that letter), and the later part `Rides` on the
earlier: the arrays' names and the layout are the same; a message that was sent, the mask row's
message, a seat in the book and a seated table's bits stay; at a slot under which a value has been
put what was shown and the factor stay. (`Fork.hide` refuses a filled slot: that guard is what can
pay the last clause; no block is shown to meet `Rides` here.)

Two letters stay, and they bear the weight.
  `Readers.forms piece run s`: the reader: the forms of that run as a plain function of the record:
    over the arrays' own rows, with public coefficients; nothing where the record does not hold them
    (the sentence fails there: `formsQ_unread`). Each hearing kind gives its own.
    It must give one list at every border at which the item is open: so it may read only what was
    heard in front of the item's opening. For the smallness test's run it is the family of single
    equations, not the sums over powers of the draw that the program adds. That the claims which the
    run makes at the batching's place add up to these forms is the batching's law's premise on a
    run (kind K9's `AddOk`): not said here. Nor that the run lays just `late`: in front of
    the filling nothing here ties these values to the run: with `K9.readerOf`
    (Johnson/Desc/First/Batch/ReaderOf.lean: the reader is the run itself) it is so by the make.
  `Stated.at1 s D`: the data D with each array of the second sending set to its stated function of
    the first sending's arrays: the smallness test's formula.

Silly members. No segment open: all fail (`none_fails`). A form that names an array, a cell or a
slot that is not there, or the slot of the merge's end value (its scalar is masked by the index
masks' message, not by the segment's mask row: `K9.mergeOf`): `formsQ` fails (`formsQ_outside`): if
a run's forms name that slot the item fails aloud and the table's row must turn (at the small stored
proof's two feed-forward segments no run's claims name it: by a run). A silly reader (late := every
free slot that a form names, at values of its liking) makes the tests true and a form in slots alone
worth what it likes: the tests say nothing on the run: but an item has two sides at one reader: its
closer must give it from the sum at the real ledger: at silly values that law cannot be had. At a
reader that gives the empty list the sentence holds of every witness (`formsQ_nil`): the item is
idle there, the table is not: the closer's law is free, and the opener's, which must give its own
items in front from these forms behind, cannot be had.

Limits: (1) Nothing says that any block meets these sentences. (2) `dataOf` reads a cell as a sum
over the layout's blocks; that it is the table's entry at the one place where the layout lays the
cell (Johnson/Desc/LaidAt.lean, `laidAt`) is typed nowhere. (Where this and
lean/THEOREM.md differ, the page holds.)
(3) OnBytes/Model/HideLaws.lean says of itself that no theorem on the program's decision rests on
it: its measures are called here as definitions. Nothing on acceptance. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.Law.AsRow
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS segAt? segAt_of_atS seatAt seatAt_mem seatAt_rides arrayIn
  arrayIn_some entIn entIn_some maskAt maskSeat lateAt lateOk slotIn affIn affInT Read Readers
  formsIn formsInT totalIn)
open VerifiableInference.Desc.K9L (Bound dataOf worldAt maskOracle)
open VerifiableInference.Desc.First (S)

/-- The field. -/
abbrev GQ : Type := Cb.Gl.E

/-- A table of the witness: mask row or main row, row, place. -/
abbrev MsgQ : Type := Bool → ℕ → ℕ → GQ

/-! ## 1 The one accessor -/

section
variable (own : List (ℕ × ℕ))

/-- **THE ONE ACCESSOR: entry J of the main or the mask table of oracle message number o.** -/
def tabQ (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd : ℕ × ℕ → MsgQ) (o : ℕ)
    (part : OnBytes.Part) (J : ℕ) : GQ :=
  match seatAt own book o with
  | some x => rd x (part == .mask) (J % 2 ^ st.rowBits o part) (J / 2 ^ st.rowBits o part)
  | none => 0

/-- It reads the witness at own's seats alone. -/
theorem tabQ_congr (st : OnBytes.Statement) (book : OnBytes.TreeBook) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ x ∈ own, rd x = rd' x) : tabQ own st book rd = tabQ own st book rd' := by
  funext o part J
  unfold tabQ
  cases e : seatAt own book o with
  | none => rfl
  | some x =>
    show rd x _ _ _ = rd' x _ _ _
    rw [h x (seatAt_mem own book o x e)]

/-- At a seated message the later record's table is the earlier one's. -/
theorem tabQ_rides (st st' : OnBytes.Statement) (book book' : OnBytes.TreeBook)
    (rd : ℕ × ℕ → MsgQ) (o : ℕ) (x : ℕ × ℕ) (part : OnBytes.Part)
    (e : seatAt own book o = some x) (e' : seatAt own book' o = some x)
    (hr : st'.rowBits o part = st.rowBits o part) :
    tabQ own st' book' rd o part = tabQ own st book rd o part := by
  funext J
  unfold tabQ
  rw [e, e', hr]

/-- The arrays' cells and the segment's mask row, off the witness's tables. -/
def dataQ (a : K9.Part) (rd : ℕ × ℕ → MsgQ) : Bound GQ :=
  dataOf a.L.check.rows a.L.check.frame a.d.st (tabQ own a.d.st a.d.book rd)

theorem dataQ_congr (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ) (h : ∀ x ∈ own, rd x = rd' x) :
    dataQ own a rd = dataQ own a rd' := by
  unfold dataQ
  rw [tabQ_congr own a.d.st a.d.book rd rd' h]

end

/-! ## 2 The two worlds -/

/-- The hidden value under slot j, for the forms: at a late slot by what the run will lay, elsewhere
by the ledger. -/
def slotW (F : Fork) (late : List (ℕ × E × E)) (mask : ℕ → GQ) (j : ℕ) : GQ :=
  match lateAt late j with
  | some y => Reading.gl.val y.1 - Reading.gl.val y.2 * mask j
  | none => Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * mask j

theorem slotW_late (F : Fork) (late : List (ℕ × E × E)) (mask : ℕ → GQ) (j : ℕ) (y : E × E)
    (e : lateAt late j = some y) :
    slotW F late mask j = Reading.gl.val y.1 - Reading.gl.val y.2 * mask j := by
  unfold slotW
  rw [e]

theorem slotW_ledger (F : Fork) (late : List (ℕ × E × E)) (mask : ℕ → GQ) (j : ℕ)
    (e : lateAt late j = none) :
    slotW F late mask j =
      Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * mask j := by
  unfold slotW
  rw [e]

/-- **The world of the forms**: row r of array t is the array's own row r. -/
def worldOwn (a : K9.Part) (late : List (ℕ × E × E)) (D : Bound GQ) : World GQ where
  slot := slotW a.F late D.mask
  entry := fun t r i =>
    match a.L.arrayOf[t]? with
    | some b => D.cell b.1 b.2 r i
    | none => 0

/-- **The world of the sum**: row r of array t is the ledger's virtual row r. -/
def worldSum (a : K9.Part) (D : Bound GQ) : World GQ := worldAt Reading.gl a.L a.F D

/-- A form's worth reads a world at the entries and the slots that the form names, and nowhere
else. -/
theorem value_eq (W W' : World GQ) (f : Aff)
    (he : ∀ x ∈ f.ents.toList, W.entry x.tree x.row x.idx = W'.entry x.tree x.row x.idx)
    (hs : ∀ x ∈ f.slots.toList, W.slot x.1 = W'.slot x.1) :
    f.value Reading.gl W = f.value Reading.gl W' := by
  have h1 : f.ents.toList.map (Ent.value Reading.gl W) =
      f.ents.toList.map (Ent.value Reading.gl W') :=
    List.map_congr_left fun x hx => by
      unfold Ent.value
      rw [he x hx]
  have h2 : f.slots.toList.map (slotValue Reading.gl W) =
      f.slots.toList.map (slotValue Reading.gl W') :=
    List.map_congr_left fun x hx => by
      unfold slotValue
      rw [hs x hx]
  unfold Aff.value
  rw [h1, h2]

/-! ## 3 The storey below -/

/-- The lower storey's reader of the mask row's message is kind K9's. -/
theorem maskAt_eq (f : ReqFrame) : maskAt f = maskOracle f := rfl

/-- Where a slot is filled and the late slots are as the test asks, the forms' world has under it
what the ledger's own world has. -/
theorem slotW_filled (a : K9.Part) (late : List (ℕ × E × E)) (mask : ℕ → GQ) (j : ℕ)
    (h : lateOk late a = true) (hg : a.F.gotF.getD j false = true) :
    slotW a.F late mask j =
      Reading.gl.val (a.F.vp.getD j zeroE) - Reading.gl.val (a.F.mf.getD j zeroE) * mask j := by
  cases e : lateAt late j with
  | none => exact slotW_ledger a.F late mask j e
  | some y =>
    rw [slotW_late a.F late mask j y e]
    unfold lateAt at e
    obtain ⟨x, hx, hy⟩ := Option.map_eq_some_iff.1 e
    have hj : x.1 = j := by
      have h0 := List.find?_some hx
      exact of_decide_eq_true (by simpa using h0)
    have hm : x ∈ late := List.mem_of_find?_eq_some hx
    unfold lateOk at h
    have h1 := List.all_eq_true.1 h x hm
    obtain ⟨_, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h1
    rw [hj, hg] at h2
    have h3 : (decide (a.F.vp.getD j zeroE = x.2.1) &&
        decide (a.F.mf.getD j zeroE = x.2.2)) = true := h2
    obtain ⟨h4, h5⟩ := Eq.mp (Bool.and_eq_true _ _) h3
    rw [of_decide_eq_true h4, of_decide_eq_true h5, hy]

/-! ## 4 The second letter (the first, `Readers`, stands in the storey below) -/

/-- The data with each array of the segment's second sending set to its stated function of the first
sending's arrays. -/
structure Stated where
  at1 : S → Bound GQ → Bound GQ

/-! ## 5 The four sentences, and the tests for the promise -/

section
variable (Rd : Readers) (St : Stated) (after : S → Except String S) (own : List (ℕ × ℕ))

/-- **forms.** -/
def formsQ (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  ∃ a R, segAt? s = some a ∧ Rd.forms piece run s = some R ∧ lateOk R.late a = true ∧
    ∀ f ∈ R.forms, affIn own (K9.mergeOf s) R.late a f = true ∧
      f.value Reading.gl (worldOwn a R.late (dataQ own a rd)) = 0

/-- **formsT.** own: the first sending's seats. -/
def formsTQ (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  ∃ a R, segAt? s = some a ∧ Rd.forms piece run s = some R ∧ lateOk R.late a = true ∧
    ∀ f ∈ R.forms, affInT own (K9.mergeOf s) R.late a f = true ∧
      f.value Reading.gl (worldOwn a R.late (St.at1 s (dataQ own a rd))) = 0

/-- **total.** -/
def totalQ (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  ∃ a, atS.get? s = some a ∧ a.F.total Reading.gl (worldSum a (dataQ own a rd)) = 0

/-- **totalB.** after: the runs behind the batching, one after the other. -/
def totalBQ (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  ∃ s', after s = .ok s' ∧ totalIn own s' = true ∧ totalQ own s' rd

/-- The sentence holds the test. -/
theorem formsQ_in (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ)
    (h : formsQ Rd own piece run s rd) : formsIn Rd own piece run s = true := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := h
  unfold formsIn
  rw [ha, hs]
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hm => (hf f hm).1⟩

/-! ## 6 They read the witness at own's seats alone -/

theorem formsQ_congr (piece : ℕ) (run : String) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ x ∈ own, rd x = rd' x) (hw : formsQ Rd own piece run s rd) :
    formsQ Rd own piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, ?_⟩
  rw [← dataQ_congr own a rd rd' h]
  exact hf

theorem formsTQ_congr (piece : ℕ) (run : String) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ x ∈ own, rd x = rd' x) (hw : formsTQ Rd St own piece run s rd) :
    formsTQ Rd St own piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, ?_⟩
  rw [← dataQ_congr own a rd rd' h]
  exact hf

theorem totalQ_congr (s : S) (rd rd' : ℕ × ℕ → MsgQ) (h : ∀ x ∈ own, rd x = rd' x)
    (hw : totalQ own s rd) : totalQ own s rd' := by
  obtain ⟨a, ha, hf⟩ := hw
  refine ⟨a, ha, ?_⟩
  rw [← dataQ_congr own a rd rd' h]
  exact hf

theorem totalBQ_congr (s : S) (rd rd' : ℕ × ℕ → MsgQ) (h : ∀ x ∈ own, rd x = rd' x)
    (hw : totalBQ after own s rd) : totalBQ after own s rd' := by
  obtain ⟨s', hs, hi, ht⟩ := hw
  exact ⟨s', hs, hi, totalQ_congr own s' rd rd' h ht⟩

end

/-! ## 7 What rides -/

section
variable (own : List (ℕ × ℕ))

/-- **The later part b rides on the earlier part a**: as far as a form can see that names only what
is there at a. -/
structure Rides (a b : K9.Part) : Prop where
  arrays : b.L.arrayOf = a.L.arrayOf
  rows : b.L.check.rows = a.L.check.rows
  sent : ∀ born k o : ℕ, a.L.check.frame.whereIs born k = some o →
    b.L.check.frame.whereIs born k = some o
  mask : ∀ o : ℕ, maskOracle a.L.check.frame = some o → maskOracle b.L.check.frame = some o
  book : ∀ (o : ℕ) (y : ℕ × ℕ), a.d.book.place[o]? = some y → b.d.book.place[o]? = some y
  bits : ∀ (o : ℕ) (x : ℕ × ℕ) (part : OnBytes.Part), seatAt own a.d.book o = some x →
    b.d.st.rowBits o part = a.d.st.rowBits o part ∧
      b.d.st.placeBits o part = a.d.st.placeBits o part
  filled : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
    b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE

/-- A cell of a seated array is the same off both records. -/
theorem cell_rides (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (h : Rides own a b) (c : ℕ × String)
    (A : Params.ReqArray) (o : ℕ) (x : ℕ × ℕ)
    (hA : reqArray a.L.check.rows.layout c.1 c.2 = some A)
    (ho : a.L.check.frame.whereIs c.1 A.message = some o)
    (hx : seatAt own a.d.book o = some x) (r i : ℕ) :
    (dataQ own b rd).cell c.1 c.2 r i = (dataQ own a rd).cell c.1 c.2 r i := by
  have hx' := seatAt_rides own a.d.book b.d.book o x (h.book o) hx
  have ht := tabQ_rides own a.d.st b.d.st a.d.book b.d.book rd o x .main hx hx'
    (h.bits o x .main hx).1
  simp only [dataQ, dataOf, h.rows, hA, ho, h.sent c.1 A.message o ho, ht,
    (h.bits o x .main hx).1, (h.bits o x .main hx).2]

/-- The mask row is the same off both records, where it is there at the earlier one. -/
theorem mask_rides (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (h : Rides own a b) (x : ℕ × ℕ)
    (hm : maskSeat own a = some x) (j : ℕ) :
    (dataQ own b rd).mask j = (dataQ own a rd).mask j := by
  unfold maskSeat at hm
  rw [maskAt_eq] at hm
  obtain ⟨o, ho, hx⟩ := Option.bind_eq_some_iff.1 hm
  have hx' := seatAt_rides own a.d.book b.d.book o x (h.book o) hx
  have ht := tabQ_rides own a.d.st b.d.st a.d.book b.d.book rd o x .mask hx hx'
    (h.bits o x .mask hx).1
  simp only [dataQ, dataOf, ho, h.mask o ho, ht]

/-- A slot that is there at the earlier record has the same value under it at both, where the mask
row's entry is the same. -/
theorem slot_rides (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (ma mb : ℕ → GQ) (j : ℕ) (hs : slotIn own free late a j = true) (hm : mb j = ma j) :
    slotW b.F late mb j = slotW a.F late ma j := by
  cases e : lateAt late j with
  | some y => rw [slotW_late b.F late mb j y e, slotW_late a.F late ma j y e, hm]
  | none =>
    unfold slotIn at hs
    obtain ⟨s1, hs⟩ := Eq.mp (Bool.and_eq_true _ _) hs
    obtain ⟨_, hs⟩ := Eq.mp (Bool.and_eq_true _ _) hs
    obtain ⟨_, hs⟩ := Eq.mp (Bool.and_eq_true _ _) hs
    rw [e] at hs
    have hs' : (a.F.gotF.getD j false &&
        (decide (j < a.F.vp.size) && decide (j < a.F.mf.size))) = true := hs
    obtain ⟨s2, _⟩ := Eq.mp (Bool.and_eq_true _ _) hs'
    obtain ⟨e1, e2⟩ := hfill j (of_decide_eq_true s1) s2
    rw [slotW_ledger b.F late mb j e, slotW_ledger a.F late ma j e, e1, e2, hm]

/-- The mask row's seat is there wherever a slot is. -/
theorem slotIn_mask (free : Option ℕ) (late : List (ℕ × E × E)) (a : K9.Part) (j : ℕ)
    (hs : slotIn own free late a j = true) : ∃ y, maskSeat own a = some y := by
  unfold slotIn at hs
  obtain ⟨_, hs⟩ := Eq.mp (Bool.and_eq_true _ _) hs
  obtain ⟨s2, _⟩ := Eq.mp (Bool.and_eq_true _ _) hs
  exact Option.isSome_iff_exists.1 s2

/-- **The general step**: two records, two data: a form is worth the same at both, where the arrays'
names are the same, the slots that it names are there at the earlier record, and the data agree at
the cells and the mask row's entries that it names. -/
theorem value_ridesW (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part)
    (Da Db : Bound GQ) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (f : Aff) (hsl : ∀ x ∈ f.slots.toList, slotIn own free late a x.1 = true)
    (hcell : ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
      Db.cell c.1 c.2 x.row x.idx = Da.cell c.1 c.2 x.row x.idx)
    (hmask : ∀ x ∈ f.slots.toList, Db.mask x.1 = Da.mask x.1) :
    f.value Reading.gl (worldOwn b late Db) = f.value Reading.gl (worldOwn a late Da) := by
  refine value_eq _ _ f (fun x hx => ?_) (fun x hx => ?_)
  · show (match b.L.arrayOf[x.tree]? with
      | some c => Db.cell c.1 c.2 x.row x.idx
      | none => 0) = (match a.L.arrayOf[x.tree]? with
      | some c => Da.cell c.1 c.2 x.row x.idx
      | none => 0)
    rw [harr]
    cases e : a.L.arrayOf[x.tree]? with
    | none => rfl
    | some c => exact hcell x hx c e
  · exact slot_rides own free late a b hfill Da.mask Db.mask x.1 (hsl x hx) (hmask x hx)

/-- **A form that names only what is there at the earlier record is worth the same at both.** -/
theorem value_rides (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part)
    (rd : ℕ × ℕ → MsgQ) (h : Rides own a b) (f : Aff) (hf : affIn own free late a f = true) :
    f.value Reading.gl (worldOwn b late (dataQ own b rd)) =
      f.value Reading.gl (worldOwn a late (dataQ own a rd)) := by
  unfold affIn at hf
  obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) hf
  refine value_ridesW own free late a b _ _ h.arrays h.filled f (List.all_eq_true.1 h2)
    (fun x hx c hc => ?_) (fun x hx => ?_)
  · obtain ⟨A, hA⟩ := entIn_some own a x (List.all_eq_true.1 h1 x hx)
    obtain ⟨c', o, y, hc', hr, ho, hy⟩ := arrayIn_some own a x.tree A hA
    obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hc)
    exact cell_rides own a b rd h c' A o y hr ho hy x.row x.idx
  · obtain ⟨y, hy⟩ := slotIn_mask own free late a x.1 (List.all_eq_true.1 h2 x hx)
    exact mask_rides own a b rd h y hy x.1

/-- **WHAT RIDES: from the sentence at the later record s' to the sentence at the earlier record s,
at one witness.** -/
theorem formsQ_rides (Rd : Readers) (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part)
    (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsIn Rd own piece run s = true) (hr : Rides own a b)
    (h : formsQ Rd own piece run s' rd) : formsQ Rd own piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hf⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs : Rd.forms piece run s = some R := hl ▸ hs'
  unfold formsIn at hin
  rw [ha, hs] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨a, R, ha, hs, hlate, fun f hm => ?_⟩
  have hi : affIn own (K9.mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
  refine ⟨hi, ?_⟩
  rw [← value_rides own (K9.mergeOf s) R.late a b' rd hr f hi]
  exact (hf f hm).2

/-- **The same for formsT.** hat: A PREMISE ON THE LETTER: the stated data agree at both records at
what the reader's forms name. -/
theorem formsTQ_rides (Rd : Readers) (St : Stated) (piece : ℕ) (run : String) (s s' : S)
    (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInT Rd own piece run s = true) (hr : Rides own a b)
    (hat : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      (∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (St.at1 s' (dataQ own b rd)).cell c.1 c.2 x.row x.idx =
          (St.at1 s (dataQ own a rd)).cell c.1 c.2 x.row x.idx) ∧
      ∀ x ∈ f.slots.toList,
        (St.at1 s' (dataQ own b rd)).mask x.1 = (St.at1 s (dataQ own a rd)).mask x.1)
    (h : formsTQ Rd St own piece run s' rd) : formsTQ Rd St own piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hf⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs : Rd.forms piece run s = some R := hl ▸ hs'
  unfold formsInT at hin
  rw [ha, hs] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨a, R, ha, hs, hlate, fun f hm => ?_⟩
  have hi : affInT own (K9.mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
  refine ⟨hi, ?_⟩
  have h2 := hi
  unfold affInT at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [← value_ridesW own (K9.mergeOf s) R.late a b' (St.at1 s (dataQ own a rd))
    (St.at1 s' (dataQ own b' rd)) hr.arrays hr.filled f (List.all_eq_true.1 h3)
    (hat R hs f hm).1 (hat R hs f hm).2]
  exact (hf f hm).2

end

/-! ## 8 Tried -/

section
variable (Rd : Readers) (St : Stated) (after : S → Except String S) (own : List (ℕ × ℕ))

/-- Where no segment is open, none of the first three holds. -/
theorem none_fails (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ)
    (h : segAt? s = none) :
    ¬ formsQ Rd own piece run s rd ∧ ¬ formsTQ Rd St own piece run s rd ∧ ¬ totalQ own s rd := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, _, ha, _⟩
    rw [h] at ha
    exact nomatch ha
  · rintro ⟨a, _, ha, _⟩
    rw [h] at ha
    exact nomatch ha
  · rintro ⟨a, ha, _⟩
    rw [segAt_of_atS s a ha] at h
    exact nomatch h

/-- A form that names what is not there: the sentence fails. -/
theorem formsQ_outside (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ) (a : K9.Part)
    (ha : segAt? s = some a) (R : Read) (hs : Rd.forms piece run s = some R) (f : Aff)
    (hf : f ∈ R.forms) (ho : affIn own (K9.mergeOf s) R.late a f = false) :
    ¬ formsQ Rd own piece run s rd := by
  rintro ⟨a', R', ha', hs', _, h⟩
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain rfl : R' = R := Option.some.inj (hs'.symm.trans hs)
  have h1 := (h f hf).1
  rw [ho] at h1
  exact nomatch h1

/-- At a reader that gives no form the sentence holds of every witness, wherever a segment is
open: the item is idle there. -/
theorem formsQ_nil (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ) (a : K9.Part)
    (ha : segAt? s = some a) (hn : Rd.forms piece run s = some ⟨[], []⟩) :
    formsQ Rd own piece run s rd :=
  ⟨a, ⟨[], []⟩, ha, hn, rfl, fun _ hf => nomatch hf⟩

/-- Where the record does not hold the run's forms the sentence fails. -/
theorem formsQ_unread (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ)
    (hn : Rd.forms piece run s = none) : ¬ formsQ Rd own piece run s rd := by
  rintro ⟨_, _, _, hs, _⟩
  rw [hn] at hs
  exact nomatch hs

/-- The law of the block that runs the runs behind the batching: by unfolding. -/
theorem totalB_of_total (s s' : S) (rd : ℕ × ℕ → MsgQ) (h : after s = .ok s')
    (hi : totalIn own s' = true) (ht : totalQ own s' rd) : totalBQ after own s rd :=
  ⟨s', h, hi, ht⟩

/-- `totalQ`, written out. -/
theorem totalQ_iff (s : S) (rd : ℕ × ℕ → MsgQ) :
    totalQ own s rd ↔ ∃ a, atS.get? s = some a ∧
      a.F.total Reading.gl (worldAt Reading.gl a.L a.F
        (dataOf a.L.check.rows a.L.check.frame a.d.st (tabQ own a.d.st a.d.book rd))) = 0 :=
  Iff.rfl

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabQ_congr
#print axioms VerifiableInference.Desc.Sound.value_eq
#print axioms VerifiableInference.Desc.Sound.formsQ_in
#print axioms VerifiableInference.Desc.Sound.formsQ_congr
#print axioms VerifiableInference.Desc.Sound.formsTQ_congr
#print axioms VerifiableInference.Desc.Sound.totalQ_congr
#print axioms VerifiableInference.Desc.Sound.totalBQ_congr
#print axioms VerifiableInference.Desc.Sound.cell_rides
#print axioms VerifiableInference.Desc.Sound.mask_rides
#print axioms VerifiableInference.Desc.Sound.slotW_filled
#print axioms VerifiableInference.Desc.Sound.slot_rides
#print axioms VerifiableInference.Desc.Sound.value_ridesW
#print axioms VerifiableInference.Desc.Sound.value_rides
#print axioms VerifiableInference.Desc.Sound.formsQ_rides
#print axioms VerifiableInference.Desc.Sound.formsTQ_rides
#print axioms VerifiableInference.Desc.Sound.none_fails
#print axioms VerifiableInference.Desc.Sound.formsQ_outside
#print axioms VerifiableInference.Desc.Sound.formsQ_nil
#print axioms VerifiableInference.Desc.Sound.formsQ_unread
#print axioms VerifiableInference.Desc.Sound.maskAt_eq
#print axioms VerifiableInference.Desc.Sound.totalB_of_total
#print axioms VerifiableInference.Desc.Sound.totalQ_iff
