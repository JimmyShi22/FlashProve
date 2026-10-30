-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/FormsIn.lean: THE PUBLIC TESTS BESIDE FOUR SENTENCES OF THE TABLE OF JOINTS
("the forms of a run are worth 0"; "the one equation's sum is 0": Johnson/Desc/Sound/FormsQ.lean):
WHAT A FORM OR THE LEDGER NAMES IS THERE. Definitions with code, and five small lemmas. No Mathlib:
so that a run can evaluate them at every border. No witness stands in any of them.

Why. The sentences read the witness through total functions: an array that the segment's list
lacks, a message that is not sent, a seat that the sentence may not read, a slot under which nothing
was put would each read as 0, in silence. These tests say that nothing of the sort is asked. They
stand inside the sentences on forms, and are meant for the table's promise at every border at which
the item is open.
  `seatAt own book o`: the seat (tree, tenant) of oracle message number o of the record's
    statement, by the book of trees; nothing unless it is a seat of own (the seats that the sentence
    may read).
  `arrayIn own a t`: array number t of the segment's list is in the layout, its message has been
    sent, and that message sits at a seat of own.
  `entIn`, `slotIn`, `affIn`: an entry names a cell inside such an array; a slot is below the number
    of slots, the segment's mask row's message is seated, the slot is not the one whose scalar is
    masked elsewhere (free: the merge's end value's: `K9.mergeOf`), and EITHER a value has been put
    under it (inside the two arrays' sizes) OR it is LATE; a form names such entries and slots
    alone.
  LATE SLOTS. Some runs of claims fill, at the batching's place, slots that their own forms name
    (by a run at the small stored proof: the feed-forward kind's two runs, the smallness test's
    equations, attention's "planes"). At every earlier border the ledger holds nothing under such a
    slot. So a run's reader gives, with the forms, `late`: slot, what is shown, the factor: what the
    run will lay. `lateOk`: a late slot is below the number of slots, and is free or holds just
    that.
  `entInT`, `affInT`: in front of the segment's second sending an entry may also name a cell of an
    array of that sending (by the shape: the array's message has the moment 1).
  `ledgerIn`: the ledger's sizes fit; the mask row is there; every array of the ledger is there;
    every virtual row has a weight for each of its array's rows: RIGHT BEHIND THE RUNS BEHIND THE
    BATCHING ALONE: until then the weights are empty.
  `Readers`: THE LETTER: a run's forms and late slots (`Read`) as a plain function of the record;
    NOTHING where the record does not hold them yet.
  `formsIn`, `formsInT`, `totalIn`: the tests at the carried record.
`maskAt` is `maskOracle` of kind K9's law files (over Mathlib), typed again for this storey;
Johnson/Desc/Sound/FormsQ.lean holds the two together (`maskAt_eq`).
HAVE THEY RUN? `formsIn`, `formsInT`, `lateOk`, `totalIn`: at the generic readers
(Johnson/Desc/First/Batch/ReaderOf.lean), on a walk over the first chain at the small stored proof,
AT EVERY BORDER AT WHICH THE TABLE HAS THE ITEM OPEN, own := the table's own list of the segment's
seats (FOR `formsInT` TOO: the whole group: NOT YET its first sending's seats alone, which are all
that the sentence in front of the second sending may read), with controls that ring: they hold
wherever the reader gives an answer. IT GIVES NONE: for the smallness test's equations, at every
border; for five runs of the head, at the one border behind the head's own block. At the full size:
at the batching's place alone. `ledgerIn` (in `totalIn`) HOLDS ONLY WHERE THE VIRTUAL ROWS' WEIGHTS
ARE LAID: on the walk at the first border at which the table has "total" open; in an earlier run, at
the batching's place, it was false until the smallness test's weights were laid over the ledger by
hand.
Limits: tests; nothing is proved of any block. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.AtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

section
variable (own : List (Nat × Nat))

/-- The seat of oracle message number o of the record's statement, by the book. Nothing where the
book has no such message, or it sits at no seat of own. -/
def seatAt (book : OnBytes.TreeBook) (o : Nat) : Option (Nat × Nat) :=
  (book.place[o]?).bind fun x => if own.contains x then some x else none

theorem seatAt_mem (book : OnBytes.TreeBook) (o : Nat) (x : Nat × Nat)
    (e : seatAt own book o = some x) : x ∈ own := by
  unfold seatAt at e
  obtain ⟨y, _, hy⟩ := Option.bind_eq_some_iff.1 e
  by_cases hc : own.contains y = true
  · rw [if_pos hc] at hy
    rw [← Option.some.inj hy]
    simpa using hc
  · rw [if_neg hc] at hy
    exact nomatch hy

/-- A seat in an earlier book stays in a later one. -/
theorem seatAt_rides (book book' : OnBytes.TreeBook) (o : Nat) (x : Nat × Nat)
    (hb : ∀ y, book.place[o]? = some y → book'.place[o]? = some y)
    (e : seatAt own book o = some x) : seatAt own book' o = some x := by
  unfold seatAt at e
  obtain ⟨y, h1, hy⟩ := Option.bind_eq_some_iff.1 e
  unfold seatAt
  rw [hb y h1]
  exact hy

variable (free : Option Nat) (late : List (Nat × E × E))

/-- Array number t of the segment's list is in the layout, its message has been sent, and that
message sits at a seat of own. Gives the array. -/
def arrayIn (a : Part) (t : Nat) : Option Params.ReqArray :=
  (a.L.arrayOf[t]?).bind fun b =>
    (reqArray a.L.check.rows.layout b.1 b.2).bind fun A =>
      (a.L.check.frame.whereIs b.1 A.message).bind fun o =>
        (seatAt own a.d.book o).map fun _ => A

theorem arrayIn_some (a : Part) (t : Nat) (A : Params.ReqArray) (h : arrayIn own a t = some A) :
    ∃ b o x, a.L.arrayOf[t]? = some b ∧ reqArray a.L.check.rows.layout b.1 b.2 = some A ∧
      a.L.check.frame.whereIs b.1 A.message = some o ∧ seatAt own a.d.book o = some x := by
  unfold arrayIn at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨A', hA, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨o, ho, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, hx, h⟩ := Option.map_eq_some_iff.1 h
  subst h
  exact ⟨b, o, x, hb, hA, ho, hx⟩

/-- An entry names a cell that is there. -/
def entIn (a : Part) (x : Ent) : Bool :=
  match arrayIn own a x.tree with
  | some A => decide (x.row < A.sizeI) && decide (x.idx < A.sizeC)
  | none => false

theorem entIn_some (a : Part) (x : Ent) (h : entIn own a x = true) :
    ∃ A, arrayIn own a x.tree = some A := by
  unfold entIn at h
  cases e : arrayIn own a x.tree with
  | some A => exact ⟨A, rfl⟩
  | none =>
    rw [e] at h
    exact nomatch h

/-- The number, in the statement, of the present segment's first message with mask rows. -/
def maskAt (f : ReqFrame) : Option Nat :=
  (((f.shape.link[f.link]?.map (·.messages)).getD []).findIdx? fun x =>
    x.shape.maskRows != 0).bind fun m => f.whereIs f.link m

/-- The seat of the segment's mask row's message. -/
def maskSeat (a : Part) : Option (Nat × Nat) :=
  (maskAt a.L.check.frame).bind fun o => seatAt own a.d.book o

/-- What the run will lay under slot j: what is shown, the factor. Nothing if the slot is not
late. -/
def lateAt (j : Nat) : Option (E × E) := (late.find? fun x => x.1 == j).map (·.2)

/-- A late slot is below the number of slots, and is free or holds just what the reader says. -/
def lateOk (a : Part) : Bool :=
  late.all fun x => decide (x.1 < a.F.ns) &&
    (!(a.F.gotF.getD x.1 false) ||
      (decide (a.F.vp.getD x.1 zeroE = x.2.1) && decide (a.F.mf.getD x.1 zeroE = x.2.2)))

/-- A slot is below the number of slots, the mask row is there, the slot is not the one (free) whose
scalar is masked elsewhere, and it is late, or a value has been put under it, inside the sizes. -/
def slotIn (a : Part) (j : Nat) : Bool :=
  decide (j < a.F.ns) && ((maskSeat own a).isSome && ((free != some j) &&
    ((lateAt late j).isSome ||
      (a.F.gotF.getD j false && (decide (j < a.F.vp.size) && decide (j < a.F.mf.size))))))

/-- **A form names only what is there.** -/
def affIn (a : Part) (f : Aff) : Bool :=
  (f.ents.toList.all fun x => entIn own a x) &&
    f.slots.toList.all fun x => slotIn own free late a x.1

/-- The array b of the layout is of the open segment's own second sending. -/
def atMoment1 (a : Part) (b : Nat × String) (A : Params.ReqArray) : Bool :=
  b.1 == a.L.check.frame.link &&
    match (a.L.check.frame.shape.link[b.1]?).bind fun l => l.messages[A.message]? with
    | some m => m.moment == 1
    | none => false

/-- In front of the second sending: an entry names a cell of an array that is there, or of an array
of the second sending. -/
def entInT (a : Part) (x : Ent) : Bool :=
  entIn own a x ||
    match a.L.arrayOf[x.tree]? with
    | none => false
    | some b =>
      match reqArray a.L.check.rows.layout b.1 b.2 with
      | none => false
      | some A => atMoment1 a b A && (decide (x.row < A.sizeI) && decide (x.idx < A.sizeC))

/-- The same test for a form in front of the second sending. -/
def affInT (a : Part) (f : Aff) : Bool :=
  (f.ents.toList.all fun x => entInT own a x) &&
    f.slots.toList.all fun x => slotIn own free late a x.1

/-- The ledger's sizes fit; the mask row is there; every array of the ledger is there; every virtual
row has a weight for each of its array's rows. -/
def ledgerIn (a : Part) : Bool :=
  a.F.LS.size == a.F.ns && a.F.vp.size == a.F.ns && a.F.mf.size == a.F.ns &&
    (maskSeat own a).isSome &&
    (List.range a.F.trees.size).all fun t =>
      (arrayIn own a t).isSome &&
        (a.F.trees.getD t {}).rows.all fun R => R.coef.size == (a.F.trees.getD t {}).R

end

/-- What a run's reader gives. -/
structure Read where
  /-- the run's forms, over the arrays' own rows -/
  forms : List Aff
  /-- the slots that the run itself fills, at the batching's place: slot, shown, factor -/
  late : List (Nat × E × E)

/-- **THE READERS**: what a run (the piece's number in its segment; the run's name) will claim and
lay, as a plain function of the record; nothing where the record does not hold it. -/
structure Readers where
  forms : Nat → String → S → Option Read

/-- **The open segment's part, as far as "forms" and "formsT" read it**: the link's context, the
ledger, the chain's state, the book. Kind K9's lens `atS` asks one thing more: "the slots taken",
which at the head's segment is there only behind the merge: so at the head's earlier borders that
lens gives nothing. Here that number is 0 where it is not there: NO TEST AND NO SENTENCE OF THESE
FILES READS IT. -/
def segAt? (s : S) : Option Part := do
  let L ← s.link?
  let F ← s.fork?
  let tl ← s.tl?
  pure { owed := owedOf s, used := (usedOf s).getD 0, laid := laidOf tl, L := L, F := F,
         d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }

/-- Where kind K9's lens gives a part, this is that part. -/
theorem segAt_of_atS (s : S) (a : Part) (h : atS.get? s = some a) : segAt? s = some a := by
  unfold atS at h
  unfold segAt?
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        cases hu : usedOf s with
        | none => simp [hL, hF, ht, hu] at h
        | some u =>
          simp [hL, hF, ht, hu] at h
          simp [h]

section
variable (Rd : Readers) (own : List (Nat × Nat))

/-- FOR THE PROMISE, wherever the item forms is open. -/
def formsIn (piece : Nat) (run : String) (s : S) : Bool :=
  match segAt? s, Rd.forms piece run s with
  | some a, some R => lateOk R.late a && R.forms.all fun f => affIn own (mergeOf s) R.late a f
  | _, _ => false

/-- FOR THE PROMISE, wherever the item formsT is open. -/
def formsInT (piece : Nat) (run : String) (s : S) : Bool :=
  match segAt? s, Rd.forms piece run s with
  | some a, some R => lateOk R.late a && R.forms.all fun f => affInT own (mergeOf s) R.late a f
  | _, _ => false

/-- FOR THE PROMISE, at total's borders; and inside the sentence totalB, at the record that the runs
behind the batching return. -/
def totalIn (s : S) : Bool :=
  match atS.get? s with
  | some a => ledgerIn own a
  | none => false

end

end VerifiableInference.Desc.K9
