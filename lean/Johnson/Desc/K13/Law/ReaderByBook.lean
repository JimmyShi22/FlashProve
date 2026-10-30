-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/ReaderByBook.lean: THE READER OF THE ROWS ON THE TABLE THAT GOES THROUGH THE
RECORD's OWN BOOK: the matrix off the witness's cells, the mask entries off the first chain's
reader of a row's words (`wordsFirst`, Johnson/Desc/Sound/WordsAt.lean: the
one reader). A definition, and statements with their proofs.
Main names:
  `maskCut`, `rwBook arr mat`: the reader. mat: the matrix that cells hold: a letter. THE MASK
    ENTRIES ARE CUT TO THE TABLE: beyond a table's size the reader gives 0. WHY: kind K13's law
    asks that two witnesses under one pair of pins be read alike AT EVERY mask entry of the index
    masks' message (`AgreeAt`), and a pin fixes a message inside its ranges alone.
  `agree_in_ranges`: **INSIDE THE PROMISE's PUBLIC TESTS, TWO WITNESSES WITH ONE MATRIX WHOSE
    TABLES AT THE INDEX MASKS' SEAT AGREE INSIDE THE RANGES ARE READ ALIKE** (`AgreeAt`). The
    tests: the proximity test's three items; the book has a place for every message; the plan's
    places name trees that are there; the message is there; by the book it sits at `N.index`.
  `agree_at_index`: so are two that agree on the cells and on that tenant's message and pad, whole.
  `reads_rows`: so, where the rows on the table name that message alone ("K13.pileMasks"), "all rows
    on the table are true" has one truth value at the two: WHAT THE TABLE BOOKS FOR "every pending
    row holds" AND "the one claim holds" IS ALL THAT THE SENTENCE READS THERE.
  `rwBook_same`: the reader is the same at two records with one book, one code table and the same
    shape at every message (spent in Johnson/Desc/K13/Law/Reader3.lean).
What is not claimed. The tests. That two witnesses under one pair of pins have one matrix and
tables that agree inside the ranges (with it `agree_in_ranges` gives `FillM3.det`): other
files' letters. That the ranges here (the real rows; the places that the statement's bits index)
are the pins' own. That the cut reader and the plain one say the same of a row: they do where its
entries lie within their tables: not typed. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.PileMasksIff
import Johnson.Desc.K13.Law.Letters
import Johnson.Desc.Sound.WordsAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words wordsOn realRows tableSize)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (MsgT wordsFirst wordsFirst_is wordsBy_congr tabFirst_at_door)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB)

section
variable {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
  (mat : Cells → Fin nR → (Fin k → Bool) → GE)

/-- The mask entries off the words, CUT TO THE TABLE: beyond a table's size: 0. -/
def maskCut (st : Statement) (m : Words GE) : Slot → GE := fun t =>
  if t.index < tableSize st t.oracle .mask then m t.oracle .mask t.index else 0

/-- **The reader through the record's own book.** -/
def rwBook (x : Pp × S) (w : Desc.Wit Cells Tok MsgT) : Wit GE nR k :=
  ⟨mat w.cells, maskCut x.2.st (wordsFirst arr x.2.st x.2.book w)⟩

/-- Cut to the table, words off tables read a message's table inside its ranges alone: its real
rows; the places that the statement's bits for a place index. -/
theorem maskCut_agree (st : Statement) (T T' : ℕ → Bool → ℕ → ℕ → GE) (o : ℕ)
    (h : ∀ row place, row < realRows st o .mask → place < 2 ^ st.placeBits o .mask →
      T o true row place = T' o true row place) (i : ℕ) :
    maskCut st (wordsOn st T) ⟨o, i⟩ = maskCut st (wordsOn st T') ⟨o, i⟩ := by
  unfold maskCut
  dsimp only
  by_cases hi : i < tableSize st o .mask
  · rw [if_pos hi, if_pos hi]
    have hlt : i < 2 ^ (st.rowBits o .mask + st.placeBits o .mask) := by
      unfold tableSize at hi
      split at hi
      · exact hi
      · exact absurd hi (Nat.not_lt_zero _)
    have hpl : i / 2 ^ st.rowBits o .mask < 2 ^ st.placeBits o .mask := by
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add]
      exact hlt
    unfold wordsOn
    by_cases hr : i % 2 ^ st.rowBits o .mask < realRows st o .mask
    · rw [if_pos hr, if_pos hr]
      exact h _ _ hr hpl
    · rw [if_neg hr, if_neg hr]
  · rw [if_neg hi, if_neg hi]

/-- The one accessor reads the message's and the seat's component alone. -/
theorem tab_same (w w' : Desc.Wit Cells Tok MsgT) (cs : Codes) (sh : OracleShape) (n j t : ℕ)
    (hm : w.msg n = w'.msg n) (hp : w.pad j t = w'.pad j t) :
    w.tab cs sh n j t = w'.tab cs sh n j t := by
  funext mask row place
  unfold Desc.Wit.tab
  rw [hm, hp]

/-- **INSIDE THE PROMISE's PUBLIC TESTS TWO WITNESSES WITH ONE MATRIX, WHOSE TABLES AT THE INDEX
MASKS' SEAT AGREE INSIDE THE RANGES, ARE READ ALIKE**: at the matrix and at EVERY mask entry of
the record's index masks' message. -/
theorem agree_in_ranges (N : Numbers) (M : List OracleShape) (L : K12.Door.Laid) (z : Pp) (s : S)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ht : s.out.indexMasks < s.st.oracles.size)
    (hseat : s.book.place[s.out.indexMasks]? = some N.index) (w w' : Desc.Wit Cells Tok MsgT)
    (hc : mat w.cells = mat w'.cells)
    (hT : ∀ sh, M[s.out.indexMasks]? = some sh → ∀ row place,
      row < realRows s.st s.out.indexMasks .mask →
      place < 2 ^ s.st.placeBits s.out.indexMasks .mask →
      w.tab s.st.codes sh (arr N.index.1 N.index.2) N.index.1 N.index.2 true row place =
        w'.tab s.st.codes sh (arr N.index.1 N.index.2) N.index.1 N.index.2 true row place) :
    AgreeAt s.out.indexMasks (rwBook arr mat (z, s) w) (rwBook arr mat (z, s) w') := by
  obtain ⟨sh, q, a1, a2, a3⟩ :=
    tabFirst_at_door arr M L s.st s.book s.roots h₁ h₂ h₃ hs hb w _ ht
  obtain ⟨sh', q', b1, b2, b3⟩ :=
    tabFirst_at_door arr M L s.st s.book s.roots h₁ h₂ h₃ hs hb w' _ ht
  obtain rfl : sh = sh' := Option.some.inj (a1.symm.trans b1)
  obtain rfl : q = N.index := Option.some.inj (a2.symm.trans hseat)
  obtain rfl : q' = N.index := Option.some.inj (b2.symm.trans hseat)
  refine ⟨hc, fun i => ?_⟩
  show maskCut s.st (wordsFirst arr s.st s.book w) ⟨s.out.indexMasks, i⟩ =
    maskCut s.st (wordsFirst arr s.st s.book w') ⟨s.out.indexMasks, i⟩
  rw [wordsFirst_is, wordsFirst_is]
  refine maskCut_agree s.st _ _ _ (fun row place hr hp => ?_) i
  rw [a3, b3]
  exact hT sh a1 row place hr hp

/-- **Two witnesses that agree on the three components are read alike.** -/
theorem agree_at_index (N : Numbers) (M : List OracleShape) (L : K12.Door.Laid) (z : Pp) (s : S)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ht : s.out.indexMasks < s.st.oracles.size)
    (hseat : s.book.place[s.out.indexMasks]? = some N.index) (w w' : Desc.Wit Cells Tok MsgT)
    (hc : w.cells = w'.cells)
    (hm : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2))
    (hp : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2) :
    AgreeAt s.out.indexMasks (rwBook arr mat (z, s) w) (rwBook arr mat (z, s) w') :=
  agree_in_ranges arr mat N M L z s h₁ h₂ h₃ hs hb ht hseat w w' (by rw [hc])
    fun sh _ row place _ _ => by rw [tab_same w w' _ sh _ _ _ hm hp]

/-- **What the sentence reads there.** -/
theorem reads_rows (N : Numbers) (M : List OracleShape) (L : K12.Door.Laid) (z : Pp) (s : S)
    (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ht : s.out.indexMasks < s.st.oracles.size)
    (hseat : s.book.place[s.out.indexMasks]? = some N.index) (hOn : pileMasksC s = true)
    (w w' : Desc.Wit Cells Tok MsgT) (hc : w.cells = w'.cells)
    (hm : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2))
    (hp : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2) :
    RowsTrue (rwBook arr mat (z, s)) s w ↔ RowsTrue (rwBook arr mat (z, s)) s w' :=
  rowsTrue_congr _ ((pileMasksC_iff s).1 hOn)
    (agree_at_index arr mat N M L z s h₁ h₂ h₃ hs hb ht hseat w w' hc hm hp)

/-- A table's size hangs on the message's shape and the code table alone. -/
theorem tableSize_of_shape {st st' : Statement} {o : ℕ} (hcs : st'.codes = st.codes)
    (h : (st'.oracles[o]?).map (·.shape) = (st.oracles[o]?).map (·.shape)) :
    tableSize st' o .mask = tableSize st o .mask := by
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  rw [hcs]
  cases h1 : st.oracles[o]? with
  | none =>
    rw [h1, Option.map_none, Option.map_eq_none_iff] at h
    rw [h]
  | some a =>
    rw [h1, Option.map_some] at h
    obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 h
    rw [hb]
    simp only [e]

/-- One book, one code table, one list of shapes: one reader. -/
theorem rwBook_same (x x' : Pp × S) (hbk : x'.2.book = x.2.book)
    (hcs : x'.2.st.codes = x.2.st.codes)
    (hsh : ∀ o : ℕ, (x'.2.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape) =
      (x.2.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape))
    (w : Desc.Wit Cells Tok MsgT) : rwBook arr mat x' w = rwBook arr mat x w := by
  have hw : wordsFirst arr x'.2.st x'.2.book w = wordsFirst arr x.2.st x.2.book w := by
    funext o part i
    unfold wordsFirst
    rw [hbk]
    exact wordsBy_congr arr _ _ x.2.st x'.2.st w o o hcs rfl (hsh o) part i
  have hsz : ∀ o, tableSize x'.2.st o .mask = tableSize x.2.st o .mask := fun o =>
    tableSize_of_shape hcs (hsh o)
  unfold rwBook maskCut
  rw [hw]
  congr 1
  funext t
  rw [hsz]

end

end VerifiableInference.Desc.K13.Law
