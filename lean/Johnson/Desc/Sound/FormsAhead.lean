-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsAhead.lean: THE SENTENCE "forms" WHERE A FORM NAMES AN ARRAY THAT THE OPEN
SEGMENT HAS NOT YET SENT: THE ARRAY's CELLS ARE READ OFF THE WITNESS AT THE SEAT THAT THE PLAN GIVES
ITS MESSAGE, WITH THE PLAN's SHAPE. Definitions and theorems.

Why. See Johnson/Desc/First/Batch/Ahead.lean. The witness is one for all borders and holds every
message of the group; the table lets the item read the whole group's seats, by the plan. `dataQ`
(Johnson/Desc/Sound/FormsQ.lean) finds a cell through the record (the message's number in the
statement, the book's place, the statement's bits): an array that is not yet sent reads as 0.
  `dataQA sent own a rd`: `dataQ`, but at an array that is ahead (`K9.aheadIn`): the sum over its
  blocks
    of the witness's main table AT THE PLAN's SEAT. The mask row: `dataQ`'s.
  `formsQA`: the sentence: `formsQ`'s text with `affInA` and `dataQA`.
  `formsQA_in`: it holds its public test `formsInA`.
  `formsQA_congr`: it reads the witness at own's seats alone.
  `dataQA_none`, `formsQA_iff`: WHERE NOTHING IS AHEAD IT IS `formsQ`.
  `cellA_meets`: **THE BOOK-KEEPING ACROSS THE SENDING**: an array that is ahead at the part a and
  sent
    at the part b: where the layout is one, b's frame finds the message, b's book holds it AT THE
    PLAN's SEAT, and b's statement gives it THE PLAN's BITS: its cells are the same at both.
  `formsQA_back`: **THE RIDER**: from the sentence at a later record s' to the sentence at s, at one
    witness: one answer of the reader · the public test at s · the arrays' names and the filled
    slots
    stay · the data agree at the cells and mask entries that the forms name (hcell, hmask).
Limits: (1) `cellA_meets`' three premises on the later record (the frame finds it; the plan's seat;
the plan's bits) are premises: what the table's items on the book and on the messages' shapes say;
NOT JOINED TO THESE HERE. (2) hcell at an array that is there at both records is `cell_rides`'
matter. (3) One answer is a premise. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (segAt? seatAt lateOk slotIn affIn Read Readers formsIn mergeOf
  Ahead aheadOf aheadIn aheadIn_mem entInA affInA affInA_none formsInA rowBitsOf placeBitsOf)
open VerifiableInference.Desc.K9L (Bound dataOf cellOfBlock)
open VerifiableInference.Desc.First (S)

section
variable (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))

/-- A cell of an array that is ahead, off the witness's main table at the plan's seat. -/
def cellA (codes : Codes) (h : Ahead) (rd : ℕ × ℕ → MsgQ) (i c : ℕ) : GQ :=
  (h.A.blocks.map fun b =>
    cellOfBlock b (rowBitsOf h.shape .main) (placeBitsOf codes h.shape .main)
      (fun J => rd h.seat false (J % 2 ^ rowBitsOf h.shape .main)
        (J / 2 ^ rowBitsOf h.shape .main)) i c).sum

/-- **The data, with what is ahead read by the plan.** -/
def dataQA (a : K9.Part) (rd : ℕ × ℕ → MsgQ) : Bound GQ where
  cell := fun born name i c =>
    match aheadIn sent own a (born, name) with
    | some h => cellA a.d.st.codes h rd i c
    | none => (dataQ own a rd).cell born name i c
  mask := (dataQ own a rd).mask

theorem dataQA_congr (a : K9.Part) (rd rd' : ℕ × ℕ → MsgQ) (h : ∀ x ∈ own, rd x = rd' x) :
    dataQA sent own a rd = dataQA sent own a rd' := by
  unfold dataQA
  rw [dataQ_congr own a rd rd' h]
  congr 1
  funext born name i c
  cases e : aheadIn sent own a (born, name) with
  | none => rfl
  | some q =>
    show cellA a.d.st.codes q rd i c = cellA a.d.st.codes q rd' i c
    unfold cellA
    rw [h q.seat (aheadIn_mem sent own a _ q e)]

/-- Where nothing is ahead the data are the old ones. -/
theorem dataQA_none (a : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (hn : ∀ b, aheadIn sent own a b = none) : dataQA sent own a rd = dataQ own a rd := by
  unfold dataQA
  have e : (fun born name i c =>
      match aheadIn sent own a (born, name) with
      | some h => cellA a.d.st.codes h rd i c
      | none => (dataQ own a rd).cell born name i c) = (dataQ own a rd).cell := by
    funext born name i c
    rw [hn (born, name)]
  rw [e]

variable (Rd : Readers)

/-- **forms, where a form may name what is ahead.** -/
def formsQA (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ) : Prop :=
  ∃ a R, segAt? s = some a ∧ Rd.forms piece run s = some R ∧ lateOk R.late a = true ∧
    ∀ f ∈ R.forms, affInA sent own (mergeOf s) R.late a f = true ∧
      f.value Reading.gl (worldOwn a R.late (dataQA sent own a rd)) = 0

/-- The sentence holds the test. -/
theorem formsQA_in (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ)
    (h : formsQA sent own Rd piece run s rd) : formsInA Rd sent own piece run s = true := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := h
  unfold formsInA
  rw [ha, hs]
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hm => (hf f hm).1⟩

/-- It reads the witness at own's seats alone. -/
theorem formsQA_congr (piece : ℕ) (run : String) (s : S) (rd rd' : ℕ × ℕ → MsgQ)
    (h : ∀ x ∈ own, rd x = rd' x) (hw : formsQA sent own Rd piece run s rd) :
    formsQA sent own Rd piece run s rd' := by
  obtain ⟨a, R, ha, hs, hl, hf⟩ := hw
  refine ⟨a, R, ha, hs, hl, ?_⟩
  rw [← dataQA_congr sent own a rd rd' h]
  exact hf

/-- **Where nothing is ahead it is the sentence "forms".** -/
theorem formsQA_iff (piece : ℕ) (run : String) (s : S) (rd : ℕ × ℕ → MsgQ)
    (hn : ∀ a, segAt? s = some a → ∀ b, aheadIn sent own a b = none) :
    formsQA sent own Rd piece run s rd ↔ formsQ Rd own piece run s rd := by
  constructor
  · rintro ⟨a, R, ha, hs, hl, hf⟩
    refine ⟨a, R, ha, hs, hl, fun f hm => ?_⟩
    have h := hf f hm
    rw [affInA_none sent own (mergeOf s) R.late a (hn a ha),
      dataQA_none sent own a rd (hn a ha)] at h
    exact h
  · rintro ⟨a, R, ha, hs, hl, hf⟩
    refine ⟨a, R, ha, hs, hl, fun f hm => ?_⟩
    rw [affInA_none sent own (mergeOf s) R.late a (hn a ha), dataQA_none sent own a rd (hn a ha)]
    exact hf f hm

/-- **THE BOOK-KEEPING ACROSS THE SENDING.** -/
theorem cellA_meets (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) (c : ℕ × String) (h : Ahead) (o : ℕ)
    (ea : aheadIn sent own a c = some h) (eb : aheadIn sent own b c = none)
    (hlay : reqArray b.L.check.rows.layout c.1 c.2 = some h.A)
    (hw : b.L.check.frame.whereIs c.1 h.A.message = some o)
    (hseat : seatAt own b.d.book o = some h.seat)
    (hr : b.d.st.rowBits o .main = rowBitsOf h.shape .main)
    (hp : b.d.st.placeBits o .main = placeBitsOf a.d.st.codes h.shape .main) (i j : ℕ) :
    (dataQA sent own b rd).cell c.1 c.2 i j = (dataQA sent own a rd).cell c.1 c.2 i j := by
  show (match aheadIn sent own b (c.1, c.2) with
      | some q => cellA b.d.st.codes q rd i j
      | none => (dataQ own b rd).cell c.1 c.2 i j) =
    (match aheadIn sent own a (c.1, c.2) with
      | some q => cellA a.d.st.codes q rd i j
      | none => (dataQ own a rd).cell c.1 c.2 i j)
  rw [show ((c.1, c.2) : ℕ × String) = c from rfl, ea, eb]
  show (dataQ own b rd).cell c.1 c.2 i j = cellA a.d.st.codes h rd i j
  unfold dataQ dataOf cellA
  simp only [hlay, hw, hr, hp]
  congr 1
  refine List.map_congr_left fun blk _ => ?_
  congr 1
  funext J
  unfold tabQ
  rw [hseat, hr]
  rfl

/-- **THE RIDER: the sentence goes back from a later record to an earlier one.** -/
theorem formsQA_back (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (rd : ℕ × ℕ → MsgQ)
    (ha : segAt? s = some a) (hb : segAt? s' = some b)
    (hl : Rd.forms piece run s' = Rd.forms piece run s)
    (hin : formsInA Rd sent own piece run s = true) (harr : b.L.arrayOf = a.L.arrayOf)
    (hfill : ∀ j : ℕ, j < a.F.ns → a.F.gotF.getD j false = true →
      b.F.vp.getD j zeroE = a.F.vp.getD j zeroE ∧ b.F.mf.getD j zeroE = a.F.mf.getD j zeroE)
    (hcell : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, ∀ c : ℕ × String, a.L.arrayOf[x.tree]? = some c →
        (dataQA sent own b rd).cell c.1 c.2 x.row x.idx =
          (dataQA sent own a rd).cell c.1 c.2 x.row x.idx)
    (hmask : ∀ R : Read, Rd.forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.slots.toList, (dataQA sent own b rd).mask x.1 = (dataQA sent own a rd).mask x.1)
    (h : formsQA sent own Rd piece run s' rd) : formsQA sent own Rd piece run s rd := by
  obtain ⟨b', R, hb', hs', _, hf⟩ := h
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hs : Rd.forms piece run s = some R := hl ▸ hs'
  unfold formsInA at hin
  rw [ha, hs] at hin
  obtain ⟨hlate, hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  refine ⟨a, R, ha, hs, hlate, fun f hm => ?_⟩
  have hi : affInA sent own (mergeOf s) R.late a f = true := List.all_eq_true.1 hall f hm
  refine ⟨hi, ?_⟩
  have h2 := hi
  unfold affInA at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [← value_ridesW own (mergeOf s) R.late a b' (dataQA sent own a rd) (dataQA sent own b' rd)
    harr hfill f (List.all_eq_true.1 h3) (hcell R hs f hm) (hmask R hs f hm)]
  exact (hf f hm).2

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.dataQA_congr
#print axioms VerifiableInference.Desc.Sound.dataQA_none
#print axioms VerifiableInference.Desc.Sound.formsQA_in
#print axioms VerifiableInference.Desc.Sound.formsQA_congr
#print axioms VerifiableInference.Desc.Sound.formsQA_iff
#print axioms VerifiableInference.Desc.Sound.cellA_meets
#print axioms VerifiableInference.Desc.Sound.formsQA_back
