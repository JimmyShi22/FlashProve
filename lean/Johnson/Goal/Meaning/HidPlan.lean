-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidPlan.lean: the sizes and the labels of the 25 sub-proofs' lists, as values
off the verifier's own plans, and the two premises sizesFit and SeatsOne
(Johnson/Goal/Meaning/HidSeat.lean) brought down to a test on the plans alone.

hidAt (Johnson/Goal/Meaning/HidSeat.lean) has two public letters: the sizes s k of each sub-proof's
signature and the seat of each symbol (message's number, main row, place). This file reads what the
verifier's plans hold of them. X is what publicOf returns; its plans X.G, X.A, X.H have for each
sub-proof the list of its matrices (records TMat: rows of cells m, columns k, kind, label aId).

Main names (all with code):
  tlAt X k, matsAt X k   the record of the smallness test, and its list of matrices, in the plan of
    sub-proof k (2 g: group g; 2 g + 1: its attention sub-proof; 24: the head); empty if there is no
    such plan.
  sizesOf X k   THE LIBRARY's OWN MAKER OF SIZES (sizeOf, OnBytes/Tie/Pv/Tail/SizeOf.lean) at that
    record: so radix and shift are the library's constants and no letters. THE PLAN's RECORD IS
    OPEN: it has no table of reads yet (the verifier closes the list in the run), while the
    smallness test stands at the closed record: the two Sizes are not equal (they part in the
    reads). hid reads of the sizes only the number of matrices, the rows, the columns, the radix and
    the shift (ownOf; colTot, Johnson/Goal/Meaning/HidWord.lean), and follows_sizeOf holds of every
    family of records with the plans' lists and numbers of matrices. The sum at every such family:
    means_follows, Johnson/Goal/Meaning/HidPlanFit.lean.
  nmFit X   a Bool: each of the 25 records' number of matrices is the length of its list.
  labAt X k a   the label of entry a.
  sizesAt X rad beta k   a signature's sizes with the plan's number of matrices, rows and columns;
    radix and shift are letters; the four fields that hid does not read (reads, combinations,
    digits' tables) are 0.
  seatBy f X s k   seats as a function f of the label (f label r c: the message's number, main row,
    place).
  pairFit, planFit X   THE TEST ON THE PLANS ALONE: at each of the 24 pairs of reader and owner both
    entries are there, with the same rows, the same columns and one label.
  Follows X s   the sizes s k, k < 25, follow the plans (number of matrices; rows and columns of the
    entries of the list), with one radix and one shift for all 25.
Main theorems:
  sizesFit_of_planFit, seatsOne_of_planFit   if s follows the plans and planFit X = true, then
    sizesFit X s = true and SeatsOne X s (seatBy f X s), for every f.
  follows_sizesAt, follows_sizeOf, follows_sizesOf   sizesAt follows the plans; where nmFit X =
    true, so does sizeOf at every family of records with the plans' lists and numbers of matrices.
  words_of_planFit   so the 24 equations hold at ownAt s (seatBy f X s) msg, for every f and msg.

What is not claimed here. planFit X = true and nmFit X = true: they are proved, of every public file
in scope, in Johnson/Goal/Meaning/HidPlanFit.lean and Johnson/Goal/Meaning/HidPlanNM.lean. (At an
example with fewer groups planFit is false by its text: it asks 12 groups and sub-proof 22.) That a
real signature follows the plans; that seats are a function of the label (no f is built here; its
source is the layout file). The program does not import this file.
-/
import Johnson.Goal.Meaning.HidSeat
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Layer (matIx)
open Cb.Pv.Tail (Size)

/-- The verifier's record of the smallness test in the plan of sub-proof k; the empty record if
there is no such plan. -/
def tlAt (X : Model.Verify.Public) (k : ℕ) : Model.HTailF2 :=
  if 24 < k then {}
  else if k = 24 then X.H.tl
  else if k % 2 = 0 then ((X.G[k / 2]?).map fun P => P.tl).getD {}
  else ((X.A[k / 2]?).map fun P => P.seam.tl).getD {}

/-- The list of matrices in the plan of sub-proof k. -/
def matsAt (X : Model.Verify.Public) (k : ℕ) : Array Model.TMat := (tlAt X k).mats

/-- The label of entry a of that list. -/
def labAt (X : Model.Verify.Public) (k a : ℕ) : ℕ := ((matsAt X k).getD a {}).aId

/-- Sizes with the plan's number of matrices, rows and columns. -/
def sizesAt (X : Model.Verify.Public) (rad beta k : ℕ) : Size where
  NM := (matsAt X k).size
  m a := ((matsAt X k).getD a {}).m
  k a := ((matsAt X k).getD a {}).k
  nr _ := 0
  tau := 0
  rad := rad
  lo := 0
  hi := 0
  beta := beta

/-- **The library's own sizes of the typed smallness test, read off the plan's record** (sizeOf,
OnBytes/Tie/Pv/Tail/SizeOf.lean): radix 2^20 and shift 2^17 are the library's constants. -/
def sizesOf (X : Model.Verify.Public) (k : ℕ) : Size := (OnBytes.Tie.Pv.Tail.sizeOf (tlAt X k)).size

/-- A test on the plans: each record's number of matrices is the length of its list. -/
def nmFit (X : Model.Verify.Public) : Bool :=
  (List.range 25).all fun k => decide ((tlAt X k).NM = (tlAt X k).mats.size)

/-- Seats as a function of the label. -/
def seatBy (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (X : Model.Verify.Public) (s : ℕ → Size) (k : ℕ) :
    Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ := fun μ => f (labAt X k μ.val)

/-- The test at one pair: entry a of sub-proof k against entry a' of sub-proof k'. -/
def pairFit (X : Model.Verify.Public) (k a k' a' : ℕ) : Bool :=
  decide (a < (matsAt X k).size) && decide (a' < (matsAt X k').size) &&
    decide (((matsAt X k).getD a {}).m = ((matsAt X k').getD a' {}).m) &&
    decide (((matsAt X k).getD a {}).k = ((matsAt X k').getD a' {}).k) &&
    decide (labAt X k a = labAt X k' a')

/-- **The test on the plans alone**, at the 24 pairs of reader and owner. -/
def planFit (X : Model.Verify.Public) : Bool :=
  ((List.range 12).all fun g =>
      (g == 0 || pairFit X (2 * g) (matIx X.y).iXI (2 * (g - 1)) (matIx X.y).iXO) &&
      pairFit X (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) (2 * g) (matIx X.y).iQA) &&
    pairFit X 24 (X.hS.NHf + 3) 22 (matIx X.y).iXO

/-- The sizes follow the plans, with one radix and one shift. -/
structure Follows (X : Model.Verify.Public) (s : ℕ → Size) : Prop where
  NM : ∀ k < 25, (s k).NM = (matsAt X k).size
  m : ∀ k < 25, ∀ a < (matsAt X k).size, (s k).m a = ((matsAt X k).getD a {}).m
  k : ∀ k < 25, ∀ a < (matsAt X k).size, (s k).k a = ((matsAt X k).getD a {}).k
  rad : ∀ k < 25, ∀ k' < 25, (s k).rad = (s k').rad
  beta : ∀ k < 25, ∀ k' < 25, (s k).beta = (s k').beta

theorem follows_sizesAt (X : Model.Verify.Public) (rad beta : ℕ) :
    Follows X (sizesAt X rad beta) :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **The library's sizes follow the plans, at every family of records that has the plans' lists and
numbers of matrices**, where each plan's record has as its number of matrices the length of its
list. The plan's own record is OPEN: its list of tables is empty until the verifier closes it in the
run (closeFuns), and the smallness test's messages start from the closed record. Closing keeps the
list of matrices and its length (closeFuns_keeps, Johnson/Road/FormsKeysPlan.lean). A group's check
and the head's close the plan's own record; an attention sub-proof's closes the record that
Seam.start makes of it (OnBytes/Model/Attention.lean), which keeps both fields by its text; no lemma
says so. That the closed records are such a family is not stated as a theorem. -/
theorem follows_sizeOf {X : Model.Verify.Public} {tl : ℕ → Model.HTailF2}
    (e : ∀ k < 25, (tl k).NM = (tlAt X k).NM ∧ (tl k).mats = (tlAt X k).mats)
    (n : nmFit X = true) : Follows X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size := by
  unfold nmFit at n
  rw [List.all_eq_true] at n
  refine ⟨fun k hk => ?_, fun k hk a _ => ?_, fun k hk a _ => ?_, fun _ _ _ _ => rfl,
    fun _ _ _ _ => rfl⟩
  · show (tl k).NM = (tlAt X k).mats.size
    rw [(e k hk).1]
    exact of_decide_eq_true (n k (List.mem_range.2 hk))
  · show ((tl k).mats.getD a {}).m = ((tlAt X k).mats.getD a {}).m
    rw [(e k hk).2]
  · show ((tl k).mats.getD a {}).k = ((tlAt X k).mats.getD a {}).k
    rw [(e k hk).2]

/-- At the plans' own, open records. -/
theorem follows_sizesOf {X : Model.Verify.Public} (n : nmFit X = true) : Follows X (sizesOf X) :=
  follows_sizeOf (fun _ _ => ⟨rfl, rfl⟩) n

section
variable {X : Model.Verify.Public} {s : ℕ → Size}

/-- One pair: the sizes. -/
theorem sizeAt_of_pairFit (F : Follows X s) {k a k' a' : ℕ} (hk : k < 25) (hk' : k' < 25)
    (p : pairFit X k a k' a' = true) : sizeAt (s k) (s k') a a' = true := by
  unfold pairFit at p
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p
  obtain ⟨⟨⟨⟨h, h'⟩, hm⟩, hc⟩, -⟩ := p
  unfold sizeAt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, F.rad k hk k' hk'⟩, F.beta k hk k' hk'⟩
  · rw [F.NM k hk]
    exact h
  · rw [F.NM k' hk']
    exact h'
  · rw [F.m k hk a h, F.m k' hk' a' h']
    exact hm
  · rw [F.k k hk a h, F.k k' hk' a' h']
    exact hc

/-- One pair: the seats. -/
theorem seatAt_of_pairFit (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {k a k' a' : ℕ}
    (p : pairFit X k a k' a' = true) :
    SeatAt (s k) (s k') (seatBy f X s k) (seatBy f X s k') a a' := by
  unfold pairFit at p
  simp only [Bool.and_eq_true, decide_eq_true_eq] at p
  intro _ _ i _ c _
  show f (labAt X k a) i c = f (labAt X k' a') i c
  rw [p.2]

/-- What planFit says, pair by pair. -/
theorem pairs_of_planFit (p : planFit X = true) :
    (∀ g, 0 < g → g < 12 →
      pairFit X (2 * g) (matIx X.y).iXI (2 * (g - 1)) (matIx X.y).iXO = true) ∧
    (∀ g < 12, pairFit X (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) (2 * g) (matIx X.y).iQA = true) ∧
    pairFit X 24 (X.hS.NHf + 3) 22 (matIx X.y).iXO = true := by
  unfold planFit at p
  rw [Bool.and_eq_true, List.all_eq_true] at p
  obtain ⟨p1, p2⟩ := p
  refine ⟨fun g h0 hg => ?_, fun g hg => ?_, p2⟩
  · have q := p1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, Bool.or_eq_true] at q
    rcases q.1 with e | e
    · exact absurd (beq_iff_eq.1 e) (by omega)
    · exact e
  · have q := p1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true] at q
    exact q.2

/-- **The test on the sizes, from the test on the plans.** -/
theorem sizesFit_of_planFit (F : Follows X s) (p : planFit X = true) : sizesFit X s = true := by
  obtain ⟨a, b, c⟩ := pairs_of_planFit p
  unfold sizesFit
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun g hg => ?_, sizeAt_of_pairFit F (by norm_num) (by norm_num) c⟩
  have hg' := List.mem_range.1 hg
  rw [Bool.and_eq_true, Bool.or_eq_true]
  refine ⟨?_, sizeAt_of_pairFit F (by omega) (by omega) (b g hg')⟩
  by_cases h0 : g = 0
  · exact Or.inl (beq_iff_eq.2 h0)
  · exact Or.inr (sizeAt_of_pairFit F (by omega) (by omega) (a g (by omega) hg'))

/-- **One seat at each pair, from the test on the plans**, whatever function of the label the seats
are. -/
theorem seatsOne_of_planFit (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (p : planFit X = true) :
    SeatsOne X s (seatBy f X s) := by
  obtain ⟨a, b, c⟩ := pairs_of_planFit p
  exact ⟨fun g h0 hg => seatAt_of_pairFit f (a g h0 hg), fun g hg => seatAt_of_pairFit f (b g hg),
    seatAt_of_pairFit f c⟩

/-- **So the 24 equations hold at the lists of every witness**, whatever function of the label the
seats are. -/
theorem words_of_planFit (F : Follows X s) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (p : planFit X = true)
    (msg : Msgs) :
    OneWord X (ownAt s (seatBy f X s) msg) ∧ HeadWord X (ownAt s (seatBy f X s) msg) :=
  words_of_fit (sizesFit_of_planFit F p) (seatsOne_of_planFit f p) msg

end

end Meaning

#print axioms Meaning.follows_sizesAt
#print axioms Meaning.follows_sizeOf
#print axioms Meaning.follows_sizesOf
#print axioms Meaning.sizeAt_of_pairFit
#print axioms Meaning.seatAt_of_pairFit
#print axioms Meaning.pairs_of_planFit
#print axioms Meaning.sizesFit_of_planFit
#print axioms Meaning.seatsOne_of_planFit
#print axioms Meaning.words_of_planFit
