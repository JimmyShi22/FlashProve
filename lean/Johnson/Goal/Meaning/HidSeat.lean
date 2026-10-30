-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidSeat.lean: hid from a witness that holds a message a number: Part B of
Johnson/Goal/Meaning/HidOwn.lean fitted to the witness of the rule of composition, and the 24
equations from public letters.

The witness of the rule of composition holds, beside the token, a message for each number: mask row
or main row, row, place ↦ an element of the field; ONE component for all copies of a message that is
kept. A sub-proof's symbols are read in it through a letter seat. This file imports no file on that
rule: it takes the messages as a letter msg of that type.

THE SEAT's TYPE. seat μ r c : the message's number, its main row and its place, for the matrix μ,
the row of symbols r and the column c. A seat of the form (message's number, first main row, first
place), with symbol (μ, r, c) at row first + r, place first + c, would be too narrow: the layout
file lays an array block by block (OnBytes/Params/Items.lean: LaidBlock), so that a column may run
along a row's places, wrap over rows and lie in several rectangles.

Main names:
  symAt s seat msg   the symbols of one sub-proof's matrices, read in the messages at the seats.
  ownAt s seat msg   ownOf at these symbols: the 25 lists.
  hidAt X s seat tok msg   hidOf at these lists: THE MAP FROM A WITNESS (its token, its messages) TO
    Hid.
  sameArr_of_seat   two entries with the same sizes and, within these, ONE SEAT are SameArr
    (Johnson/Goal/Meaning/HidWord.lean): by the make, for every msg.
  sizeAt, sizesFit   a Bool on public letters alone (X, the sizes s): at each of the 24 pairs of
    reader and owner both are entries, with the same rows, columns, radix and shift.
  SeatAt, SeatsOne   a Prop on public letters (functions cannot be compared by a Bool): at each of
    the 24 pairs reader's and owner's seats are one, at the rows of symbols and columns within the
    reader's sizes.
  words_of_fit   sizesFit = true and SeatsOne give OneWord and HeadWord at ownAt, for every msg.
  hidAt_MA, hidAt_MG   under both, (hidAt …).MA g = ownAt … (2 g + 1) and (hidAt …).MG g = ownAt …
    (2 g), as functions: for a caller that comes one clause at a time, or with an equation at all
    names.
  means_hidAt   THE SUM: in scope, under both: the 24 records at ownAt and the head's clause at the
    stream that the library reads in the head's own cells give Means at hidAt.

What is not claimed. THE SEATS AND THE SIZES ARE LETTERS: that they are those of the verifier's
plans and of the layout file is not shown here (Johnson/Goal/Meaning/HidPlan.lean reads sizes and
labels off the plans). That the messages of a witness are what is committed (the pins), and that a
kept message's old and new copies are one component: the commitments' side. That any run meets the
records. Nothing on probabilities or on hiding. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidWord
import Johnson.Goal.Meaning.HidLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size Syms)

/-- A witness's messages: number ↦ (mask row or main row, row, place ↦ an element). -/
abbrev Msgs : Type := ℕ → Bool → ℕ → ℕ → Cb.Gl.E

/-- **The symbols of a sub-proof's matrices, read in the messages.** seat μ r c: the message's
number, its main row and its place, for row of symbols r and column c of the matrix μ. -/
def symAt (s : Size) (seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) : Syms Cb.Gl.E s :=
  fun μ r c => msg (seat μ r.val c.val).1 false (seat μ r.val c.val).2.1 (seat μ r.val c.val).2.2

/-- The 25 lists behind these symbols. -/
noncomputable def ownAt (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msg : Msgs) : ℕ → Mats ℤ := ownOf s fun k => symAt (s k) (seat k) msg

/-- **The hidden values of a witness.** -/
noncomputable def hidAt (X : Model.Verify.Public) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (tok : Fin ppref.V) (msg : Msgs) : Hid :=
  hidOf X tok (ownAt s seat msg)

/-- **The same sizes and one seat: the same symbols**, whatever the messages. -/
theorem sameArr_of_seat {s s' : Size} {seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ} {a a' : ℕ} (h : a < s.NM) (h' : a' < s'.NM)
    (hm : s.m a = s'.m a') (hk : s.k a = s'.k a') (hr : s.rad = s'.rad) (hb : s.beta = s'.beta)
    (hs : ∀ i < Alg.symRows (s.m a), ∀ c < s.k a, seat ⟨a, h⟩ i c = seat' ⟨a', h'⟩ i c)
    (msg : Msgs) : SameArr s (symAt s seat msg) a s' (symAt s' seat' msg) a' :=
  ⟨h, h', hm, hk, hr, hb, fun i c => by
    unfold symTot
    rw [dif_pos h, dif_pos h']
    by_cases hi : i < Alg.symRows (s.m a)
    · have hi' : i < Alg.symRows (s'.m a') := hm ▸ hi
      rw [dif_pos hi, dif_pos hi']
      by_cases hc : c < s.k a
      · have hc' : c < s'.k a' := hk ▸ hc
        rw [dif_pos hc, dif_pos hc']
        unfold symAt
        rw [hs i hi c hc]
      · have hc' : ¬ c < s'.k a' := hk ▸ hc
        rw [dif_neg hc, dif_neg hc']
    · have hi' : ¬ i < Alg.symRows (s'.m a') := hm ▸ hi
      rw [dif_neg hi, dif_neg hi']⟩

/-- The test on sizes at one pair of entries. -/
def sizeAt (s s' : Size) (a a' : ℕ) : Bool :=
  decide (a < s.NM) && decide (a' < s'.NM) && decide (s.m a = s'.m a') &&
    decide (s.k a = s'.k a') && decide (s.rad = s'.rad) && decide (s.beta = s'.beta)

/-- One seat at one pair of entries, within the reader's sizes. -/
def SeatAt (s s' : Size) (seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ) (a a' : ℕ) : Prop :=
  ∀ (h : a < s.NM) (h' : a' < s'.NM), ∀ i < Alg.symRows (s.m a), ∀ c < s.k a,
    seat ⟨a, h⟩ i c = seat' ⟨a', h'⟩ i c

theorem sameArr_of_fit {s s' : Size} {seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ} {a a' : ℕ} (f : sizeAt s s' a a' = true)
    (o : SeatAt s s' seat seat' a a') (msg : Msgs) :
    SameArr s (symAt s seat msg) a s' (symAt s' seat' msg) a' := by
  unfold sizeAt at f
  simp only [Bool.and_eq_true, decide_eq_true_eq] at f
  obtain ⟨⟨⟨⟨⟨h, h'⟩, hm⟩, hk⟩, hr⟩, hb⟩ := f
  exact sameArr_of_seat h h' hm hk hr hb (o h h') msg

/-- **The test on the sizes at the 24 pairs of reader and owner**: a Bool on public letters alone.
-/
def sizesFit (X : Model.Verify.Public) (s : ℕ → Size) : Bool :=
  ((List.range 12).all fun g =>
      (g == 0 || sizeAt (s (2 * g)) (s (2 * (g - 1))) (matIx X.y).iXI (matIx X.y).iXO) &&
      sizeAt (s (2 * g + 1)) (s (2 * g)) ((Hd.shapeA X g).cf.NAs + 3) (matIx X.y).iQA) &&
    sizeAt (s 24) (s 22) (X.hS.NHf + 3) (matIx X.y).iXO

/-- **Reader's and owner's seats are one, at the 24 pairs.** -/
structure SeatsOne (X : Model.Verify.Public) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) : Prop where
  ff : ∀ g, 0 < g → g < 12 → SeatAt (s (2 * g)) (s (2 * (g - 1))) (seat (2 * g))
    (seat (2 * (g - 1))) (matIx X.y).iXI (matIx X.y).iXO
  att : ∀ g < 12, SeatAt (s (2 * g + 1)) (s (2 * g)) (seat (2 * g + 1)) (seat (2 * g))
    ((Hd.shapeA X g).cf.NAs + 3) (matIx X.y).iQA
  head : SeatAt (s 24) (s 22) (seat 24) (seat 22) (X.hS.NHf + 3) (matIx X.y).iXO

section
variable {X : Model.Verify.Public} {s : ℕ → Size}
  {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}

/-- **Under the test on sizes and one seat at each pair, the 24 equations hold at the lists of every
witness.** -/
theorem words_of_fit (f : sizesFit X s = true) (o : SeatsOne X s seat) (msg : Msgs) :
    OneWord X (ownAt s seat msg) ∧ HeadWord X (ownAt s seat msg) := by
  unfold sizesFit at f
  rw [Bool.and_eq_true, List.all_eq_true] at f
  obtain ⟨f1, f2⟩ := f
  have F : ∀ g < 12, _ := fun g hg => f1 g (List.mem_range.2 hg)
  refine ⟨oneWord_ownOf (fun g h0 hg => ?_) (fun g hg => ?_),
    headWord_ownOf (sameArr_of_fit f2 o.head msg)⟩
  · have k := F g hg
    rw [Bool.and_eq_true, Bool.or_eq_true] at k
    rcases k.1 with e | e
    · exact absurd (beq_iff_eq.1 e) (by omega)
    · exact sameArr_of_fit e (o.ff g h0 hg) msg
  · have k := F g hg
    rw [Bool.and_eq_true] at k
    exact sameArr_of_fit k.2 (o.att g hg) msg

/-- What the test on sizes says, pair by pair. -/
theorem sizes_of_fit (f : sizesFit X s = true) :
    (∀ g, 0 < g → g < 12 →
      sizeAt (s (2 * g)) (s (2 * (g - 1))) (matIx X.y).iXI (matIx X.y).iXO = true) ∧
    (∀ g < 12, sizeAt (s (2 * g + 1)) (s (2 * g)) ((Hd.shapeA X g).cf.NAs + 3) (matIx X.y).iQA =
      true) := by
  unfold sizesFit at f
  rw [Bool.and_eq_true, List.all_eq_true] at f
  refine ⟨fun g h0 hg => ?_, fun g hg => ?_⟩
  · have k := f.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true, Bool.or_eq_true] at k
    rcases k.1 with e | e
    · exact absurd (beq_iff_eq.1 e) (by omega)
    · exact e
  · have k := f.1 g (List.mem_range.2 hg)
    rw [Bool.and_eq_true] at k
    exact k.2

/-- **The lists of a witness's hidden values ARE the sub-proofs' own lists**, as functions:
attention's. -/
theorem hidAt_MA (f : sizesFit X s = true) (o : SeatsOne X s seat) (tok : Fin ppref.V) (msg : Msgs)
    {g : ℕ} (hg : g < 12) : (hidAt X s seat tok msg).MA g = ownAt s seat msg (2 * g + 1) :=
  maOf_ownOf (sameArr_of_fit ((sizes_of_fit f).2 g hg) (o.att g hg) msg)

/-- The groups'. -/
theorem hidAt_MG (f : sizesFit X s = true) (o : SeatsOne X s seat) (tok : Fin ppref.V) (msg : Msgs)
    {g : ℕ} (hg : g < 12) : (hidAt X s seat tok msg).MG g = ownAt s seat msg (2 * g) :=
  mgOf_ownOf fun h0 => sameArr_of_fit ((sizes_of_fit f).1 g h0 hg) (o.ff g h0 hg) msg

/-- **The sum**: in scope, under the test on sizes and one seat at each pair: the 24 records at the
lists of a witness, and the head's clause at the stream that the library reads in the head's own
cells, give Means at the witness's hidden values. -/
theorem means_hidAt {pol KL : ByteArray} {lay : Option ByteArray}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (f : sizesFit X s = true)
    (o : SeatsOne X s seat) {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V)
    (msg : Msgs)
    (G : ∀ g < 12,
      LayerOrd (layerShape X.P) X.layers.sc X.y g (ownAt s seat msg (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g) (ownAt s seat msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAt s seat msg 24))) :
    Means X pp i x (hidAt X s seat tok msg) :=
  means_of_ords h C tok (words_of_fit f o msg).1 (words_of_fit f o msg).2 G At H

end

end Meaning

#print axioms Meaning.sameArr_of_seat
#print axioms Meaning.sameArr_of_fit
#print axioms Meaning.words_of_fit
#print axioms Meaning.sizes_of_fit
#print axioms Meaning.hidAt_MA
#print axioms Meaning.hidAt_MG
#print axioms Meaning.means_hidAt
