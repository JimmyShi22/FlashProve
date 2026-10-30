-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidFamily.lean: a witness's hidden values where each sub-proof reads messages
of its own.

ownAt and hidAt (Johnson/Goal/Meaning/HidSeat.lean) read all 25 sub-proofs' symbols in ONE family of
messages msg. Where a message is kept and each copy has parts of its own, a sub-proof reads its own
group's copy. Here the reading is a family msgF : one Msgs for each sub-proof. The types of symAt
and of the seats stay.

What holds of one sub-proof's list carries by one line: ownAtF s seat msgF k is ownAt s seat (msgF
k) k, by unfolding (ownAtF_eq): the list of sub-proof k reads the symbols of sub-proof k alone. So
every statement of Johnson/Goal/Meaning/HidBase.lean holds at msgF k. What speaks of TWO sub-proofs
takes ONE PREMISE MORE: at each of the 24 pairs, reader's and owner's readings agree within the
reader's sizes (ReadsOne).

Main names:
  ownAtF, hidAtF, BaseSegF   the three at a family; ownAtF_eq, hidAtF_const, baseSegF_def: by
    unfolding.
  AgreeAt s s' seat seat' m m' a a'   at one pair: what the reader reads in m at its seats is what
    the owner reads in m' at its seats, at the rows of symbols and the columns within the reader's
    sizes.
  agreeAt_of_seat   from one seat at the pair, and m and m' agreeing at these seats.
  ReadsOne X s seat msgF   AgreeAt at the 24 pairs. readsOne_const: at a constant family it is
    SeatsOne's gift.
  sameArrF   the test on sizes and AgreeAt give SameArr.
  words_of_fitF, hidAtF_MA, hidAtF_MG, means_hidAtF   Johnson/Goal/Meaning/HidSeat.lean's four, at a
    family, under ReadsOne in the place of SeatsOne.
  MsgsOne X s f msgF, readsOne_of_msgs   at seats that are a function f of the label: ReadsOne
    follows, in scope, from: reader's and owner's messages agree at the seats f names for the
    reader's label.
  means_followsF, means_runF   THE SUM at a family: in scope, at sizes that follow the plans (at the
    closed records).

What is not claimed. ReadsOne or MsgsOne of any witness: that two copies of a kept message agree
where both are read is the commitments' side. THE SEAMS ARE STILL MOVED, NOT PAID: what the heads of
Johnson/Goal/Meaning/HidPlanFit.lean and Johnson/Goal/Meaning/HidPlanNM.lean name as owed stays
owed. The full size alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidClosed
import Johnson.Goal.Meaning.HidBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Cb.Pv.Tail (Size Syms Base)

/-- The 25 lists, each behind the symbols that its sub-proof reads in its own messages. -/
noncomputable def ownAtF (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msgF : ℕ → Msgs) : ℕ → Mats ℤ := ownOf s fun k => symAt (s k) (seat k) (msgF k)

/-- **The hidden values of a witness, at a family of readings.** -/
noncomputable def hidAtF (X : Model.Verify.Public) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (tok : Fin ppref.V) (msgF : ℕ → Msgs) : Hid :=
  hidOf X tok (ownAtF s seat msgF)

/-- The symbols of sub-proof k, read in its own messages, are the packing of small integers. -/
def BaseSegF (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msgF : ℕ → Msgs)
    (k : ℕ) : Prop := BaseSeg s seat (msgF k) k

section One
variable (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)

/-- **The list of sub-proof k reads the messages of sub-proof k alone.** -/
theorem ownAtF_eq (msgF : ℕ → Msgs) (k : ℕ) : ownAtF s seat msgF k = ownAt s seat (msgF k) k := rfl

theorem ownAtF_const (msg : Msgs) : ownAtF s seat (fun _ => msg) = ownAt s seat msg := rfl

theorem hidAtF_const (X : Model.Verify.Public) (tok : Fin ppref.V) (msg : Msgs) :
    hidAtF X s seat tok (fun _ => msg) = hidAt X s seat tok msg := rfl

theorem baseSegF_def (msgF : ℕ → Msgs) (k : ℕ) :
    BaseSegF s seat msgF k = Base (symAt (s k) (seat k) (msgF k)) := rfl

end One

/-- At one pair: what the reader reads in m at its seats is what the owner reads in m' at its seats,
within the reader's sizes. -/
def AgreeAt (s s' : Size) (seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ) (m m' : Msgs) (a a' : ℕ) : Prop :=
  ∀ (h : a < s.NM) (h' : a' < s'.NM), ∀ i < Alg.symRows (s.m a), ∀ c < s.k a,
    m (seat ⟨a, h⟩ i c).1 false (seat ⟨a, h⟩ i c).2.1 (seat ⟨a, h⟩ i c).2.2 =
      m' (seat' ⟨a', h'⟩ i c).1 false (seat' ⟨a', h'⟩ i c).2.1 (seat' ⟨a', h'⟩ i c).2.2

/-- From one seat at the pair, and the two messages agreeing at the reader's seats. -/
theorem agreeAt_of_seat {s s' : Size} {seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ} {m m' : Msgs} {a a' : ℕ}
    (o : SeatAt s s' seat seat' a a')
    (e : ∀ h : a < s.NM, ∀ i < Alg.symRows (s.m a), ∀ c < s.k a,
      m (seat ⟨a, h⟩ i c).1 false (seat ⟨a, h⟩ i c).2.1 (seat ⟨a, h⟩ i c).2.2 =
        m' (seat ⟨a, h⟩ i c).1 false (seat ⟨a, h⟩ i c).2.1 (seat ⟨a, h⟩ i c).2.2) :
    AgreeAt s s' seat seat' m m' a a' := fun h h' i hi c hc => by
  rw [← o h h' i hi c hc]
  exact e h i hi c hc

/-- **The test on sizes and agreeing readings: the same symbols.** -/
theorem sameArrF {s s' : Size} {seat : Fin s.NM → ℕ → ℕ → ℕ × ℕ × ℕ}
    {seat' : Fin s'.NM → ℕ → ℕ → ℕ × ℕ × ℕ} {m m' : Msgs} {a a' : ℕ}
    (f : sizeAt s s' a a' = true) (A : AgreeAt s s' seat seat' m m' a a') :
    SameArr s (symAt s seat m) a s' (symAt s' seat' m') a' := by
  unfold sizeAt at f
  simp only [Bool.and_eq_true, decide_eq_true_eq] at f
  obtain ⟨⟨⟨⟨⟨h, h'⟩, hm⟩, hk⟩, hr⟩, hb⟩ := f
  refine ⟨h, h', hm, hk, hr, hb, fun i c => ?_⟩
  unfold symTot
  rw [dif_pos h, dif_pos h']
  by_cases hi : i < Alg.symRows (s.m a)
  · have hi' : i < Alg.symRows (s'.m a') := hm ▸ hi
    rw [dif_pos hi, dif_pos hi']
    by_cases hc : c < s.k a
    · have hc' : c < s'.k a' := hk ▸ hc
      rw [dif_pos hc, dif_pos hc']
      exact A h h' i hi c hc
    · have hc' : ¬ c < s'.k a' := hk ▸ hc
      rw [dif_neg hc, dif_neg hc']
  · have hi' : ¬ i < Alg.symRows (s'.m a') := hm ▸ hi
    rw [dif_neg hi, dif_neg hi']

/-- **Reader's and owner's readings agree, at the 24 pairs.** -/
structure ReadsOne (X : Model.Verify.Public) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msgF : ℕ → Msgs) : Prop where
  ff : ∀ g, 0 < g → g < 12 → AgreeAt (s (2 * g)) (s (2 * (g - 1))) (seat (2 * g))
    (seat (2 * (g - 1))) (msgF (2 * g)) (msgF (2 * (g - 1))) (matIx X.y).iXI (matIx X.y).iXO
  att : ∀ g < 12, AgreeAt (s (2 * g + 1)) (s (2 * g)) (seat (2 * g + 1)) (seat (2 * g))
    (msgF (2 * g + 1)) (msgF (2 * g)) ((Hd.shapeA X g).cf.NAs + 3) (matIx X.y).iQA
  head : AgreeAt (s 24) (s 22) (seat 24) (seat 22) (msgF 24) (msgF 22) (X.hS.NHf + 3)
    (matIx X.y).iXO

section
variable {X : Model.Verify.Public} {s : ℕ → Size}
  {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ}

/-- At a constant family one seat at each pair is enough. -/
theorem readsOne_const (o : SeatsOne X s seat) (msg : Msgs) : ReadsOne X s seat fun _ => msg :=
  ⟨fun g h0 hg => agreeAt_of_seat (o.ff g h0 hg) fun _ _ _ _ _ => rfl,
    fun g hg => agreeAt_of_seat (o.att g hg) fun _ _ _ _ _ => rfl,
    agreeAt_of_seat o.head fun _ _ _ _ _ => rfl⟩

variable {msgF : ℕ → Msgs}

/-- **Under the test on sizes and agreeing readings, the 24 equations hold at the lists.** -/
theorem words_of_fitF (f : sizesFit X s = true) (R : ReadsOne X s seat msgF) :
    OneWord X (ownAtF s seat msgF) ∧ HeadWord X (ownAtF s seat msgF) := by
  obtain ⟨fa, fb⟩ := sizes_of_fit f
  have fc : sizeAt (s 24) (s 22) (X.hS.NHf + 3) (matIx X.y).iXO = true := by
    unfold sizesFit at f
    rw [Bool.and_eq_true] at f
    exact f.2
  exact ⟨oneWord_ownOf (fun g h0 hg => sameArrF (fa g h0 hg) (R.ff g h0 hg))
    (fun g hg => sameArrF (fb g hg) (R.att g hg)), headWord_ownOf (sameArrF fc R.head)⟩

/-- The lists of the hidden values are the sub-proofs' own lists, as functions: attention's. -/
theorem hidAtF_MA (f : sizesFit X s = true) (R : ReadsOne X s seat msgF) (tok : Fin ppref.V)
    {g : ℕ} (hg : g < 12) : (hidAtF X s seat tok msgF).MA g = ownAtF s seat msgF (2 * g + 1) :=
  maOf_ownOf (sameArrF ((sizes_of_fit f).2 g hg) (R.att g hg))

/-- The groups'. -/
theorem hidAtF_MG (f : sizesFit X s = true) (R : ReadsOne X s seat msgF) (tok : Fin ppref.V)
    {g : ℕ} (hg : g < 12) : (hidAtF X s seat tok msgF).MG g = ownAtF s seat msgF (2 * g) :=
  mgOf_ownOf fun h0 => sameArrF ((sizes_of_fit f).1 g h0 hg) (R.ff g h0 hg)

/-- **The sum at a family**, under the test on sizes and agreeing readings. -/
theorem means_hidAtF {pol KL : ByteArray} {lay : Option ByteArray}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) (f : sizesFit X s = true)
    (R : ReadsOne X s seat msgF) {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V)
    (G : ∀ g < 12,
      LayerOrd (layerShape X.P) X.layers.sc X.y g (ownAtF s seat msgF (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g) (ownAtF s seat msgF (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAtF s seat msgF 24))) :
    Means X pp i x (hidAtF X s seat tok msgF) :=
  means_of_ords h C tok (words_of_fitF f R).1 (words_of_fitF f R).2 G At H

end

/-! ## At seats that are a function of the label -/

/-- At one pair: the two messages agree at the seats that f names for the reader's label. -/
def MsgAt (X : Model.Verify.Public) (s : ℕ → Size) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (m m' : Msgs)
    (k a : ℕ) : Prop :=
  ∀ i < Alg.symRows ((s k).m a), ∀ c < (s k).k a,
    m (f (labAt X k a) i c).1 false (f (labAt X k a) i c).2.1 (f (labAt X k a) i c).2.2 =
      m' (f (labAt X k a) i c).1 false (f (labAt X k a) i c).2.1 (f (labAt X k a) i c).2.2

/-- **Reader's and owner's messages agree at the shared seats, at the 24 pairs.** -/
structure MsgsOne (X : Model.Verify.Public) (s : ℕ → Size) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msgF : ℕ → Msgs) : Prop where
  ff : ∀ g, 0 < g → g < 12 →
    MsgAt X s f (msgF (2 * g)) (msgF (2 * (g - 1))) (2 * g) (matIx X.y).iXI
  att : ∀ g < 12,
    MsgAt X s f (msgF (2 * g + 1)) (msgF (2 * g)) (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3)
  head : MsgAt X s f (msgF 24) (msgF 22) 24 (X.hS.NHf + 3)

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public} {s : ℕ → Size}
  {f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ} {msgF : ℕ → Msgs}

/-- In scope, at seats that are a function of the label, agreeing messages give agreeing readings.
-/
theorem readsOne_of_msgs (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (E : MsgsOne X s f msgF) : ReadsOne X s (seatBy f X s) msgF := by
  have o : SeatsOne X s (seatBy f X s) := seatsOne_of_planFit f (planFit_of_core h C)
  exact ⟨fun g h0 hg => agreeAt_of_seat (o.ff g h0 hg) fun _ i hi c hc => E.ff g h0 hg i hi c hc,
    fun g hg => agreeAt_of_seat (o.att g hg) fun _ i hi c hc => E.att g hg i hi c hc,
    agreeAt_of_seat o.head fun _ i hi c hc => E.head i hi c hc⟩

/-- **The sum at a family, in scope, at every family of sizes that follows the plans.** The seats
enter in the form seatBy f alone; f is a letter. -/
theorem means_followsF (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (F : Follows X s) (E : MsgsOne X s f msgF) {pp : ScalesAndPolicy} {i : Cm.Idx} {x : Instance ppref}
    (tok : Fin ppref.V)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAtF s (seatBy f X s) msgF (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g) (ownAtF s (seatBy f X s) msgF (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAtF s (seatBy f X s) msgF 24))) :
    Means X pp i x (hidAtF X s (seatBy f X s) tok msgF) :=
  means_hidAtF h C (sizesFit_of_planFit F (planFit_of_core h C)) (readsOne_of_msgs h C E) tok G At H

/-- **The sum at a family, at the closed records.** -/
theorem means_runF (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {tl : ℕ → Model.HTailF2} (c : ClosedAt X tl)
    (E : MsgsOne X (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) f msgF) {pp : ScalesAndPolicy}
    {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAtF (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msgF (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g)
      (ownAtF (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msgF (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X
      (ownAtF (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msgF 24))) :
    Means X pp i x (hidAtF X (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
      (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) tok msgF) :=
  means_followsF h C (follows_run h C c) E tok G At H

end Core

/-- MsgsOne holds at every constant family. -/
theorem msgsOne_const (X : Model.Verify.Public) (s : ℕ → Size) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ)
    (msg : Msgs) : MsgsOne X s f fun _ => msg :=
  ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

end Meaning

#print axioms Meaning.ownAtF_eq
#print axioms Meaning.ownAtF_const
#print axioms Meaning.hidAtF_const
#print axioms Meaning.baseSegF_def
#print axioms Meaning.agreeAt_of_seat
#print axioms Meaning.sameArrF
#print axioms Meaning.readsOne_const
#print axioms Meaning.words_of_fitF
#print axioms Meaning.hidAtF_MA
#print axioms Meaning.hidAtF_MG
#print axioms Meaning.means_hidAtF
#print axioms Meaning.readsOne_of_msgs
#print axioms Meaning.means_followsF
#print axioms Meaning.means_runF
#print axioms Meaning.msgsOne_const
