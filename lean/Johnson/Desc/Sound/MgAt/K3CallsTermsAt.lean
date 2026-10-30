-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsTermsAt.lean: THE LOOKUP ON A LINK's CALLS: THE THREE TERMS OF THE
KIND's LEDGER (the fields hid, small, reads of AttOwedR, LayOwedR:
Johnson/Desc/Sound/MgAt/K3Owed.lean), IN THE LEDGER's OWN TEXTS, at tls := Meaning.tlAt X and tok :=
fun w => P5J.tokVOf w.tok, WHERE THE COMPOSED MEANING's LETTER H IS THE READER OFF THE LIST OF
ROUNDS (P5J.hidAtPlan, Johnson/P5J/HidAtPlan.lean: hidAtSeat at the sizes sizesOf X
and seats seatsOf off the layout). hid and small: that reader's own text (rfl) carried over the
bridge "in scope the seats off the layout are the seats by the label" (seatsOf_all,
Johnson/Desc/First/Look/K3CallsModelSeats.lean). reads: readsOne_readAt
(Johnson/P5J/WordsAtQ.lean) at the seats by the label; its two premises on sizes and seats are
theorems in scope (fit_sizesOf). By calls alone. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the composed meaning's reader of a witness.
USER: nobody yet. Meant: the kind's files: the three fields at the constant.
LETTERS: Dm: the composed meaning's parameters (MgData, Johnson/Desc/Sound/MgAll.lean), at Tok := ℕ;
num, req, dec, hL, hN, hG: hidAtPlan's own; pol,
  KL, lay, C as in the scope's theorems.

WHAT IS LEFT, BOOKED: term: hH (Dm.H is hidAtPlan at Dm's own letters: at the constant an
  unfolding) · test: hN (SeatsNamed: hidAtPlan's own premise) · hG (GroupsSeated: the ledger's
  seated) · hP (PadsFree at the seats by the label: no place that the 24 pairs' seats name is a
  pad's).

Main names: `hid_of_plan`, `small_of_plan`, `seatsNamed_label`, `reads_of_plan`.

Limits. The goals' scope (through the public core C).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.Look.K3CallsModelSeats
import Johnson.P5J.HidAtPlan
import Johnson.P5J.WordsAtQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Road
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open _root_.Meaning (BaseSegF seatBy fLay hidAtF ReadsOne sizesFit sizesOf seatsOf laidThere
  fit_sizesOf)

section
variable {Xi P : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {pol KL : ByteArray} {lay : Option ByteArray}
  (Dm : MgData Xi P ℕ rows cols nR X) {num : ℕ → ℕ → ℕ}
  {req : P × P5J.TS → P5J.TReq}
  {dec : P × P5J.TS → Desc.Strs → Option (Fin rows → Fin cols → Flat.GE)}
  {hL : laidThere X (sizesOf X) Dm.sent.layout = true}
  {hN : SeatsNamed Dm.arr Dm.N (sizesOf X) (seatsOf X (sizesOf X) Dm.sent.layout num)}
  {hG : GroupsSeated Dm.ms Dm.N}

/-- **hid.** -/
theorem hid_of_plan (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hH : Dm.H =
      P5J.hidAtPlan X Dm.cs Dm.arr Dm.ms Dm.N Dm.sent.layout num req dec hL hN hG) :
    ∀ w, Dm.H.hid w = hidAtF X (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (_root_.Meaning.tlAt X j))
      (P5J.tokVOf w.tok)
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) :=
  hhid_of_seatsOf (layout := Dm.sent.layout) (num := num) (tok := fun w => P5J.tokVOf w.tok)
    (msgF := fun w j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) h C fun w => by
      rw [hH]
      rfl

/-- **small.** -/
theorem small_of_plan (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hH : Dm.H =
      P5J.hidAtPlan X Dm.cs Dm.arr Dm.ms Dm.N Dm.sent.layout num req dec hL hN hG) :
    ∀ j w, Dm.H.base j w → BaseSegF (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (_root_.Meaning.tlAt X j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) j :=
  hb_of_seatsOf (layout := Dm.sent.layout) (num := num)
    (msgF := fun w j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) h C fun j w hb => by
      rw [hH] at hb
      exact hb

/-- hidAtPlan's own premise on the numbers, at the seats by the label. -/
theorem seatsNamed_label (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hN' : SeatsNamed Dm.arr Dm.N (sizesOf X) (seatsOf X (sizesOf X) Dm.sent.layout num)) :
    SeatsNamed Dm.arr Dm.N (sizesOf X) (seatBy (fLay Dm.sent.layout num) X (sizesOf X)) := by
  rw [← seatsOf_all h C Dm.sent.layout num]
  exact hN'

/-- **reads.** -/
theorem reads_of_plan (h : Verify.publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (hN' : SeatsNamed Dm.arr Dm.N (sizesOf X) (seatsOf X (sizesOf X) Dm.sent.layout num))
    (hG' : GroupsSeated Dm.ms Dm.N)
    (hP : P5J.PadsFree Dm.cs Dm.arr Dm.ms Dm.N (sizesOf X)
      (seatBy (fLay Dm.sent.layout num) X (sizesOf X)) X) :
    ∀ w : Desc.Wit (CellsQ rows cols) ℕ MsgT, ReadsOne X (fun j => szOf (_root_.Meaning.tlAt X j))
      (seatBy (fLay Dm.sent.layout num) X fun j => szOf (_root_.Meaning.tlAt X j))
      (fun j => Desc.Sound.readAt Dm.cs Dm.arr Dm.ms Dm.N j w) := fun w =>
  P5J.readsOne_readAt (fit_sizesOf h C (fLay Dm.sent.layout num)).1
    (fit_sizesOf h C (fLay Dm.sent.layout num)).2 (seatsNamed_label Dm h C hN') hG' hP w

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hid_of_plan
#print axioms VerifiableInference.OnPublicFiles.small_of_plan
#print axioms VerifiableInference.OnPublicFiles.reads_of_plan
