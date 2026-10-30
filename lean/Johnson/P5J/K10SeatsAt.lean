-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K10SeatsAt.lean (kind K10): THE PREMISE seats THAT K10HXAt.lean LEFT ("under X the book
places message no i at seat i"), DRAWN AT THE CLOSED CONSTANT, AT ALL 25 LINKS, AT seat := seatK10
(loAt l) (At.pseats Zp) l, FROM THE TABLE's PROMISE, FoldFacts AND PUBLIC FACTS; AND SO THE FIELD
hX OF `K10Heavy` WITH NO PREMISE OF ITS OWN ON THE STATE: WHAT IS LEFT ON STATES IS FoldFacts,
ITSELF A SENTENCE ON ALL REACHED STATES AND A PREMISE HERE. Statements and proofs: a join; kernel
lines, one with a negative line.

What is joined. seat_at_book (NoOfLink.lean: the first chain's reader places message
o at the plan's o-th place) takes six things:
  hbook: the book stands where the plan says: OUT OF THE TABLE's PROMISE (bookAt_of_onQ,
    EqRestOf.lean).
  hseats, hord: the seats are carried; the book is in order: TWO FIELDS OF FoldFacts, at At.foldD's
    own L and ft (by definition Ld and 0).
  hlt, hpl: the member's number lies below the messages sent at K10's place, and the plan's list of
    places has the member's seat at it: hB_at_k10 (BelowAtK10.lean), in scope, where the
    value is laid.
  hb: the first places of the plan's list name trees that the book has: `AtMgA.below_at`: from
    hbook (the book's two sizes are the plan's counts), counts_at_name
    (CountsAtName.lean: the counts at every border are the written ones) and below_written
    (ToldCounts.lean: BY THE KERNEL, at all 359 written pairs).

What is said.
  `ten_is_ix`: `LinkJoin.tenAt l`, K10's place of link l, is ixK10 l. `ten_is_ix_off`: THE NEGATIVE
    LINE. `ix_le`: it is at most 358.
  `AtMgA.below_at` · `AtMgA.seats_at`: **the premise.** · `AtMgA.hX_paid`: **K10Heavy's field hX at
    the constant's letters, at every l < 25.**

PREMISES. h : AtMgA OnBytes.secondHashFunction .. · hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld
(in scope Ld is the written list: ld_at_laid) · **Fo : FoldFacts at h.rch and At.foldD Zp cF Ld (a
premise of this file; P5J.AtMgA.fold_full, Johnson/P5J/MaskLettersAtMg.lean, gives it from the head
at the written list. THE TERM At.foldD ITSELF HAS BEEN EVALUATED NOWHERE: the facts were evaluated
on an honest run at a FoldData laid by the same makers, but through other terms: see the head of
Johnson/P5J/FoldAt.lean)** · hp · hM, hZ.

Limits. AT LINK 0 IT STANDS AT THE SIX-LIST (the five-list is spent there in
K10HXFive.lean). AtMgA and FoldFacts are premises. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P5J.K10HXAt
import Johnson.LPFE1R.BelowAtK10
import Johnson.Desc.First.Link.Law.EqRestOf
import Johnson.HB.LLHARD.ToldCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData bookAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks noK10 seatK10 seat_at_book)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt hB_at_k10 ld_at_laid bookAt_of_onQ)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes placesBelowB)
open VerifiableInference.Desc.K13.Law (countsFull below_written LFull)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: the two names of K10's number of link l. -/
theorem ten_is_ix : ∀ l, l < 25 → VerifiableInference.Desc.LinkJoin.tenAt l = ixK10 l := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: it is never the next link's. -/
theorem ten_is_ix_off :
    (List.range 24).any (fun l =>
      decide (VerifiableInference.Desc.LinkJoin.tenAt l = ixK10 (l + 1))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ix_le : ∀ l, l < 25 → ixK10 l ≤ 358 := by decide +kernel

/-- **hb**: under X the first places of the plan's list name trees that the book has. -/
theorem AtMgA.below_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (s : (ProofFile.InstPub × TS) × (Frame.E FR).Str) (hX : XK h l s) :
    placesBelowB LFull s.1.2.book.place.size s.1.2.book.trees.size = true := by
  obtain ⟨hon, -, hu'⟩ := hX
  have hu : s.1.2.failed = none := not_not.1 hu'
  have e := bookAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) s hon hu
  have hc := counts_at_name h.toAtMg.scope h.toAtMg.laid (k := ixK10 l) (ix_le l hl)
  have hw := List.all_eq_true.1 below_written _ (List.mem_of_getElem? hc)
  unfold bookAt at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  rw [e.1.1, e.1.2, e.2]
  exact hw

/-- **seats, AT THE CONSTANT.** -/
theorem AtMgA.seats_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (hl : l < 25) :
    ∀ s, XK h l s → ∀ i, memMain (loAt l) i →
      seatBy noFirst s.1.2.book (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l i) =
        some (seatK10 (loAt l) (At.pseats Zp) l i) := by
  intro s hX i _
  have hb := h.below_at l hl s hX
  obtain ⟨hon, hr, hu'⟩ := hX
  have hu : s.1.2.failed = none := not_not.1 hu'
  have hbook := bookAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) s
    hon hu
  have hseats := Fo.seatsCarried (ixK10 l) s hr hu
  have hord := Fo.bookInOrder (ixK10 l) s hr hu
  obtain ⟨b1, b2, -⟩ := hB_at_k10 h.toAtMg.scope h.toAtMg.laid hLd hl i
  rw [ten_is_ix l hl] at b1
  obtain rfl : LFull = Ld :=
    Option.some.inj ((ld_at_laid h.toAtMg.scope h.toAtMg.laid).symm.trans hLd)
  exact seat_at_book hbook hseats hord hb _ _ b1 b2

/-- **K10Heavy's FIELD hX, WITH NO PREMISE OF ITS OWN ON THE STATE.** -/
theorem AtMgA.hX_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (hl : l < 25) (p : Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      RowAsks (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l) (kbW l)
        (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
        (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
          (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
        (At.N Zp cF) (p.link.getD 0) (oAt (ixK10 l))
        (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) a.1 :=
  h.hX_at Ld Fo l hl p hp hM hZ _ (h.seats_at Ld hLd Fo l hl)

end P5J

#print axioms P5J.ten_is_ix
#print axioms P5J.ten_is_ix_off
#print axioms P5J.ix_le
#print axioms P5J.AtMgA.below_at
#print axioms P5J.AtMgA.seats_at
#print axioms P5J.AtMgA.hX_paid
