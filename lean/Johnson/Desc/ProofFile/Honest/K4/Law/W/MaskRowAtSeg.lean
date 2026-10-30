-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskRowAtSeg.lean: CONDITIONAL. Two abbreviations, statements
with their proofs.

What is here. Law/W/MaskRowWritten.lean gives the seat, the number in the witness, the shape and the
mask code's length of the member u at the mask row of the segment of the feed-forward layers' own
rounds (sub-protocol K4) as terms that name no u. These terms still name the lookup's place xl,
which stands under ∃ as u does (`layAt_laid`, Law/W/LayAtHead.lean), and the proof h. HERE THEY ARE
GIVEN AS TERMS IN THE PUBLIC PART Zp, THE LAYOUT FILE Z.lay AND THE SEGMENT's NUMBER m ALONE. (1)
They read xl through its field link alone, which is m: the four at m, under `MaskRowPub` and hl :
xl.link = m (`maskRow_seat_at`, `maskRow_num_at`, `maskRow_shape_at`, `maskRow_ell_at`). (2) The
five fields of `h.𝔇` that they read take no field of the proof: they are the library's `P5J.At.arr`,
`cs`, `sentAt` and `seat3At` at Zp and `rad3At` at Zp and Z.lay, by unfolding (`atArr_is`,
`atCs_is`, `atSent_is`, `atSeat_is`, `atRad_is`). (3) `maskSeatAt`, `maskNumAt`: the seat and the
number as definitions with code, which name neither h nor xl nor u: abbreviations of
`Lot.k4MaskSeat` and `Lot.k4MaskNum` (Lot/MaskNum.lean), where the texts lie, outside the files of
laws, so that a definition of the honest prover's messages can import them; for the length the
library has such a definition, `maskEllAt` (Johnson/Road/K4/Rec/MaskEllB.lean), with a test on it
(`slotsFitB`). `maskRow_seat_free`, `maskRow_num_free`, `maskRow_shape_free`, `maskRow_ell_free`:
u's are these; `maskRow_room_free`: the place's number of entries of the mask row is within that
length. (4) `maskRow_laid`: UNDER h AND `LaidK4` ALONE THERE ARE xl, o AND u WITH hx, xl's link and
number of entries of the mask row, `MaskRowPub` AND THE FOUR OF (3): one statement to take them
from.
How. Rewriting by hl; unfolding; `layAt_laid`, `maskRowPub_head` (Law/W/MaskSixHead.lean) and the
four of Law/W/MaskRowWritten.lean.

Not shown here. WHAT THE THREE TERMS ARE WORTH AS NUMBERS: nothing is evaluated here; at the
library's written values Law/W/MaskEllHead.lean has the length. WHERE THE LINK HAS NO MESSAGE WITH
MASK ROWS they answer all the same (the search's default 0; the library's length 0); under
`MaskRowPub` there is one. That the mask code's length is at least 1 is not shown here:
Law/W/MaskEllHead.lean has the length as a number. THAT THE NUMBERS OF TWO SEGMENTS DIFFER is not
shown here: Law/W/MaskNumsApart.lean has it, under h, of the twelve segments of the feed-forward
layers' own rounds. Every limit of the heads of Law/W/MaskSixHead.lean and Law/W/MaskRowWritten.lean
holds here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). h is the only hypothesis of `atArr_is`, `atCs_is`, `atSent_is`,
`atSeat_is` and `atRad_is`; `maskRow_laid` asks `LaidK4`, which h gives at each group (`laid_at`,
Law/LaidAtGroup.lean), besides. The ten statements between them take P (`MaskRowPub`), and nine of
them hl: `maskRow_laid` has both. THE FULL SIZE ALONE, and the format's second hash function alone. A
program's walk from import to import, which reads import lines alone and stops unopened at
Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under
Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART:
no file that defines a part of the proof file's description may import this one. Nothing on
soundness, on completeness or on any other property. No property is claimed.

  `atArr_is`, `atCs_is`, `atSent_is`, `atSeat_is`, `atRad_is`   five fields of `h.𝔇`
  `maskSeatAt`, `maskNumAt`   the seat and the number: in Zp and m: abbreviations
  `maskRow_ell_lib`   the length at u's shape is the library's `maskEllAt`
  `maskRow_seat_at`, `maskRow_num_at`, `maskRow_shape_at`, `maskRow_ell_at`   the four at m
  `maskRow_seat_free`, `maskRow_num_free`, `maskRow_shape_free`, `maskRow_ell_free`
      **the four with right sides that name no h**
  `maskRow_room_free`   the place's entries are within the length
  `maskRow_laid`   **xl, o, u and these four, under h and `LaidK4` alone**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskRowWritten
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LayAtHead
import Johnson.Road.K4.Rec.MaskEllB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Johnson.Pack (pMask)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4 (k4DataWide parOf)
open OnBytes.Road.K4.Rec (RecPlan recPlanOf maskEllAt)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt sigListCalls)
open VerifiableInference.Desc.Sound (Mem seatOf numOf mgBase)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-! ## 1 Two abbreviations, in the public part and the segment's number -/

/-- The seat that the plan gives segment m's first message with mask rows. Where no message of the
segment has mask rows the search's default 0 stands in: then this is what the plan's function
answers at the number of the kept messages. An abbreviation: the text is `Lot.k4MaskSeat`'s
(Lot/MaskNum.lean). -/
abbrev maskSeatAt (Zp : ProofFile.Pub) (m : ℕ) : ℕ × ℕ := Lot.k4MaskSeat Zp m

/-- The number in the witness of the message at that seat. An abbreviation: the text is
`Lot.k4MaskNum`'s (Lot/MaskNum.lean). -/
abbrev maskNumAt (Zp : ProofFile.Pub) (m : ℕ) : ℕ := Lot.k4MaskNum Zp m

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-! ## 2 Five fields of the structure under h -/

/-- At every h, by unfolding. -/
theorem atArr_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) : h.𝔇.arr = P5J.At.arr Zp := rfl

/-- At every h, by unfolding. -/
theorem atCs_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) : h.𝔇.cs = P5J.At.cs Zp := rfl

/-- At every h, by unfolding. -/
theorem atSent_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    h.𝔇.sent = P5J.At.sentAt Zp := rfl

/-- At every h, by unfolding. -/
theorem atSeat_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    h.𝔇.l3.seat = P5J.At.seat3At Zp := rfl

/-- At every h, by unfolding. -/
theorem atRad_is (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    h.𝔇.l3.rad = P5J.At.rad3At Zp Z.lay := rfl

/-! ## 3 The four, at the segment's number; then with right sides that name no h -/

section
variable {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {R : RecPlan} {n m : ℕ}
  {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}

/-- CONDITIONAL on P and hl. u's seat, at the segment's number. -/
theorem maskRow_seat_at (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    seatOf u = h.𝔇.l3.seat m false (maskPosOf h.𝔇.sent m) := by
  have e := maskRow_seat P
  rw [hl] at e
  exact e

/-- CONDITIONAL on P and hl. u's number in the witness, at the segment's number. -/
theorem maskRow_num_at (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    numOf h.𝔇.arr u =
      h.𝔇.arr (h.𝔇.l3.seat m false (maskPosOf h.𝔇.sent m)).1
        (h.𝔇.l3.seat m false (maskPosOf h.𝔇.sent m)).2 := by
  have e := maskRow_num P
  rw [hl] at e
  exact e

/-- CONDITIONAL on P and hl. u's shape, at the segment's number. -/
theorem maskRow_shape_at (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    ((sigListCalls h.𝔇.sent h.𝔇.l3.rad m)[maskPosOf h.𝔇.sent m]?).map (·.1) =
      some (u.1.l.get u.2).1 := by
  have e := maskRow_shape P
  rw [hl] at e
  exact e

/-- CONDITIONAL on P and hl. The mask code's length at u's shape, at the segment's number. -/
theorem maskRow_ell_at (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    ((sigListCalls h.𝔇.sent h.𝔇.l3.rad m)[maskPosOf h.𝔇.sent m]?).map
        (fun z => (pMask h.𝔇.cs z.1).ell) = some (pMask h.𝔇.cs (u.1.l.get u.2).1).ell := by
  have e := maskRow_ell P
  rw [hl] at e
  exact e

/-- CONDITIONAL on P. The mask code's length at u's shape is the library's `maskEllAt`. -/
theorem maskRow_ell_lib (P : MaskRowPub h R n m xl o u) :
    (pMask h.𝔇.cs (u.1.l.get u.2).1).ell = maskEllAt h.𝔇.sent h.𝔇.l3.rad xl.link := by
  obtain ⟨mI, hm, hf, -, hsh⟩ := P.seat
  have e : maskEllAt h.𝔇.sent h.𝔇.l3.rad xl.link =
      (pMask h.𝔇.sent.codes ((sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).get ⟨_, hm⟩).1).ell := by
    unfold OnBytes.Road.K4.Rec.maskEllAt
    rw [hf]
    exact dif_pos hm
  rw [hsh]
  exact e.symm

/-- CONDITIONAL on P and hl. **u's SEAT IS `maskSeatAt`.** -/
theorem maskRow_seat_free (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    seatOf u = maskSeatAt Zp m :=
  maskRow_seat_at P hl

/-- CONDITIONAL on P and hl. **u's NUMBER IN THE WITNESS IS `maskNumAt`.** -/
theorem maskRow_num_free (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    numOf h.𝔇.arr u = maskNumAt Zp m :=
  maskRow_num_at P hl

/-- CONDITIONAL on P and hl. **u's SHAPE**, off the library's list at Zp, Z.lay and m. -/
theorem maskRow_shape_free (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    ((sigListCalls (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) m)[maskPosOf
      (P5J.At.sentAt Zp) m]?).map (·.1) = some (u.1.l.get u.2).1 :=
  maskRow_shape_at P hl

/-- CONDITIONAL on P and hl. **THE MASK CODE's LENGTH AT u's SHAPE IS THE LIBRARY's `maskEllAt`** at
Zp, Z.lay and m. -/
theorem maskRow_ell_free (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    (pMask h.𝔇.cs (u.1.l.get u.2).1).ell =
      maskEllAt (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) m := by
  have e := maskRow_ell_lib P
  rw [hl] at e
  exact e

/-- CONDITIONAL on P and hl. The place's number of entries of the mask row is within that length. -/
theorem maskRow_room_free (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) :
    xl.ns ≤ maskEllAt (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) m := by
  rw [← maskRow_ell_free P hl]
  exact P.room

end

/-! ## 4 Under h and `LaidK4` alone -/

/-- CONDITIONAL on h and Lh. **THE PLACE, THE MESSAGE NUMBER, THE MEMBER, AND THE FOUR WHOSE RIGHT
SIDES NAME NO h**: no prover, script, coin or state is named. -/
theorem maskRow_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    ∃ (xl : VerifiableInference.Desc.First.Look.Place) (o : ℕ) (u : Mem),
      layAt (P5J.At.X Zp) m = some xl ∧ xl.link = m ∧ xl.ns = (parOf x).hp.ns ∧
      MaskRowPub h
        (recPlanOf (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase)
          (k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).sd)
        ((k4DataWide h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) mgBase).N.msgsAt
          PS[k]?) m xl o u ∧
      seatOf u = maskSeatAt Zp m ∧ numOf h.𝔇.arr u = maskNumAt Zp m ∧
      ((sigListCalls (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) m)[maskPosOf
        (P5J.At.sentAt Zp) m]?).map (·.1) = some (u.1.l.get u.2).1 ∧
      (pMask h.𝔇.cs (u.1.l.get u.2).1).ell =
        maskEllAt (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) m := by
  obtain ⟨xl, hx, hl, -, -, -, hns⟩ := layAt_laid h Lh
  obtain ⟨o, u, P⟩ := maskRowPub_head h Lh hx
  exact ⟨xl, o, u, hx, hl, hns, P, maskRow_seat_free P hl, maskRow_num_free P hl,
    maskRow_shape_free P hl, maskRow_ell_free P hl⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.atArr_is
#print axioms ProofFile.Honest.K4.W.atCs_is
#print axioms ProofFile.Honest.K4.W.atSent_is
#print axioms ProofFile.Honest.K4.W.atSeat_is
#print axioms ProofFile.Honest.K4.W.atRad_is
#print axioms ProofFile.Honest.K4.W.maskRow_seat_at
#print axioms ProofFile.Honest.K4.W.maskRow_num_at
#print axioms ProofFile.Honest.K4.W.maskRow_shape_at
#print axioms ProofFile.Honest.K4.W.maskRow_ell_at
#print axioms ProofFile.Honest.K4.W.maskRow_ell_lib
#print axioms ProofFile.Honest.K4.W.maskRow_seat_free
#print axioms ProofFile.Honest.K4.W.maskRow_num_free
#print axioms ProofFile.Honest.K4.W.maskRow_shape_free
#print axioms ProofFile.Honest.K4.W.maskRow_ell_free
#print axioms ProofFile.Honest.K4.W.maskRow_room_free
#print axioms ProofFile.Honest.K4.W.maskRow_laid
