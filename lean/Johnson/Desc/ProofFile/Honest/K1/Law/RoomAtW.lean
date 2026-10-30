-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RoomAtW.lean: THE SHARED "SENDING" (the kind K1): THE RIDER OF
W's SENDING (number 356), ON THE ROWS: THE ROOM AT ITS PLAN · ITS TWO ROWS IN THE PART's OWN COINS ·
NO OTHER PLACE · THE ROWS FIX THE ELEVEN: AT THE WRITTEN PLAN BY LEAN's KERNEL, AND UNDER THE
LIBRARY's HEAD. PUBLIC IN FORM. Twelve theorems; no definition.

  - room_w_written: at W's sending's written plan (K1.parWF), at its ride: two messages; message 1
    has 2 mask rows; its mask code's message length is 256; the rider's coins begin at number 3882
    of the part's coins of the larger field; these are 4003.
  - room_first_written: the like at the opening's written plan (K1.parGF), message 3: 1 mask row;
    8192; 8411; 8958: OTHER NUMBERS: the test can fail.
  - room_w_head: UNDER THE HEAD (h, and the opening O): the five numbers at the head's own plan
    and ride.
  - ce's FENCE IS ELDER LAW, NOT RESTATED HERE: mask_any (Honest/K1/CoinsIn.lean: "whether its
    table rides or not") and seat_in (Honest/K1/Seat.lean) at the seat "mask coin number i", whose
    number is maskStart + i by another house's mask_no (Johnson/SendSim/At/Split.lean, a row of
    .
  - rider_rows: GENERAL IN THE PLAN: where message k rides at ⟨5, 1⟩, has 2 mask rows and room for
    10 places: THE TWO ROWS OF rowsR's MASK, with C i := ce cs (maskStart P ride k + i): row 0: C 2,
    0, C 3, C 4, C 5, C 6, C 7, C 9, C 10, C 8 · row 1: C 2 + C 0, C 1, C 3, C 4, C 5, C 6, C 7, C
    9, C 10, C 8.
  - rider_rows_fix: under the same three premises: two lists of coins whose masks agree at these
    twenty places agree at the eleven numbers.
  - w_rider_rows_head, w_rider_fix_head: both UNDER THE HEAD, at number 356's plan and ride: no
    premise but h and O.
  - w_rider_in_head: under the head the eleven numbers lie inside the part's count: 3882 + 11 ≤
    4003: by the numbers.
  - w_rider_count_head: under the head message 1's count of mask coins is 11: so mask_any's
    premise is met at the eleven: the second road to the same end.
  - w_rider_ce_head: so, under the head, at the eleven ce IS the coin itself (ce_eq,
    Honest/K1/MaskLaw.lean): ce's default "0 beyond the count" is not met.
  - w_rider_no_other_head: under the head: at a row from 2 on, or at a place from 10 on, message
    1's mask holds 0.
  - w_rider_top: ONE THEOREM THAT JOINS THEM, UNDER THE HEAD ALONE: the ride ⟨5, 1⟩ · the room ·
    the two rows · no other place · the rows fix the eleven · at the eleven ce is the coin.

The first two are evaluations in Lean's kernel (decide +kernel; no compiled code).

The road. ride_coin (Honest/K1/RideLaw.lean); lay_w_row0, lay_w_row1, no_other_ride_more
(RideRows.lean); lay_fixes (RideFixes.lean); w_not_one_row_head, ride_w_head (RideAtPlans.lean);
parW_written, fits_w_head (FitsAtW.lean); ce_eq (MaskLaw.lean).
Kin: another house's rows shapesW, startsW, ridesW (Johnson/SendSim/Seat/FastAtWrittenExact.lean)
have W's and the opening's numbers at the written plans, in a list's form, by Lean's kernel: not
called.

Limits. IT SAYS WHAT STANDS WHERE, AND NOTHING ELSE. NINE OF THE ELEVEN STAND IN BOTH ROWS; ONE
PLACE HOLDS A SUM OF TWO; ONE HOLDS 0. On the rows alone: not on codewords, trees' tables or what is
opened. THE FULL SIZE ALONE; the format's second hash function alone. It stands over files of ours that are
on no seal. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RideAtPlans
import Johnson.Desc.ProofFile.Honest.K1.RideRows
import Johnson.Desc.ProofFile.Honest.K1.RideFixes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open Johnson.Prover.Send (Rows shapeAt)

/-- **THE ROOM AT W's SENDING's WRITTEN PLAN.** -/
theorem room_w_written :
    K1.parWF.sent.size = 2 ∧ (shapeAt K1.parWF 1).maskRows = 2 ∧
      (K1.parWF.codes.mask.getD (shapeAt K1.parWF 1).maskCode default).ell = 256 ∧
      maskStart K1.parWF (rideOf (wFold K1.qFull.lin)) 1 = 3882 ∧
      (dueR K1.parWF (rideOf (wFold K1.qFull.lin))).e = 4003 := by
  decide +kernel

/-- The like at the opening's written plan: other numbers. -/
theorem room_first_written :
    K1.parGF.sent.size = 5 ∧ (shapeAt K1.parGF 3).maskRows = 1 ∧
      (K1.parGF.codes.mask.getD (shapeAt K1.parGF 3).maskCode default).ell = 8192 ∧
      maskStart K1.parGF (rideOf (firstFold K1.qFull)) 3 = 8411 ∧
      (dueR K1.parGF (rideOf (firstFold K1.qFull))).e = 8958 := by
  decide +kernel


/-- **THE TWO ROWS, ON rowsR**, where a message rides at ⟨5, 1⟩ and has the room. -/
theorem rider_rows (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k : Nat)
    (hr : ride k = some ⟨5, 1⟩) (hm : (shapeAt P k).maskRows = 2)
    (hl : 10 ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).ell) :
    (List.range 10).map ((rowsR P ride data cs k).mask 0) =
        [ce cs (maskStart P ride k + 2), 0, ce cs (maskStart P ride k + 3),
          ce cs (maskStart P ride k + 4), ce cs (maskStart P ride k + 5),
          ce cs (maskStart P ride k + 6), ce cs (maskStart P ride k + 7),
          ce cs (maskStart P ride k + 9), ce cs (maskStart P ride k + 10),
          ce cs (maskStart P ride k + 8)] ∧
      (List.range 10).map ((rowsR P ride data cs k).mask 1) =
        [ce cs (maskStart P ride k + 2) + ce cs (maskStart P ride k + 0),
          ce cs (maskStart P ride k + 1), ce cs (maskStart P ride k + 3),
          ce cs (maskStart P ride k + 4), ce cs (maskStart P ride k + 5),
          ce cs (maskStart P ride k + 6), ce cs (maskStart P ride k + 7),
          ce cs (maskStart P ride k + 9), ce cs (maskStart P ride k + 10),
          ce cs (maskStart P ride k + 8)] := by
  have e : ∀ b, b < 2 → (List.range 10).map ((rowsR P ride data cs k).mask b) =
      (List.range 10).map ((⟨5, 1⟩ : Ride).lay
        (fun i => if i < (⟨5, 1⟩ : Ride).count then ce cs (maskStart P ride k + i) else 0) b) :=
    fun b hb => List.map_congr_left fun j hj =>
      ride_coin P ride data cs k b j ⟨5, 1⟩ hr (by omega) (by
        have := List.mem_range.1 hj
        omega)
  rw [e 0 (by omega), e 1 (by omega), lay_w_row0, lay_w_row1]
  simp [Ride.count]

/-- **THE ROWS FIX THE ELEVEN**, where a message rides at ⟨5, 1⟩ and has the room. -/
theorem rider_rows_fix (P : K1.Par) (ride : Nat → Option Ride)
    (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs cs' : Cs (dueR P ride)) (k : Nat)
    (hr : ride k = some ⟨5, 1⟩) (hm : (shapeAt P k).maskRows = 2)
    (hl : 10 ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).ell)
    (H : ∀ b, b < 2 → ∀ j, j < 10 →
      (rowsR P ride data cs k).mask b j = (rowsR P ride data' cs' k).mask b j) :
    ∀ i, i < 11 → ce cs (maskStart P ride k + i) = ce cs' (maskStart P ride k + i) := by
  intro i hi
  have g := lay_fixes 1 4
    (fun i => if i < (⟨5, 1⟩ : Ride).count then ce cs (maskStart P ride k + i) else 0)
    (fun i => if i < (⟨5, 1⟩ : Ride).count then ce cs' (maskStart P ride k + i) else 0)
    (fun b hb j hj => by
      rw [← ride_coin P ride data cs k b j ⟨5, 1⟩ hr (by omega) (by omega),
        ← ride_coin P ride data' cs' k b j ⟨5, 1⟩ hr (by omega) (by omega)]
      exact H b hb j hj) i hi
  have hc : i < (⟨5, 1⟩ : Ride).count := by
    show i < 2 * 5 + 1
    omega
  simpa only [if_pos hc] using g

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **THE ROOM AT NUMBER 356's PLAN AND RIDE**, under the head. -/
theorem room_w_head :
    (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size = 2 ∧
      (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 1).maskRows = 2 ∧
      ((K1.parW Zp.first (wGp Zp) 4 wMsgFull).codes.mask.getD
        (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 1).maskCode default).ell = 256 ∧
      maskStart (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)) 1 = 3882 ∧
      (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))).e = 4003 := by
  rw [parW_written h O, ride_w_head h O]
  exact room_w_written

/-- **THE TWO ROWS OF W's RIDER**, under the head. -/
theorem w_rider_rows_head (data : Nat → Nat → Nat → Option (GF ⊕ GE))
    (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)))) :
    (List.range 10).map
        ((rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask 0) =
        [ce cs (3882 + 2), 0, ce cs (3882 + 3), ce cs (3882 + 4), ce cs (3882 + 5),
          ce cs (3882 + 6), ce cs (3882 + 7), ce cs (3882 + 9), ce cs (3882 + 10),
          ce cs (3882 + 8)] ∧
      (List.range 10).map
        ((rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask 1) =
        [ce cs (3882 + 2) + ce cs (3882 + 0), ce cs (3882 + 1), ce cs (3882 + 3),
          ce cs (3882 + 4), ce cs (3882 + 5), ce cs (3882 + 6), ce cs (3882 + 7),
          ce cs (3882 + 9), ce cs (3882 + 10), ce cs (3882 + 8)] := by
  obtain ⟨-, hm, hl, hs, -⟩ := room_w_head h O
  have g := rider_rows _ _ data cs 1 (w_not_one_row_head h O).1 hm (by omega)
  rw [hs] at g
  exact g

/-- **THE ROWS OF W's RIDER FIX ITS ELEVEN**, under the head. -/
theorem w_rider_fix_head (data data' : Nat → Nat → Nat → Option (GF ⊕ GE))
    (cs cs' : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))))
    (H : ∀ b, b < 2 → ∀ j, j < 10 →
      (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask b j =
        (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data' cs' 1).mask b j) :
    ∀ i, i < 11 → ce cs (3882 + i) = ce cs' (3882 + i) := by
  obtain ⟨-, hm, hl, hs, -⟩ := room_w_head h O
  have g := rider_rows_fix _ _ data data' cs cs' 1 (w_not_one_row_head h O).1 hm (by omega) H
  rw [hs] at g
  exact g

/-- **THE ELEVEN NUMBERS LIE INSIDE THE PART's COUNT**, under the head. -/
theorem w_rider_in_head (i : Nat) (hi : i < 11) :
    maskStart (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
        (rideOf (wFold Zp.first.lin)) 1 + i <
      (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))).e := by
  obtain ⟨-, -, -, hs, he⟩ := room_w_head h O
  omega

/-- **MESSAGE 1's COUNT OF MASK COINS IS 11**, under the head: mask_any's premise at the eleven. -/
theorem w_rider_count_head :
    (stepsOf (K1.parW Zp.first (wGp Zp) 4 wMsgFull).codes
      (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 1)
      ((rideOf (wFold Zp.first.lin)) 1)).mask = 11 := by
  rw [(w_not_one_row_head h O).1]
  rfl

/-- **AT THE ELEVEN ce IS THE COIN ITSELF**, under the head. -/
theorem w_rider_ce_head
    (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))))
    (i : Nat) (hi : i < 11) :
    ∃ hlt : 3882 + i <
        (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))).e,
      ce cs (3882 + i) = cs.e ⟨3882 + i, hlt⟩ := by
  obtain ⟨-, -, -, -, he⟩ := room_w_head h O
  exact ⟨by omega, ce_eq _ cs _ _⟩

/-- **NO OTHER PLACE OF W's RIDER's MASK**, under the head. -/
theorem w_rider_no_other_head (data : Nat → Nat → Nat → Option (GF ⊕ GE))
    (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))))
    (b p : Nat) (hh : 2 ≤ b ∨ 10 ≤ p) :
    (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask b p = 0 := by
  obtain ⟨hz, -, -, -, -⟩ := room_w_head h O
  exact no_other_ride_more _ _ data cs 1 b p ⟨5, 1⟩ (fits_w_head h O) (by omega)
    (w_not_one_row_head h O).1 (by
      show 2 ^ 1 ≤ b ∨ 2 * 5 - 1 < p
      omega)

/-- **W's RIDER, ON THE ROWS, IN ONE CONJUNCTION**, under the head alone. -/
theorem w_rider_top :
    (rideOf (wFold Zp.first.lin)) 1 = some ⟨5, 1⟩ ∧
    (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 1).maskRows = 2 ∧
    ((K1.parW Zp.first (wGp Zp) 4 wMsgFull).codes.mask.getD
      (shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 1).maskCode default).ell = 256 ∧
    (∀ (data : Nat → Nat → Nat → Option (GF ⊕ GE))
      (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)))),
      (List.range 10).map
          ((rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask 0) =
          [ce cs (3882 + 2), 0, ce cs (3882 + 3), ce cs (3882 + 4), ce cs (3882 + 5),
            ce cs (3882 + 6), ce cs (3882 + 7), ce cs (3882 + 9), ce cs (3882 + 10),
            ce cs (3882 + 8)] ∧
        (List.range 10).map
          ((rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask 1) =
          [ce cs (3882 + 2) + ce cs (3882 + 0), ce cs (3882 + 1), ce cs (3882 + 3),
            ce cs (3882 + 4), ce cs (3882 + 5), ce cs (3882 + 6), ce cs (3882 + 7),
            ce cs (3882 + 9), ce cs (3882 + 10), ce cs (3882 + 8)]) ∧
    (∀ (data : Nat → Nat → Nat → Option (GF ⊕ GE))
      (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))))
      (b p : Nat), 2 ≤ b ∨ 10 ≤ p →
      (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask b p = 0) ∧
    (∀ (data data' : Nat → Nat → Nat → Option (GF ⊕ GE))
      (cs cs' : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin)))),
      (∀ b, b < 2 → ∀ j, j < 10 →
        (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data cs 1).mask b j =
          (rowsR (K1.parW Zp.first (wGp Zp) 4 wMsgFull)
          (rideOf (wFold Zp.first.lin)) data' cs' 1).mask b j) →
      ∀ i, i < 11 → ce cs (3882 + i) = ce cs' (3882 + i)) ∧
    (∀ (cs : Cs (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))))
      (i : Nat), i < 11 →
      ∃ hlt : 3882 + i <
        (dueR (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (rideOf (wFold Zp.first.lin))).e,
        ce cs (3882 + i) = cs.e ⟨3882 + i, hlt⟩) :=
  ⟨(w_not_one_row_head h O).1, (room_w_head h O).2.1, (room_w_head h O).2.2.1,
    fun data cs => w_rider_rows_head h O data cs,
    fun data cs b p hh => w_rider_no_other_head h O data cs b p hh,
    fun data data' cs cs' H => w_rider_fix_head h O data data' cs cs' H,
    fun cs i hi => w_rider_ce_head h O cs i hi⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.room_w_written
#print axioms ProofFile.Honest.K1.room_first_written
#print axioms ProofFile.Honest.K1.rider_rows
#print axioms ProofFile.Honest.K1.rider_rows_fix
#print axioms ProofFile.Honest.K1.room_w_head
#print axioms ProofFile.Honest.K1.w_rider_rows_head
#print axioms ProofFile.Honest.K1.w_rider_fix_head
#print axioms ProofFile.Honest.K1.w_rider_in_head
#print axioms ProofFile.Honest.K1.w_rider_count_head
#print axioms ProofFile.Honest.K1.w_rider_ce_head
#print axioms ProofFile.Honest.K1.w_rider_no_other_head
#print axioms ProofFile.Honest.K1.w_rider_top
