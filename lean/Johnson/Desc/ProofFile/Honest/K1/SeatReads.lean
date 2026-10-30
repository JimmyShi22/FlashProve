-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/SeatReads.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: AT EVERY PLACE INSIDE THE SIZES rowsR HOLDS THE COIN WITH THE NUMBER Seat.no. Two
definitions, two statements and their proofs.

  coinNo        a coin of the part by field and number, in the extension field
  Seat.read     what a message's rows hold at a place (Honest/K1/Seat.lean), in the extension field
  pad_pos       a pad in a main row: the message has no mask row and is sampled
  seat_reads    under sendFits (Honest/K1/Coins.lean), at a message whose table does not ride: at
                every place inside the sizes the rows that rowsR lays hold the coin of the place's
                field with the number Seat.no: so seat_inj (Seat.lean) speaks of rowsR

By cases on the place, each a call: tail_coin_e and _f, word_coin_e and _f, pad_coin_e and _f,
maskTail_coin (CoinLaw.lean), mask_slot (MaskLaw.lean), pad_le_of_fits and fits_main (PadLaw.lean).

sendFits is spent at a pad's place alone.

Limits. At a riding table the mask coins are laid otherwise (ride_coin, RideLaw.lean): not here.
What is WRITTEN where: no sentence on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seat
import Johnson.Desc.ProofFile.Honest.K1.PadLaw
import Johnson.Prover.Send.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- A coin of the part by field and number, in the extension field. -/
def coinNo {d : Due} (cs : Cs d) (e : Bool) (n : Nat) : GE :=
  if e then ce cs n else algebraMap GF GE (cf cs n)

/-- What a message's rows hold at a place, in the extension field. A pad's entry number i: in the
last main row at the place ell - pad + i. A mask coin number i: the entry with the format's
number i. -/
def Seat.read (V : Rows) (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → GE
  | .tail r q => V.mainTl (s.mainDeg == 3) r q
  | .word r j => V.main (s.mainDeg == 3) r j
  | .pad i => V.main (s.mainDeg == 3) (s.mainRows - 1)
      ((codes.base.getD s.code default).ell - (stepsOf codes s R).pad + i)
  | .mask i => V.mask (i % s.maskRows) (i / s.maskRows)
  | .maskTail r q => V.maskTl r q

/-- A pad in a main row: the message has no mask row and is sampled. -/
theorem pad_pos (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (h : (stepsOf P.codes (shapeAt P k) (ride k)).pad ≠ 0) :
    (shapeAt P k).maskRows = 0 ∧ (shapeAt P k).answers ≠ 0 := by
  by_cases hc : ((shapeAt P k).maskRows == 0 && (shapeAt P k).answers != 0) = true
  · simpa only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] using hc
  · exact absurd (by simp only [stepsOf, hc, Bool.false_eq_true, if_false]) h

/-- **rowsR holds the coin with the number Seat.no.** -/
theorem seat_reads (P : K1.Par) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (cs : Cs (dueR P ride)) (k : Nat) (x : Seat)
    (hf : sendFits P ride = true) (hk : k < P.sent.size) (hr : ride k = none)
    (hx : x.ok P.codes (shapeAt P k) (ride k)) :
    x.read (rowsR P ride data cs k) P.codes (shapeAt P k) (ride k) =
      coinNo cs (x.inE (shapeAt P k)) (x.no P ride k) := by
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · cases x with
    | tail r q =>
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.mainTl, h3, if_true]
      rw [tail_coin_e P ride data cs k r q h3 hx.1 hx.2, Nat.add_assoc]
    | word r j =>
      have ha : (shapeAt P k).answers = 0 := by
        by_contra hne
        have : ((shapeAt P k).answers == 0) = false := beq_eq_false_iff_ne.2 hne
        exact hx.1 (by simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false])
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.main, h3, if_true]
      exact word_coin_e P ride data cs k r j h3 ha hx.2.1 hx.2.2
    | pad i =>
      have hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).pad := hx
      obtain ⟨hz, ha⟩ := pad_pos P ride k (by omega)
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.main, h3, if_true]
      exact pad_coin_e P ride data cs k i h3 ha (fits_main P ride k hf hk hz)
        (pad_le_of_fits P ride k hf hk) hi
    | mask i =>
      have hi : i < (shapeAt P k).maskRows *
          (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
        have : i < (stepsOf P.codes (shapeAt P k) (ride k)).mask := hx
        simpa only [stepsOf, hr, Option.map_none, Option.getD_none] using this
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, h3, if_true]
      rw [mask_slot P ride data cs k i hr hi, maskStart, h3, if_pos rfl, Nat.add_assoc]
    | maskTail r q =>
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, h3, if_true]
      rw [maskTail_coin P ride data cs k r q hx.1 hx.2, maskStart, h3, if_pos rfl]
      congr 1
      omega
  · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
    cases x with
    | tail r q =>
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.mainTl, h3',
        Bool.false_eq_true, if_false]
      rw [tail_coin_f P ride data cs k r q h3' hx.1 hx.2, Nat.add_assoc]
    | word r j =>
      have ha : (shapeAt P k).answers = 0 := by
        by_contra hne
        have : ((shapeAt P k).answers == 0) = false := beq_eq_false_iff_ne.2 hne
        exact hx.1 (by simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false])
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.main, h3',
        Bool.false_eq_true, if_false]
      rw [word_coin_f P ride data cs k r j h3' ha hx.2.1 hx.2.2]
    | pad i =>
      have hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).pad := hx
      obtain ⟨hz, ha⟩ := pad_pos P ride k (by omega)
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, Rows.main, h3',
        Bool.false_eq_true, if_false]
      rw [pad_coin_f P ride data cs k i h3' ha (fits_main P ride k hf hk hz)
        (pad_le_of_fits P ride k hf hk) hi]
    | mask i =>
      have hi : i < (shapeAt P k).maskRows *
          (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
        have : i < (stepsOf P.codes (shapeAt P k) (ride k)).mask := hx
        simpa only [stepsOf, hr, Option.map_none, Option.getD_none] using this
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, h3', Bool.false_eq_true,
        if_false, if_true, Nat.zero_add]
      rw [mask_slot P ride data cs k i hr hi, maskStart, h3']
      rfl
    | maskTail r q =>
      simp only [Seat.read, Seat.no, Seat.inE, Seat.off, coinNo, h3', Bool.false_eq_true,
        if_false, if_true, Nat.zero_add]
      rw [maskTail_coin P ride data cs k r q hx.1 hx.2, maskStart, h3']
      congr 1
      simp only [Bool.false_eq_true, if_false]
      omega

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.pad_pos
#print axioms ProofFile.Honest.K1.seat_reads
#print axioms ProofFile.Honest.K1.coinNo
#print axioms ProofFile.Honest.K1.Seat.read
