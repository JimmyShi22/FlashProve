-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/NoOther.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: NO OTHER PLACE HOLDS A COIN. Three definitions, statements and proofs.

  Rd, rdAt      the four tables of a message's rows; what they hold at (row, place), the main ones
                read in the rows' own field, in the extension field
  Seat.place    where a place (Honest/K1/Seat.lean) lies: the table, the row, the place in the row
  read_place    Seat.read (Honest/K1/SeatReads.lean) is rdAt at Seat.place
  no_main       inside the sizes, where no place of step (2) or (3) lies at (r, j), neither of the
                two tests by which rowsR tells a main entry's coin holds
  place_inj     two places inside the sizes lie at two (table, row, place)
  no_other      at a table, row and place that is Seat.place of no place inside the sizes, what
                rowsR (Honest/K1/Coins.lean) lays is THE SAME AT EVERY TWO VALUES OF THE PART's
                COINS: in the mask table: for a message whose table does not ride; in the three
                other tables: for every message
  other_field   the main tables of the field that is not the rows' own hold 0
  no_other_ride at a riding table of one row, under sendFits: off the places (0, p), p ≤ 2 k, the
                mask table holds 0

No test on the job is asked in no_other: it holds also where a pad is longer than its row.

Limits. At a riding table of more than one row nothing is said. What is WRITTEN where: no sentence
on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.SeatReads
import Johnson.Desc.ProofFile.Honest.K1.RideOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- The four tables of a message's rows, the main ones read in the rows' own field. -/
inductive Rd where
  | main
  | mainTl
  | mask
  | maskTl
  deriving DecidableEq

/-- What a message's rows hold in a table at (row, place), in the extension field. -/
def rdAt (V : Rows) (overE : Bool) : Rd → Nat → Nat → GE
  | .main => V.main overE
  | .mainTl => V.mainTl overE
  | .mask => V.mask
  | .maskTl => V.maskTl

/-- Where a place (Honest/K1/Seat.lean) lies: the table, the row, the place in the row. A mask coin
number i: at the entry with the format's number i: for a message whose table does not ride. -/
def Seat.place (codes : Codes) (s : OracleShape) (R : Option Ride) : Seat → Rd × Nat × Nat
  | .tail r q => (.mainTl, r, q)
  | .word r j => (.main, r, j)
  | .pad i => (.main, s.mainRows - 1,
      (codes.base.getD s.code default).ell - (stepsOf codes s R).pad + i)
  | .mask i => (.mask, i % s.maskRows, i / s.maskRows)
  | .maskTail r q => (.maskTl, r, q)

theorem read_place (V : Rows) (codes : Codes) (s : OracleShape) (R : Option Ride) (x : Seat) :
    x.read V codes s R =
      rdAt V (s.mainDeg == 3) (x.place codes s R).1 (x.place codes s R).2.1
        (x.place codes s R).2.2 := by
  cases x <;> rfl

/-- **Two places inside the sizes lie at two (table, row, place).** -/
theorem place_inj (codes : Codes) (s : OracleShape) (R : Option Ride) (x x' : Seat)
    (hx : x.ok codes s R) (hx' : x'.ok codes s R)
    (h : x.place codes s R = x'.place codes s R) : x = x' := by
  have hwp := word_pad codes s R
  cases x with
  | tail r q =>
    cases x' with
    | tail r' q' =>
      simp only [Seat.place, Prod.mk.injEq, true_and] at h
      rw [h.1, h.2]
    | _ => simp [Seat.place] at h
  | word r j =>
    cases x' with
    | word r' j' =>
      simp only [Seat.place, Prod.mk.injEq, true_and] at h
      rw [h.1, h.2]
    | pad i' =>
      have a : (stepsOf codes s R).word ≠ 0 := hx.1
      have b : i' < (stepsOf codes s R).pad := hx'
      omega
    | _ => simp [Seat.place] at h
  | pad i =>
    cases x' with
    | pad i' =>
      simp only [Seat.place, Prod.mk.injEq, true_and] at h
      obtain rfl : i = i' := by omega
      rfl
    | word r' j' =>
      have a : (stepsOf codes s R).word ≠ 0 := hx'.1
      have b : i < (stepsOf codes s R).pad := hx
      omega
    | _ => simp [Seat.place] at h
  | mask i =>
    cases x' with
    | mask i' =>
      simp only [Seat.place, Prod.mk.injEq, true_and] at h
      have a := Nat.div_add_mod i s.maskRows
      have b := Nat.div_add_mod i' s.maskRows
      rw [h.1, h.2] at a
      rw [← a, b]
    | _ => simp [Seat.place] at h
  | maskTail r q =>
    cases x' with
    | maskTail r' q' =>
      simp only [Seat.place, Prod.mk.injEq, true_and] at h
      rw [h.1, h.2]
    | _ => simp [Seat.place] at h

variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))

/-- The main tables of the field that is not the rows' own hold 0. -/
theorem other_field (cs : Cs (dueR P ride)) (k r j : Nat) :
    (((shapeAt P k).mainDeg == 3) = true →
      (rowsR P ride data cs k).mainF r j = 0 ∧ (rowsR P ride data cs k).mainTlF r j = 0) ∧
    (((shapeAt P k).mainDeg == 3) = false →
      (rowsR P ride data cs k).mainE r j = 0 ∧ (rowsR P ride data cs k).mainTlE r j = 0) := by
  constructor
  · intro h3
    constructor <;> simp only [rowsR, h3, Bool.true_or, Bool.not_true, Bool.false_and, if_true,
      Bool.false_eq_true, if_false]
  · intro h3
    constructor <;> simp only [rowsR, h3, Bool.not_false, Bool.true_or, Bool.false_and, if_true,
      Bool.false_eq_true, if_false]

/-- The number of the coin at a main entry, or none: rowsR's own two tests, as one statement: inside
the sizes, where no place of step (2) or (3) lies at (r, j), neither test holds. -/
theorem no_main (k r j : Nat)
    (h : ∀ x : Seat, x.ok P.codes (shapeAt P k) (ride k) →
      x.place P.codes (shapeAt P k) (ride k) ≠ (.main, r, j))
    (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = false ∧
    ((stepsOf P.codes (shapeAt P k) (ride k)).pad != 0 && r + 1 == (shapeAt P k).mainRows &&
      decide ((P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤ j) &&
      decide (j < (P.codes.base.getD (shapeAt P k).code default).ell)) = false := by
  constructor
  · by_contra hc
    have hw : (stepsOf P.codes (shapeAt P k) (ride k)).word ≠ 0 := by
      simpa only [bne_iff_ne] using eq_true_of_ne_false hc
    exact h (.word r j) ⟨hw, hr, hj⟩ rfl
  · by_contra hc
    have hc' := eq_true_of_ne_false hc
    simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq] at hc'
    obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := hc'
    refine h (.pad (j - ((P.codes.base.getD (shapeAt P k).code default).ell -
      (stepsOf P.codes (shapeAt P k) (ride k)).pad))) ?_ ?_
    · show j - _ < (stepsOf P.codes (shapeAt P k) (ride k)).pad
      omega
    · show ((Rd.main, (shapeAt P k).mainRows - 1, _ + (j - _)) : Rd × Nat × Nat) = _
      congr 2 <;> omega

/-- **NO OTHER PLACE HOLDS A COIN.** -/
theorem no_other (cs cs' : Cs (dueR P ride)) (k : Nat) (t : Rd) (r j : Nat)
    (hr : t = .mask → ride k = none)
    (h : ∀ x : Seat, x.ok P.codes (shapeAt P k) (ride k) →
      x.place P.codes (shapeAt P k) (ride k) ≠ (t, r, j)) :
    rdAt (rowsR P ride data cs k) ((shapeAt P k).mainDeg == 3) t r j =
      rdAt (rowsR P ride data cs' k) ((shapeAt P k).mainDeg == 3) t r j := by
  cases t with
  | main =>
    by_cases hin : r < (shapeAt P k).mainRows ∧
        j < (P.codes.base.getD (shapeAt P k).code default).ell
    · obtain ⟨a, b⟩ := no_main P ride k r j h hin.1 hin.2
      by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
      · simp only [rdAt, Rows.main, rowsR, h3, a, b, if_true, Bool.false_eq_true, if_false,
          Option.map_none]
      · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
        simp only [rdAt, Rows.main, rowsR, h3', a, b, Bool.false_eq_true, if_false,
          Option.map_none]
    · have hout : (decide ((shapeAt P k).mainRows ≤ r) ||
          decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j)) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        by_contra hc
        exact hin ⟨by omega, by omega⟩
      by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
      · simp only [rdAt, Rows.main, rowsR, h3, Bool.not_true, Bool.false_or, hout, if_true]
      · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
        simp only [rdAt, Rows.main, rowsR, h3', Bool.false_or, hout, if_true, Bool.false_eq_true,
          if_false]
  | mainTl =>
    have hout : (decide (r < (shapeAt P k).mainRows) &&
        decide (j < (P.codes.base.getD (shapeAt P k).code default).r)) = false := by
      by_contra hc
      have hc' := eq_true_of_ne_false hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
      exact h (.tail r j) hc' rfl
    by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
    · simp only [rdAt, Rows.mainTl, rowsR, h3, Bool.true_and, hout, if_true, Bool.false_eq_true,
        if_false]
    · have h3' : ((shapeAt P k).mainDeg == 3) = false := by simpa using h3
      simp only [rdAt, Rows.mainTl, rowsR, h3', Bool.not_false, Bool.true_and, hout,
        Bool.false_eq_true, if_false]
  | mask =>
    have hr := hr rfl
    have hout : ¬ (r < (shapeAt P k).maskRows ∧
        j < (P.codes.mask.getD (shapeAt P k).maskCode default).ell) := by
      intro hc
      refine h (.mask (j * (shapeAt P k).maskRows + r)) ?_ ?_
      · show _ < (stepsOf P.codes (shapeAt P k) (ride k)).mask
        simp only [stepsOf, hr, Option.map_none, Option.getD_none]
        rw [Nat.mul_comm (shapeAt P k).maskRows]
        exact lt_mul j r _ _ hc.2 hc.1
      · show ((Rd.mask, _ % _, _ / _) : Rd × Nat × Nat) = _
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc.1,
          Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc.1, Nat.zero_add]
    simp only [rdAt, rowsR, hr]
    rw [if_neg hout, if_neg hout]
  | maskTl =>
    have hout : ¬ (r < (shapeAt P k).maskRows ∧
        j < (P.codes.mask.getD (shapeAt P k).maskCode default).r) :=
      fun hc => h (.maskTail r j) hc rfl
    simp only [rdAt, rowsR]
    rw [if_neg hout, if_neg hout]

/-- At a riding table of one row. -/
theorem no_other_ride (cs : Cs (dueR P ride)) (k r p : Nat) (R : Ride)
    (hf : sendFits P ride = true) (hk : k < P.sent.size) (hr : ride k = some R) (h0 : R.h = 0)
    (h : r ≠ 0 ∨ 2 * R.k < p) : (rowsR P ride data cs k).mask r p = 0 := by
  obtain ⟨hm, -, -⟩ := ride_sizes _ _ R (fits_ride P ride k R hf hk hr) h0
  by_cases hr0 : r = 0
  · subst hr0
    exact ride_one_beyond P ride data cs k p R hf hk hr h0 (by omega)
  · simp only [rowsR, hr]
    rw [if_neg (fun hc => by omega)]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.read_place
#print axioms ProofFile.Honest.K1.place_inj
#print axioms ProofFile.Honest.K1.other_field
#print axioms ProofFile.Honest.K1.no_main
#print axioms ProofFile.Honest.K1.no_other
#print axioms ProofFile.Honest.K1.no_other_ride
#print axioms ProofFile.Honest.K1.Rd
#print axioms ProofFile.Honest.K1.rdAt
#print axioms ProofFile.Honest.K1.Seat.place
