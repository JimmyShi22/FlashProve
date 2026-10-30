-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/RideOne.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: A RIDING TABLE OF ONE ROW, UNDER THE PUBLIC TEST sendFits (Honest/K1/Coins.lean),
ON rowsR AND ON THE HELD WORD. Statements and proofs.

  fits_ride     sendFits hands rideFits at a message whose table rides
  ride_sizes    what rideFits says at one row: one mask row; 1 ≤ k; 2 k + 1 ≤ the mask code's ell
  ride_one      ride k = some R, R.h = 0, p ≤ 2 R.k: the place p of the one mask row that rowsR lays
                holds the part's coin number maskStart + sig R.k p (sig: Honest/K1/RideLaw.lean)
  ride_one_beyond   every later place holds 0
  held_ride_one the same on the held word: in the mask table of message number first + k at the
                index p (one row: the index is the place)

rideFits is spent thrice: one mask row; 1 ≤ k; the 2 k + 1 places lie inside the mask code's message
length.

Limits. AT MORE THAN ONE ROW (h > 0), which rideFits allows, THERE IS NO LAW HERE. What is WRITTEN
where: no sentence on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.RideLaw
import Johnson.Desc.ProofFile.Honest.K1.PadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- sendFits hands rideFits at a message whose table rides. -/
theorem fits_ride (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (R : Ride)
    (hf : sendFits P ride = true) (hk : k < P.sent.size) (hr : ride k = some R) :
    rideFits P.codes (shapeAt P k) R = true := by
  simp only [sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hf
  have h := (hf.2 k hk).2
  rw [hr] at h
  exact h

/-- What rideFits says at one row. -/
theorem ride_sizes (codes : Codes) (s : OracleShape) (R : Ride) (h : rideFits codes s R = true)
    (h0 : R.h = 0) :
    s.maskRows = 1 ∧ 1 ≤ R.k ∧ 2 * R.k + 1 ≤ (codes.mask.getD s.maskCode default).ell := by
  simp only [rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, h0, Nat.pow_zero,
    Nat.sub_zero] at h
  exact ⟨h.1.1.1.2, h.1.2, h.2⟩

variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
  (cs : Cs (dueR P ride)) (k : Nat)

/-- **On rowsR.** -/
theorem ride_one (p : Nat) (R : Ride) (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (hr : ride k = some R) (h0 : R.h = 0) (hp : p ≤ 2 * R.k) :
    (rowsR P ride data cs k).mask 0 p = ce cs (maskStart P ride k + sig R.k p) := by
  obtain ⟨hm, h1, hl⟩ := ride_sizes _ _ R (fits_ride P ride k R hf hk hr) h0
  rw [ride_coin P ride data cs k 0 p R hr (by omega) (by omega)]
  obtain ⟨kk, hh⟩ := R
  obtain rfl : hh = 0 := h0
  rw [lay_one kk p _ h1 hp, if_pos (by
    have := sig_lt kk p h1 hp
    show sig kk p < 2 * kk + 1
    omega)]

/-- Every later place holds 0. -/
theorem ride_one_beyond (p : Nat) (R : Ride) (hf : sendFits P ride = true)
    (hk : k < P.sent.size) (hr : ride k = some R) (h0 : R.h = 0) (hp : 2 * R.k < p) :
    (rowsR P ride data cs k).mask 0 p = 0 := by
  obtain ⟨hm, h1, hl⟩ := ride_sizes _ _ R (fits_ride P ride k R hf hk hr) h0
  by_cases hj : p < (P.codes.mask.getD (shapeAt P k).maskCode default).ell
  · rw [ride_coin P ride data cs k 0 p R hr (by omega) hj]
    obtain ⟨kk, hh⟩ := R
    obtain rfl : hh = 0 := h0
    exact lay_one_beyond kk p _ h1 hp
  · simp only [rowsR, hr]
    rw [if_neg (fun h => hj h.2)]

/-- **On the held word.** -/
theorem held_ride_one (w : Words GE) (first p : Nat) (R : Ride) (hf : sendFits P ride = true)
    (hk : k < P.sent.size) (hr : ride k = some R) (h0 : R.h = 0) (hp : p ≤ 2 * R.k) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .mask p =
      ce cs (maskStart P ride k + sig R.k p) := by
  obtain ⟨hm, -, -⟩ := ride_sizes _ _ R (fits_ride P ride k R hf hk hr) h0
  rw [Johnson.Prover.Send.held_new w first P _ k hk]
  have e : p = 0 + p * 2 ^ K1.clog (shapeAt P k).maskRows := by
    rw [hm]
    show p = 0 + p * 2 ^ 0
    omega
  have hw := Johnson.Prover.Send.word_mask (rowsR P ride data cs k) (shapeAt P k) 0 p (by omega)
  rw [← e] at hw
  rw [hw]
  exact ride_one P ride data cs k p R hf hk hr h0 hp

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.fits_ride
#print axioms ProofFile.Honest.K1.ride_sizes
#print axioms ProofFile.Honest.K1.ride_one
#print axioms ProofFile.Honest.K1.ride_one_beyond
#print axioms ProofFile.Honest.K1.held_ride_one
