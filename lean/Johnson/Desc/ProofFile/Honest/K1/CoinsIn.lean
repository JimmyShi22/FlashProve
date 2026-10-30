-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/CoinsIn.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: NO READ THAT rowsR (Honest/K1/Coins.lean) MAKES IN RANGE GOES BEYOND THE PART's
COUNT: so cf and ce, which let 0 stand in beyond the count, hand out a coin at each such read.
Statements and proofs.

  lt_mul        r < m and q < c give r * c + q < m * c
  startR_mono_f, msg_in_e, msg_in_f   a message's coins lie inside the part's count, by field
  main_coin_e, main_coin_f   a number below the message's main coins (tails, a word's message, a pad
                in a main row), in the field of the main rows
  tail_lt_main, main_tail_e, main_tail_f   a main row's tail
  mask_any      a number below the message's count of mask coins, whether its table rides or not
  mask_tail     a mask row's tail

The numbers on the left-hand sides are rowsR's own: a.e + r * C.r + q, a.e + i, m0 + i,
m0 + n.mask + r * Z.r + q, with m0 = maskStart (Honest/K1/MaskLaw.lean).

Limits. That rowsR reads at no other number is read off its text, not stated here. That a word's
entry's and a pad's place's number lies below the main coins is a premise here (main_coin_e,
main_coin_f): Seat.rng and seat_in (Honest/K1/Seat.lean) pay it. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

theorem lt_mul (r q m c : Nat) (hr : r < m) (hq : q < c) : r * c + q < m * c :=
  calc r * c + q < r * c + c := Nat.add_lt_add_left hq _
    _ = (r + 1) * c := (Nat.succ_mul r c).symm
    _ ≤ m * c := Nat.mul_le_mul_right c hr

theorem startR_mono_f (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) :
    ∀ n, k ≤ n → (startR P ride k).f ≤ (startR P ride n).f := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih =>
    rw [startR_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- A message's coins lie inside the part's count. -/
theorem msg_in_e (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (hk : k < P.sent.size) :
    (startR P ride k).e + (dueMsg P.codes (shapeAt P k) (ride k)).e ≤ (dueR P ride).e := by
  have h1 := startR_mono P ride (k + 1) P.sent.size hk
  rw [startR_succ] at h1
  exact h1

theorem msg_in_f (P : K1.Par) (ride : Nat → Option Ride) (k : Nat) (hk : k < P.sent.size) :
    (startR P ride k).f + (dueMsg P.codes (shapeAt P k) (ride k)).f ≤ (dueR P ride).f := by
  have h1 := startR_mono_f P ride (k + 1) P.sent.size hk
  rw [startR_succ] at h1
  exact h1

/-- A number below the message's main coins, over the extension field. -/
theorem main_coin_e (P : K1.Par) (ride : Nat → Option Ride) (k i : Nat) (hk : k < P.sent.size)
    (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).main) :
    (startR P ride k).e + i < (dueR P ride).e := by
  have h := msg_in_e P ride k hk
  simp only [dueMsg, h3, if_true] at h
  omega

/-- Over the base field. -/
theorem main_coin_f (P : K1.Par) (ride : Nat → Option Ride) (k i : Nat) (hk : k < P.sent.size)
    (h3 : ((shapeAt P k).mainDeg == 3) = false)
    (hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).main) :
    (startR P ride k).f + i < (dueR P ride).f := by
  have h := msg_in_f P ride k hk
  simp only [dueMsg, h3, Bool.false_eq_true, if_false] at h
  omega

/-- A main row's tail lies among the message's main coins. -/
theorem tail_lt_main (P : K1.Par) (ride : Nat → Option Ride) (k r q : Nat)
    (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    r * (P.codes.base.getD (shapeAt P k).code default).r + q <
      (stepsOf P.codes (shapeAt P k) (ride k)).main := by
  have h := lt_mul r q _ _ hr hq
  have e : (stepsOf P.codes (shapeAt P k) (ride k)).tails =
      (shapeAt P k).mainRows * (P.codes.base.getD (shapeAt P k).code default).r := rfl
  unfold Steps.main
  omega

theorem main_tail_e (P : K1.Par) (ride : Nat → Option Ride) (k r q : Nat) (hk : k < P.sent.size)
    (h3 : ((shapeAt P k).mainDeg == 3) = true) (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    (startR P ride k).e + r * (P.codes.base.getD (shapeAt P k).code default).r + q <
      (dueR P ride).e := by
  rw [Nat.add_assoc]
  exact main_coin_e P ride k _ hk h3 (tail_lt_main P ride k r q hr hq)

theorem main_tail_f (P : K1.Par) (ride : Nat → Option Ride) (k r q : Nat) (hk : k < P.sent.size)
    (h3 : ((shapeAt P k).mainDeg == 3) = false) (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    (startR P ride k).f + r * (P.codes.base.getD (shapeAt P k).code default).r + q <
      (dueR P ride).f := by
  rw [Nat.add_assoc]
  exact main_coin_f P ride k _ hk h3 (tail_lt_main P ride k r q hr hq)

/-- A number below the message's count of mask coins, whether its table rides or not. -/
theorem mask_any (P : K1.Par) (ride : Nat → Option Ride) (k i : Nat) (hk : k < P.sent.size)
    (hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).mask) :
    maskStart P ride k + i < (dueR P ride).e := by
  have h := msg_in_e P ride k hk
  unfold maskStart
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · simp only [dueMsg, h3, if_true] at h ⊢
    omega
  · simp only [dueMsg, h3, Bool.false_eq_true, if_false] at h ⊢
    omega

/-- A mask row's tail. -/
theorem mask_tail (P : K1.Par) (ride : Nat → Option Ride) (k r q : Nat) (hk : k < P.sent.size)
    (hr : r < (shapeAt P k).maskRows)
    (hq : q < (P.codes.mask.getD (shapeAt P k).maskCode default).r) :
    maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask +
      r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q < (dueR P ride).e := by
  have h := msg_in_e P ride k hk
  have h2 := lt_mul r q _ _ hr hq
  have e : (stepsOf P.codes (shapeAt P k) (ride k)).maskTails =
      (shapeAt P k).maskRows * (P.codes.mask.getD (shapeAt P k).maskCode default).r := rfl
  unfold maskStart
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · simp only [dueMsg, h3, if_true] at h ⊢
    omega
  · simp only [dueMsg, h3, Bool.false_eq_true, if_false] at h ⊢
    omega

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lt_mul
#print axioms ProofFile.Honest.K1.startR_mono_f
#print axioms ProofFile.Honest.K1.msg_in_e
#print axioms ProofFile.Honest.K1.msg_in_f
#print axioms ProofFile.Honest.K1.main_coin_e
#print axioms ProofFile.Honest.K1.main_coin_f
#print axioms ProofFile.Honest.K1.tail_lt_main
#print axioms ProofFile.Honest.K1.main_tail_e
#print axioms ProofFile.Honest.K1.main_tail_f
#print axioms ProofFile.Honest.K1.mask_any
#print axioms ProofFile.Honest.K1.mask_tail
