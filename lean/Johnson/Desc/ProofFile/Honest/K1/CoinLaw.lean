-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/CoinLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: WHICH COIN STANDS WHERE, for the steps (1), (2), (3) and (5) of the order in the
head of Honest/K1/Coins.lean (step (4): Honest/K1/MaskLaw.lean); and THE PAD THAT THE VERIFIER's
SAMPLE ROW READS IS THE PAD THAT rowsR LAYS, under the codes' lengths' test: in two halves here; as
one statement, on the held word, under sendFits: pad_held_e, pad_held_f, pad_held_mask
(Honest/K1/PadLaw.lean). Statements and proofs.

  tail_coin_e, tail_coin_f   step (1): a main row's tail
  word_coin_e, word_coin_f   step (2): the message of a word with main rows and no answer
  pad_coin_e, pad_coin_f   step (3), AT rowsR's OWN PLACE: coin number i of a pad in a main row
                stands in the last main row at the place ell - pad + i
  maskTail_coin step (5): a mask row's tail
  two_logEll_base, two_logEll_mask   under the test a code's message length is 2 ^ logEll
  pad_main_at, pad_mask_at   UNDER Own.lengthsFit (Johnson/Desc/Own/Lin.lean): the index of each
                entry of K1.Msg.pad (Johnson/Desc/K1/Own.lean), which counts by 2 ^ logEll, written
                by the length ell, by which rowsR counts

pad_coin_e and pad_coin_f do not ask "no mask row": a number below the pad's count says it. They do
ask that the pad be no longer than its row (pad ≤ ell): under sendFits pad_le_of_fits
(Honest/K1/PadLaw.lean) pays it.

Limits. What is WRITTEN where: no sentence on what a coin is for. pad_coin_e and pad_coin_f speak of
rowsR's own place and hold without the lengths' test; THAT THIS PLACE IS THE ONE THAT THE VERIFIER's
ROW READS WANTS THE TEST: pad_main_at. The riding arm of step (4) (Ride.lay of the coins) has no law
here: ride_coin, and at one row lay_one (Honest/K1/RideLaw.lean) and ride_one
(Honest/K1/RideOne.lean); at more than one row the laying itself is held by evaluation alone
(Honest/K1/ToyCount.lean, ToyPlay.lean). Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.CoinsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
  (cs : Cs (dueR P ride)) (k : Nat)

/-- Step (1), over the extension field. -/
theorem tail_coin_e (r q : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    (rowsR P ride data cs k).mainTlE r q =
      ce cs ((startR P ride k).e + r * (P.codes.base.getD (shapeAt P k).code default).r + q) := by
  simp only [rowsR, h3, hr, hq, decide_true, Bool.and_self, if_true]

/-- Over the base field. -/
theorem tail_coin_f (r q : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = false)
    (hr : r < (shapeAt P k).mainRows)
    (hq : q < (P.codes.base.getD (shapeAt P k).code default).r) :
    (rowsR P ride data cs k).mainTlF r q =
      cf cs ((startR P ride k).f + r * (P.codes.base.getD (shapeAt P k).code default).r + q) := by
  simp only [rowsR, h3, hr, hq, decide_true, Bool.not_false, Bool.and_self, if_true]

/-- Step (2), over the extension field. -/
theorem word_coin_e (r j : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (ha : (shapeAt P k).answers = 0) (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    (rowsR P ride data cs k).mainE r j =
      ce cs ((startR P ride k).e + ((stepsOf P.codes (shapeAt P k) (ride k)).tails +
        r * (P.codes.base.getD (shapeAt P k).code default).ell + j)) := by
  have hm : ((shapeAt P k).mainRows != 0) = true := by
    rw [bne_iff_ne]
    omega
  have hw : (stepsOf P.codes (shapeAt P k) (ride k)).word =
      (shapeAt P k).mainRows * (P.codes.base.getD (shapeAt P k).code default).ell := by
    simp only [stepsOf, hm, ha, beq_self_eq_true, Bool.and_self, if_true]
  have hw0 : ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = true := by
    rw [hw, bne_iff_ne]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have n1 : decide ((shapeAt P k).mainRows ≤ r) = false := decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false :=
    decide_eq_false (by omega)
  simp only [rowsR, h3, n1, n2, hw0, hj, Bool.not_true, Bool.or_self, Bool.false_eq_true,
    if_false, if_true]

/-- Over the base field. -/
theorem word_coin_f (r j : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = false)
    (ha : (shapeAt P k).answers = 0) (hr : r < (shapeAt P k).mainRows)
    (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell) :
    (rowsR P ride data cs k).mainF r j =
      cf cs ((startR P ride k).f + ((stepsOf P.codes (shapeAt P k) (ride k)).tails +
        r * (P.codes.base.getD (shapeAt P k).code default).ell + j)) := by
  have hm : ((shapeAt P k).mainRows != 0) = true := by
    rw [bne_iff_ne]
    omega
  have hw : (stepsOf P.codes (shapeAt P k) (ride k)).word =
      (shapeAt P k).mainRows * (P.codes.base.getD (shapeAt P k).code default).ell := by
    simp only [stepsOf, hm, ha, beq_self_eq_true, Bool.and_self, if_true]
  have hw0 : ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = true := by
    rw [hw, bne_iff_ne]
    exact Nat.ne_of_gt (Nat.mul_pos (by omega) (by omega))
  have n1 : decide ((shapeAt P k).mainRows ≤ r) = false := decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false :=
    decide_eq_false (by omega)
  simp only [rowsR, h3, n1, n2, hw0, hj, Bool.or_self, Bool.false_eq_true, if_false, if_true]

/-- Step (3), at rowsR's own place, over the extension field. -/
theorem pad_coin_e (i : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (ha : (shapeAt P k).answers ≠ 0) (hm : 0 < (shapeAt P k).mainRows)
    (hp : (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤
      (P.codes.base.getD (shapeAt P k).code default).ell)
    (hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).pad) :
    (rowsR P ride data cs k).mainE ((shapeAt P k).mainRows - 1)
        ((P.codes.base.getD (shapeAt P k).code default).ell -
          (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) =
      ce cs ((startR P ride k).e + ((stepsOf P.codes (shapeAt P k) (ride k)).tails + i)) := by
  have hw0 : ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = false := by
    have : ((shapeAt P k).answers == 0) = false := beq_eq_false_iff_ne.2 ha
    simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false, bne_self_eq_false]
  have hp0 : ((stepsOf P.codes (shapeAt P k) (ride k)).pad != 0) = true := by
    rw [bne_iff_ne]
    omega
  have n1 : decide ((shapeAt P k).mainRows ≤ (shapeAt P k).mainRows - 1) = false :=
    decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤
      (P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) = false := decide_eq_false (by omega)
  have n3 : ((shapeAt P k).mainRows - 1 + 1 == (shapeAt P k).mainRows) = true := by
    rw [beq_iff_eq]
    omega
  have n4 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
      (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤
      (P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) = true := decide_eq_true (by omega)
  have n5 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i <
      (P.codes.base.getD (shapeAt P k).code default).ell) = true := decide_eq_true (by omega)
  simp only [rowsR, h3, n1, n2, n3, n4, n5, hw0, hp0, Bool.not_true, Bool.or_self, Bool.and_self,
    Bool.false_eq_true, if_false, if_true, Option.map_some, Nat.add_sub_cancel_left]

/-- Over the base field. -/
theorem pad_coin_f (i : Nat) (h3 : ((shapeAt P k).mainDeg == 3) = false)
    (ha : (shapeAt P k).answers ≠ 0) (hm : 0 < (shapeAt P k).mainRows)
    (hp : (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤
      (P.codes.base.getD (shapeAt P k).code default).ell)
    (hi : i < (stepsOf P.codes (shapeAt P k) (ride k)).pad) :
    (rowsR P ride data cs k).mainF ((shapeAt P k).mainRows - 1)
        ((P.codes.base.getD (shapeAt P k).code default).ell -
          (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) =
      cf cs ((startR P ride k).f + ((stepsOf P.codes (shapeAt P k) (ride k)).tails + i)) := by
  have hw0 : ((stepsOf P.codes (shapeAt P k) (ride k)).word != 0) = false := by
    have : ((shapeAt P k).answers == 0) = false := beq_eq_false_iff_ne.2 ha
    simp only [stepsOf, this, Bool.and_false, Bool.false_eq_true, if_false, bne_self_eq_false]
  have hp0 : ((stepsOf P.codes (shapeAt P k) (ride k)).pad != 0) = true := by
    rw [bne_iff_ne]
    omega
  have n1 : decide ((shapeAt P k).mainRows ≤ (shapeAt P k).mainRows - 1) = false :=
    decide_eq_false (by omega)
  have n2 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤
      (P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) = false := decide_eq_false (by omega)
  have n3 : ((shapeAt P k).mainRows - 1 + 1 == (shapeAt P k).mainRows) = true := by
    rw [beq_iff_eq]
    omega
  have n4 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
      (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤
      (P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i) = true := decide_eq_true (by omega)
  have n5 : decide ((P.codes.base.getD (shapeAt P k).code default).ell -
        (stepsOf P.codes (shapeAt P k) (ride k)).pad + i <
      (P.codes.base.getD (shapeAt P k).code default).ell) = true := decide_eq_true (by omega)
  simp only [rowsR, h3, n1, n2, n3, n4, n5, hw0, hp0, Bool.or_self, Bool.and_self,
    Bool.false_eq_true, if_false, if_true, Option.map_some, Nat.add_sub_cancel_left]

/-- Step (5). -/
theorem maskTail_coin (r q : Nat) (hr : r < (shapeAt P k).maskRows)
    (hq : q < (P.codes.mask.getD (shapeAt P k).maskCode default).r) :
    (rowsR P ride data cs k).maskTl r q =
      ce cs (maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask +
        r * (P.codes.mask.getD (shapeAt P k).maskCode default).r + q) := by
  simp only [rowsR]
  rw [if_pos ⟨hr, hq⟩]
  rfl

/-! ## The pad that the verifier's sample row reads -/

/-- Under the test a base code's message length is 2 ^ logEll. -/
theorem two_logEll_base (codes : Codes) (c : Nat) (h : Own.lengthsFit codes = true)
    (hc : c < codes.base.size) :
    2 ^ (codes.base.getD c default).logEll = (codes.base.getD c default).ell := by
  simp only [Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true] at h
  have := h.1 c hc
  simp only [Own.twoPower, Bool.and_eq_true, beq_iff_eq] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc]
  exact this.2

theorem two_logEll_mask (codes : Codes) (c : Nat) (h : Own.lengthsFit codes = true)
    (hc : c < codes.mask.size) :
    2 ^ (codes.mask.getD c default).logEll = (codes.mask.getD c default).ell := by
  simp only [Own.lengthsFit, Bool.and_eq_true, Array.all_eq_true] at h
  have := h.2 c hc
  simp only [Own.twoPower, Bool.and_eq_true, beq_iff_eq] at this
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hc]
  exact this.2

/-- **In a message without a mask row.** -/
theorem pad_main_at (codes : Codes) (s : OracleShape) (i t : Nat)
    (h : Own.lengthsFit codes = true) (hc : s.code < codes.base.size) (hz : s.maskRows = 0)
    (ht : t < (K1.Msg.of codes s).e) :
    ((K1.Msg.of codes s).pad i)[t]? = some ((s.mainRows - 1) +
      ((codes.base.getD s.code default).ell - (K1.Msg.of codes s).e * s.answers +
        (K1.Msg.of codes s).e * i + t) * 2 ^ K1.clog s.mainRows, t) := by
  have hk : ((K1.Msg.of codes s).Kzk != 0) = false := by
    show (s.maskRows != 0) = false
    rw [hz]
    rfl
  unfold K1.Msg.pad
  simp only [hk, Bool.false_eq_true, if_false]
  rw [List.getElem?_map, List.getElem?_range ht]
  show some ((s.mainRows - 1) +
    (2 ^ (codes.base.getD s.code default).logEll - _ + _ + t) * _, t) = _
  rw [two_logEll_base codes s.code h hc]
  rfl

/-- **Where the message has mask rows**: the pad lies in the last mask row. -/
theorem pad_mask_at (codes : Codes) (s : OracleShape) (i : Nat)
    (h : Own.lengthsFit codes = true) (hc : s.maskCode < codes.mask.size) (hz : s.maskRows ≠ 0) :
    (K1.Msg.of codes s).pad i = [((s.maskRows - 1) +
      ((codes.mask.getD s.maskCode default).ell - s.answers + i) * 2 ^ K1.clog s.maskRows, 0)] := by
  have hk : ((K1.Msg.of codes s).Kzk != 0) = true := by
    show (s.maskRows != 0) = true
    rw [bne_iff_ne]
    exact hz
  have he : (K1.Msg.of codes s).e = 1 := by
    unfold K1.Msg.e
    rw [hk]
    rfl
  unfold K1.Msg.pad
  simp only [hk, if_true, he, List.range_one, List.map_cons, List.map_nil, Nat.one_mul,
    Nat.add_zero]
  show [((s.maskRows - 1) + (2 ^ (codes.mask.getD s.maskCode default).logEll - s.answers + i) * _,
    0)] = _
  rw [two_logEll_mask codes s.maskCode h hc]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tail_coin_e
#print axioms ProofFile.Honest.K1.tail_coin_f
#print axioms ProofFile.Honest.K1.word_coin_e
#print axioms ProofFile.Honest.K1.word_coin_f
#print axioms ProofFile.Honest.K1.pad_coin_e
#print axioms ProofFile.Honest.K1.pad_coin_f
#print axioms ProofFile.Honest.K1.maskTail_coin
#print axioms ProofFile.Honest.K1.two_logEll_base
#print axioms ProofFile.Honest.K1.two_logEll_mask
#print axioms ProofFile.Honest.K1.pad_main_at
#print axioms ProofFile.Honest.K1.pad_mask_at
