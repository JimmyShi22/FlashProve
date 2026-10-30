-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PadLaw.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: A PAD's COIN, UNDER THE PUBLIC TEST sendFits (Honest/K1/Coins.lean): the held word
AT THE INDEX THAT THE VERIFIER's SAMPLE ROW READS (K1.Msg.pad, Johnson/Desc/K1/Own.lean) is the
pad's coin. Statements and proofs.

  fits_lengths, fits_pad, fits_shape, fits_code, fits_maskCode, fits_main, fits_noRide   what
                sendFits hands: the codes' lengths' test · a sampled message's pads fit their row ·
                the plan's own test on each sent shape: so the numbers of the codes that a message's
                rows name lie in the arrays, and a message without a mask row has a main row · a
                sampled message's table does not ride
  pad_le_of_fits   so the count of a pad in a main row is at most the code's message length
  pad_held_e    a message without a mask row, over the extension field: the held word at the index
                of answer i's pad is the coin number tails + i of the message's main coins
  pad_held_f    over the base field: at the index of entry t of answer i's pad: the coin number
                tails + (3 i + t)
  pad_held_mask a message with mask rows: the held word, in the mask table, at the index of answer
                i's pad is the mask coin with the format's number (ell - answers + i) * m + (m - 1)

Of an entry x of K1.Msg.pad's list its index x.1 alone is read, not the power x.2 that goes with it.

Limits. What is WRITTEN where: no sentence on what a coin is for. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.CoinLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt held_new word_main word_mask)

variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
  (cs : Cs (dueR P ride)) (k : Nat)

theorem fits_lengths (hf : sendFits P ride = true) : Own.lengthsFit P.codes = true := by
  simp only [sendFits, Bool.and_eq_true] at hf
  exact hf.1

theorem fits_pad (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (ha : (shapeAt P k).answers ≠ 0) : (K1.Msg.of P.codes (shapeAt P k)).padFits = true := by
  simp only [sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq] at hf
  rcases (hf.2 k hk).1.2 with h | h
  · exact absurd h ha
  · exact h

/-- sendFits hands the plan's own test on each sent shape. -/
theorem fits_shape (hf : sendFits P ride = true) (hk : k < P.sent.size) :
    Own.sentShapeFits P.codes (shapeAt P k) = true := by
  simp only [sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hf
  exact (hf.2 k hk).1.1

/-- A message with a main row names a base code in the array. -/
theorem fits_code (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (hm : (shapeAt P k).mainRows ≠ 0) : (shapeAt P k).code < P.codes.base.size := by
  have h := fits_shape P ride k hf hk
  simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h.1.1.2 with h0 | h0
  · exact absurd h0 hm
  · exact h0

/-- One with a mask row names a mask code in the array. -/
theorem fits_maskCode (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (hz : (shapeAt P k).maskRows ≠ 0) : (shapeAt P k).maskCode < P.codes.mask.size := by
  have h := fits_shape P ride k hf hk
  simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h.1.2 with h0 | h0
  · exact absurd h0 hz
  · exact h0

/-- A message without a mask row has a main row. -/
theorem fits_main (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (hz : (shapeAt P k).maskRows = 0) : 0 < (shapeAt P k).mainRows := by
  have h := fits_shape P ride k hf hk
  simp only [Own.sentShapeFits, Bool.and_eq_true, decide_eq_true_eq] at h
  have := h.1.1.1
  omega

/-- A sampled message's table does not ride. -/
theorem fits_noRide (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (ha : (shapeAt P k).answers ≠ 0) : ride k = none := by
  simp only [sendFits, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hf
  have h := (hf.2 k hk).2
  cases hr : ride k with
  | none => rfl
  | some R =>
    rw [hr] at h
    simp only [Option.map_some, Option.getD_some, rideFits, Bool.and_eq_true, beq_iff_eq] at h
    exact absurd h.1.1.1.1.1 ha

/-- The count of a pad in a main row is at most the code's message length. -/
theorem pad_le_of_fits (hf : sendFits P ride = true) (hk : k < P.sent.size) :
    (stepsOf P.codes (shapeAt P k) (ride k)).pad ≤
      (P.codes.base.getD (shapeAt P k).code default).ell := by
  by_cases hp : ((shapeAt P k).maskRows == 0 && (shapeAt P k).answers != 0) = true
  · have hp' := hp
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hp'
    have h := fits_pad P ride k hf hk hp'.2
    have hc := fits_code P ride k hf hk (Nat.ne_of_gt (fits_main P ride k hf hk hp'.1))
    have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = false := by
      show ((shapeAt P k).maskRows != 0) = false
      rw [hp'.1]
      rfl
    simp only [K1.Msg.padFits, K1.Msg.e, hK, Bool.false_or, Bool.false_eq_true, if_false,
      decide_eq_true_eq] at h
    rw [show (K1.Msg.of P.codes (shapeAt P k)).logEll =
      (P.codes.base.getD (shapeAt P k).code default).logEll from rfl,
      two_logEll_base P.codes _ (fits_lengths P ride hf) hc] at h
    simp only [stepsOf, hp, if_true]
    exact h
  · simp only [stepsOf, hp, Bool.false_eq_true, if_false]
    exact Nat.zero_le _

/-- **A pad's coin, over the extension field.** -/
theorem pad_held_e (w : Words GE) (first i : Nat) (x : Nat × Nat) (hf : sendFits P ride = true)
    (hk : k < P.sent.size) (h3 : ((shapeAt P k).mainDeg == 3) = true)
    (hz : (shapeAt P k).maskRows = 0) (hi : i < (shapeAt P k).answers)
    (hx : ((K1.Msg.of P.codes (shapeAt P k)).pad i)[0]? = some x) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .main x.1 =
      ce cs ((startR P ride k).e + ((stepsOf P.codes (shapeAt P k) (ride k)).tails + i)) := by
  have hm := fits_main P ride k hf hk hz
  have hc := fits_code P ride k hf hk (Nat.ne_of_gt hm)
  have he : (K1.Msg.of P.codes (shapeAt P k)).e = 1 := by
    show (if _ || ((shapeAt P k).mainDeg == 3) then 1 else 3) = 1
    rw [h3, Bool.or_true]
    rfl
  have hpad : (stepsOf P.codes (shapeAt P k) (ride k)).pad = (shapeAt P k).answers := by
    have ha : ((shapeAt P k).answers != 0) = true := by
      rw [bne_iff_ne]
      omega
    simp only [stepsOf, hz, ha, h3, beq_self_eq_true, Bool.and_self, if_true, Nat.one_mul]
  have hle := pad_le_of_fits P ride k hf hk
  rw [pad_main_at P.codes _ i 0 (fits_lengths P ride hf) hc hz (by rw [he]; exact Nat.one_pos),
    he] at hx
  obtain rfl := Option.some.inj hx
  rw [held_new w first P _ k hk]
  show (rowsR P ride data cs k).word (shapeAt P k) .main
    ((shapeAt P k).mainRows - 1 + _ * 2 ^ K1.clog (shapeAt P k).mainRows) = _
  rw [word_main _ _ _ _ (by omega), h3]
  show (rowsR P ride data cs k).mainE _ _ = _
  have := pad_coin_e P ride data cs k i h3 (by omega) hm hle (by rw [hpad]; exact hi)
  rw [hpad] at this
  rw [← this]
  congr 1
  omega

/-- **Over the base field**: entry t of answer i's pad. -/
theorem pad_held_f (w : Words GE) (first i t : Nat) (x : Nat × Nat)
    (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (h3 : ((shapeAt P k).mainDeg == 3) = false) (hz : (shapeAt P k).maskRows = 0)
    (hi : i < (shapeAt P k).answers) (ht : t < 3)
    (hx : ((K1.Msg.of P.codes (shapeAt P k)).pad i)[t]? = some x) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .main x.1 =
      algebraMap GF GE (cf cs ((startR P ride k).f +
        ((stepsOf P.codes (shapeAt P k) (ride k)).tails + (3 * i + t)))) := by
  have hm := fits_main P ride k hf hk hz
  have hc := fits_code P ride k hf hk (Nat.ne_of_gt hm)
  have he : (K1.Msg.of P.codes (shapeAt P k)).e = 3 := by
    show (if ((shapeAt P k).maskRows != 0) || ((shapeAt P k).mainDeg == 3) then 1 else 3) = 3
    rw [h3, hz]
    rfl
  have hpad : (stepsOf P.codes (shapeAt P k) (ride k)).pad = 3 * (shapeAt P k).answers := by
    have ha : ((shapeAt P k).answers != 0) = true := by
      rw [bne_iff_ne]
      omega
    simp only [stepsOf, hz, ha, h3, beq_self_eq_true, Bool.and_self, if_true, Bool.false_eq_true,
      if_false]
  have hle := pad_le_of_fits P ride k hf hk
  rw [pad_main_at P.codes _ i t (fits_lengths P ride hf) hc hz (by rw [he]; exact ht), he] at hx
  obtain rfl := Option.some.inj hx
  rw [held_new w first P _ k hk]
  show (rowsR P ride data cs k).word (shapeAt P k) .main
    ((shapeAt P k).mainRows - 1 + _ * 2 ^ K1.clog (shapeAt P k).mainRows) = _
  rw [word_main _ _ _ _ (by omega), h3]
  show algebraMap GF GE ((rowsR P ride data cs k).mainF _ _) = _
  have := pad_coin_f P ride data cs k (3 * i + t) h3 (by omega) hm hle (by rw [hpad]; omega)
  rw [hpad] at this
  rw [← this]
  congr 2
  omega

/-- **A message with mask rows**: the pad lies in the last mask row. -/
theorem pad_held_mask (w : Words GE) (first i : Nat) (x : Nat × Nat)
    (hf : sendFits P ride = true) (hk : k < P.sent.size)
    (hz : (shapeAt P k).maskRows ≠ 0) (hi : i < (shapeAt P k).answers)
    (hx : ((K1.Msg.of P.codes (shapeAt P k)).pad i)[0]? = some x) :
    Johnson.Prover.Send.held w first P (rowsR P ride data cs) (first + k) .mask x.1 =
      ce cs (maskStart P ride k +
        (((P.codes.mask.getD (shapeAt P k).maskCode default).ell - (shapeAt P k).answers + i) *
          (shapeAt P k).maskRows + ((shapeAt P k).maskRows - 1))) := by
  have hc := fits_maskCode P ride k hf hk hz
  have hr := fits_noRide P ride k hf hk (by omega)
  have hle : (shapeAt P k).answers ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).ell := by
    have h := fits_pad P ride k hf hk (by omega)
    have hK : ((K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = true := by
      show ((shapeAt P k).maskRows != 0) = true
      rw [bne_iff_ne]
      exact hz
    simp only [K1.Msg.padFits, K1.Msg.e, hK, Bool.true_or, if_true, Nat.one_mul,
      decide_eq_true_eq] at h
    rw [show (K1.Msg.of P.codes (shapeAt P k)).logEllZk =
      (P.codes.mask.getD (shapeAt P k).maskCode default).logEll from rfl,
      two_logEll_mask P.codes _ (fits_lengths P ride hf) hc] at h
    exact h
  rw [pad_mask_at P.codes _ i (fits_lengths P ride hf) hc hz] at hx
  obtain rfl := Option.some.inj hx
  rw [held_new w first P _ k hk]
  show (rowsR P ride data cs k).word (shapeAt P k) .mask
    ((shapeAt P k).maskRows - 1 + _ * 2 ^ K1.clog (shapeAt P k).maskRows) = _
  rw [word_mask _ _ _ _ (by omega), mask_coin P ride data cs k _ _ hr (by omega) (by omega),
    Nat.add_assoc]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.fits_lengths
#print axioms ProofFile.Honest.K1.fits_pad
#print axioms ProofFile.Honest.K1.fits_shape
#print axioms ProofFile.Honest.K1.fits_code
#print axioms ProofFile.Honest.K1.fits_maskCode
#print axioms ProofFile.Honest.K1.fits_main
#print axioms ProofFile.Honest.K1.fits_noRide
#print axioms ProofFile.Honest.K1.pad_le_of_fits
#print axioms ProofFile.Honest.K1.pad_held_e
#print axioms ProofFile.Honest.K1.pad_held_f
#print axioms ProofFile.Honest.K1.pad_held_mask
