-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RatesTail.lean: rounds of the written link at the small test configuration whose
error counts are at most 2^-31 as probabilities.

The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary). Three kinds of its rounds are treated. A round
that draws one element of the extension field, with a count of at most 2^14. The last round, which
draws 41 positions of 15 bits and has eight test bits. The first, fourth and fifth round, whose
shares are in OnBytes/Slice/RatesToy.lean.


Main theorems.
 `elem_round`   a round that draws one element.
 `last_round`   the last round, at the radius 10738 (in positions of a code word). Its share of
                bad typed values is (22029 / 32768)^41, a little below 2^-23. The test bits divide
                it by 2^8. By a reckoning that is no theorem here the result is above 2^-32: hence
                the number 31.

 `core_num`     the three numbers of the first five rounds are at most 2^-31.

Not claimed here: that the counts and the radius are right for the codes. Nothing on the hash
function: a share is a count among all strings of hash blocks and test bits.
-/
import OnBytes.Slice.RatesNum
import OnBytes.Slice.RatesToy

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- The extension field has at least 2^191 elements. -/
theorem card_GE_big : 2 ^ 191 ≤ Fintype.card GE := by
  rewrite [Cb.Gl.gl_card.2.1]
  exact le_of_lt Cb.Gl.gl_card.2.2.1

/-- The typed values of a draw of one element. -/
theorem nVals_elem : nVals [.elem, .trits 0] = Fintype.card GE := by
  rw [card_GE]
  simp only [nVals]
  ring

/-! ### Arithmetic, for a variable q in the place of the field's size -/

/-- A number that is at most c * Q is at most c * q for every q from Q on. -/
theorem mul_le_of_big (a c Q q : ℕ) (hq : Q ≤ q) (h : a ≤ c * Q) : a ≤ c * q :=
  h.trans (Nat.mul_le_mul_left c hq)

/-- One element, five hash blocks, a count of at most 2^14. -/
theorem elem_num (e q : ℕ) (he : e ≤ 2 ^ 14) (hq : 2 ^ 191 ≤ q) :
    (2 ^ 128 + 1) ^ 5 * e * 2 ^ 31 ≤ (2 ^ 128) ^ 5 * q * 2 ^ 0 := by
  have h0 : (2 ^ 128 + 1) ^ 5 * 2 ^ 14 * 2 ^ 31 ≤ (2 ^ 128) ^ 5 * 2 ^ 191 * 2 ^ 0 := by
    decide +kernel
  calc (2 ^ 128 + 1) ^ 5 * e * 2 ^ 31 ≤ (2 ^ 128 + 1) ^ 5 * 2 ^ 14 * 2 ^ 31 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)
    _ ≤ (2 ^ 128) ^ 5 * 2 ^ 191 * 2 ^ 0 := h0
    _ ≤ (2 ^ 128) ^ 5 * q * 2 ^ 0 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hq)

/-- The last round's count among its typed values. -/
theorem last_share : (2 ^ 15 - 10738 - 1) ^ 41 * 32768 ^ 41 ≤ 22029 ^ 41 * (2 ^ 15) ^ 41 := by
  decide +kernel

/-- The last round: eleven hash blocks, eight test bits. -/
theorem last_num : (2 ^ 128 + 1) ^ 11 * 22029 ^ 41 * 2 ^ 31 ≤
    (2 ^ 128) ^ 11 * 32768 ^ 41 * 2 ^ 8 := by
  decide +kernel

/-! ### The rounds -/

/-- A round that draws one element, with five hash blocks, no test bit and a count e of at most
2^14: e * w is at most 2^-31 times the number of the round's written verifier messages (w: the
number in the law of the format's sampler). -/
theorem elem_round (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hds : Fmt.dsOf d.entry d.kind = [.elem, .trits 0])
    (hb : (bsRound .two d.entry d.kind).b = 5) (hw : d.entry.work = 0) (e : ℕ)
    (he : e ≤ 2 ^ 14) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 31 * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  refine entry_pow d hlog e e (Fintype.card GE) 5 0 31 hb hw card_GE_pos ?_
    (elem_num e _ he card_GE_big)
  rewrite [hds, nVals_elem]
  exact le_rfl

/-- The last round: 41 positions of 15 bits, eleven hash blocks, eight test bits, the count
e = (2^15 - 10738 - 1)^41. e * w is at most 2^-31 times the number of the round's written verifier
messages (w: the number in the law of the format's sampler). -/
theorem last_round (d : PQ.RD) (hlog : d.entry.logN ≤ 64)
    (hds : Fmt.dsOf d.entry d.kind = List.replicate 41 (Fmt.Draw.pos 15) ++ [.trits 0])
    (hb : (bsRound .two d.entry d.kind).b = 11) (hw : d.entry.work = 8) (e : ℕ)
    (he : e = (2 ^ 15 - 10738 - 1) ^ 41) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 31 * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  refine entry_pow d hlog e (22029 ^ 41) (32768 ^ 41) 11 8 31 hb hw (by positivity) ?_ last_num
  rewrite [hds, nVals_rep, nVals_end, mul_one, he]
  exact last_share

/-! ### The rounds of the small test configuration -/

/-- A count of 0 is at most every share. -/
theorem zero_round (d : PQ.RD) (e : ℕ) (he : e = 0) (c : ℝ≥0∞) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      c * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  rw [he, zero_mul, Nat.cast_zero]
  exact _root_.zero_le _

/-- The bias of B blocks times a share n / D is at most 2^-k, without test bits. -/
theorem rate_pow0 (B n D k : ℕ) (hD : 0 < D)
    (h : (2 ^ 128 + 1) ^ B * n * 2 ^ k ≤ (2 ^ 128) ^ B * D) :
    kapSl 128 ^ B * ((n : ℝ≥0∞) / (D : ℝ≥0∞)) ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
  have h1 := rate_pow B n D 0 k hD (by rw [pow_zero, mul_one]; exact h)
  rw [pow_zero, div_one] at h1
  exact h1

/-- The three numbers of the first five rounds are at most 2^-31. -/
theorem core_num :
    kapSl 128 ^ 14 * (((6609 : ℕ) : ℝ≥0∞) / ((Fintype.card GE : ℕ) : ℝ≥0∞)) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 31 ∧
      kapSl 128 ^ 171 * (((4003 ^ 58 : ℕ) : ℝ≥0∞) / ((16384 ^ 58 : ℕ) : ℝ≥0∞) / 2 ^ 8) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 31 ∧
      kapSl 128 ^ 45 * (((10 : ℕ) : ℝ≥0∞) / ((Fintype.card GE : ℕ) : ℝ≥0∞)) ≤
        (2 : ℝ≥0∞)⁻¹ ^ 31 :=
  ⟨rate_pow0 14 6609 _ 31 card_GE_pos
      (mul_le_of_big _ _ (2 ^ 191) _ card_GE_big (by decide +kernel)),
    rate_pow 171 (4003 ^ 58) (16384 ^ 58) 8 31 (by positivity) (by decide +kernel),
    rate_pow0 45 10 _ 31 card_GE_pos
      (mul_le_of_big _ _ (2 ^ 191) _ card_GE_big (by decide +kernel))⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.elem_round
#print axioms OnBytes.Slice.last_round
#print axioms OnBytes.Slice.core_num
