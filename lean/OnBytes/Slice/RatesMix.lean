-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RatesMix.lean: the error counts of the two code switches' second rounds at the small
test configuration, as probabilities.

In the second round of a code switch (CS) the verifier draws positions and one element of the
extension field. The library's count of bad verifier messages has two parts: X q for the positions,
where q is the size of the field, and n^t Z for the element, where n^t is the number of lists of
positions.
This file compares such a count with a power of one half, and does it at the rounds number 11 and 16
of the small test configuration's description, counted from 0.

Main theorems.
 `mix_num`      the comparison of natural numbers, in variables: it holds for every q from Q on if
                it holds at Q and the factor of q on the left is at most that on the right.
 `mix_round`    the clause on the count of a round that draws t positions of a bits and one element.
 `num11`        round 11, at the radius 2539: 63 positions of 13 bits, 8 test bits, 21 hash blocks.

 `num16`        round 16, at the radius 2673: 43 positions of 13 bits, 8 test bits, 16 hash blocks.


The count enters as a variable with an equation, the radius too, and the arithmetic is done for a
variable in the place of q. The reason is given in the head of OnBytes/Slice/RatesToy.lean.

Not claimed here: that the counts are those of the two code switches, and that the radii are right
for the stages' codes.
-/
import OnBytes.Slice.RatesNum
import OnBytes.Slice.RatesToy
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-! ### In variables -/

/-- The comparison of natural numbers for a round that draws positions and one element. If it
holds at Q, and the factor of q on the left is at most that on the right, it holds for every q
from Q on. -/
theorem mix_num (A M X Y Z T U Q q : ℕ) (hq : Q ≤ q) (h1 : A * X * T ≤ M * Y * U)
    (h2 : A * X * T * Q + A * (Y * Z) * T ≤ M * Y * U * Q) :
    A * (X * q + Y * Z) * T ≤ M * (Y * q) * U := by
  have h := lin_le (A * X * T) (A * (Y * Z) * T) (M * Y * U) Q q h1 hq h2
  calc A * (X * q + Y * Z) * T = A * X * T * q + A * (Y * Z) * T := by ring
    _ ≤ M * Y * U * q := h
    _ = M * (Y * q) * U := by ring

/-- The clause on the count e of a round that draws t positions of a bits and one of q elements:
e * w is at most 2^-k times the number of the round's written verifier messages. The count is
X q + (2^a)^t Z. B, W: the round's numbers of hash blocks and of test bits. -/
theorem mix_round (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (a t B W k q X Z e : ℕ)
    (hn : nVals (Fmt.dsOf d.entry d.kind) = (2 ^ a) ^ t * q)
    (hb : (bsRound .two d.entry d.kind).b = B) (hw : d.entry.work = W) (hq : 0 < q)
    (he : e = X * q + (2 ^ a) ^ t * Z)
    (hnum : (2 ^ 128 + 1) ^ B * (X * q + (2 ^ a) ^ t * Z) * 2 ^ k ≤
      (2 ^ 128) ^ B * ((2 ^ a) ^ t * q) * 2 ^ W) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ k * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have hD : 0 < (2 ^ a) ^ t * q := Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos a)) hq
  refine entry_pow d hlog e (X * q + (2 ^ a) ^ t * Z) ((2 ^ a) ^ t * q) B W k hb hw hD ?_ hnum
  rewrite [hn, he]
  exact le_rfl

/-- Round 11 in numbers, for a variable q and a radius r. -/
theorem num11 (q r : ℕ) (hq : 2 ^ 191 ≤ q) (hr : r = 2539) :
    (2 ^ 128 + 1) ^ 21 * ((2 ^ 13 - r - 1) ^ 63 * q + (2 ^ 13) ^ 63 * (1 * (1 + 3 * 63))) * 2 ^ 31 ≤
      (2 ^ 128) ^ 21 * ((2 ^ 13) ^ 63 * q) * 2 ^ 8 := by
  subst hr
  exact mix_num _ _ _ _ _ _ _ (2 ^ 191) q hq (by decide +kernel) (by decide +kernel)

/-- Round 16 in numbers, for a variable q and a radius r. -/
theorem num16 (q r : ℕ) (hq : 2 ^ 191 ≤ q) (hr : r = 2673) :
    (2 ^ 128 + 1) ^ 16 * ((2 ^ 13 - r - 1) ^ 43 * q + (2 ^ 13) ^ 43 * (1 * (1 + 3 * 43))) * 2 ^ 31 ≤
      (2 ^ 128) ^ 16 * ((2 ^ 13) ^ 43 * q) * 2 ^ 8 := by
  subst hr
  exact mix_num _ _ _ _ _ _ _ (2 ^ 191) q hq (by decide +kernel) (by decide +kernel)

/-! ### What the two rounds draw -/

/-- The extension field has at least 2^191 elements. -/
theorem card_GE_large : 2 ^ 191 ≤ Fintype.card GE := by
  have h : 2 ^ 191 ≤ Fmt.Fld.two.p ^ 3 := by decide +kernel
  exact le_of_le_of_eq h card_GE.symm

/-- One element, then an empty draw of matrix entries. -/
theorem nVals_elem_end : nVals [.elem, .trits 0] = Fintype.card GE := by
  rewrite [card_GE]
  simp only [nVals]
  ring

/-! ### The two rounds -/

end OnBytes.Slice

#print axioms OnBytes.Slice.mix_num
#print axioms OnBytes.Slice.mix_round
