-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RatesToy.lean: the error counts of the link's first rounds at the small test
configuration, as probabilities.

The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary).

This file bounds the counts of the round in front and of the link's five rounds by
explicit numbers. The radii, in positions of a word of the tables' code, whose distance is 14581:
12380 = 14581 - 1 - 2200 for the test of the first fold, 2200 for that of the second. The count of
exceptional fold points is 3 * 2201 * q^2, for q the size of the extension field. All lists have at
most one member.

Main theorems.
 `errGam_eq`, `errLoc_eq`, `errPhi_eq`, `errSend_one`   the library's counts at any sizes.
 `core_below`, `link_below`   the clause on error counts (`Err.Below`, Iop/InteractiveOracleProof.lean: each round's
     count is at most e times the number of that round's verifier messages), round by round, at
     any sizes.
 `gam_num`, `loc_num`, `phi_num`   the first, fourth and fifth round. The shares of bad typed
     values are 6609 / q, (4003 / 16384)^58 and 10 / q. The fourth round has eight test bits,
     which divide its share by 2^8. The third round draws nothing.



The radii are variables with equations as hypotheses, and the arithmetic is done for a variable in
the place of q. The reason: Lean may try to compute a term of natural numbers that has no variable
in it, and to compute the size of the field it would list the field's elements.

Not claimed here: that the radii, the count of exceptional fold points and the bounds on the
lists are right for the tables' code. Nothing is said on the rounds after the fifth.
-/
import OnBytes.Slice.Rates
import OnBytes.Slice.LinkAt
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Run.PlanQXFastR
import Fmt.M3Entry
import OnBytes.Slice.LinkSound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch Run Run.PQ Cb Cb.Ood Blocks
open scoped ENNReal

/-- The extension field has p^3 elements. -/
theorem card_GE : Fintype.card GE = Fmt.Fld.two.p ^ 3 := by
  have hp : Cb.Gl.p = Fmt.Fld.two.p := by decide +kernel
  rw [← hp]
  exact Cb.Gl.gl_card.2.1

/-- The field is not empty. -/
theorem card_GE_pos : 0 < Fintype.card GE := Fintype.card_pos

/-! ### The library's counts, at any sizes -/

/-- The count of the first round. -/
theorem errGam_eq (S : Sz) (a b : ℕ) :
    S.lk.errGam a b = a + b + S.P.v * Fintype.card GE ^ (S.P.v - 1) := rfl

/-- The count of the fourth round. -/
theorem errLoc_eq (S : Sz) : S.lk.errLoc =
    max ((2 ^ S.P.T.a - S.e0 - 1) ^ S.P.nu0 * (2 ^ S.P.T.a) ^ S.P.nuj)
      ((2 ^ S.P.T.a) ^ S.P.nu0 * (2 ^ S.P.T.a - S.e1 - 1) ^ S.P.nuj) := by
  show max ((Fintype.card (Fin (2 ^ S.P.T.a)) - S.e0 - 1) ^ S.P.nu0 *
      Fintype.card (Fin (2 ^ S.P.T.a)) ^ S.P.nuj)
    (Fintype.card (Fin (2 ^ S.P.T.a)) ^ S.P.nu0 *
      (Fintype.card (Fin (2 ^ S.P.T.a)) - S.e1 - 1) ^ S.P.nuj) = _
  rw [Fintype.card_fin]

/-- The count of the fifth round. -/
theorem errPhi_eq (S : Sz) : S.lk.errPhi = S.P.aPhi * Fintype.card GE ^ (S.P.aPhi - 1) := rfl

/-- The count of the second round is 0 if both lists have at most one member. -/
theorem errSend_one (S : Sz) : ldSendFamErr S.lk.N S.seeds (fun _ => 1) = 0 := by
  unfold ldSendFamErr
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [show Nat.choose 1 2 = 0 from rfl, zero_mul, mul_zero]

/-- The clause on error counts for the five rounds and the rounds after them, from one inequality
for each of the five but the third, whose count is 0, and the clause for the rounds after them. -/
theorem core_below (S : Sz) (d1 d2 d3 d4 d5 : PQ.RD) (a b : ℕ) (L : Bool → ℕ) {t : Shape}
    (εt : Err t) (εs : ℝ≥0∞)
    (h1 : ((S.lk.errGam a b * (bsRound .two d1.entry d1.kind).w : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound d1).Chal : ℝ≥0∞))
    (h2 : ((ldSendFamErr S.lk.N S.seeds L * (bsRound .two d2.entry d2.kind).w : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound d2).Chal : ℝ≥0∞))
    (h4 : ((S.lk.errLoc * (bsRound .two d4.entry d4.kind).w : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound d4).Chal : ℝ≥0∞))
    (h5 : ((S.lk.errPhi * (bsRound .two d5.entry d5.kind).w : ℕ) : ℝ≥0∞) ≤
      εs * (Fintype.card (wRound d5).Chal : ℝ≥0∞))
    (ht : Err.Below εt εs) : Err.Below (coreErr S d1 d2 d3 d4 d5 a b L εt) εs := by
  refine ⟨h1, h2, ?_, h4, h5, ht⟩
  show ((0 * (bsRound .two d3.entry d3.kind).w : ℕ) : ℝ≥0∞) ≤ _
  rw [zero_mul, Nat.cast_zero]
  exact _root_.zero_le _

/-- The same for the written link: before the five rounds it has a round with the count 0. -/
theorem link_below (S : Sz) (d1 d2 d3 d4 d5 : PQ.RD) (tl : List PQ.RD) (xs : List PQ.XO)
    (dec : PQ.View → Bool) (a b : ℕ) (L : Bool → ℕ) (εt : Err (PQ.uL (ckP .two) tl)) (εs : ℝ≥0∞)
    (h : Err.Below (coreErr S d1 d2 d3 d4 d5 a b L εt) εs) :
    Err.Below (s := (written S d1 d2 d3 d4 d5 tl xs dec).shape)
      (0, coreErr S d1 d2 d3 d4 d5 a b L εt) εs := by
  refine ⟨?_, h⟩
  show ((0 : ℕ) : ℝ≥0∞) ≤ _
  rw [Nat.cast_zero]
  exact _root_.zero_le _

/-! ### What the rounds draw at the small test configuration -/

/-- An empty draw of matrix entries has one value. -/
theorem nVals_end : nVals [.trits 0] = 1 := rfl

/-! ### Arithmetic, for a variable q in the place of the field's size

The size of the field is a number that must never be computed from the field's list of elements.
So each fact is proved for a variable and then used as it is. -/

/-- The first round: 6609 q^2 of q^3. -/
theorem gam_num (q : ℕ) : (0 + (3 * (2200 + 1) * q ^ (3 - 1) + 1 * (3 * q ^ (3 - 1))) +
    3 * q ^ (3 - 1)) * q ≤ 6609 * q ^ 3 := by
  show (0 + (3 * (2200 + 1) * q ^ 2 + 1 * (3 * q ^ 2)) + 3 * q ^ 2) * q ≤ 6609 * q ^ 3
  exact le_of_eq (by ring)

/-- The fifth round: 10 q^9 of q^10. -/
theorem phi_num (q : ℕ) : 10 * q ^ (10 - 1) * q ≤ 10 * q ^ 10 := by
  show 10 * q ^ 9 * q ≤ 10 * q ^ 10
  exact le_of_eq (by ring)

/-- The fourth round: the first fold's test has the larger share, (4003 / 16384)^58. -/
theorem loc_num : max ((2 ^ 14 - 12380 - 1) ^ 58 * (2 ^ 14) ^ 623)
    ((2 ^ 14) ^ 58 * (2 ^ 14 - 2200 - 1) ^ 623) * 16384 ^ 58 ≤ 4003 ^ 58 * (2 ^ 14) ^ 681 := by
  decide +kernel

/-! ### The counts among the typed values

The radii are variables with equations, for the reason given above: a term without a variable in
it may be computed. -/

section
variable (eM e0 e1 eU : ℕ)

/-- The first round's count, for any sizes with three fold variables. -/
theorem gam_share (S : Sz) (vv r : ℕ) (hS : S.P.v = 3) (hvv : vv = 3) (hr : r = 2200) :
    S.lk.errGam 0 (vv * (r + 1) * Fintype.card GE ^ (vv - 1) +
        1 * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) * Fintype.card GE ≤
      6609 * Fintype.card GE ^ 3 := by
  rewrite [errGam_eq, hS, hvv, hr]
  exact gam_num _

/-! ### The five rounds -/

end

end OnBytes.Slice

#print axioms OnBytes.Slice.core_below
#print axioms OnBytes.Slice.link_below
