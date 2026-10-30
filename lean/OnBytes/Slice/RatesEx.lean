-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RatesEx.lean: the bias of a written round, by what the round draws.

OnBytes/Slice/Rates.lean turns a share of bad typed values of a round into a share of bad written
verifier messages, at the price of a factor 1 + 2^-128 (`kapSl 128`) for each of the round's hash
blocks. The library proves a price that is never larger, and this file states it for a round: three
such factors for each element of the extension field that the round draws, and none for a position,
a matrix entry or a sealing (`Run.ex`, `Run.drawPage_all`, `Run.drawBS_good`). So a round that draws
positions alone has no bias.

Main theorems.
 `bsRound_good_ex`       the round's block sampler is good at the factor to the power `exAll` of
                         the round's draws.
 `exAll_dsOf`            that power is 3 ((drawE - drawNZ) + drawNZ), in natural numbers: three
                         times the entry's drawE if its drawNZ is at most its drawE.
 `below_round_work_ex`, `below_round_div_ex`   the statements `below_round_work` and
                         `below_round_div` of OnBytes/Slice/Rates.lean with that power.

What is not claimed: any bound on an error count itself. Nothing on the hash function: a share is a
count among all strings of hash blocks and test bits. For proofs only; the program, that is the Lean
port built from OnBytes/, does not import this file.

-/
import Run.DrawPageProofs
import OnBytes.Slice.Rates

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- The block sampler of a round is good at the bias 1 + 2^-128 to the power `exAll` of the round's
draws. Asked: the entry has `logN` at most 64. -/
theorem bsRound_good_ex (e : Fmt.Entry) (k : Fmt.Kind) (h : e.logN ≤ 64) :
    (bsRound .two e k).Good (kapSl 128 ^ exAll (Fmt.dsOf e k)) :=
  drawBS_good _ _ e64 0 _ _ _ _ (drawPage_all .two _ (lawful_dsOf e k h)).1

/-- The power of two lists of draws in a row. -/
theorem exAll_append (a b : List Fmt.Draw) : exAll (a ++ b) = exAll a + exAll b := by
  induction a with
  | nil => exact (Nat.zero_add _).symm
  | cons d ds ih =>
      show ex d + exAll (ds ++ b) = ex d + exAll ds + exAll b
      rw [ih, Nat.add_assoc]

/-- The power of one draw repeated. -/
theorem exAll_replicate (n : ℕ) (d : Fmt.Draw) : exAll (List.replicate n d) = n * ex d := by
  induction n with
  | zero => exact (Nat.zero_mul _).symm
  | succ n ih =>
      show ex d + exAll (List.replicate n d) = (n + 1) * ex d
      rw [ih]
      ring

/-- The power of s seeds of v coordinates. -/
theorem exAll_seeds (s v : ℕ) : exAll (Fmt.dsSeeds s v) = s * (3 * v + 3) := by
  induction s with
  | zero => exact (Nat.zero_mul _).symm
  | succ s ih =>
      have e : Fmt.dsSeeds (s + 1) v =
          (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) ++ Fmt.dsSeeds s v := by
        unfold Fmt.dsSeeds
        rw [List.replicate_succ, List.flatten_cons]
      rw [e, exAll_append, exAll_append, exAll_replicate, ih]
      show v * 3 + (3 + 0) + s * (3 * v + 3) = (s + 1) * (3 * v + 3)
      ring

/-- The power of a round's draws, from the entry's two numbers of elements: drawE, all elements, and
drawNZ, those among them that are other than 0. The subtraction is that of natural numbers: the
right side is 3 * drawE if drawNZ ≤ drawE, which is not asked here. -/
theorem exAll_dsOf (e : Fmt.Entry) (k : Fmt.Kind) :
    exAll (Fmt.dsOf e k) = 3 * ((e.drawE - e.drawNZ) + e.drawNZ) := by
  have hel : exAll (Fmt.dsElems e k) = 3 * ((e.drawE - e.drawNZ) + e.drawNZ) := by
    unfold Fmt.dsElems
    split
    · rw [exAll_append, exAll_seeds, exAll_replicate]
      show e.drawNZ * (3 * ((e.drawE - e.drawNZ) / e.drawNZ) + 3) +
        (e.drawE - e.drawNZ) % e.drawNZ * 3 = _
      have hm := Nat.div_add_mod (e.drawE - e.drawNZ) e.drawNZ
      nlinarith [hm]
    · rw [exAll_append, exAll_replicate, exAll_replicate]
      show (e.drawE - e.drawNZ) * 3 + e.drawNZ * 3 = _
      ring
  have htail : exAll (Fmt.Draw.trits e.trits :: (if k = .sealed then [Fmt.Draw.sealed] else [])) =
      0 := by
    split <;> rfl
  unfold Fmt.dsOf
  rw [exAll_append, exAll_append, exAll_replicate, hel, htail]
  show e.poss * 0 + (3 * ((e.drawE - e.drawNZ) + e.drawNZ) + 0) = _
  ring

/-- `below_round_work` (OnBytes/Slice/Rates.lean) with the bias by what the round draws. -/
theorem below_round_work_ex (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (e : ℕ) (c : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) * 2 ^ d.entry.work ≤
      (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * c) *
        (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have hr := (bsRound_good_ex d.entry d.kind hlog).ratio
  rw [card_wRound, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  calc (e : ℝ≥0∞) * ((bsRound .two d.entry d.kind).w : ℝ≥0∞)
      ≤ (c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) *
          ((bsRound .two d.entry d.kind).w : ℝ≥0∞) := mul_le_mul' h le_rfl
    _ = c * (((bsRound .two d.entry d.kind).w : ℝ≥0∞) *
          (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) := by ring
    _ ≤ c * (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) *
          (Fintype.card (Fin (bsRound .two d.entry d.kind).b → Dig 256) : ℝ≥0∞)) :=
        mul_le_mul' le_rfl hr
    _ = kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * c *
          (Fintype.card (Fin (bsRound .two d.entry d.kind).b → Dig 256) : ℝ≥0∞) := by ring

/-- `below_round_div` (OnBytes/Slice/Rates.lean) with the bias by what the round draws. -/
theorem below_round_div_ex (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (e : ℕ) (c : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ c * (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work)) *
        (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have h0 : (2 : ℝ≥0∞) ^ d.entry.work ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ d.entry.work ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞)
      = ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) * 2 ^ d.entry.work /
          2 ^ d.entry.work := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ ≤ (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * c) *
          (Fintype.card (wRound d).Chal : ℝ≥0∞) / 2 ^ d.entry.work :=
        ENNReal.div_le_div_right (below_round_work_ex d hlog e c h) _
    _ = (kapSl 128 ^ exAll (Fmt.dsOf d.entry d.kind) * (c / 2 ^ d.entry.work)) *
          (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

end OnBytes.Slice

#print axioms OnBytes.Slice.bsRound_good_ex
#print axioms OnBytes.Slice.exAll_dsOf
#print axioms OnBytes.Slice.below_round_work_ex
#print axioms OnBytes.Slice.below_round_div_ex
