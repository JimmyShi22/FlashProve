-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/HeldRound.lean: in a round that holds in the planner's reckoning, a count that is at
most the planner's number meets the bound that the theorems on written rounds ask for.

The Lean port admits a plan only if each of its rounds holds (`finishHeld`; read off its callers, no
theorem), as the C++ planner that it renders is meant to: the planner's number for the round's
error, with a term for the distance of the round's drawn field elements from uniform, is at most
2 ^ (work - target) (`roundHolds`, OnBytes/Params/Planner.lean). The theorems of OnBytes/Slice/ ask
of a round: a count of bad typed values, times the sampler's weight w (`wOf` of
OnBytes/Slice/ChainErr.lean: at most w strings of blocks give one typed value), is at most a share
of the round's written verifier messages. This file joins the two for one round, whatever the chain
and the routine that planned it: if the count, as a share of the round's typed values, is at most
the planner's number for the round's error, and the round holds, then the count, times the weight,
is at most 2 ^ -target of the written messages. Asked besides: the setting has the format's field;
`logN` is at most 64; drawNZ is at most drawE; and, in a round that draws an element,
work + 66 ≤ target. Under that last condition the planner's term for the drawn elements pays for the
sampler's bias (OnBytes/Slice/RatesEx.lean). At a smaller target nothing is said of such a round.

Main theorem: `held_round`.
What is not claimed: that the planner's number bounds any count: that is the hypothesis `hc`. That
any count bounds a prover's chance. That `capped` bounds the sampler's distance from uniform: of its
value only "at least 3 * 2 ^ -193" is used. Nothing on a plan as a whole, on the routines that plan
rounds, or on the C++ planner, of which OnBytes/Params/ is a rendering. The work is counted as the
written round counts it: of the 2 ^ work strings of test bits over one string of blocks one passes.
Nothing on what that is worth against a prover who tries many times. For proofs only; the program,
that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.Planner
import OnBytes.Params.RealLaws
import OnBytes.Slice.RatesEx

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run OnBytes.Params
open scoped ENNReal

/-- For x ≥ 0: (1 + x) ^ m is at most 1 + 2 m x as long as m x is at most a half. -/
theorem pow_le_lin (x : ℚ) (hx : 0 ≤ x) :
    ∀ m : ℕ, (m : ℚ) * x ≤ 1 / 2 → (1 + x) ^ m ≤ 1 + 2 * m * x
  | 0, _ => by simp
  | m + 1, h => by
      have hm : (m : ℚ) * x ≤ 1 / 2 := by
        push_cast at h
        nlinarith
      have ih := pow_le_lin x hx m hm
      have h2 : (1 + x) ^ m * (1 + x) ≤ (1 + 2 * m * x) * (1 + x) :=
        mul_le_mul_of_nonneg_right ih (by linarith)
      have h3 : (m : ℚ) * x * x ≤ 1 / 2 * x := mul_le_mul_of_nonneg_right hm hx
      rw [pow_succ]
      push_cast
      nlinarith

/-- The planner's bound on the distance from uniform of one drawn element, at the field of the
format: the text of `capped` at p = 2 ^ 64 - 2 ^ 32 + 1 (`Fmt.Fld.two.p`: `p_two`,
OnBytes/Field/WordEq.lean) and degree 3. -/
def cappedTwo : Binary :=
  let bits := Params.bitsOf (2 ^ 64 - 2 ^ 32 + 1 - 1)
  (Bound.ofWord 3 * Bound.pow (Bound.ratio (2 ^ bits - (2 ^ 64 - 2 ^ 32 + 1)) (2 ^ bits)) 6).error

/-- That number is at least 3 * 2 ^ -193. -/
theorem cappedTwo_ge : (3 : ℚ) * (2 : ℚ) ^ (-193 : ℤ) ≤ cappedTwo.val := by
  have h : (⟨3, -193⟩ : Binary).le cappedTwo = true := by decide +kernel
  exact Binary.le_sound _ _ h

/-- `capped` at the field of the format. -/
theorem capped_two (s : Setting) (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdeg : s.degree = 3) :
    capped s = cappedTwo := by
  unfold capped cappedTwo
  rw [hp, hdeg]

/-- A round's whole error is at least its error and, if it draws elements, the unit times
drawE + drawNZ: an element other than 0 counts twice. -/
theorem whole_ge (s : Setting) (u : Binary) (r : PlanRound) :
    r.error.val + (if r.entry.drawE = 0 then 0
      else u.val * ((r.entry.drawE + r.entry.drawNZ : ℕ) : ℚ)) ≤ (wholeError s u r).val := by
  unfold wholeError
  by_cases h0 : r.entry.drawE = 0
  · simp [h0]
  · rw [if_neg h0, if_neg (by simpa using h0)]
    have a1 := Binary.val_add_up r.error (u.mul (.ofNat (r.entry.drawE + r.entry.drawNZ)) .up)
    have a2 := Binary.val_mul_up u (.ofNat (r.entry.drawE + r.entry.drawNZ))
    rw [Binary.val_ofNat] at a2
    dsimp only
    split
    · have a3 := Binary.val_add_up
        (r.error.add (u.mul (.ofNat (r.entry.drawE + r.entry.drawNZ)) .up) .up)
        (((Bound.ofWord 1 / Bound.pow (Bound.ofNat s.cardE) 2).error).mul
          (.ofNat r.entry.drawNZ) .up)
      have a4 := Binary.val_nonneg (((Bound.ofWord 1 / Bound.pow (Bound.ofNat s.cardE) 2).error).mul
          (.ofNat r.entry.drawNZ) .up)
      linarith
    · linarith

/-- The arithmetic of `held_round`, in rational numbers. c: the round's error; u: the unit; D: the
elements drawn; N: those other than 0; W: the work; T: the target. If 0 ≤ c, c + u (D + N) ≤ 2 ^ (W
- T) (c ≤ 2 ^ (W - T) where D is 0), u ≥ 3 * 2 ^ -193, and W + 66 ≤ T where D is not 0, then (1 + 2
^ -128) ^ (3 D) * c / 2 ^ W ≤ 2 ^ -T. -/
theorem held_num (c u : ℚ) (D N W T : ℕ) (hc0 : 0 ≤ c) (hu : (3 : ℚ) * (2 : ℚ) ^ (-193 : ℤ) ≤ u)
    (hw : D ≠ 0 → W + 66 ≤ T)
    (H : c + (if D = 0 then 0 else u * ((D + N : ℕ) : ℚ)) ≤ (2 : ℚ) ^ ((W : ℤ) - (T : ℤ))) :
    (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * D) * (c / 2 ^ W) ≤ (2⁻¹ : ℚ) ^ T := by
  have hW : (0 : ℚ) < 2 ^ W := by positivity
  have hsplit : (2 : ℚ) ^ ((W : ℤ) - (T : ℤ)) = 2 ^ W * (2⁻¹ : ℚ) ^ T := by
    rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]
  have key : (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * D) * c ≤ (2 : ℚ) ^ ((W : ℤ) - (T : ℤ)) := by
    by_cases h0 : D = 0
    · simpa [h0] using H
    · rw [if_neg h0] at H
      have hD : (1 : ℚ) ≤ D := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
      have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
      have hu0 : (0 : ℚ) < u := lt_of_lt_of_le (by positivity) hu
      have h66 : (2 : ℚ) ^ ((W : ℤ) - (T : ℤ)) ≤ (2 : ℚ) ^ (-66 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by have := hw h0; omega)
      push_cast at H
      have hcle : c ≤ (2 : ℚ) ^ (-66 : ℤ) := by
        nlinarith [mul_nonneg hu0.le (add_nonneg (le_trans zero_le_one hD) hN)]
      have huD : u * D ≤ (2 : ℚ) ^ (-66 : ℤ) := by nlinarith [mul_nonneg hu0.le hN]
      -- 3 D 2^-128 is at most a half
      have e1 : (2 : ℚ) ^ (-66 : ℤ) = 2 ^ (-193 : ℤ) * 2 ^ (127 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        norm_num
      have e2 : (2 : ℚ) ^ (-128 : ℤ) * 2 ^ (127 : ℤ) = 1 / 2 := by
        rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
        norm_num
      have p193 : (0 : ℚ) < 2 ^ (-193 : ℤ) := by positivity
      have p128 : (0 : ℚ) < 2 ^ (-128 : ℤ) := by positivity
      have hD3 : (3 : ℚ) * D ≤ 2 ^ (127 : ℤ) := by
        have : (3 : ℚ) * 2 ^ (-193 : ℤ) * D ≤ 2 ^ (-193 : ℤ) * 2 ^ (127 : ℤ) := by
          rw [← e1]
          exact le_trans (mul_le_mul_of_nonneg_right hu (le_trans zero_le_one hD)) huD
        nlinarith
      have hy : ((3 * D : ℕ) : ℚ) * (2 : ℚ) ^ (-128 : ℤ) ≤ 1 / 2 := by
        push_cast
        rw [← e2]
        nlinarith
      have hlin := pow_le_lin ((2 : ℚ) ^ (-128 : ℤ)) p128.le (3 * D) hy
      push_cast at hlin
      -- c ((1 + 2 ^ -128) ^ (3 D) - 1) is at most u D
      have e3 : (2 : ℚ) ^ (-66 : ℤ) * (2 * 3 * 2 ^ (-128 : ℤ)) = 3 * 2 ^ (-193 : ℤ) := by
        have : (2 : ℚ) ^ (-66 : ℤ) * 2 ^ (-128 : ℤ) * 2 = 2 ^ (-193 : ℤ) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0), ← zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
          norm_num
        linarith
      have hgain : c * (2 * (3 * D) * 2 ^ (-128 : ℤ)) ≤ u * D := by
        have s1 : c * (2 * (3 * D) * 2 ^ (-128 : ℤ)) ≤
            2 ^ (-66 : ℤ) * (2 * (3 * D) * 2 ^ (-128 : ℤ)) :=
          mul_le_mul_of_nonneg_right hcle (by positivity)
        have s2 : (2 : ℚ) ^ (-66 : ℤ) * (2 * (3 * D) * 2 ^ (-128 : ℤ)) =
            3 * 2 ^ (-193 : ℤ) * D := by
          rw [← e3]
          ring
        have s3 : (3 : ℚ) * 2 ^ (-193 : ℤ) * D ≤ u * D :=
          mul_le_mul_of_nonneg_right hu (le_trans zero_le_one hD)
        linarith
      have hmul : (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * D) * c ≤
          (1 + 2 * (3 * D) * 2 ^ (-128 : ℤ)) * c := mul_le_mul_of_nonneg_right hlin hc0
      nlinarith [mul_nonneg hu0.le hN]
  calc (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * D) * (c / 2 ^ W)
      = (1 + (2 : ℚ) ^ (-128 : ℤ)) ^ (3 * D) * c / 2 ^ W := by ring
    _ ≤ (2 ^ W * (2⁻¹ : ℚ) ^ T) / 2 ^ W := by
        rw [← hsplit]
        exact div_le_div_of_nonneg_right key hW.le
    _ = (2⁻¹ : ℚ) ^ T := by field_simp

/-- `kapSl 128` as a real number. -/
theorem kapSl_ofReal : kapSl 128 = ENNReal.ofReal (((1 + (2 : ℚ) ^ (-128 : ℤ) : ℚ)) : ℝ) := by
  unfold kapSl
  have h1 : (((1 + (2 : ℚ) ^ (-128 : ℤ) : ℚ)) : ℝ) = 1 + ((2 : ℝ) ^ 128)⁻¹ := by
    push_cast
    rw [zpow_neg]
    norm_cast
  rw [h1, ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- One round. s: the plan's setting, at the field of the format. r: a round of a plan. d: a written
round with r's entry; its kind is free. If r holds in the planner's reckoning (`roundHolds`, with
`capped s` as the unit), and `count`, as a share of the round's typed values, is at most the
planner's number for the round's error (`hc`), then `count` times the sampler's weight is at most
2 ^ -target of the round's written verifier messages. These include the strings of test bits: of
the target's bits, `work` are work. Asked besides: `logN` at most 64; no more elements other than 0
than elements; and, if the round draws an element, work + 66 ≤ target. Nothing says that a count
meets `hc`. In `hc` an element other than 0 has p ^ 3 - 1 typed values, not p ^ 3. -/
theorem held_round (s : Setting) (hp : s.p = 2 ^ 64 - 2 ^ 32 + 1) (hdeg : s.degree = 3)
    (r : PlanRound) (d : PQ.RD) (hd : d.entry = r.entry) (hlog : r.entry.logN ≤ 64)
    (hnz : r.entry.drawNZ ≤ r.entry.drawE)
    (hw : r.entry.drawE ≠ 0 → r.entry.work + 66 ≤ s.target)
    (hold : roundHolds s (capped s) r = true) (count : ℕ)
    (hc : (count : ℚ) ≤ r.error.val * (nVals (Fmt.dsOf d.entry d.kind) : ℚ)) :
    ((count * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ s.target * (Fintype.card (wRound d).Chal : ℝ≥0∞) := by
  have hc0 : 0 ≤ r.error.val := Binary.val_nonneg _
  have H := (whole_ge s (capped s) r).trans (Binary.le_sound _ _ hold)
  rw [Binary.val_twoTo] at H
  have hu : (3 : ℚ) * (2 : ℚ) ^ (-193 : ℤ) ≤ (capped s).val := by
    rw [capped_two s hp hdeg]
    exact cappedTwo_ge
  have hnum := held_num r.error.val (capped s).val r.entry.drawE r.entry.drawNZ r.entry.work
    s.target hc0 hu hw H
  have hnumR : (((1 + (2 : ℚ) ^ (-128 : ℤ) : ℚ)) : ℝ) ^ (3 * r.entry.drawE) *
      ((r.error.val : ℝ) / 2 ^ r.entry.work) ≤ (2⁻¹ : ℝ) ^ s.target := by
    have h := (Rat.cast_le (K := ℝ)).2 hnum
    simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_inv, Rat.cast_ofNat] using h
  have hcR : (count : ℝ) ≤ (r.error.val : ℝ) * (nVals (Fmt.dsOf d.entry d.kind) : ℝ) := by
    exact_mod_cast hc
  have hc0R : (0 : ℝ) ≤ (r.error.val : ℝ) := by exact_mod_cast hc0
  have hcount : (count : ℝ≥0∞) ≤ ENNReal.ofReal (r.error.val : ℝ) *
      (Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞) := by
    rw [card_vals_all, ← ENNReal.ofReal_natCast (nVals _), ← ENNReal.ofReal_mul hc0R,
      ← ENNReal.ofReal_natCast count]
    exact ENNReal.ofReal_le_ofReal hcR
  refine (below_round_div_ex d (hd ▸ hlog) count _ hcount).trans (mul_le_mul' ?_ le_rfl)
  rw [exAll_dsOf, hd, Nat.sub_add_cancel hnz, kapSl_ofReal]
  have h2 : (2 : ℝ≥0∞) ^ r.entry.work = ENNReal.ofReal ((2 : ℝ) ^ r.entry.work) := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  have h3 : (2 : ℝ≥0∞)⁻¹ ^ s.target = ENNReal.ofReal ((2⁻¹ : ℝ) ^ s.target) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  rw [h2, h3, ← ENNReal.ofReal_div_of_pos (by positivity),
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hnumR

end OnBytes.Slice

#print axioms OnBytes.Slice.cappedTwo_ge
#print axioms OnBytes.Slice.whole_ge
#print axioms OnBytes.Slice.held_num
#print axioms OnBytes.Slice.held_round
