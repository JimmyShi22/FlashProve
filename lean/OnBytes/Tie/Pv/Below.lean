-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Below.lean: if the rounds of a reduction are covered by the rounds of a plan, every
error of the reduction, as a probability, is at most what bounds the plan's errors.

The proof library asks of a list of errors that each, as a share of the values of its round's
verifier's message, is at most one number (`Err.Below`, Iop/InteractiveOracleProof.lean), or at most that number
times 2 to the round's bits of work (`Err.BelowG`, Iop/Grind.lean). A tie to the planner says that
each share is at most the error that a plan holds for a round (`Covered`,
OnBytes/Tie/Pv/PortKit.lean). This file puts the two together. Statements with their proofs.
Main names:
  `heldError σ c y`, `heldWork σ c y`: the error and the bits of work that a plan holds for the
    planned round y.
  `row_of_covered`, `rowG_of_covered`: one round.
  `below_of_covered`: rounds covered one by one, and every held error at most c: `Err.Below` at c.
  `bitsList g`: the bits of work of a list, round by round.
  `belowG_of_covered`: rounds covered one by one, the bits of work those that the plan holds, and
    every held error at most c * 2 ^ work: `Err.BelowG` at c.
  `le_wholeError`, `roundHolds_sound`, `held_of_holds`: a round that holds in the planner's
    reckoning has an error of at most 2 ^ work / 2 ^ target.
  `belowG_of_plan`: rounds covered one by one by the list of a finished plan (`PlanIs`,
    OnBytes/Params/PlanListsChains.lean), with that plan's bits of work: `Err.BelowG` at
    1 / 2 ^ target.
Limits: a maximum over the rounds; no sum. That the rounds of a given reduction are covered is a
premise. That work is worth its bits is not said here: `Err.BelowG` is a statement on numbers. The
planner's addition for the distance from uniform of its draws is dropped.

See also: OnBytes/Params/HoldsLaws.lean states `le_wholeError` and `roundHolds_sound` in the same
words. They are stated again here so that this file imports nothing beyond the files named below.
-/
import OnBytes.Tie.Pv.PortKit
import OnBytes.Params.PlanListsChains
import Iop.Grind
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv
open OnBytes OnBytes.Params Iop
open scoped ENNReal

/-- The error that a plan holds for a planned round, as a real number. -/
def heldError (σ : Setting) (c : Scope) (y : RoundSpec) : ℝ :=
  (((y.round σ c).error.val : ℚ) : ℝ)

/-- The bits of work that a plan holds for a planned round. -/
def heldWork (σ : Setting) (c : Scope) (y : RoundSpec) : ℕ := (y.round σ c).entry.work

theorem heldError_nonneg (σ : Setting) (c : Scope) (y : RoundSpec) : 0 ≤ heldError σ c y := by
  unfold heldError
  exact_mod_cast Binary.val_nonneg _

section
variable {σ : Setting} {sc : Scope}

/-- One round. -/
theorem row_of_covered {cn : ℕ × ℕ} {y : RoundSpec} {c : ℝ} (h : Covered σ sc cn y)
    (hy : heldError σ sc y ≤ c) (hn : 0 < cn.2) :
    (cn.1 : ℝ≥0∞) ≤ ENNReal.ofReal c * (cn.2 : ℝ≥0∞) := by
  have hn' : (0 : ℝ) < (cn.2 : ℝ) := by exact_mod_cast hn
  have hc : 0 ≤ c := le_trans (heldError_nonneg σ sc y) hy
  have h0 : (cn.1 : ℝ) / (cn.2 : ℝ) ≤ heldError σ sc y := h
  have h1 : (cn.1 : ℝ) ≤ c * (cn.2 : ℝ) := (div_le_iff₀ hn').1 (le_trans h0 hy)
  rw [← ENNReal.ofReal_natCast cn.1, ← ENNReal.ofReal_natCast cn.2, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h1

/-- One round with b bits of work. -/
theorem rowG_of_covered {cn : ℕ × ℕ} {y : RoundSpec} {c : ℝ} {b : ℕ} (h : Covered σ sc cn y)
    (hy : heldError σ sc y ≤ c * 2 ^ b) (hc : 0 ≤ c) (hn : 0 < cn.2) :
    (cn.1 : ℝ≥0∞) ≤ ENNReal.ofReal c * ((2 : ℝ≥0∞) ^ b * (cn.2 : ℝ≥0∞)) := by
  have h1 := row_of_covered h hy hn
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
    mul_assoc] at h1
  exact h1

end

/-- Rounds covered one by one, and every held error at most c. -/
theorem below_of_covered (σ : Setting) (sc : Scope) (c : ℝ) :
    ∀ (s : Shape) (ε : Err s) (ys : List RoundSpec),
      List.Forall₂ (Covered σ sc) (ε.toList.zip s.chalList) ys →
      (∀ y ∈ ys, heldError σ sc y ≤ c) → Err.Below ε (ENNReal.ofReal c)
  | [], _, _, _, _ => trivial
  | r :: s, (e, ε), _, h, hy => by
      have h' : List.Forall₂ (Covered σ sc)
          ((e, Fintype.card r.Chal) :: ε.toList.zip (Shape.chalList s)) _ := h
      cases h' with
      | cons h1 h2 =>
        exact ⟨row_of_covered h1 (hy _ List.mem_cons_self) Fintype.card_pos,
          below_of_covered σ sc c s ε _ h2 fun y hm => hy y (List.mem_cons_of_mem _ hm)⟩

/-- The bits of work, round by round. -/
def bitsList : {s : Shape} → GBits s → List ℕ
  | [], _ => []
  | _ :: _, (b, g) => b :: bitsList g

/-- Rounds covered one by one, with the bits of work that the plan holds. -/
theorem belowG_of_covered (σ : Setting) (sc : Scope) (c : ℝ) (hc : 0 ≤ c) :
    ∀ (s : Shape) (g : GBits s) (ε : Err s) (ys : List RoundSpec),
      List.Forall₂ (Covered σ sc) (ε.toList.zip s.chalList) ys →
      bitsList g = ys.map (heldWork σ sc) →
      (∀ y ∈ ys, heldError σ sc y ≤ c * 2 ^ heldWork σ sc y) →
      Err.BelowG g ε (ENNReal.ofReal c)
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (b, g), (e, ε), _, h, hg, hy => by
      have h' : List.Forall₂ (Covered σ sc)
          ((e, Fintype.card r.Chal) :: ε.toList.zip (Shape.chalList s)) _ := h
      cases h' with
      | cons h1 h2 =>
        simp only [bitsList, List.map_cons, List.cons.injEq] at hg
        obtain ⟨rfl, hg2⟩ := hg
        exact ⟨rowG_of_covered h1 (hy _ List.mem_cons_self) hc Fintype.card_pos,
          belowG_of_covered σ sc c hc s g ε _ h2 hg2
            fun y hm => hy y (List.mem_cons_of_mem _ hm)⟩

/-! ### a plan that holds -/

/-- A round's own error is at most the error with the distance from uniform of its draws. -/
theorem le_wholeError (s : Setting) (unit : Binary) (r : PlanRound) :
    r.error.val ≤ (wholeError s unit r).val := by
  unfold wholeError
  split
  · exact le_rfl
  · have h1 : r.error.val ≤
        (r.error.add (unit.mul (.ofNat (r.entry.drawE + r.entry.drawNZ)) .up) .up).val :=
      le_trans (le_add_of_nonneg_right (Binary.val_nonneg _)) (Binary.val_add_up _ _)
    dsimp only
    split
    · exact le_trans h1
        (le_trans (le_add_of_nonneg_right (Binary.val_nonneg _)) (Binary.val_add_up _ _))
    · exact h1

/-- A round that holds has an error of at most 2 ^ (work - target). -/
theorem roundHolds_sound {s : Setting} {unit : Binary} {r : PlanRound}
    (h : roundHolds s unit r = true) :
    r.error.val ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ)) := by
  have h1 := Binary.le_sound _ _ h
  rw [Binary.val_twoTo] at h1
  exact (le_wholeError s unit r).trans h1

/-- The same of a planned round, in real numbers. -/
theorem held_of_holds {σ : Setting} {sc : Scope} {unit : Binary} {y : RoundSpec}
    (h : roundHolds σ unit (y.round σ sc) = true) :
    heldError σ sc y ≤ ((2 : ℝ) ^ σ.target)⁻¹ * 2 ^ heldWork σ sc y := by
  have h1 : heldError σ sc y ≤ (2 : ℝ) ^ ((heldWork σ sc y : ℤ) - (σ.target : ℤ)) := by
    have h0 : (((y.round σ sc).error.val : ℚ) : ℝ) ≤
        (((2 : ℚ) ^ (((y.round σ sc).entry.work : ℤ) - (σ.target : ℤ)) : ℚ) : ℝ) :=
      Rat.cast_le.2 (roundHolds_sound h)
    rw [Rat.cast_zpow, Rat.cast_ofNat] at h0
    exact h0
  rw [zpow_sub₀ (two_ne_zero), zpow_natCast, zpow_natCast, div_eq_mul_inv, mul_comm] at h1
  exact h1

/-- Rounds covered one by one by the list of a finished plan, with that plan's bits of work. -/
theorem belowG_of_plan {P : Planned} {σ : Setting} {sc : Scope} {ys : List RoundSpec}
    (hP : PlanIs P σ sc ys) (s : Shape) (g : GBits s) (ε : Err s)
    (h : List.Forall₂ (Covered σ sc) (ε.toList.zip s.chalList) ys)
    (hg : bitsList g = ys.map (heldWork σ sc)) :
    Err.BelowG g ε (ENNReal.ofReal ((2 : ℝ) ^ σ.target)⁻¹) :=
  belowG_of_covered σ sc _ (by positivity) s g ε ys h hg fun y hy => held_of_holds (hP.holds y hy)

end Cb.Pv

#print axioms Cb.Pv.below_of_covered
#print axioms Cb.Pv.belowG_of_covered
#print axioms Cb.Pv.belowG_of_plan
