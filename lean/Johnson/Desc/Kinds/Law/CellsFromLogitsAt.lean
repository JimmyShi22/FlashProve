--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsFromLogitsAt.lean.
WHAT IT DOES NOT SHOW. A TOY: a MADE-UP stream (feature 0 has the
value 1 at every position, all else 0), MADE-UP weights (one weight 1, at feature 0 and entry 0), a
made-up request (Law/CellsWithCostsAt.lean's: 1024 tokens 0; positions 0 to 1022 checked), the table
of two values: no stored model, no file in scope, not what the prover's program lays. The sizes and
the policy are typed in as numbers there. One logit moves, and it is the token's own: the gap stays
0, the cost 2^sh = 256 = theta = C; nothing is over; the top digit is 0. No soundness, no
probability, nothing on hiding.
WHAT IT IS. Law/CellsFromLogits.lean's premises ARE MET BY CELLS WHOSE LOGITS ARE NOT ALL 0.
  bX, wX, cX        the stream, the weights, the cells (Law/NormHonest.lean's honest cells of bX).
  x_X, v_X, sig_X, r_X, yw_X, act_X   the library's integer program on that stream, in numbers: the
                    sum of squares 1; the root 231; the reciprocal 76156649543; the rounded product
                    and the activation 71 at feature 0, else 0.
  runs_X, cellRelN_X   the program goes on; the norm's relation holds of cX.
  logit_X, gap_X, cost_X, paid_X, mar_X, digits_X   the logit of entry 0 is 71, every other 0; the
                    gap 0; the cost 256; the lifted margins 256 (at entry 0) and 327; their digits
                    1 and 0 | 71.
  admitsG_X, both_X   AdmitsG cX; BOTH RELATIONS ON CELLS HOLD WHOLE OF withHead cX: no premise.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsFromLogits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtX

open Norm (lt ls d lPd T S2)
open Inst.Model (NORM.V NORM.sig NORM.R NORM.yw NORM.out rhu clamp isqrt Fits16)

attribute [local instance] sizesX policyX requestX tokenX

/-- The stream: at every position feature 0 has the value 1 (its lowest limb is 1); else 0. -/
def bX : Nat → Nat → Nat → Int := fun _ l k => if l = 0 ∧ k = 0 then 1 else 0

/-- The head's weights: 1 at feature 0 and vocabulary entry 0; all else is 0. -/
def wX : Nat → Nat → Int := fun k v => if k = 0 ∧ v = 0 then 1 else 0

theorem x_X (t k : Nat) : xH bX t k = if k = 0 then 1 else 0 := by
  unfold xH Inst.Model.Ledger.xOf bX
  by_cases h : k = 0 <;> simp [Finset.sum_range_succ, h]

theorem v_X (t : Nat) : NORM.V d (xH bX t) = 1 := by
  unfold NORM.V
  rw [Finset.sum_eq_single 0]
  · rw [x_X]
    simp
  · intro j _ hj
    rw [x_X, if_neg hj]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by decide : 0 < d)) h

theorem sig_X (t : Nat) : NORM.sig npOf d (xH bX t) = 231 := by
  unfold NORM.sig isqrt
  rw [v_X]
  show ((Nat.sqrt ((1 : Int) + 53687).toNat : Nat) : Int) = 231
  have e : ((1 : Int) + 53687).toNat = 53688 := rfl
  have e2 : 231 = Nat.sqrt 53688 := Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩
  rw [e, ← e2]
  rfl

theorem r_X (t : Nat) : NORM.R npOf d (xH bX t) = 76156649543 := by
  unfold NORM.R
  rw [sig_X]
  show ((2 : Int) ^ 44 + 231 / 2) / 231 = 76156649543
  norm_num

theorem yw_X (t k : Nat) : awH bX t k = if k = 0 then 71 else 0 := by
  unfold awH NORM.yw rhu
  rw [r_X, x_X]
  show ((if k = 0 then (1 : Int) else 0) * 76156649543 + 2 ^ (30 - 1)) / 2 ^ 30 = _
  by_cases h : k = 0
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

theorem act_X (t k : Nat) : actH bX t k = if k = 0 then 71 else 0 := by
  have e : actH bX t k = clamp 2047 (awH bX t k) := rfl
  rw [e, yw_X]
  unfold clamp
  by_cases h : k = 0
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

theorem runs_X : RunsN bX := by
  refine ⟨fun t _ => ⟨by decide, by decide, by decide, by decide, fun l _ j _ => ?_, ?_⟩,
    fun t _ k _ => ?_⟩
  · unfold bX
    split <;> norm_num
  · have e : NORM.V d (Inst.Model.Ledger.xOf (bX t)) = 1 := v_X t
    rw [e]
    show (1 : Int) + 53687 < 2 ^ 78
    norm_num
  · rw [yw_X]
    unfold Fits16
    split <;> norm_num

/-- The cells: the honest cells of that stream (Law/NormHonest.lean: honestN), with the weights. -/
def cX : NCells := { honestN bX with Wh := wX }

theorem cellRelN_X : CellRelN cX := by
  have h := honest_meets (planN plan_X) runs_X
  exact ⟨h.small, h.smallS, h.rows, h.remLow, h.remHigh, h.clamp, h.digits⟩

theorem act_cX {t k : Nat} (ht : t < T) (hk : k < d) :
    act cX.toCells t k = if k = 0 then 71 else 0 := by
  have e : act cX.toCells t k = act (honestN bX).toCells t k := rfl
  rw [e, act_honest ht hk, act_X]

/-- **The logit of entry 0 is 71; every other logit is 0.** -/
theorem logit_X {t : Nat} (ht : t < T) (v : Nat) :
    logit cX.toCells t v = if v = 0 then 71 else 0 := by
  unfold logit
  rw [sumZ_eq, Finset.sum_eq_single 0]
  · rw [act_cX ht (by decide), if_pos rfl]
    show (71 : Int) * (if (0 : Nat) = 0 ∧ v = 0 then 1 else 0) = _
    by_cases h : v = 0 <;> simp [h]
  · intro k _ hk
    show _ * (if k = 0 ∧ v = 0 then (1 : Int) else 0) = 0
    rw [if_neg (fun h => hk h.1), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by decide : 0 < d)) h

theorem foldl_max_le (f : Nat → Int) (B : Int) : ∀ (l : List Nat) (a : Int), a ≤ B →
    (∀ v ∈ l, f v ≤ B) → l.foldl (fun m v => max m (f v)) a ≤ B
  | [], _, ha, _ => ha
  | w :: l, a, ha, hf =>
    foldl_max_le f B l (max a (f w)) (max_le ha (hf w (by simp))) fun v hv => hf v (by simp [hv])

theorem gap_X {t : Nat} (ht : t < T) : gap cX.toCells t = 0 := by
  refine le_antisymm ?_ (gap_nonneg _ _)
  unfold gap
  refine foldl_max_le _ 0 _ 0 (le_refl _) fun v _ => ?_
  rw [logit_X ht, logit_X ht, win_X, if_pos rfl, if_neg (Nat.not_lt_zero v)]
  split <;> norm_num

theorem cost_X {t : Nat} (ht : t < T) : cost cX.toCells t = 256 := by
  unfold cost
  rw [gap_X ht]
  rfl

theorem checked_X {t : Nat} (h : checked t = true) : t < 1023 := by
  unfold checked at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem paid_X {t : Nat} (ht : t < 1023) : paidG cX t = 256 := by
  unfold paidG
  rw [if_pos (costed_X ht), cost_X (show t < 2 ^ 10 by omega)]
  rfl

/-- **The lifted margins: 256 at the token's own entry, 327 at every other.** -/
theorem mar_X {t x : Nat} (ht : t < 1023) (hx : x < V) :
    marG cX x t = if x = 0 then 256 else 327 := by
  have hc := costed_X ht
  have h3 := checked_of_costed hc
  have hT : t < T := show t < 2 ^ 10 by omega
  have hn : ¬ (checked t = true ∧ x < 0) := fun h => Nat.not_lt_zero x h.2
  have h00 : (0 : Nat) = 0 := rfl
  unfold marG
  rw [if_pos ⟨hx, h3⟩, if_pos ⟨hx, hc⟩, paid_X ht, logit_X hT, logit_X hT, win_X, if_neg hn,
    if_pos h00]
  split <;> norm_num

theorem admitsG_X : AdmitsG cX := by
  refine ⟨fun t x hx hc => ?_, fun t hc => ?_, by decide⟩
  · rw [mar_X (checked_X hc) hx]
    show _ ∧ _ < (2 : Int) ^ (8 + 16)
    split <;> norm_num
  · rw [paid_X (checked_X (checked_of_costed hc))]
    decide

/-- The two digits of a lifted margin: the middle one is 1; the low one 0 at the token's own entry,
71 at every other. -/
theorem digits_X {t x : Nat} (ht : t < 1023) (hx : x < V) :
    midN cX x t = 1 ∧ lowN cX x t = if x = 0 then 0 else 71 := by
  unfold midN lowN
  rw [mar_X ht hx]
  show _ / (2 : Int) ^ 8 = 1 ∧ _ % (2 : Int) ^ 8 = _
  split <;> norm_num

/-- **BOTH RELATIONS ON CELLS, WHOLE, OF CELLS WHOSE LOGITS ARE NOT ALL 0: NO PREMISE IS LEFT.** -/
theorem both_X :
    CellRelN (withHead cX) ∧ CellRel (withHead cX).toCells stepTab ∧ TableOk stepTab ∧
      (dataOf (withHead cX)).Holds ∧ (withHead cX).Wh = wX ∧
      (∀ t, t < T → ∀ v, logit (withHead cX).toCells t v = if v = 0 then 71 else 0) ∧
      (∀ t, t < 1023 → numZ (withHead cX).toCells .paid t = cost (withHead cX).toCells t ∧
        cost (withHead cX).toCells t = 256) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    both_withHead plan_X request_X token_X admitsG_X cellRelN_X
  exact ⟨a1, a2, a3, a4, a5, fun t ht v => by rw [a6, logit_X ht], fun t ht =>
    ⟨a7 t (costed_X ht), by rw [cost_withHead, cost_X (show t < 2 ^ 10 by omega)]⟩⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtX
