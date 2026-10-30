-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/World.lean: THE HEAD's FORMS IN CLOSED FORM, IN ANY WORLD (for the glue of K06_law).
Closed.lean and General.lean give each form's value in the world 0 where the classes are FILLED WITH
CONSTANT FORMS (`Filled`: equalities of forms). Here the same closed forms are proved for the value
in ANY world W (`vW W`, Ends.lean) under `FilledW W c`: the reads' entries and the claimed sum have
their true VALUES in W. THE FOURTEEN THEOREMS BELOW THE LINE ARE THOSE FILES' OWN PROOFS, RE-TYPED BY A
PROGRAM under a fixed list of turns (cv ↦ vW W; Filled ↦ FilledW W; «hentry, cv_coe» ↦ «hentry»); Lean
has checked each.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)

/-! ## The signs that Ends.lean has not yet -/

theorem vW_ofConst (W : World K) (x : E) : vW W (Aff.ofConst x) = rd x := Aff.value_ofConst _ _ x
theorem vW_natCast (W : World K) (n : Nat) : vW W ((n : Nat) : Form) = (n : K) := by
  show vW W (Aff.ofConst (natE n)) = _
  rw [vW_ofConst, rd_natE]
theorem vW_addE (W : World K) (f : Form) (x : E) :
    vW W (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) = vW W f + rd x := by
  show vW W (f + Aff.ofConst x) = _
  rw [vW_add, vW_ofConst]
theorem vW_Eadd (W : World K) (x : E) (f : Form) :
    vW W (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) = rd x + vW W f := by
  show vW W (Aff.ofConst x + f) = _
  rw [vW_add, vW_ofConst]
theorem vW_subE (W : World K) (f : Form) (x : E) :
    vW W (HSub.hSub (α := Form) (β := E) (γ := Form) f x) = vW W f - rd x := by
  show vW W (f - Aff.ofConst x) = _
  rw [vW_sub, vW_ofConst]
theorem vW_addN (W : World K) (f : Form) (n : Nat) :
    vW W (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) = vW W f + (n : K) := by
  show vW W (f + Aff.ofConst (natE n)) = _
  rw [vW_add, vW_ofConst, rd_natE]
theorem vW_subN (W : World K) (f : Form) (n : Nat) :
    vW W (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) = vW W f - (n : K) := by
  show vW W (f - Aff.ofConst (natE n)) = _
  rw [vW_sub, vW_ofConst, rd_natE]

variable [Sizes] [Policy] [Request] [Token]

section Filled
variable [FinalNorm.In] [In] [Heard] [Reads]

/-- In the world W the reads' entries and the claimed sum have their true values; the letters that
come in are the weights that they are taken for. -/
structure FilledW (W : World K) (c : Cells) : Prop where
  hentry : ∀ r i, vW W (entry r i) = rd (readAt c r.of i)
  hclaimed : vW W logits.claimed.var = rd (invE (2 ^ lPd) * trueSum c)
  hin : FilledIn

variable {W : World K} {c : Cells}

/-! ## ———— re-typed by a program from Closed.lean and General.lean ———— -/

/-- A number under the weights of the positions with a cost. -/
theorem vW_atCosts (hF : FilledW W c) (n : Number) :
    vW W (atCosts n) = (Finset.range T).sum fun t => Ph t * ((numZ c n t : Int) : K) := by
  unfold atCosts
  rw [vW_sumTo]
  have h1 : ∀ l, vW W ((256 : Nat) ^ l • (entry Read.rowAtCosts (NR + n.digits.1 + l) + off1 * ERC))
      = (Finset.range T).sum fun t =>
          Ph t * ((256 : K) ^ l * (((c.cell .row (NR + n.digits.1 + l) t : Int) : K) + 128)) := by
    intro l
    rw [vW_smulN, vW_addE, rd_nmul, hF.hentry, rd_ERC]
    show _ * (rd (readAt c (.row, .short phiC) _) + _) = _
    rw [rd_readAt_short, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_phiC]
    unfold off1
    push_cast
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  unfold numZ
  push_cast
  rfl

/-- A number, summed plainly over the positions with a cost. -/
theorem vW_summed (hF : FilledW W c) (n : Number) :
    vW W (summed n) = (Finset.range T).sum fun t =>
      if costed t = true then ((numZ c n t : Int) : K) else 0 := by
  unfold summed
  rw [vW_sumTo]
  have h1 : ∀ l, vW W ((256 : Nat) ^ l • (entry Read.rowCount (NR + n.digits.1 + l) + off1 * RC))
      = (Finset.range T).sum fun t => if costed t = true then
          ((256 : K) ^ l * (((c.cell .row (NR + n.digits.1 + l) t : Int) : K) + 128)) else 0 := by
    intro l
    rw [vW_smulN, vW_addN, hF.hentry]
    show _ * (rd (readAt c (.row, .short fun t => if costed t then 1 else 0) _) + _) = _
    rw [rd_readAt_short]
    push_cast
    rw [RC_eq, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold off1
    by_cases hc : costed t = true
    · simp only [hc, if_true, rd_one]; push_cast; ring
    · simp only [hc, if_false, rd_zero, Bool.false_eq_true]; ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : costed t = true
  · simp only [hc, if_true]
    unfold numZ
    push_cast
    rfl
  · simp [hc]

theorem wx_liftW (hF : FilledW W c) :
    rd (wx .marginTop) * (vW W (atCosts .paid) + (BIG : K) * vW W (atCosts .over))
      = (Finset.range JV).sum fun x => (Finset.range T).sum fun t => Ut .marginTop x * Wt t *
        (((if x < V ∧ costed t = true then liftZ c t else 0 : Int)) : K) := by
  have hlen : len Key.marginTop = JV := rfl
  rw [rd_wx hF.hin, vW_atCosts hF, vW_atCosts hF, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_mul_sum, hlen]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [first, Nat.zero_add]
  unfold Ph liftZ
  by_cases hx : x < V <;> by_cases hc : costed t = true <;> simp [hx, hc]
  ring

theorem vW_clip (hF : FilledW W c) : vW W clip = (Finset.range T).sum fun t =>
    Ph t * ((numZ c .paid t + numZ c .slackClip t - (C : Int) : Int) : K) := by
  unfold clip
  rw [vW_subE, vW_add, rd_nmul, vW_atCosts hF, vW_atCosts hF, rd_ERC, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  ring

theorem vW_mean (hF : FilledW W c) : vW W mean = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t
    else 0) - (theta : Int) * (RC : Int) : Int) : K) := by
  unfold mean
  rw [vW_subN, vW_add, vW_add, vW_smulN, vW_summed hF, vW_summed hF, vW_summed hF, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem vW_count (hF : FilledW W c) : vW W count = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .over t + numZ c .slackCap t else 0)
      - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) := by
  unfold count
  rw [vW_sub, vW_add, vW_natCast, vW_summed hF, vW_summed hF, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem vW_wideAtG (hF : FilledW W c) (k : Key) (f0 nl stride : Nat) :
    vW W (wideAt k f0 nl stride) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * wideG c k f0 nl stride x t := by
  have hle : len k / S2 * S2 ≤ len k := Nat.div_mul_le_self _ _
  have hR : ((Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * wideG c k f0 nl stride x t)
      = (Finset.range (len k / S2 * S2)).sum fun x => (Finset.range T).sum fun t =>
        Ut k x * Wt t * (Finset.range nl).sum fun l =>
          (256 : K) ^ l * ((c.cell .wide (S2 * ((f0 + l * stride) / S2) + x) t : Int) : K) := by
    rw [← sum_range_ite_lt hle]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold wideG
    split
    · rfl
    · simp
  rw [hR, ← sum_blocks S2 _ (len k / S2)]
  unfold wideAt
  rw [vW_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [vW_sumTo]
  have h1 : ∀ l ∈ Finset.range nl,
      vW W (((256 : E) ^ l * ewh k i) • entry Read.wideAtKeys ((f0 + l * stride) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
          Ut k (S2 * i + j) * Wt t * ((256 : K) ^ l *
            ((c.cell .wide (S2 * ((f0 + l * stride) / S2) + (S2 * i + j)) t : Int) : K)) := by
    intro l _
    rw [vW_smulE, rd_mul, rd_pow, rd_ofNat, hF.hentry]
    show _ * rd (readAt c (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) _) = _
    rw [rd_readAt_long, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hidx : S2 * ((f0 + l * stride) / S2 + i) + j
        = S2 * ((f0 + l * stride) / S2) + (S2 * i + j) := by
      rw [Nat.mul_add]; omega
    rw [hidx, Ut_block hF.hin k i j (Finset.mem_range.mp hj)
      (block_lt (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))]
    unfold Wt
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

theorem vW_midG (hF : FilledW W c) (k : Key) (v0 : Nat) :
    vW W (mid k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * midG c k v0 x t := by
  unfold mid
  rw [vW_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON, vW_wideAtG hF, mul_assoc,
    Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold midG
  by_cases h1 : first k + x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

theorem vW_lowG (hF : FilledW W c) (k : Key) :
    vW W (low k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * lowG c k x t := by
  unfold low
  rw [vW_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON, vW_wideAtG hF, mul_assoc,
    Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold lowG
  by_cases h1 : first k + x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

theorem vW_tableValueG (hF : FilledW W c) (hzt : (FinalNorm.zt).size = lt) (k : Key) (v0 : Nat) :
    vW W (tableValue k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * tvG c k v0 x t := by
  unfold tableValue
  rw [vW_Eadd, rd_nmul, rd_wsum hF.hin, vW_wideAtG hF, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (offE : K) * Ut k x = (Finset.range T).sum fun t => Ut k x * Wt t * (offE : K) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_Wt hzt]; ring
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tvG
  ring

theorem vW_topG (hF : FilledW W c) (hreq : Request.ok = true) (hy : y < V) :
    vW W top = (Finset.range JV).sum fun x => (Finset.range T).sum fun t =>
      Ut .marginTop x * Wt t * (((2 : K) ^ (sh + 15))⁻¹ * topG c x t) := by
  have hlen : len Key.marginTop = JV := rfl
  have hsplit : ∀ x t, Ut .marginTop x * Wt t * (((2 : K) ^ (sh + 15))⁻¹ * topG c x t)
      = ((2 : K) ^ (sh + 15))⁻¹ * (Ut .marginTop x * Wt t *
          (((if x < V ∧ checked t = true then logit c t (win t) - logit c t x else 0 : Int)) : K)
        + Ut .marginTop x * Wt t * (((if x < V ∧ costed t = true then liftZ c t else 0 : Int)) : K)
        - Ut .marginTop x * Wt t * (((if checked t = true ∧ x < win t then 1 else 0 : Int)) : K)
        - (2 : K) ^ sh * (Ut .marginTop x * Wt t * midG c .marginTop 0 x t)
        - Ut .marginTop x * Wt t * lowG c .marginTop x t) := by
    intro x t
    unfold topG
    ring
  simp only [hsplit, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← rd_trueSum hF.hin, ← wx_liftW hF, ← rd_ties hF.hin hreq hy, ← hlen, ← vW_midG hF .marginTop 0,
    ← vW_lowG hF .marginTop]
  simp only [top, vW_smulE, vW_sub, vW_add, vW_smulN, vW_ofConst, hF.hclaimed, rd_mul,
    rd_inv, rd_pow]
  have h2 : ((2 : K) ^ lPd) ≠ 0 := two_pow_ne_zero _
  have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
  push_cast
  rw [hr2, mul_inv_cancel_left₀ h2]

/-- **Every key, at any filled classes.** -/
theorem vW_keyG (hF : FilledW W c) (hzt : (FinalNorm.zt).size = lt) (hreq : Request.ok = true)
    (hy : y < V) (k : Key) :
    vW W (key k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * keyG c k x t := by
  cases k
  · exact vW_topG hF hreq hy
  · exact vW_midG hF .marginMid 0
  · exact vW_lowG hF .marginLow
  · show vW W (mid Key.tableA 0 + (2 ^ 16 : Nat) • tableValue Key.tableA 0) = _
    rw [vW_add, vW_smulN, vW_midG hF, vW_tableValueG hF hzt, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [keyG]
    push_cast
    ring
  · show vW W (mid Key.tableB JVa + (2 ^ 16 : Nat) • tableValue Key.tableB JVa) = _
    rw [vW_add, vW_smulN, vW_midG hF, vW_tableValueG hF hzt, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [keyG]
    push_cast
    ring

theorem vW_tableValuesAtCostsG (hF : FilledW W c) :
    vW W tableValuesAtCosts = (Finset.range T).sum fun t => Ph t * tvSumG c t := by
  have h1 : ∀ l, vW W (sumTo (JV / S2) fun i =>
      (256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
      = (Finset.range T).sum fun t => Ph t * (Finset.range JV).sum fun x => (256 : K) ^ l *
          ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + x) t : Int) : K) := by
    intro l
    rw [vW_sumTo]
    have h2 : ∀ i, vW W ((256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t => Ph t * ((256 : K) ^ l *
            ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + (S2 * i + j)) t : Int) : K)) := by
      intro i
      rw [vW_smulN, hF.hentry]
      show _ * rd (readAt c (.wide, .long (fun _ => 1) phiC) _) = _
      rw [rd_readAt_long, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hidx : S2 * ((4 * d + (3 + l) * JV) / S2 + i) + j
          = S2 * ((4 * d + (3 + l) * JV) / S2) + (S2 * i + j) := by
        rw [Nat.mul_add]; omega
      rw [hidx, rd_one, rd_phiC]
      push_cast
      ring
    simp only [h2]
    rw [sum_blocks S2 (fun x => (Finset.range T).sum fun t => Ph t * ((256 : K) ^ l *
      ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + x) t : Int) : K))) (JV / S2),
      Nat.div_mul_cancel S2_dvd_JV, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
  unfold tableValuesAtCosts
  rw [vW_Eadd, rd_nmul, rd_ERC, vW_sumTo]
  simp only [h1]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  unfold tvSumG
  push_cast
  ring

theorem vW_tableG (hF : FilledW W c) :
    vW W table = (Finset.range T).sum fun t => Ph t * tableG c t := by
  unfold table
  rw [vW_subE, vW_add, rd_nmul, vW_atCosts hF, vW_tableValuesAtCostsG hF, rd_ERC, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tableG
  push_cast
  ring

end Filled

end VerifiableInference.Desc.Kinds.Head.Law
