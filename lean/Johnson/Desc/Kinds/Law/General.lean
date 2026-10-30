-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/General.lean: THE HEAD's FORMS IN CLOSED FORM WITHOUT THE TESTS ON THE PLAN, for
Lemma 2a, which has none among its premises. Where S2 does not divide d or JVa, `wideAt` reads the
cell at S2 * (f / S2) + x in the place of f + x, and whole blocks alone: `wideG` says just that. Each
key's value at any filled classes is the sum over entries x and positions t of (the entry's weight)
(the position's weight) (`keyG c k x t`), AND keyG DOES NOT DEPEND ON THE POINT.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Values

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- What `wideAt` holds at entry x and position t. -/
def wideG (c : Cells) (k : Key) (f0 nl stride x t : Nat) : K :=
  if x < len k / S2 * S2 then (Finset.range nl).sum fun l =>
    (256 : K) ^ l * ((c.cell .wide (S2 * ((f0 + l * stride) / S2) + x) t : Int) : K)
  else 0

def midG (c : Cells) (k : Key) (v0 x t : Nat) : K :=
  (if first k + x < V ∧ checked t = true then (off2 : K) else 0) + wideG c k (4 * d + v0) 2 JV x t

def lowG (c : Cells) (k : Key) (x t : Nat) : K :=
  (if first k + x < V ∧ checked t = true then (off1 : K) else 0)
    + wideG c k (4 * d + 2 * JV) 1 JV x t

def tvG (c : Cells) (k : Key) (v0 x t : Nat) : K :=
  (offE : K) + wideG c k (4 * d + 3 * JV + v0) 3 JV x t

def topG (c : Cells) (x t : Nat) : K :=
  (((if x < V ∧ checked t = true then logit c t (win t) - logit c t x else 0 : Int)) : K)
    + (((if x < V ∧ costed t = true then liftZ c t else 0 : Int)) : K)
    - (((if checked t = true ∧ x < win t then 1 else 0 : Int)) : K)
    - (2 : K) ^ sh * midG c .marginTop 0 x t - lowG c .marginTop x t

/-- A key at entry x and position t. -/
def keyG (c : Cells) : Key → Nat → Nat → K
  | .marginTop, x, t => ((2 : K) ^ (sh + 15))⁻¹ * topG c x t
  | .marginMid, x, t => midG c .marginMid 0 x t
  | .marginLow, x, t => lowG c .marginLow x t
  | .tableA, x, t => midG c .tableA 0 x t + (2 : K) ^ 16 * tvG c .tableA 0 x t
  | .tableB, x, t => midG c .tableB JVa x t + (2 : K) ^ 16 * tvG c .tableB JVa x t

/-- The table values of a position, as `tableValuesAtCosts` sums them. -/
def tvSumG (c : Cells) (t : Nat) : K :=
  (offE : K) * (JV : K) + (Finset.range 3).sum fun l => (Finset.range JV).sum fun x =>
    (256 : K) ^ l * ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + x) t : Int) : K)

def clipG (c : Cells) (t : Nat) : K :=
  ((numZ c .paid t + numZ c .slackClip t - (C : Int) : Int) : K)

def tableG (c : Cells) (t : Nat) : K :=
  ((numZ c .slackTable t : Int) : K) + tvSumG c t - ((JV - V + 1 : Nat) : K) * (2 : K) ^ F

section Filled
variable [FinalNorm.In] [In] [Heard] [Reads] {c : Cells}

theorem cv_wideAtG (hF : Filled c) (k : Key) (f0 nl stride : Nat) :
    cv (wideAt k f0 nl stride) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
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
  rw [cv_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cv_sumTo]
  have h1 : ∀ l ∈ Finset.range nl,
      cv (((256 : E) ^ l * ewh k i) • entry Read.wideAtKeys ((f0 + l * stride) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
          Ut k (S2 * i + j) * Wt t * ((256 : K) ^ l *
            ((c.cell .wide (S2 * ((f0 + l * stride) / S2) + (S2 * i + j)) t : Int) : K)) := by
    intro l _
    rw [cv_smulE, rd_mul, rd_pow, rd_ofNat, hF.hentry, cv_coe]
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

theorem cv_midG (hF : Filled c) (k : Key) (v0 : Nat) :
    cv (mid k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * midG c k v0 x t := by
  unfold mid
  rw [cv_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON, cv_wideAtG hF, mul_assoc,
    Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold midG
  by_cases h1 : first k + x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

theorem cv_lowG (hF : Filled c) (k : Key) :
    cv (low k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * lowG c k x t := by
  unfold low
  rw [cv_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON, cv_wideAtG hF, mul_assoc,
    Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold lowG
  by_cases h1 : first k + x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

theorem cv_tableValueG (hF : Filled c) (hzt : (FinalNorm.zt).size = lt) (k : Key) (v0 : Nat) :
    cv (tableValue k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * tvG c k v0 x t := by
  unfold tableValue
  rw [cv_Eadd, rd_nmul, rd_wsum hF.hin, cv_wideAtG hF, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (offE : K) * Ut k x = (Finset.range T).sum fun t => Ut k x * Wt t * (offE : K) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_Wt hzt]; ring
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tvG
  ring

theorem cv_topG (hF : Filled c) (hreq : Request.ok = true) (hy : y < V) :
    cv top = (Finset.range JV).sum fun x => (Finset.range T).sum fun t =>
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
  rw [← rd_trueSum hF.hin, ← wx_lift hF, ← rd_ties hF.hin hreq hy, ← hlen, ← cv_midG hF .marginTop 0,
    ← cv_lowG hF .marginTop]
  simp only [top, cv_smulE, cv_sub, cv_add, cv_smulN, cv_ofConst, hF.hclaimed, rd_mul,
    rd_inv, rd_pow]
  have h2 : ((2 : K) ^ lPd) ≠ 0 := two_pow_ne_zero _
  have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
  push_cast
  rw [hr2, mul_inv_cancel_left₀ h2]

/-- **Every key, at any filled classes.** -/
theorem cv_keyG (hF : Filled c) (hzt : (FinalNorm.zt).size = lt) (hreq : Request.ok = true)
    (hy : y < V) (k : Key) :
    cv (key k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * keyG c k x t := by
  cases k
  · exact cv_topG hF hreq hy
  · exact cv_midG hF .marginMid 0
  · exact cv_lowG hF .marginLow
  · show cv (mid Key.tableA 0 + (2 ^ 16 : Nat) • tableValue Key.tableA 0) = _
    rw [cv_add, cv_smulN, cv_midG hF, cv_tableValueG hF hzt, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [keyG]
    push_cast
    ring
  · show cv (mid Key.tableB JVa + (2 ^ 16 : Nat) • tableValue Key.tableB JVa) = _
    rw [cv_add, cv_smulN, cv_midG hF, cv_tableValueG hF hzt, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [keyG]
    push_cast
    ring

theorem cv_tableValuesAtCostsG (hF : Filled c) :
    cv tableValuesAtCosts = (Finset.range T).sum fun t => Ph t * tvSumG c t := by
  have h1 : ∀ l, cv (sumTo (JV / S2) fun i =>
      (256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
      = (Finset.range T).sum fun t => Ph t * (Finset.range JV).sum fun x => (256 : K) ^ l *
          ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + x) t : Int) : K) := by
    intro l
    rw [cv_sumTo]
    have h2 : ∀ i, cv ((256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t => Ph t * ((256 : K) ^ l *
            ((c.cell .wide (S2 * ((4 * d + (3 + l) * JV) / S2) + (S2 * i + j)) t : Int) : K)) := by
      intro i
      rw [cv_smulN, hF.hentry, cv_coe]
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
  rw [cv_Eadd, rd_nmul, rd_ERC, cv_sumTo]
  simp only [h1]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  unfold tvSumG
  push_cast
  ring

theorem cv_tableG (hF : Filled c) :
    cv table = (Finset.range T).sum fun t => Ph t * tableG c t := by
  unfold table
  rw [cv_subE, cv_add, rd_nmul, cv_atCosts hF, cv_tableValuesAtCostsG hF, rd_ERC, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold tableG
  push_cast
  ring

end Filled

end VerifiableInference.Desc.Kinds.Head.Law
