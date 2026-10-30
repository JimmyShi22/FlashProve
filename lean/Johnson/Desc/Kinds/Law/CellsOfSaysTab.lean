--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsOfSaysTab.lean.
WHAT IT DOES NOT SHOW. A TOY: cells written out in Lean; no file in
scope; not what the prover's program lays. That a given table is a step table: Law/
CellsOfSaysEX.lean (the library's EX; the table of two values). Fair's premises stand as in Law/
CellsOfSays.lean (Says; |Wh| <= 2^12; |act| <= 2047; C < 2^40). No soundness, no probability,
nothing on hiding.
LETTERS. No top statement has a letter under "there is": withTab tab c is a function of the caller's
tab and c. sT is read by planOk alone.
WHAT IT IS. Law/CellsOfSays.lean's maker WITH THE TABLE A LETTER (a reader's mend): for every table
with Steps tab (TableOk; from row 1 on at most 2).
  Steps             what is asked of the table.
  sumU, numU, digitU, withTab   the cells: the margins' digits, what is paid, "over" and the slacks
                    of the mean, the clip and the count are Law/CellsOfSays.lean's; the table
                    value's
                    three limbs are the bytes of tab (middle digit) - 1, each less 128; the table's
                    slack is 2^24 less the sum of a position's V values.
  sumU_ge, sumU_le  that sum is at least V; at a position with a cost at most 2 V: with the plan's
                    test 2 V <= 2^F, WHICH IS SPENT HERE, the slack is not negative.
  ..._withTab, rowU, wideU_..., digitU_byte, tvU_sum   as their namesakes there.
  intRel_withTab, cellRel_withTab, cellRelN_withTab, holds_withTab, both_withTab   IntRel; CellRel
                    WHOLE at tab; CellRelN whole where it holds of c; Holds; all together.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsOfSays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 1. The table, a letter; the cells -/

/-- What is asked of the table: HeadLaw.lean's TableOk, and that from row 1 on a row holds at most
2: a step table. -/
structure Steps (tab : Nat → Nat) : Prop where
  ok : TableOk tab
  two : ∀ u, 1 ≤ u → tab u ≤ 2

variable (tab : Nat → Nat)

/-- The table values of a position's vocabulary entries, added up. -/
def sumU (c : NCells) (t : Nat) : Nat :=
  (Finset.range V).sum fun x => tab (midA c x t).toNat

/-- The six hidden numbers: Law/CellsOfSays.lean's, but for the table's slack: 2^24 less that sum.
-/
def numU (c : NCells) : Number → Nat → Nat
  | .slackTable, t => 2 ^ 24 - sumU tab c t
  | .paid, t => numA c .paid t
  | .over, t => numA c .over t
  | .slackMean, t => numA c .slackMean t
  | .slackClip, t => numA c .slackClip t
  | .slackCap, t => numA c .slackCap t

def digitU (c : NCells) (t j : Nat) : Nat :=
  if j < 5 then dig 5 (numU tab c .paid t) j
  else if j < 6 then dig 1 (numU tab c .over t) (j - 5)
  else if j < 11 then dig 5 (numU tab c .slackMean t) (j - 6)
  else if j < 16 then dig 5 (numU tab c .slackClip t) (j - 11)
  else if j < 18 then dig 2 (numU tab c .slackCap t) (j - 16)
  else dig 3 (numU tab c .slackTable t) (j - 18)

/-- Cells c with the head's own cells laid anew, of c's own logits, the policy AND THE TABLE: the
table value's three limbs are the bytes of tab (the middle digit) - 1, each less 128. -/
def withTab (c : NCells) : NCells :=
  { c with
    cell := fun m f t =>
      match m with
      | .row =>
        if NR ≤ f ∧ f < NR + 21 then (digitU tab c t (f - NR) : Int) - 128 else c.cell .row f t
      | .wide =>
        if f < 4 * d then c.cell .wide f t
        else if f < 4 * d + JV then loZ (midA c (f - 4 * d) t - o2 (f - 4 * d) t)
        else if f < 4 * d + 2 * JV then
          hiZ (midA c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
        else if f < 4 * d + 3 * JV then
          lowA c (f - (4 * d + 2 * JV)) t - o1 (f - (4 * d + 2 * JV)) t
        else if f < 4 * d + 6 * JV then
          (dig 3 (tab (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat - 1)
            ((f - (4 * d + 3 * JV)) / JV) : Int) - 128
        else c.cell .wide f t
      | .act => c.cell .act f t }

theorem sumU_ge (hS : Steps tab) (c : NCells) (t : Nat) : V ≤ sumU tab c t := by
  unfold sumU
  calc V = (Finset.range V).sum fun _ => 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun x _ => (hS.ok.2 _).1

/-- At a position with a cost no middle digit is 0: so every value is at most 2. HERE THE PLAN's
TEST 2 V <= 2^F FINDS ITS USE. -/
theorem sumU_le (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    {c : NCells} (A : Fair c) {t : Nat} (hc : costed t = true) : sumU tab c t ≤ 2 * V := by
  unfold sumU
  calc _ ≤ (Finset.range V).sum fun _ => 2 := Finset.sum_le_sum fun x hx =>
        hS.two _ (Nat.one_le_iff_ne_zero.mpr (midA_pos hplan hreq A (Finset.mem_range.mp hx) hc))
    _ = 2 * V := by simp [Nat.mul_comm]

theorem logit_withTab (c : NCells) (t v : Nat) :
    logit (withTab tab c).toCells t v = logit c.toCells t v := rfl

theorem cost_withTab (c : NCells) (t : Nat) :
    cost (withTab tab c).toCells t = cost c.toCells t := rfl

theorem rowU (c : NCells) (t : Nat) {j : Nat} (hj : j < 21) :
    (withTab tab c).cell .row (NR + j) t = (digitU tab c t j : Int) - 128 := by
  show (if NR ≤ NR + j ∧ NR + j < NR + 21 then (digitU tab c t (NR + j - NR) : Int) - 128
    else c.cell .row (NR + j) t) = _
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem rowU_low (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    (withTab tab c).cell .row n t = c.cell .row n t := by
  show (if NR ≤ n ∧ n < NR + 21 then (digitU tab c t (n - NR) : Int) - 128
    else c.cell .row n t) = _
  rw [if_neg (by unfold NR; omega)]

theorem numU_sum (c : NCells) (t a k N : Nat) (hak : a + k ≤ 21)
    (hd : ∀ l, l < k → digitU tab c t (a + l) = dig k N l)
    (hs : (Finset.range k).sum (fun l => 256 ^ l * dig k N l) = N) :
    ((Finset.range k).sum fun l =>
      (256 : Int) ^ l * ((withTab tab c).cell .row (NR + a + l) t + 128)) = (N : Int) := by
  rw [← hs]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [Nat.add_assoc, rowU tab c t (by omega), hd l hl']
  ring

theorem numZ_withTab (c : NCells) (n : Number) (t : Nat) :
    numZ (withTab tab c).toCells n t = (numU tab c n t : Int) := by
  unfold numZ
  cases n
  · exact numU_sum tab c t 0 5 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_pos (by omega), Nat.zero_add]) (dig_sum5 _)
  · exact numU_sum tab c t 5 1 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum1 _)
  · exact numU_sum tab c t 6 5 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left])
      (dig_sum5 _)
  · exact numU_sum tab c t 11 5 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left]) (dig_sum5 _)
  · exact numU_sum tab c t 16 2 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum2 _)
  · exact numU_sum tab c t 18 3 _ (by omega) (fun l hl => by
      unfold digitU
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), Nat.add_sub_cancel_left]) (dig_sum3 _)

theorem wideU_old (c : NCells) (t : Nat) {f : Nat} (hf : f < 4 * d) :
    (withTab tab c).cell .wide f t = c.cell .wide f t := by
  show (if f < 4 * d then c.cell .wide f t else _) = _
  rw [if_pos hf]

theorem wideU_mid0 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withTab tab c).cell .wide (4 * d + x) t = loZ (midA c x t - o2 x t) := by
  show (if 4 * d + x < 4 * d then c.cell .wide (4 * d + x) t
    else if 4 * d + x < 4 * d + JV then
      loZ (midA c (4 * d + x - 4 * d) t - o2 (4 * d + x - 4 * d) t)
    else _) = _
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideU_mid1 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withTab tab c).cell .wide (4 * d + JV + x) t = hiZ (midA c x t - o2 x t) := by
  show (if 4 * d + JV + x < 4 * d then c.cell .wide (4 * d + JV + x) t
    else if 4 * d + JV + x < 4 * d + JV then _
    else if 4 * d + JV + x < 4 * d + 2 * JV then
      hiZ (midA c (4 * d + JV + x - (4 * d + JV)) t - o2 (4 * d + JV + x - (4 * d + JV)) t)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideU_low (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withTab tab c).cell .wide (4 * d + 2 * JV + x) t = lowA c x t - o1 x t := by
  show (if 4 * d + 2 * JV + x < 4 * d then c.cell .wide (4 * d + 2 * JV + x) t
    else if 4 * d + 2 * JV + x < 4 * d + JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 2 * JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 3 * JV then
      lowA c (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t -
        o1 (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem wideU_tv (c : NCells) (t : Nat) {l x : Nat} (hl : l < 3) (hx : x < JV) :
    (withTab tab c).cell .wide (4 * d + (3 + l) * JV + x) t =
      (dig 3 (tab (midA c x t).toNat - 1) l : Int) - 128 := by
  have e : 4 * d + (3 + l) * JV + x - (4 * d + 3 * JV) = x + l * JV := by
    rw [Nat.add_mul]
    omega
  have h1 : 4 * d + 3 * JV ≤ 4 * d + (3 + l) * JV + x := by
    rw [Nat.add_mul]
    omega
  have h2 : 4 * d + (3 + l) * JV + x < 4 * d + 6 * JV := by
    have : (3 + l) * JV + JV ≤ 6 * JV := by
      have : (3 + l + 1) * JV ≤ 6 * JV := Nat.mul_le_mul_right _ (by omega)
      rwa [Nat.add_mul _ 1, Nat.one_mul] at this
    omega
  show (if 4 * d + (3 + l) * JV + x < 4 * d then c.cell .wide (4 * d + (3 + l) * JV + x) t
    else if 4 * d + (3 + l) * JV + x < 4 * d + JV then _
    else if 4 * d + (3 + l) * JV + x < 4 * d + 2 * JV then _
    else if 4 * d + (3 + l) * JV + x < 4 * d + 3 * JV then _
    else if 4 * d + (3 + l) * JV + x < 4 * d + 6 * JV then
      (dig 3 (tab (midA c ((4 * d + (3 + l) * JV + x - (4 * d + 3 * JV)) % JV) t).toNat - 1)
        ((4 * d + (3 + l) * JV + x - (4 * d + 3 * JV)) / JV) : Int) - 128
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2, e,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt hx, Nat.zero_add]

theorem midZ_withTab (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    midZ (withTab tab c).toCells x t = midA c x t := by
  unfold midZ off2
  rw [show (withTab tab c).toCells.cell .wide (4 * d + x) t = _ from wideU_mid0 tab c t hx,
    show (withTab tab c).toCells.cell .wide (4 * d + JV + x) t = _ from wideU_mid1 tab c t hx,
    lo_hi]
  unfold o2
  split <;> push_cast <;> ring

theorem lowZ_withTab (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    lowZ (withTab tab c).toCells x t = lowA c x t := by
  unfold lowZ off1
  rw [show (withTab tab c).toCells.cell .wide (4 * d + 2 * JV + x) t = _ from wideU_low tab c t hx]
  unfold o1
  split <;> push_cast <;> ring

theorem tvZ_withTab (hS : Steps tab) (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    tvZ (withTab tab c).toCells x t = (tab (midA c x t).toNat : Int) := by
  unfold tvZ offE
  rw [Finset.sum_congr rfl fun l hl => by
    rw [show (withTab tab c).toCells.cell .wide (4 * d + (3 + l) * JV + x) t =
      (dig 3 (tab (midA c x t).toNat - 1) l : Int) - 128 from
        wideU_tv tab c t (Finset.mem_range.mp hl) hx]]
  have h1 := (hS.ok.2 (midA c x t).toNat).1
  have h3 := dig_sum3 (tab (midA c x t).toNat - 1)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h3 ⊢
  have h4 : ((tab (midA c x t).toNat : Nat) : Int) =
      ((tab (midA c x t).toNat - 1 : Nat) : Int) + 1 := by
    rw [Nat.cast_sub h1]
    ring
  rw [h4]
  generalize tab (midA c x t).toNat - 1 = N at h3 ⊢
  generalize dig 3 N 0 = a0 at h3 ⊢
  generalize dig 3 N 1 = a1 at h3 ⊢
  generalize dig 3 N 2 = a2 at h3 ⊢
  rw [← h3]
  push_cast
  ring

/-- **The top digit's number is 2^(sh+15) times the top digit.** No premise. -/
theorem topNum_withTab (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    topNum (withTab tab c).toCells x t = 2 ^ (sh + 15) * topA c x t := by
  unfold topNum liftZ
  rw [logit_withTab tab, logit_withTab tab, numZ_withTab tab, numZ_withTab tab,
    midZ_withTab tab c t hx, lowZ_withTab tab c t hx]
  have e := Int.mul_ediv_add_emod (marA c x t) (2 ^ sh)
  have e2 := digits_add (marA c x t / 2 ^ sh)
  have e3 : marA c x t = (if x < V ∧ checked t = true then
      logit c.toCells t (win t) - logit c.toCells t x else 0) +
      (if x < V ∧ costed t = true then
        (numU tab c .paid t : Int) + (BIG : Int) * (numU tab c .over t : Int)
        else 0) - (if checked t = true ∧ x < win t then 1 else 0) := rfl
  rw [← e3]
  unfold midA lowA topA
  rw [pow_add]
  linear_combination e.symm - 2 ^ sh * e2


theorem digitU_byte (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    {c : NCells} (A : Fair c) (t : Nat)
    {j : Nat} (hj : j < 21) : digitU tab c t j < 256 := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, hcap, _⟩ := hp
  have hC := A.clip
  have hV := P.hV2
  have h5 : (256 : Nat) ^ 5 = 2 ^ 40 := by norm_num
  unfold digitU
  split
  · refine dig_byte (by omega) (by omega) ?_
    show paidA c t < 256 ^ 5
    rw [h5]
    exact lt_of_le_of_lt (paidA_le c t) hC
  split
  · refine dig_byte (by omega) (by omega) ?_
    show overA c t < 256 ^ 1
    have := overA_le c t
    omega
  split
  · refine dig_byte (by omega) (by omega) ?_
    show (if costed t = true then share (slackA c) RC (t - r) else 0) < 256 ^ 5
    rw [h5]
    split
    · rename_i hc
      exact lt_of_le_of_lt (share_le (b := theta) (Nat.sub_le _ _) (rc_pos hc) _)
        (lt_of_le_of_lt hth hC)
    · norm_num
  split
  · refine dig_byte (by omega) (by omega) ?_
    show C - paidA c t < 256 ^ 5
    rw [h5]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hC
  split
  · refine dig_byte (by omega) (by omega) ?_
    show (if t = r then cap - oversA c else 0) < 256 ^ 2
    split
    · norm_num
      omega
    · norm_num
  · refine dig_byte (by omega) (by omega) ?_
    show 2 ^ 24 - sumU tab c t < 256 ^ 3
    have := sumU_ge tab hS c t
    norm_num
    omega

theorem tvU_sum (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) {t : Nat} (hc : costed t = true) :
    ((Finset.range JV).sum fun x => tvZ (withTab tab c).toCells x t) =
      (sumU tab c t : Int) + ((JV - V : Nat) : Int) * 2 ^ 24 := by
  have P := planFacts hplan
  rw [Finset.sum_congr rfl fun x hx => tvZ_withTab tab hS c t (Finset.mem_range.mp hx)]
  have hJ : JV = V + (JV - V) := by
    have := V_le_JV
    omega
  conv_lhs => rw [hJ]
  rw [Finset.sum_range_add]
  have e2 : ∀ x ∈ Finset.range (JV - V),
      ((tab (midA c (V + x) t).toNat : Nat) : Int) = 2 ^ 24 := by
    intro x _
    rw [midA_pad hreq hy c t (by omega : ¬ V + x < V), hS.ok.1, P.hF]
    norm_num
  rw [Finset.sum_congr rfl e2]
  unfold sumU
  simp


/-! ## 5. The relations -/

/-- **THE RELATION IN INTEGERS.** -/
theorem intRel_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) : IntRel (withTab tab c).toCells tab := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hV24, h2V, _⟩ := hp
  refine ⟨fun t _ j hj => ?_, fun t _ x hx => ?_, fun t _ x hx => ?_,
    fun t _ x hx => ⟨(topA c x t).toNat, ?_⟩, fun t _ x hx => ?_, fun t _ hc => ?_,
    fun t _ hc => ?_, ?_, ?_⟩
  · rw [show (withTab tab c).toCells.cell .row (NR + j) t = _ from rowU tab c t hj]
    have := digitU_byte tab hS hplan A t hj
    omega
  · rw [midZ_withTab tab c t hx]
    exact (midA_range hplan hreq hy A x t).1
  · rw [lowZ_withTab tab c t hx]
    exact (lowA_range P c x t).1
  · rw [topNum_withTab tab c t hx, Int.toNat_of_nonneg (topA_range hplan hreq hy A x t).1]
  · rw [tvZ_withTab tab hS c t hx, midZ_withTab tab c t hx]
  · rw [numZ_withTab tab, numZ_withTab tab]
    show ((paidA c t : Nat) : Int) + ((C - paidA c t : Nat) : Int) = (C : Int)
    rw [Nat.cast_sub (paidA_le c t)]
    ring
  · rw [numZ_withTab tab, tvU_sum tab hS hplan hreq hy A hc, P.hF]
    show ((2 ^ 24 - sumU tab c t : Nat) : Int) +
      ((sumU tab c t : Int) + ((JV - V : Nat) : Int) * 2 ^ 24) = _
    have hle : sumU tab c t ≤ 2 ^ 24 := by
      have := sumU_le tab hS hplan hreq A hc
      rw [P.hF] at h2V
      omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  · rw [← meanA_eq A]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withTab tab, numZ_withTab tab, numZ_withTab tab]
    rfl
  · rw [← countA_eq A]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withTab tab, numZ_withTab tab]
    rfl

theorem small_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18)
    (m : Matrix) (f t : Nat) : ((withTab tab c).cell m f t).natAbs < 2 ^ 18 := by
  have P := planFacts hplan
  have ho2 : ∀ x, 0 ≤ o2 x t ∧ o2 x t ≤ 32896 := fun x => by unfold o2; split <;> norm_num
  have ho1 : ∀ x, 0 ≤ o1 x t ∧ o1 x t ≤ 128 := fun x => by unfold o1; split <;> norm_num
  cases m
  · show (if f < 4 * d then c.cell .wide f t
      else if f < 4 * d + JV then loZ (midA c (f - 4 * d) t - o2 (f - 4 * d) t)
      else if f < 4 * d + 2 * JV then
        hiZ (midA c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
      else if f < 4 * d + 3 * JV then
        lowA c (f - (4 * d + 2 * JV)) t - o1 (f - (4 * d + 2 * JV)) t
      else if f < 4 * d + 6 * JV then
        (dig 3 (tab (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat - 1)
          ((f - (4 * d + 3 * JV)) / JV) : Int) - 128
      else c.cell .wide f t).natAbs < 2 ^ 18
    have h0 := hs .wide f t
    split
    · exact h0
    split
    · have := lo_bd (midA c (f - 4 * d) t - o2 (f - 4 * d) t)
      omega
    split
    · have a := midA_range hplan hreq hy A (f - (4 * d + JV)) t
      have b := ho2 (f - (4 * d + JV))
      have := hi_bd (z := midA c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
        (by norm_num; omega) (by norm_num at a ⊢; omega)
      omega
    split
    · have a := lowA_range P c (f - (4 * d + 2 * JV)) t
      have b := ho1 (f - (4 * d + 2 * JV))
      norm_num at a
      omega
    split
    · rename_i g1 g2 g3 g4 g5
      have hl : (f - (4 * d + 3 * JV)) / JV < 3 := Nat.div_lt_of_lt_mul (by omega)
      have hN : tab (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat - 1 < 256 ^ 3 := by
        have := (hS.ok.2 (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat)
        rw [P.hF] at this
        norm_num
        omega
      have := dig_byte (by omega) hl hN
      omega
    · exact h0
  · exact hs .act f t
  · show (if NR ≤ f ∧ f < NR + 21 then (digitU tab c t (f - NR) : Int) - 128
      else c.cell .row f t).natAbs < 2 ^ 18
    split
    · rename_i h
      have := digitU_byte tab hS hplan A t (j := f - NR) (by omega)
      omega
    · exact hs .row f t

theorem rowV_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (t : Nat) {x : Nat} (hx : x < JV) :
    ∃ u : Nat, u < 2 ^ 16 ∧
      midZ (withTab tab c).toCells x t + 2 ^ 16 * tvZ (withTab tab c).toCells x t
      = (u : Int) + 2 ^ 16 * (tab u : Int) := by
  obtain ⟨h0, h1⟩ := midA_range hplan hreq hy A x t
  refine ⟨(midA c x t).toNat, by omega, ?_⟩
  rw [midZ_withTab tab c t hx, tvZ_withTab tab hS c t hx, Int.toNat_of_nonneg h0]

/-- **THE HEAD's RELATION ON CELLS, WHOLE.** -/
theorem cellRel_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) :
    CellRel (withTab tab c).toCells tab := by
  have P := planFacts hplan
  have hI := intRel_withTab tab hS hplan hreq hy A
  obtain ⟨a, b, e⟩ := four_of_int P hI
  have hJ := jva_le (by have := P.hV2; omega)
  refine ⟨small_withTab tab hS hplan hreq hy A hs, hI.bytes, fun t ht x hx => ?_,
    fun t ht x hx => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, a, b, e⟩
  · obtain ⟨h0, h1⟩ := topA_range hplan hreq hy A x t
    refine inBits_of_rd (z := topA c x t) (okE_keyAt _ _ _) ?_ h0 h1
    rw [rd_key_top P hreq hy hx ht, topNum_withTab tab c t hx]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (two_pow_ne_zero _), one_mul]
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_mid P hx ht) (hI.mid t ht x hx) ?_
    rw [midZ_withTab tab c t hx]
    exact (midA_range hplan hreq hy A x t).2
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_low P hx ht) (hI.low t ht x hx) ?_
    rw [lowZ_withTab tab c t hx]
    exact (lowA_range P c x t).2
  · have hx' : x < JVa := hx
    obtain ⟨u, hu, hr⟩ := rowV_withTab tab hS hplan hreq hy A t (x := x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableA P hx' ht, hr])
  · have hx' : x < JV - JVa := hx
    obtain ⟨u, hu, hr⟩ := rowV_withTab tab hS hplan hreq hy A t (x := JVa + x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableB P hx' ht, hr])

theorem digZ_withTab (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    digZ (withTab tab c) t n = digZ c t n := by
  unfold digZ
  rw [rowU_low tab c t hn]

theorem holds_withTab (c : NCells) (h : (dataOf c).Holds) : (dataOf (withTab tab c)).Holds := by
  intro i hi k hk t ht
  obtain rfl : i = 0 := by
    have : i < 1 := hi
    omega
  have e := h 0 hi k hk t ht
  rw [idAt_eq] at e ⊢
  rw [← e]
  unfold vecK
  exact idn_congr _ _ (fun n hn => by
    unfold dK
    rw [digZ_withTab tab c t hn]) k

/-- **THE NORM's RELATION ON CELLS, WHOLE, WHERE IT HOLDS OF c.** -/
theorem cellRelN_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (h : CellRelN c) : CellRelN (withTab tab c) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero (planFacts hplan).hdS
  have haw : ∀ t x, x < d → awZ (withTab tab c) t x = awZ c t x := fun t x hx => by
    unfold awZ
    rw [wideU_old tab c t (by omega), wideU_old tab c t (by omega)]
  have hrem : ∀ t x, x < d → remZ (withTab tab c) t x = remZ c t x := fun t x hx => by
    unfold remZ
    rw [wideU_old tab c t (by omega), wideU_old tab c t (by omega)]
  have hrec : ∀ t, recZ (withTab tab c) t = recZ c t := fun t => by
    unfold recZ Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
    rw [b256_congr (fun n hn => digZ_withTab tab c t hn) 80 3 (by omega),
      b256_congr (fun n hn => digZ_withTab tab c t hn) 83 3 (by omega)]
  refine ⟨small_withTab tab hS hplan hreq hy A h.small, h.smallS, fun t ht v hv => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht j hj => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt _ _ hv) okE_zero
    have e := rd_rowsAt (withTab tab c) (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht] at e
    have hH := holds_withTab tab c (holds_of_rows c h.rows) 0 (show 0 < 1 by omega) k hk' t ht
    rw [idAt_eq] at hH
    rw [e, hH, rd_zero]
  · have e : keyNAt (withTab tab c) (cornerN x t) .remLow = keyNAt c (cornerN x t) .remLow :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remLow ht hd hx, rd_keyN_remLow ht hd hx, hrec, haw t x hx, hrem t x hx]
        rfl)
    rw [e]
    exact h.remLow t ht x hx
  · have e : keyNAt (withTab tab c) (cornerN x t) .remHigh = keyNAt c (cornerN x t) .remHigh :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remHigh ht hd hx, rd_keyN_remHigh ht hd hx, hrem t x hx])
    rw [e]
    exact h.remHigh t ht x hx
  · have e : keyNAt (withTab tab c) (cornerN x t) .clamp = keyNAt c (cornerN x t) .clamp :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_clamp ht hd hx, rd_keyN_clamp ht hd hx, haw t x hx]
        rfl)
    rw [e]
    exact h.clamp t ht x hx
  · by_cases h99 : j < 99
    · have e : keyNAt (withTab tab c) (cornerN j t) .digits = keyNAt c (cornerN j t) .digits :=
        eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
          rw [rd_keyN_digits ht hj, rd_keyN_digits ht hj, digZ_withTab tab c t h99])
      rw [e]
      exact h.digits t ht j hj
    · have hm : ((mul j : Nat) : Int) = 1 := by
        unfold mul
        have : ∀ a : Nat, a < 99 → (j == a) = false := fun a ha => by simp; omega
        simp [this]
      have hj' : j - NR < 21 := by unfold NR at hj ⊢; omega
      have hjj : NR + (j - NR) = j := by unfold NR; omega
      have hb := digitU_byte tab hS hplan A t hj'
      have hz : digZ (withTab tab c) t j = (digitU tab c t (j - NR) : Int) := by
        unfold digZ
        rw [← hjj, rowU tab c t hj', hjj]
        ring
      refine inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_digits ht hj) ?_ ?_
      · rw [hm, one_mul, hz]
        omega
      · rw [hm, one_mul, hz]
        norm_num
        omega

/-- **THE CONVERSE OF LEMMA 1, AGAINST THE TABLE OF TWO VALUES.** For any cells that meet the norm's
relation, with any weights and activations within Lemma 1's two bounds: WHERE THE TEXT's OWN CLAIM
UNDER THE POLICY HOLDS OF THEM (Says) and C < 2^40: the head's own cells, laid of their logits and
the policy, meet both relations on cells, whole. Weights, logits, costs and claim are c's. -/
theorem both_withTab (hS : Steps tab) {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (h : CellRelN c) :
    CellRelN (withTab tab c) ∧ CellRel (withTab tab c).toCells tab ∧ TableOk tab ∧
      (dataOf (withTab tab c)).Holds ∧ (withTab tab c).Wh = c.Wh ∧
      (∀ t v, logit (withTab tab c).toCells t v = logit c.toCells t v) ∧
      (∀ n t, numZ (withTab tab c).toCells n t = (numU tab c n t : Int)) ∧
      ∀ t, costed t = true →
        numZ (withTab tab c).toCells .paid t + (C : Int) * numZ (withTab tab c).toCells .over t =
          min (cost (withTab tab c).toCells t) (C : Int) :=
  ⟨cellRelN_withTab tab hS hplan hreq hy A h, cellRel_withTab tab hS hplan hreq hy A h.small,
    hS.ok, holds_withTab tab c (holds_of_rows c h.rows), rfl,
    fun _ _ => rfl, numZ_withTab tab c, fun t hc => by
      rw [numZ_withTab tab, numZ_withTab tab, cost_withTab tab, ← spentA_cast c hc]
      show (paidA c t : Int) + (C : Int) * (overA c t : Int) = _
      unfold spentA
      push_cast
      ring⟩

end VerifiableInference.Desc.Kinds.Head.Law
