--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsOfSays.lean.
WHAT IT DOES NOT SHOW. A TOY: cells written out in Lean; no file in
scope; not what the prover's program lays. NOTE: AGAINST A TABLE OF TWO VALUES (Law/
CellsWithCosts.lean: stepTab: row 0 holds 2^24, every other row 1). THE FORMAT's TABLE AT THE ONE
EXPONENT THAT planOk ADMITS (sT + 4 = sh) IS 2^24, 2, 1, 1, ...: stepTab PARTS FROM IT AT ROW 1, AND
THAT ROW IS HIT AT EVERY POSITION THAT PAYS (the entry that attains the gap has the lifted margin
2^sh: middle digit 1): SO withAll's CELLS DO NOT PASS AT THE FORMAT's TABLE (a reader's find). The
cells that do: Law/CellsOfSaysTab.lean, which takes the table as a letter and stands on this file's
lemmas on the margins and the sums. That cells exist which meet its premises with a position over, a
top digit that is not 0 and a slack that does not divide: Law/CellsOfSaysAt.lean. |Wh| <= 2^12 is a
premise that no test or relation of ours gives. No soundness, no probability, nothing on hiding.
LETTERS. No statement at the top has a letter under "there is": withAll c is a function of the
caller's c. sT is read by planOk alone.
WHAT IT IS. THE CONVERSE OF LEMMA 1 (HeadLaw.lean: Lemma1Statement: CellRel c tab -> Says c), at
that table: honest head cells FOR ALL THAT LEMMA 1 COVERS: Law/CellsFromLogits.lean's two
bounds (a lifted margin below 2^(sh+16); cost <= theta at every position) were that lemma's own and
are gone.
  costA, overA, paidA, spentA, slackA, oversA, numA, digitA, marA, lowA, midA, topA, withAll   the
                    cells: a position whose cost is above the clip is "over": it pays nothing and is
                    lifted by BIG; else it pays its cost; the mean's slack theta RC - (the clipped
                    costs' sum) is dealt over the positions with a cost (MakerArith.lean: share);
                    the count's slack cap - (the number over) lies at the first; a lifted margin is
                    cut in three digits so that the middle one is 0 only where the margin is below
                    2^sh (midD, topD). The top digit is no cell.
  topNum_withAll    the top digit's number is 2^(sh+15) topA: NO PREMISE.
  Three, three      the plan's two tests "three-digits", which "only let an honest prover pass"
                    (HeadOk.lean): HERE THEY ARE SPENT, both.
  Fair              what is asked: Says c.toCells; |Wh| <= 2^12; |act| <= 2047 (Lemma 1's own two
                    bounds); C < 2^40.
  diff_le, gap_le, lift_cases, liftedA, marA_hi, marA_last, rangeA, quotA, midA_range, topA_range,
  lowA_range, midA_pos, midA_pad   the lifted margins: at least 2^sh at a position with a cost; not
                    negative at the last (the claim's third clause); below (2^16 + 1) 2^(sh+15).
  spentA_cast, total_le, filter_len, overs_le   the claim's first two clauses, in these numbers.
  digitA_byte, tvA_sum, meanA_eq, countA_eq   the 21 digits are bytes; the three sums.
  intRel_withAll, small_withAll, cellRel_withAll, holds_withAll, cellRelN_withAll, both_withAll
                    IntRel; CellRel WHOLE; Holds; CellRelN whole where it holds of c; all together,
                    with paid + C over = min (cost, C) at every position with a cost.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.MakerArith
import Johnson.Desc.Kinds.Law.CellsFromLogits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 1. The head's own cells, of the logits and the policy -/

/-- The text's cost, as a natural number. -/
def costA (c : NCells) (t : Nat) : Nat := (cost c.toCells t).toNat

theorem costA_cast (c : NCells) (t : Nat) : (costA c t : Int) = cost c.toCells t := by
  unfold costA
  rw [Int.toNat_of_nonneg]
  unfold cost
  have := gap_nonneg c.toCells t
  positivity

/-- The digit "over": 1 at a position whose cost is above the clip. -/
def overA (c : NCells) (t : Nat) : Nat := if costed t = true ∧ C < costA c t then 1 else 0

/-- What the prover pays: the cost where it is at most the clip; nothing where the position is over.
-/
def paidA (c : NCells) (t : Nat) : Nat := if costed t = true ∧ costA c t ≤ C then costA c t else 0

/-- What a position adds to the mean's sum: its cost, clipped. -/
def spentA (c : NCells) (t : Nat) : Nat := paidA c t + C * overA c t

/-- The mean's slack, whole; the number of positions that are over. -/
def slackA (c : NCells) : Nat :=
  theta * RC - (Finset.range T).sum fun t => if costed t = true then spentA c t else 0
@[inherit_doc slackA] def oversA (c : NCells) : Nat :=
  (Finset.range T).sum fun t => if costed t = true then overA c t else 0

/-- The six hidden numbers. The mean's slack is dealt over the positions with a cost; the count's
lies at the first of them. -/
def numA (c : NCells) : Number → Nat → Nat
  | .paid, t => paidA c t
  | .over, t => overA c t
  | .slackMean, t => if costed t = true then share (slackA c) RC (t - r) else 0
  | .slackClip, t => C - paidA c t
  | .slackCap, t => if t = r then cap - oversA c else 0
  | .slackTable, _ => 2 ^ 24 - V

def digitA (c : NCells) (t j : Nat) : Nat :=
  if j < 5 then dig 5 (numA c .paid t) j
  else if j < 6 then dig 1 (numA c .over t) (j - 5)
  else if j < 11 then dig 5 (numA c .slackMean t) (j - 6)
  else if j < 16 then dig 5 (numA c .slackClip t) (j - 11)
  else if j < 18 then dig 2 (numA c .slackCap t) (j - 16)
  else dig 3 (numA c .slackTable t) (j - 18)

/-- The margin of entry x at position t, lifted by what is paid and, where the position is over, by
BIG. -/
def marA (c : NCells) (x t : Nat) : Int :=
  (if x < V ∧ checked t = true then logit c.toCells t (win t) - logit c.toCells t x else 0)
    + (if x < V ∧ costed t = true then (paidA c t : Int) + (BIG : Int) * (overA c t : Int) else 0)
    - (if checked t = true ∧ x < win t then 1 else 0)

/-- Its three digits: the low one below 2^sh; the rest cut by Law/MakerArith.lean. The top digit is
no cell. -/
def lowA (c : NCells) (x t : Nat) : Int := marA c x t % 2 ^ sh
@[inherit_doc lowA] def midA (c : NCells) (x t : Nat) : Int := midD (marA c x t / 2 ^ sh)
@[inherit_doc lowA] def topA (c : NCells) (x t : Nat) : Int := topD (marA c x t / 2 ^ sh)

/-- Cells c with the head's own cells laid anew, of c's own logits and the policy. The activations,
the weights and all else are c's. -/
def withAll (c : NCells) : NCells :=
  { c with
    cell := fun m f t =>
      match m with
      | .row =>
        if NR ≤ f ∧ f < NR + 21 then (digitA c t (f - NR) : Int) - 128 else c.cell .row f t
      | .wide =>
        if f < 4 * d then c.cell .wide f t
        else if f < 4 * d + JV then loZ (midA c (f - 4 * d) t - o2 (f - 4 * d) t)
        else if f < 4 * d + 2 * JV then
          hiZ (midA c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
        else if f < 4 * d + 3 * JV then
          lowA c (f - (4 * d + 2 * JV)) t - o1 (f - (4 * d + 2 * JV)) t
        else if f < 4 * d + 6 * JV then
          (if (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat = 0 then 127 else -128)
        else c.cell .wide f t
      | .act => c.cell .act f t }

theorem logit_withAll (c : NCells) (t v : Nat) :
    logit (withAll c).toCells t v = logit c.toCells t v := rfl

theorem cost_withAll (c : NCells) (t : Nat) :
    cost (withAll c).toCells t = cost c.toCells t := rfl

theorem rowA (c : NCells) (t : Nat) {j : Nat} (hj : j < 21) :
    (withAll c).cell .row (NR + j) t = (digitA c t j : Int) - 128 := by
  show (if NR ≤ NR + j ∧ NR + j < NR + 21 then (digitA c t (NR + j - NR) : Int) - 128
    else c.cell .row (NR + j) t) = _
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem rowA_low (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    (withAll c).cell .row n t = c.cell .row n t := by
  show (if NR ≤ n ∧ n < NR + 21 then (digitA c t (n - NR) : Int) - 128
    else c.cell .row n t) = _
  rw [if_neg (by unfold NR; omega)]

theorem numA_sum (c : NCells) (t a k N : Nat) (hak : a + k ≤ 21)
    (hd : ∀ l, l < k → digitA c t (a + l) = dig k N l)
    (hs : (Finset.range k).sum (fun l => 256 ^ l * dig k N l) = N) :
    ((Finset.range k).sum fun l =>
      (256 : Int) ^ l * ((withAll c).cell .row (NR + a + l) t + 128)) = (N : Int) := by
  rw [← hs]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [Nat.add_assoc, rowA c t (by omega), hd l hl']
  ring

theorem numZ_withAll (c : NCells) (n : Number) (t : Nat) :
    numZ (withAll c).toCells n t = (numA c n t : Int) := by
  unfold numZ
  cases n
  · exact numA_sum c t 0 5 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_pos (by omega), Nat.zero_add]) (dig_sum5 _)
  · exact numA_sum c t 5 1 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum1 _)
  · exact numA_sum c t 6 5 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left])
      (dig_sum5 _)
  · exact numA_sum c t 11 5 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left]) (dig_sum5 _)
  · exact numA_sum c t 16 2 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum2 _)
  · exact numA_sum c t 18 3 _ (by omega) (fun l hl => by
      unfold digitA
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), Nat.add_sub_cancel_left]) (dig_sum3 _)

theorem wideA_old (c : NCells) (t : Nat) {f : Nat} (hf : f < 4 * d) :
    (withAll c).cell .wide f t = c.cell .wide f t := by
  show (if f < 4 * d then c.cell .wide f t else _) = _
  rw [if_pos hf]

theorem wideA_mid0 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withAll c).cell .wide (4 * d + x) t = loZ (midA c x t - o2 x t) := by
  show (if 4 * d + x < 4 * d then c.cell .wide (4 * d + x) t
    else if 4 * d + x < 4 * d + JV then
      loZ (midA c (4 * d + x - 4 * d) t - o2 (4 * d + x - 4 * d) t)
    else _) = _
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideA_mid1 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withAll c).cell .wide (4 * d + JV + x) t = hiZ (midA c x t - o2 x t) := by
  show (if 4 * d + JV + x < 4 * d then c.cell .wide (4 * d + JV + x) t
    else if 4 * d + JV + x < 4 * d + JV then _
    else if 4 * d + JV + x < 4 * d + 2 * JV then
      hiZ (midA c (4 * d + JV + x - (4 * d + JV)) t - o2 (4 * d + JV + x - (4 * d + JV)) t)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideA_low (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withAll c).cell .wide (4 * d + 2 * JV + x) t = lowA c x t - o1 x t := by
  show (if 4 * d + 2 * JV + x < 4 * d then c.cell .wide (4 * d + 2 * JV + x) t
    else if 4 * d + 2 * JV + x < 4 * d + JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 2 * JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 3 * JV then
      lowA c (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t -
        o1 (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem wideA_tv (c : NCells) (t : Nat) {l x : Nat} (hl : l < 3) (hx : x < JV) :
    (withAll c).cell .wide (4 * d + (3 + l) * JV + x) t =
      if (midA c x t).toNat = 0 then 127 else -128 := by
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
      (if (midA c ((4 * d + (3 + l) * JV + x - (4 * d + 3 * JV)) % JV) t).toNat = 0 then
        (127 : Int) else -128)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2, e,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem midZ_withAll (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    midZ (withAll c).toCells x t = midA c x t := by
  unfold midZ off2
  rw [show (withAll c).toCells.cell .wide (4 * d + x) t = _ from wideA_mid0 c t hx,
    show (withAll c).toCells.cell .wide (4 * d + JV + x) t = _ from wideA_mid1 c t hx, lo_hi]
  unfold o2
  split <;> push_cast <;> ring

theorem lowZ_withAll (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    lowZ (withAll c).toCells x t = lowA c x t := by
  unfold lowZ off1
  rw [show (withAll c).toCells.cell .wide (4 * d + 2 * JV + x) t = _ from wideA_low c t hx]
  unfold o1
  split <;> push_cast <;> ring

theorem tvZ_withAll (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    tvZ (withAll c).toCells x t = (stepTab (midA c x t).toNat : Int) := by
  unfold tvZ offE stepTab
  rw [Finset.sum_congr rfl fun l hl => by
    rw [show (withAll c).toCells.cell .wide (4 * d + (3 + l) * JV + x) t =
      if (midA c x t).toNat = 0 then (127 : Int) else -128 from
        wideA_tv c t (Finset.mem_range.mp hl) hx]]
  by_cases h : (midA c x t).toNat = 0
  · rw [if_pos h, if_pos h]
    simp [Finset.sum_range_succ]
  · rw [if_neg h, if_neg h]
    simp [Finset.sum_range_succ]

/-- **The top digit's number is 2^(sh+15) times the top digit.** No premise. -/
theorem topNum_withAll (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    topNum (withAll c).toCells x t = 2 ^ (sh + 15) * topA c x t := by
  unfold topNum liftZ
  rw [logit_withAll, logit_withAll, numZ_withAll, numZ_withAll, midZ_withAll c t hx,
    lowZ_withAll c t hx]
  have e := Int.mul_ediv_add_emod (marA c x t) (2 ^ sh)
  have e2 := digits_add (marA c x t / 2 ^ sh)
  have e3 : marA c x t = (if x < V ∧ checked t = true then
      logit c.toCells t (win t) - logit c.toCells t x else 0) +
      (if x < V ∧ costed t = true then (numA c .paid t : Int) + (BIG : Int) * (numA c .over t : Int)
        else 0) - (if checked t = true ∧ x < win t then 1 else 0) := rfl
  rw [← e3]
  unfold midA lowA topA
  rw [pow_add]
  linear_combination e.symm - 2 ^ sh * e2

/-! ## 2. What the plan's two tests "three-digits" say, and how large a logit is -/

/-- The plan's two tests that "only let an honest prover pass" (HeadOk.lean: noOverflow). -/
structure Three : Prop where
  a1 : 2 * d * 2 ^ 11 * 2 ^ 12 + 1 ≤ 2 ^ 37
  a2 : 2 * d * 2 ^ 11 * 2 ^ 12 + 1 + 2 ^ 37 + 2 ^ 32 ≤ (2 ^ 16 + 1) * 2 ^ (sh + 15)
  b : 2 * d * 2 ^ 11 * 2 ^ 12 + 1 + 2 ^ (sh + 15) ≤ 2 ^ 37

theorem three {sT : Nat} (h : planOk sT = true) : Three := by
  unfold planOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨_, hn⟩ := h
  unfold noOverflow at hn
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at hn
  obtain ⟨_, _, _, _, h5, h6, _⟩ := hn
  have x1 := of_decide_eq_true h5.1
  have x2 := of_decide_eq_true h5.2
  have x3 := of_decide_eq_true h6
  unfold BW BC BIG at x1 x2 x3
  exact ⟨x1, x2, x3⟩

theorem foldl_max_ub (f : Nat → Int) (B : Int) : ∀ (l : List Nat) (a : Int), a ≤ B →
    (∀ v ∈ l, f v ≤ B) → l.foldl (fun m v => max m (f v)) a ≤ B
  | [], _, ha, _ => ha
  | w :: l, a, ha, hf =>
    foldl_max_ub f B l (max a (f w)) (max_le ha (hf w (by simp))) fun v hv => hf v (by simp [hv])

/-- What is asked of the cells: THE TEXT's OWN CLAIM UNDER THE POLICY (HeadLaw.lean: Says), the two
bounds of Lemma 1's statement, and that the clip fits its five digits. -/
structure Fair (c : NCells) : Prop where
  claim : Says c.toCells
  wts : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12
  acts : ∀ t, t < T → ∀ k, k < d → (act c.toCells t k).natAbs ≤ 2047
  clip : C < 2 ^ 40

theorem diff_le {c : NCells} (A : Fair c) {t : Nat} (ht : t < T) (v w : Nat) :
    logit c.toCells t v - logit c.toCells t w ≤ 2 * (d : Int) * 2 ^ 11 * 2 ^ 12 := by
  have h1 := abs_le.mp (abs_logit_le A.wts A.acts ht v)
  have h2 := abs_le.mp (abs_logit_le A.wts A.acts ht w)
  have hd : (0 : Int) ≤ d := Int.natCast_nonneg _
  nlinarith [h1.2, h2.1]

theorem gap_le {c : NCells} (A : Fair c) {t : Nat} (ht : t < T) :
    gap c.toCells t ≤ 2 * (d : Int) * 2 ^ 11 * 2 ^ 12 + 1 := by
  unfold gap
  have hd : (0 : Int) ≤ d := Int.natCast_nonneg _
  refine foldl_max_ub _ _ _ 0 (by positivity) fun v _ => ?_
  have := diff_le A ht v (win t)
  split <;> linarith

theorem checked_lt (hreq : Request.ok = true) {t : Nat} (h : checked t = true) : t < T := by
  unfold Request.ok at hreq
  unfold checked at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hreq h
  omega

/-! ## 3. The lifted margins -/

theorem marA_pad (hreq : Request.ok = true) (hy : y < V) (c : NCells) (t : Nat) {x : Nat}
    (hx : ¬ x < V) : marA c x t = 0 := by
  have hw := win_lt hreq hy t
  have h4 : ¬ x < win t := by omega
  unfold marA
  simp [hx, h4]

theorem marA_unchecked (c : NCells) (x : Nat) {t : Nat} (h : ¬ checked t = true) :
    marA c x t = 0 := by
  have h2 : ¬ costed t = true := fun hc => h (checked_of_costed hc)
  unfold marA
  simp [h, h2]

/-- What lifts a position with a cost: the cost, or BIG. -/
theorem lift_cases (c : NCells) {t : Nat} (hc : costed t = true) :
    ((paidA c t : Int) + (BIG : Int) * (overA c t : Int) = cost c.toCells t ∧ costA c t ≤ C) ∨
      ((paidA c t : Int) + (BIG : Int) * (overA c t : Int) = 2 ^ 37 ∧ C < costA c t) := by
  unfold paidA overA
  by_cases h : costA c t ≤ C
  · left
    rw [if_pos ⟨hc, h⟩, if_neg (fun x => by omega), costA_cast]
    exact ⟨by simp, h⟩
  · right
    rw [if_neg (fun x => h x.2), if_pos ⟨hc, by omega⟩]
    unfold BIG
    exact ⟨by norm_num, by omega⟩

/-- **At a position with a cost every vocabulary entry's lifted margin is at least 2^sh.** -/
theorem liftedA {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) {c : NCells}
    (A : Fair c) {t x : Nat} (hx : x < V) (hc : costed t = true) : 2 ^ sh ≤ marA c x t := by
  have h3 := checked_of_costed hc
  have hT := checked_lt hreq h3
  have hg := le_gap c.toCells t hx
  have hG := gap_le A hT
  have Th := three hplan
  have hb : (2 * (d : Int) * 2 ^ 11 * 2 ^ 12 + 1 + 2 ^ (sh + 15) : Int) ≤ 2 ^ 37 := by
    exact_mod_cast Th.b
  have hp : (2 : Int) ^ sh ≤ 2 ^ (sh + 15) := pow_le_pow_right₀ (by norm_num) (by omega)
  have ht : (if checked t = true ∧ x < win t then (1 : Int) else 0) =
      if x < win t then 1 else 0 := by simp [h3]
  unfold marA
  rw [if_pos ⟨hx, h3⟩, if_pos ⟨hx, hc⟩, ht]
  rcases lift_cases c hc with ⟨e, _⟩ | ⟨e, _⟩
  · rw [e]
    unfold cost
    linarith
  · rw [e]
    linarith

/-- It fits the three digits. -/
theorem marA_hi {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) {c : NCells}
    (A : Fair c) {t x : Nat} (hx : x < V) (h3 : checked t = true) :
    marA c x t < (2 ^ 16 + 1) * 2 ^ (sh + 15) := by
  have hT := checked_lt hreq h3
  have hD := diff_le A hT (win t) x
  have hG := gap_le A hT
  have Th := three hplan
  have P := planFacts hplan
  have ha1 : (2 * (d : Int) * 2 ^ 11 * 2 ^ 12 + 1 : Int) ≤ 2 ^ 37 := by exact_mod_cast Th.a1
  have ha2 : (2 * (d : Int) * 2 ^ 11 * 2 ^ 12 + 1 + 2 ^ 37 + 2 ^ 32 : Int) ≤
      (2 ^ 16 + 1) * 2 ^ (sh + 15) := by exact_mod_cast Th.a2
  have hs : (2 : Int) ^ sh ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) (by
    rcases P.hsh with h | h <;> omega)
  have ht : (0 : Int) ≤ if checked t = true ∧ x < win t then (1 : Int) else 0 := by
    split <;> norm_num
  unfold marA
  rw [if_pos ⟨hx, h3⟩]
  by_cases hc : costed t = true
  · rw [if_pos ⟨hx, hc⟩]
    rcases lift_cases c hc with ⟨e, _⟩ | ⟨e, _⟩
    · rw [e]
      unfold cost
      linarith
    · rw [e]
      have : (0 : Int) < 2 ^ 32 := by norm_num
      linarith
  · rw [if_neg (fun h => hc h.2)]
    have : (0 : Int) < 2 ^ 32 := by norm_num
    have : (0 : Int) < 2 ^ 37 := by norm_num
    linarith

/-- At the last position, which has no cost: the claim says that the token wins. -/
theorem marA_last (hreq : Request.ok = true) {c : NCells} (A : Fair c) {t x : Nat} (hx : x < V)
    (h3 : checked t = true) (hc : ¬ costed t = true) : 0 ≤ marA c x t := by
  have hg := le_gap c.toCells t hx
  have hr := hreq
  unfold Request.ok at hr
  have h3' := h3
  unfold checked at h3'
  have hc' := hc
  unfold costed at hc'
  rw [h3] at hc'
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.true_and] at hr h3' hc'
  have e1 : e = T := by omega
  have e2 : t = T - 1 := by omega
  have h0 := A.claim.c e1
  rw [← e2] at h0
  have ht : (if checked t = true ∧ x < win t then (1 : Int) else 0) =
      if x < win t then 1 else 0 := by simp [h3]
  unfold marA
  rw [if_pos ⟨hx, h3⟩, if_neg (fun h => hc h.2), ht]
  linarith

theorem rangeA {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) (x t : Nat) :
    0 ≤ marA c x t ∧ marA c x t < (2 ^ 16 + 1) * 2 ^ (sh + 15) := by
  have hpos : (0 : Int) < (2 ^ 16 + 1) * 2 ^ (sh + 15) := by positivity
  by_cases h1 : x < V
  · by_cases h3 : checked t = true
    · refine ⟨?_, marA_hi hplan hreq A h1 h3⟩
      by_cases hc : costed t = true
      · exact le_trans (by positivity) (liftedA hplan hreq A h1 hc)
      · exact marA_last hreq A h1 h3 hc
    · rw [marA_unchecked c x h3]
      exact ⟨le_refl _, hpos⟩
  · rw [marA_pad hreq hy c t h1]
    exact ⟨le_refl _, hpos⟩

theorem quotA {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) (x t : Nat) :
    0 ≤ marA c x t / 2 ^ sh ∧ marA c x t / 2 ^ sh < (2 ^ 16 + 1) * 2 ^ 15 := by
  obtain ⟨h0, h1⟩ := rangeA hplan hreq hy A x t
  refine ⟨Int.ediv_nonneg h0 (by positivity), Int.ediv_lt_of_lt_mul (by positivity) ?_⟩
  have : ((2 : Int) ^ 16 + 1) * 2 ^ 15 * 2 ^ sh = (2 ^ 16 + 1) * 2 ^ (sh + 15) := by
    rw [pow_add]
    ring
  rw [this]
  exact h1

theorem midA_range {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) (x t : Nat) : 0 ≤ midA c x t ∧ midA c x t < 2 ^ 16 :=
  midD_range (quotA hplan hreq hy A x t).1

theorem topA_range {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) (x t : Nat) : 0 ≤ topA c x t ∧ topA c x t < 2 ^ 16 :=
  topD_range (quotA hplan hreq hy A x t).2

theorem lowA_range (P : PlanFacts) (c : NCells) (x t : Nat) :
    0 ≤ lowA c x t ∧ lowA c x t < 2 ^ 8 := by
  unfold lowA
  have hp : (0 : Int) < 2 ^ sh := by positivity
  refine ⟨Int.emod_nonneg _ hp.ne', lt_of_lt_of_le (Int.emod_lt_of_pos _ hp) ?_⟩
  rcases P.hsh with h | h <;> rw [h] <;> norm_num

theorem midA_pos {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) {c : NCells}
    (A : Fair c) {t x : Nat} (hx : x < V) (hc : costed t = true) : (midA c x t).toNat ≠ 0 := by
  have h := liftedA hplan hreq A hx hc
  have h1 : 1 ≤ marA c x t / 2 ^ sh :=
    Int.le_ediv_of_mul_le (by positivity) (by rw [one_mul]; exact h)
  have := midD_pos h1
  unfold midA
  omega

theorem midA_pad (hreq : Request.ok = true) (hy : y < V) (c : NCells) (t : Nat) {x : Nat}
    (hx : ¬ x < V) : (midA c x t).toNat = 0 := by
  unfold midA
  rw [marA_pad hreq hy c t hx]
  simp [midD_zero]

/-! ## 4. The six numbers -/

theorem paidA_le (c : NCells) (t : Nat) : paidA c t ≤ C := by
  unfold paidA
  split
  · rename_i h
    exact h.2
  · omega

theorem overA_le (c : NCells) (t : Nat) : overA c t ≤ 1 := by
  unfold overA
  split <;> omega

theorem rc_pos {t : Nat} (hc : costed t = true) : 0 < RC := by
  have := (costed_iff_min t).mp hc
  unfold RC
  omega

/-- What a position with a cost adds to the mean's sum is its cost, clipped. -/
theorem spentA_cast (c : NCells) {t : Nat} (hc : costed t = true) :
    (spentA c t : Int) = min (cost c.toCells t) (C : Int) := by
  unfold spentA paidA overA
  have e := costA_cast c t
  by_cases h : costA c t ≤ C
  · rw [if_pos ⟨hc, h⟩, if_neg (fun x => by omega), ← e]
    have : (costA c t : Int) ≤ (C : Int) := by exact_mod_cast h
    rw [min_eq_left this]
    simp
  · rw [if_neg (fun x => h x.2), if_pos ⟨hc, by omega⟩, ← e]
    have : (C : Int) ≤ (costA c t : Int) := by
      have : C ≤ costA c t := by omega
      exact_mod_cast this
    rw [min_eq_right this]
    simp

/-- The claim's first clause: the clipped costs add up to at most theta RC. -/
theorem total_le {c : NCells} (A : Fair c) :
    ((Finset.range T).sum fun t => if costed t = true then spentA c t else 0) ≤ theta * RC := by
  have h := A.claim.a
  rw [sumZ_eq] at h
  have e : ((Finset.range T).sum fun t => if costed t = true then min (cost c.toCells t) (C : Int)
      else 0) = (((Finset.range T).sum fun t => if costed t = true then spentA c t else 0 : Nat)
        : Int) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split
    · rename_i hc
      rw [spentA_cast c hc]
    · simp
  rw [e] at h
  exact_mod_cast h

theorem filter_len (p : Nat → Bool) (n : Nat) :
    ((List.range n).filter p).length =
      (Finset.range n).sum fun t => if p t = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    cases h : p n <;> simp [h]

/-- The claim's second clause: at most cap positions are over. -/
theorem overs_le {c : NCells} (A : Fair c) : oversA c ≤ cap := by
  have h := A.claim.b
  rw [filter_len] at h
  refine le_trans (le_of_eq ?_) h
  unfold oversA
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold overA
  have e := costA_cast c t
  by_cases hc : costed t = true
  · by_cases h2 : C < costA c t
    · have : (C : Int) < cost c.toCells t := by rw [← e]; exact_mod_cast h2
      simp [hc, h2, this]
    · have : ¬ (C : Int) < cost c.toCells t := by rw [← e]; exact_mod_cast h2
      simp [hc, h2, this]
  · simp [hc]

theorem digitA_byte {sT : Nat} (hplan : planOk sT = true) {c : NCells} (A : Fair c) (t : Nat)
    {j : Nat} (hj : j < 21) : digitA c t j < 256 := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, hcap, _⟩ := hp
  have hC := A.clip
  have hV := P.hV2
  have h5 : (256 : Nat) ^ 5 = 2 ^ 40 := by norm_num
  unfold digitA
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
    show 2 ^ 24 - V < 256 ^ 3
    norm_num
    omega

theorem tvA_sum {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true) (hy : y < V)
    {c : NCells} (A : Fair c) {t : Nat} (hc : costed t = true) :
    ((Finset.range JV).sum fun x => tvZ (withAll c).toCells x t) =
      (V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24 := by
  rw [Finset.sum_congr rfl fun x hx => tvZ_withAll c t (Finset.mem_range.mp hx)]
  have hJ : JV = V + (JV - V) := by
    have := V_le_JV
    omega
  conv_lhs => rw [hJ]
  rw [Finset.sum_range_add]
  have e1 : ∀ x ∈ Finset.range V, ((stepTab (midA c x t).toNat : Nat) : Int) = 1 := by
    intro x hx
    unfold stepTab
    rw [if_neg (midA_pos hplan hreq A (Finset.mem_range.mp hx) hc)]
    rfl
  have e2 : ∀ x ∈ Finset.range (JV - V),
      ((stepTab (midA c (V + x) t).toNat : Nat) : Int) = 2 ^ 24 := by
    intro x _
    unfold stepTab
    rw [if_pos (midA_pad hreq hy c t (by omega : ¬ V + x < V))]
    norm_num
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  simp

/-- The mean's equation. -/
theorem meanA_eq {c : NCells} (A : Fair c) :
    ((Finset.range T).sum fun t => if costed t = true then
      (numA c .paid t : Int) + (C : Int) * (numA c .over t : Int) + (numA c .slackMean t : Int)
      else 0) = (theta : Int) * (RC : Int) := by
  have hT := total_le A
  have e1 : ((Finset.range T).sum fun t => if costed t = true then
      (numA c .paid t : Int) + (C : Int) * (numA c .over t : Int) + (numA c .slackMean t : Int)
      else 0) =
      (((Finset.range T).sum fun t => if costed t = true then spentA c t else 0 : Nat) : Int) +
      (Finset.range T).sum fun t => if costed t = true then
        ((share (slackA c) RC (t - r) : Nat) : Int) else 0 := by
    rw [Nat.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split
    · rename_i hc
      show (paidA c t : Int) + (C : Int) * (overA c t : Int) +
        ((if costed t = true then share (slackA c) RC (t - r) else 0 : Nat) : Int) = _
      rw [if_pos hc]
      unfold spentA
      push_cast
      ring
    · simp
  rw [e1, sum_costed_run fun i => ((share (slackA c) RC i : Nat) : Int), ← Nat.cast_sum]
  by_cases h0 : 0 < RC
  · rw [share_sum _ h0]
    unfold slackA
    rw [Nat.cast_sub hT]
    push_cast
    ring
  · have hz : RC = 0 := by omega
    rw [hz] at hT ⊢
    have : ((Finset.range T).sum fun t => if costed t = true then spentA c t else 0) = 0 := by
      omega
    rw [this]
    simp

/-- The count's equation. -/
theorem countA_eq {c : NCells} (A : Fair c) :
    ((Finset.range T).sum fun t => if costed t = true then
      (numA c .over t : Int) + (numA c .slackCap t : Int) else 0) =
      ((if RC > 0 then cap else 0 : Nat) : Int) := by
  have hO := overs_le A
  have e1 : ((Finset.range T).sum fun t => if costed t = true then
      (numA c .over t : Int) + (numA c .slackCap t : Int) else 0) =
      ((oversA c : Nat) : Int) + (Finset.range T).sum fun t => if costed t = true then
        (if t = r then ((cap - oversA c : Nat) : Int) else 0) else 0 := by
    unfold oversA
    rw [Nat.cast_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split
    · show (overA c t : Int) + ((if t = r then cap - oversA c else 0 : Nat) : Int) = _
      unfold oversA
      split <;> simp
    · simp
  rw [e1, sum_costed_first]
  by_cases h0 : RC > 0
  · rw [if_pos h0, if_pos h0, Nat.cast_sub hO]
    ring
  · rw [if_neg h0, if_neg h0]
    have : oversA c = 0 := by
      unfold oversA
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [if_neg fun hc => h0 (rc_pos hc)]
    rw [this]
    simp

/-! ## 5. The relations -/

/-- **THE RELATION IN INTEGERS.** -/
theorem intRel_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) : IntRel (withAll c).toCells stepTab := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hV24, _⟩ := hp
  refine ⟨fun t _ j hj => ?_, fun t _ x hx => ?_, fun t _ x hx => ?_,
    fun t _ x hx => ⟨(topA c x t).toNat, ?_⟩, fun t _ x hx => ?_, fun t _ hc => ?_,
    fun t _ hc => ?_, ?_, ?_⟩
  · rw [show (withAll c).toCells.cell .row (NR + j) t = _ from rowA c t hj]
    have := digitA_byte hplan A t hj
    omega
  · rw [midZ_withAll c t hx]
    exact (midA_range hplan hreq hy A x t).1
  · rw [lowZ_withAll c t hx]
    exact (lowA_range P c x t).1
  · rw [topNum_withAll c t hx, Int.toNat_of_nonneg (topA_range hplan hreq hy A x t).1]
  · rw [tvZ_withAll c t hx, midZ_withAll c t hx]
  · rw [numZ_withAll, numZ_withAll]
    show ((paidA c t : Nat) : Int) + ((C - paidA c t : Nat) : Int) = (C : Int)
    rw [Nat.cast_sub (paidA_le c t)]
    ring
  · rw [numZ_withAll, tvA_sum hplan hreq hy A hc, P.hF]
    show ((2 ^ 24 - V : Nat) : Int) + ((V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24) = _
    rw [Nat.cast_sub hV24]
    push_cast
    ring
  · rw [← meanA_eq A]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withAll, numZ_withAll, numZ_withAll]
  · rw [← countA_eq A]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withAll, numZ_withAll]

theorem small_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18)
    (m : Matrix) (f t : Nat) : ((withAll c).cell m f t).natAbs < 2 ^ 18 := by
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
        (if (midA c ((f - (4 * d + 3 * JV)) % JV) t).toNat = 0 then (127 : Int) else -128)
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
    · split <;> norm_num
    · exact h0
  · exact hs .act f t
  · show (if NR ≤ f ∧ f < NR + 21 then (digitA c t (f - NR) : Int) - 128
      else c.cell .row f t).natAbs < 2 ^ 18
    split
    · rename_i h
      have := digitA_byte hplan A t (j := f - NR) (by omega)
      omega
    · exact hs .row f t

theorem rowT_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (t : Nat) {x : Nat} (hx : x < JV) :
    ∃ u : Nat, u < 2 ^ 16 ∧ midZ (withAll c).toCells x t + 2 ^ 16 * tvZ (withAll c).toCells x t
      = (u : Int) + 2 ^ 16 * (stepTab u : Int) := by
  obtain ⟨h0, h1⟩ := midA_range hplan hreq hy A x t
  refine ⟨(midA c x t).toNat, by omega, ?_⟩
  rw [midZ_withAll c t hx, tvZ_withAll c t hx, Int.toNat_of_nonneg h0]

/-- **THE HEAD's RELATION ON CELLS, WHOLE.** -/
theorem cellRel_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) :
    CellRel (withAll c).toCells stepTab := by
  have P := planFacts hplan
  have hI := intRel_withAll hplan hreq hy A
  obtain ⟨a, b, e⟩ := four_of_int P hI
  have hJ := jva_le (by have := P.hV2; omega)
  refine ⟨small_withAll hplan hreq hy A hs, hI.bytes, fun t ht x hx => ?_, fun t ht x hx => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, a, b, e⟩
  · obtain ⟨h0, h1⟩ := topA_range hplan hreq hy A x t
    refine inBits_of_rd (z := topA c x t) (okE_keyAt _ _ _) ?_ h0 h1
    rw [rd_key_top P hreq hy hx ht, topNum_withAll c t hx]
    push_cast
    rw [← mul_assoc, inv_mul_cancel₀ (two_pow_ne_zero _), one_mul]
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_mid P hx ht) (hI.mid t ht x hx) ?_
    rw [midZ_withAll c t hx]
    exact (midA_range hplan hreq hy A x t).2
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_low P hx ht) (hI.low t ht x hx) ?_
    rw [lowZ_withAll c t hx]
    exact (lowA_range P c x t).2
  · have hx' : x < JVa := hx
    obtain ⟨u, hu, hr⟩ := rowT_withAll hplan hreq hy A t (x := x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableA P hx' ht, hr])
  · have hx' : x < JV - JVa := hx
    obtain ⟨u, hu, hr⟩ := rowT_withAll hplan hreq hy A t (x := JVa + x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableB P hx' ht, hr])

theorem digZ_withAll (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    digZ (withAll c) t n = digZ c t n := by
  unfold digZ
  rw [rowA_low c t hn]

theorem holds_withAll (c : NCells) (h : (dataOf c).Holds) : (dataOf (withAll c)).Holds := by
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
    rw [digZ_withAll c t hn]) k

/-- **THE NORM's RELATION ON CELLS, WHOLE, WHERE IT HOLDS OF c.** -/
theorem cellRelN_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (h : CellRelN c) : CellRelN (withAll c) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero (planFacts hplan).hdS
  have haw : ∀ t x, x < d → awZ (withAll c) t x = awZ c t x := fun t x hx => by
    unfold awZ
    rw [wideA_old c t (by omega), wideA_old c t (by omega)]
  have hrem : ∀ t x, x < d → remZ (withAll c) t x = remZ c t x := fun t x hx => by
    unfold remZ
    rw [wideA_old c t (by omega), wideA_old c t (by omega)]
  have hrec : ∀ t, recZ (withAll c) t = recZ c t := fun t => by
    unfold recZ Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
    rw [b256_congr (fun n hn => digZ_withAll c t hn) 80 3 (by omega),
      b256_congr (fun n hn => digZ_withAll c t hn) 83 3 (by omega)]
  refine ⟨small_withAll hplan hreq hy A h.small, h.smallS, fun t ht v hv => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht j hj => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt _ _ hv) okE_zero
    have e := rd_rowsAt (withAll c) (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht] at e
    have hH := holds_withAll c (holds_of_rows c h.rows) 0 (show 0 < 1 by omega) k hk' t ht
    rw [idAt_eq] at hH
    rw [e, hH, rd_zero]
  · have e : keyNAt (withAll c) (cornerN x t) .remLow = keyNAt c (cornerN x t) .remLow :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remLow ht hd hx, rd_keyN_remLow ht hd hx, hrec, haw t x hx, hrem t x hx]
        rfl)
    rw [e]
    exact h.remLow t ht x hx
  · have e : keyNAt (withAll c) (cornerN x t) .remHigh = keyNAt c (cornerN x t) .remHigh :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remHigh ht hd hx, rd_keyN_remHigh ht hd hx, hrem t x hx])
    rw [e]
    exact h.remHigh t ht x hx
  · have e : keyNAt (withAll c) (cornerN x t) .clamp = keyNAt c (cornerN x t) .clamp :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_clamp ht hd hx, rd_keyN_clamp ht hd hx, haw t x hx]
        rfl)
    rw [e]
    exact h.clamp t ht x hx
  · by_cases h99 : j < 99
    · have e : keyNAt (withAll c) (cornerN j t) .digits = keyNAt c (cornerN j t) .digits :=
        eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
          rw [rd_keyN_digits ht hj, rd_keyN_digits ht hj, digZ_withAll c t h99])
      rw [e]
      exact h.digits t ht j hj
    · have hm : ((mul j : Nat) : Int) = 1 := by
        unfold mul
        have : ∀ a : Nat, a < 99 → (j == a) = false := fun a ha => by simp; omega
        simp [this]
      have hj' : j - NR < 21 := by unfold NR at hj ⊢; omega
      have hjj : NR + (j - NR) = j := by unfold NR; omega
      have hb := digitA_byte hplan A t hj'
      have hz : digZ (withAll c) t j = (digitA c t (j - NR) : Int) := by
        unfold digZ
        rw [← hjj, rowA c t hj', hjj]
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
theorem both_withAll {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : Fair c) (h : CellRelN c) :
    CellRelN (withAll c) ∧ CellRel (withAll c).toCells stepTab ∧ TableOk stepTab ∧
      (dataOf (withAll c)).Holds ∧ (withAll c).Wh = c.Wh ∧
      (∀ t v, logit (withAll c).toCells t v = logit c.toCells t v) ∧
      (∀ n t, numZ (withAll c).toCells n t = (numA c n t : Int)) ∧
      ∀ t, costed t = true →
        numZ (withAll c).toCells .paid t + (C : Int) * numZ (withAll c).toCells .over t =
          min (cost (withAll c).toCells t) (C : Int) :=
  ⟨cellRelN_withAll hplan hreq hy A h, cellRel_withAll hplan hreq hy A h.small,
    tableOk_step (planFacts hplan).hF, holds_withAll c (holds_of_rows c h.rows), rfl,
    fun _ _ => rfl, numZ_withAll c, fun t hc => by
      rw [numZ_withAll, numZ_withAll, cost_withAll, ← spentA_cast c hc]
      show (paidA c t : Int) + (C : Int) * (overA c t : Int) = _
      unfold spentA
      push_cast
      ring⟩

end VerifiableInference.Desc.Kinds.Head.Law
