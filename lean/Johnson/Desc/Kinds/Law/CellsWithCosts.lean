-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CellsWithCosts.lean.
WHAT IT DOES NOT SHOW. A toy: cells written out in Lean, of a model
WHOSE HEAD HAS THE WEIGHTS 0 (every logit is 0) on the stream of zeros, against A TABLE OF TWO
VALUES (stepTab: row 0 holds 2^24, every other row 1): not the format's table of exponentials, no
stored model, no file in scope, not what the prover's program lays. OF THE NORM's OWN RELATION
(CellRelN) ONLY THE 17 IDENTITIES ARE CARRIED OVER TO THE NEW CELLS (Holds): its four keys (among
them the key on all 120 digits) are not shown of them. Three things are asked beyond the tests on
the plan and the request (Admits): the cost is at most theta at every position that has one;
C < 2^40; at a checked position without a cost the token is 0. No soundness, no probability, nothing
on hiding.
WHAT IT IS. CELLS THAT MEET THE OUTPUT HEAD's RELATION ON CELLS (HeadLaw.lean: CellRel), WHOLE, AT A
REQUEST WITH COSTS: so the policy's four forms ask something of the cells and are 0.
  b256_congr, cs_congr, idn_congr   the library's 17 identities read the row's first 99 digits
                    alone.
  dig, dig_sum1 .. dig_sum5, dig_byte   a number in k digits at the radix 256.
  stepTab, costN, headNum, headDigit, withCosts   the example: see their own lines: the prover pays
                    the cost 2^sh, and 1 more where an entry stands in front of the token.
  holds_withCosts   the norm's identities hold of the new cells where they hold of the old.
  numZ_withCosts, midZ_withCosts, lowZ_withCosts, tvZ_withCosts, tv_sum, logit_withCosts   what the
                    new cells spell, in integers.
  costed_iff_min, sum_costed_const, sum_costed_first, costed_first, last_of_lt   the positions with
                    a cost.
  Admits            what is asked beside the tests.
  intRel_withCosts  the relation in integers (Law/Ints.lean: IntRel), all nine clauses.
  four_of_int       from that relation: clip and table are 0 at every corner; mean and count are 0.
  cellRel_withCosts CellRel, all ten clauses: small, bytes, the three digits' ranges, the table's
                    rows in both halves, the two lines, the two sums.
  foldl_max_ite, cost_withCosts   HeadLaw.lean's own cost (gap + 2^sh) at the new cells IS costN:
                    so the hidden number "paid" is the cost.
  cells_with_costs  THERE ARE c : NCells with (dataOf c).Holds, TableOk stepTab, CellRel, IntRel,
                    the four forms 0, the six numbers as headNum says, the weights 0, paid = cost.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Values
import Johnson.Desc.Kinds.Law.Lemma2a
import Johnson.Desc.Kinds.Law.NormJoint
import Johnson.Desc.Kinds.Law.NormHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

/-! ## 1. The library's 17 identities read the row's first 99 digits alone -/

section Congr
open Inst.Model.Ledger
variable {R : Type} [CommRing R] {D D' : ℕ → R}

theorem b256_congr (h : ∀ n, n < 99 → D n = D' n) (a n : ℕ) (ha : a + n ≤ 99) :
    b256 D a n = b256 D' a n := by
  unfold b256
  exact Finset.sum_congr rfl fun l hl => by
    rw [h _ (by have := Finset.mem_range.mp hl; omega)]

theorem cs_congr (h : ∀ n, n < 99 → D n = D' n) (s : ℕ) (hs : s ≤ 9) : cs D s = cs D' s := by
  unfold cs
  rw [h 9 (by omega)]
  by_cases h0 : s = 0
  · rw [if_pos h0, if_pos h0]
  by_cases h9 : s = 9
  · rw [if_neg h0, if_pos h9, if_neg h0, if_pos h9]
  rw [if_neg h0, if_neg h9, if_neg h0, if_neg h9, b256_congr h _ _ (by omega)]

theorem idn_congr (np : Inst.Model.NormPar) (Ws : ℕ → R) (h : ∀ n, n < 99 → D n = D' n) (k : ℕ) :
    idn np Ws D k = idn np Ws D' k := by
  have hsa : sa D = sa D' := by
    unfold sa
    rw [h 58 (by omega), h 59 (by omega), h 60 (by omega), h 61 (by omega)]
  have hs0 : s0 D = s0 D' := h 59 (by omega)
  have hsb : sb D = sb D' := by
    unfold sb
    rw [h 62 (by omega), h 63 (by omega)]
  have hsig : sig D = sig D' := by
    unfold sig
    rw [hsa, hsb]
  have hkc : kc D = kc D' := by
    unfold kc
    rw [h 79 (by omega)]
  have hVlo : Vlo D = Vlo D' := b256_congr h _ _ (by omega)
  have hVhi : Vhi D = Vhi D' := b256_congr h _ _ (by omega)
  have hl1 : l1 D = l1 D' := b256_congr h _ _ (by omega)
  have hh1 : h1 D = h1 D' := b256_congr h _ _ (by omega)
  have hBlo : Blo D = Blo D' := b256_congr h _ _ (by omega)
  have hBhi : Bhi D = Bhi D' := b256_congr h _ _ (by omega)
  have hRlo : Rlo D = Rlo D' := b256_congr h _ _ (by omega)
  have hRhi : Rhi D = Rhi D' := b256_congr h _ _ (by omega)
  have hq1 : q1 D = q1 D' := b256_congr h _ _ (by omega)
  have hrr : rr D = rr D' := b256_congr h _ _ (by omega)
  have hrq : rq D = rq D' := b256_congr h _ _ (by omega)
  unfold idn
  by_cases hk : k < 9
  · rw [if_pos hk, if_pos hk, cs_congr h k (by omega), cs_congr h (k + 1) (by omega),
      h k (by omega)]
  · rw [if_neg hk, if_neg hk, hsa, hs0, hsb, hsig, hkc, hVlo, hVhi, hl1, hh1, hBlo, hBhi, hRlo,
      hRhi, hq1, hrr, hrq]

end Congr

/-! ## 2. Digits -/

/-- Digit l of n in k digits at the radix 256; the last takes what is left. -/
def dig (k n l : Nat) : Nat := if l + 1 < k then n / 256 ^ l % 256 else n / 256 ^ l

theorem dig_sum1 (n : Nat) : (Finset.range 1).sum (fun l => 256 ^ l * dig 1 n l) = n := by
  simp [Finset.sum_range_succ, dig]

theorem dig_sum2 (n : Nat) : (Finset.range 2).sum (fun l => 256 ^ l * dig 2 n l) = n := by
  simp [Finset.sum_range_succ, dig]
  omega

theorem dig_sum3 (n : Nat) : (Finset.range 3).sum (fun l => 256 ^ l * dig 3 n l) = n := by
  simp [Finset.sum_range_succ, dig]
  omega

theorem dig_sum5 (n : Nat) : (Finset.range 5).sum (fun l => 256 ^ l * dig 5 n l) = n := by
  simp [Finset.sum_range_succ, dig]
  omega

theorem dig_byte {k n l : Nat} (hk : 0 < k) (hl : l < k) (hn : n < 256 ^ k) : dig k n l < 256 := by
  unfold dig
  split
  · exact Nat.mod_lt _ (by norm_num)
  · have e : l + 1 = k := by omega
    rw [← e, pow_succ] at hn
    exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hn ⊢)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 3. The cells -/

/-- The table of the example: row 0 holds 2^24, every other row 1. -/
def stepTab (u : Nat) : Nat := if u = 0 then 2 ^ 24 else 1

/-- The cost of position t for a model whose weights are all 0: every logit is 0, so the gap is 1
where a vocabulary entry stands in front of the token (it wins the tie), else 0. -/
def costN (t : Nat) : Nat := 2 ^ sh + if 0 < win t then 1 else 0

/-- The six hidden numbers at position t: THE PROVER PAYS THE COST; nothing is over; the mean's and
the clip's slack are what theta and C leave; the cap's slack lies whole at the first checked
position; the table's slack is what V table values of 1 leave of 2^24. -/
def headNum : Number → Nat → Nat
  | .paid, t => costN t
  | .over, _ => 0
  | .slackMean, t => theta - costN t
  | .slackClip, t => C - costN t
  | .slackCap, t => if t = r then cap else 0
  | .slackTable, _ => 2 ^ 24 - V

/-- Digit j of the head's 21 at position t. -/
def headDigit (t j : Nat) : Nat :=
  if j < 5 then dig 5 (headNum .paid t) j
  else if j < 6 then dig 1 (headNum .over t) (j - 5)
  else if j < 11 then dig 5 (headNum .slackMean t) (j - 6)
  else if j < 16 then dig 5 (headNum .slackClip t) (j - 11)
  else if j < 18 then dig 2 (headNum .slackCap t) (j - 16)
  else dig 3 (headNum .slackTable t) (j - 18)

/-- Cells c with the head's own cells laid anew: its 21 digits of the row; in the wide matrix, from
feature 4 d on: the margins' middle digit (two limbs; 1 at a vocabulary entry of a position with a
cost, else 0), their low digit (there 1 from win t on if win t is not 0, else 0), the table values
(three limbs: there 1, else 2^24). A cell holds its digit less the offset that the text adds at a
vocabulary entry of a checked position. The head's weights are all 0. All else is c's. -/
def withCosts (c : NCells) : NCells :=
  { c with
    Wh := fun _ _ => 0
    cell := fun m f t =>
      match m with
      | .row =>
        if NR ≤ f ∧ f < NR + 21 then (headDigit t (f - NR) : Int) - 128 else c.cell .row f t
      | .wide =>
        if f < 4 * d then c.cell .wide f t
        else if f < 4 * d + JV then
          (if f - 4 * d < V ∧ checked t = true then (if costed t = true then -127 else -128)
            else 0)
        else if f < 4 * d + 2 * JV then
          (if f - (4 * d + JV) < V ∧ checked t = true then -128 else 0)
        else if f < 4 * d + 3 * JV then
          (if f - (4 * d + 2 * JV) < V ∧ checked t = true then
            (if costed t = true ∧ 0 < win t ∧ ¬ f - (4 * d + 2 * JV) < win t then -127 else -128)
            else 0)
        else if f < 4 * d + 6 * JV then
          (if (f - (4 * d + 3 * JV)) % JV < V ∧ costed t = true then -128 else 127)
        else c.cell .wide f t
      | .act => c.cell .act f t }

theorem cell_row (c : NCells) (t : Nat) {j : Nat} (hj : j < 21) :
    (withCosts c).cell .row (NR + j) t = (headDigit t j : Int) - 128 := by
  show (if NR ≤ NR + j ∧ NR + j < NR + 21 then (headDigit t (NR + j - NR) : Int) - 128
    else c.cell .row (NR + j) t) = _
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem cell_row_low (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    (withCosts c).cell .row n t = c.cell .row n t := by
  show (if NR ≤ n ∧ n < NR + 21 then (headDigit t (n - NR) : Int) - 128
    else c.cell .row n t) = _
  rw [if_neg (by unfold NR; omega)]

/-- **The norm's identities hold of the new cells where they hold of the old.** -/
theorem holds_withCosts (c : NCells) (h : (dataOf c).Holds) : (dataOf (withCosts c)).Holds := by
  intro i hi k hk t ht
  obtain rfl : i = 0 := by
    have : i < 1 := hi
    omega
  have e := h 0 hi k hk t ht
  rw [idAt_eq] at e ⊢
  rw [← e]
  unfold vecK
  exact idn_congr _ _ (fun n hn => by
    unfold dK digZ
    rw [cell_row_low c t hn]) k

/-- A sum of k digits that begin at digit a of the 21. -/
theorem num_sum (c : NCells) (t a k N : Nat) (hak : a + k ≤ 21)
    (hd : ∀ l, l < k → headDigit t (a + l) = dig k N l)
    (hs : (Finset.range k).sum (fun l => 256 ^ l * dig k N l) = N) :
    ((Finset.range k).sum fun l =>
      (256 : Int) ^ l * ((withCosts c).cell .row (NR + a + l) t + 128)) = (N : Int) := by
  rw [← hs]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [Nat.add_assoc, cell_row c t (by omega), hd l hl']
  ring

theorem numZ_withCosts (c : NCells) (n : Number) (t : Nat) :
    numZ (withCosts c).toCells n t = (headNum n t : Int) := by
  unfold numZ
  cases n
  · exact num_sum c t 0 5 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_pos (by omega), Nat.zero_add]) (dig_sum5 _)
  · exact num_sum c t 5 1 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum1 _)
  · exact num_sum c t 6 5 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left])
      (dig_sum5 _)
  · exact num_sum c t 11 5 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left]) (dig_sum5 _)
  · exact num_sum c t 16 2 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum2 _)
  · exact num_sum c t 18 3 _ (by omega) (fun l hl => by
      unfold headDigit
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), Nat.add_sub_cancel_left]) (dig_sum3 _)

theorem wide_mid0 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withCosts c).cell .wide (4 * d + x) t =
      if x < V ∧ checked t = true then (if costed t = true then -127 else -128) else 0 := by
  show (if 4 * d + x < 4 * d then c.cell .wide (4 * d + x) t
    else if 4 * d + x < 4 * d + JV then
      (if 4 * d + x - 4 * d < V ∧ checked t = true then
        (if costed t = true then (-127 : Int) else -128) else 0)
    else _) = _
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wide_mid1 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withCosts c).cell .wide (4 * d + JV + x) t =
      if x < V ∧ checked t = true then -128 else 0 := by
  show (if 4 * d + JV + x < 4 * d then c.cell .wide (4 * d + JV + x) t
    else if 4 * d + JV + x < 4 * d + JV then _
    else if 4 * d + JV + x < 4 * d + 2 * JV then
      (if 4 * d + JV + x - (4 * d + JV) < V ∧ checked t = true then (-128 : Int) else 0)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wide_low (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withCosts c).cell .wide (4 * d + 2 * JV + x) t =
      if x < V ∧ checked t = true then
        (if costed t = true ∧ 0 < win t ∧ ¬ x < win t then -127 else -128) else 0 := by
  show (if 4 * d + 2 * JV + x < 4 * d then c.cell .wide (4 * d + 2 * JV + x) t
    else if 4 * d + 2 * JV + x < 4 * d + JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 2 * JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 3 * JV then
      (if 4 * d + 2 * JV + x - (4 * d + 2 * JV) < V ∧ checked t = true then
        (if costed t = true ∧ 0 < win t ∧ ¬ 4 * d + 2 * JV + x - (4 * d + 2 * JV) < win t then
          (-127 : Int) else -128) else 0)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem wide_tv (c : NCells) (t : Nat) {l x : Nat} (hl : l < 3) (hx : x < JV) :
    (withCosts c).cell .wide (4 * d + (3 + l) * JV + x) t =
      if x < V ∧ costed t = true then -128 else 127 := by
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
      (if (4 * d + (3 + l) * JV + x - (4 * d + 3 * JV)) % JV < V ∧ costed t = true then
        (-128 : Int) else 127)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2, e,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem midZ_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    midZ (withCosts c).toCells x t = if x < V ∧ costed t = true then 1 else 0 := by
  unfold midZ off2
  rw [show (withCosts c).toCells.cell .wide (4 * d + x) t = _ from wide_mid0 c t hx,
    show (withCosts c).toCells.cell .wide (4 * d + JV + x) t = _ from wide_mid1 c t hx]
  by_cases h1 : x < V
  · by_cases h2 : costed t = true
    · simp [h1, h2, checked_of_costed h2]
    · by_cases h3 : checked t = true <;> simp [h1, h2, h3]
  · simp [h1]

theorem lowZ_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    lowZ (withCosts c).toCells x t =
      if x < V ∧ costed t = true ∧ 0 < win t ∧ ¬ x < win t then 1 else 0 := by
  unfold lowZ off1
  rw [show (withCosts c).toCells.cell .wide (4 * d + 2 * JV + x) t = _ from wide_low c t hx]
  by_cases h1 : x < V
  · by_cases h2 : costed t = true
    · by_cases h4 : x < win t <;> by_cases h5 : 0 < win t <;>
        simp [h1, h2, h4, h5, checked_of_costed h2]
    · by_cases h3 : checked t = true <;> simp [h1, h2, h3]
  · simp [h1]

theorem tvZ_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    tvZ (withCosts c).toCells x t = if x < V ∧ costed t = true then 1 else 2 ^ 24 := by
  unfold tvZ offE
  rw [Finset.sum_congr rfl fun l hl => by
    rw [show (withCosts c).toCells.cell .wide (4 * d + (3 + l) * JV + x) t =
      if x < V ∧ costed t = true then (-128 : Int) else 127 from
        wide_tv c t (Finset.mem_range.mp hl) hx]]
  by_cases h : x < V ∧ costed t = true
  · rw [if_pos h, if_pos h]
    simp [Finset.sum_range_succ]
  · rw [if_neg h, if_neg h]
    simp [Finset.sum_range_succ]

theorem tv_sum (c : NCells) {t : Nat} (hc : costed t = true) :
    ((Finset.range JV).sum fun x => tvZ (withCosts c).toCells x t) =
      (V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24 := by
  rw [Finset.sum_congr rfl fun x hx => tvZ_withCosts c t (Finset.mem_range.mp hx)]
  have hJ : JV = V + (JV - V) := by
    have := V_le_JV
    omega
  conv_lhs => rw [hJ]
  rw [Finset.sum_range_add]
  rw [Finset.sum_congr rfl fun x hx => if_pos ⟨Finset.mem_range.mp hx, hc⟩,
    Finset.sum_congr rfl fun x _ => if_neg (by omega : ¬ (V + x < V ∧ costed t = true))]
  simp

/-! ## 4. Sums over the positions with a cost -/

theorem costed_iff_min (t : Nat) : costed t = true ↔ r ≤ t ∧ t < min e (T - 1) := by
  unfold costed checked
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem sum_costed_const (a : Int) :
    ((Finset.range T).sum fun t => if costed t = true then a else 0) = a * (RC : Int) := by
  rw [← Finset.sum_filter, Finset.sum_const]
  have : (Finset.range T).filter (fun t => costed t = true) = Finset.Ico r (min e (T - 1)) := by
    ext t
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, costed_iff_min]
    omega
  rw [this, Nat.card_Ico]
  unfold RC
  simp [mul_comm]

theorem sum_costed_first (a : Int) :
    ((Finset.range T).sum fun t => if costed t = true then (if t = r then a else 0) else 0) =
      if RC > 0 then a else 0 := by
  by_cases h : RC > 0
  · have hr : costed r = true := (costed_iff_min r).mpr ⟨le_refl _, by unfold RC at h; omega⟩
    have hT : r < T := by
      have := ((costed_iff_min r).mp hr).2
      omega
    rw [if_pos h, Finset.sum_eq_single r]
    · rw [if_pos hr, if_pos rfl]
    · intro b _ hb
      rw [if_neg hb]
      simp
    · intro hn
      exact absurd (Finset.mem_range.mpr hT) hn
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t _ => ?_
    have : ¬ costed t = true := fun hc => by
      have := (costed_iff_min t).mp hc
      unfold RC at h
      omega
    rw [if_neg this]

theorem costed_first (h1 : r < e) (h2 : r + 1 < T) : costed r = true :=
  (costed_iff_min r).mpr ⟨le_refl _, by omega⟩

/-- Where the last position is not checked every checked position has a cost. -/
theorem last_of_lt (he : e < T) : ∀ t, checked t = true → costed t = false → win t = 0 := by
  intro t h1 h2
  exfalso
  have : costed t = true := by
    unfold costed
    unfold checked at h1 ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1 ⊢
    omega
  rw [this] at h2
  cases h2

/-! ## 5. The relation in integers -/

theorem sumZ_zero (n : Nat) : sumZ n (fun _ => (0 : Int)) = 0 := by
  unfold sumZ
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem logit_withCosts (c : NCells) (t v : Nat) : logit (withCosts c).toCells t v = 0 := by
  unfold logit
  have : (fun k => act (withCosts c).toCells t k * (withCosts c).toCells.Wh k v) =
      fun _ => (0 : Int) := funext fun k => mul_zero _
  rw [this, sumZ_zero]

theorem tableOk_step (hF : F = 24) : TableOk stepTab := by
  refine ⟨by rw [hF]; rfl, fun u => ?_⟩
  rw [hF]
  unfold stepTab
  split <;> norm_num

/-- What is asked of the plan and the request beyond their own tests, for this example. -/
structure Admits : Prop where
  /-- the policy admits the cost at every position that has one -/
  pay : ∀ t, costed t = true → costN t ≤ theta
  /-- the clip's slack fits its five digits -/
  clip : C < 2 ^ 40
  /-- at a checked position without a cost (the last) the token is the first of the vocabulary: with
  all logits 0 no other wins the ties -/
  last : ∀ t, checked t = true → costed t = false → win t = 0

theorem headDigit_byte {sT : Nat} (hplan : planOk sT = true) (A : Admits) (t : Nat) {j : Nat}
    (hj : j < 21) : headDigit t j < 256 := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, hcap, _⟩ := hp
  have hC := A.clip
  have hV := P.hV2
  have h5 : (256 : Nat) ^ 5 = 2 ^ 40 := by norm_num
  unfold headDigit
  split
  · refine dig_byte (by omega) (by omega) ?_
    show (2 ^ sh + if 0 < win t then 1 else 0) < 256 ^ 5
    rcases P.hsh with h | h <;> rw [h] <;> split <;> norm_num
  split
  · exact dig_byte (by omega) (by omega) (by show 0 < 256 ^ 1; norm_num)
  split
  · refine dig_byte (by omega) (by omega) ?_
    show theta - costN t < 256 ^ 5
    rw [h5]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hth hC)
  split
  · refine dig_byte (by omega) (by omega) ?_
    show C - costN t < 256 ^ 5
    rw [h5]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hC
  split
  · refine dig_byte (by omega) (by omega) ?_
    show (if t = r then cap else 0) < 256 ^ 2
    split
    · norm_num
      exact hcap
    · norm_num
  · refine dig_byte (by omega) (by omega) ?_
    show 2 ^ 24 - V < 256 ^ 3
    norm_num
    omega

/-- **THE RELATION IN INTEGERS HOLDS OF THE NEW CELLS.** -/
theorem intRel_withCosts {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) (A : Admits) (c : NCells) : IntRel (withCosts c).toCells stepTab := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hV24, _⟩ := hp
  have hpay := A.pay
  refine ⟨fun t _ j hj => ?_, fun t _ x hx => ?_, fun t _ x hx => ?_, fun t _ x hx => ⟨0, ?_⟩,
    fun t _ x hx => ?_, fun t _ hc => ?_, fun t _ hc => ?_, ?_, ?_⟩
  · rw [show (withCosts c).toCells.cell .row (NR + j) t = _ from cell_row c t hj]
    have := headDigit_byte hplan A t hj
    omega
  · rw [midZ_withCosts c t hx]
    split <;> norm_num
  · rw [lowZ_withCosts c t hx]
    split <;> norm_num
  · unfold topNum liftZ
    rw [logit_withCosts, logit_withCosts, numZ_withCosts, numZ_withCosts, midZ_withCosts c t hx,
      lowZ_withCosts c t hx]
    have hw := win_lt hreq hy t
    show (if x < V ∧ checked t = true then (0 : Int) - 0 else 0) +
      (if x < V ∧ costed t = true then ((2 ^ sh + (if 0 < win t then 1 else 0) : Nat) : Int) +
        (BIG : Int) * ((0 : Nat) : Int) else 0) - (if checked t = true ∧ x < win t then 1 else 0) -
      2 ^ sh * (if x < V ∧ costed t = true then 1 else 0) -
      (if x < V ∧ costed t = true ∧ 0 < win t ∧ ¬ x < win t then 1 else 0) =
        2 ^ (sh + 15) * ((0 : Nat) : Int)
    by_cases h1 : x < V
    · by_cases h2 : costed t = true
      · have h3 := checked_of_costed h2
        by_cases h4 : x < win t
        · have h5 : 0 < win t := by omega
          simp [h1, h2, h3, h4, h5]
        · by_cases h5 : 0 < win t <;> simp [h1, h2, h3, h4, h5]
      · by_cases h3 : checked t = true
        · have h5 : win t = 0 := A.last t h3 (by simpa using h2)
          simp [h1, h2, h3, h5]
        · simp [h1, h2, h3]
    · have h4 : ¬ x < win t := by omega
      simp [h1, h4]
  · rw [tvZ_withCosts c t hx, midZ_withCosts c t hx]
    by_cases h : x < V ∧ costed t = true
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
      rfl
  · rw [numZ_withCosts, numZ_withCosts]
    show ((costN t : Nat) : Int) + ((C - costN t : Nat) : Int) = (C : Int)
    rw [Nat.cast_sub (le_trans (hpay t hc) hth)]
    ring
  · rw [numZ_withCosts, tv_sum c hc, P.hF]
    show ((2 ^ 24 - V : Nat) : Int) + ((V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24) = _
    rw [Nat.cast_sub hV24]
    push_cast
    ring
  · rw [← sum_costed_const]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withCosts, numZ_withCosts, numZ_withCosts]
    show (if costed t = true then ((costN t : Nat) : Int) + (C : Int) * ((0 : Nat) : Int) +
      ((theta - costN t : Nat) : Int) else 0) = _
    split
    · rename_i hc
      rw [Nat.cast_sub (hpay t hc)]
      push_cast
      ring
    · rfl
  · have e : (((if RC > 0 then cap else 0 : Nat)) : Int) = if RC > 0 then (cap : Int) else 0 := by
      split <;> simp
    rw [e, ← sum_costed_first]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withCosts, numZ_withCosts]
    show (if costed t = true then ((0 : Nat) : Int) + ((if t = r then cap else 0 : Nat) : Int)
      else 0) = _
    by_cases h : t = r <;> simp [h]

/-! ## 6. The policy's four forms, as elements -/

theorem zero_of_rd' {x : E} (hx : okE x = true) (h : rd x = 0) : x = 0 :=
  eq_of_rd hx okE_zero (h.trans rd_zero.symm)

/-- Where the relation in integers holds, the policy's four forms are 0. -/
theorem four_of_int (P : PlanFacts) {c : Cells} {tab : Nat → Nat} (h : IntRel c tab) :
    (∀ t, t < T → clipAt c (corner 0 t) = 0 ∧ tableAt c (corner 0 t) = 0) ∧
    meanAt c = 0 ∧ countAt c = 0 := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, ?_, ?_⟩
  · apply zero_of_rd' (okE_clipAt _ _)
    rw [rd_clip ht]
    split
    · rename_i hc
      rw [h.clip t ht hc]
      simp
    · rfl
  · apply zero_of_rd' (okE_tableAt _ _)
    rw [rd_table P ht]
    split
    · rename_i hc
      rw [h.table t ht hc]
      simp
    · rfl
  · apply zero_of_rd' (show okE (meanAt c) = true from okE_addMul _ _ _)
    rw [rd_mean, h.mean]
    simp
  · apply zero_of_rd' (show okE (countAt c) = true from okE_addMul _ _ _)
    rw [rd_count, h.count]
    simp

/-! ## 7. The relation on cells, whole -/

/-- JVa_le (Law/Clamp.lean), typed again: that file stands above this one's needs. -/
theorem jva_le (hV : 0 < V) : JVa ≤ JV := by
  have hJ : 0 < JV := lt_of_lt_of_le hV V_le_JV
  unfold JVa clog2
  split
  · simp; omega
  · rename_i h
    have h1 : JV - 1 ≠ 0 := by omega
    have := Nat.log2_self_le h1
    simp only [Nat.add_sub_cancel]
    omega

theorem isRow_of_rd {tab : Nat → Nat} {v : E} {u : Nat} (hv : okE v = true) (hu : u < 2 ^ 16)
    (hr : rd v = (((u : Int) + 2 ^ 16 * (tab u : Int) : Int) : K)) : IsRow tab v := by
  refine ⟨u, hu, eq_of_rd hv (okE_natE _) ?_⟩
  rw [hr]
  show _ = rd ((u + 2 ^ 16 * tab u : Nat) : E)
  rw [rd_natCast]
  push_cast
  rfl

theorem row_withCosts (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    ∃ u : Nat, u < 2 ^ 16 ∧ midZ (withCosts c).toCells x t + 2 ^ 16 * tvZ (withCosts c).toCells x t
      = (u : Int) + 2 ^ 16 * (stepTab u : Int) := by
  rw [midZ_withCosts c t hx, tvZ_withCosts c t hx]
  by_cases h : x < V ∧ costed t = true
  · exact ⟨1, by norm_num, by rw [if_pos h, if_pos h]; rfl⟩
  · exact ⟨0, by norm_num, by rw [if_neg h, if_neg h]; rfl⟩

theorem small_withCosts {sT : Nat} (hplan : planOk sT = true) (A : Admits) (c : NCells)
    (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) (m : Matrix) (f t : Nat) :
    ((withCosts c).cell m f t).natAbs < 2 ^ 18 := by
  cases m
  · show (if f < 4 * d then c.cell .wide f t
      else if f < 4 * d + JV then
        (if f - 4 * d < V ∧ checked t = true then (if costed t = true then (-127 : Int) else -128)
          else 0)
      else if f < 4 * d + 2 * JV then
        (if f - (4 * d + JV) < V ∧ checked t = true then -128 else 0)
      else if f < 4 * d + 3 * JV then
        (if f - (4 * d + 2 * JV) < V ∧ checked t = true then
          (if costed t = true ∧ 0 < win t ∧ ¬ f - (4 * d + 2 * JV) < win t then -127 else -128)
          else 0)
      else if f < 4 * d + 6 * JV then
        (if (f - (4 * d + 3 * JV)) % JV < V ∧ costed t = true then -128 else 127)
      else c.cell .wide f t).natAbs < 2 ^ 18
    have h0 := hs .wide f t
    repeat' split
    all_goals first | exact h0 | norm_num
  · exact hs .act f t
  · show (if NR ≤ f ∧ f < NR + 21 then (headDigit t (f - NR) : Int) - 128
      else c.cell .row f t).natAbs < 2 ^ 18
    split
    · rename_i h
      have := headDigit_byte hplan A t (j := f - NR) (by omega)
      omega
    · exact hs .row f t

/-- **THE HEAD's RELATION ON CELLS (HeadLaw.lean: CellRel) HOLDS OF THE NEW CELLS, WHOLE.** -/
theorem cellRel_withCosts {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) (A : Admits) (c : NCells) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) :
    CellRel (withCosts c).toCells stepTab := by
  have P := planFacts hplan
  have hI := intRel_withCosts hplan hreq hy A c
  obtain ⟨a, b, e⟩ := four_of_int P hI
  have hJ := jva_le (by have := P.hV2; omega)
  refine ⟨small_withCosts hplan A c hs, hI.bytes, fun t ht x hx => ?_, fun t ht x hx => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, a, b, e⟩
  · obtain ⟨n, hn⟩ := hI.top t ht x hx
    have h0 : topNum (withCosts c).toCells x t = 0 := by
      -- the witness of intRel_withCosts is 0; here it is had again from the two sizes
      unfold topNum liftZ
      rw [logit_withCosts, logit_withCosts, numZ_withCosts, numZ_withCosts,
        midZ_withCosts c t hx, lowZ_withCosts c t hx]
      have hw := win_lt hreq hy t
      show (if x < V ∧ checked t = true then (0 : Int) - 0 else 0) +
        (if x < V ∧ costed t = true then ((2 ^ sh + (if 0 < win t then 1 else 0) : Nat) : Int) +
          (BIG : Int) * ((0 : Nat) : Int) else 0) -
        (if checked t = true ∧ x < win t then 1 else 0) -
        2 ^ sh * (if x < V ∧ costed t = true then 1 else 0) -
        (if x < V ∧ costed t = true ∧ 0 < win t ∧ ¬ x < win t then 1 else 0) = 0
      by_cases h1 : x < V
      · by_cases h2 : costed t = true
        · have h3 := checked_of_costed h2
          by_cases h4 : x < win t
          · have h5 : 0 < win t := by omega
            simp [h1, h2, h3, h4, h5]
          · by_cases h5 : 0 < win t <;> simp [h1, h2, h3, h4, h5]
        · by_cases h3 : checked t = true
          · have h5 : win t = 0 := A.last t h3 (by simpa using h2)
            simp [h1, h2, h3, h5]
          · simp [h1, h2, h3]
      · have h4 : ¬ x < win t := by omega
        simp [h1, h4]
    refine inBits_of_rd (z := 0) (okE_keyAt _ _ _) ?_ (le_refl _) (by norm_num)
    rw [rd_key_top P hreq hy hx ht, h0]
    simp
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_mid P hx ht) (hI.mid t ht x hx) ?_
    rw [midZ_withCosts c t hx]
    split <;> norm_num
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_low P hx ht) (hI.low t ht x hx) ?_
    rw [lowZ_withCosts c t hx]
    split <;> norm_num
  · have hx' : x < JVa := hx
    obtain ⟨u, hu, hr⟩ := row_withCosts c t (x := x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableA P hx' ht, hr])
  · have hx' : x < JV - JVa := hx
    obtain ⟨u, hu, hr⟩ := row_withCosts c t (x := JVa + x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableB P hx' ht, hr])

/-! ## 8. costN is the text's own cost at these cells -/

theorem foldl_max_ite (p : Nat → Prop) [DecidablePred p] (n : Nat) :
    (List.range n).foldl (fun (m : Int) v => max m (if p v then 1 else 0)) 0 =
      if ∃ v, v < n ∧ p v then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    show max (if ∃ v, v < n ∧ p v then (1 : Int) else 0) (if p n then 1 else 0) = _
    by_cases h1 : ∃ v, v < n ∧ p v
    · have hB : ∃ v, v < n + 1 ∧ p v := by
        obtain ⟨v, hv, hp⟩ := h1
        exact ⟨v, by omega, hp⟩
      rw [if_pos h1, if_pos hB]
      split <;> norm_num
    · rw [if_neg h1]
      by_cases h2 : p n
      · have hB : ∃ v, v < n + 1 ∧ p v := ⟨n, by omega, h2⟩
        rw [if_pos h2, if_pos hB]
        norm_num
      · have hB : ¬ ∃ v, v < n + 1 ∧ p v := by
          rintro ⟨v, hv, hp⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
          · exact h1 ⟨v, h, hp⟩
          · exact h2 (h ▸ hp)
        rw [if_neg h2, if_neg hB]
        norm_num

/-- **HeadLaw.lean's cost at the new cells is costN.** -/
theorem cost_withCosts (hV : 0 < V) (c : NCells) (t : Nat) :
    cost (withCosts c).toCells t = (costN t : Int) := by
  unfold cost gap costN
  have e : (fun (m : Int) v => max m (logit (withCosts c).toCells t v -
      logit (withCosts c).toCells t (win t) + if v < win t then 1 else 0)) =
      fun (m : Int) v => max m (if v < win t then 1 else 0) := by
    funext m v
    rw [logit_withCosts, logit_withCosts]
    simp
  rw [e, foldl_max_ite]
  by_cases h : 0 < win t
  · have hB : ∃ v, v < V ∧ v < win t := ⟨0, hV, h⟩
    rw [if_pos hB, if_pos h]
    push_cast
    ring
  · have hB : ¬ ∃ v, v < V ∧ v < win t := by
      rintro ⟨v, _, hv⟩
      omega
    rw [if_neg hB, if_neg h]
    push_cast
    ring

/-- **THERE ARE CELLS AT WHICH THE NORM's IDENTITIES HOLD, THE HEAD's RELATION ON CELLS HOLDS WHOLE,
AND THE POLICY's FOUR FORMS ARE 0: AT EVERY REQUEST THAT THE EXAMPLE ADMITS, WITH COSTS OR NOT.** -/
theorem cells_with_costs {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) (A : Admits) :
    ∃ c : NCells, (dataOf c).Holds ∧ TableOk stepTab ∧ CellRel c.toCells stepTab ∧
      IntRel c.toCells stepTab ∧
      (∀ t, t < T → clipAt c.toCells (corner 0 t) = 0 ∧ tableAt c.toCells (corner 0 t) = 0) ∧
      meanAt c.toCells = 0 ∧ countAt c.toCells = 0 ∧
      (∀ n t, numZ c.toCells n t = (headNum n t : Int)) ∧ (∀ k v, c.Wh k v = 0) ∧
      ∀ t, numZ c.toCells .paid t = cost c.toCells t := by
  obtain ⟨c, hc⟩ := cellRelN_met hplan
  have P := planFacts hplan
  have hI := intRel_withCosts hplan hreq hy A c
  obtain ⟨a, b, e⟩ := four_of_int P hI
  exact ⟨withCosts c, holds_withCosts c (holds_of_rows c hc.rows), tableOk_step P.hF,
    cellRel_withCosts hplan hreq hy A c hc.small, hI, a, b, e, numZ_withCosts c, fun _ _ => rfl,
    fun t => by
      rw [numZ_withCosts, cost_withCosts (by have := P.hV2; omega)]
      rfl⟩

end VerifiableInference.Desc.Kinds.Head.Law
