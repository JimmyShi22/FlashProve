--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsFromLogits.lean.
WHAT IT DOES NOT SHOW. A TOY: cells written out in Lean; no file in
scope; not what the prover's program lays. AGAINST A TABLE OF TWO VALUES (Law/CellsWithCosts.lean:
stepTab), not the format's table of exponentials: so the cost is the text's gap + 2^sh and no sum of
exponentials is exercised. THAT CELLS WITH LOGITS THAT ARE NOT 0 MEET ITS PREMISES (CellRelN c;
AdmitsG c) IS NOT SHOWN HERE: the one c that is known to meet CellRelN has activations 0. The top
digit is always 0 (AdmitsG asks that a lifted margin fits the two lower digits); nothing is ever
"over". No soundness, no probability, nothing on hiding.
WHAT IT IS. THE HEAD's OWN CELLS, LAID OF THE LOGITS, FOR ANY ACTIVATIONS AND ANY WEIGHTS: Law/
CellsWithCosts.lean's example with its two letters freed.
  foldl_max_ge, gap_nonneg, le_gap   the text's gap is at least 0 and at least every entry's term.
  paidG, numG, digitG, marG, midN, lowN, o2, o1, withHead   the cells: the prover pays the cost; a
                    lifted margin is cut at 2^sh into a low and a middle digit; the table value is
                    stepTab's at the middle digit.
  logit_withHead, cost_withHead   BY rfl: the logits and the cost are c's.
  numZ | midZ | lowZ | tvZ _withHead, topNum_withHead   what the new cells spell; the top digit's
                    number is 0 WITHOUT ANY PREMISE.
  lifted            at a position with a cost every entry's lifted margin is at least 2^sh: no
                    premise: it is what paying the gap buys.
  AdmitsG           what is asked: the lifted margins' range; cost <= theta; C < 2^40.
  intRel_withHead, cellRel_withHead, cellRelN_withHead, holds_withHead, both_withHead   IntRel;
                    CellRel whole; CellRelN whole where it holds of c; Holds; all together, with
                    paid = cost at every position that has one.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsWithCostsNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-! ## 1. The gap -/

theorem foldl_max_ge (f : Nat → Int) : ∀ (l : List Nat) (a : Int),
    a ≤ l.foldl (fun m v => max m (f v)) a ∧ ∀ v ∈ l, f v ≤ l.foldl (fun m v => max m (f v)) a
  | [], a => ⟨le_refl _, fun v hv => by simp at hv⟩
  | w :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge f l (max a (f w))
    refine ⟨le_trans (le_max_left _ _) h1, fun v hv => ?_⟩
    rcases List.mem_cons.mp hv with h | h
    · rw [h]
      exact le_trans (le_max_right _ _) h1
    · exact h2 v h

theorem gap_nonneg (c : Cells) (t : Nat) : 0 ≤ gap c t := (foldl_max_ge _ _ 0).1

theorem le_gap (c : Cells) (t : Nat) {v : Nat} (hv : v < V) :
    logit c t v - logit c t (win t) + (if v < win t then 1 else 0) ≤ gap c t :=
  (foldl_max_ge _ _ 0).2 v (List.mem_range.mpr hv)

/-! ## 2. The head's own cells, of the logits -/

/-- What the prover pays at a position with a cost: the cost. -/
def paidG (c : NCells) (t : Nat) : Nat := if costed t = true then (cost c.toCells t).toNat else 0

theorem paidG_cast (c : NCells) {t : Nat} (h : costed t = true) :
    (paidG c t : Int) = cost c.toCells t := by
  unfold paidG
  rw [if_pos h, Int.toNat_of_nonneg]
  unfold cost
  have := gap_nonneg c.toCells t
  positivity

/-- The six hidden numbers. -/
def numG (c : NCells) : Number → Nat → Nat
  | .paid, t => paidG c t
  | .over, _ => 0
  | .slackMean, t => theta - paidG c t
  | .slackClip, t => C - paidG c t
  | .slackCap, t => if t = r then cap else 0
  | .slackTable, _ => 2 ^ 24 - V

def digitG (c : NCells) (t j : Nat) : Nat :=
  if j < 5 then dig 5 (numG c .paid t) j
  else if j < 6 then dig 1 (numG c .over t) (j - 5)
  else if j < 11 then dig 5 (numG c .slackMean t) (j - 6)
  else if j < 16 then dig 5 (numG c .slackClip t) (j - 11)
  else if j < 18 then dig 2 (numG c .slackCap t) (j - 16)
  else dig 3 (numG c .slackTable t) (j - 18)

/-- The margin of entry x at position t, lifted by what is paid. -/
def marG (c : NCells) (x t : Nat) : Int :=
  (if x < V ∧ checked t = true then logit c.toCells t (win t) - logit c.toCells t x else 0)
    + (if x < V ∧ costed t = true then (paidG c t : Int) else 0)
    - (if checked t = true ∧ x < win t then 1 else 0)

/-- Its middle digit (all above the low one) and its low digit. -/
def midN (c : NCells) (x t : Nat) : Int := marG c x t / 2 ^ sh
@[inherit_doc midN] def lowN (c : NCells) (x t : Nat) : Int := marG c x t % 2 ^ sh

/-- The offsets that the text adds at a vocabulary entry of a checked position. -/
def o2 (x t : Nat) : Int := if x < V ∧ checked t = true then 32896 else 0
@[inherit_doc o2] def o1 (x t : Nat) : Int := if x < V ∧ checked t = true then 128 else 0

/-- Cells c with the head's own cells laid anew, OF c's OWN LOGITS: its 21 digits; the margins'
middle digit in two limbs, their low digit, and the middle digit's value in the table stepTab in
three limbs. The activations, the weights and all else are c's. -/
def withHead (c : NCells) : NCells :=
  { c with
    cell := fun m f t =>
      match m with
      | .row =>
        if NR ≤ f ∧ f < NR + 21 then (digitG c t (f - NR) : Int) - 128 else c.cell .row f t
      | .wide =>
        if f < 4 * d then c.cell .wide f t
        else if f < 4 * d + JV then loZ (midN c (f - 4 * d) t - o2 (f - 4 * d) t)
        else if f < 4 * d + 2 * JV then
          hiZ (midN c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
        else if f < 4 * d + 3 * JV then
          lowN c (f - (4 * d + 2 * JV)) t - o1 (f - (4 * d + 2 * JV)) t
        else if f < 4 * d + 6 * JV then
          (if (midN c ((f - (4 * d + 3 * JV)) % JV) t).toNat = 0 then 127 else -128)
        else c.cell .wide f t
      | .act => c.cell .act f t }

theorem logit_withHead (c : NCells) (t v : Nat) :
    logit (withHead c).toCells t v = logit c.toCells t v := rfl

theorem cost_withHead (c : NCells) (t : Nat) :
    cost (withHead c).toCells t = cost c.toCells t := rfl

theorem rowG (c : NCells) (t : Nat) {j : Nat} (hj : j < 21) :
    (withHead c).cell .row (NR + j) t = (digitG c t j : Int) - 128 := by
  show (if NR ≤ NR + j ∧ NR + j < NR + 21 then (digitG c t (NR + j - NR) : Int) - 128
    else c.cell .row (NR + j) t) = _
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem rowG_low (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    (withHead c).cell .row n t = c.cell .row n t := by
  show (if NR ≤ n ∧ n < NR + 21 then (digitG c t (n - NR) : Int) - 128
    else c.cell .row n t) = _
  rw [if_neg (by unfold NR; omega)]

theorem numG_sum (c : NCells) (t a k N : Nat) (hak : a + k ≤ 21)
    (hd : ∀ l, l < k → digitG c t (a + l) = dig k N l)
    (hs : (Finset.range k).sum (fun l => 256 ^ l * dig k N l) = N) :
    ((Finset.range k).sum fun l =>
      (256 : Int) ^ l * ((withHead c).cell .row (NR + a + l) t + 128)) = (N : Int) := by
  rw [← hs]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.mp hl
  rw [Nat.add_assoc, rowG c t (by omega), hd l hl']
  ring

theorem numZ_withHead (c : NCells) (n : Number) (t : Nat) :
    numZ (withHead c).toCells n t = (numG c n t : Int) := by
  unfold numZ
  cases n
  · exact numG_sum c t 0 5 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_pos (by omega), Nat.zero_add]) (dig_sum5 _)
  · exact numG_sum c t 5 1 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum1 _)
  · exact numG_sum c t 6 5 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left])
      (dig_sum5 _)
  · exact numG_sum c t 11 5 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
        Nat.add_sub_cancel_left]) (dig_sum5 _)
  · exact numG_sum c t 16 2 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left]) (dig_sum2 _)
  · exact numG_sum c t 18 3 _ (by omega) (fun l hl => by
      unfold digitG
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), Nat.add_sub_cancel_left]) (dig_sum3 _)

theorem wideG_old (c : NCells) (t : Nat) {f : Nat} (hf : f < 4 * d) :
    (withHead c).cell .wide f t = c.cell .wide f t := by
  show (if f < 4 * d then c.cell .wide f t else _) = _
  rw [if_pos hf]

theorem wideG_mid0 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withHead c).cell .wide (4 * d + x) t = loZ (midN c x t - o2 x t) := by
  show (if 4 * d + x < 4 * d then c.cell .wide (4 * d + x) t
    else if 4 * d + x < 4 * d + JV then
      loZ (midN c (4 * d + x - 4 * d) t - o2 (4 * d + x - 4 * d) t)
    else _) = _
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideG_mid1 (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withHead c).cell .wide (4 * d + JV + x) t = hiZ (midN c x t - o2 x t) := by
  show (if 4 * d + JV + x < 4 * d then c.cell .wide (4 * d + JV + x) t
    else if 4 * d + JV + x < 4 * d + JV then _
    else if 4 * d + JV + x < 4 * d + 2 * JV then
      hiZ (midN c (4 * d + JV + x - (4 * d + JV)) t - o2 (4 * d + JV + x - (4 * d + JV)) t)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]

theorem wideG_low (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    (withHead c).cell .wide (4 * d + 2 * JV + x) t = lowN c x t - o1 x t := by
  show (if 4 * d + 2 * JV + x < 4 * d then c.cell .wide (4 * d + 2 * JV + x) t
    else if 4 * d + 2 * JV + x < 4 * d + JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 2 * JV then _
    else if 4 * d + 2 * JV + x < 4 * d + 3 * JV then
      lowN c (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t -
        o1 (4 * d + 2 * JV + x - (4 * d + 2 * JV)) t
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]

theorem wideG_tv (c : NCells) (t : Nat) {l x : Nat} (hl : l < 3) (hx : x < JV) :
    (withHead c).cell .wide (4 * d + (3 + l) * JV + x) t =
      if (midN c x t).toNat = 0 then 127 else -128 := by
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
      (if (midN c ((4 * d + (3 + l) * JV + x - (4 * d + 3 * JV)) % JV) t).toNat = 0 then
        (127 : Int) else -128)
    else _) = _
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h2, e,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

theorem midZ_withHead (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    midZ (withHead c).toCells x t = midN c x t := by
  unfold midZ off2
  rw [show (withHead c).toCells.cell .wide (4 * d + x) t = _ from wideG_mid0 c t hx,
    show (withHead c).toCells.cell .wide (4 * d + JV + x) t = _ from wideG_mid1 c t hx, lo_hi]
  unfold o2
  split <;> push_cast <;> ring

theorem lowZ_withHead (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    lowZ (withHead c).toCells x t = lowN c x t := by
  unfold lowZ off1
  rw [show (withHead c).toCells.cell .wide (4 * d + 2 * JV + x) t = _ from wideG_low c t hx]
  unfold o1
  split <;> push_cast <;> ring

theorem tvZ_withHead (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    tvZ (withHead c).toCells x t = (stepTab (midN c x t).toNat : Int) := by
  unfold tvZ offE stepTab
  rw [Finset.sum_congr rfl fun l hl => by
    rw [show (withHead c).toCells.cell .wide (4 * d + (3 + l) * JV + x) t =
      if (midN c x t).toNat = 0 then (127 : Int) else -128 from
        wideG_tv c t (Finset.mem_range.mp hl) hx]]
  by_cases h : (midN c x t).toNat = 0
  · rw [if_pos h, if_pos h]
    simp [Finset.sum_range_succ]
  · rw [if_neg h, if_neg h]
    simp [Finset.sum_range_succ]

/-- The top digit is 0: the margin is its two lower digits. No premise. -/
theorem topNum_withHead (c : NCells) (t : Nat) {x : Nat} (hx : x < JV) :
    topNum (withHead c).toCells x t = 0 := by
  unfold topNum liftZ
  rw [logit_withHead, logit_withHead, numZ_withHead, numZ_withHead, midZ_withHead c t hx,
    lowZ_withHead c t hx]
  have e := Int.mul_ediv_add_emod (marG c x t) (2 ^ sh)
  show (if x < V ∧ checked t = true then logit c.toCells t (win t) - logit c.toCells t x else 0) +
    (if x < V ∧ costed t = true then (paidG c t : Int) + (BIG : Int) * ((0 : Nat) : Int) else 0) -
    (if checked t = true ∧ x < win t then 1 else 0) - 2 ^ sh * midN c x t - lowN c x t = 0
  have e2 : (if x < V ∧ costed t = true then (paidG c t : Int) + (BIG : Int) * ((0 : Nat) : Int)
      else 0) = if x < V ∧ costed t = true then (paidG c t : Int) else 0 := by
    split <;> simp
  rw [e2]
  unfold midN lowN
  have e3 : marG c x t = (if x < V ∧ checked t = true then
      logit c.toCells t (win t) - logit c.toCells t x else 0) +
      (if x < V ∧ costed t = true then (paidG c t : Int) else 0) -
      (if checked t = true ∧ x < win t then 1 else 0) := rfl
  rw [← e3]
  linarith

/-! ## 3. What is asked, and what follows of the margins -/

/-- What is asked of the cells' logits, the policy and the request, beside the tests. -/
structure AdmitsG (c : NCells) : Prop where
  /-- a lifted margin at a vocabulary entry of a checked position is not negative (at a position
  with a cost that is so of itself: lifted; at the last position it says that the token wins) and
  fits its two digits -/
  range : ∀ t x, x < V → checked t = true → 0 ≤ marG c x t ∧ marG c x t < 2 ^ (sh + 16)
  /-- the policy admits the cost at every position that has one -/
  pay : ∀ t, costed t = true → paidG c t ≤ theta
  /-- the clip's slack fits its five digits -/
  clip : C < 2 ^ 40

theorem marG_pad (hreq : Request.ok = true) (hy : y < V) (c : NCells) (t : Nat) {x : Nat}
    (hx : ¬ x < V) : marG c x t = 0 := by
  have hw := win_lt hreq hy t
  have h4 : ¬ x < win t := by omega
  unfold marG
  simp [hx, h4]

theorem marG_unchecked (c : NCells) (x : Nat) {t : Nat} (h : ¬ checked t = true) :
    marG c x t = 0 := by
  have h2 : ¬ costed t = true := fun hc => h (checked_of_costed hc)
  unfold marG
  simp [h, h2]

/-- **At a position with a cost every vocabulary entry's lifted margin is at least 2^sh**: the
prover pays the gap and 2^sh. No premise. -/
theorem lifted (c : NCells) {t x : Nat} (hx : x < V) (hc : costed t = true) :
    2 ^ sh ≤ marG c x t := by
  have h3 := checked_of_costed hc
  have hg := le_gap c.toCells t hx
  unfold marG
  rw [if_pos ⟨hx, h3⟩, if_pos ⟨hx, hc⟩, paidG_cast c hc]
  unfold cost
  by_cases h4 : x < win t
  · rw [if_pos h4] at hg
    rw [if_pos ⟨h3, h4⟩]
    linarith
  · rw [if_neg h4] at hg
    rw [if_neg (fun h => h4 h.2)]
    linarith

theorem range_all (hreq : Request.ok = true) (hy : y < V) {c : NCells} (A : AdmitsG c)
    (x t : Nat) : 0 ≤ marG c x t ∧ marG c x t < 2 ^ (sh + 16) := by
  by_cases h1 : x < V
  · by_cases h3 : checked t = true
    · exact A.range t x h1 h3
    · rw [marG_unchecked c x h3]
      exact ⟨le_refl _, by positivity⟩
  · rw [marG_pad hreq hy c t h1]
    exact ⟨le_refl _, by positivity⟩

theorem midN_range (hreq : Request.ok = true) (hy : y < V) {c : NCells} (A : AdmitsG c)
    (x t : Nat) : 0 ≤ midN c x t ∧ midN c x t < 2 ^ 16 := by
  obtain ⟨h0, h1⟩ := range_all hreq hy A x t
  unfold midN
  refine ⟨Int.ediv_nonneg h0 (by positivity), Int.ediv_lt_of_lt_mul (by positivity) ?_⟩
  rw [← pow_add, Nat.add_comm]
  exact h1

theorem lowN_range (P : PlanFacts) (c : NCells) (x t : Nat) :
    0 ≤ lowN c x t ∧ lowN c x t < 2 ^ 8 := by
  unfold lowN
  have hp : (0 : Int) < 2 ^ sh := by positivity
  refine ⟨Int.emod_nonneg _ hp.ne', lt_of_lt_of_le (Int.emod_lt_of_pos _ hp) ?_⟩
  rcases P.hsh with h | h <;> rw [h] <;> norm_num

theorem midN_pos (c : NCells) {t x : Nat} (hx : x < V) (hc : costed t = true) :
    (midN c x t).toNat ≠ 0 := by
  have h := lifted c hx hc
  have h1 : 1 ≤ midN c x t := by
    unfold midN
    exact Int.le_ediv_of_mul_le (by positivity) (by rw [one_mul]; exact h)
  omega

theorem midN_pad (hreq : Request.ok = true) (hy : y < V) (c : NCells) (t : Nat) {x : Nat}
    (hx : ¬ x < V) : (midN c x t).toNat = 0 := by
  unfold midN
  rw [marG_pad hreq hy c t hx]
  simp

theorem tvG_sum (hreq : Request.ok = true) (hy : y < V) (c : NCells) {t : Nat}
    (hc : costed t = true) :
    ((Finset.range JV).sum fun x => tvZ (withHead c).toCells x t) =
      (V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24 := by
  rw [Finset.sum_congr rfl fun x hx => tvZ_withHead c t (Finset.mem_range.mp hx)]
  have hJ : JV = V + (JV - V) := by
    have := V_le_JV
    omega
  conv_lhs => rw [hJ]
  rw [Finset.sum_range_add]
  have e1 : ∀ x ∈ Finset.range V, ((stepTab (midN c x t).toNat : Nat) : Int) = 1 := by
    intro x hx
    unfold stepTab
    rw [if_neg (midN_pos c (Finset.mem_range.mp hx) hc)]
    rfl
  have e2 : ∀ x ∈ Finset.range (JV - V),
      ((stepTab (midN c (V + x) t).toNat : Nat) : Int) = 2 ^ 24 := by
    intro x _
    unfold stepTab
    rw [if_pos (midN_pad hreq hy c t (by omega : ¬ V + x < V))]
    norm_num
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
  simp

theorem digitG_byte {sT : Nat} (hplan : planOk sT = true) {c : NCells} (A : AdmitsG c) (t : Nat)
    {j : Nat} (hj : j < 21) : digitG c t j < 256 := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, hcap, _⟩ := hp
  have hC := A.clip
  have hV := P.hV2
  have h5 : (256 : Nat) ^ 5 = 2 ^ 40 := by norm_num
  unfold digitG
  split
  · refine dig_byte (by omega) (by omega) ?_
    show paidG c t < 256 ^ 5
    rw [h5]
    by_cases hc : costed t = true
    · exact lt_of_le_of_lt (le_trans (A.pay t hc) hth) hC
    · unfold paidG
      rw [if_neg hc]
      norm_num
  split
  · exact dig_byte (by omega) (by omega) (by show 0 < 256 ^ 1; norm_num)
  split
  · refine dig_byte (by omega) (by omega) ?_
    show theta - paidG c t < 256 ^ 5
    rw [h5]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (lt_of_le_of_lt hth hC)
  split
  · refine dig_byte (by omega) (by omega) ?_
    show C - paidG c t < 256 ^ 5
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

/-! ## 4. The relations -/

/-- **THE RELATION IN INTEGERS.** -/
theorem intRel_withHead {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : AdmitsG c) : IntRel (withHead c).toCells stepTab := by
  have P := planFacts hplan
  have hp := hplan
  simp only [planOk, Policy.ok, Sizes.ranges, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at hp
  obtain ⟨hth, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hV24, _⟩ := hp
  refine ⟨fun t _ j hj => ?_, fun t _ x hx => ?_, fun t _ x hx => ?_, fun t _ x hx => ⟨0, ?_⟩,
    fun t _ x hx => ?_, fun t _ hc => ?_, fun t _ hc => ?_, ?_, ?_⟩
  · rw [show (withHead c).toCells.cell .row (NR + j) t = _ from rowG c t hj]
    have := digitG_byte hplan A t hj
    omega
  · rw [midZ_withHead c t hx]
    exact (midN_range hreq hy A x t).1
  · rw [lowZ_withHead c t hx]
    exact (lowN_range P c x t).1
  · rw [topNum_withHead c t hx]
    simp
  · rw [tvZ_withHead c t hx, midZ_withHead c t hx]
  · rw [numZ_withHead, numZ_withHead]
    show ((paidG c t : Nat) : Int) + ((C - paidG c t : Nat) : Int) = (C : Int)
    rw [Nat.cast_sub (le_trans (A.pay t hc) hth)]
    ring
  · rw [numZ_withHead, tvG_sum hreq hy c hc, P.hF]
    show ((2 ^ 24 - V : Nat) : Int) + ((V : Int) + ((JV - V : Nat) : Int) * 2 ^ 24) = _
    rw [Nat.cast_sub hV24]
    push_cast
    ring
  · rw [← sum_costed_const]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withHead, numZ_withHead, numZ_withHead]
    show (if costed t = true then ((paidG c t : Nat) : Int) + (C : Int) * ((0 : Nat) : Int) +
      ((theta - paidG c t : Nat) : Int) else 0) = _
    split
    · rename_i hc
      rw [Nat.cast_sub (A.pay t hc)]
      push_cast
      ring
    · rfl
  · have e : (((if RC > 0 then cap else 0 : Nat)) : Int) = if RC > 0 then (cap : Int) else 0 := by
      split <;> simp
    rw [e, ← sum_costed_first]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [numZ_withHead, numZ_withHead]
    show (if costed t = true then ((0 : Nat) : Int) + ((if t = r then cap else 0 : Nat) : Int)
      else 0) = _
    by_cases h : t = r <;> simp [h]

theorem small_withHead {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : AdmitsG c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18)
    (m : Matrix) (f t : Nat) : ((withHead c).cell m f t).natAbs < 2 ^ 18 := by
  have P := planFacts hplan
  have ho2 : ∀ x, 0 ≤ o2 x t ∧ o2 x t ≤ 32896 := fun x => by unfold o2; split <;> norm_num
  have ho1 : ∀ x, 0 ≤ o1 x t ∧ o1 x t ≤ 128 := fun x => by unfold o1; split <;> norm_num
  cases m
  · show (if f < 4 * d then c.cell .wide f t
      else if f < 4 * d + JV then loZ (midN c (f - 4 * d) t - o2 (f - 4 * d) t)
      else if f < 4 * d + 2 * JV then
        hiZ (midN c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
      else if f < 4 * d + 3 * JV then
        lowN c (f - (4 * d + 2 * JV)) t - o1 (f - (4 * d + 2 * JV)) t
      else if f < 4 * d + 6 * JV then
        (if (midN c ((f - (4 * d + 3 * JV)) % JV) t).toNat = 0 then (127 : Int) else -128)
      else c.cell .wide f t).natAbs < 2 ^ 18
    have h0 := hs .wide f t
    split
    · exact h0
    split
    · have := lo_bd (midN c (f - 4 * d) t - o2 (f - 4 * d) t)
      omega
    split
    · have a := midN_range hreq hy A (f - (4 * d + JV)) t
      have b := ho2 (f - (4 * d + JV))
      have := hi_bd (z := midN c (f - (4 * d + JV)) t - o2 (f - (4 * d + JV)) t)
        (by norm_num; omega) (by norm_num at a ⊢; omega)
      omega
    split
    · have a := lowN_range P c (f - (4 * d + 2 * JV)) t
      have b := ho1 (f - (4 * d + 2 * JV))
      norm_num at a
      omega
    split
    · split <;> norm_num
    · exact h0
  · exact hs .act f t
  · show (if NR ≤ f ∧ f < NR + 21 then (digitG c t (f - NR) : Int) - 128
      else c.cell .row f t).natAbs < 2 ^ 18
    split
    · rename_i h
      have := digitG_byte hplan A t (j := f - NR) (by omega)
      omega
    · exact hs .row f t

theorem rowG_withHead (hreq : Request.ok = true) (hy : y < V) {c : NCells} (A : AdmitsG c)
    (t : Nat) {x : Nat} (hx : x < JV) :
    ∃ u : Nat, u < 2 ^ 16 ∧ midZ (withHead c).toCells x t + 2 ^ 16 * tvZ (withHead c).toCells x t
      = (u : Int) + 2 ^ 16 * (stepTab u : Int) := by
  obtain ⟨h0, h1⟩ := midN_range hreq hy A x t
  refine ⟨(midN c x t).toNat, by omega, ?_⟩
  rw [midZ_withHead c t hx, tvZ_withHead c t hx, Int.toNat_of_nonneg h0]

/-- **THE HEAD's RELATION ON CELLS, WHOLE.** -/
theorem cellRel_withHead {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : AdmitsG c) (hs : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) :
    CellRel (withHead c).toCells stepTab := by
  have P := planFacts hplan
  have hI := intRel_withHead hplan hreq hy A
  obtain ⟨a, b, e⟩ := four_of_int P hI
  have hJ := jva_le (by have := P.hV2; omega)
  refine ⟨small_withHead hplan hreq hy A hs, hI.bytes, fun t ht x hx => ?_, fun t ht x hx => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, a, b, e⟩
  · refine inBits_of_rd (z := 0) (okE_keyAt _ _ _) ?_ (le_refl _) (by norm_num)
    rw [rd_key_top P hreq hy hx ht, topNum_withHead c t hx]
    simp
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_mid P hx ht) (hI.mid t ht x hx) ?_
    rw [midZ_withHead c t hx]
    exact (midN_range hreq hy A x t).2
  · refine inBits_of_rd (okE_keyAt _ _ _) (rd_key_low P hx ht) (hI.low t ht x hx) ?_
    rw [lowZ_withHead c t hx]
    exact (lowN_range P c x t).2
  · have hx' : x < JVa := hx
    obtain ⟨u, hu, hr⟩ := rowG_withHead hreq hy A t (x := x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableA P hx' ht, hr])
  · have hx' : x < JV - JVa := hx
    obtain ⟨u, hu, hr⟩ := rowG_withHead hreq hy A t (x := JVa + x) (by omega)
    exact isRow_of_rd (okE_keyAt _ _ _) hu (by rw [rd_key_tableB P hx' ht, hr])

theorem digZ_withHead (c : NCells) (t : Nat) {n : Nat} (hn : n < 99) :
    digZ (withHead c) t n = digZ c t n := by
  unfold digZ
  rw [rowG_low c t hn]

theorem holds_withHead (c : NCells) (h : (dataOf c).Holds) : (dataOf (withHead c)).Holds := by
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
    rw [digZ_withHead c t hn]) k

/-- **THE NORM's RELATION ON CELLS, WHOLE, WHERE IT HOLDS OF c.** -/
theorem cellRelN_withHead {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : AdmitsG c) (h : CellRelN c) : CellRelN (withHead c) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero (planFacts hplan).hdS
  have haw : ∀ t x, x < d → awZ (withHead c) t x = awZ c t x := fun t x hx => by
    unfold awZ
    rw [wideG_old c t (by omega), wideG_old c t (by omega)]
  have hrem : ∀ t x, x < d → remZ (withHead c) t x = remZ c t x := fun t x hx => by
    unfold remZ
    rw [wideG_old c t (by omega), wideG_old c t (by omega)]
  have hrec : ∀ t, recZ (withHead c) t = recZ c t := fun t => by
    unfold recZ Inst.Model.Ledger.R Inst.Model.Ledger.Rlo Inst.Model.Ledger.Rhi
    rw [b256_congr (fun n hn => digZ_withHead c t hn) 80 3 (by omega),
      b256_congr (fun n hn => digZ_withHead c t hn) 83 3 (by omega)]
  refine ⟨small_withHead hplan hreq hy A h.small, h.smallS, fun t ht v hv => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht j hj => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt _ _ hv) okE_zero
    have e := rd_rowsAt (withHead c) (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht] at e
    have hH := holds_withHead c (holds_of_rows c h.rows) 0 (show 0 < 1 by omega) k hk' t ht
    rw [idAt_eq] at hH
    rw [e, hH, rd_zero]
  · have e : keyNAt (withHead c) (cornerN x t) .remLow = keyNAt c (cornerN x t) .remLow :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remLow ht hd hx, rd_keyN_remLow ht hd hx, hrec, haw t x hx, hrem t x hx]
        rfl)
    rw [e]
    exact h.remLow t ht x hx
  · have e : keyNAt (withHead c) (cornerN x t) .remHigh = keyNAt c (cornerN x t) .remHigh :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_remHigh ht hd hx, rd_keyN_remHigh ht hd hx, hrem t x hx])
    rw [e]
    exact h.remHigh t ht x hx
  · have e : keyNAt (withHead c) (cornerN x t) .clamp = keyNAt c (cornerN x t) .clamp :=
      eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
        rw [rd_keyN_clamp ht hd hx, rd_keyN_clamp ht hd hx, haw t x hx]
        rfl)
    rw [e]
    exact h.clamp t ht x hx
  · by_cases h99 : j < 99
    · have e : keyNAt (withHead c) (cornerN j t) .digits = keyNAt c (cornerN j t) .digits :=
        eq_of_rd (okE_keyNAt _ _ _) (okE_keyNAt _ _ _) (by
          rw [rd_keyN_digits ht hj, rd_keyN_digits ht hj, digZ_withHead c t h99])
      rw [e]
      exact h.digits t ht j hj
    · have hm : ((mul j : Nat) : Int) = 1 := by
        unfold mul
        have : ∀ a : Nat, a < 99 → (j == a) = false := fun a ha => by simp; omega
        simp [this]
      have hj' : j - NR < 21 := by unfold NR at hj ⊢; omega
      have hjj : NR + (j - NR) = j := by unfold NR; omega
      have hb := digitG_byte hplan A t hj'
      have hz : digZ (withHead c) t j = (digitG c t (j - NR) : Int) := by
        unfold digZ
        rw [← hjj, rowG c t hj', hjj]
        ring
      refine inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_digits ht hj) ?_ ?_
      · rw [hm, one_mul, hz]
        omega
      · rw [hm, one_mul, hz]
        norm_num
        omega

/-- **FOR ANY CELLS THAT MEET THE NORM's RELATION, WITH ANY WEIGHTS: THE HEAD's OWN CELLS, LAID OF
THEIR LOGITS, MEET BOTH RELATIONS, WHOLE**, where AdmitsG holds. At a position with a cost the
hidden number "paid" is the text's own cost. -/
theorem both_withHead {sT : Nat} (hplan : planOk sT = true) (hreq : Request.ok = true)
    (hy : y < V) {c : NCells} (A : AdmitsG c) (h : CellRelN c) :
    CellRelN (withHead c) ∧ CellRel (withHead c).toCells stepTab ∧ TableOk stepTab ∧
      (dataOf (withHead c)).Holds ∧ (withHead c).Wh = c.Wh ∧
      (∀ t v, logit (withHead c).toCells t v = logit c.toCells t v) ∧
      ∀ t, costed t = true →
        numZ (withHead c).toCells .paid t = cost (withHead c).toCells t :=
  ⟨cellRelN_withHead hplan hreq hy A h, cellRel_withHead hplan hreq hy A h.small,
    tableOk_step (planFacts hplan).hF, holds_withHead c (holds_of_rows c h.rows), rfl,
    fun _ _ => rfl, fun t hc => by
      rw [numZ_withHead, cost_withHead]
      exact paidG_cast c hc⟩

end VerifiableInference.Desc.Kinds.Head.Law
