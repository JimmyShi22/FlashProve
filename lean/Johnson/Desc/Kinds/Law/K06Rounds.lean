-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Rounds.lean: THE ROW «K06_rounds»: the output head's own rounds have the shape
of the rounds that the planner lays for them, entry for entry, and at each round the number of bad
elements that the block's one rule names is at most the price that the plan's accounting gives that
entry.
WHAT IT DOES NOT SHOW. NO PROBABILITY IS BOUNDED HERE: that a draw outside the rule's list keeps the
claims true is the row K06_law's matter. THE POINT pV (round 0): the rule with the point's part
(rowRuleC) names at most ONE bad element FOR EACH COORDINATE, at a front cut in front of that
coordinate: lt coordinates: the plan prices the round lt / |E|: here 1 ≤ lt is all that is said of it.
A price is a numerator: the denominator is the field's number of elements, at the round «PSC Y» one
fewer (the draw is never 0): clause (c). The prices are the routine's, BEFORE the planner multiplies by
the number of instances and before any proof of work. The premises WellLaid F and zt.size = lt are
another file's theorem's (Law/RowPrice.lean rowRuleC_tight; paid at the decision under planOk by its
ruleCutAt_tight). 0 < lt is a premise: a head with one position has no point to draw.
WHAT IT IS.
  tightAt_le      Law/RowPrice.lean's ceiling by the round's number (tightAt) is at most the price, at every j. Under 0 < lt.
  K06Rounds       the row, as one closed proposition, general in the sizes: (a) the kind's declared rounds
                  are the planner's entries · (b) these are the entries of the planner's descriptions,
                  which bear the bounds · (c) the bounds are the pairs' quotients · (d) THE CEILING: at
                  every front g the rule's list is no longer than the price of round number g.length - 1.
  k06Rounds       its proof.

-/
import Johnson.Desc.Kinds.Law.HeadPriceAt
import Johnson.Desc.Kinds.Law.RowPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Params (Setting)
open OnBytes.Tie.Pv.Lay (boundOf)
open Norm (lt lPd)
open Prices (prices priceFn sum3 prices_getD recOf recAt headRatios stated)

/-- A sumcheck's ceiling at a front of i + 1 rounds is its price at round number i. -/
theorem tight3_le_sum3 (m i : Nat) : tight3 m (i + 1) ≤ sum3 m i := by
  unfold tight3 sum3
  split_ifs <;> omega

/-- **The tight ceiling is at most the price, round by round.** -/
theorem tightAt_le [Sizes] [Policy] [Request] [Token] (h : 0 < lt) (j : Nat) : tightAt j ≤ (prices lt lPd).getD j 0 := by
  rw [prices_getD]
  have hl : lvl = lPd + lt + 4 := rfl
  have hs : smc = lt + 3 := rfl
  by_cases h0 : j = 0
  · subst h0
    have e1 : tightAt 0 = 1 := by
      unfold tightAt
      exact if_pos rfl
    have e2 : priceFn lt lPd 0 = lt := by
      unfold priceFn
      rw [if_pos (by omega), if_pos rfl]
    rw [e1, e2]
    exact h
  by_cases h1 : j = 1
  · subst h1
    have e1 : tightAt 1 = 8 := by
      unfold tightAt
      rw [if_neg (by omega), if_pos rfl]
    have e2 : priceFn lt lPd 1 = 8 := by
      unfold priceFn
      rw [if_pos (by omega), if_neg (by omega), if_pos rfl]
    exact le_of_eq (e1.trans e2.symm)
  by_cases h2 : j < 1 + lvl
  · rw [tightAt_level (by omega) (by omega)]
    have e2 : priceFn lt lPd j = sum3 (lPd + lt) (j - 2) := by
      unfold priceFn
      rw [if_neg (by omega), if_pos (by omega)]
    have e3 : j - 1 = (j - 2) + 1 := by omega
    rw [e2, e3]
    exact tight3_le_sum3 _ _
  by_cases h3 : j = 1 + lvl
  · rw [tightAt_level (by omega) (by omega)]
    have e1 : tight3 (lPd + lt) (j - 1) = 0 := by
      unfold tight3
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e1]
    exact Nat.zero_le _
  by_cases h4 : j = 2 + lvl
  · have e1 : tightAt j = 6 := by rw [h4]; exact tightAt_six
    have e2 : priceFn lt lPd j = 6 := by
      unfold priceFn
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
        if_pos (by omega)]
    exact le_of_eq (e1.trans e2.symm)
  by_cases h5 : j < 3 + lvl + smc
  · rw [tightAt_products (by omega) h5]
    have e2 : priceFn lt lPd j = sum3 lt (j - 2 - (lPd + lt + 3) - 2) := by
      unfold priceFn
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    have e3 : j - (2 + lvl) = (j - 2 - (lPd + lt + 3) - 2) + 1 := by omega
    rw [e2, e3]
    exact tight3_le_sum3 _ _
  by_cases h6 : j < 3 + lvl + 2 * smc
  · rw [tightAt_normed (by omega) h6]
    have e2 : priceFn lt lPd j = sum3 lt (j - 2 - (lPd + lt + 3) - 2 - (lt + 3)) := by
      unfold priceFn
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)]
    have e3 : j - (2 + lvl + smc) = (j - 2 - (lPd + lt + 3) - 2 - (lt + 3)) + 1 := by omega
    rw [e2, e3]
    exact tight3_le_sum3 _ _
  · rw [tightAt_logits (by omega)]
    have e2 : priceFn lt lPd j
        = sum3 (lt + lPd) (j - 2 - (lPd + lt + 3) - 2 - (lt + 3) - (lt + 3)) := by
      unfold priceFn
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    have e3 : j - (2 + lvl + 2 * smc)
        = (j - 2 - (lPd + lt + 3) - 2 - (lt + 3) - (lt + 3)) + 1 := by omega
    rw [e2, e3]
    exact tight3_le_sum3 _ _

/-- **The row.** -/
def K06Rounds : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In], 0 < lt →
    (∀ w : Nat, rounds.map (Round.entry w) = OnBytes.Tie.Pv.Head.headOwnList w recOf) ∧
    (∀ s : Setting, (OnBytes.Params.headOwnList s recOf).map (fun r => (r.round s .request).entry) =
      OnBytes.Tie.Pv.Head.headOwnList (s.workOf .field .request) recOf) ∧
    (∀ s : Setting, (OnBytes.Params.headOwnList s recOf).map stated =
      (headRatios s.cardE recOf).map boundOf) ∧
    (∀ (c : NCells) (mask : Nat → E) (F : Fork), WellLaid F → (FinalNorm.zt).size = lt →
      ∀ g : List Fmt.RoundView, (rowRuleC c mask F g).length ≤ (prices lt lPd).getD (g.length - 1) 0)

theorem k06Rounds : K06Rounds := by
  intro _ _ _ _ _ _ h
  have h4 : 0 < (recOf).rowValues := by simp [recOf, recAt]
  exact ⟨fun w => Prices.k6_entries w h, fun s => Prices.spec_entries s _ h4,
    fun s => Prices.headOwn_bounds s _ h4,
    fun c mask F hW hzt g => le_trans (rowRuleC_tight c mask F hW hzt g) (tightAt_le h _)⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tightAt_le
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k06Rounds
