-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPriceAt.lean: THE PRICE OF THE OUTPUT HEAD's ROUND NUMBER j, AS A FUNCTION OF
NUMBERS: Law/HeadPrices.lean has the prices' numerators as a list (prices lt lPd); a rule's ceiling is
stated by the round's number. Here the list's member number j is written out.
WHAT IT DOES NOT SHOW. Nothing of soundness; nothing beyond Law/HeadPrices.lean: lists and numbers alone.
  sum3 m i       the price of round number i of a masked sumcheck in m variables: 1 at its first round;
                 2 at its m rounds and at the one behind them; 0 at the round of the end values, in which
                 nothing is drawn, and behind.
  priceFn        the price of round number j of the block; 0 behind its last round.
  prices_getD    member number j of prices lt lPd, or 0 behind its end, is priceFn lt lPd j.

-/
import Johnson.Desc.Kinds.Law.HeadPrices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Prices

/-- The price of round number i of a masked sumcheck in m variables. -/
def sum3 (m i : Nat) : Nat := if i = 0 then 1 else if i ≤ m + 1 then 2 else 0

/-- The prices of a masked sumcheck's rounds, as a list. -/
def sumList (m : Nat) : List Nat := 1 :: (List.replicate m 2 ++ [2, 0])

theorem sumList_length (m : Nat) : (sumList m).length = m + 3 := by
  simp [sumList]

theorem getD_app (l₁ l₂ : List Nat) (j : Nat) :
    (l₁ ++ l₂).getD j 0 = if j < l₁.length then l₁.getD j 0 else l₂.getD (j - l₁.length) 0 := by
  split
  · rename_i h
    exact List.getD_append _ _ _ _ h
  · rename_i h
    exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_two (a b j : Nat) :
    [a, b].getD j 0 = if j = 0 then a else if j = 1 then b else 0 := by
  rcases j with _ | _ | j <;> simp

theorem getD_rep (m j : Nat) : (List.replicate m 2).getD j 0 = if j < m then 2 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem getD_sum (m i : Nat) : (sumList m).getD i 0 = sum3 m i := by
  unfold sumList sum3
  rcases i with _ | k
  · simp
  · rw [List.getD_cons_succ, getD_app, getD_rep, getD_two, List.length_replicate]
    split_ifs <;> first | rfl | omega | simp_all

/-- The price of round number j of the block. -/
def priceFn (lt lPd j : Nat) : Nat :=
  if j < 2 then (if j = 0 then lt else if j = 1 then 8 else 0)
  else if j - 2 < lPd + lt + 3 then sum3 (lPd + lt) (j - 2)
  else if j - 2 - (lPd + lt + 3) < 2 then
    (if j - 2 - (lPd + lt + 3) = 0 then 1 else if j - 2 - (lPd + lt + 3) = 1 then 6 else 0)
  else if j - 2 - (lPd + lt + 3) - 2 < lt + 3 then sum3 lt (j - 2 - (lPd + lt + 3) - 2)
  else if j - 2 - (lPd + lt + 3) - 2 - (lt + 3) < lt + 3 then
    sum3 lt (j - 2 - (lPd + lt + 3) - 2 - (lt + 3))
  else sum3 (lt + lPd) (j - 2 - (lPd + lt + 3) - 2 - (lt + 3) - (lt + 3))

/-- The list, cut at its stretches. -/
theorem prices_cut (lt lPd : Nat) :
    prices lt lPd = [lt, 8] ++ (sumList (lPd + lt) ++ ([1, 6] ++ (sumList lt ++ (sumList lt ++
      sumList (lt + lPd))))) := by
  rw [prices_eq]
  simp [sumList]

theorem two_length (a b : Nat) : [a, b].length = 2 := rfl

/-- **Member number j of the list of prices.** -/
theorem prices_getD (lt lPd j : Nat) : (prices lt lPd).getD j 0 = priceFn lt lPd j := by
  rw [prices_cut]
  simp only [getD_app, getD_two, getD_sum, sumList_length, two_length]
  rfl

end VerifiableInference.Desc.Kinds.Head.Law.Prices

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.prices_getD
