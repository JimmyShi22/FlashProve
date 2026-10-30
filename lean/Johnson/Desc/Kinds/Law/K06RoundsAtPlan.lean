-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06RoundsAtPlan.lean: THE ROW «K06_rounds», STRONGER: FIVE TIES THAT Law/K06Rounds.lean LEFT OPEN, on finds by reading (B1 to B5).
This file stands beside K06Rounds.lean, and K06RoundsAtPlan has its four clauses and these.
WHAT IT DOES NOT SHOW. NO PROBABILITY IS BOUNDED. That a draw outside the rule's list keeps the claims true is K06_law's. THAT THE PROVED ROW (Cb/Pv/Head/HeadRow.lean: rowR) AND OUR BLOCK DECIDE ALIKE: (B4) ties their ROUNDS' SHAPE AND THEIR
ERRORS' NUMBERS, not their tests: we prove our block's law outright. The plan that a file's public part makes is not read here: P and h are letters.
  (B1) rule_draws_le   AT EVERY FRONT: THE RULE's LIST's LENGTH TIMES THE NUMBER OF ELEMENTS THAT THE ROUND's OWN ENTRY DRAWS is at most the price. WHY: «no bad draw» asks every drawn element; the
                       point's round draws lt elements, and K06Rounds' clause (d) compared the ceiling of ONE draw with the price: 1 ≤ lt: it would have stayed true had the plan priced
                       that round at 1 / |E|. Here: lt times 1 ≤ lt: equal. The draws are read off the planner's own entries (clause (a)'s list).
  (B3) priceAt_le      the ceiling at which the rule that the laws SPEND is cut (Law/RowPrice.lean: ruleK6T, cut at priceAt p j) is at most the price, at every j: no premise but 0 < lt.
       ruleK6T_le      so that rule's own list is no longer than the price: at every record, seat and front.
  (B2) own_is          under h.XL = 5 THE PLANNER's OWN RECORD of the head's rounds (OnBytes/Model/HeadRounds.lean: HPlanH2.own) GIVES THE ENTRIES of the record that Law/HeadPrices.lean types beside it
                       (recAt h.lt h.lPd): the three numbers 9 · 7 · 4 are ledNS | ledNP | ledNO at 5; lkW and rows are read by none of these rounds.
  (B4) row_fits_k6     THE PROVED ROW's ROUNDS FIT THE KIND's DECLARED ROUNDS' ENTRIES, one by one and in order: row_fits (OnBytes/Tie/Pv/Head/HeadRowFits.lean) at clause (a)'s list.
       rowNums_is      THE PROVED ROW's OWN ERRORS (row_nums' list rowNums q s sW, Cb/Pv/Head/HeadRowNums.lean) ARE lt q^(lt - 1) AT THE POINT AND, BEHIND IT, OUR PRICES.
  (B5) bound_is        where the setting has one instance at most, the bound that the planner's close PRICES (RoundSpec.bound s .request) is the routine's stated one; 0 at a silent round.
       bounds_priced   so clause (c) holds of the priced bounds.      pair_encloses  a pair's bound encloses numerator / denominator (Bound.encl_ratio).
  K06RoundsAtPlan | k06RoundsAtPlan   all of it as one closed proposition.

-/
import Johnson.Desc.Kinds.Law.K06Rounds
import OnBytes.Model.HeadRounds
import OnBytes.Tie.Pv.Head.HeadRowFits
import Cb.Pv.Head.HeadRowNums
import OnBytes.Params.BoundLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law
namespace Came

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Tie.Pv.Lay (eDraw eBat)
open Norm (lt lPd)
open Prices (prices recAt recOf)

/-- What a masked sumcheck's entries draw. -/
def sumDraws (m : Nat) : List Nat := 1 :: (List.replicate m 1 ++ [1, 0])

/-- What the planner's entries draw: the point's round lt elements; every other round one or none. -/
theorem draws_eq (w lt lPd : Nat) :
    (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)).map (·.drawE) =
      lt :: (1 :: (sumDraws (lPd + lt) ++ (1 :: 1 :: (sumDraws lt ++ (sumDraws lt ++ sumDraws (lt + lPd)))))) := by
  simp [sumDraws, recAt, eDraw, eBat, OnBytes.Tie.Pv.Head.headOwnList, OnBytes.Tie.Pv.Head.hPoint,
    OnBytes.Tie.Pv.Head.hBatSums, OnBytes.Tie.Pv.Head.hSquares, OnBytes.Tie.Pv.Head.hBatProducts,
    OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream, OnBytes.Tie.Pv.Head.hLogits,
    OnBytes.Tie.Pv.Lay.lLayer, OnBytes.Tie.Pv.Lay.lPsc]

theorem getD_le_one (l : List Nat) (h : ∀ x ∈ l, x ≤ 1) (i : Nat) : l.getD i 0 ≤ 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact Nat.zero_le 1
  | some x => exact h x (List.mem_of_getElem? hi)

/-- Behind the point's round an entry draws one element at most. -/
theorem draws_le_one (w lt lPd i : Nat) :
    ((OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)).map (·.drawE)).getD (i + 1) 0 ≤ 1 := by
  rw [draws_eq, List.getD_cons_succ]
  apply getD_le_one
  intro x hx
  simp only [sumDraws, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hx
  omega

/-- **(B1) The rule's list, times what the round's own entry draws, is at most the price.** -/
theorem rule_draws_le [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] (h : 0 < lt) (w : Nat)
    (c : NCells) (mask : Nat → E) (F : Fork) (hW : WellLaid F) (hzt : (FinalNorm.zt).size = lt)
    (g : List Fmt.RoundView) :
    (rowRuleC c mask F g).length *
        ((OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)).map (·.drawE)).getD (g.length - 1) 0 ≤
      (prices lt lPd).getD (g.length - 1) 0 := by
  have hT := rowRuleC_tight c mask F hW hzt g
  rcases Nat.eq_zero_or_pos (g.length - 1) with h0 | h0
  · rw [h0] at hT ⊢
    have e1 : tightAt 0 = 1 := by
      unfold tightAt
      exact if_pos rfl
    have e2 : (prices lt lPd).getD 0 0 = lt := by
      rw [Prices.prices_eq]
      rfl
    rw [draws_eq, e2]
    show _ * lt ≤ lt
    rw [e1] at hT
    calc (rowRuleC c mask F g).length * lt ≤ 1 * lt := Nat.mul_le_mul_right _ hT
      _ = lt := Nat.one_mul _
  · obtain ⟨i, hi⟩ : ∃ i, g.length - 1 = i + 1 := ⟨g.length - 1 - 1, by omega⟩
    rw [hi] at hT ⊢
    calc (rowRuleC c mask F g).length * _ ≤ (rowRuleC c mask F g).length * 1 :=
          Nat.mul_le_mul_left _ (draws_le_one w lt lPd i)
      _ = (rowRuleC c mask F g).length := Nat.mul_one _
      _ ≤ tightAt (i + 1) := hT
      _ ≤ (prices lt lPd).getD (i + 1) 0 := tightAt_le h _

end Came

open Norm (lt lPd) in
/-- **(B3) The ceiling at which the spent rule is cut is at most the price.** -/
theorem priceAt_le (p : Par) (pol : Policy) (rq : Request) (tk : Token)
    (h : letI := p.sizes; 0 < lt) (j : Nat) :
    letI := p.sizes
    priceAt p j ≤ (Prices.prices lt lPd).getD j 0 :=
  letI := p.sizes
  le_trans (Nat.min_le_right _ _) (Came.tightAt_le h j)

open Norm (lt lPd) in
/-- So the spent rule's own list is no longer than the price. -/
theorem ruleK6T_le {S : Type} (p : Par) (pol : Policy) (rq : Request) (tk : Token)
    (h : letI := p.sizes; 0 < lt) (L : Seat S) (s : S) (c : NCells) (mask : Nat → OnBytes.E)
    (g : List Fmt.RoundView) :
    letI := p.sizes
    (ruleK6T p L s c mask g).length ≤ (Prices.prices lt lPd).getD (g.length - 1) 0 :=
  letI := p.sizes
  le_trans (List.length_take_le _ _) (priceAt_le p pol rq tk h _)

/-- **(B2) The planner's own record gives the entries of the record typed beside it.** -/
theorem own_is (P : OnBytes.Model.Head.HPlanH2) (h : OnBytes.Model.Head.Shape) (hXL : h.XL = 5) (w : Nat) :
    OnBytes.Tie.Pv.Head.headOwnList w (P.own h) =
      OnBytes.Tie.Pv.Head.headOwnList w (Prices.recAt h.lt h.lPd) := by
  simp [OnBytes.Model.Head.HPlanH2.own, hXL, Prices.recAt, OnBytes.Model.ledNS, OnBytes.Model.ledNP,
    OnBytes.Model.ledNO, OnBytes.Tie.Pv.Head.headOwnList, OnBytes.Tie.Pv.Head.hPoint,
    OnBytes.Tie.Pv.Head.hBatSums, OnBytes.Tie.Pv.Head.hSquares, OnBytes.Tie.Pv.Head.hBatProducts,
    OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream, OnBytes.Tie.Pv.Head.hLogits]


/-! ## (B4) The proved row -/

/-- The proved row's record gives the entries of the record typed beside it. -/
theorem rowRounds_is (s : Cb.Pv.Head.SqSize) (lkW rows w : Nat) :
    OnBytes.Tie.Pv.Head.headOwnList w (OnBytes.Tie.Pv.Head.rowRounds s lkW rows) =
      OnBytes.Tie.Pv.Head.headOwnList w (Prices.recAt s.lt s.lPd) := by
  simp [OnBytes.Tie.Pv.Head.rowRounds, Prices.recAt, OnBytes.Tie.Pv.Head.headOwnList,
    OnBytes.Tie.Pv.Head.hPoint, OnBytes.Tie.Pv.Head.hBatSums, OnBytes.Tie.Pv.Head.hSquares,
    OnBytes.Tie.Pv.Head.hBatProducts, OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream,
    OnBytes.Tie.Pv.Head.hLogits]

/-- **(B4) The proved row's own errors are the point's count and, behind it, our prices.** -/
theorem rowNums_is (q : Nat) (s : Cb.Pv.Head.SqSize) (sW : Nat) :
    Cb.Pv.Head.rowNums q s sW = s.lt * q ^ (s.lt - 1) :: (Prices.prices s.lt s.lPd).tail := by
  rw [Prices.prices_eq]
  simp [Cb.Pv.Head.rowNums, Cb.Pv.Head.normNums, Cb.Pv.Head.sqNums, Cb.Pv.Head.Tok.TokKind.errs,
    Cb.Pv.Head.Tok.TokKind.vars]

/-! ## (B5) The priced bound -/

open OnBytes.Params in
/-- **(B5) With one instance at most the priced bound is the stated one.** -/
theorem bound_is (s : Setting) (h : s.instances ≤ 1) (r : RoundSpec) :
    r.bound s .request = (Prices.stated r).getD (Bound.ofWord 0) := by
  cases r with
  | said _ _ error _ _ _ _ =>
    have hn : ¬ 1 < s.instances := by omega
    simp [RoundSpec.bound, Prices.stated, hn]
  | silent _ _ _ => rfl
  | record _ _ error => rfl

open OnBytes.Params OnBytes.Tie.Pv.Lay in
/-- So the priced bounds of the head's own rounds are the pairs' quotients; 0 where nothing is drawn. -/
theorem bounds_priced (s : Setting) (h : s.instances ≤ 1) (x : HeadRounds) (hx : 0 < x.rowValues) :
    (OnBytes.Params.headOwnList s x).map (fun r => r.bound s .request) =
      (Prices.headRatios s.cardE x).map fun o => (boundOf o).getD (Bound.ofWord 0) := by
  have e := Prices.headOwn_bounds s x hx
  have e2 : (OnBytes.Params.headOwnList s x).map (fun r => r.bound s .request) =
      ((OnBytes.Params.headOwnList s x).map Prices.stated).map fun o => o.getD (Bound.ofWord 0) := by
    rw [List.map_map]
    exact List.map_congr_left fun r _ => bound_is s h r
  rw [e2, e, List.map_map]
  rfl

open OnBytes.Params in
/-- A pair's bound encloses numerator / denominator. -/
theorem pair_encloses (a b : Nat) : Encl (Bound.ratio a b) ((a : ℚ) / (b : ℚ)) :=
  Bound.encl_ratio a b

/-! ## (B4), the shape -/

namespace AtRow
open Iop Prob Cb Johnson.L5.Layers Cb.Pv.Head Cb.Pv.Head.Bat Cb.Pv.Head.Tok Inst.Model
open OnBytes.Tie.Pv.Head (row_fits)

section
variable {E : Type} [Field E] [Fintype E] {J P M Wp Kc : Type} [Fintype J] [DecidableEq J]
variable (np : NormPar) (limb : (J → E) → ℕ → ℕ → E) (dig : (J → E) → ℕ → ℕ → E)
variable (msk : ℕ → J) (sW : ℕ) (Ex : ExtSpec) (msg : M → J → E)
variable (Q0 : IOR.Rels Kc P Ex (M × Wp)) (s : SqSize)
variable (ztN ztH : P → Fin s.lt → E) (tabN tabH : P → (J → E) → Fin 2 → ℕ → E)
variable (join : P → E → E → (J → E) → Prop)

/-- **(B4) The proved row's rounds fit the kind's declared rounds' entries**, one by one and in order: at sizes whose lt and lPd are the row's. -/
theorem row_fits_k6 [z : VerifiableInference.Desc.Kinds.Head.Sizes]
    (hl : VerifiableInference.Desc.Kinds.Norm.lt = s.lt)
    (hp : VerifiableInference.Desc.Kinds.Norm.lPd = s.lPd)
    (h0 : 0 < VerifiableInference.Desc.Kinds.Norm.lt) (w : ℕ) :
    List.Forall₂ (OnBytes.Tie.Pv.Head.Fits E)
      (rowR np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join).shape
      (VerifiableInference.Desc.Kinds.Head.rounds.map (VerifiableInference.Desc.Kinds.Round.entry w)) := by
  rw [Prices.k6_entries w h0]
  have h := row_fits np limb dig msk sW Ex msg Q0 s ztN ztH tabN tabH join w 0 0
  rw [rowRounds_is] at h
  have e : Prices.recOf = Prices.recAt s.lt s.lPd := by
    unfold Prices.recOf
    rw [hl, hp]
  rw [e]
  exact h

end
end AtRow

/-- **The row, stronger**: K06Rounds' four clauses, and the ties, each as its theorem's own type. (row_fits_k6 stands beside: it is general in the proved row's letters.) -/
def K06RoundsAtPlan : Prop :=
  Came.K06Rounds ∧ (type_of% @Came.rule_draws_le) ∧ (type_of% @priceAt_le) ∧ (type_of% @ruleK6T_le) ∧
    (type_of% @own_is) ∧ (type_of% @rowNums_is) ∧ (type_of% @bounds_priced)

theorem k06RoundsAtPlan : K06RoundsAtPlan :=
  ⟨Came.k06Rounds, @Came.rule_draws_le, @priceAt_le, @ruleK6T_le, @own_is, @rowNums_is, @bounds_priced⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06RoundsAtPlan
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtRow.row_fits_k6
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowNums_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowRounds_is
#print axioms VerifiableInference.Desc.Kinds.Head.Law.bounds_priced
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rule_draws_le
#print axioms VerifiableInference.Desc.Kinds.Head.Law.priceAt_le
#print axioms VerifiableInference.Desc.Kinds.Head.Law.ruleK6T_le
#print axioms VerifiableInference.Desc.Kinds.Head.Law.own_is
