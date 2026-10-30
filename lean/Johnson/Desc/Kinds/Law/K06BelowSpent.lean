-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06BelowSpent.lean: FOUR TIES ON FINDS BY READING (B3 · B7 · the second lot's B2; with B1's factor 2 ^ work from Law/K06BelowWork.lean): this file stands beside the files that were read.
WHAT IT DOES NOT SHOW. **NO SHARE OF BAD CHALLENGES IS BOUNDED HERE.** What is below 2^-128 is a COUNT (here: the length of the rule's own list, times what the round's entry draws beside, times 2 ^ work) × the sampler's fibre bound wOf d, against all written verifier messages of the round. From the bad challenges to such a count four links are typed
in no file that this one calls (found by reading): the pin of c and mask in front of the draws · from a rule to a set of written challenges (RuleBound | KitMeasure) · kitK × kitF at K6's entries · the pieces' type of round (TypedOracleCompiler.Run.PQ.RD; here: the library's _root_.Run.PQ.RD). No sum over the rounds.
  k06BelowWork_at   by the round's number, behind the point: every count up to the price, times 2 ^ w.
  (B3) k6T_below    THE RULE THAT THE LAWS SPEND (Law/RowPrice.lean: ruleK6T), not rowRuleC: at every front of at least two rounds its own list's length times 2 ^ w meets the clause in every written round with the plan's entry of that number: NO WellLaid, NO zt.size: 0 < lt alone (Law/K06RoundsAtPlan.lean: ruleK6T_le).
       k6T_below_point   at the point's round (a front of one round): lt × the list's length × q^(lt - 1) × 2 ^ w: the list has one member at most there (priceAt p 0 ≤ 1).
  (B7) spends_belowWork  «FOR ALL SIZES» BY THEOREM, NOT BY READING: from Law/K06Condition.lean's K06Cond (its field admitted gives lt ≤ 16) and work ≤ 57: k06BelowWork's conclusion at the kind's own lt, lPd. At the two written records work is 0.
  (B2, the second lot) ownSpecs_is   under h.XL = 5 THE PLANNER's OWN RECORD gives THE DESCRIPTIONS THAT BEAR THE BOUNDS (OnBytes.Params.headOwnList), not their entries alone (own_is): so spends_once's list is the plan's own: bounds_at_own.

-/
import Johnson.Desc.Kinds.Law.K06BelowWork
import Johnson.Desc.Kinds.Law.K06ConditionSpends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law
namespace Below

open OnBytes (E)
open Johnson.Bridge (KindFits)
open _root_.Run (PQ.RD)
open OnBytes.Slice (RoundBelow)
open Prices (prices recAt)
open Norm (lt lPd)
open scoped ENNReal

/-- By the round's number, behind the point, with the factor 2 ^ w. -/
theorem k06BelowWork_at {lt lPd w : ℕ} (h1 : 1 ≤ lt) (h2 : lt ≤ 16) (hw : w ≤ 57) (j : ℕ) (hj : 1 ≤ j) (c : ℕ)
    (hc : c ≤ (prices lt lPd).getD j 0) (d : PQ.RD)
    (hd : (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))[j]? = some d.entry)
    (hk : KindFits false d.kind) : RoundBelow (c * 2 ^ w) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [← k6Priced_entries, List.getElem?_map] at hd
  obtain ⟨p, hp, hpe⟩ := Option.map_eq_some_iff.1 hd
  have hcnt : ((k6Priced lt lPd w).map (·.2))[j]? = some p.2 := by
    rw [List.getElem?_map, hp]
    rfl
  rw [k6Priced_counts] at hcnt
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [List.getElem?_cons_succ, List.getElem?_tail] at hcnt
  have hv : (prices lt lPd).getD (i + 1) 0 = p.2 := by
    rw [List.getD_eq_getElem?_getD, hcnt]
    rfl
  exact RoundBelow.mono (Nat.mul_le_mul_right _ (hv ▸ hc))
    (k06BelowWork lt lPd w h1 h2 hw p (List.mem_of_getElem? hp) d hpe.symm hk)

/-- **(B3) The spent rule's own list, behind the point.** -/
theorem k6T_below {S : Type} (p : Par) (pol : Policy) (rq : Request) (tk : Token)
    (h1 : letI := p.sizes; 1 ≤ lt) (h2 : letI := p.sizes; lt ≤ 16) (w : ℕ) (hw : w ≤ 57) (L : Seat S) (s : S)
    (c : NCells) (mask : Nat → E) (g : List Fmt.RoundView) (hg : 2 ≤ g.length) (d : PQ.RD)
    (hd : letI := p.sizes
      (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))[g.length - 1]? = some d.entry)
    (hk : KindFits false d.kind) :
    RoundBelow ((ruleK6T p L s c mask g).length * 2 ^ w) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  letI := p.sizes
  k06BelowWork_at h1 h2 hw (g.length - 1) (by omega) _ (ruleK6T_le p pol rq tk h1 L s c mask g) d hd hk

/-- **At the point's round**: the list has one member at most; each of the lt drawn elements leaves q^(lt - 1) values to the others. -/
theorem k6T_below_point {S : Type} (p : Par) (h1 : letI := p.sizes; 1 ≤ lt) (h2 : letI := p.sizes; lt ≤ 16)
    (w : ℕ) (hw : w ≤ 57) (lPd' : ℕ) (L : Seat S) (s : S) (c : NCells) (mask : Nat → E) (g : List Fmt.RoundView)
    (hg : g.length - 1 = 0) (d : PQ.RD)
    (hd : letI := p.sizes; d.entry = OnBytes.Tie.Pv.Lay.eDraw "ZERO" w 0 lt) (hk : KindFits false d.kind) :
    letI := p.sizes
    RoundBelow (lt * (ruleK6T p L s c mask g).length * q ^ (lt - 1) * 2 ^ w) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  letI := p.sizes
  have hl : (ruleK6T p L s c mask g).length ≤ 1 := by
    refine le_trans (List.length_take_le _ _) ?_
    rw [hg]
    refine le_trans (Nat.min_le_right _ _) ?_
    unfold Came.tightAt
    rw [if_pos rfl]
  have hb := k06BelowWork lt lPd' w h1 h2 hw (OnBytes.Tie.Pv.Lay.eDraw "ZERO" w 0 lt, lt * q ^ (lt - 1))
    (by simp [k6Priced]) d hd hk
  refine RoundBelow.mono ?_ hb
  show lt * (ruleK6T p L s c mask g).length * q ^ (lt - 1) * 2 ^ w ≤ lt * q ^ (lt - 1) * 2 ^ w
  refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
  calc lt * (ruleK6T p L s c mask g).length ≤ lt * 1 := Nat.mul_le_mul_left _ hl
    _ = lt := Nat.mul_one _

end Below

namespace Cond

open OnBytes.Model.Head (Shape Border)
open Johnson.Bridge (KindFits)
open _root_.Run (PQ.RD)
open OnBytes.Slice (RoundBelow)
open Norm (lt lPd)
open scoped ENNReal

/-- The program's own tests on the shape give lt ≤ 16. -/
theorem admitted_lt (h : Shape) (ha : OnBytes.Model.Head.admitted h = true) : h.lt ≤ 16 := by
  simp only [OnBytes.Model.Head.admitted, Bool.and_eq_true, decide_eq_true_eq] at ha
  omega

/-- **(B7) From the condition on public numbers to the clause with the factor 2 ^ work.** -/
theorem spends_belowWork {h : Shape} {b : Border} {work inst : Nat} {reads : Option Nat}
    (C : K06Cond h b work inst reads) (hw : work ≤ 57) :
    letI := sizesOf h
    ∀ p ∈ Below.k6Priced lt lPd work, ∀ r : PQ.RD, r.entry = p.1 → KindFits false r.kind →
      RoundBelow (p.2 * 2 ^ work) r ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  letI := sizesOf h
  Below.k06BelowWork lt lPd work C.point (admitted_lt h C.admitted) hw

theorem workAt_small : workAt ≤ 57 := by decide

end Cond

/-- **(B2 of the second lot) The planner's own record gives the descriptions that bear the bounds.** -/
theorem ownSpecs_is (P : OnBytes.Model.Head.HPlanH2) (h : OnBytes.Model.Head.Shape) (hXL : h.XL = 5)
    (s : OnBytes.Params.Setting) :
    OnBytes.Params.headOwnList s (P.own h) = OnBytes.Params.headOwnList s (Prices.recAt h.lt h.lPd) := by
  simp [OnBytes.Model.Head.HPlanH2.own, hXL, Prices.recAt, OnBytes.Model.ledNS, OnBytes.Model.ledNP,
    OnBytes.Model.ledNO, OnBytes.Params.headOwnList]

open OnBytes.Params OnBytes.Tie.Pv.Lay in
/-- So the bounds that the planner's close prices AT ITS OWN RECORD are the pairs' quotients. -/
theorem bounds_at_own (P : OnBytes.Model.Head.HPlanH2) (h : OnBytes.Model.Head.Shape) (hXL : h.XL = 5)
    (s : Setting) (hi : s.instances ≤ 1) :
    (OnBytes.Params.headOwnList s (P.own h)).map (fun r => r.bound s .request) =
      (Prices.headRatios s.cardE (Prices.recAt h.lt h.lPd)).map fun o =>
        (boundOf o).getD (Bound.ofWord 0) := by
  rw [ownSpecs_is P h hXL s]
  exact bounds_priced s hi _ (by simp [Prices.recAt])

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k6T_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k6T_below_point
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_belowWork
#print axioms VerifiableInference.Desc.Kinds.Head.Law.bounds_at_own
