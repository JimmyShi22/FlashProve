-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPrices.lean: THE PLAN's SIDE OF THE ROW «K06_rounds»: the rounds that the
output head's kind declares (Johnson/Desc/Kinds/Head.lean: rounds) against the rounds that the
planner lays for the head's own rounds, entry for entry, and the price that the plan's accounting
gives each of these entries, as one written list.
WHAT IT DOES NOT SHOW. Nothing of soundness: no error is bounded here. That a price bounds anything.
The prices are the routine's bounds BEFORE the planner multiplies them by the number of instances
(RoundSpec.bound) and before any proof of work. A price is a pair (numerator, denominator); the
planner's Bound is its quotient, rounded outward (boundOf). Nothing on the place of these rounds in
a chain's plan. Nothing on the rounds behind the smallness test (the merge).
WHAT IT IS.
  recOf             the planner's record of the head's numbers at the kind's sizes: lt, lPd; nine
                    sums, seven products, four row values. lkW and rows are laid 0: the own rounds
                    do not read them.
  k6_entries        the kind's declared rounds, as entries of a plan at the work w, ARE the
                    closed list OnBytes.Tie.Pv.Head.headOwnList w recOf: names and all eleven
                    numbers. Under 0 < lt. By headOwn_adds that list is just what the
                    planner's own routine planHeadOwn adds.
  spec_entries      the entries of the planner's rounds as descriptions (OnBytes.Params.headOwnList,
                    which carries the bounds; runs_headOwn) are that same list: so the
                    k-th price below is the price of the k-th entry.
  headRatios        the prices as pairs, stretch by stretch, in the plan's order; none: a round in
                    which nothing is drawn.
  headOwn_bounds    the bounds that the descriptions state are these pairs' quotients.
  prices, prices_eq the numerators, written out: THE LIST THAT A RULE's CEILING HAS TO MEET, round by
                    round. prices_length: as many as the kind declares rounds.
The tools boundOf, qPsc, qLayer, numsOf are the layers' (OnBytes/Tie/Pv/Lay/Errs.lean).

-/
import OnBytes.Params.PlanListsSub
import OnBytes.Tie.Pv.Head.PlanList
import OnBytes.Tie.Pv.Lay.Errs
import Johnson.Desc.Kinds.Head

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Prices

open OnBytes.Params (Setting HeadRounds RoundSpec Bound)
open OnBytes.Tie.Pv.Lay (boundOf qPsc qLayer numsOf)
open Norm (lt lPd)

/-- The planner's record at given numbers of bits. -/
def recAt (lt lPd : Nat) : HeadRounds :=
  { lt := lt, lPd := lPd, lkW := 0, sums := 9, products := 7, rowValues := 4, rows := 0 }

/-- The planner's record of the head's numbers, at the kind's sizes. -/
def recOf [Sizes] : HeadRounds := recAt lt lPd

/-- **The kind's declared rounds are the planner's entries.** -/
theorem k6_entries [Sizes] (w : Nat) (h : 0 < lt) :
    rounds.map (Round.entry w) = OnBytes.Tie.Pv.Head.headOwnList w recOf := by
  have h0 : (lt == 0) = false := by simp; omega
  have hN : Norm.lNI = 0 := by simp [Norm.lNI, clog2, Norm.NI]
  simp [rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, sendThenBatch.rounds,
    level.rounds, sumcheck.rounds, Round.entry, hN, h0, recOf, recAt, Norm.NI,
    OnBytes.Tie.Pv.Head.headOwnList, OnBytes.Tie.Pv.Head.hPoint, OnBytes.Tie.Pv.Head.hBatSums,
    OnBytes.Tie.Pv.Head.hSquares, OnBytes.Tie.Pv.Head.hBatProducts,
    OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream, OnBytes.Tie.Pv.Head.hLogits,
    OnBytes.Tie.Pv.Lay.lLayer, OnBytes.Tie.Pv.Lay.lPsc, OnBytes.Tie.Pv.Lay.eDraw,
    OnBytes.Tie.Pv.Lay.eBat]

/-- The descriptions' entries are the closed list's. -/
theorem spec_entries (s : Setting) (x : HeadRounds) (h : 0 < x.rowValues) :
    (OnBytes.Params.headOwnList s x).map (fun r => (r.round s .request).entry) =
      OnBytes.Tie.Pv.Head.headOwnList (s.workOf .field .request) x := by
  simp [OnBytes.Params.headOwnList, OnBytes.Params.zeroRound, OnBytes.Params.batSigmaFrom,
    OnBytes.Params.pscList, OnBytes.Params.pscListFrom, OnBytes.Params.pscEpsilon,
    OnBytes.Params.pscEpsilonFrom, OnBytes.Params.pscVariable, OnBytes.Params.pscY,
    OnBytes.Params.lineRound, RoundSpec.round, h,
    OnBytes.Tie.Pv.Head.headOwnList, OnBytes.Tie.Pv.Head.hPoint, OnBytes.Tie.Pv.Head.hBatSums,
    OnBytes.Tie.Pv.Head.hSquares, OnBytes.Tie.Pv.Head.hBatProducts,
    OnBytes.Tie.Pv.Head.hProducts, OnBytes.Tie.Pv.Head.hStream, OnBytes.Tie.Pv.Head.hLogits,
    OnBytes.Tie.Pv.Lay.lLayer, OnBytes.Tie.Pv.Lay.lPsc, OnBytes.Tie.Pv.Lay.eDraw,
    OnBytes.Tie.Pv.Lay.eBat]

/-- The prices of the head's own rounds, as pairs, in the plan's order. c: the number of elements of
the field. -/
def headRatios (c : Nat) (x : HeadRounds) : List (Option (Nat × Nat)) :=
  [some (x.lt, c)] ++ [some (x.sums - 1, c)] ++ qLayer c (x.lPd + x.lt) ++
    [some (x.products - 1, c)] ++ qPsc c x.lt 2 ++ qPsc c x.lt 2 ++ qPsc c (x.lt + x.lPd) 2

/-- The bound that a description states; none: a round in which the verifier says nothing. -/
def stated : RoundSpec → Option Bound
  | .said _ _ error _ _ _ _ => some error
  | .silent _ _ _ => none
  | .record _ _ error => some error

/-- **The bounds that the plan's accounting states for these rounds are the pairs' quotients.** -/
theorem headOwn_bounds (s : Setting) (x : HeadRounds) (h : 0 < x.rowValues) :
    (OnBytes.Params.headOwnList s x).map stated = (headRatios s.cardE x).map boundOf := by
  simp [OnBytes.Params.headOwnList, OnBytes.Params.zeroRound, OnBytes.Params.batSigmaFrom,
    OnBytes.Params.pscList, OnBytes.Params.pscListFrom, OnBytes.Params.pscEpsilon,
    OnBytes.Params.pscEpsilonFrom, OnBytes.Params.pscVariable, OnBytes.Params.pscY,
    OnBytes.Params.lineRound, stated, h, headRatios, qLayer, qPsc, boundOf,
    OnBytes.Params.fieldError, OnBytes.Params.fieldErrorNonzero, OnBytes.Params.powersError]

/-- The numerators: what a rule's ceiling has to meet, round by round. -/
def prices (lt lPd : Nat) : List Nat := numsOf (headRatios 0 (recAt lt lPd))

/-- The list, written out: the point · the nine sums' batch · the squares' level with its line · the
seven products' batch · the three token sumchecks. -/
theorem prices_eq (lt lPd : Nat) :
    prices lt lPd =
      lt :: 8 :: (1 :: (List.replicate (lPd + lt) 2 ++ [2, 0, 1])) ++
        (6 :: (1 :: (List.replicate lt 2 ++ [2, 0]))) ++
        (1 :: (List.replicate lt 2 ++ [2, 0])) ++
        (1 :: (List.replicate (lt + lPd) 2 ++ [2, 0])) := by
  simp [prices, headRatios, recAt, numsOf, qLayer, qPsc]

/-- The numerators do not hang on the field's number of elements. -/
theorem prices_free (c lt lPd : Nat) : numsOf (headRatios c (recAt lt lPd)) = prices lt lPd := by
  simp [prices, headRatios, recAt, numsOf, qLayer, qPsc]

theorem prices_length (lt lPd : Nat) : (prices lt lPd).length = 16 + 2 * lPd + 4 * lt := by
  rw [prices_eq]
  simp
  omega

/-- As many prices as the kind declares rounds. -/
theorem rounds_length [Sizes] : rounds.length = (prices lt lPd).length := by
  have hN : Norm.lNI = 0 := by simp [Norm.lNI, clog2, Norm.NI]
  rw [prices_length]
  simp [rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, sendThenBatch.rounds,
    level.rounds, sumcheck.rounds, hN]
  omega

end VerifiableInference.Desc.Kinds.Head.Law.Prices

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.k6_entries
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.spec_entries
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.headOwn_bounds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.prices_eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Prices.rounds_length
