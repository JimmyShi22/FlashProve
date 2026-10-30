-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/Errs.lean: the errors of the blocks of a layers' sub-proof against the bounds
that the planner gives the same rounds.

The planner gives each of a sub-proof's own rounds a bound (`ownBounds`,
OnBytes/Tie/Pv/Lay/PlanBounds.lean): a quotient of two numbers, computed with outward rounding.
The blocks (Cb/Pv/Lay/) have for each round a number of bad draws. Here the bounds are written as
pairs (numerator, denominator), and each block's list of errors is shown to be the list of the
numerators of such pairs. The pairs are the bounds before the planner multiplies them by the
number of instances (`scaled`, PlanBounds.lean).

Main names:
  `boundOf`: a pair as the planner's bound. `qPsc c n dy`, `qLayer c v`: the pairs of a masked
    sumcheck's rounds and of a product layer's; c is the number of elements of the field.
  `ownRatios c x`: the pairs of all own rounds, stretch by stretch, in the plan's order.
  `ownBounds_ratios`: `ownBounds s x` is `(ownRatios s.cardE x).map boundOf`.
  `numsOf`: the numerators; a round without a draw counts 0. `nums_psc`, `nums_layer`: 1, then 2
    for each variable, then dy, 0; and one more 1 for a layer's last draw.
  `prod_plan`, `tok_plan`, `inner_plan`, `merge_plan`, `rows_plan`, `stack_plan`, `weights_plan`,
    `weightsFirst_plan`: each block's list of errors is the list of numerators of a sumcheck's or
    a layer's pairs at the block's own numbers: 1, then 2 for each variable, then the degree in
    the further variable, 0 (with a batch's number before it, a 1 behind it). c is a free letter,
    which the numerators forget. In `inner_plan` and `merge_plan` the block's list is a field of
    the letter V for its verifier (`nums`, Cb/G6/Letter.lean); in `stack_plan` the number of
    combined claims is a letter.
  `routed_plan`, `squares_plan`: the same for what stands behind the round of a join (and, for the
    squares, the scalars' round before it).
  `join_ratio`, `routed_join`, `squares_join`: a join draws g elements at once: the block's number
    of bad draws, g * q ^ (g - 1) of q ^ g, is the plan's quotient g / q.

Limits: a numerator is compared with a number of bad draws. That the draw is from the whole field,
or from its elements other than 0, so that the denominators agree too, is a fact on the rounds'
shapes and is not shown here; nor that c is the number of elements of E. Which record of a block
belongs to which stretch of `ownRatios` is not shown here: that matching is the reader's (for the
whole chain: OnBytes/Tie/Pv/Lay/OwnPlan.lean). Nothing is said on the rounding of the planner's
quotients.
-/
import OnBytes.Tie.Pv.Lay.PlanBounds
import Cb.Pv.Lay.Rows
import Cb.Pv.Lay.Stack
import Cb.Pv.Lay.Squares
import Cb.Pv.Lay.WeightsFirst
import Cb.Pv.Lay.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-- A pair as the planner's bound. -/
def boundOf (o : Option (Nat × Nat)) : Option Bound := o.map fun p => Bound.ratio p.1 p.2

/-- The pairs of a masked sumcheck's rounds. c: the number of elements of the field. -/
def qPsc (c n dy : Nat) : List (Option (Nat × Nat)) :=
  [some (1, c)] ++ List.replicate n (some (2, c)) ++ [some (dy, c - 1), none]

/-- The pairs of a product layer's rounds. -/
def qLayer (c v : Nat) : List (Option (Nat × Nat)) := qPsc c v 2 ++ [some (1, c)]

/-- The pairs of all own rounds, in the plan's order. -/
def ownRatios (c : Nat) (x : LayerRounds) : List (Option (Nat × Nat)) :=
  [some (x.lt, c)] ++
  (if x.firstGroup then [some (x.ls + x.lt, c), some (x.lPd - x.ls, c)] else []) ++
  [some (x.NS - 1, c)] ++
  (if x.lNI != 0 then [some (x.lNI, c)] else []) ++
  qLayer c (x.lNI + x.lPd + x.lt) ++
  [some (x.NP * x.NI - 1, c)] ++
  qPsc c x.lt 2 ++
  (if x.withTerms then qPsc c x.lt 1 else []) ++
  (if x.withTerms then [some (2 - 1, c)] else []) ++
  qPsc c x.lamS 2 ++
  qLayer c (x.ll + x.lPf + x.lt) ++
  (if x.routed then (if 1 < x.ll then [some (x.ll - 1, c)] else []) else []) ++
  (if x.routed then qLayer c (x.ll - 1 + x.lfe + x.lt) else []) ++
  [some (x.weightClaims + (if x.firstGroup then 1 else 0) - 1, c)] ++
  qPsc c x.lkW 1

theorem bPsc_ratios (s : Setting) (n dy : Nat) : bPsc s n dy = (qPsc s.cardE n dy).map boundOf := by
  simp [bPsc, qPsc, boundOf, fieldError, fieldErrorNonzero]

theorem bLayer_ratios (s : Setting) (v : Nat) : bLayer s v = (qLayer s.cardE v).map boundOf := by
  simp [bLayer, qLayer, bPsc_ratios, boundOf, fieldError]

/-- The planner's bounds are these pairs. -/
theorem ownBounds_ratios (s : Setting) (x : LayerRounds) :
    ownBounds s x = (ownRatios s.cardE x).map boundOf := by
  unfold ownBounds ownRatios
  simp only [List.map_append, bPsc_ratios, bLayer_ratios]
  cases x.firstGroup <;> cases x.withTerms <;> cases x.routed <;> by_cases h1 : x.lNI != 0 <;>
    by_cases h2 : 1 < x.ll <;> simp [h1, h2, boundOf, fieldError, powersError]

/-- The numerators; a round without a draw counts 0. -/
def numsOf (l : List (Option (Nat × Nat))) : List Nat := l.map fun o => (o.map (·.1)).getD 0

theorem nums_psc (c n dy : Nat) : numsOf (qPsc c n dy) = 1 :: (List.replicate n 2 ++ [dy, 0]) := by
  simp [numsOf, qPsc]

theorem nums_layer (c v : Nat) : numsOf (qLayer c v) = 1 :: (List.replicate v 2 ++ [2, 0, 1]) := by
  simp [numsOf, qLayer, qPsc]

theorem numsOf_cons (o : Option (Nat × Nat)) (l : List (Option (Nat × Nat))) :
    numsOf (o :: l) = (o.map (·.1)).getD 0 :: numsOf l := rfl

/-- A join's number of bad draws, of q ^ g draws, is the quotient g / q. -/
theorem join_ratio (g q : Nat) (h : 0 < g) : g * q ^ (g - 1) * q = g * q ^ g := by
  obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
  simp [pow_succ, Nat.mul_assoc]

section Blocks
open Iop Cb Cb.Pv.Lay TWhole
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} {Kc : Type} (c : Nat)

theorem prod_plan (L : ProdL E) (V : ShortK L.T.par Ex) :
    TWhole.errList (L.eps (Kc := Kc) V) = numsOf (qLayer c L.k) := by
  rw [L.errs V, nums_layer]

theorem tok_plan (L : TokL E) :
    TWhole.errList (L.toSum.reps (Ex := Ex) (F₀ L.toSum.T.par)) = numsOf (qPsc c L.k L.dy) := by
  rw [L.errs, nums_psc]

theorem inner_plan (L : InnL E) (V : ShortK L.toSum.T.par Ex) :
    TWhole.errList V.ε = numsOf (qPsc c L.k 2) := by
  rw [L.errs V, nums_psc]

theorem merge_plan (L : MergeL E) (V : ShortK L.T.par Ex) :
    TWhole.errList V.ε = numsOf (qPsc c L.k 1) := by
  rw [L.errs V, nums_psc]

theorem rows_plan (L : RowsL E) :
    TWhole.errList (L.eps (Ex := Ex)) = numsOf (some (L.np - 1, c) :: qPsc c L.k 2) := by
  rw [L.errs, numsOf_cons, nums_psc]
  rfl

theorem stack_plan (L : StackL E) (V : ShortK L.inn.toSum.T.par Ex) :
    TWhole.errList (L.eps (Kc := Kc) V) = numsOf (some (L.nc - 1, c) :: qPsc c L.inn.k 2) := by
  rw [L.errs V, numsOf_cons, nums_psc]
  rfl

theorem weights_plan (G : WeightsL E) (V : ShortK G.L.T.par Ex) :
    TWhole.errList (G.eps (Kc := Kc) V) = numsOf (some (G.n - 1, c) :: qPsc c G.k 1) := by
  rw [G.errs V, numsOf_cons, nums_psc]
  rfl

/-- In the first group one claim more is combined: n + 1 claims, so n bad draws. -/
theorem weightsFirst_plan (G : WFirstL E) (V : ShortK G.L.T.par Ex) :
    TWhole.errList (G.eps V) = numsOf (some (G.n + 1 - 1, c) :: qPsc c G.k 1) := by
  rw [G.errs V, numsOf_cons, nums_psc]
  rfl

/-- Behind the join's round the list is a product layer's. -/
theorem routed_plan (G : RoutedL E) (V : ShortK G.L.T.par Ex) :
    (TWhole.errList (G.eps (Kc := Kc) V)).tail = numsOf (qLayer c (G.g + G.k')) := by
  rw [G.errs V, nums_layer]
  rfl

/-- The join's own round: its number of bad draws, of q ^ g draws, is the plan's quotient g / q. -/
theorem routed_join (G : RoutedL E) (V : ShortK G.L.T.par Ex) (h : 0 < G.g) :
    ∃ e, (TWhole.errList (G.eps (Kc := Kc) V)).head? = some e ∧
      e * Fintype.card E = G.g * Fintype.card E ^ G.g := by
  rw [G.errs V]
  exact ⟨_, rfl, join_ratio G.g _ h⟩

/-- The scalars' round; behind the join's round a product layer's list. -/
theorem squares_plan (G : SquaresL E) (V : ShortK G.R.L.T.par Ex) :
    (TWhole.errList (G.eps (Kc := Kc) V)).head? = some (G.ns - 1) ∧
      (TWhole.errList (G.eps (Kc := Kc) V)).tail.tail = numsOf (qLayer c (G.g + G.k')) := by
  rw [G.errs V, nums_layer]
  exact ⟨rfl, rfl⟩

theorem squares_join (G : SquaresL E) (V : ShortK G.R.L.T.par Ex) (h : 0 < G.g) :
    ∃ e, (TWhole.errList (G.eps (Kc := Kc) V)).tail.head? = some e ∧
      e * Fintype.card E = G.g * Fintype.card E ^ G.g := by
  rw [G.errs V]
  exact ⟨_, rfl, join_ratio G.g _ h⟩

end Blocks

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.ownBounds_ratios
#print axioms OnBytes.Tie.Pv.Lay.prod_plan
#print axioms OnBytes.Tie.Pv.Lay.tok_plan
#print axioms OnBytes.Tie.Pv.Lay.inner_plan
#print axioms OnBytes.Tie.Pv.Lay.merge_plan
#print axioms OnBytes.Tie.Pv.Lay.rows_plan
#print axioms OnBytes.Tie.Pv.Lay.stack_plan
#print axioms OnBytes.Tie.Pv.Lay.weights_plan
#print axioms OnBytes.Tie.Pv.Lay.weightsFirst_plan
#print axioms OnBytes.Tie.Pv.Lay.routed_plan
#print axioms OnBytes.Tie.Pv.Lay.squares_plan
#print axioms OnBytes.Tie.Pv.Lay.routed_join
#print axioms OnBytes.Tie.Pv.Lay.squares_join
