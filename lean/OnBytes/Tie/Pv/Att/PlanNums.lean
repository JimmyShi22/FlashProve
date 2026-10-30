-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlanNums.lean: the plan's bounds for an attention sub-proof's own rounds as pairs
of natural numbers, and the numerators as one list.

OnBytes/Tie/Pv/Att/PlanOwnW.lean gives each round's bound as the planner's Bound.ratio. Here the two
arguments of ratio are laid bare, so that a block's list of errors, which has the form
1 :: (the variables' numbers ++ [0]), can be compared with the plan's.

Main names:
  `attBounds_ratios`: attBounds s x is attRatios s.cardE x, where a pair (n, d) is read as
    Bound.ratio n d, and none is a round in which the verifier says nothing.
  `nums_psc`, `nums_sc3`, `nums_scd`: a sumcheck's numerators in closed form, Y's among the
    variables'.
  `dens_psc`: in a sumcheck the denominator is c at every round but PSC Y, where it is c - 1, since
    that element is drawn among those that are not 0. At a batch and at the point it is c by the
    definition of attRatios.
  `nums_att`: the numerators of attRatios c x are attNums x, for every c. With attBounds_ratios this
    ties attNums to the plan's bounds.
  `attNums_length`: there are as many numbers as rounds.
Limits: no statement says what number Bound.ratio n d is (the planner rounds), that the factor by
which close counts a bound (the instances) is 1, or that a bound holds of the protocol.
-/
import OnBytes.Tie.Pv.Att.PlanOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att.Plan

open OnBytes OnBytes.Params

/-- A pair as the planner's bound. -/
def boundOf (o : Option (Nat × Nat)) : Option Bound := o.map fun p => Bound.ratio p.1 p.2

/-- The pairs of a sumcheck's rounds. c: the number of elements of E. -/
def qPsc (c : Nat) (x : PscSize) : List (Option (Nat × Nat)) :=
  [some (1, c)] ++ x.degree.map (fun g => some (g - 1, c)) ++
    (if x.withY then [some (x.degreeY, c - 1), none] else [])

/-- The pairs, in the order of attRounds. -/
def attRatios (c : Nat) (x : AttentionRounds) : List (Option (Nat × Nat)) :=
  (x.score.map fun u => qPsc c (attentionSc3 u.1 u.2)).flatten ++
  qPsc c (attentionSc3 x.e x.pairs) ++
  [some (2 - 1, c)] ++
  qPsc c (attentionSc3 x.valueM x.pairs) ++
  qPsc c (attentionSc3 x.valueD x.pairs) ++
  [some (2 * x.lgk + 2 * x.lt + 4, c)] ++
  [some (x.pairs - 1, c)] ++
  qPsc c (attentionSc3 x.attained x.pairs) ++
  [some (x.pairs - 1, c)] ++
  qPsc c (attentionScd x.lt x.lgk x.pairs x.Lam) ++
  [some (x.pairs - 1, c)] ++
  qPsc c (attentionSc3 x.bits x.pairs)

theorem bPsc_ratios (s : Setting) (x : PscSize) : bPsc s x = (qPsc s.cardE x).map boundOf := by
  cases h : x.withY <;>
    simp [bPsc, qPsc, h, boundOf, fieldError, fieldErrorNonzero, Function.comp_def]

theorem units_ratios (s : Setting) : ∀ l : List (Nat × Nat),
    (l.map fun u => bPsc s (attentionSc3 u.1 u.2)).flatten =
      ((l.map fun u => qPsc s.cardE (attentionSc3 u.1 u.2)).flatten).map boundOf
  | [] => rfl
  | u :: t => by
    simp only [List.map_cons, List.flatten_cons, List.map_append]
    rw [units_ratios s t, bPsc_ratios]

/-- The bounds are these pairs. -/
theorem attBounds_ratios (s : Setting) (x : AttentionRounds) :
    attBounds s x = (attRatios s.cardE x).map boundOf := by
  simp only [attBounds, attRatios, List.map_append]
  rw [units_ratios]
  simp only [bPsc_ratios]
  simp [boundOf, fieldError, powersError]

/-- The numerators; 0 where the verifier says nothing. A bound with the numerator 0 (a batch of one
row, or of none) gives 0 too: this list does not tell the two apart. -/
def numsOf (l : List (Option (Nat × Nat))) : List Nat := l.map fun o => (o.map (·.1)).getD 0

/-- The numerators, round by round. -/
def attNums (x : AttentionRounds) : List Nat := numsOf (attRatios 0 x)

/-- A sumcheck's numerators. They do not depend on c. -/
theorem nums_psc (c : Nat) (x : PscSize) : numsOf (qPsc c x) =
    1 :: (x.degree.map (· - 1) ++ (if x.withY then [x.degreeY, 0] else [])) := by
  cases h : x.withY <;> simp [numsOf, qPsc, h, Function.comp_def]

/-- The size attentionSc3: 1, then 3 for each variable, then 2, then 0. -/
theorem nums_sc3 (c nv pairs : Nat) :
    numsOf (qPsc c (attentionSc3 nv pairs)) = 1 :: ((List.replicate nv 3 ++ [2]) ++ [0]) := by
  simp [nums_psc, attentionSc3]

/-- The size attentionScd: 1, then lt times 2, lgk times lt + 2 and lt times lt + 1, then lt + 1,
then 0. -/
theorem nums_scd (c lt lgk pairs Lam : Nat) :
    numsOf (qPsc c (attentionScd lt lgk pairs Lam)) =
      1 :: ((List.replicate lt 2 ++ List.replicate lgk (lt + 2) ++ List.replicate lt (lt + 1) ++
        [lt + 1]) ++ [0]) := by
  simp [nums_psc, attentionScd]

/-- The denominators of a sumcheck with Y: c, then c for each variable, then c - 1 for Y. -/
theorem dens_psc (c : Nat) (x : PscSize) (h : x.withY = true) :
    (qPsc c x).map (fun o => o.map (·.2)) =
      some c :: (x.degree.map (fun _ => some c) ++ [some (c - 1), none]) := by
  simp [qPsc, h, Function.comp_def]

theorem numsOf_append (a b : List (Option (Nat × Nat))) :
    numsOf (a ++ b) = numsOf a ++ numsOf b := List.map_append

theorem nums_free (c : Nat) (x : PscSize) : numsOf (qPsc c x) = numsOf (qPsc 0 x) := by
  rw [nums_psc, nums_psc]

theorem nums_units (c : Nat) : ∀ l : List (Nat × Nat),
    numsOf (l.map fun u => qPsc c (attentionSc3 u.1 u.2)).flatten =
      numsOf (l.map fun u => qPsc 0 (attentionSc3 u.1 u.2)).flatten
  | [] => rfl
  | u :: t => by
    simp only [List.map_cons, List.flatten_cons, numsOf_append]
    rw [nums_units c t, nums_free]

/-- The numerators of the pairs are attNums, whatever c is. -/
theorem nums_att (c : Nat) (x : AttentionRounds) : numsOf (attRatios c x) = attNums x := by
  simp only [attNums, attRatios, numsOf_append]
  rw [nums_units c]
  simp only [nums_free c]
  simp [numsOf]

theorem attBounds_length (s : Setting) (x : AttentionRounds) :
    (attBounds s x).length = (attRounds s x).length := by
  have := congrArg List.length (attRounds_errors s x)
  simpa using this.symm

/-- There are as many numbers as rounds. -/
theorem attNums_length (x : AttentionRounds) : (attNums x).length = (firsts x).all := by
  have s : Setting := default
  have h1 : (attRatios 0 x).length = (attRatios s.cardE x).length := by
    simp [attRatios, qPsc, attentionSc3, attentionScd, Function.comp_def]
  have h2 : (attRatios s.cardE x).length = (attBounds s x).length := by
    rw [attBounds_ratios]; simp
  have h3 : (attRounds s x).length = (attList (s.workOf .field .request) x).length := by
    rw [← attRounds_entries]; simp
  simp only [attNums, numsOf, List.length_map]
  rw [h1, h2, attBounds_length, h3, attList_length]

end OnBytes.Tie.Pv.Att.Plan

#print axioms OnBytes.Tie.Pv.Att.Plan.attBounds_ratios
#print axioms OnBytes.Tie.Pv.Att.Plan.nums_psc
#print axioms OnBytes.Tie.Pv.Att.Plan.nums_sc3
#print axioms OnBytes.Tie.Pv.Att.Plan.nums_scd
#print axioms OnBytes.Tie.Pv.Att.Plan.dens_psc
#print axioms OnBytes.Tie.Pv.Att.Plan.nums_att
#print axioms OnBytes.Tie.Pv.Att.Plan.attNums_length
