-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/OrderedLaws.lean: a bound of the planner's that is not marked bad has its ends in
order.

The operations on the planner's intervals make their results by `Bound.ends`, which marks two ends
that have crossed as bad. The planner's comparison of two numbers is exact
(OnBytes/Params/CmpLaws.lean). So the result of every operation, if it is not marked bad, has its
lower end at most its upper end, whatever the arguments were: `Ordered b` says that, and it holds of
`ends`, `failed`, `exact`, `ofWord`, `ofNat`, sums, products, powers, square roots, differences,
quotients and `ratio`; `inherit` keeps it (`ordered_ends` to `ordered_ratio`). It also follows from
a yes of the planner's own `le` on the two ends (`ordered_of_le`). A bound whose ends are in order
encloses its own upper end and its own lower end (`encl_hi`, `encl_lo`). The use: a law that asks
for a number that a price encloses can be met at the price's own upper end. That says nothing of
what the price's formula means: whoever does so still owes that the quantity meant is at most that
upper end.

Main definition: `Ordered`.
Main theorems: `Bound.ordered_ends`, `Bound.ordered_inherit`, `Bound.ordered_failed`,
`Bound.ordered_exact`, `Bound.ordered_ofWord`, `Bound.ordered_ofNat`, `Bound.ordered_add`,
`Bound.ordered_mul`, `Bound.ordered_pow`, `Bound.ordered_sqrt`, `Bound.ordered_sub`,
`Bound.ordered_div`, `Bound.ordered_ratio`, `Bound.ordered_of_le`, `Bound.encl_hi`, `Bound.encl_lo`.
What is not claimed: that a bound encloses what its formula is meant to bound: see
OnBytes/Params/BoundLaws.lean and OnBytes/Params/SqrtLaws.lean. Nothing of a bound that somebody
builds by the structure's constructor. That each price of the planner's is the result of one of
these operations is not stated here formula by formula. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.CmpLaws

set_option autoImplicit false

namespace OnBytes.Params

/-- The ends of the bound b are in order, unless b is marked bad. -/
def Ordered (b : Bound) : Prop := b.bad = false → b.lo.val ≤ b.hi.val

namespace Bound
open Binary

/-- Two ends are in order unless they are marked bad. -/
theorem ordered_ends (l h : Binary) : Ordered (ends l h) := fun g => le_of_not_lt h l g

/-- A mark that is handed on keeps the order. -/
theorem ordered_inherit {r : Bound} (hr : Ordered r) (a b : Bound) : Ordered (r.inherit a b) :=
  fun g => by
  have g' : (r.bad || a.bad || b.bad) = false := g
  simp only [Bool.or_eq_false_iff] at g'
  exact hr g'.1.1

/-- The result of a formula outside its range is marked bad. -/
theorem ordered_failed : Ordered failed := fun g => by cases g

/-- An exact bound. -/
theorem ordered_exact (x : Binary) : Ordered (exact x) := fun _ => le_rfl

/-- A word. -/
theorem ordered_ofWord (x : ℕ) : Ordered (ofWord x) := ordered_exact _

/-- A natural number of any size. -/
theorem ordered_ofNat (x : ℕ) : Ordered (ofNat x) := fun _ =>
  (val_cut_down _).trans (val_cut_up _)

/-- A sum, whatever the arguments. -/
theorem ordered_add (a b : Bound) : Ordered (a + b) := ordered_inherit (ordered_ends _ _) a b

/-- A product, whatever the arguments. -/
theorem ordered_mul (a b : Bound) : Ordered (a * b) := ordered_inherit (ordered_ends _ _) a b

/-- A power, whatever the argument. -/
theorem ordered_pow (a : Bound) (n : ℕ) : Ordered (a.pow n) :=
  ordered_inherit (ordered_ends _ _) a a

/-- A square root, whatever the argument. -/
theorem ordered_sqrt (a : Bound) : Ordered a.sqrt := ordered_inherit (ordered_ends _ _) a a

/-- A difference, whatever the arguments. -/
theorem ordered_sub (a b : Bound) : Ordered (a - b) := by
  show Ordered (Bound.sub a b)
  unfold Bound.sub
  split
  · exact ordered_failed
  · exact ordered_ends _ _

/-- A quotient, whatever the arguments. -/
theorem ordered_div (a b : Bound) : Ordered (a / b) := by
  show Ordered (Bound.div a b)
  unfold Bound.div
  split
  · exact ordered_failed
  · exact ordered_ends _ _

/-- A quotient of two natural numbers. -/
theorem ordered_ratio (a b : ℕ) : Ordered (ratio a b) := ordered_div _ _

/-- A bound of which the planner's own `le` says that its ends are in order. -/
theorem ordered_of_le {b : Bound} (h : b.lo.le b.hi = true) : Ordered b := fun _ => le_sound _ _ h

/-- **A bound whose ends are in order encloses its own upper end.** -/
theorem encl_hi {b : Bound} (h : Ordered b) : Encl b b.hi.val := fun g => ⟨h g, le_rfl⟩

/-- It encloses its own lower end too. -/
theorem encl_lo {b : Bound} (h : Ordered b) : Encl b b.lo.val := fun g => ⟨le_rfl, h g⟩

end Bound

end OnBytes.Params

#print axioms OnBytes.Params.Bound.ordered_ends
#print axioms OnBytes.Params.Bound.ordered_sqrt
#print axioms OnBytes.Params.Bound.ordered_div
#print axioms OnBytes.Params.Bound.ordered_of_le
#print axioms OnBytes.Params.Bound.encl_hi
