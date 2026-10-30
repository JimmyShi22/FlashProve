-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/RowsAtPlan.lean: `Numbers.rowsAt` AS A TERM OFF THE PLAN. Small; no Mathlib. A
file BESIDE the table of joints: it turns nothing of it.

Why. `rowsHeld`, a fixed clause of the promise at every border, reads `Numbers.rowsAt m c`: where in
group m's list of rows the class c stands, and how many rows it has. The field's default is (0, 0):
at it the clause is false on an honest run wherever a class with rows is open.

What is said. `positionRows s t m`: how many generator rows the switch into group m lays: t draws,
and at each draw one main row, one row for each main row of each message that group m keeps of the
group in front (the plan's target of the switch), and two mask rows. `carriedRows N m`: the carried
claim and one row a kept copy; none at the first group. `rowsAtPlan s t N n`: the four classes in
the order of laying: "carried" from place 0, "position" behind it, the one equation behind both
(none at the last switch's group, number n); a sample's class is no stretch of the list.
`Numbers.withRows`: the numbers with that field laid. `possOf`: the positions that a block's
declared rounds draw, for t off the description's own blocks.

Limits. (1) That a switch's yes lays just so many rows is the switch's law: not here. (2) t is a
letter: meant: `possOf` of the switch's block. (3) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

/-- How many generator rows the switch into group m lays. t: the positions that it draws. -/
def positionRows (s : Params.ReqShape) (t m : Nat) : Nat :=
  t * (1 + (((reqGroups s).getD m {}).target.kept.toList.map (·.shape.mainRows)).sum + 2)

/-- The carried claim and one row a kept copy of the group in front; none at the first group. -/
def carriedRows (N : Numbers) (m : Nat) : Nat :=
  if m == 0 then 0 else 1 + (N.keptOf (m - 1)).length

/-- **Where each class of rows stands in group m's list, and how many it has.** n: the number of
segments. -/
def rowsAtPlan (s : Params.ReqShape) (t : Nat → Nat) (N : Numbers) (n m : Nat) :
    RowClass → Nat × Nat
  | .carried => (0, carriedRows N m)
  | .position => (carriedRows N m, if m == 0 then 0 else positionRows s (t m) m)
  | .equation =>
    (carriedRows N m + (if m == 0 then 0 else positionRows s (t m) m), if m == n then 0 else 1)
  | .sample _ => (0, 0)

/-- The numbers with `rowsAt` laid off the plan. -/
def Numbers.withRows (N : Numbers) (s : Params.ReqShape) (t : Nat → Nat) (n : Nat) : Numbers :=
  { N with rowsAt := rowsAtPlan s t N n }

/-- The positions that a block's declared rounds draw. -/
def possOf {S Cl : Type} (b : Block S Cl) : Nat := (b.rounds.map fun d => d.entry.poss).sum

theorem withRows_rowsAt (N : Numbers) (s : Params.ReqShape) (t : Nat → Nat) (n : Nat) :
    (N.withRows s t n).rowsAt = rowsAtPlan s t N n := rfl

/-- Every other field that the promise's fixed clauses read is as it was. -/
theorem withRows_else (N : Numbers) (s : Params.ReqShape) (t : Nat → Nat) (n : Nat) :
    (N.withRows s t n).sent = N.sent ∧ (N.withRows s t n).keptOf = N.keptOf ∧
      (N.withRows s t n).groupAt = N.groupAt ∧ (N.withRows s t n).treesAt = N.treesAt ∧
      (N.withRows s t n).msgsAt = N.msgsAt :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.withRows_else
