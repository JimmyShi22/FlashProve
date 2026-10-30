-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/RowsAtFitAt.lean: THE TABLE's OWN TEST ON THE FORM OF THE PLAN's NUMBERS OF ROWS
(`rowsAtFit`, Johnson/Desc/First/Borders.lean) SAYS YES AT THE CONSTANT's NUMBERS: A THEOREM, WITH
NO
PREMISE BUT THE CONSTANT's OWN STRUCTURE. Statements and proofs; a negative line.

Why. The test stands as a premise (hN) in the hand-on over the one equation,
in the tie of the equation's numbers, in the groups' bridge and in four shares
of the closing; unproved, it would stand beneath K9's frozen condition as a bare conjunct.
Were it false there, what is left of the condition would be empty and no build
would show it. By a search by name and by the sentence's end over the
library's sources in another version and K9's files' folders:
no theorem ended in it; another file says "we know of no run of it".

What the test asks: no two of the segments 0 .. n have one group; in each group's list "carried"
stands from place 0, "position" behind it, the one equation behind both; the equation's class has
one row but at n; the first segment's group has the equation alone; every later one has a carried
row.

What is said.
  `rowsAtFit_of_plan`: for numbers whose rowsAt is the plan's (`rowsAtPlan s t N₀ n`,
    Johnson/Desc/First/RowsAtPlan.lean), WHATEVER s, t AND N₀ ARE: the second conjunct holds by that
    table's own text; so the test says yes where the groups' numbers are each once (hg).
  `rowsAtFit_at`: **at the constant: rowsAtFit h.𝔇.N fullLinks.length = true**: rowsAt by
    rowsAt_const (FactsAtConstant.lean); the group of segment m is m, by definition.
  `rowsAtFit_bent`: THE NEGATIVE LINE: at numbers of the same rows' table in which all segments have
    one group the test says no.

Limits. IT IS A TEST ON THE FORM: it does not see how many positions a switch draws (t), nor whether
the counts are the verifier's. Nothing on soundness.

-/
import Johnson.LPFK9R.FactsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Numbers rowsAtPlan carriedRows rowsAtFit eachOnce)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open P5J (AtMgA fullLinks)

/-- **The plan's table of rows has the form that the test asks.** -/
theorem rowsAtFit_of_plan (N N₀ : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ)
    (hN : N.rowsAt = rowsAtPlan s t N₀ n)
    (hg : eachOnce ((List.range (n + 1)).map fun m => (N.groupAt m, 0)) = true) :
    rowsAtFit N n = true := by
  unfold rowsAtFit
  rw [Bool.and_eq_true]
  refine ⟨hg, List.all_eq_true.2 fun m _ => ?_⟩
  rw [hN]
  by_cases h0 : m = 0
  · subst h0
    simp [rowsAtPlan, carriedRows]
  · have hz : (m == 0) = false := by simpa using h0
    simp [rowsAtPlan, carriedRows, hz]

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT THE CONSTANT.** -/
theorem rowsAtFit_at (h : AtMgA o Z D r Zp Np cF x) :
    rowsAtFit h.𝔇.N fullLinks.length = true := by
  have e : fullLinks.length = 25 := by decide
  rw [e]
  refine rowsAtFit_of_plan h.𝔇.N _ _ _ 25 (rowsAt_const h) ?_
  show eachOnce ((List.range 26).map fun m => (m, 0)) = true
  decide

/-- The negative line: all segments in one group. -/
theorem rowsAtFit_bent (N₀ : Numbers) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) :
    rowsAtFit { N₀ with rowsAt := rowsAtPlan s t N₀ 25, groupAt := fun _ => 0 } 25 = false := by
  unfold rowsAtFit
  rw [Bool.and_eq_false_iff]
  refine Or.inl ?_
  show eachOnce ((List.range 26).map fun _ => ((0 : ℕ), (0 : ℕ))) = false
  decide

end LPFK9

#print axioms LPFK9.rowsAtFit_of_plan
#print axioms LPFK9.rowsAtFit_at
#print axioms LPFK9.rowsAtFit_bent
