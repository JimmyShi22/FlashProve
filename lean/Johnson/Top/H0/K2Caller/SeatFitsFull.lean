-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SeatFitsFull.lean: the code switch: SeatFitsPlan.lean's new test AT THE
WRITTEN VALUES OF THE FULL SIZE, BY LEAN's KERNEL: the 25 written rows (K2Caller/LitRows.lean:
`tableFullLit`) against the plan's seats as a closed term (Johnson/P5T/PlanSeatsFull.lean: `psFull`;
`N0Full` is `numbersOf psFull`) and the written codes (`codesFull2`). A law file; no running text
imports it.

  `seats25_full`    seats25B psFull codesFull2 tableFullLit = true: at each of the 25 switches the
                    typed list that is sent has, by place, the shapes of a first stretch of the
                    plan's entries of that sending, and the kept members have, by place, the shapes
                    of the plan's kept entries; the rows' codes are the written codes.
  `seats25_counts`  what was held: 25 rows; 107 members sent; 36 kept. (psFull is whole: 199 seats,
                    36 of them kept copies: PlanSeatsFull.lean's psFull_whole | psFull_roles.)
  `seats25_whole`   each typed list that is sent is THE WHOLE of the table's list of that sending:
                    as many members as `N0Full.sent (m + 1) 0` has seats: so the "first stretch" of
                    `shapesNewB` is all of it, and the table has no seat beyond the typed list.
  `seats25_moved`, `seats25_more`   TWO NEGATIVE TESTS, by the kernel: the rows moved by one place;
                    every entry's shape with one main row more: false.
  `seats_full`      so, at every description G at which the composed meaning's head's named test
                    fit holds at these closed terms: at each written row: SeatFits at the list that
                    is sent, and the seven clauses at every kept member, in the caller's letters.
By evaluations in Lean's kernel (`decide +kernel`): the first five.
Limits. hfit (P5T.seatsFitP G codesFull2 psFull = true) IS A PREMISE, PAID BY NOBODY. `SeatFits`
reads of a member its shape and its seat alone: two members of one shape could change seats and the
sentence would stand. That the public part's own seats are `psFull` in the goals' scope:
Johnson/P5T/PlanSeatsTie.lean's seats_in_scope (not imported); that its codes are `codesFull2`, and
that the law's rows are `tableFullLit`'s: others'. The full size alone. Nothing on soundness or on
hiding.

-/
import Johnson.Top.H0.K2Caller.SeatFitsPlan
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (SeatFits)
open P5T (PSeat psFull N0Full seatsFitP)
open Johnson.G (codesFull2)

/-- **The new test at the written values of the full size.** -/
theorem seats25_full : seats25B psFull codesFull2 tableFullLit = true := by decide +kernel

/-- What was held. -/
theorem seats25_counts :
    (tableFullLit.length, (tableFullLit.map (·.l.length)).sum,
      (tableFullLit.map (·.kept.length)).sum) = (25, 107, 36) := by decide +kernel

/-- Each typed list that is sent has as many members as the table's list of that sending has
seats. -/
theorem seats25_whole :
    (List.range 25).map (fun m => (N0Full.sent (m + 1) 0).length) =
      tableFullLit.map (·.l.length) := by decide +kernel

/-- A negative test: the rows moved by one place. -/
theorem seats25_moved : seats25B psFull codesFull2 (tableFullLit.drop 1) = false := by
  decide +kernel

/-- A negative test: every entry's shape with one main row more. -/
theorem seats25_more :
    seats25B (psFull.map fun p => { p with shape := { p.shape with mainRows := p.shape.mainRows + 1
      } }) codesFull2 tableFullLit = false := by decide +kernel

/-- **At each written row: both sentences, in the caller's letters.** -/
theorem seats_full {Xi : Type} (G : FileDescription Xi) (hfit : seatsFitP G codesFull2 psFull = true)
    {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    SeatFits G r.cs r.l (fun i => (N0Full.sent (m + 1) 0).getD i.val (0, 0)) ∧
      ∀ i : Fin r.lo.length, i.val ∈ r.kept →
        SeatFitOne G r.cs r.lo (fun i => (N0Full.keptOf m).getD (r.kept.idxOf i.val) (0, 0)) i :=
  seats_at_row G hfit seats25_full hr

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.seats25_full
#print axioms VerifiableInference.Desc.First.K2Caller.seats25_counts
#print axioms VerifiableInference.Desc.First.K2Caller.seats25_whole
#print axioms VerifiableInference.Desc.First.K2Caller.seats25_moved
#print axioms VerifiableInference.Desc.First.K2Caller.seats25_more
#print axioms VerifiableInference.Desc.First.K2Caller.seats_full
