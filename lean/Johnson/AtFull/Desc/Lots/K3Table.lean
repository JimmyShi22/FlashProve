-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Desc/Lots/K3Table.lean: THE LOT OF THE KIND "LOOKUP": CLOSED FACTS BY LEAN's KERNEL,
STATED AGAINST THE WRITTEN TABLE OF THE FIRST CHAIN ITSELF (cutFirstFull,
Johnson/Desc/Ok/PlanWritten/CutLit.lean).
  `rows_in_table`: at each of the fifty lookups' places the table has a row; its numbers of rounds
    and of lists of oracle messages are the written number nW; it tells no oracle message.
  `rows_in_table_control`: a negative test: with the written number of rounds one higher no place
    passes.
  `before_written`: the kind's own reading `beforeAt` at the written codes and shape gives the
    table's column "before" at all fifty. `before_at`: the same, place by place.
  `num_bend`: a negative test on the plan's tests: with one number of padding keys of segment 0's
    calls one higher they reject.
  `rows_ok`: every written skeleton has planOk = true; there are fifty.
Limits. Facts on written values. Nothing on soundness.

-/
import Johnson.AtFull.Desc.Lots.K3Written
import Johnson.G.SendsWritten
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Lots.K3
open VerifiableInference.Desc.First.Look (beforeAt)

/-- The test at one place, the number of rounds a letter (for the negative test). -/
def inTableB (n : Nat → Bool → Nat) (i : Nat) (d : Bool) : Bool :=
  (tableAt i d).any fun r =>
    r.2.2.1 == n (sortOf i) d && r.2.2.2.1 == n (sortOf i) d && r.2.2.2.2.1.isEmpty

theorem rows_in_table :
    ((List.range 25).all fun i => inTableB nW i false && inTableB nW i true) = true := by
  decide +kernel

theorem rows_in_table_control :
    ((List.range 25).any fun i =>
      inTableB (fun s d => nW s d + 1) i false || inTableB (fun s d => nW s d + 1) i true) =
      false := by
  decide +kernel

theorem before_written :
    ((List.range 25).all fun i => [false, true].all fun d =>
      beforeAt Johnson.G.proofCodesWritten VerifiableInference.Desc.ReqLit.shapeFull i d ==
        some (beforeW i d)) = true := by
  decide +kernel

/-- The same, place by place: what pays the field "before" of the row's hypotheses where the codes
and the shape are the written ones. -/
theorem before_at {i : Nat} (hi : i < 25) (d : Bool) :
    beforeAt Johnson.G.proofCodesWritten VerifiableInference.Desc.ReqLit.shapeFull i d =
      some (beforeW i d) := by
  have h := List.all_eq_true.1 before_written i (List.mem_range.2 hi)
  exact eq_of_beq (List.all_eq_true.1 h d (by cases d <;> simp))

theorem num_bend :
    (numOf { coreW 0 false with pub := (pubW 0 false).modify 0 (· + 1) } (pubW 0 false)).2 =
      false := by
  decide +kernel

theorem rows_ok : (k3RowsW.length == 50 && k3RowsW.all (·.planOk)) = true := by decide +kernel

end Johnson.AtFull.Lots.K3

#print axioms Johnson.AtFull.Lots.K3.rows_in_table
#print axioms Johnson.AtFull.Lots.K3.rows_in_table_control
#print axioms Johnson.AtFull.Lots.K3.before_written
#print axioms Johnson.AtFull.Lots.K3.before_at
#print axioms Johnson.AtFull.Lots.K3.num_bend
#print axioms Johnson.AtFull.Lots.K3.rows_ok
