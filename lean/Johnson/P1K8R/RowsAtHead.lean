-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RowsAtHead.lean: the smallness test's draw (K8): THE CLOSED FIELD «rows» OF WHAT IS
LEFT IN FRONT OF THAT KIND's NAMED CONDITION (K8Rest6, Johnson/P1K8R/CondOfRest6.lean), FROM THE
HEAD (WITH THE FOURTEEN ENTRY TESTS). NO SUB-PROTOCOL IMPORTS THIS FILE.
THE FIELD's THREE CLAUSES, AND WHO PAYS EACH.
  the rows can be read   READ OFF THE HEAD's OWN FIELD plan.radii: rows_at_head
                    (Johnson/IMR/RadAtHead.lean), then P1Opts.rows_at
                    (Johnson/Top/H0/Opts/SomeAtName.lean). The head was made with it: it is not
                    shown to hold at any files, and it pays nothing toward whether the head can be
                    met.
  radOneB           P5T.radOne_of_radii (Johnson/HB/LLHARD/RadOneWritten.lean) at
                    radii_in_scope (Johnson/HB/LLHARD/RadiiInScope.lean): in scope, under the
                    first pinned entry test, the first chain's rows' sampled columns are radsFull
  rowsShapedB       (Johnson/P1K8R/RowsShapedTest.lean) THE ONE NEW PROOF: the test reads of the
                    rows these columns alone (rowsShapedB_is); at radsFull, the written tenants and
                    the written sendings' number it accepts BY LEAN's KERNEL (shaped_written)
  shapedAtB         the test, at the columns
  shaped_moved · shaped_other   two negative tests, by the kernel: the columns moved by one sending;
                    the first column's first shape given one main row more: it rejects
  shaped_count      how many pairs it compares: so that the accept is not idle
  k8Rows_at_head    THE STATEMENT: the field, to the letter
CALLED BESIDE: P5J.pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean) · the head's law that the
plan's tenants are the written ones (Johnson/P5T/CoreAtMg.lean) · P5J.written_at_head
(Johnson/P5J/StartAtHead.lean).
LIMITS. The full size alone. At the second hash function alone. No example of the head. No
soundness is claimed.
-/
import Johnson.P1K8R.RowsShapedTest
import Johnson.IMR.RadAtHead
import Johnson.Top.H0.Opts.SomeAtName
import Johnson.HB.LLHARD.RadOneWritten
import Johnson.HB.LLHARD.RadiiInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.StartAtHead
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8T
open OnBytes
open P5T (PSeat mineAt firstRows psFull)
open Johnson.G (radsFull proofSends0)

/-- The test, at the rows' sampled columns. -/
def shapedAtB (cols : List (List (OracleShape × ℕ))) (ps : List PSeat) (n : ℕ) : Bool :=
  (List.range n).all fun k => (mineAt ps k).zipIdx.all fun pj =>
    decide (((cols[k]?).bind (·[pj.2]?)).map (·.1) = some pj.1.shape)

/-- The test reads of the rows the first chain's sampled columns alone. -/
theorem rowsShapedB_is (rows : List Johnson.G.SendRow) (ps : List PSeat) (n : ℕ) :
    rowsShapedB rows ps n = shapedAtB ((firstRows rows).map (·.sampled)) ps n := by
  unfold rowsShapedB shapedAtB
  refine congrArg _ (funext fun k => congrArg _ (funext fun pj => ?_))
  rw [List.getElem?_map]
  cases (firstRows rows)[k]? <;> rfl

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT.** -/
theorem shaped_written : shapedAtB radsFull psFull proofSends0.sends.length = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the columns moved by one sending. -/
theorem shaped_moved : shapedAtB (radsFull.drop 1) psFull proofSends0.sends.length = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A second: the first column's first shape with one main row more. -/
theorem shaped_other :
    shapedAtB (radsFull.zipIdx.map fun c => if c.2 = 0 then
        c.1.zipIdx.map fun e => if e.2 = 0 then
          ({ e.1.1 with mainRows := e.1.1.mainRows + 1 }, e.1.2) else e.1
      else c.1) psFull proofSends0.sends.length = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- How many pairs the test compares. -/
theorem shaped_count :
    (((List.range proofSends0.sends.length).map fun k => (mineAt psFull k).length).sum = 167) := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The field «rows», from the head (with the fourteen entry tests).** -/
theorem k8Rows_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ rows, P5T.rowsAt? Zp.pol Z.lay Zp.KL = some rows ∧
      P5T.radOneB ((P5T.firstRows rows).flatMap (·.sampled)) = true ∧
      rowsShapedB rows (P5J.At.pseats Zp) Zp.made.proof.1.sends.length = true := by
  obtain ⟨R, hR, -⟩ := IM.Seats.rows_at_head h.toAtMg
  have hy := (P5J.pins_of_laid h.toAtMg.scope h.toAtMg.laid).1
  have hc := VerifiableInference.Desc.LinkJoin.radii_in_scope h.toAtMg.scope h.toAtMg.laid.pub hy hR
  refine ⟨R, P1Opts.rows_at h.toAtMg.laid hR, P5T.radOne_of_radii hc, ?_⟩
  rw [rowsShapedB_is, hc, (P5J.written_at_head h.toAtMg).1]
  show shapedAtB radsFull (P5T.planSeats Zp Zp.D.1) proofSends0.sends.length = true
  rw [h.toAtMg.seats]
  exact shaped_written

end P1K8T

#print axioms P1K8T.rowsShapedB_is
#print axioms P1K8T.shaped_written
#print axioms P1K8T.shaped_moved
#print axioms P1K8T.shaped_other
#print axioms P1K8T.shaped_count
#print axioms P1K8T.k8Rows_at_head
