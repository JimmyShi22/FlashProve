-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Cut/CutBent.lean: A SECOND NEGATIVE TEST TO `cut_written`
(Johnson/AtFull/Cut/CutAtWritten.lean): THE COMPARISON WITH THE 477 WRITTEN ROWS BITES: against the
written table with ONE number bent (row number 240's "take" one higher) the eager twin's value at
the
written rounds' entries is NOT that table. One decision of Lean's kernel, stated positively: a Bool
that compares the two tables row by row, field by field, is false.
  `sameCutsB`: two tables are one, as a Bool. `bent`: the written table with the one number bent.
  **`cutK_bent`**: `((cutOfK ‹the entries›).map fun C => sameCutsB C bent) = some false`.
  The control (the same Bool against the written table itself: `some true`): CutStraight.lean [not in this library].
Limits. One bent number at one place. The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.G.DryProofLit
import Johnson.AtFull.Cut.CutEager
import Johnson.AtFull.Cut.CutWrittenLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Cut
open VerifiableInference.Desc.First
open Johnson.G (dryProofFull)

/-- Two rows are one, field by field. -/
def sameCutB (a b : Cut) : Bool :=
  a.look == b.look && a.step == b.step && a.place == b.place && a.kind == b.kind && a.take == b.take

/-- Two tables are one. -/
def sameCutsB : List Cut → List Cut → Bool
  | [], [] => true
  | a :: as, b :: bs => sameCutB a b && sameCutsB as bs
  | _, _ => false

/-- The written table, row number 240's "take" one higher. -/
def bent : List Cut :=
  cutWritten.take 240 ++ (cutWritten.drop 240).modifyHead fun c => { c with take := c.take + 1 }

set_option maxRecDepth 1000000 in
/-- **Against the bent table: no.** -/
theorem cutK_bent :
    ((cutOfK (dryProofFull.1.map (·.1.entry))).map fun C => sameCutsB C bent) = some false := by
  decide +kernel

end Johnson.AtFull.Cut

#print axioms Johnson.AtFull.Cut.cutK_bent
