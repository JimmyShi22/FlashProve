-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/LedgerTables.lean: the steps of `publicOfO` that ask the second hash function, IN
THE LETTERS OF THE LEDGER OF `publicOfO` (`publicOfO_of_parts`, Johnson/AtFull/Public/Ledger.lean:
each step's return as a named premise), at the second hash function and at all public files in the
goals' scope.
From the ledger's own first premise `p1 : polLayout Z.pol = .ok (P, y)`:
  **`ledger_tables`**: h3 (`y.h.p3 = true`) · p4 (table SILU) · p5 (table FS) · p10 (`ropeOf y.h`
    returns `ropeTable 12 500000 128 10`) · p11 (the rotary table).
  `ledger_h4`: h4 (`y.h.p4 = true`): so p14's step is run.
  `ledger_exp`: the comparison inside p14, at the array of the library's list `refL`.
  `ledger_hPar`: p7, from three sizes: `hParO_returns` (Johnson/Unfolds/SecondHashFunctionTree.lean) by name.
By `polScan_of_polLayout` (Johnson/Flat/ScalesSame.lean), `Hd.layout_of_polLayout`
(Johnson/Road/HeadMade.lean) and Johnson/Unfolds/TablesInScope.lean.
The three digests of lists of calls in the value that `publicOfO` returns (`callsDigestO`) are no
steps: they cannot refuse, and the ledger leaves them as terms. Where a later test reads
`Public.digests`, their values are owed there: not looked at here.
Limits. Calls alone. That `polLayout` returns is a premise. The three sizes are premises. That the
array which p14's step compares (`X.S.Tt` of the attention's first plan) is `refL.toArray` is not
said here: the attention's side's to show.

-/
import Johnson.Unfolds.TablesInScope
import Johnson.Unfolds.SecondHashFunctionTree
import Johnson.Flat.ScalesSame
import Johnson.Road.HeadMade

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify OnBytes.Road
open OnBytes.Model.Layer (Lay ropeTable)
open VerifiableInference.PlanWritten
open OnBytes.Road.L5 (refL)

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
  (hR : VerifierAndGoals.readFiles Z = .ok pp) {P : PolScan} {y : Lay}
  (p1 : polLayout Z.pol = .ok (P, y))
include hZ hR p1

/-- **h3 · p4 · p5 · p10 · p11 of the ledger, in scope.** -/
theorem ledger_tables :
    y.h.p3 = true ∧ tableHeldO secondHashFunction P .silu y.silu = .ok () ∧
      tableHeldO secondHashFunction P .sigmoid y.fs = .ok () ∧
      Layer.ropeOf y.h = .ok (ropeTable 12 500000 128 10) ∧
      tableHeldO secondHashFunction P .rope (ropeTable 12 500000 128 10) = .ok () :=
  have hs := VerifiableInference.OnPublicFiles.Flat.polScan_of_polLayout p1
  have hy := Hd.layout_of_polLayout p1
  have s := scan_at_policy hZ hR hs
  ⟨(tables_at_scan s hy).1, silu_step s hy, fs_step s hy, (tables_at_scan s hy).2.2.2,
    rope_held s⟩

/-- h4 of the ledger, in scope. -/
theorem ledger_h4 : y.h.p4 = true := by
  have hs := VerifiableInference.OnPublicFiles.Flat.polScan_of_polLayout p1
  have hh := layout_shape (Hd.layout_of_polLayout p1)
  rw [shape_of_scan (scan_at_policy hZ hR hs)] at hh
  rw [hh]
  rfl

/-- The comparison inside p14, at the array of `refL`. -/
theorem ledger_exp : tableHeldO secondHashFunction P .exp refL.toArray = .ok () :=
  have hs := VerifiableInference.OnPublicFiles.Flat.polScan_of_polLayout p1
  (tableHeldO_iff secondHashFunction P .exp _).2 fun d e => by
    rw [(expected_in_scope hZ hR hs).2.2.2] at e
    rw [← Option.some.inj e]
    exact (Exp.digest_of_list refL.toArray (by simp)).symm

end

/-- p7 of the ledger, from three sizes. -/
theorem ledger_hPar {pol KL lay : ByteArray} (hp : pol.size < 2 ^ 32)
    (hp' : tkOk (textSize pol.size) = true) (hk : tkOk KL.size = true) (hl : lay.size < 2 ^ 32)
    (hl' : tkOk (textSize lay.size) = true) : ∃ x, hParO secondHashFunction pol KL (some lay) = .ok x :=
  hParO_returns hp hp' hk hl hl'

end Johnson.Unfolds

#print axioms Johnson.Unfolds.ledger_tables
#print axioms Johnson.Unfolds.ledger_h4
#print axioms Johnson.Unfolds.ledger_exp
#print axioms Johnson.Unfolds.ledger_hPar
