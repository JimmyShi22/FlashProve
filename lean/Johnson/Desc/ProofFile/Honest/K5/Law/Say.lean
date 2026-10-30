-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Say.lean: CONDITIONAL: what the claims of an attention
segment's own rounds say (`SayAt`, Johnson/Desc/First/Att/Claims/SayAt.lean), from the rows' worth
and the rest. Statements with their proofs. The reading is the library's own (`Reading.gl`); the
world is any.

`SayAt` has clauses of three sorts: a slot is worth a written reader's form; a row that a masked
sumcheck leaves is worth 0; a form on slots alone (the first clause of `Say6`, on the two value
products, the accumulated output and the denominator). The claims' lists hold a second form on slots
alone, "the second end value is the first less 1"; `Say8` holds it folded into its clause on the end
values, at the odd numbers. Here the second sort is laid in, out of
`RowsZero` (Honest/K5/Law/RowsAt.lean), through the sentence on where the verifier's function for
the named points lays the rows (`PointsAre`, Johnson/Desc/First/Att/Claims/PointsRows.lean).

Main names:
  `rows_at_points`   each row, in the place where the claims read it, is worth 0
  `sayAt_of_rows`    **`SayAt`, from the rows and the rest.** CONDITIONAL on: `PointsAre`;
                     `RowsZero`; and, claim by claim, a premise that is handed the rows' worth and
                     owes the claim's sentence whole. Whoever reads the lone values and the end
                     values, and whoever says what lies under a slot, are meant to show these

Limits. The clauses of the first and the third sort are not touched: they stand inside the
premises, in the library's own forms. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RowsAt
import Johnson.Desc.First.Att.Claims.SayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open OnBytes.Attention (Shape)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard Left)
open K5Law (SayAt Say3 UnitAt Say5 Say6 Say7 Say8 PointsAre oldOf scoreBack tbBack remBack rows_are)

variable {W : World GE} {S : Shape} {gL : OnBytes.Model.Forest.Heard} {i : P.Runs.In} {K : Nat}
  {zk : Array (Array E)} {h : Heard} {L : Left}

/-- The rows in the places where the claims read them: each row that the named points hold is worth
0. CONDITIONAL on: the named points are those that the verifier's function lays of the rows L; every
row of L is worth 0. -/
theorem rows_at_points (H : PointsAre i.g zk h L i.p) (R : RowsZero W L) :
    (∀ x ∈ i.p.scores.toList.zipIdx, x.1.sc.row.value Reading.gl W = 0) ∧
      i.p.d.scE.row.value Reading.gl W = 0 ∧ i.p.d.vpm.row.value Reading.gl W = 0 ∧
      i.p.d.vpd.row.value Reading.gl W = 0 ∧ i.p.x.scF.row.value Reading.gl W = 0 ∧
      i.p.x.scd.row.value Reading.gl W = 0 ∧ i.p.x.scH.row.value Reading.gl W = 0 := by
  refine ⟨fun x hx => ?_, by rw [H.scE]; exact R.division, by rw [H.vpm]; exact R.below,
    by rw [H.vpd]; exact R.on, by rw [H.scF]; exact R.atIndex, by rw [H.scd]; exact R.key,
    by rw [H.scH]; exact R.cells⟩
  have hx' : i.p.scores.toList[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
  have e := congrArg (·[x.2]?) (rows_are H)
  simp only [List.getElem?_map, hx', Option.map_some] at e
  exact R.scores x.2 _ (by rw [← Array.getElem?_toList]; exact e.symm)

/-- **What the kind's claims say, from the rows and the rest.** CONDITIONAL on: the named points are
the verifier's; every row is worth 0; and, claim by claim, all that the claim says beside its rows:
each premise q is handed the rows' worth and owes the claim's sentence whole. -/
theorem sayAt_of_rows (H : PointsAre i.g zk h L i.p) (R : RowsZero W L)
    (q3 : Say3 Reading.gl W (oldOf S gL i) K)
    (q4 : ∀ x ∈ i.p.scores.toList.zipIdx, x.1.sc.row.value Reading.gl W = 0 →
      ∃ tb pc, i.t.score[x.2]? = some tb ∧ i.p.planes[x.1.claim]? = some pc ∧
        UnitAt Reading.gl W (oldOf S gL i) K (scoreBack x.1) (tbBack tb) (remBack pc))
    (q5 : i.p.d.scE.row.value Reading.gl W = 0 → Say5 Reading.gl W (oldOf S gL i) K)
    (q6 : i.p.d.vpm.row.value Reading.gl W = 0 → i.p.d.vpd.row.value Reading.gl W = 0 →
      Say6 Reading.gl W (oldOf S gL i) K)
    (q7 : i.p.x.scF.row.value Reading.gl W = 0 → i.p.x.scd.row.value Reading.gl W = 0 →
      Say7 Reading.gl W (oldOf S gL i) K)
    (q8 : i.p.x.scH.row.value Reading.gl W = 0 → Say8 Reading.gl W (oldOf S gL i) K) :
    SayAt Reading.gl W S gL i K := by
  obtain ⟨r4, r5, rM, rD, rF, rK, rH⟩ := rows_at_points H R
  exact ⟨q3, fun x hx => q4 x hx (r4 x hx), q5 r5, q6 rM rD, q7 rF rK, q8 rH⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.rows_at_points
#print axioms ProofFile.Honest.K5.sayAt_of_rows
