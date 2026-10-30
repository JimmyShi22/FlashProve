-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05NamedTable.lean: kind K5: EVERY ENTRY OF THE ARRAY OF THE READS THAT A
FORM OF THE KIND's NAMES LIES AT A TABLE: so the attention segments' arm of the one stated function
(uAtt A (funsAt A), Johnson/Desc/First/Att/K05WorldTieAt.lean) answers the stated sum there, and
never its "else 0".

Why. entryOf (Johnson/Desc/First/Att/Claims/TabsByChoice.lean) answers 0 where no table of the list
lies. The exchange at the block behind the second sending ("the committed cell is the arm in front")
would ask a committed cell to be 0 at such an entry.

IS IT EMPTY HERE? NO MEMBER IS SHOWN: that tablesP returns at a real geometry with nW ≠ 0 is shown
by nobody in these files.

Main names:
  `named_has_table`: where the claims' seat's reading answers (i, K) at a verifier's state s, and
    the tail's number of matrices is its list's size: an entry y with EntIn A.iU3 K A.nW y
    (Johnson/Desc/First/Att/Claims/Covered.lean: what Cov says of every entry of a form) has a table
    Fn of funsAt A s, a column c, a run sg and a position pos with tabAt Fn c sg = some pos, y.row =
    pos / K, y.idx = pos % K. THE PROOF's TWELVE LINES:
    typed without a compiler, laid here; over tables_tile
    (Johnson/Desc/First/Att/Claims/TablesTile.lean).
  `uAtt_at_named`: **so the arm at (y.row, y.idx) IS the stated sum of that table** (uAtt_is_sum,
    Johnson/Desc/First/Att/K05StatedArm.lean), where K is the plan's width.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05StatedArm
import Johnson.Desc.First.Att.Claims.TablesTile
import Johnson.Desc.First.Att.Claims.Covered

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ)
open K5Law (funsAt)

/-- **Every named entry lies at a table.** -/
theorem named_has_table (A : Attention.Plan) {s : First.S} {i : Runs.In} {K : ℕ} {y : Ent}
    (h : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, K))
    (hNM : A.seam.tl.NM = A.seam.tl.mats.size) (hy : K5Law.EntIn A.iU3 K A.nW y) :
    ∃ Fn ∈ funsAt A s, ∃ c sg pos, A.seam.tl.tabAt Fn c sg = some pos ∧ y.row = pos / K ∧
      y.idx = pos % K := by
  obtain ⟨x, hx, _, hr, hi⟩ := hy
  obtain ⟨lk, ht⟩ := tables_of_inOf h
  obtain ⟨Fn, hFn, c, sg, e⟩ := K5Law.tables_tile (tl := A.seam.tl) ht hNM x hx
  refine ⟨Fn, ?_, c, sg, x, e, hr, hi⟩
  unfold funsAt
  rw [h]
  show Fn ∈ (i.t.funs.map K5Law.funBack).toList
  rw [Array.toList_map]
  exact hFn

/-- **The arm at a named entry is the stated sum.** -/
theorem uAtt_at_named (A : Attention.Plan) {s : First.S} {i : Runs.In} {y : Ent}
    (h : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A))
    (hNM : A.seam.tl.NM = A.seam.tl.mats.size) (hy : K5Law.EntIn A.iU3 (plannedK A) A.nW y)
    (Dt : Bound GQ) (cN : ℕ × String) :
    ∃ Fn ∈ funsAt A s, ∃ c sg pos, A.seam.tl.tabAt Fn c sg = some pos ∧ y.row = pos / plannedK A ∧
      y.idx = pos % plannedK A ∧
      uAtt A (funsAt A) s Dt cN y.row y.idx =
        ∑ j ∈ Finset.range Fn.len, Reading.gl.val (Fn.phi.getD j zeroE) *
          matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) Dt Fn.mat (sg * Fn.len + j) c := by
  obtain ⟨Fn, hFn, c, sg, pos, e, hr, hi⟩ := named_has_table A h hNM hy
  refine ⟨Fn, hFn, c, sg, pos, e, hr, hi, ?_⟩
  rw [hr, hi]
  exact uAtt_is_sum A s Dt cN hFn e

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.named_has_table
#print axioms VerifiableInference.Desc.First.Att.P.uAtt_at_named
