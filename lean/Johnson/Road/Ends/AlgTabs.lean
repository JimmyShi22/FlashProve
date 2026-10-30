-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgTabs.lean: that the lookup's records of a group's eight calls have the
library's tables, as ONE test, with its theorem.
States: (isLut_of_test) Hd.IsLut c T (Johnson/Road/HeadTabs.lean: as many rows; row by row the
verifier's word is the residue of a natural number that is the library's entry; so is the padding
row's) follows from the Bool isLutB c T, which walks through all rows of T.
(hL_of_tablesB) if tablesB y says true, then for every call cc the lookup's record y.fo.calls[cc] is
there and has the library's table lut tbRef cc: the premise hL of AlgBridgeTest.lean,
AlgBridgeRec.lean and AlgBridgeOne.lean.
Does not say: that tablesB is true at any layout (a run decides it: seven tables of 2^16 rows and
one of 2^8).
-/
import Inst.Model.TablesRef
import Inst.Model.FF.Index
import Johnson.Road.HeadTabs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open OnBytes.Model (Call)
open OnBytes.Model.Layer (Lay)
open Inst.Model (Lut tbRef)
open Inst.Model.FFSeg (lut)

/-- Whether the call's record c has the library's table T: as many rows; in every row, and in the
padding row, the library's entry is not negative and the verifier's word is its residue. -/
def isLutB (c : Call) (T : Lut) : Bool :=
  2 ^ c.k == T.rows &&
    ((List.range T.rows).all fun u =>
      decide (0 ≤ T.row u) && c.tauAt u == Model.fOfNat (T.row u).toNat) &&
    decide (0 ≤ T.pad) && c.tauAt c.t0 == Model.fOfNat T.pad.toNat

/-- **If the test says true, the record has the table.** -/
theorem isLut_of_test {c : Call} {T : Lut} (t : isLutB c T = true) : Hd.IsLut c T := by
  unfold isLutB at t
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at t
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := t
  refine ⟨h1, fun u hu => ?_, ⟨T.pad.toNat, h4, Int.toNat_of_nonneg h3⟩⟩
  have h := List.all_eq_true.mp h2 u (List.mem_range.mpr hu)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨(T.row u).toNat, h.2, Int.toNat_of_nonneg h.1⟩

/-- The eight records of the lookup of a layout, against the library's reference tables. -/
def tablesB (y : Lay) : Bool :=
  (List.finRange 8).all fun cc =>
    match y.fo.calls[cc.val]? with
    | some c0 => isLutB c0 (lut tbRef cc)
    | none => false

/-- **hL from one test.** -/
theorem hL_of_tablesB {y : Lay} (t : tablesB y = true) :
    ∀ cc : Fin 8, ∃ c0 : Call, y.fo.calls[cc.val]? = some c0 ∧ Hd.IsLut c0 (lut tbRef cc) := by
  intro cc
  have h := List.all_eq_true.mp t cc (List.mem_finRange cc)
  cases e : y.fo.calls[cc.val]? with
  | none =>
    simp only [e] at h
    cases h
  | some c0 =>
    simp only [e] at h
    exact ⟨c0, rfl, isLut_of_test h⟩

#print axioms isLut_of_test
#print axioms hL_of_tablesB

end OnBytes.Road.Alg
