-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFF.lean: the families of keys of the feed-forward segment of group g (all of the group's four
layers but attention itself, from queries, keys and values to its output o; 34 families of keys,
among them the seven that hold a matrix product with weights: queries and keys with the rotation,
values, output projection, gate, up and down projections with the routed experts, router; see the
head of Cm/SegFFMat.lean), and the sizes of their tables. The segment itself, over p = 2^64 - 2^32 +
1: Cm/TargetSegFF.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`). A segment has the shape of its matrix of cells, its families of identities and
its families of keys with their tables. Keys (`FFSeg.key`), identities (`FFSeg.idnVal`) and the
relation's part `FFSeg.trace` are those of Inst/Model/FF/Trace.lean. Group g is four consecutive
layers of the model; its feed-forward segment is segment 2 g of Cm/SegLayout.lean.

Main names:
  `allFams`: all families. `tOf s`, `rows_eq`: log2 of the number of rows of the table of a family.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegPilotAff
import Cm.SegFFAffPass
import Inst.Model.TablesSanity

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl]

/-! ## Tables -/

/-- all families -/
def allFams : List FFSeg.Fam :=
  [.G, .U, .UT, .QK, .N1, .N2, .O, .D, .V, .LR, .XR, .LT, .DD, .GH, .UH, .OH, .DH, .VH, .LH, .QKH,
    .N1H, .N2H, .ROW, .SEL, .L3, .G0, .CN1, .CN2, .CQK, .CV, .CLR, .F, .MR, .CG]

theorem mem_allFams (s : FFSeg.Fam) : s ∈ allFams := by cases s <;> decide

/-- log2 of the number of rows of the table of a family -/
def tOf (s : FFSeg.Fam) : ℕ := if FFSeg.call s = 3 then 8 else 16

theorem rows_eq (tb : Tables) (s : FFSeg.Fam) : (FFSeg.lut tb (FFSeg.call s)).rows = 2 ^ tOf s := by
  cases s <;> rfl

end Cm.Seg
