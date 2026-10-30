-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/Look.lean: AN ARRAY's LOOK: its kind, number of rows, number of
columns, number of virtual rows: what the plan fixes of an array of a sub-proof's ledger and, by
reading, no routine behind the planner writes. Definitions and small lemmas: a light file, beneath
Johnson/Desc/First/Batch/Law/FitsAtS.lean, whose relation "goes on" carries the looks.

  `Look`, `look`. `look_rows_map`, `look_rows_modify`: a writing of the virtual rows that keeps
    their number leaves the look. `ofFrame`, `look_frame`, `looks_of_frame`: whatever leaves all but
    the weights' values (`treesFrame`, OnBytes/Model/HideLaws.lean) leaves the looks.
  `widths_of_looks`: the looks give the numbers of columns.
`Look`, `look`, `look_rows_map`, `look_rows_modify`, `ofFrame`, `look_frame` stood in
Johnson/Desc/First/Link/Law/LooksAre.lean, under these names, in this namespace; `looks_of_frame`
(the form on arrays of that file's `looks_frame`) and `widths_of_looks` are new. Nothing on
soundness.
-/
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model

/-- An array's kind, number of rows, number of columns, number of virtual rows. -/
abbrev Look : Type := HKind × Nat × Nat × Nat

/-- An array's look. -/
def look (X : HTree) : Look := (X.kind, X.R, X.K, X.rows.size)

theorem look_rows_map (X : HTree) (f : HRow → HRow) :
    look { X with rows := X.rows.map f } = look X := by
  simp [look]

theorem look_rows_modify (X : HTree) (r : Nat) (f : HRow → HRow) :
    look { X with rows := X.rows.modify r f } = look X := by
  simp [look]

/-- The look, off an array's frame. -/
def ofFrame (x : HTree × Array (HRow × Nat)) : Look := (x.1.kind, x.1.R, x.1.K, x.2.size)

theorem look_frame (X : HTree) : ofFrame X.frame = look X := by
  simp [ofFrame, HTree.frame, look]

/-- Whatever keeps the arrays' frame keeps their looks. -/
theorem looks_of_frame (A B : Array HTree) (h : treesFrame A = treesFrame B) :
    A.map look = B.map look := by
  have e : ∀ tr : Array HTree, tr.map look = (treesFrame tr).map ofFrame := by
    intro tr
    unfold treesFrame
    rw [Array.map_map]
    congr 1
    funext X
    exact (look_frame X).symm
  rw [e A, e B, h]

/-- The looks give the numbers of columns. -/
theorem widths_of_looks (A B : Array HTree) (h : A.map look = B.map look) :
    A.map (·.K) = B.map (·.K) := by
  have e : ∀ X : Array HTree, X.map (·.K) = (X.map look).map (·.2.2.1) := fun X => by
    simp [look, Array.map_map, Function.comp_def]
  rw [e A, e B, h]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.looks_of_frame
#print axioms VerifiableInference.Desc.LinkJoin.widths_of_looks
