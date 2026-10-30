-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WhOf.lean: the output matrix's weights, read off the stored table's cells;
and the bound "at most 2 ^ 12 in size", which the output head's laws take as a premise, at these
weights.

The stored table's cells are a matrix M of field elements. Johnson/Flat/LedgerClaim.lean says when
such a matrix holds an index (Holds M i: every entry of M is the cast of the index's digit, and the
index is 0 outside M's shape), that it holds at most one (holds_unique), and names it (indexOf).
"In range" (InRange M) is: M holds an index.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  whOf M: the output matrix H that the library's layout reads (Inst/Model/Layout.lean: weightsOf
      ppref kRef) in the index that M holds; THE ZERO MATRIX WHERE M HOLDS NONE.
  whOf_holds: where M holds the index i, whOf M is that index's output matrix.
  whOf_inRange: where M is in range there is such an index.
  whOf_none: where M is not in range, whOf M is 0 everywhere.
  whOf_abs, whOf_natAbs: |whOf M j v| is at most 2 ^ 12, AT EVERY M, WITH NO PREMISE: an index is
      well formed by its type, and the library's abs_H (Inst/Model/All/NoWrap.lean) reads the bound
      off that.

Every letter under "there is", and the clause that pins it. whOf_inRange: i by Holds M i (one alone,
under the two bounds on rows and cols: holds_unique).
What it does not say. THAT THE CELLS HOLD AN INDEX. Where they hold none the weights are 0, in
silence, and the bound is idle: a law at whOf M then speaks of the weights 0, not of the committed
bytes. That the decoded table is in range is the key file's side. That any block of a description
reads its weights off M: this file names no text. No chance in it. Nothing on soundness.

-/
import Mathlib
import Inst.Model.All.NoWrap
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE Holds InRange indexOf indexOf_eq)

/-- **The output matrix's weights, off the stored table's cells**: in the index that the matrix
holds; 0 where it holds none. -/
def whOf {rows cols : Nat} (M : Fin rows → Fin cols → GE) : Nat → Nat → Int :=
  match indexOf M with
  | some i => (Inst.Model.Layout.weightsOf Inst.Model.ppref kRef i.mat).H
  | none => fun _ _ => 0

namespace Came

variable {rows cols : Nat}

/-- **Where the cells hold an index, the weights are that index's output matrix.** -/
theorem whOf_holds (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i : Cm.Idx} (h : Holds M i) :
    whOf M = (Inst.Model.Layout.weightsOf Inst.Model.ppref kRef i.mat).H := by
  unfold whOf
  rw [indexOf_eq hr hc h]

/-- Where the cells are in range, there is such an index. -/
theorem whOf_inRange (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    (h : InRange M) :
    ∃ i : Cm.Idx, Holds M i ∧
      whOf M = (Inst.Model.Layout.weightsOf Inst.Model.ppref kRef i.mat).H := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi, whOf_holds hr hc hi⟩

/-- **Where the cells are not in range, the weights are 0.** -/
theorem whOf_none {M : Fin rows → Fin cols → GE} (h : ¬ InRange M) : whOf M = fun _ _ => 0 := by
  unfold whOf indexOf
  rw [dif_neg h]

/-- **The weights off the stored table's cells are at most 2 ^ 12 in size: at every matrix of
cells.** -/
theorem whOf_abs (M : Fin rows → Fin cols → GE) (j v : Nat) : |whOf M j v| ≤ 2 ^ 12 := by
  unfold whOf
  cases indexOf M with
  | none => norm_num
  | some i => exact Inst.Model.All.abs_H i.wf j v

/-- The same, in the form of the head's laws' premise. -/
theorem whOf_natAbs (M : Fin rows → Fin cols → GE) (j v : Nat) :
    (whOf M j v).natAbs ≤ 2 ^ 12 := by
  have h := whOf_abs M j v
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.whOf_holds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.whOf_inRange
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.whOf_none
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.whOf_abs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.whOf_natAbs
