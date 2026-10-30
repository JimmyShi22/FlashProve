-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/RowForm.lean: the first output claim of a sumcheck, the row on the hiding
coefficients, as a form on committed entries.

Cb/Ld/LdPsc.lean writes the first output claim of its sumcheck as a linear row with a public target
(slU, tU; psc_row_U), where the kept maps are linear in the entries. This file carries that row to a
form of Blocks/Form.lean on early and late entries, in which the files of this folder write the
verifier's claims, and gives it for a product layer and for the merge, which keep no map.

Main definitions: uForm, prodU, mergeU. Main theorems: uForm_val, uForm_iff (the form is worth 0
exactly if the first output claim holds), prodU_iff, mergeU_iff.

Limits. That a program's claim is this form is not said here.


-/
import Cb.Ld.LdPscProofsIor
import Cb.Pv.Lay.OwnParts
import Blocks.Form

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay

noncomputable section

variable {E : Type} [Field E] [Fintype E] {J₂ : Type}

/-- The first output claim as a form: the row's coefficients on the early entries, 0 on the late
ones, and the target. -/
def uForm (Y : PscPar E) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E) (o : Y.Out) :
    Blocks.Form (Y.J ⊕ J₂) E
  | none => -Y.tU o
  | some (.inl j) => Y.slU rowB o j
  | some (.inr _) => 0

variable [Fintype J₂]

omit [Fintype E] in
theorem uForm_val (Y : PscPar E) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E)
    (o : Y.Out) (m : Y.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (uForm (J₂ := J₂) Y rowB o) =
      ∑ j, Y.slU rowB o j * m j - Y.tU o := by
  rw [Blocks.Form.val_apply, Fintype.sum_sum_type]
  show -Y.tU o + (∑ j, Y.slU rowB o j * m j + ∑ j : J₂, (0 : E) * u j) = _
  simp only [zero_mul, sum_const_zero, add_zero]
  ring

omit [Fintype E] in
/-- The form is worth 0 exactly if the first output claim holds. -/
theorem uForm_iff (Y : PscPar E) (rowB : (st : Y.St) → Y.B → HPt (Y.vars st) → Y.J → E)
    (hB : Y.LinB rowB) (o : Y.Out) (m : Y.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (uForm (J₂ := J₂) Y rowB o) = 0 ↔ Y.UHolds o m := by
  rw [uForm_val, psc_row_U E Y rowB hB o m, sub_eq_zero]
  rfl

/-- The first output claim of a product layer's sumcheck. -/
def prodU (L : ProdL E) (o : L.toSum.T.par.Out) : Blocks.Form (L.J ⊕ J₂) E :=
  uForm L.toSum.T.par (fun _ b => Empty.elim b) o

theorem prodU_iff (L : ProdL E) (o : L.toSum.T.par.Out) (m : L.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (prodU (J₂ := J₂) L o) = 0 ↔ L.toSum.T.par.UHolds o m :=
  uForm_iff L.toSum.T.par _ (fun _ _ b _ => Empty.elim b) o m u

/-- The first output claim of the merge's sumcheck. -/
def mergeU (L : MergeL E) (o : L.toSum.T.par.Out) : Blocks.Form (L.J ⊕ J₂) E :=
  uForm L.toSum.T.par (fun _ b => Empty.elim b) o

theorem mergeU_iff (L : MergeL E) (o : L.toSum.T.par.Out) (m : L.J → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (mergeU (J₂ := J₂) L o) = 0 ↔ L.toSum.T.par.UHolds o m :=
  uForm_iff L.toSum.T.par _ (fun _ _ b _ => Empty.elim b) o m u

end

end Cb.Pv.Lay.End.Gated
