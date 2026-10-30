-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Digits/DigOut.lean: the output claim of the lookup on the digits of a smallness test,
as a list of plain forms on the entries.

A lookup ends with a masked claim on its joint keys at a point, and a list of linear rows
(`Cb.LdLkp.TX`, Cb/Ld/LdLkpTree.lean). At the digits the joint keys are entries or 0, shifted by θ
times the tag of their call (`CbQ.DatQ`, DatQ.lean). So the masked claim is a plain form on the
entries too.

Main names:
  `DatQ.OutD x mu`: the output claim at the out-statement x = ((the statement in front, θ), the
    masked claim, the rows): the masked claim holds of the shifted joint keys, and all rows hold.
  `DatQ.keyForm x`: the masked claim as a plain form: coefficients formK pt + mf, target tg - θ
    constK pt.
  `rowForm`: a row as a plain form.
  `DatQ.endCl x`: the list: the form of the masked claim, then the rows in their order. It is a
    function of x alone, and has 1 + (the number of x's rows) forms.
  `endCl_iff`: under `DatOK`: every form of `endCl x` holds at mu if and only if `OutD x mu`.
Limits: no lookup occurs: that `OutD` is the output claim of a given record of a lookup is by
unfolding, where that record is at hand. Nothing on which rows a lookup puts out, or how many.

-/
import Cb.Pv.Lookup.Digits.DatQ
import Cb.Ld.LdLkpTree
import Cb.G6.Led

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CbQ
open Finset Cb.LdLkp TWhole

/-- A row as a plain form. -/
def rowForm {E J : Type} (r : Row E J) : Form E J := ⟨r.cf, r.tg⟩

variable {I J E St : Type} [Field E] [Fintype I] [Fintype J] [DecidableEq J] (Q : DatQ I J)

namespace DatQ

/-- The output claim of the lookup on the digits. -/
def OutD (x : TX (St × E) E J) (μ : J → E) : Prop :=
  x.2.1.Holds Q.v (shKeyQ Q.fK (Q.key μ) Q.tagE x.1.2) μ ∧ RowsHold x.2.2 μ

/-- The masked claim on the joint keys as a plain form on the entries. -/
def keyForm (x : TX (St × E) E J) : Form E J :=
  ⟨fun n => Q.formK x.2.1.pt n + x.2.1.mf n, x.2.1.tg - x.1.2 * Q.constK x.2.1.pt⟩

/-- The output claim as a list of plain forms. -/
def endCl (x : TX (St × E) E J) : Ledger E J := Q.keyForm x :: x.2.2.map rowForm

end DatQ

omit [DecidableEq J] in
theorem rowForm_holds (r : Row E J) (μ : J → E) : (rowForm r).Holds μ ↔ r.Holds μ := by
  unfold rowForm Form.Holds Form.gap Row.Holds
  exact sub_eq_zero

theorem keyForm_holds {q H pp : ℕ} (h : Q.DatOK q H pp) (x : TX (St × E) E J) (μ : J → E) :
    (Q.keyForm x).Holds μ ↔ x.2.1.Holds Q.v (shKeyQ Q.fK (Q.key μ) Q.tagE x.1.2) μ := by
  unfold DatQ.keyForm Form.Holds Form.gap MCl.Holds
  rw [dgQ_form Q h μ x.1.2 x.2.1.pt]
  simp only [add_mul, sum_add_distrib]
  constructor <;> intro e <;> linear_combination e

/-- The list holds if and only if the output claim does. -/
theorem endCl_iff {q H pp : ℕ} (h : Q.DatOK q H pp) (x : TX (St × E) E J) (μ : J → E) :
    Ledger.Holds (Q.endCl x) μ ↔ Q.OutD x μ := by
  unfold Ledger.Holds DatQ.endCl DatQ.OutD RowsHold
  rw [List.forall_mem_cons, keyForm_holds Q h x μ, List.forall_mem_map]
  exact and_congr_right fun _ => forall₂_congr fun r _ => rowForm_holds r μ

omit [Fintype J] in
theorem endCl_length (x : TX (St × E) E J) : (Q.endCl x).length = 1 + x.2.2.length := by
  unfold DatQ.endCl
  rw [List.length_cons, List.length_map, Nat.add_comm]

end CbQ

#print axioms CbQ.keyForm_holds
#print axioms CbQ.endCl_iff
#print axioms CbQ.endCl_length
