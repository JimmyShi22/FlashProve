-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsRows.lean: the two claims that the norms' sumchecks themselves leave, as the
library's own rows; and what the ledger of the claims on the norms then pays.

In Cb/Pv/Lay/End/NormsCl.lean the claims that the two sumchecks leave are letters u1, u2, and
Cb/Pv/Lay/End/NormsPay.lean asks as premises that they say the sumchecks' first output claims. Here
they are the forms of Cb/Sub/SeatPsc.lean (formU), which are made of the library's own rows on the
hiding coefficients, read as forms on early and late entries. The two premises fall away.

Main definitions: upForm (a claim on early entries as a form on early and late entries), u1At, u2At.
Main theorems: val_upForm, norms_pay_rows.

Limits: as Cb/Pv/Lay/End/NormsPay.lean, without its premises hU1 and hU2.


-/
import Cb.Sub.SeatPsc
import Cb.Pv.Lay.End.NormsPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

section Up

variable {E J₁ J₂ : Type} [Field E]

/-- A claim on early entries as a form on early and late entries: worth the claim's gap. -/
def upForm (f : TWhole.Form E J₁) : Blocks.Form (J₁ ⊕ J₂) E :=
  fun o => o.elim (-f.tg) (Sum.elim f.co fun _ => 0)

theorem val_upForm [Fintype J₁] [Fintype J₂] (f : TWhole.Form E J₁) (m : J₁ → E) (u : J₂ → E) :
    Blocks.Form.val (Sum.elim m u) (upForm (J₂ := J₂) f) = f.gap m := by
  rw [Blocks.Form.val_apply, Fintype.sum_sum_type]
  simp only [upForm, Option.elim, Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero,
    add_zero]
  unfold TWhole.Form.gap
  ring

end Up

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) {J₂ : Type} [Fintype J₂]
  [DecidableEq P.J] [DecidableEq J₂]

/-- The claim that the product layer of the squares leaves. It has no kept map. -/
noncomputable def u1At (o1 : P.sq.R.L.toSum.T.par.Out) : Blocks.Form (P.J ⊕ J₂) E :=
  upForm (Cb.Sub.formU P.sq.R.L.toSum.T.par (fun _ b _ _ => Empty.elim b) o1)

/-- The claim that the token sumcheck of the row products leaves. It has no kept map. -/
noncomputable def u2At (o2 : P.rows.tok.toSum.T.par.Out) : Blocks.Form (P.J ⊕ J₂) E :=
  upForm (Cb.Sub.formU P.rows.tok.toSum.T.par (fun _ b _ _ => Empty.elim b) o2)

/-- The five clauses that the chain owes at its end for the norms, from the ledger and the true
tables. -/
theorem norms_pay_rows (U : NormsReads J₂) (p : Fin P.D.lT → E) (sW : Fin (P.D.nNu * 9) → E)
    (c : E) (o1 : P.sq.R.L.toSum.T.par.Out) (sP : Fin (P.D.nNu * 7) → E) (σ z : E)
    (o2 : P.rows.tok.toSum.T.par.Out) (zt : ℕ → E) (m : P.J → E) (u : J₂ → E) (b s B : ℕ)
    (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b) (hst : o1.st.1.2 = c)
    (T : TablesTrue (namesAt P U) (normsEAt P p sW c o1 sP σ z o2 zt) P.D (P.rd m) (P.D.lL + 1) b s
      B (Sum.elim m u))
    (h : TWhole.Ledger.Holds (normsLed (namesAt P U) (normsEAt P p sW c o1 sP σ z o2 zt)
      (u1At P o1) (u2At P o2) P.D (P.D.lL + 1) b B) (Sum.elim m u)) :
    P.sq.B ((p, fun q => sW (finProdFinEquiv q)), c) m ∧
      P.sq.R.L.toSum.T.par.OutHolds o1 m ∧
      (P.rows.led p m fun n => sP n - m (P.mkP n)) ∧ P.rows.tie ((p, sP), σ) z m ∧
      P.rows.tok.toSum.T.par.OutHolds o2 m :=
  norms_pay P U p sW c o1 sP σ z o2 zt _ _ m u b s B hl hd hB hst T h
    (fun k => (Cb.Sub.formU_holds _ _ (fun _ _ b _ => Empty.elim b) o1 m).1 (by
      unfold u1At at k
      rw [val_upForm] at k
      exact k))
    (fun k => (Cb.Sub.formU_holds _ _ (fun _ _ b _ => Empty.elim b) o2 m).1 (by
      unfold u2At at k
      rw [val_upForm] at k
      exact k))

end Cb.Pv.Lay.End
