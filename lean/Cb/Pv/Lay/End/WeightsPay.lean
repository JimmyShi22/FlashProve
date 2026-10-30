-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/WeightsPay.lean: what the chain of a layers' sub-proof's own rounds owes at its end
for the merge of the claims on the committed weights, from the claim that the merge leaves and one
equation on the matrix.

The chain owes at its end (Cb/Pv/Lay/End/Last.lean) all output claims of the merge's sumcheck: a row
on the hiding coefficients, and the row on the end value. At the records of Cb/Pv/Lay/At/FootW.lean,
where each claim is a pair (γ, ε), the merge's summand at a point ψ is the matrix under row weights
g and the equality weights of ψ on the columns, with g the sum over the claims of the claim's
coefficient times the extension of its ε at ψ times its γ. So the row on the end value is one
equation on the matrix: the pending row, which leaves the sub-proof.

Main definitions: rowW, rowWF (the row weights g), Pending (the equation).
Main theorems: summand_rows (one claim's summand at a point), merge_rows, first_rows (the merge's
summand at a point, in a later group and in the first), wt_ev_iff, wf_ev_iff (the row on the end
value is Pending), weights_pay, first_pay (the clause of the chain's bill).

Limits. hU (what the letter u7 says) and Pending are premises. Who tests the pending row is not
looked at. That the programs' row weights are these is not said here.


-/
import Cb.Pv.Lay.At.FootW
import Cb.Pv.Lay.OwnParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At

noncomputable section

section Rows

variable {E : Type} [Field E] {h k : ℕ}

/-- One claim's summand at a point: the extension of its ε, times the matrix under its γ on the rows
and the equality weights of the point on the columns. -/
theorem summand_rows (a : (Fin h → E) × ((Fin k → Bool) → E)) (W : Fin h → (Fin k → Bool) → E)
    (ψ : Fin k → E) :
    summand a W ψ = ∑ r, (Alg.mle a.2 ψ * a.1 r) * Alg.mle (W r) ψ := by
  unfold summand
  have e : Alg.mle (fun c => ∑ r, a.1 r * W r c) ψ = ∑ r, a.1 r * Alg.mle (W r) ψ := by
    unfold Alg.mle
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun r _ => sum_congr rfl fun c _ => by ring
  rw [e, mul_sum]
  exact sum_congr rfl fun r _ => by ring

/-- The row weights of the pending row: the sum over the claims of the coefficient times the
extension of the claim's ε at the point times its γ. -/
def rowW {n : ℕ} (co : Fin n → E) (ten : Fin n → (Fin h → E) × ((Fin k → Bool) → E))
    (ψ : Fin k → E) (r : Fin h) : E :=
  ∑ a, co a * (Alg.mle (ten a).2 ψ * (ten a).1 r)

/-- The combination of the claims' summands at a point is the matrix under the row weights. -/
theorem comb_rows {n : ℕ} (co : Fin n → E) (ten : Fin n → (Fin h → E) × ((Fin k → Bool) → E))
    (W : Fin h → (Fin k → Bool) → E) (ψ : Fin k → E) :
    ∑ a, co a * summand (ten a) W ψ = ∑ r, rowW co ten ψ r * Alg.mle (W r) ψ := by
  unfold rowW
  simp only [summand_rows, mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun r _ => sum_congr rfl fun a _ => by ring

end Rows

variable {E : Type} [Field E] [Fintype E] (P : FootW0 E)

/-- The pending row: the matrix under the row weights g and the equality weights of ψ, plus the mask
entry times the factor, is the value that was shown. -/
def Pending (g : Fin P.h → E) (ψ : Fin P.k → E) (β v : E) (m : P.J → E) : Prop :=
  ∑ r, g r * Alg.mle (P.Wm m r) ψ + m P.cAt * β = v

/-- The merge's summand at a point, in a later group. -/
theorem merge_rows (x : St7 E P.n × E) (m : P.J → E) (ψ : Fin P.k → E) :
    P.wt.L.f x m ψ =
      ∑ r, rowW (fun a : Fin P.n => x.2 ^ (a : ℕ)) (fun a => P.ten a x.1) ψ r *
        Alg.mle (P.Wm m r) ψ :=
  comb_rows (fun a : Fin P.n => x.2 ^ (a : ℕ)) (fun a => P.ten a x.1) (P.Wm m) ψ

/-- The row on the merge's end value is the pending row. -/
theorem wt_ev_iff (o : P.wt.L.toSum.T.par.Out) (m : P.J → E) :
    P.wt.L.toSum.T.par.EHolds o m () ↔
      Pending P (rowW (fun a : Fin P.n => o.st.2 ^ (a : ℕ)) (fun a => P.ten a o.st.1)
          ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o))
        ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o) ((noKept P.wt.L.Sm).outB P.wt.L.Mk o) (o.vals ())
        m := by
  rw [MergeL.kval_iff, merge_rows]
  rfl

/-- The clause that the chain owes at its end for the merge, in a later group. u7: the claim that
the merge leaves, as a proposition. -/
theorem weights_pay (o : P.wt.L.toSum.T.par.Out) (m : P.J → E) (u7 : Prop)
    (hU : u7 → P.wt.L.toSum.T.par.UHolds o m) (h7 : u7)
    (hP : Pending P (rowW (fun a : Fin P.n => o.st.2 ^ (a : ℕ)) (fun a => P.ten a o.st.1)
          ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o))
        ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o) ((noKept P.wt.L.Sm).outB P.wt.L.Mk o) (o.vals ())
        m) :
    P.wt.L.toSum.T.par.OutHolds o m :=
  ⟨hU h7, fun _ => (wt_ev_iff P o m).2 hP⟩

/-! ### The first group -/

section First

variable (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E))
  (rhs : St7 E P.n → (P.J → E) → E) (mkE : P.J)

/-- The row weights of the pending row in the first group: one claim more, under the next power. -/
def rowWF (st : St7 E P.n) (α : E) (ψ : Fin P.k → E) (r : Fin P.h) : E :=
  rowW (fun a : Fin P.n => α ^ (a : ℕ)) (fun a => P.ten a st) ψ r +
    α ^ P.n * (Alg.mle (tenE st).2 ψ * (tenE st).1 r)

/-- The merge's summand at a point, in the first group. -/
theorem first_rows (x : (P.wf tenE rhs mkE).St1) (m : P.J → E) (ψ : Fin P.k → E) :
    (P.wf tenE rhs mkE).L.f x m ψ =
      ∑ r, rowWF P tenE x.1.1 x.2 ψ r * Alg.mle (P.Wm m r) ψ := by
  show ∑ a : Fin P.n, x.2 ^ (a : ℕ) * summand (P.ten a x.1.1) (P.Wm m) ψ +
    x.2 ^ P.n * summand (tenE x.1.1) (P.Wm m) ψ = _
  rw [comb_rows (fun a : Fin P.n => x.2 ^ (a : ℕ)) (fun a => P.ten a x.1.1) (P.Wm m) ψ,
    summand_rows, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun r _ => ?_
  unfold rowWF
  ring

/-- The row on the merge's end value is the pending row. -/
theorem wf_ev_iff (o : (P.wf tenE rhs mkE).L.toSum.T.par.Out) (m : P.J → E) :
    (P.wf tenE rhs mkE).L.toSum.T.par.EHolds o m () ↔
      Pending P (rowWF P tenE o.st.1.1 o.st.2
          ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o))
        ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o)
        ((noKept (P.wf tenE rhs mkE).L.Sm).outB (P.wf tenE rhs mkE).L.Mk o) (o.vals ()) m := by
  rw [MergeL.kval_iff, first_rows]
  rfl

/-- The clause that the chain owes at its end for the merge, in the first group. -/
theorem first_pay (o : (P.wf tenE rhs mkE).L.toSum.T.par.Out) (m : P.J → E) (u7 : Prop)
    (hU : u7 → (P.wf tenE rhs mkE).L.toSum.T.par.UHolds o m) (h7 : u7)
    (hP : Pending P (rowWF P tenE o.st.1.1 o.st.2
          ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o))
        ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o)
        ((noKept (P.wf tenE rhs mkE).L.Sm).outB (P.wf tenE rhs mkE).L.Mk o) (o.vals ()) m) :
    (P.wf tenE rhs mkE).L.toSum.T.par.OutHolds o m :=
  ⟨hU h7, fun _ => (wf_ev_iff P tenE rhs mkE o m).2 hP⟩

end First

end

end Cb.Pv.Lay.End.Gated
