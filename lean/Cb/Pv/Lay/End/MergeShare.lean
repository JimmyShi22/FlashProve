-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/MergeShare.lean: all output claims of the merge of the claims on the committed
weights, from the pull-back of the ledger of the one claim that the merge leaves and from the
pending row.

Cb/Pv/Lay/End/WeightsPay.lean shows that the row on the merge's end value is the pending row.
Cb/Pv/Lay/End/RowForm.lean writes the claim that the merge leaves as a form and shows what it says.
This file puts the two together, at the records of Cb/Pv/Lay/At/FootW.lean, with the ledger entering
by its pull-back to the early entries (Cb/Sub/Late.lean).

Main definitions: mergeLed, mergeLedF (the ledger, in a later group and in the first).
Main theorems: merge_pull, merge_pull_first.

Limits. The pending row (Pending) is a premise: it leaves the sub-proof. Both premises are the
merge's two output claims in other words (mergeU_iff, wt_ev_iff, wf_ev_iff): a rewriting. The late
entries' forms play no part. That the ledger is a program's is not said here.


-/
import Cb.Pv.Lay.End.Led
import Cb.Pv.Lay.End.RowForm
import Cb.Pv.Lay.End.WeightsPay
import Cb.Sub.Late

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At

noncomputable section

variable {E : Type} [Field E] [Fintype E] (P : FootW0 E) {J₂ : Type} [Fintype J₂]

/-- The ledger of the one claim that the merge leaves, off the merge's output. -/
def mergeLed (o : P.wt.L.toSum.T.par.Out) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf [mergeU P.wt.L o]

/-- All output claims of the merge's sumcheck, in a later group. -/
theorem merge_pull (a : J₂ → TWhole.Aff E P.J) (o : P.wt.L.toSum.T.par.Out) (m : P.J → E)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL a (mergeLed P o)) m)
    (hP : Pending P (rowW (fun c : Fin P.n => o.st.2 ^ (c : ℕ)) (fun c => P.ten c o.st.1)
          ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o))
        ((noKept P.wt.L.Sm).outPt P.wt.L.Mk o) ((noKept P.wt.L.Sm).outB P.wt.L.Mk o) (o.vals ())
        m) :
    P.wt.L.toSum.T.par.OutHolds o m :=
  weights_pay P o m _ (mergeU_iff P.wt.L o m _).1
    ((ledOf_holds _ _).1 ((Cb.Sub.pullL_holds _ _ _).1 h) _ List.mem_cons_self) hP

variable (tenE : St7 E P.n → (Fin P.h → E) × ((Fin P.k → Bool) → E))
  (rhs : St7 E P.n → (P.J → E) → E) (mkE : P.J)

/-- The same ledger in the first group. -/
def mergeLedF (o : (P.wf tenE rhs mkE).L.toSum.T.par.Out) : TWhole.Ledger E (P.J ⊕ J₂) :=
  ledOf [mergeU (P.wf tenE rhs mkE).L o]

/-- All output claims of the merge's sumcheck, in the first group. -/
theorem merge_pull_first (a : J₂ → TWhole.Aff E P.J)
    (o : (P.wf tenE rhs mkE).L.toSum.T.par.Out) (m : P.J → E)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL a (mergeLedF P tenE rhs mkE o)) m)
    (hP : Pending P (rowWF P tenE o.st.1.1 o.st.2
          ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o))
        ((noKept (P.wf tenE rhs mkE).L.Sm).outPt (P.wf tenE rhs mkE).L.Mk o)
        ((noKept (P.wf tenE rhs mkE).L.Sm).outB (P.wf tenE rhs mkE).L.Mk o) (o.vals ()) m) :
    (P.wf tenE rhs mkE).L.toSum.T.par.OutHolds o m :=
  first_pay P tenE rhs mkE o m _ (mergeU_iff (P.wf tenE rhs mkE).L o m _).1
    ((ledOf_holds _ _).1 ((Cb.Sub.pullL_holds _ _ _).1 h) _ List.mem_cons_self) hP

end

end Cb.Pv.Lay.End.Gated
