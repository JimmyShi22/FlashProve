-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/WeightsShare.lean: what the pull-back of the merge's claim and the pending row pay of
what the chain of the own rounds of a layers' sub-proof that is not the first owes at its end.

Cb/Pv/Lay/At/OwnW.lean has the chain at a value, with the weights' stretch filled: the record of
Cb/Pv/Lay/At/FootW.lean at the pairs of Cb/Pv/Lay/At/TnSplit.lean. At that value this file gives the
fields lW, c7, o7 of the chain's bill (Cb/Pv/Lay/End/Last.lean), with the letters read off a last
statement e.

Main theorem: weights_share (from merge_pull in Cb/Pv/Lay/End/MergeShare.lean).

Limits. At this value lW and c7 are True. The two premises are o7's two claims in other words
(mergeU_iff, wt_ev_iff). The pending row (Pending in Cb/Pv/Lay/End/WeightsPay.lean) is a premise: it
leaves the sub-proof. That the ledger is a program's is not said here. The first sub-proof is not
here.


-/
import Cb.Pv.Lay.At.OwnW
import Cb.Pv.Lay.End.Last
import Cb.Pv.Lay.End.MergeShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)

noncomputable section

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {J₂ : Type} [Fintype J₂]

/-- The three fields of the chain's bill that belong to the weights' round and the merge, at the
chain's value, with the letters read off a last statement e. -/
theorem weights_share (a : J₂ → TWhole.Aff E P.wp0.J) (e : (P.layV P.wPart).toTail.s7.Nx) (m : M)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL a (mergeLed P.wp0 e.2)) (P.msg m))
    (hP : Pending P.wp0
      (rowW (fun c : Fin P.wp0.n => e.2.st.2 ^ (c : ℕ)) (fun c => P.wp0.ten c e.2.st.1)
        ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2))
      ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2)
      ((noKept P.wp0.wt.L.Sm).outB P.wp0.wt.L.Mk e.2) (e.2.vals ()) (P.msg m)) :
    (P.layV P.wPart).toTail.lW ((P.layV P.wPart).toTail.xW e)
        ((P.layV P.wPart).toTail.y7 e).1.2 m ∧
      (P.layV P.wPart).toTail.s7.Lc ((P.layV P.wPart).toTail.y7 e) e.1.2 m ∧
      (P.layV P.wPart).toTail.s7.Out e m :=
  ⟨trivial, trivial, merge_pull P.wp0 a e.2 (P.msg m) h hP⟩

end

end Cb.Pv.Lay.End.Gated
