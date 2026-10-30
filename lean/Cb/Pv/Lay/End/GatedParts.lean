-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/GatedParts.lean: the clauses of the two product layers of the gated products, of the
weights' round and of the merge in what the chain of a layers' sub-proof's own rounds owes at its
end, at a last statement made from parts whose three last outputs are honest.

Cb/Pv/Lay/End/Parts.lean makes a last statement from a record of its parts.
Cb/Pv/Lay/End/HonOut.lean gives, for any output of a sumcheck and any entries, the output with the
same state and point at which all output claims hold. This file applies gated_share
(Cb/Pv/Lay/End/GatedAt.lean) and weights_share (Cb/Pv/Lay/End/WeightsShare.lean) at such a
statement. Their premises on the ledgers and the pending row are shown by the converses of
Cb/Pv/Lay/End/GatedIff.lean. So the two shares' premises on the ledgers and the pending row can be
met together at any value of the letters, whatever the cells and the entries are.

Main theorems: gated_at_parts, weights_at_parts.

Limits. The statement need not be a run's. hfm, GoodNm and the sizes stay premises.


-/
import Cb.Pv.Lay.End.Parts
import Cb.Pv.Lay.End.HonOut
import Cb.Pv.Lay.End.GatedAt
import Cb.Pv.Lay.End.WeightsShare
import Cb.Pv.Lay.End.GatedIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The four clauses of the two product layers, at a statement whose outputs o5, o6 are honest; two
of them (c5, c6) are True at this chain. -/
theorem gated_at_parts (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (q : (P.layV P.wPart).toTail.Parts) (m : M) (s : ℕ) (h1 : 1 ≤ P.D.lL) (hs1 : s ≤ lF P.D)
    (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D) (a5 : P.fp.gp.toSum.T.par.Out)
    (a6 : P.fp.rt.L.toSum.T.par.Out) (h5 : q.o5 = honOut P.fp.gp.toSum.T.par a5 (P.msg m))
    (h6 : q.o6 = honOut P.fp.rt.L.toSum.T.par a6 (P.msg m))
    (hfm : ∀ x : GatedNm, x.InR P.D s →
      fm (ι x) = toAff (gatedFm P.rd P.D (gatedEAt P.fp q.o5 q.o6) s x))
    (hY : GoodNm Y ι P.D s) :
    (P.layV P.wPart).toTail.s5.Lc q.b4 q.r5 m ∧ (P.layV P.wPart).toTail.ow5 q.b5 m ∧
      (P.layV P.wPart).toTail.s6.Lc ((q.b5, q.d5), q.pR) q.r6 m ∧
      (P.layV P.wPart).toTail.ow6 q.b6 m := by
  have H5 : P.fp.gp.toSum.T.par.OutHolds q.o5 (P.msg m) := by
    rw [h5]
    exact honOut_holds _ a5 _
  have H6 : P.fp.rt.L.toSum.T.par.OutHolds q.o6 (P.msg m) := by
    rw [h6]
    exact honOut_holds _ a6 _
  exact gated_share P.toOwnPar P.wPart Y ι fm q.e m s h1 hs1 hs2 hfe hfm hY
    ((gated_pull_iff P.fp P.hrd Y ι fm q.o5 q.o6 (P.msg m) s h1 hs1 hs2 hfe hfm hY).2 ⟨H5, H6⟩)

omit [DecidableEq P.J] [DecidableEq J₂] in
/-- The three clauses of the weights' round and the merge, at a statement whose output o7 is
honest. -/
theorem weights_at_parts (a : J₂ → TWhole.Aff E P.wp0.J) (q : (P.layV P.wPart).toTail.Parts)
    (m : M) (a7 : P.wp0.wt.L.toSum.T.par.Out)
    (h7 : q.o7 = honOut P.wp0.wt.L.toSum.T.par a7 (P.msg m)) :
    (P.layV P.wPart).toTail.lW (q.b6, q.d6) q.sW m ∧
      (P.layV P.wPart).toTail.s7.Lc (((q.b6, q.d6), q.sW), q.cW) q.r7 m ∧
      (P.layV P.wPart).toTail.s7.Out q.e m := by
  have H7 : P.wp0.wt.L.toSum.T.par.OutHolds q.o7 (P.msg m) := by
    rw [h7]
    exact honOut_holds _ a7 _
  obtain ⟨hl, hp⟩ := (merge_pull_iff P.wp0 a q.o7 (P.msg m)).2 H7
  exact weights_share P a q.e m hl hp

end Cb.Pv.Lay.End.Gated
