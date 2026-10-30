-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayAllMeet.lean: the premises of lay_last_all can be met: at a last statement made
from a record of parts, the pull-back of the whole ledger holds, and so does what is asked beside
it.

lay_last_all (Cb/Pv/Lay/End/LayAll.lean) gives what the chain of a layers' sub-proof's own rounds
claims at its end from two premises on a last statement e and the messages: OkAt, and that the
pull-back of the whole ledger, eleven parts one after the other, holds. This file shows both at the
statement made from a record (Cb/Pv/Lay/End/Parts.lean) whose scalars and outputs are those of
Cb/Pv/Lay/End/NormsMeetAt.lean, trueOut (Cb/Pv/Lay/End/TermsIff.lean) and honOut
(Cb/Pv/Lay/End/HonOut.lean). The three parts of the ledger that are letters in lay_last_all are
empty here.

Main names:
  `noRest`: the three parts that stay letters, empty.
  `ok_at_parts`: OkAt at the statement made from the record.
  `ledger_at_parts`: the pull-back of the whole ledger holds there.
Limits. The statement made from the record need be no run's. NormsOk, TermsOk and GatedOk stay
premises, with equations on the record's own fields and three conditions on the cells of the norms'
ledgers and the selectors.


-/
import Cb.Pv.Lay.End.LayAll
import Cb.Pv.Lay.End.LayMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (d10 lDd lF lFe)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

/-- The pull-back of the empty ledger holds. -/
theorem pull_nil {E J₁ J₂ : Type} [Field E] [Fintype J₁] [Fintype J₂] (a : J₂ → Aff E J₁)
    (m : J₁ → E) : Ledger.Holds (pullL a ([] : Ledger E (J₁ ⊕ J₂))) m :=
  fun _ h => absurd h List.not_mem_nil

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- The three parts of the ledger that stay letters, empty. -/
def noRest (_ : (tailF P).s7.Nx) : Rest3 E (P.J ⊕ J₂) := ⟨[], [], []⟩

variable (q : (tailF P).Parts) (m : M) (p : Fin P.D.lT → E) (c σ dl e1 e2 : E)
  (ρj : Fin (P.D.lL + 1) → E) (pt1 : PPt P.nr.sq.R.L.toSum.T.par.fmt)
  (pt2 : PPt P.nr.rows.tok.toSum.T.par.fmt)
  (hx : q.x.2 = p) (hsL : q.sL = sWAt P.nr (P.msg m) p) (hcN : q.cN = c)
  (ho1 : q.o1 = o1At P.nr (P.msg m) p c ρj e1 pt1) (hsP : q.sP = sPAt P.nr (P.msg m) p dl)
  (hcP : q.cP = σ) (hr2 : q.r2 = fun _ => zAt P.nr (P.msg m) p dl σ)
  (ho2 : q.o2 = o2At P.nr (P.msg m) p dl σ e2 pt2)
  (a3 : P.tp.tm.toSum.T.par.Out) (a4 : P.ip.inn.toSum.T.par.Out) (heps : a3.eps ≠ 0)
  (h3 : q.o3 = trueOut P.tp a3 (P.msg m))
  (h4 : q.o4 = honOut P.ip.inn.toSum.T.par a4 (P.msg m))
  (a5 : P.fp.gp.toSum.T.par.Out) (a6 : P.fp.rt.L.toSum.T.par.Out)
  (h5 : q.o5 = honOut P.fp.gp.toSum.T.par a5 (P.msg m))
  (h6 : q.o6 = honOut P.fp.rt.L.toSum.T.par a6 (P.msg m))
  (a7 : P.wp0.wt.L.toSum.T.par.Out) (h7 : q.o7 = honOut P.wp0.wt.L.toSum.T.par a7 (P.msg m))

include hcN ho1 heps h3 h7 in
omit [Fintype J₂] [DecidableEq J₂] in
/-- What is asked beside the ledger holds at the statement made from the record. -/
theorem ok_at_parts : OkAt P (fun _ _ => True) q.e m := by
  have H7 : P.wp0.wt.L.toSum.T.par.OutHolds q.o7 (P.msg m) := by
    rw [h7]
    exact honOut_holds _ a7 _
  refine ⟨?_, ?_, ((merge_pull_iff P.wp0 (fun x : Empty => x.elim) q.o7 (P.msg m)).2 H7).2, trivial⟩
  · show q.o1.st.1.2 = q.cN
    rw [ho1, hcN]
    rfl
  · show q.o3.eps ≠ 0
    rw [h3]
    exact heps

variable {fm : (tailF P).s7.Nx → Nm → Aff E P.J} {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}
  (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
  (G : GatedOk P Y ιG fm sG)
  (h12 : ∀ ν, ν < P.D.nNu → l1 (Dgs P.nr (P.msg m) p ν) + h1 (Dgs P.nr (P.msg m) p ν) -
    2 * sig (Dgs P.nr (P.msg m) p ν) = 0)
  (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P.nr (P.msg m) p ν) + rq (Dgs P.nr (P.msg m) p ν) -
    sig (Dgs P.nr (P.msg m) p ν) + 1 = 0)
  (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd (P.msg m)) l) (zt q.e) = 0)

include hx hsL hcN ho1 hsP hcP hr2 ho2 h3 h4 h5 h6 h7 N Tm G h12 h16 hHot in
/-- The pull-back of the whole ledger holds at the statement made from the record. -/
theorem ledger_at_parts :
    Ledger.Holds (pullL (lateA Y (fm q.e))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG (noRest P) sG) zt b B q.e).all)
      (P.msg m) := by
  have hN := led_at_parts P.toOwnPar P.wPart Y ιN (fm q.e) q m p c σ dl e1 e2 ρj pt1 pt2 (zt q.e)
    hx hsL hcN ho1 hsP hcP hr2 ho2 b s B N.hl N.hd N.hB (N.hfm q.e) N.gXi N.gP N.gR N.gS h12 h16
    hHot
  rw [ledAt_eq, pull_append, pull_append, pull_append] at hN
  have hT : Ledger.Holds (pullL (lateA Y (fm q.e)) (termsLed P.tp (readsT Y ιT) q.o3))
      (P.msg m) := by
    have hf := Tm.hfm q.e
    have e3 : ((tailF P).b3 q.e).2 = trueOut P.tp a3 (P.msg m) := h3
    rw [e3] at hf
    rw [h3]
    exact terms_meets P.toOwnPar Y ιT (fm q.e) a3 m hf Tm.gR Tm.gC Tm.gS
  have hS : Ledger.Holds (pullL (lateA Y (fm q.e)) (stackLed P.ip q.o4)) (P.msg m) := by
    rw [h4]
    exact stack_meets P.toOwnPar (lateA Y (fm q.e)) a4 m
  have H5 : P.fp.gp.toSum.T.par.OutHolds q.o5 (P.msg m) := by
    rw [h5]
    exact honOut_holds _ a5 _
  have H6 : P.fp.rt.L.toSum.T.par.OutHolds q.o6 (P.msg m) := by
    rw [h6]
    exact honOut_holds _ a6 _
  have H7 : P.wp0.wt.L.toSum.T.par.OutHolds q.o7 (P.msg m) := by
    rw [h7]
    exact honOut_holds _ a7 _
  have hG := (gated_pull_iff P.fp P.hrd Y ιG (fm q.e) q.o5 q.o6 (P.msg m) sG G.h1 G.hs1 G.hs2 G.hfe
    (G.hfm q.e) G.hY).2 ⟨H5, H6⟩
  have hM := ((merge_pull_iff P.wp0 (lateA Y (fm q.e)) q.o7 (P.msg m)).2 H7).1
  exact (holds_all _ _ _).2 ⟨pull_nil _ _, hN.1, hN.2.1, hN.2.2.1, hT, hG, hN.2.2.2, pull_nil _ _,
    pull_nil _ _, hS, hM⟩

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.ok_at_parts
#print axioms Cb.Pv.Lay.End.ledger_at_parts
