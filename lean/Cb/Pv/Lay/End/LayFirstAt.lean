-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayFirstAt.lean: at the last statement of a run of the own rounds of the FIRST layers'
sub-proof, the pull-back of the ledger clFirst (written down in Cb/Pv/Lay/End/LayFirst.lean) gives
what the stages owe.

Cb/Pv/Lay/End/LayHEndAt.lean says this of a layers' sub-proof that is not the first. This file says
it of the chain of the first sub-proof (P.ownF, Cb/Pv/Lay/At/OwnFirstW.lean), from
Cb/Pv/Lay/End/LayFirst.lean. That chain draws three points before its stages. That the coefficient
drawn in the sumcheck of the terms is not 0 is a premise at the run, in the letters of
Cb/Pv/Lay/OwnTest.lean (LayVOF.epsOK): there a run that draws 0 is refused.

Main definitions: chFst (the chain with its three points), OkMoreF (what is asked beside the ledger,
St1OkF and the coefficient: the pending row, and the letter Ok').
Main theorems.
 - lay_owed_first: at a run with epsOK: Dn, and Ch.Owed of the chain.
 - owed0_first: what the chain owes gives what the chain without the claim on the coefficient owes
   (LayVOF.toOwn0).
 - lay_hEnd_first: with what rides: at every run with epsOK that meets A0.on and B0's relation: from
   the pull-back of the whole ledger: A0's relation, Dn, and Ch.Owed of LayVOF.toOwn0.

Limits. NormsOkF, TermsOkF, GatedOkF, EmbOkF are premises. In lay_hEnd_first three premises range
over the runs with epsOK that meet A0.on and B0's relation: hA0 (what rides is handed on); hDn (the
claim of the first statement, from the whole ledger); hM (the pending row). Of the three things that
it concludes, A0's relation and Dn are the premises hA0 and hDn; what the stages owe is derived. The
pending row holds the transcript's last message: hM can hold only where B0's relation itself carries
that row. No run is shown here at which the coefficient is not 0 and B0's relation and the ledger's
pull-back hold. That the ledger is a program's is not said here. All limits of
Cb/Pv/Lay/End/LayFirst.lean.


-/
import Cb.Pv.Att.ChainLast
import Cb.Pv.Lay.End.LayFirst
import Cb.Pv.Lay.OwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Iop TWhole Cb IOR Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂}
  {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm} {ιE : EmbNm → Nm}

/-- The chain of the first sub-proof's own rounds, with its three points. -/
noncomputable abbrev chFst : Ch E M X := P.ownF.toOwn.ch

/-- What is asked of a last statement and the messages beside the ledger, St1OkF and the
coefficient. -/
def OkMoreF (Ok' : (tailW P).s7.Nx → M → Prop) (e : (tailW P).s7.Nx) (m : M) : Prop :=
  Pending P.wp0 (rowWF P.wp0 (tenEF P) e.2.st.1.1 e.2.st.2
      ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2))
    ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2) ((noKept P.wf.L.Sm).outB P.wf.L.Mk e.2)
    (e.2.vals ()) (P.msg m) ∧ Ok' e m

/-- At a run at which the coefficient is not 0: the claim of the first statement, and what the
stages owe. -/
theorem lay_owed_first {fm : (tailW P).s7.Nx → Nm → Aff E P.J} {zt : (tailW P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B) (Tm : TermsOkF P Y ιT fm)
    (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (Dn : X → M → Prop)
    (Ok' : (tailW P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkFirst P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) →
      Dn ((tailW P).xL e).1.1.1 m)
    (x : X) (ts : (chFst P).Trs) (m : M) (ht : P.ownF.epsOK ((chFst P).run x ts))
    (hM : OkMoreF P Ok' ((chFst P).run x ts) m)
    (h : Ledger.Holds (pullL (lateA Y (fm ((chFst P).run x ts)))
      (clFirst P Y ιN ιT ιG ιE R zt b B sG ((chFst P).run x ts)).all) (P.msg m)) :
    Dn x m ∧ (chFst P).Owed x ts m := by
  refine (Ch.last_run (chFst P) Dn x ts m).1 ?_
  have hr : St1OkF P ((chFst P).run x ts) :=
    hst_run_first P.ofp P.wfPart (((x, ts.1), ts.2.1), ts.2.2.1) ts.2.2.2
  exact lay_last_first P N Tm G Em R (fun b m => Dn b.1.1.1 m) Ok' dn ((chFst P).run x ts) m
    ⟨hr, ht, hM⟩ h

omit [Fintype J₂] [DecidableEq J₂] in
/-- What the chain owes gives what the chain without the claim on the coefficient owes. -/
theorem owed0_first (x : X) (ts : (chFst P).Trs) (m : M) (h : (chFst P).Owed x ts m) :
    P.ownF.toOwn0.ch.Owed x ts m := by
  have h1 : (chFst P).Last (fun _ _ => True) ((chFst P).run x ts) m :=
    (Ch.last_run (chFst P) _ x ts m).2 ⟨trivial, h⟩
  have h2 : P.ownF.toOwn0.ch.Last (fun _ _ => True) (P.ownF.toOwn0.ch.run x ts) m :=
    LayTail.last_withOw3 (P.ownF.V.toTail.withOw3 fun b m =>
        ∀ a, P.ownF.V.Tm.toSum.T.par.EHolds b.2 (P.ownF.V.rd3 m) a) P.ownF.V.toTail.ow3
      (fun _ _ => True) ((chFst P).run x ts) m (fun g => g.2) h1
  exact ((Ch.last_run P.ownF.toOwn0.ch _ x ts m).1 h2).2

/-- With what rides: at the runs at which the coefficient is not 0. -/
theorem lay_hEnd_first {fm : (tailW P).s7.Nx → Nm → Aff E P.J} {zt : (tailW P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B) (Tm : TermsOkF P Y ιT fm)
    (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (Dn : X → M → Prop)
    {Kc X0 Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (B0 : Rels Kc (chFst P).End Ex (M × Wp))
    (hA0 : ∀ x ts y w, P.ownF.epsOK ((chFst P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chFst P).run x ts, y) w → A0.relR (pr x, y) w)
    (hDn : ∀ x ts y w, P.ownF.epsOK ((chFst P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chFst P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chFst P).run x ts)))
        (clFirst P Y ιN ιT ιG ιE R zt b B sG ((chFst P).run x ts)).all) (P.msg w.1) → Dn x w.1)
    (hM : ∀ x ts y w, P.ownF.epsOK ((chFst P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chFst P).run x ts, y) w →
      OkMoreF P (fun _ _ => True) ((chFst P).run x ts) w.1) :
    ∀ x ts y w, P.ownF.epsOK ((chFst P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chFst P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chFst P).run x ts)))
        (clFirst P Y ιN ιT ιG ιE R zt b B sG ((chFst P).run x ts)).all) (P.msg w.1) →
      A0.relR (pr x, y) w ∧ Dn x w.1 ∧ P.ownF.toOwn0.ch.Owed x ts w.1 :=
  fun x ts y w ht ho hf hL =>
    ⟨hA0 x ts y w ht ho hf, hDn x ts y w ht ho hf hL,
      owed0_first P x ts w.1 (lay_owed_first P N Tm G Em R (fun _ _ => True) (fun _ _ => True)
        (fun _ _ _ _ _ _ => trivial) x ts w.1 ht (hM x ts y w ht ho hf) hL).2⟩

end Cb.Pv.Lay.End
