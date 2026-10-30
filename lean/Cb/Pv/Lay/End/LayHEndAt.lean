-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayHEndAt.lean: at the last statement of a run of the own rounds of a layers'
sub-proof that is not the first, the pull-back of the ledger of the verifier's claims gives what the
stages owe.

The seam behind a layers' own rounds refuses a last statement in which the coefficient drawn in the
sumcheck of the terms is 0 (LayVO.epsOK, Cb/Pv/Lay/OwnTest.lean). It asks, at each run at which that
coefficient is not 0: from what rides and the pull-back of the ledger, what rides, the claim Dn of
the first statement, and what the stages claim, each at the statement that it has found, without the
claim on the coefficient (Ch.Owed of LayVO.toOwn0). This file gives that for the chain of
Cb/Pv/Lay/At/OwnW.lean, from Cb/Pv/Lay/End/LayAll.lean.

Main definitions: chF (the chain with its token point), OkMore (what is asked beside the ledger,
St1Ok and the coefficient: the pending row, and the letter Ok').
Main theorems.
 - lay_owed: at a run with epsOK: Dn, and Ch.Owed of the chain.
 - owed0: what the chain owes gives what the chain without the claim on the coefficient owes
   (LayVO.toOwn0).
 - lay_hEnd_at: with what rides: at every run with epsOK that meets A0.on and B0's relation: from
   the pull-back of the whole ledger: A0's relation, Dn, and Ch.Owed of LayVO.toOwn0.
 - layB0, layB0_on, lay_hEnd_b0: the same at a written joint B0: what rides, at the first statement
   inside the last one, and the pending row at the last statement. There hA0 and hM are projections.

Limits. NormsOk, TermsOk and GatedOk are premises. In lay_hEnd_at three premises range over the runs
with epsOK that meet A0.on and B0's relation: hA0 (what rides is handed on); hDn (the claim of the
first statement, from the whole ledger); hM (the pending row). The pending row reads the run's last
message. Of two runs from one first statement that differ in that message alone, at most one meets
it (by reading; no theorem here says so). So hM asks that B0's relation holds at no more than one of
them: B0 has to read the run's last statement. layB0 does: it is what rides and this sub-proof's
pending row at the run's last statement. At layB0 hM and hA0 are projections; the pending row is
then owed by whoever gives layB0 back from the tail's end: nobody does yet. Of the three conclusions
of lay_hEnd_at one is derived (Ch.Owed): A0's relation is hA0 and Dn is hDn. No run is shown at
which the ledger's pull-back and the pending row hold: the toy of Cb/Pv/Lay/End/TestLayBill.lean
[not in this library] is at a statement that is no run's. Of the eleven parts of the ledger three
are letters. The part on the batched sumcheck is the three owed claims themselves, written on the
early entries. The programs' two claims on the form parts read late tables; that their pull-back is
these claims is shown nowhere. The forms of the late entries are the link's: that the late entries
agree with them (Agree, Cb/Sub/Late.lean) is owed by whoever lays the tail. The parts are read off
each output's own state; that it is the state of the sumcheck's claim is shown at runs for the first
two sumchecks alone (Cb/Pv/Lay/End/Runs.lean).


-/
import Cb.Pv.Att.ChainLast
import Cb.Pv.Lay.End.LayAll
import Cb.Pv.Lay.OwnTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Iop TWhole Cb IOR Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- The chain of the own rounds, with its token point. -/
noncomputable abbrev chF : Ch E M X := (P.layVO P.wPart).toOwn.ch

/-- What is asked of a last statement and the messages beside the ledger, St1Ok and the
coefficient. -/
def OkMore (Ok' : (tailF P).s7.Nx → M → Prop) (e : (tailF P).s7.Nx) (m : M) : Prop :=
  Pending P.wp0
      (rowW (fun c : Fin P.wp0.n => e.2.st.2 ^ (c : ℕ)) (fun c => P.wp0.ten c e.2.st.1)
        ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2))
      ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2)
      ((noKept P.wp0.wt.L.Sm).outB P.wp0.wt.L.Mk e.2) (e.2.vals ()) (P.msg m) ∧ Ok' e m

/-- At a run at which the coefficient is not 0: the claim of the first statement, and what the
stages owe. -/
theorem lay_owed {fm : (tailF P).s7.Nx → Nm → Aff E P.J} {zt : (tailF P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Dn : X → M → Prop)
    (Ok' : (tailF P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkAt P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) →
      Dn ((tailF P).xL e).1 m)
    (x : X) (ts : (chF P).Trs) (m : M) (ht : (P.layVO P.wPart).epsOK ((chF P).run x ts))
    (hM : OkMore P Ok' ((chF P).run x ts) m)
    (h : Ledger.Holds (pullL (lateA Y (fm ((chF P).run x ts)))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).run x ts)).all)
      (P.msg m)) :
    Dn x m ∧ (chF P).Owed x ts m := by
  refine (Ch.last_run (chF P) Dn x ts m).1 ?_
  have hr : St1Ok P.toOwnPar P.wPart ((chF P).run x ts) :=
    hst_run P.toOwnPar P.wPart (x, ts.1) ts.2
  exact lay_last_all P N Tm G R (fun b m => Dn b.1 m) Ok' dn ((chF P).run x ts) m ⟨hr, ht, hM⟩ h

omit [Fintype J₂] [DecidableEq J₂] in
/-- What the chain owes gives what the chain without the claim on the coefficient owes. -/
theorem owed0 (x : X) (ts : (chF P).Trs) (m : M) (h : (chF P).Owed x ts m) :
    (P.layVO P.wPart).toOwn0.ch.Owed x ts m := by
  have h1 : (chF P).Last (fun _ _ => True) ((chF P).run x ts) m :=
    (Ch.last_run (chF P) _ x ts m).2 ⟨trivial, h⟩
  have h2 : (P.layVO P.wPart).toOwn0.ch.Last (fun _ _ => True)
      ((P.layVO P.wPart).toOwn0.ch.run x ts) m :=
    LayTail.last_withOw3 ((P.layVO P.wPart).V.toTail.withOw3 fun b m =>
        ∀ a, (P.layVO P.wPart).V.Tm.toSum.T.par.EHolds b.2 ((P.layVO P.wPart).V.rd3 m) a)
      (P.layVO P.wPart).V.toTail.ow3 (fun _ _ => True) ((chF P).run x ts) m (fun g => g.2) h1
  exact ((Ch.last_run (P.layVO P.wPart).toOwn0.ch _ x ts m).1 h2).2

/-- With what rides: at the runs at which the coefficient is not 0. -/
theorem lay_hEnd_at {fm : (tailF P).s7.Nx → Nm → Aff E P.J} {zt : (tailF P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Dn : X → M → Prop)
    {Kc X0 Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (B0 : Rels Kc (chF P).End Ex (M × Wp))
    (hA0 : ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chF P).run x ts, y) w → A0.relR (pr x, y) w)
    (hDn : ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chF P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chF P).run x ts)))
        (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).run x ts)).all)
        (P.msg w.1) → Dn x w.1)
    (hM : ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chF P).run x ts, y) w → OkMore P (fun _ _ => True) ((chF P).run x ts) w.1) :
    ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      B0.relR ((chF P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chF P).run x ts)))
        (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).run x ts)).all)
        (P.msg w.1) →
      A0.relR (pr x, y) w ∧ Dn x w.1 ∧ (P.layVO P.wPart).toOwn0.ch.Owed x ts w.1 :=
  fun x ts y w ht ho hf hL =>
    ⟨hA0 x ts y w ht ho hf, hDn x ts y w ht ho hf hL,
      owed0 P x ts w.1 (lay_owed P N Tm G R (fun _ _ => True) (fun _ _ => True)
        (fun _ _ _ _ _ _ => trivial) x ts w.1 ht (hM x ts y w ht ho hf) hL).2⟩

/-- A joint behind the chain: what rides, at the first statement inside the last one, and the
pending row at the last statement. -/
noncomputable def layB0 {Kc X0 Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp))
    (pr : X → X0) : Rels Kc (chF P).End Ex (M × Wp) :=
  jt A0 (fun e => pr ((chF P).back e)) fun e m => OkMore P (fun _ _ => True) e m

omit [Fintype J₂] [DecidableEq J₂] in
/-- At a run, A0's condition at the first statement gives layB0's at the last. -/
theorem layB0_on {Kc X0 Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (x : X) (ts : (chF P).Trs) (y : Ex.Str) (h : A0.on (pr x, y)) :
    (layB0 P A0 pr).on ((chF P).run x ts, y) := by
  show A0.on (pr ((chF P).back ((chF P).run x ts)), y)
  rw [Ch.back_run]
  exact h

/-- lay_hEnd_at at the joint layB0: hA0 and hM are projections. -/
theorem lay_hEnd_b0 {fm : (tailF P).s7.Nx → Nm → Aff E P.J} {zt : (tailF P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Dn : X → M → Prop)
    {Kc X0 Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (hDn : ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      (layB0 P A0 pr).relR ((chF P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chF P).run x ts)))
        (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).run x ts)).all)
        (P.msg w.1) → Dn x w.1) :
    ∀ x ts y w, (P.layVO P.wPart).epsOK ((chF P).run x ts) → A0.on (pr x, y) →
      (layB0 P A0 pr).relR ((chF P).run x ts, y) w →
      Ledger.Holds (pullL (lateA Y (fm ((chF P).run x ts)))
        (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).run x ts)).all)
        (P.msg w.1) →
      A0.relR (pr x, y) w ∧ Dn x w.1 ∧ (P.layVO P.wPart).toOwn0.ch.Owed x ts w.1 :=
  lay_hEnd_at P N Tm G R Dn A0 pr (layB0 P A0 pr)
    (fun x ts y w _ _ hf => by
      have h : A0.relR (pr ((chF P).back ((chF P).run x ts)), y) w := hf.1
      rw [Ch.back_run] at h
      exact h)
    hDn fun _ _ _ _ _ _ hf => hf.2

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.lay_hEnd_b0
#print axioms Cb.Pv.Lay.End.lay_owed
#print axioms Cb.Pv.Lay.End.owed0
#print axioms Cb.Pv.Lay.End.lay_hEnd_at
