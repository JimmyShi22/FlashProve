-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CarriageLedger.lean: THE FIELD `last` OF THE CARRIAGE
(Johnson/Road/K4/Carriage.lean, CarriageHeard.lean), CUT INTO THREE BY THE LIBRARY's OWN THEOREM ON
THE CHAIN's END (of `last` itself only the condition `St1Ok` is paid here): what the chain of the
own rounds claims at its end follows from the pull-back of the ledger of the verifier's claims
(`lay_owed`, Cb/Pv/Lay/End/LayHEndAt.lean, over `lay_last_all`). Two general theorems, a record of
premises and two theorems at the value. Bookkeeping: no count is made here.

  `last_at_run`: the same as the next, at any statement that is a run's last.
  `last_of_ledger`: at every `FullPar`, statement and transcript of the chain, under the three
    records `NormsOk`, `TermsOk`, `GatedOk`: at what the chain's verifier puts out (`Ch.val`): if
    the coefficient drawn in the sumcheck of the terms is not 0, the pending row on the committed
    weights holds, and the pull-back of the whole ledger holds of the messages, then `Ch.Last` (with
    True for the claim of the first statement) holds there. That the output is a run's last
    statement is `Ch.val_cut` (Cb/Pv/Att/Ran.lean); so the condition `St1Ok` is paid
    (`hst_run`, inside `lay_owed`).
  `Plan4.HeardL`: the premises of `Plan4.Heard` with `last` cut in three, each at every yes:
    `coin`, `pending`, `ledger`.
  `Plan4.heard_of_ledger`, `Plan4.leads_ledger`: `Plan4.Heard`, and the plain law of the piece that
    holds K4's own block and puts no round behind its own, from `Plan4.HeardL` and the three records
    `NormsOk`, `TermsOk`, `GatedOk`; for the law also: the maps are as asked and the piece's errors
    bear the carried ones.

The three parts of the ledger that are letters in the library's theorem (look, planes, emb) stay a
letter R here: whoever calls may hand in empty lists (`noRest`, Cb/Pv/Lay/End/LayAllMeet.lean),
since the claim Dn of the first statement is taken as True.

Limits. `Plan4.HeardL`, `NormsOk`, `TermsOk` AND `GatedOk` ARE PREMISES: NOTHING HERE SHOWS THAT
THEY CAN BE MET TOGETHER AT A PLAN. Those of LayAll.lean and LayHEndAt.lean, among them: the
ledger's part on the batched sumcheck is the three owed claims themselves, written on the early
entries; that the programs' two claims on the form parts pull back to these is shown nowhere. Those
of Carriage.lean and CarriageHeard.lean.
-/
import Johnson.Road.K4.CarriageHeard
import Cb.Pv.Lay.End.LayHEndAt
import Cb.Pv.Att.Ran

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop TWhole Cb IOR Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par Seat block)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece below)
open VerifiableInference.Desc.Plain.K04 (HearsAs)
open Inst.Model (Scl)

section General
variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- At a statement that is a run's last. -/
theorem last_at_run {fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J} {zt : (tailF P).s7.Nx → ℕ → E}
    {b s B sG : ℕ} (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (e : (chF P).End)
    (x : X) (ts : (chF P).Trs) (he : e = (chF P).run x ts) (m : M)
    (ht : (P.layVO P.wPart).epsOK e) (hM : OkMore P (fun _ _ => True) e m)
    (h : Ledger.Holds (pullL (lateA Y (fm e))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B e).all) (P.msg m)) :
    (chF P).Last (fun _ _ => True) e m := by
  subst he
  exact (Ch.last_run (chF P) _ x ts m).2 (lay_owed P N Tm G R (fun _ _ => True) (fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial) x ts m ht hM h)

/-- **What the chain claims at its end, at what its verifier puts out, from the ledger.** -/
theorem last_of_ledger {fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J}
    {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}
    (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG) (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Ex : ExtSpec)
    (a : X × Ex.Str) (τ : Tr ((chF P).R Ex).shape) (m : M)
    (ht : (P.layVO P.wPart).epsOK ((chF P).val Ex a τ).1)
    (hM : OkMore P (fun _ _ => True) ((chF P).val Ex a τ).1 m)
    (h : Ledger.Holds (pullL (lateA Y (fm ((chF P).val Ex a τ).1))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B ((chF P).val Ex a τ).1).all)
      (P.msg m)) :
    (chF P).Last (fun _ _ => True) ((chF P).val Ex a τ).1 m :=
  last_at_run P N Tm G R _ a.1 ((chF P).cut Ex τ)
    (congrArg Prod.fst (Ch.val_cut Ex (chF P) a.1 a.2 τ)) m ht hM h

end General

section AtTheValue
variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame}
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- The premises of `Plan4.Heard`, with `last` cut in three. -/
structure Plan4.HeardL (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) (par : Par)
    (pc : Piece (ckP .two) Fr T Cl Wt) (Mp : Maps pc.ds ((chF Q.full).R Ex).shape)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop)
    (Y : LateLay Nm J₂) (ιN : NormsNm → Nm) (ιT : TermsNm → Nm) (ιG : GatedNm → Nm)
    (fm : (tailF Q.full).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.full.J)
    (zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E) (b B sG : ℕ)
    (R : (tailF Q.full).s7.Nx → Rest3 Cb.Gl.E (Q.full.J ⊕ J₂)) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- the coefficient drawn in the sumcheck of the terms, as the chain reads it, is not 0 -/
  coin : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G →
    (Q.full.layVO Q.full.wPart).epsOK ((chF Q.full).val Ex (fa a) (Mp.view τ)).1
  /-- what the row opens gives the pending row on the committed weights -/
  pending : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    OkMore Q.full (fun _ _ => True) ((chF Q.full).val Ex (fa a) (Mp.view τ)).1 (part w)
  /-- what the row opens gives the pull-back of the library's ledger of claims -/
  ledger : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (pullL (lateA Y (fm ((chF Q.full).val Ex (fa a) (Mp.view τ)).1))
      (clAt Q.full.toOwnPar Q.full.wPart Y ιN (restAt Q.full Y ιT ιG R sG) zt b B
        ((chF Q.full).val Ex (fa a) (Mp.view τ)).1).all) (Q.full.msg (part w))
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.full.own.pT (fa a).1 (part w) → Front a w

variable {Y : LateLay Nm J₂} {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}

/-- **`Plan4.Heard` from the ledger.** -/
theorem Plan4.heard_of_ledger (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt} {Mp : Maps pc.ds ((chF Q.full).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {fm : (tailF Q.full).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.full.J}
    {zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E} {b s B sG : ℕ}
    {R : (tailF Q.full).s7.Nx → Rest3 Cb.Gl.E (Q.full.J ⊕ J₂)}
    (N : NormsOk Q.full.toOwnPar Q.full.wPart Y ιN fm zt b s B) (Tm : TermsOk Q.full Y ιT fm)
    (G : GatedOk Q.full Y ιG fm sG)
    (H : Q.HeardL L Ex par pc Mp fa part on on' Front Behind Y ιN ιT ιG fm zt b B sG R) :
    Q.Heard L Ex par pc Mp fa part on on' Front Behind where
  kept := H.kept
  last := fun a τ fo o G' w ha hy hB =>
    last_of_ledger Q.full N Tm G R Ex (fa a) (Mp.view τ) (part w) (H.coin a τ fo o G' ha hy)
      (H.pending a τ fo o G' w ha hy hB) (H.ledger a τ fo o G' w ha hy hB)
  first := H.first

/-- **The plain law of the piece that holds K4's own block, from the ledger**, the messages m
outside the game. -/
theorem Plan4.leads_ledger (Q : Plan4 Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt} {Mp : Maps pc.ds ((chF Q.full).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {fm : (tailF Q.full).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.full.J}
    {zt : (tailF Q.full).s7.Nx → ℕ → Cb.Gl.E} {b s B sG : ℕ}
    {R : (tailF Q.full).s7.Nx → Rest3 Cb.Gl.E (Q.full.J ⊕ J₂)}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk) (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ((chF Q.full).eps Ex)) pc.err)
    (N : NormsOk Q.full.toOwnPar Q.full.wPart Y ιN fm zt b s B) (Tm : TermsOk Q.full Y ιT fm)
    (G : GatedOk Q.full Y ιG fm sG)
    (H : Q.HeardL L Ex par pc Mp fa part on on' Front Behind Y ιN ιT ιG fm zt b B sG R) (m : Mm) :
    pc.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, part w = m → Behind b w → Front a w) pc.err :=
  Q.leads_heard L Ex hk hb hback hOK herr (Q.heard_of_ledger L Ex N Tm G H) m

end AtTheValue
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.last_of_ledger
#print axioms OnBytes.Road.K4.Plan4.heard_of_ledger
#print axioms OnBytes.Road.K4.Plan4.leads_ledger
