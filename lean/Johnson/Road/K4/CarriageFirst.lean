-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CarriageFirst.lean: THE CARRIAGE OF Johnson/Road/K4/Carriage.lean,
CarriageHeard.lean AND CarriageLedger.lean FOR THE FIRST LAYERS' SUB-PROOF (g = 0), whose own rounds
are another chain: two further points behind the token point, and one scalar more in the weights'
round (Cb/Pv/Lay/At/OwnFirstW.lean). A record of letters with its value, two further definitions
(`chFF`, `PendF`), two records of premises and five theorems. Bookkeeping: no count is made here.

  `Plan4F E M X`: the letters of Johnson/Road/K4/Value.lean and the first group's seven: ls, nb, gB
    with their two conditions, the request's tokens off the first statement, and the slot sE of the
    scalar that is sent in the weights' round. `Plan4F.fullF : FullFPar E M X`: the value.
  `Plan4F.pickIs`: the batched sumcheck's pick is the library's lawful one.
  `Plan4F.Heard`: three premises, each at every `Yes` of K4's block: `kept`, `last`, `first`.
  `Plan4F.leads_heard`: the plain law of the piece that holds `below bk` (bk hears as K4's own block
  at the seat L), for each m.
  `lastF_at_run`, `lastF_of_ledger`: what the first chain claims at its end, at what its verifier
    puts out, from the pull-back of the library's ledger `clFirst` (`lay_last_first`,
    Cb/Pv/Lay/End/LayFirst.lean), that the coefficient drawn in the sumcheck of the terms is not 0,
    and the pending row. `St1OkF` is paid (`Ch.val_cut`, `hst_run_first`).
  `Plan4F.HeardL`: `Plan4F.Heard` with `last` cut in three: `coin`, `pending`, `ledger`.
  `Plan4F.leads_ledger`: the plain law from `Plan4F.HeardL` and the library's four records.

Limits. `Plan4F.Heard`, `Plan4F.HeardL`, `NormsOkF`, `TermsOkF`, `GatedOkF` AND `EmbOkF` ARE
PREMISES: NOTHING HERE SHOWS THAT THEY CAN BE MET. No premise says g = 0, and the maps' type does
not bar another group: what cannot be paid there are the fields `ledger` and `first`. Those of the
three files named above, of OwnFirstW.lean and of LayFirst.lean.
-/
import Johnson.Road.K4.CarriageHeard
import Cb.Pv.Lay.At.OwnFirstW
import Cb.Pv.Lay.End.LayFirst
import Cb.Pv.Att.Ran
import Cb.Pv.Att.ChainLast

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

noncomputable section

/-- The letters of the first group. -/
structure Plan4F (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends Plan4 E M X where
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  hd : D.d = nb * 2 ^ ls
  /-- the request's tokens -/
  tok : X → ℕ → ℕ
  /-- the slot of the scalar that is sent in the weights' round -/
  sE : ℕ

/-- The value. -/
def Plan4F.fullF {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4F E M X) :
    FullFPar E M X where
  toFullPar := Q.toPlan4.full
  ls := Q.ls
  nb := Q.nb
  gB := Q.gB
  hnb := Q.hnb
  hd := Q.hd
  tok := Q.tok
  mkE := Q.toPlan4.sl Q.sE

/-- The first chain of the own rounds, with its three points. -/
abbrev chFF {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X) :
    Ch E M X := P.ownF.toOwn.ch

section General
variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm} {ιE : EmbNm → Nm}

/-- The pending row on the committed weights, off a last statement. -/
def PendF (e : (tailW P).s7.Nx) (m : M) : Prop :=
  Pending P.wp0 (rowWF P.wp0 (tenEF P) e.2.st.1.1 e.2.st.2
      ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2))
    ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2) ((noKept P.wf.L.Sm).outB P.wf.L.Mk e.2)
    (e.2.vals ()) (P.msg m)

/-- At a statement that is a run's last. -/
theorem lastF_at_run {fm : (tailW P).s7.Nx → Nm → TWhole.Aff E P.J}
    {zt : (tailW P).s7.Nx → ℕ → E} {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B)
    (Tm : TermsOkF P Y ιT fm) (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (e : (chFF P).End) (x : X)
    (ts : (chFF P).Trs) (he : e = (chFF P).run x ts) (m : M)
    (ht : ((tailW P).b3 e).2.eps ≠ 0) (hM : PendF P e m)
    (h : Ledger.Holds (pullL (lateA Y (fm e)) (clFirst P Y ιN ιT ιG ιE R zt b B sG e).all)
      (P.msg m)) :
    (chFF P).Last (fun _ _ => True) e m := by
  subst he
  have hr : St1OkF P ((chFF P).run x ts) :=
    hst_run_first P.ofp P.wfPart (((x, ts.1), ts.2.1), ts.2.2.1) ts.2.2.2
  exact lay_last_first P N Tm G Em R (fun _ _ => True) (fun _ _ => True)
    (fun _ _ _ _ _ _ => trivial) ((chFF P).run x ts) m ⟨hr, ht, hM, trivial⟩ h

/-- **What the first chain claims at its end, at what its verifier puts out, from the ledger.** -/
theorem lastF_of_ledger {fm : (tailW P).s7.Nx → Nm → TWhole.Aff E P.J}
    {zt : (tailW P).s7.Nx → ℕ → E} {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B)
    (Tm : TermsOkF P Y ιT fm) (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (Ex : ExtSpec) (a : X × Ex.Str)
    (τ : Tr ((chFF P).R Ex).shape) (m : M)
    (ht : ((tailW P).b3 ((chFF P).val Ex a τ).1).2.eps ≠ 0)
    (hM : PendF P ((chFF P).val Ex a τ).1 m)
    (h : Ledger.Holds (pullL (lateA Y (fm ((chFF P).val Ex a τ).1))
      (clFirst P Y ιN ιT ιG ιE R zt b B sG ((chFF P).val Ex a τ).1).all) (P.msg m)) :
    (chFF P).Last (fun _ _ => True) ((chFF P).val Ex a τ).1 m :=
  lastF_at_run P N Tm G Em R _ a.1 ((chFF P).cut Ex τ)
    (congrArg Prod.fst (Ch.val_cut Ex (chFF P) a.1 a.2 τ)) m ht hM h

end General

section AtTheValue
variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Nm J₂ : Type} [Fintype J₂]
  [DecidableEq J₂]

/-- At the value the batched sumcheck's pick is the library's lawful one. -/
theorem Plan4F.pickIs (Q : Plan4F Cb.Gl.E Mm X) : Q.fullF.ownF.PickIs := rfl

/-- The premises, said of what K4's hearing returns. -/
structure Plan4F.Heard (Q : Plan4F Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) (par : Par)
    (pc : Piece (ckP .two) Fr T Cl Wt) (Mp : Maps pc.ds ((chFF Q.fullF).R Ex).shape)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- what the row opens gives the chain's last claim, at the chain's own output on the
  transcript's image -/
  last : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    (chFF Q.fullF).Last (fun _ _ => True) ((chFF Q.fullF).val Ex (fa a) (Mp.view τ)).1 (part w)
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.fullF.ownF.pT (fa a).1 (part w) → Front a w

/-- **The plain law of the piece that holds K4's own block, in the first group**, the messages m
outside the game. -/
theorem Plan4F.leads_heard (Q : Plan4F Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt}
    {Mp : Maps pc.ds ((chFF Q.fullF).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk)
    (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ((chFF Q.fullF).eps Ex)) pc.err)
    (H : Q.Heard L Ex par pc Mp fa part on on' Front Behind) (m : Mm) :
    pc.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, part w = m → Behind b w → Front a w) pc.err :=
  leads_of_ties (rest := fun _ => ())
    (Q.fullF.ownF_knowAt Ex (noJoint Ex Mm) (fun _ => ()) (fun _ _ => True))
    (Q.fullF.ownF.tot Q.pickIs Ex) hOK herr
    { front_on := fun _ _ => trivial
      work := fun a τ b _ h => Mp.pass_of_passT τ (yes_of_out L hk hb hback a b τ h).1
      kept := fun a τ b ha h => by
        obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
        exact H.kept a τ fo o G ha hy
      last := fun a τ b w ha h hB => by
        obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
        exact ⟨trivial, H.last a τ fo o G w ha hy hB⟩
      first := fun a τ b w ha h hB hp => by
        obtain ⟨_, fo, o, G, hy, rfl⟩ := yes_of_out L hk hb hback a b τ h
        exact H.first a τ fo o G w ha hy hB hp.2.2 } m

/-- The premises of `Plan4F.Heard`, with `last` cut in three. -/
structure Plan4F.HeardL (Q : Plan4F Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) (par : Par)
    (pc : Piece (ckP .two) Fr T Cl Wt) (Mp : Maps pc.ds ((chFF Q.fullF).R Ex).shape)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (on on' : T × Fr.E.Str → Prop)
    (Front Behind : T × Fr.E.Str → Wt → Prop)
    (Y : LateLay Nm J₂) (ιN : NormsNm → Nm) (ιT : TermsNm → Nm) (ιG : GatedNm → Nm)
    (ιE : EmbNm → Nm) (fm : (tailW Q.fullF).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.fullF.J)
    (zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E) (b B sG : ℕ)
    (R : (tailW Q.fullF).s7.Nx → Rest2 Cb.Gl.E (Q.fullF.J ⊕ J₂)) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G → on' (behindOf L pc a τ o G)
  /-- the coefficient drawn in the sumcheck of the terms, as the chain reads it, is not 0 -/
  coin : ∀ a τ fo o G, on a → Yes L par pc a τ fo o G →
    ((tailW Q.fullF).b3 ((chFF Q.fullF).val Ex (fa a) (Mp.view τ)).1).2.eps ≠ 0
  /-- what the row opens gives the pending row on the committed weights -/
  pending : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    PendF Q.fullF ((chFF Q.fullF).val Ex (fa a) (Mp.view τ)).1 (part w)
  /-- what the row opens gives the pull-back of the library's ledger of claims -/
  ledger : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G →
    Behind (behindOf L pc a τ o G) w →
    Ledger.Holds (pullL (lateA Y (fm ((chFF Q.fullF).val Ex (fa a) (Mp.view τ)).1))
      (clFirst Q.fullF Y ιN ιT ιG ιE R zt b B sG
        ((chFF Q.fullF).val Ex (fa a) (Mp.view τ)).1).all) (Q.fullF.msg (part w))
  /-- with what the row opens, what is claimed before the chain's first round gives what the row
  closes -/
  first : ∀ a τ fo o G w, on a → Yes L par pc a τ fo o G → Behind (behindOf L pc a τ o G) w →
    Q.fullF.ownF.pT (fa a).1 (part w) → Front a w

variable {Y : LateLay Nm J₂} {ιN : NormsNm → Nm} {ιT : TermsNm → Nm} {ιG : GatedNm → Nm}
  {ιE : EmbNm → Nm}

/-- **The plain law in the first group, from the ledger**, the messages m outside the game. -/
theorem Plan4F.leads_ledger (Q : Plan4F Cb.Gl.E Mm X) (L : Seat T) (Ex : ExtSpec) {par : Par}
    {pc : Piece (ckP .two) Fr T Cl Wt}
    {Mp : Maps pc.ds ((chFF Q.fullF).R Ex).shape}
    {fa : T × Fr.E.Str → X × Ex.Str} {part : Wt → Mm} {on on' : T × Fr.E.Str → Prop}
    {Front Behind : T × Fr.E.Str → Wt → Prop}
    {fm : (tailW Q.fullF).s7.Nx → Nm → TWhole.Aff Cb.Gl.E Q.fullF.J}
    {zt : (tailW Q.fullF).s7.Nx → ℕ → Cb.Gl.E} {b s B sG : ℕ}
    {R : (tailW Q.fullF).s7.Nx → Rest2 Cb.Gl.E (Q.fullF.J ⊕ J₂)}
    {bk : VerifiableInference.Desc.Block T Cl}
    (hk : HearsAs L par bk)
    (hb : pc.b = below bk) (hback : pc.back = []) (hOK : Mp.OK)
    (herr : Err.le (Mp.err ((chFF Q.fullF).eps Ex)) pc.err)
    (N : NormsOkF Q.fullF Y ιN fm zt b s B) (Tm : TermsOkF Q.fullF Y ιT fm)
    (G : GatedOkF Q.fullF Y ιG fm sG) (Em : EmbOkF Q.fullF Y ιE fm)
    (H : Q.HeardL L Ex par pc Mp fa part on on' Front Behind Y ιN ιT ιG ιE fm zt b B sG R)
    (m : Mm) :
    pc.ior.red.Leads on
      (fun a b => on' b ∧ ∀ w, part w = m → Behind b w → Front a w) pc.err :=
  Q.leads_heard L Ex hk hb hback hOK herr
    { kept := H.kept
      last := fun a τ fo o G' w ha hy hB =>
        lastF_of_ledger Q.fullF N Tm G Em R Ex (fa a) (Mp.view τ) (part w)
          (H.coin a τ fo o G' ha hy) (H.pending a τ fo o G' w ha hy hB)
          (H.ledger a τ fo o G' w ha hy hB)
      first := H.first } m

end AtTheValue
end
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.lastF_of_ledger
#print axioms OnBytes.Road.K4.Plan4F.leads_heard
#print axioms OnBytes.Road.K4.Plan4F.leads_ledger
