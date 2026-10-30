-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayFirst.lean: what the chain of the FIRST layers' sub-proof's own rounds claims at
its end, at the chain's value, from the pull-back of the ledger clFirst, written down here: the
norms' and the gated products' shares proved; the terms' but for the coefficient; the weights' from
the claim on the stream that comes in, the merge's row and the pending row; one share a premise.

Cb/Pv/Lay/End/LayAll.lean says this of a layers' sub-proof that is not the first. The first
sub-proof has a chain of its own (Cb/Pv/Lay/At/OwnFirstW.lean: P.ofp.layVF P.wfPart, P.ownF). Here
the frame of Cb/Pv/Lay/End/LayEnd.lean is filled at that chain: the norms' share
(Cb/Pv/Lay/End/NormsFirst.lean), that of the terms and the batched sumcheck
(Cb/Pv/Lay/End/TermsFirst.lean), the gated products' and the weights'
(Cb/Pv/Lay/End/FirstShare.lean). In the first sub-proof the part emb holds the claim on the stream
that comes in.

Main definitions.
 - Rest2: the two parts of the ledger that stay letters: look, planes.
 - clFirst: the ledger, part by part, off a last statement.
 - St1OkF: the state that the first sumcheck's output carries holds the element drawn before it.
 - NormsOkF, TermsOkF, GatedOkF, EmbOkF: what the shares ask of sizes, names and forms.
 - OkFirst: what is asked of a last statement and the messages beside the ledger: St1OkF; the
   coefficient drawn in the sumcheck of the terms is not 0; the pending row on the committed
   weights; a letter Ok' for the share that is a premise.
Main theorems: lay_shares_first (the record Shares); lay_last_first (Ch.Last of the chain behind the
three points).

Limits. The share dn (from the parts look, hot, planes) is a premise, closed over every last
statement. Of the eighteen clauses of the chain's bill six are True at this chain: c1, c3, c4, c5,
c6, c7. The pending row leaves the sub-proof: it is asked, not paid; so is that the drawn
coefficient is not 0. The merge's row and the pending row are read off the output's own state; that
it is the claim's state is shown for the first sumcheck alone.
NormsOkF, TermsOkF, GatedOkF and EmbOkF are premises. They bind one family of forms fm through four
maps, at the names in range: they can hold together only if no two names in range whose forms
differ, of one map or of two, go to one member of Nm. No field says so; in
Cb/Pv/Lay/End/TestLayFirst.lean [not in this library] Nm is the disjoint sum of the four types of
names. The forms fm are the link's: that the late entries agree with them (Agree, Cb/Sub/Late.lean)
is owed by whoever lays the tail.
That the ledger is a program's is not said here. The part stack is the three owed claims written on
the early entries; the programs' claims on the two form parts read late tables, and that their
pull-back gives these is shown nowhere. look and planes are letters. zt is a letter, meant for the
tail of the lookup's point; no statement here ties it to that point.


-/
import Cb.Pv.Lay.End.FirstShare
import Cb.Pv.Lay.End.LayEnd
import Cb.Pv.Lay.End.TermsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (Arr lDd lF lFe)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ιN : NormsNm → Nm) (ιT : TermsNm → Nm) (ιG : GatedNm → Nm) (ιE : EmbNm → Nm)

/-- The two parts of the ledger that stay letters. -/
structure Rest2 (E J : Type) where
  look : Ledger E J
  planes : Ledger E J

/-- The ledger, part by part, off a last statement. zt: a letter, meant for the tail of the lookup's
point. -/
noncomputable def clFirst (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂))
    (zt : (tailW P).s7.Nx → ℕ → E) (b B sG : ℕ) (e : (tailW P).s7.Nx) : LayCl E (P.J ⊕ J₂) where
  look := (R e).look
  sq := sqAtF P.ofp P.wfPart Y ιN e (zt e) b B
  bat := batAtF P.ofp P.wfPart Y ιN e (zt e)
  led := rowsAtF P.ofp P.wfPart Y ιN e (zt e)
  terms := termsLed P.tp (readsT Y ιT) ((tailW P).b3 e).2
  gated := gatedLedOf P.fp Y ιG ((tailW P).b5 e).2 ((tailW P).b6 e).2 sG
  hot := hotAt P.toOwnPar Y ιN
  planes := (R e).planes
  emb := embLedOf Y ιE (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB (stF P e).pb
  stack := stackLed P.ip ((tailW P).b4 e).2
  merge := mergeLedF P.wp0 (tenEF P) (rhsF P) P.mkE e.2

/-- The state that the first sumcheck's output carries holds the element that was drawn before that
sumcheck. It is so at the last statement of a run (hst_run_first). -/
def St1OkF (e : (tailW P).s7.Nx) : Prop :=
  ((tailW P).b1 e).2.st.1.2 = ((tailW P).b1 e).1.1.1.2

/-- What the norms' share asks of sizes, names and forms. -/
structure NormsOkF (fm : (tailW P).s7.Nx → Nm → Aff E P.J) (zt : (tailW P).s7.Nx → ℕ → E)
    (b s B : ℕ) : Prop where
  hl : lDd P.D = b + s
  hd : P.D.d = B * 2 ^ s
  hB : B ≤ 2 ^ b
  hfm : ∀ e x, InRange P.D.nNu B P.D.ne P.D.nx x → fm e (ιN x) =
    toAff (normsFm P.rd P.D (eAtF P.ofp P.wfPart e (zt e)) (P.D.lL + 1) b s x)
  gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ιN (.xi ν l kh))
  gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιN (.atP ν n))
  gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιN (.atR ν n))
  gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ιN (.sel l x))

/-- What the share of the terms asks of names and forms. -/
structure TermsOkF (fm : (tailW P).s7.Nx → Nm → Aff E P.J) : Prop where
  hfm : ∀ e (x : TermsNm), x.InR P.D → fm e (ιT x) =
    toAff (termsFm P.rd P.D (termsEAt P.tp ((tailW P).b3 e).2).rt x)
  gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιT (.row ν n))
  gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ιT (.sc l k))
  gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ιT (.sel l x k))

/-- What the gated products' share asks of sizes, names and forms. -/
structure GatedOkF (fm : (tailW P).s7.Nx → Nm → Aff E P.J) (sG : ℕ) : Prop where
  h1 : 1 ≤ P.D.lL
  hs1 : sG ≤ lF P.D
  hs2 : sG ≤ lFe P.D
  hfe : P.D.fe = 2 ^ lFe P.D
  hfm : ∀ e (x : GatedNm), x.InR P.D sG → fm e (ιG x) = toAff (gatedFm P.rd P.D
    (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) sG x)
  hY : GoodNm Y ιG P.D sG

/-- What the claim on the stream that comes in asks of names and forms. -/
structure EmbOkF (fm : (tailW P).s7.Nx → Nm → Aff E P.J) : Prop where
  hfm : ∀ e x, EmbIn P.nb x → fm e (ιE x) = toAff (embFm P.rd P.D (stF P e).pa P.ls x)
  hY : ∀ l, l < Arr.x0.nCell → ∀ kh, kh < P.nb → Y.good (ιE (.x0 l kh))

/-- What is asked of a last statement and the messages beside the ledger. -/
def OkFirst (Ok' : (tailW P).s7.Nx → M → Prop) (e : (tailW P).s7.Nx) (m : M) : Prop :=
  St1OkF P e ∧ ((tailW P).b3 e).2.eps ≠ 0 ∧
    Pending P.wp0 (rowWF P.wp0 (tenEF P) e.2.st.1.1 e.2.st.2
        ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2))
      ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2) ((noKept P.wf.L.Sm).outB P.wf.L.Mk e.2)
      (e.2.vals ()) (P.msg m) ∧ Ok' e m

variable {Y ιN ιT ιG ιE}

/-- The record Shares at the first chain's value; dn is a premise. -/
theorem lay_shares_first {fm : (tailW P).s7.Nx → Nm → Aff E P.J}
    {zt : (tailW P).s7.Nx → ℕ → E} {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B)
    (Tm : TermsOkF P Y ιT fm) (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (Dn : P.ofp.fs.X3 → M → Prop)
    (Ok' : (tailW P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkFirst P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) → Dn ((tailW P).xL e) m) :
    Shares (tailW P) Dn P.msg (fun e => lateA Y (fm e)) (clFirst P Y ιN ιT ιG ιE R zt b B sG)
      (OkFirst P Ok') where
  dn := dn
  norms := fun e m hOk h1 h2 h3 h4 =>
    norms_share_first P.ofp P.wfPart Y ιN (fm e) e (zt e) m b s B N.hl N.hd N.hB hOk.1 (N.hfm e)
      N.gXi N.gP N.gR N.gS h1 h2 h3 h4
  terms := fun e m hOk h3 h4 =>
    terms_bill_first P.ofp P.wfPart Y ιT (fm e) e m hOk.2.1 (Tm.hfm e) Tm.gR Tm.gC Tm.gS h3 h4
  gated := fun e m _ h =>
    gated_share_first P Y ιG (fm e) e m sG G.h1 G.hs1 G.hs2 G.hfe (G.hfm e) G.hY h
  weights := fun e m hOk hE hM =>
    weights_share_first P Y ιE (fm e) e m (Em.hfm e) Em.hY hE hM hOk.2.2.1

/-- What the chain behind the three points claims at its end. -/
theorem lay_last_first {fm : (tailW P).s7.Nx → Nm → Aff E P.J}
    {zt : (tailW P).s7.Nx → ℕ → E} {b s B sG : ℕ} (N : NormsOkF P Y ιN fm zt b s B)
    (Tm : TermsOkF P Y ιT fm) (G : GatedOkF P Y ιG fm sG) (Em : EmbOkF P Y ιE fm)
    (R : (tailW P).s7.Nx → Rest2 E (P.J ⊕ J₂)) (Dn : P.ofp.fs.X3 → M → Prop)
    (Ok' : (tailW P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkFirst P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) → Dn ((tailW P).xL e) m)
    (e : (tailW P).s7.Nx) (m : M) (hOk : OkFirst P Ok' e m)
    (h : Ledger.Holds (pullL (lateA Y (fm e)) (clFirst P Y ιN ιT ιG ιE R zt b B sG e).all)
      (P.msg m)) :
    (tailW P).ch.Last Dn e m :=
  last_of_shares (lay_shares_first P N Tm G Em R Dn Ok' dn) e m hOk h

end Cb.Pv.Lay.End
