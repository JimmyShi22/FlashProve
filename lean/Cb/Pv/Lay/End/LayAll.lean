-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayAll.lean: what the chain of the own rounds of a layers' sub-proof that is not the
first claims at its end, at the chain's value, from the pull-back of the ledger of the verifier's
claims: three shares proved (that of the terms but for the drawn coefficient), the weights' share a
rewording of its two premises, one share a premise.

Cb/Pv/Lay/End/LayHEnd.lean gives the record Shares at the chain of Cb/Pv/Lay/At/Own.lean with the
norms' share proved. Here the letters are those of Cb/Pv/Lay/At/OwnW.lean (FullPar), and three more
shares are put in: that of the terms and the batched sumcheck (Cb/Pv/Lay/End/TermsBillAt.lean), the
gated products' (Cb/Pv/Lay/End/GatedAt.lean) and the weights' (Cb/Pv/Lay/End/WeightsShare.lean).
With last_of_shares this gives Ch.Last.

Main definitions.
 - Rest3: the three parts of the ledger that stay letters: look, planes, emb.
 - restAt: the seven parts that are not on the norms: these three; the claims on the terms' end
   values; the three claims of the batched sumcheck; the six claims on the gated products; the
   merge's row; all off a last statement.
 - TermsOk, GatedOk: what these shares ask of sizes, names and forms.
 - OkAt: what is asked of a last statement and the messages beside the ledger: St1Ok, which holds
   of a run's last statement; the coefficient drawn in the sumcheck of the terms is not 0; the
   pending row on the committed weights holds; and a letter Ok' for the share that is a premise.
Main theorems: lay_shares_all (the record Shares); lay_last_all (Ch.Last of the chain behind the
token point).

Limits. Of the bill's eighteen clauses seven are True at this chain (c1, c3, c4, c5, c6, c7, lW).
The share dn (the claim of the first statement, from the parts look, hot, planes) is a premise.
NormsOk, TermsOk and GatedOk are premises: choices of names and forms, and conditions on sizes.
These forms are the link's: that the late entries agree with them (Agree, Cb/Sub/Late.lean) is owed
by whoever lays the tail. The weights' share says its two premises in other words: the merge's row
is the first output claim by definition, and the pending row is the second. The pending row leaves
the sub-proof: it is asked, not paid. So is that the drawn coefficient is not 0. No ledger can pay
that: it comes from a test of the last statement that is laid behind the chain (LayVO.epsOK in
Cb/Pv/Lay/OwnTest.lean); Cb/Pv/Lay/End/LayHEndAt.lean takes it as a premise at the run. Of the
eleven parts of the ledger three are letters (look, planes, emb); the part emb is read by no share
here. The part on the batched sumcheck is the three owed claims themselves, written on the early
entries. The programs' two claims on the form parts read late tables; that their pull-back is these
claims is shown nowhere. Of the other parts, that they are a program's is not said here. The first
sub-proof has another chain.


-/
import Cb.Pv.Lay.End.GatedAt
import Cb.Pv.Lay.End.LayHEnd
import Cb.Pv.Lay.End.TermsBillAt
import Cb.Pv.Lay.End.WeightsShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (lF lFe)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂) (ιN : NormsNm → Nm)
  (ιT : TermsNm → Nm) (ιG : GatedNm → Nm)

/-- The letters of the chain behind the token point. -/
noncomputable abbrev tailF : LayTail E M P.XT := tailAt P.toOwnPar P.wPart

/-- The three parts of the ledger that stay letters. -/
structure Rest3 (E J : Type) where
  look : Ledger E J
  planes : Ledger E J
  emb : Ledger E J

/-- The seven parts of the ledger that are not on the norms, off a last statement. -/
noncomputable def restAt (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (sG : ℕ)
    (e : (tailF P).s7.Nx) : Rest E (P.J ⊕ J₂) where
  look := (R e).look
  terms := termsLedAt P.toOwnPar P.wPart Y ιT e
  gated := gatedLedOf P.fp Y ιG ((tailF P).b5 e).2 ((tailF P).b6 e).2 sG
  planes := (R e).planes
  emb := (R e).emb
  stack := stackLedAt P.toOwnPar P.wPart e
  merge := mergeLed P.wp0 e.2

/-- What the share of the terms asks of names and forms. -/
structure TermsOk (fm : (tailF P).s7.Nx → Nm → Aff E P.J) : Prop where
  hfm : ∀ e (x : TermsNm), x.InR P.D → fm e (ιT x) =
    toAff (termsFm P.rd P.D (termsEAt P.tp ((tailF P).b3 e).2).rt x)
  gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ιT (.row ν n))
  gC : ∀ l k, l < P.D.ne → k < 3 → Y.good (ιT (.sc l k))
  gS : ∀ l x k, l < P.D.ne → x < P.D.nx → k < 1 → Y.good (ιT (.sel l x k))

/-- What the gated products' share asks of sizes, names and forms. -/
structure GatedOk (fm : (tailF P).s7.Nx → Nm → Aff E P.J) (sG : ℕ) : Prop where
  h1 : 1 ≤ P.D.lL
  hs1 : sG ≤ lF P.D
  hs2 : sG ≤ lFe P.D
  hfe : P.D.fe = 2 ^ lFe P.D
  hfm : ∀ e (x : GatedNm), x.InR P.D sG → fm e (ιG x) = toAff (gatedFm P.rd P.D
    (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) sG x)
  hY : GoodNm Y ιG P.D sG

/-- What is asked of a last statement and the messages beside the ledger. -/
def OkAt (Ok' : (tailF P).s7.Nx → M → Prop) (e : (tailF P).s7.Nx) (m : M) : Prop :=
  St1Ok P.toOwnPar P.wPart e ∧ ((tailF P).b3 e).2.eps ≠ 0 ∧
    Pending P.wp0
      (rowW (fun c : Fin P.wp0.n => e.2.st.2 ^ (c : ℕ)) (fun c => P.wp0.ten c e.2.st.1)
        ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2))
      ((noKept P.wp0.wt.L.Sm).outPt P.wp0.wt.L.Mk e.2)
      ((noKept P.wp0.wt.L.Sm).outB P.wp0.wt.L.Mk e.2) (e.2.vals ()) (P.msg m) ∧ Ok' e m

variable {Y ιN ιT ιG}

/-- The record Shares at the chain's value: three shares are proved, the weights' share is a
rewording of its two premises; dn is a premise. -/
theorem lay_shares_all {fm : (tailF P).s7.Nx → Nm → Aff E P.J}
    {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}
    (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG)
    (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Dn : P.XT → M → Prop)
    (Ok' : (tailF P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkAt P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) → Dn ((tailF P).xL e) m) :
    Shares (tailF P) Dn P.msg (fun e => lateA Y (fm e))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B) (OkAt P Ok') :=
  lay_shares P.toOwnPar P.wPart N (restAt P Y ιT ιG R sG) Dn (OkAt P Ok') (fun _ _ h => h.1) dn
    (fun e m hOk h3 h4 => terms_bill P.toOwnPar P.wPart Y ιT (fm e) e m hOk.2.1 (Tm.hfm e) Tm.gR
      Tm.gC Tm.gS h3 h4)
    (fun e m _ h => gated_share P.toOwnPar P.wPart Y ιG (fm e) e m sG G.h1 G.hs1 G.hs2 G.hfe
      (G.hfm e) G.hY h)
    (fun e m hOk _ h => weights_share P (lateA Y (fm e)) e m h hOk.2.2.1)

/-- What the chain behind the token point claims at its end. -/
theorem lay_last_all {fm : (tailF P).s7.Nx → Nm → Aff E P.J}
    {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}
    (N : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (Tm : TermsOk P Y ιT fm)
    (G : GatedOk P Y ιG fm sG)
    (R : (tailF P).s7.Nx → Rest3 E (P.J ⊕ J₂)) (Dn : P.XT → M → Prop)
    (Ok' : (tailF P).s7.Nx → M → Prop)
    (dn : ∀ e m, OkAt P Ok' e m →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P.toOwnPar Y ιN)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) → Dn ((tailF P).xL e) m)
    (e : (tailF P).s7.Nx) (m : M) (hOk : OkAt P Ok' e m)
    (h : Ledger.Holds (pullL (lateA Y (fm e))
      (clAt P.toOwnPar P.wPart Y ιN (restAt P Y ιT ιG R sG) zt b B e).all) (P.msg m)) :
    (tailF P).ch.Last Dn e m :=
  last_of_shares (lay_shares_all P N Tm G R Dn Ok' dn) e m hOk h

end Cb.Pv.Lay.End
