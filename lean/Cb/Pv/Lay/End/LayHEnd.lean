-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/LayHEnd.lean: what the chain of the own rounds of a layers' sub-proof that is not the
first claims at its end, at the chain's value, from the pull-back of the ledger of the verifier's
claims: the norms' share proved, the other shares as premises.

Cb/Pv/Lay/End/LayEnd.lean has the frame: the ledger in eleven parts (LayCl), what the parts pay
(Shares), and last_of_shares. Here the chain is that of Cb/Pv/Lay/At/Own.lean. The four parts on the
norms are those of Cb/Pv/Lay/End/NormsShare.lean; the other seven are letters (Rest). The late
entries' forms are made from a form for each name, which may read the last statement (fm e).

Main definitions: Rest (the seven other parts), clAt (the ledger, part by part), St1Ok (the state
that the first sumcheck's output carries holds the element drawn before it), NormsOk (what the
norms' share asks of names, forms and sizes).
Main theorem: lay_shares (the record Shares, from the four other shares as premises). With
last_of_shares it gives what the chain claims at its end.

Limits. The shares dn, terms, gated, weights are premises. NormsOk is a premise: it is a choice of
names and forms, with two equations and a bound on sizes. These forms are the link's: that the late
entries agree with them (Agree, Cb/Sub/Late.lean) is owed by whoever lays the tail. That the ledger
is a program's is not said here.
The first sub-proof has another chain.


-/
import Cb.Pv.Lay.End.NormsShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : OwnPar E M X)
  (W : P.WPart) {Nm J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Y : LateLay Nm J₂)
  (ι : NormsNm → Nm)

/-- The seven parts of the ledger that are not on the norms. -/
structure Rest (E J : Type) where
  look : Ledger E J
  terms : Ledger E J
  gated : Ledger E J
  planes : Ledger E J
  emb : Ledger E J
  stack : Ledger E J
  merge : Ledger E J

/-- The ledger, part by part, off a last statement. zt: the tail of the lookup's point, off a last
statement. -/
noncomputable def clAt (R : (tailAt P W).s7.Nx → Rest E (P.J ⊕ J₂))
    (zt : (tailAt P W).s7.Nx → ℕ → E) (b B : ℕ) (e : (tailAt P W).s7.Nx) :
    LayCl E (P.J ⊕ J₂) where
  look := (R e).look
  sq := sqAt P W Y ι e (zt e) b B
  bat := batAt P W Y ι e (zt e)
  led := rowsAt P W Y ι e (zt e)
  terms := (R e).terms
  gated := (R e).gated
  hot := hotAt P Y ι
  planes := (R e).planes
  emb := (R e).emb
  stack := (R e).stack
  merge := (R e).merge

/-- The state that the first sumcheck's output carries holds the element that was drawn before that
sumcheck. It is so at the last statement of a run (hst_run in Cb/Pv/Lay/End/NormsBillAt.lean). -/
def St1Ok (e : (tailAt P W).s7.Nx) : Prop :=
  ((tailAt P W).b1 e).2.st.1.2 = ((tailAt P W).b1 e).1.1.1.2

/-- What the norms' share asks of sizes, names and forms. -/
structure NormsOk (fm : (tailAt P W).s7.Nx → Nm → Aff E P.J) (zt : (tailAt P W).s7.Nx → ℕ → E)
    (b s B : ℕ) : Prop where
  hl : lDd P.D = b + s
  hd : P.D.d = B * 2 ^ s
  hB : B ≤ 2 ^ b
  hfm : ∀ e x, InRange P.D.nNu B P.D.ne P.D.nx x →
    fm e (ι x) = toAff (normsFm P.rd P.D (eAt P W e (zt e)) (P.D.lL + 1) b s x)
  gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (ι (.xi ν l kh))
  gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atP ν n))
  gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (ι (.atR ν n))
  gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (ι (.sel l x))

variable {Y ι}

/-- The record Shares at the chain's value. The norms' share is proved; the others are premises. -/
theorem lay_shares {fm : (tailAt P W).s7.Nx → Nm → Aff E P.J}
    {zt : (tailAt P W).s7.Nx → ℕ → E} {b s B : ℕ} (N : NormsOk P W Y ι fm zt b s B)
    (R : (tailAt P W).s7.Nx → Rest E (P.J ⊕ J₂)) (Dn : P.XT → M → Prop)
    (Ok : (tailAt P W).s7.Nx → M → Prop) (hSt : ∀ e m, Ok e m → St1Ok P W e)
    (dn : ∀ e m, Ok e m → Ledger.Holds (pullL (lateA Y (fm e)) (R e).look) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (hotAt P Y ι)) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).planes) (P.msg m) → Dn ((tailAt P W).xL e) m)
    (terms : ∀ e m, Ok e m → Ledger.Holds (pullL (lateA Y (fm e)) (R e).terms) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).stack) (P.msg m) →
      (tailAt P W).s3.Lc ((tailAt P W).b3 e).1.1 ((tailAt P W).b3 e).1.2 m ∧
        (tailAt P W).ow3 ((tailAt P W).b3 e) m ∧
        (tailAt P W).s4.Lc ((tailAt P W).b4 e).1.1 ((tailAt P W).b4 e).1.2 m ∧
        (tailAt P W).ow4 ((tailAt P W).b4 e) m)
    (gated : ∀ e m, Ok e m → Ledger.Holds (pullL (lateA Y (fm e)) (R e).gated) (P.msg m) →
      (tailAt P W).s5.Lc ((tailAt P W).b5 e).1.1 ((tailAt P W).b5 e).1.2 m ∧
        (tailAt P W).ow5 ((tailAt P W).b5 e) m ∧
        (tailAt P W).s6.Lc ((tailAt P W).b6 e).1.1 ((tailAt P W).b6 e).1.2 m ∧
        (tailAt P W).ow6 ((tailAt P W).b6 e) m)
    (weights : ∀ e m, Ok e m → Ledger.Holds (pullL (lateA Y (fm e)) (R e).emb) (P.msg m) →
      Ledger.Holds (pullL (lateA Y (fm e)) (R e).merge) (P.msg m) →
      (tailAt P W).lW ((tailAt P W).xW e) ((tailAt P W).y7 e).1.2 m ∧
        (tailAt P W).s7.Lc ((tailAt P W).y7 e) e.1.2 m ∧ (tailAt P W).s7.Out e m) :
    Shares (tailAt P W) Dn P.msg (fun e => lateA Y (fm e)) (clAt P W Y ι R zt b B) Ok where
  dn := dn
  norms := fun e m hOk h1 h2 h3 h4 =>
    norms_share P W Y ι (fm e) e (zt e) m b s B N.hl N.hd N.hB (hSt e m hOk) (N.hfm e)
      N.gXi N.gP N.gR N.gS h1 h2 h3 h4
  terms := terms
  gated := gated
  weights := weights

end Cb.Pv.Lay.End
