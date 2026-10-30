-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/OwnFirstW.lean: the own rounds of the first layers' sub-proof, at a value, with the
weights' stretch filled: no stage's record is left as a letter with a law. The readings rd and rw
keep theirs (hrd, hrw).

Main names:
  `FullFPar`: over the letters of Cb/Pv/Lay/At/OwnW.lean: ls, nb, gB with their two conditions; the
    request's tokens in the first statement (tok); the mask entry of the scalar that is sent in the
    weights' round. The embedding is the library's reading of the committed matrix (embR).
  `ofp`: the letters of Cb/Pv/Lay/At/OwnFirst.lean.
  `st7F`: what the weights' stretch reads: as in a later group, and the two further points and the
    tokens.
  `wfPart`: the first group's weights' stretch of Cb/Pv/Lay/At/FootW.lean at the pairs of
    TnSplit.lean and TnEmb.lean, with its two laws proved.
  `ownF`: the record LayVOF. `ownF_pT`: what is claimed before the first round.
  `ownF_knowAt`: knowledge soundness of the chain at the value.

Limits: those of Cb/Pv/Lay/At/OwnW.lean. At a position whose token is not below the vocabulary's
size the library's embR is 0, so (J11) says there that the stream's entries are 0; the programs
refuse such a request, this chain does not.


-/
import Cb.Pv.Lay.At.OwnW
import Cb.Pv.Lay.At.OwnFirst
import Cb.Pv.Lay.At.TnEmb

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW embR xS dJ)

noncomputable section

/-- The letters of the first sub-proof that stay free, beside At/OwnW.lean's. -/
structure FullFPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends FullPar E M X where
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  hd : D.d = nb * 2 ^ ls
  /-- the request's tokens -/
  tok : X → ℕ → ℕ
  /-- the mask entry of the scalar that is sent in the weights' round -/
  mkE : J

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace FullFPar
variable (P : FullFPar E M X)

/-- The letters of At/OwnFirst.lean; the embedding is read off the committed matrix. -/
@[reducible] def ofp : OwnFPar E M X where
  toOwnPar := P.toOwnPar
  ls := P.ls
  nb := P.nb
  gB := P.gB
  hnb := P.hnb
  hd := P.hd
  emb := fun m => embR P.D.P P.kW (P.Wn m)
  tok := P.tok

/-- What the weights' stretch reads. -/
def st7F (z : P.ofp.fs.X3) (o : P.O4) : St7 E P.nW :=
  { P.ip.st7 P.num o with
    pa := Blocks.nat z.1.2
    pb := Blocks.nat z.2
    tok := P.tok (P.ofp.fs.x0F z) }

/-- The first group's weights' stretch. -/
def wf : WFirstL E :=
  P.wp0.wf (fun st => tenEmb P.D.P P.kW P.hW P.D.lT P.ls P.gB st.pa st.pb st.tok)
    (fun st m => P.ofp.fs.side (fun F i => xS P.D (P.rd m) 0 F i) st.pa st.pb) P.mkE

/-- The first group's weights' stretch, with its two laws. -/
def wfPart : P.ofp.WFPart where
  Wf := P.wf
  st7 := P.st7F
  rd7 := P.msg
  law := fun _ o m hc => P.wPart.law o m hc
  lawE := fun z o m h => by
    have h1 : P.wf.lhs (P.st7F z o) (P.msg m) =
        tval (tenEmb P.D.P P.kW P.hW P.D.lT P.ls P.gB (Blocks.nat z.1.2) (Blocks.nat z.2)
          (P.tok (P.ofp.fs.x0F z))) (Inst.Model.Layout.Tensor.matOf (P.Wn (P.msg m))) :=
      P.wp0.wf_lhs _ _ _ _ _
    rw [h1, tenEmb_val P.D.P P.kW P.hW P.D.lT P.ls P.gB P.nb P.hd P.hnb _ _ _ P.hH] at h
    exact h

/-- The own rounds of the first sub-proof, at the value. -/
def ownF : LayVOF E M X := P.ofp.layVOF P.wfPart

/-- What is claimed before the first round. -/
theorem ownF_pT (x : X) (m : M) :
    P.ownF.pT x m ↔
      (∀ k : ℕ × Fin P.D.nNu, ∀ Y < 2 ^ P.D.lT, dJ P.D (P.rd (P.msg m)) k.1 k.2 Y = 0) ∧
        P.ofp.fs.Q0F x m := Iff.rfl

/-- **Knowledge soundness of the first sub-proof's own rounds at the value: no premise but the
letters' fields.** -/
theorem ownF_knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (Dn : X → M → Prop) :
    KnowAt (P.ownF.toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ P.ownF.pT x m)
      (jt A0 (fun e => pr (P.ownF.toOwn.ch.back e)) (P.ownF.toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) (P.ownF.toOwn.ch.eps Ex) :=
  P.ownF.knowAt Ex A0 pr Dn

end FullFPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.FullFPar.ownF_knowAt
