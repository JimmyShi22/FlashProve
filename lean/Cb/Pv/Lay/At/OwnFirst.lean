-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/OwnFirst.lean: all stages of the first layers' sub-proof's own rounds (LayVF, LayVOF:
Cb/Pv/Lay/OwnAll.lean) at a value, with the laws seam and rides proved, the weights' stretch still a
letter.

Main names:
  `OwnFPar`: over the letters of Cb/Pv/Lay/At/Own.lean those of First.lean: ls, nb, gB, emb, tok.
  `fs`: the letters of Cb/Pv/Lay/At/First.lean.
  `WFPart`: the first group's weights' stretch as a letter with two laws: its older claims give the
    batched sumcheck's rows on the weight claims' end values; its identity says that the embedding's
    side is the stream's side at the two further points (its value: Cb/Pv/Lay/At/OwnFirstW.lean).
  `layVF`, `layVOF`: the records. `layVOF_pT`: what is claimed before the first round.
  `layVOF_knowAt`: knowledge soundness of the chain at these letters.

Limits: those of Cb/Pv/Lay/At/Own.lean.


-/
import Cb.Pv.Lay.At.Own
import Cb.Pv.Lay.At.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW dJ)

noncomputable section

/-- The letters of the first sub-proof that stay free, beside At/Own.lean's. -/
structure OwnFPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends OwnPar E M X where
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  hd : D.d = nb * 2 ^ ls
  emb : (J → E) → ℕ → ℕ → E
  tok : X → ℕ → ℕ

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace OwnFPar
variable (P : OwnFPar E M X)

/-- The letters of At/First.lean. -/
@[reducible] def fs : FirstPar E M X where
  toForePar := P.toForePar
  ls := P.ls
  nb := P.nb
  gB := P.gB
  hnb := P.hnb
  hd := P.hd
  emb := P.emb
  tok := P.tok

/-- The stages up to the batched sumcheck. -/
abbrev midF : Mid E M P.fs.X3 := P.mid (X' := P.fs.X3) P.fs.x0F P.fs.pvF P.fs.Rd0F

/-- The first group's weights' stretch, as a letter with two laws. -/
structure WFPart where
  Wf : WFirstL E
  st7 : P.fs.X3 → P.O4 → Wf.St
  rd7 : M → Wf.J → E
  /-- its older claims give the rows on the weight claims' end values -/
  law : ∀ z o m, (∀ a, Wf.toWeightsL.val (st7 z o) (rd7 m) a = Wf.sh a (st7 z o)) →
    ∀ i, P.In.toSum.T.par.EHolds o (P.msg m) (.inr (.inr i))
  /-- its identity says that the embedding's side is the stream's side -/
  lawE : ∀ z o m, Wf.lhs (st7 z o) (rd7 m) = Wf.rhs (st7 z o) (rd7 m) →
    P.fs.sumE (P.fs.x0F z) m (Blocks.nat z.1.2) (Blocks.nat z.2) =
      P.fs.sumX m (Blocks.nat z.1.2) (Blocks.nat z.2)

/-- The older claims alone, as At/Own.lean's letter, at a statement behind the three points. -/
def wp (W : P.WFPart) (z : P.fs.X3) : P.WPart where
  Wt := W.Wf.toWeightsL
  st7 := W.st7 z
  rd7 := W.rd7
  law := W.law z

/-- All stages behind the three points. -/
def layVF (W : P.WFPart) : LayVF E M P.fs.X3 where
  toMid := P.midF
  Ft :=
    { Gp := P.fp.gp
      st5 := fun b => P.st5 b.2
      rd5 := P.msg
      Rt := P.fp.rt
      st6 := fun b => P.st6 b.2
      rd6 := P.msg
      Wf := W.Wf
      st7 := fun b => W.st7 (P.midF.x3 b.1.1.1) b.2
      rd7 := W.rd7 }
  ow4 := fun b m => P.ow4 b.2 m
  seam := fun b m h0 h5 h6 h7 =>
    P.out_of (P.wp W (P.midF.x3 b.1.1.1)) b.2 m h0 h5 h6 h7.1
  rides := fun b m h7 =>
    (P.fs.rd0_iff (P.midF.x3 b.1.1.1) m).2 (W.lawE (P.midF.x3 b.1.1.1) b.2 m h7.2)

/-- The own rounds of the first sub-proof. -/
def layVOF (W : P.WFPart) : LayVOF E M X where
  gT := P.D.lT
  K := ℕ × Fin P.D.nNu
  d := fun _ m k => dJ P.D (P.rd (P.msg m)) k.1 k.2
  Q0 := P.fs.Q0F
  gA := P.ls + P.D.lT
  gB := P.gB
  e := P.fs.eG
  Q := P.fs.QF
  V := P.layVF W
  atPt := P.fs.first_atPt
  atTwo := P.fs.first_atTwo

/-- What is claimed before the first round: all 17 identities of every norm at every position, the
lookup's join at the true sum of the terms, and all gaps of (J11). -/
theorem layVOF_pT (W : P.WFPart) (x : X) (m : M) :
    (P.layVOF W).pT x m ↔
      (∀ k : ℕ × Fin P.D.nNu, ∀ Y < 2 ^ P.D.lT, dJ P.D (P.rd (P.msg m)) k.1 k.2 Y = 0) ∧
        P.fs.Q0F x m := Iff.rfl

/-- **Knowledge soundness of the first sub-proof's own rounds at the value.** -/
theorem layVOF_knowAt (W : P.WFPart) {Kc X0 Wp : Type} (Ex : ExtSpec)
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt ((P.layVOF W).toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ (P.layVOF W).pT x m)
      (jt A0 (fun e => pr ((P.layVOF W).toOwn.ch.back e)) ((P.layVOF W).toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) ((P.layVOF W).toOwn.ch.eps Ex) :=
  (P.layVOF W).knowAt Ex A0 pr Dn

end OwnFPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.OwnFPar.layVOF_knowAt
