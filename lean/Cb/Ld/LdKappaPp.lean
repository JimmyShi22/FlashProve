-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaPp.lean: one number κ above every round-by-round error of the object's five lists,
counting proof of work at the rounds that draw locations and at no other round, for the object at
the plan of a write-up of ours (lean/CREDITS.md) for the linear test (one splitting in the
shared part; nine whole tests).

A record, a definition and four statements (in `Cb.Spec`); the proofs are in
Cb/Ld/LdKappaPpProofs.lean. The analogue of Cb/Ld/LdKappaW.lean (the plan without a splitting, seven
whole tests): read its head first. Generic: any finite fields. Nothing assumed beyond the hypotheses
of the statements and whatever the arguments hold as proofs. "Work" is proof of work throughout.
The five lists are the errors of the protocol's sub-protocols: weights-formedness, the test for
linear constraints at one instance, the link, a request's preamble, the test at N instances (in
Lean: wf, linOff, link, req, linOn). These errors are numbers that the object lists (`obj.nums`,
Cb/Obj/LdObject.lean: a `SubsR.Nums`, Hiop/RecBuild.lean, whose five entries each have the data
field `err`): that a sub-protocol is sound at the numbers that are listed for it is no statement of
this file (the premise `Z.HypRefPP` asks it of the links of the request's sub-protocol moves and of
the link that each of its fold moves holds (`LdFoldD.Hyp.good`, Cb/Req1/LdSegKit.lean):
`core.req.rHyp : P.r.Hyp`); for the object that tie is `Spec.ldObj_hyp` (Cb/Obj/LdObject.lean),
under `Obj.OK L`, in the sense of `SubsR.HypK` (Hiop/RecBuild.lean) (that condition itself asks
soundness of the parts one level down: the tie carries soundness, it does not found it).

Why: the record of Cb/Ld/LdKappaW.lean is typed on `LdObjZ`. In that plan the first whole test of a
session runs on the fold's and Ω's messages together: by reading it has no counterpart in the
write-up. The object at the write-up's plan is `LdObjZp`
(Cb/Obj/LdObjectPpData.lean).
Both end at the level `LdObjT`; what differs is the two closings.

Main names:
  `LdWk4` (Cb/Ld/LdKappaW.lean): four numbers of bits by the class of the round that draws locations
    (off, lk, sh, ins).
  `Z.KapW ws κ`: thirteen clauses.
    wf: weights-formedness (no work);
    lin: the offline core, off at "loc";
    t₁ .. t₄: the offline test's four whole tests, off;
    link, tK: the link's core and whole test, lk;
    linB: the core of the test at N instances, sh at "loc";
    t₁B, t₂B: the two shared whole tests (the group of the index's fold; Ω's group): sh;
    t₃B, t₄B: the instance's own (the instance's group; the group of what the request leaves
      beside): ins.
    The senders in lin, link, linB are the standard ones: those that the object reads (`P.D`,
      Cb/Obj/LdObjectPlanPaper.lean).
  The splitting has no clause. The front of each closing is "split ; a step without rounds": one
    round, in which the prover says one scalar in the clear; its error is 0 by definition
    (Cb/Ld/LdSplit.lean). Under `kIs`, `kIsB` (`LdObjPp.HypR`, Cb/Obj/LdObjectPlanPaper.lean), the
    oracle message that holds the splitting's mask entry stands in Ω's family: the error of its
    sending is in the cores' clause sO.
  `Z.bitsP ws`: the five lists of bits, in the order of the rounds: 0 everywhere but at the rounds
    that draw locations.
  `Spec.ldKappaPp_any`: generic in the request (`Z.HypRefPP`, Cb/Obj/LdObjectPpDataP.lean: the
    request is a parameter P): `Z.HypRefPP` → `Z.KapW ws κ` → `P.r.BelowW ws.ins κ`
    (Cb/Ld/LdKappaWork.lean: the request's preamble with ins bits at its rounds that draw locations)
    → round by round, with the bits `Z.bitsP ws`: e ≤ κ · (2^b · number of values). Used of
    `Z.HypRefPP`: core.reqIs and the nine equations "the whole test is its tower".
  `Spec.ldKappaPp`: the request `ldReqRef` (Cb/Req1/LdReqRef.lean): `Z.HypRefPJ` at any κ'
    (conditions on the object at the reference request: Cb/Obj/LdObjectPpData.lean) →
    `Z.KapW ws κ` → `LdReqKapW` (Cb/Ld/LdKappaW.lean) at ws.ins, κ → the five lists are at most κ
    round by round, with the bits `Z.bitsP ws`.
  `Spec.ldKappaPp_work`: under the hypotheses of `Spec.ldKappaPp`: (1) every work vector
    (`SubsR.Bits`, Cond/ObjBits.lean: numbers of proof-of-work bits for the rounds of the
    five lists) that has exactly these bits has the object's lists at most κ, work counted
    (`SubsR.Nums.BelowG`); (2) there is one; (3) none of its bits exceeds the largest of the four
    numbers. `Spec.ldKappaPp_bits`: the same three clauses from "round by round, with these bits"
    alone.

Used of `Z.HypRefPJ` at κ': the equation core.reqIs and the nine equations "the whole test is its
tower". Its own clauses "below κ'" are not used.

Limits: as in the heads of Cb/Ld/LdKappa.lean, Cb/Ld/LdKappaW.lean, these still speak of more than
numbers, among them: the lists of lookups, sumchecks and batchings, each closing's link's list.
This file says nothing on the size of κ. It says nothing on the way back. It does not say what the
work costs. This file does not show that the classes are the write-up's (a swap in a clause
and in its list at once no statement of this file can notice: that rests on a reading).


The guard: Cb/Ld/LdKappaPpLeast.lean (under `Z.HypRefPP`, or `Z.HypRefPJ`: for every object at once:
the records hold, for all four numbers of bits, at every κ above all round errors without work;
under `Z.HypRefPP` the request's record comes without work: `P.r.Below κ`, not the
`P.r.BelowW ws.ins κ` that `Spec.ldKappaPp_any` asks). It is not tight. This file gives no instance
that meets its hypotheses, so as far as this file shows its theorems may hold of nothing.

The tight one, the way back with work (under `Z.HypRefPP` (`Z.HypRefPJ`): the records hold at κ if
and only if the first count (`Nums.maxAll`, Cond/ObjQuote.lean) at a work with the named bits is
at most κ), is not proved here.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdKappaW
import Cb.Obj.LdObjectPpDataP
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record with work, at the write-up's plan: the four lists that are not the
request's. -/
structure LdObjZp.KapW (Z : LdObjZp F E) (ws : LdWk4) (κ : ℝ≥0∞) : Prop where
  wf   : Z.R.Bw.Kap κ
  lin  : Z.R.W.O.toC.P.KapCW (Z.R.toLdObjD.std Z.R.Y).Sn Z.R.εf ws.off κ
  t₁   : Z.R.TP₀.D₁.KapTW (Z.R.TP₀.D₁.up3 Z.tw₁) ws.off κ
  t₂   : Z.R.TP₀.D₂.KapTW (Z.R.TP₀.D₂.up3 Z.tw₂) ws.off κ
  t₃   : Z.R.TP₀.D₃.KapTW (Z.R.TP₀.D₃.up3 Z.tw₃) ws.off κ
  t₄   : Z.R.X.run.KapTW (Z.R.X.run.up3 Z.tw₄) ws.off κ
  link : Z.R.K.P.KapCW (Z.R.toLdObjD.std Z.R.Y).Sl Z.R.ε₀ Z.R.ε₁ ws.lk κ
  tK   : Z.R.Kc.run.KapTW (Z.R.Kc.run.up3 Z.twK) ws.lk κ
  linB : Z.R.on.ol.toC.P.KapCBW (Z.R.toLdObjD.std Z.R.Y).SnB Z.R.εfB Z.R.N ws.sh κ
  t₁B  : Z.R.TB₀.D₁.KapTW (Z.R.TB₀.D₁.upJ Z.tw₁B) ws.sh κ
  t₂B  : Z.R.TB₀.D₂.KapTW (Z.R.TB₀.D₂.upJ Z.tw₂B) ws.sh κ
  t₃B  : Z.R.TB₀.D₃.KapTW (Z.R.TB₀.D₃.upJ Z.tw₃B) ws.ins κ
  t₄B  : Z.R.XB.run.KapTW (Z.R.XB.run.upJ Z.tw₄B) ws.ins κ

/-- The five lists of bits. The entry [0] after the core in `linOff` and in `linOn` is the
splitting's one round. -/
def LdObjZp.bitsP (Z : LdObjZp F E) (ws : LdWk4) : Bits5 where
  wf     := List.replicate Z.R.Bw.link.R.shape.nAll 0
  linOff := linBits ws.off ++
    ([0] ++ ((0 :: Z.R.TP₀.D₁.bitsT (Z.R.TP₀.D₁.up3 Z.tw₁) ws.off) ++
        ((0 :: Z.R.TP₀.D₂.bitsT (Z.R.TP₀.D₂.up3 Z.tw₂) ws.off) ++
          ((0 :: Z.R.TP₀.D₃.bitsT (Z.R.TP₀.D₃.up3 Z.tw₃) ws.off) ++
            ((0 :: Z.R.X.run.bitsT (Z.R.X.run.up3 Z.tw₄) ws.off) ++ [])))))
  link   := lkBits ws.lk ++ ((0 :: Z.R.Kc.run.bitsT (Z.R.Kc.run.up3 Z.twK) ws.lk) ++ [])
  req    := Z.R.r.bits ws.ins
  linOn  := linBits ws.sh ++
    ([0] ++ ((0 :: Z.R.TB₀.D₁.bitsT (Z.R.TB₀.D₁.upJ Z.tw₁B) ws.sh) ++
        ((0 :: Z.R.TB₀.D₂.bitsT (Z.R.TB₀.D₂.upJ Z.tw₂B) ws.sh) ++
          ((0 :: Z.R.TB₀.D₃.bitsT (Z.R.TB₀.D₃.upJ Z.tw₃B) ws.ins) ++
            ((0 :: Z.R.XB.run.bitsT (Z.R.XB.run.upJ Z.tw₄B) ws.ins) ++ [])))))

end

namespace Spec

/-- Round by round, with these bits; the request a parameter. -/
def ldKappaPp_any : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (P : LdReqPack F E) (Rq : LdORE F E Kc)
      (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC) (plR : Rq.Bn → Rq.S.Ent → Prop)
      (κ : ℝ≥0∞) (ws : LdWk4),
    Z.HypRefPP p P Rq V p₀ plR → Z.KapW ws κ → P.r.BelowW ws.ins κ →
    Z.R.toPp.toT.obj.nums.BelowB (Z.bitsP ws) κ

/-- States, of the work vectors with these bits, from "round by round" alone: each has the five
lists at most κ, work counted; there is one; none of its bits exceeds `ws.top`. -/
def ldKappaPp_bits : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Z : LdObjZp F E)
      (κ : ℝ≥0∞) (ws : LdWk4),
    Z.R.toPp.toT.obj.nums.BelowB (Z.bitsP ws) κ →
    (∀ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws) → Z.R.toPp.toT.obj.nums.BelowG g κ) ∧
    (∃ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws)) ∧
    ∀ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws) →
      g.wf.AllLe ws.top ∧ g.linOff.AllLe ws.top ∧ g.link.AllLe ws.top ∧
      g.req.AllLe ws.top ∧ g.linOn.AllLe ws.top

/-- Round by round, with these bits: the request `ldReqRef`. -/
def ldKappaPp : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (Rq : LdORE F E Kc)
      (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC)
      (plR : Rq.Bn → Rq.S.Ent → Prop) (ws : LdWk4),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ' V p₀ plR → Z.KapW ws κ →
    LdReqKapW ws.ins κ Rq first (.nil first.tgt) Ls T → Z.R.toPp.toT.obj.nums.BelowB (Z.bitsP ws) κ

/-- The work vectors with these bits. -/
def ldKappaPp_work : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZp F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (Rq : LdORE F E Kc)
      (core : Rq.Cf.conf.PIdx × Rq.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (Rq.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc Rq.ix first.tgt b) (T : LdRefT Rq b)
      (qφ : Finset (LdStage.start E Kc (Rq.O.jReq core)).J.E.Pos → Prop)
      (q : Finset Rq.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (V : Z.Zw.StdW Fp) (p₀ : LdLinPp Rq.O.d.ol.toC)
      (plR : Rq.Bn → Rq.S.Ent → Prop) (ws : LdWk4),
    Z.HypRefPJ p Rq core first b Ls T qφ q κ' V p₀ plR → Z.KapW ws κ →
    LdReqKapW ws.ins κ Rq first (.nil first.tgt) Ls T →
    (∀ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws) → Z.R.toPp.toT.obj.nums.BelowG g κ) ∧
    (∃ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws)) ∧
    ∀ g : Z.R.toPp.toT.obj.subs.Bits, g.Is (Z.bitsP ws) →
      g.wf.AllLe ws.top ∧ g.linOff.AllLe ws.top ∧ g.link.AllLe ws.top ∧
      g.req.AllLe ws.top ∧ g.linOn.AllLe ws.top

end Spec
end Cb
