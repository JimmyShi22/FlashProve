-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaW.lean: one number κ above every round-by-round error of the object's (`LdObjZ`,
Cb/Obj/LdObjectData.lean) five lists, counting proof of work at the rounds that draw locations and
at no other round.

Records, definitions and two statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdKappaWProofs.lean.
The five lists are the errors of the protocol's sub-protocols: weights-formedness, the test for
linear constraints at one instance, the link, a request's preamble, the test at N instances (in
Lean: wf, linOff, link, req, linOn).
"Work" is proof of work throughout; the error e of a round with b bits whose verifier message has v
values is at most κ, work counted, if e ≤ κ · (2^b · v) (`Err.BelowB`, Cb/Ld/LdKappaBits.lean).
These errors are numbers that the object lists (`obj.nums`, Cb/Obj/LdObject.lean: a `SubsR.Nums`,
Hiop/RecBuild.lean, whose five entries each have the data field `err`): that a sub-protocol is sound
at the numbers that are listed for it is no statement of this file (the premise `Z.HypRef` asks it
of the link that each closing's fold move holds (`LdFoldD.Hyp.good`, Cb/Req1/LdSegKit.lean):
`req.proto.segs`); for the object that tie is `Spec.ldObj_hyp` (Cb/Obj/LdObject.lean), under
`Obj.OK L`, in the sense of `SubsR.HypK` (Hiop/RecBuild.lean) (that condition itself asks soundness
of the parts one level down: the tie carries soundness, it does not found it).

Why: Cb/Ld/LdKappa.lean bounds every round without work. The error of a round that draws t locations
depends on t: for the base case the clause `loc` of `LdJoint.KapBW` (Cb/Ld/LdKappaWorkObj.lean) has,
with n long positions and the radius r, (n - r - 1)^t of n^t values; the field's size does not occur
in it, so a larger field does not lower it.
In a write-up of ours that is not in this repository (lean/CREDITS.md) the rounds that draw
locations are far weaker by themselves than all others, and get the rest from work: its rule for
parameters is (round error) · 2^-(bits of work of that round) ≤ target. So without work κ can be no
better than the weakest such round. Here each such round has a number of bits, by its class.

A work vector (`SubsR.Bits`, Cond/ObjBits.lean) holds numbers of proof-of-work bits for
the rounds of the five lists.


With all four numbers 0 `Spec.ldKappaW` says what `Cb.ldKappa` says.

Main names:
  `LdWk4`: four numbers of bits, by the class of the round that draws locations: off (the offline
    test and its three whole tests); lk (the link and its whole test); sh (the shared rounds of a
    session: the core of the test at N instances, and its first whole test, which runs once); ins
    (an instance's own rounds: each closing of the request; the second and third whole test of the
    test at N instances).
  `D.KapTW T w κ`: one whole test with its tower: the bridge's number (no work); `T.KapW w κ`
    (Cb/Ld/LdKappaWorkObj.lean): w at the second round of each code switch and of the base case.
  `Z.KapW ws κ`: the record `Z.Kap` of Cb/Ld/LdKappa.lean, field for field, with the class's bits
    at the clauses "loc".
  `LdReqKapW w κ R first more Ls T`: the request's five clauses "at most κ"
    (Cb/Req1/LdReqRefFinal.lean: bFirst .. bLast), with w at each closing's clause "loc".
  `Z.bits ws`: the five lists of bits, in the order of the rounds: 0 everywhere but at the rounds
    that draw locations.
  `Spec.ldKappaW`: for `more` all of whose moves are sendings or steps (`hm`): `Z.HypRef` at any κ'
    (conditions on the object at the reference request: Cb/Obj/LdObjectDataRef.lean)
    → `Z.KapW ws κ` → `LdReqKapW ws.ins κ R first more Ls T` → the five lists are at most κ round by
    round, with the bits `Z.bits ws`.
  `Spec.ldKappaW_work`: the work vectors with exactly these bits (three clauses).

Used of `Z.HypRef` at κ': the equation reqIs and the seven equations "the whole test is its tower".
Its own five clauses "below κ'" are not used here: `LdReqKapW` stands in their place (they have no
work; at κ' := κ they would ask the closings' locations to be below κ by themselves).

Limits: as in the head of Cb/Ld/LdKappa.lean, these still speak of more than numbers, among them:
the lists of lookups, sumchecks and batchings, each closing's link's list (in numbers, block by
block: Cb/Ld/LdKappaList.lean, Cb/Ld/LdGroupLinkBelow.lean: not put in), the lists of the moves of
`more` (`bMore`).
This file says nothing on the size of κ. It says nothing on the way back (that the records hold at
the first count (`Nums.maxAll`, Cond/ObjQuote.lean) with this work). It does not say what the
work costs: neither the chance that a search fails nor the searches in the prover's time is
bounded here.
It does not say that work at these rounds and no others is
the best choice.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaWorkRef
import Cb.Ld.LdKappa
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- Bits of work, by the class of the round that draws locations. -/
structure LdWk4 where
  off : ℕ
  lk  : ℕ
  sh  : ℕ
  ins : ℕ

/-- the largest of the four -/
def LdWk4.top (ws : LdWk4) : ℕ := max (max ws.off ws.lk) (max ws.sh ws.ins)

structure LdRunD.KapTW {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S)
    (T : D.Tow) (w : ℕ) (κ : ℝ≥0∞) : Prop where
  bridge : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)
  tow    : T.KapW w κ

/-- the bits of the tower of a whole test -/
abbrev LdRunD.bitsT
    {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) (T : D.Tow) (w : ℕ) : List ℕ :=
  T.bits w

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record with work: the four lists that are not the request's. -/
structure LdObjZ.KapW (Z : LdObjZ F E) (ws : LdWk4) (κ : ℝ≥0∞) : Prop where
  wf   : Z.R.Bw.Kap κ
  lin  : Z.R.W.O.toC.P.KapCW Z.R.Sn Z.R.εf ws.off κ
  t₁   : Z.R.TP₀.D₁.KapTW Z.tw₁ ws.off κ
  t₂   : Z.R.TP₀.D₂.KapTW Z.tw₂ ws.off κ
  t₃   : Z.R.X.run.KapTW Z.tw₃ ws.off κ
  link : Z.R.K.P.KapCW Z.R.Sl Z.R.ε₀ Z.R.ε₁ ws.lk κ
  tK   : Z.R.Kc.run.KapTW Z.twK ws.lk κ
  linB : Z.R.on.ol.toC.P.KapCBW Z.R.SnB Z.R.εfB Z.R.N ws.sh κ
  t₁B  : Z.R.TB₀.D₁.KapTW Z.tw₁B ws.sh κ
  t₂B  : Z.R.TB₀.D₂.KapTW Z.tw₂B ws.ins κ
  t₃B  : Z.R.XB.run.KapTW Z.tw₃B ws.ins κ

/-- The request's clauses with work. -/
structure LdReqKapW {Kc : Type} (w : ℕ) (κ : ℝ≥0∞) (R : LdORE F E Kc) {a : LdStage E Kc}
    (first : LdSendD a) {a₁ : LdStage E Kc} (more : LdProg first.tgt a₁) {b : LdStage E Kc}
    (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b) : Prop where
  bFirst : (ldSendFamErr first.N first.Sd first.L : ℝ≥0∞) ≤ κ * (Fintype.card first.Sd.D : ℝ≥0∞)
  bMore  : more.Below κ
  bSegs  : Ls.NumsW w κ
  bTail  : T.A.Nums κ
  bLast  : Err.Below (R.X.bt.nums R.Cf.conf.E0 Kc).err κ

/-- The five lists of bits. -/
def LdObjZ.bits (Z : LdObjZ F E) (ws : LdWk4) : Bits5 where
  wf     := List.replicate Z.R.Bw.link.R.shape.nAll 0
  linOff := linBits ws.off ++
    ((0 :: Z.R.TP₀.D₁.bitsT Z.tw₁ ws.off) ++
      ((0 :: Z.R.TP₀.D₂.bitsT Z.tw₂ ws.off) ++ ((0 :: Z.R.X.run.bitsT Z.tw₃ ws.off) ++ [])))
  link   := lkBits ws.lk ++ ((0 :: Z.R.Kc.run.bitsT Z.twK ws.lk) ++ [])
  req    := Z.R.r.bits ws.ins
  linOn  := linBits ws.sh ++
    ((0 :: Z.R.TB₀.D₁.bitsT Z.tw₁B ws.sh) ++
      ((0 :: Z.R.TB₀.D₂.bitsT Z.tw₂B ws.ins) ++ ((0 :: Z.R.XB.run.bitsT Z.tw₃B ws.ins) ++ [])))

end

namespace Spec

/-- States: under the hypotheses below, the object's five lists are at most κ round by round, with
these bits (`Z.bits ws`). -/
def ldKappaW : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Kc : Type) (p : ℕ)
      (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (ws : LdWk4),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ' → Z.KapW ws κ →
    LdReqKapW ws.ins κ R first more Ls T → Z.R.toP.toT.obj.nums.BelowB (Z.bits ws) κ

/-- States, under the hypotheses below (those of `Spec.ldKappaW`), of the work vectors with these
bits: each has the five lists at most κ, work counted; there is one; none of its bits exceeds
`ws.top`. -/
def ldKappaW_work : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Kc : Type) (p : ℕ)
      (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (ws : LdWk4),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ' →
    Z.KapW ws κ → LdReqKapW ws.ins κ R first more Ls T →
    (∀ g : Z.R.toP.toT.obj.subs.Bits, g.Is (Z.bits ws) → Z.R.toP.toT.obj.nums.BelowG g κ) ∧
    (∃ g : Z.R.toP.toT.obj.subs.Bits, g.Is (Z.bits ws)) ∧
    ∀ g : Z.R.toP.toT.obj.subs.Bits, g.Is (Z.bits ws) →
      g.wf.AllLe ws.top ∧ g.linOff.AllLe ws.top ∧ g.link.AllLe ws.top ∧
      g.req.AllLe ws.top ∧ g.linOn.AllLe ws.top

end Spec
end Cb
