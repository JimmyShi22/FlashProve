-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean (the test tabIsEXB is the linear one of
Law/TabIsEXCode.lean, with its law in Law/TabIsEX.lean): THE FIELD
head_cuts ("the output head's four parts together give the head's half of the model's relation in
plain integers": Johnson/P5J/MeansQ.lean: HeadCuts) AT THE COMPOSED MEANING's CONSTANT
(Johnson/P5J/MgAtAll.lean: AtMgA, its structure of parameters h.𝔇): AND WHAT THE CONSTANT's
headPart READS OF THE VERIFIER's STATE AND OF THE STRINGS. Statements and proofs: each proof is one
call of K6's law at the constant's terms.

  headCuts_atAll   MAIN: HeadCuts (ppAtFiles Z.pol Z.KL) putReq h.𝔇.H h.𝔇.headPart: one call of
                   Law/HeadCutsWords.lean's headCuts_k6_words. The head h pays: the scope, the
                   reading of the public files, the public parameters (AtMg.scope | reads | pubOne);
                   SeatsNamed and GroupsSeated (PlanOk.hN | hG). In scope: the kind's tests on the
                   plan (Goal/Meaning/HeadCondScope.lean: ok_in_scope); the sizes fit; one seat for
                   one label. By evaluation: the committed table's numbers of rows and columns.
  headPart_atAll_blind   of the strings nothing; of the state the heard reply's token, at the part
                   lookCallsHeard alone: an equation: one call of Law/HeadCutsK6.lean's
                   headPartK6_blind; the request is read off the public instance (by rfl).
  headPart_atAll_reply   so where the reply is as it was.

THAT LEAN TAKES THE CALLS SHOWS: the constant's H and headPart bear ONE seat term; oneDec turns a
field that headPartK6 does not read; At.put is putReq.
WHAT IT IS NOT. An implication. TWO NAMED PREMISES BESIDE THE HEAD: htab: A TEST WITH CODE THAT HAS
RUN NOWHERE · hpads: P5J.PadsFree at the constant's terms (its payer: K6's cheap test on the
pads; not called here). THE HEAD ITSELF IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.P5J.MgAtAll
import Johnson.Desc.Kinds.Law.HeadCutsWords
import Johnson.Desc.Kinds.Law.HeadPartsGoBack
import Johnson.Goal.Meaning.HeadCondScope
import Johnson.Desc.Kinds.Law.TabIsEX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain Strs)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **"HEAD CUTS" AT THE COMPOSED MEANING's CONSTANT.** -/
theorem headCuts_atAll (h : AtMgA o Z D r Zp Np cF x)
    (htab : tabIsEXB (P5J.At.tabH x) = true)
    (hpads : P5J.PadsFree (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
      (Meaning.sizesOf (P5J.At.X Zp))
      (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp)) (P5J.At.X Zp)) :
    P5J.HeadCuts (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) OnBytes.Flat.putReq h.𝔇.H
      h.𝔇.headPart :=
  Came.headCuts_k6_words (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
    (Meaning.sizesOf (P5J.At.X Zp)) (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp))
    (P5J.At.X Zp) (plAt (P5J.At.num Zp 24 0) 0) h.scope h.reads h.pubOne (by decide) (by decide)
    (P5J.At.tabH x) OnBytes.Flat.putReq P5J.tokVOf _ _ h.plan.hN h.plan.hG P5J.tokHOf
    (InScope.ok_in_scope h.scope h.reads h.pubOne _) (tab_of_B htab)
    (P5J.sizesFit_sizesOf h.scope h.reads h.pubOne)
    (Meaning.seatsOne_of_planFit (Meaning.fLay (P5J.At.layout Zp) (P5J.At.num Zp))
      (Meaning.planFit_of_core h.pubOne (OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne)))
    hpads

/-- **WHAT THE CONSTANT's headPart READS OF THE VERIFIER's STATE AND OF THE STRINGS**: of the
strings nothing; of the state the heard reply's token, at the part lookCallsHeard alone. (The
request is read off the public instance z.) -/
theorem headPart_atAll_blind (h : AtMgA o Z D r Zp Np cF x) (p : P5J.TPart)
    (i : VerifiableInference.Desc.Sound.IdxQ) (z : ProofFile.InstPub) (s t : TS) (y y' : Strs)
    (w : VerifiableInference.Desc.Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      VerifiableInference.Desc.Sound.MsgT)
    (ht : p = .lookCallsHeard → P5J.tokHOf (z, t) = P5J.tokHOf (z, s)) :
    h.𝔇.headPart p i (z, t) y' w = h.𝔇.headPart p i (z, s) y w :=
  Came.headPartK6_blind (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
    (Meaning.sizesOf (P5J.At.X Zp)) (seatLay (P5J.At.X Zp) (P5J.At.layout Zp) (P5J.At.num Zp))
    (P5J.At.X Zp) (plAt (P5J.At.num Zp 24 0) 0) (P5J.At.tabH x) P5J.At.put _ P5J.tokHOf p i (z, s)
    (z, t) y y' w rfl ht

/-- So where the reply is as it was. -/
theorem headPart_atAll_reply (h : AtMgA o Z D r Zp Np cF x) (p : P5J.TPart)
    (i : VerifiableInference.Desc.Sound.IdxQ) (z : ProofFile.InstPub) (s t : TS) (y y' : Strs)
    (w : VerifiableInference.Desc.Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      VerifiableInference.Desc.Sound.MsgT) (hr : t.out.reply = s.out.reply) :
    h.𝔇.headPart p i (z, t) y' w = h.𝔇.headPart p i (z, s) y w :=
  headPart_atAll_blind h p i z s t y y' w fun _ => by
    show P5J.tokVOf ((t.out.reply.bind _).getD 0) = P5J.tokVOf ((s.out.reply.bind _).getD 0)
    rw [hr]

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headPart_atAll_reply
#print axioms VerifiableInference.Desc.Kinds.Head.Law.headCuts_atAll
