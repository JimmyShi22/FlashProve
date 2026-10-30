-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06CountedCalls.lean: OVER THE PROOF FILE'S ENTRY TESTS (lawsAsk):
THE KIND K6 IN THE FORM IN WHICH A KIND'S LAW IS COUNTED (P5J.AtMgA.Kind h L K6),
UNDER THE HEAD AtMgA AND ONE NAMED TEST ON PUBLIC DATA: callsC. Of the two tests that
Law/K06CountedStart.lean leaves, startB is paid here, by a call.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  cond_at_head_one: there are Lp, Lk with K06AtConst.lean's K6Cond at them: GENERAL IN "REACHED"
      above bare RchAt.
  k6Cond_of_calls: P5J.AtMgA.K6Cond h L (Johnson/Goal/Skeleton/Kinds/K6Bridge.lean) holds.
  k06_counted_calls: h.Kind L K6.

BY A CALL OF P5J.startB_at_head (Johnson/P5J/StartAtHead.lean: under the head the
test startB accepts: off the two pins, the written values and closed facts by the kernel).
THE GROUND: as Law/K06AtHeadTwo.lean's: of the entry tests lawsAsk at least madeRow and cutRow.
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ (L's three lists are the IOP's own) · callsC: a test with code on
public data: each of the head's matrices that the lookup on the calls reads is a
member of the caller's list and sits as the table has it.
What it does not say. THAT THE HEAD OR THE TEST CAN BE MET: NO EXAMPLE. Nothing at another function
for the second hash function. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06CountedStart
import Johnson.P5J.StartAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : First.Look.Place}

/-- **K6Cond (Law/K06AtConst.lean), at the head, from the one test.** -/
theorem cond_at_head_one (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hR : ∀ k a, Rch k a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) k a)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    ∃ (Lp : K12.Door.Laid) (Lk : Link S Claim), K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_at_head_start h L q₁ q₂ q₃ Rch hR (P5J.startB_at_head h.toAtMg) callsC

/-- **The named condition P5J.AtMgA.K6Cond (K6Bridge.lean) holds.** -/
theorem k6Cond_of_calls (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.K6Cond L :=
  k6Cond_of_start h L q₁ q₂ q₃ (P5J.startB_at_head h.toAtMg) callsC

/-- **THE KIND, IN THE COUNTED FORM, FROM THE HEAD AND ONE TEST.** -/
theorem k06_counted_calls (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.Kind L KindName.K6 :=
  k06_counted_start h L q₁ q₂ q₃ (P5J.startB_at_head h.toAtMg) callsC

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_one
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6Cond_of_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_calls
