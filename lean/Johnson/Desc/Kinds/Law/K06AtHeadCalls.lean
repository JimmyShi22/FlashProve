-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtHeadCalls.lean: OVER THE PROOF FILE'S ENTRY TESTS (lawsAsk):
THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE SECOND HASH FUNCTION ITSELF, UNDER THE
HEAD AtMgA, AtMgR AND ONE NAMED TEST: callsC. Of the two that Law/K06AtHeadTwo.lean leaves,
maskC is paid here, by a call.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  cond_at_head_calls, k06_kind_head_calls: Law/K06AtHeadTwo.lean's cond_at_head_two and
      k06_kind_head_two with the one test in K6LeftTwo's place.

BY A CALL OF maskC_at_head (Johnson/HB/LLHARD/K6MaskAtHead.lean: no premise beside
the head; over the pins).
THE GROUND: as Law/K06AtHeadTwo.lean's: of the entry tests lawsAsk at least madeRow and cutRow.
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ · AtMgR (six of its facts on every reached state are spent, at
border 341, and its field listed) · callsC: a test with code on public data: each of the head's
matrices that the lookup on the calls reads is a member of the caller's list and sits as the table
has it.
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing at another function for the second
hash function. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtHeadTwo
import Johnson.HB.LLHARD.K6MaskAtHead

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

/-- **THE ONE CONDITION, AT THE HEAD, FROM THE ONE TEST.** -/
theorem cond_at_head_calls (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a)
    (Lp : K12.Door.Laid) (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    ∃ Lk : Link S Claim, K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) :=
  cond_at_head_two h L q₁ q₂ q₃ Rch hRch Lp hF ⟨callsC, maskC_at_head h⟩

/-- **The kind's share at bare "reached", from the one test.** -/
theorem k06_kind_head_calls (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF
      (RchAt (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
      (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) (fun a
                      => a.1) Lp)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.toAtMg.Kind (dAt h) L .K6 :=
  k06_kind_head_two h L q₁ q₂ q₃ Lp hF ⟨callsC, maskC_at_head h⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_calls
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_head_calls
