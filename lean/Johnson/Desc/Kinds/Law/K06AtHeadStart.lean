-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtHeadStart.lean: OVER THE PROOF FILE'S ENTRY TESTS (lawsAsk):
THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE SECOND HASH FUNCTION ITSELF, UNDER THE
HEAD AtMgA AND TWO NAMED TESTS ON PUBLIC DATA: startB AND callsC. The head with the facts on every
reached state (AtMgR), which Law/K06AtHeadCalls.lean leaves in front, is paid here,
by a call.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  cond_at_head_start: THERE ARE Lp, Lk WITH K6Cond h ‹the frame› 4 Lk Rch Lp ‹the closed list of the
      messages' shapes› (h.row L): GENERAL IN "REACHED" above bare RchAt.
  k06_kind_head_start: the kind's share at bare "reached".

BY A CALL OF P5J.atMgR_at_head (Johnson/P5J/AtMgRAtHead.lean: under the head and
startB there is a laid list L with AtMgR at every "reached" above bare RchAt; over other files'
join of the facts on reached states, and over the pins).
THE GROUND: as Law/K06AtHeadTwo.lean's: of the entry tests lawsAsk at least madeRow and cutRow.
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ (L's three lists are the IOP's own) · startB: a test with code on
the public part (AtMgR's own field start) · callsC: a test with code on public data
(AtFold.callsSeatedC, Law/K6CallsTest.lean).
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing at another function in the second
hash function's place. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06AtHeadCalls
import Johnson.P5J.AtMgRAtHead

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

/-- **THE ONE CONDITION, AT THE HEAD, FROM THE TWO TESTS.** -/
theorem cond_at_head_start (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hR : ∀ k a, Rch k a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) k a)
    (hs : First.FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    ∃ (Lp : K12.Door.Laid) (Lk : Link S Claim), K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) := by
  obtain ⟨Lp, hF⟩ := P5J.atMgR_at_head h hs Rch hR
  obtain ⟨Lk, C⟩ := cond_at_head_calls h L q₁ q₂ q₃ Rch (hR 341) Lp hF callsC
  exact ⟨Lp, Lk, C⟩

/-- **The kind's share at bare "reached", from the two tests.** -/
theorem k06_kind_head_start (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hs : First.FillP1.startB Zp (K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (callsC : AtFold.callsSeatedC (dAt h).arr (dAt h).ms (dAt h).N (P5J.At.X Zp) (P5J.At.layout Zp)
      (P5J.At.num Zp) (dAt h).sent (dAt h).l3.rad x.link ((dAt h).l3.seat x.link false) = true) :
    h.toAtMg.Kind (dAt h) L .K6 := by
  obtain ⟨Lp, Lk, C⟩ := cond_at_head_start h L q₁ q₂ q₃ _ (fun _ _ hr => hr) hs callsC
  exact k06_kind h L 4 Lk Lp _ C

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head_start
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_head_start
