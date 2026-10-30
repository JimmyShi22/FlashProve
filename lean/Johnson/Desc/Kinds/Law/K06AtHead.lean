-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06AtHead.lean: THE SHARE OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, AT THE
SECOND HASH FUNCTION (o := OnBytes.secondHashFunction), UNDER THE HEAD AtMgA (MgAtAll.lean), AtMgR (AtMgR.lean),
AND NINE NAMED FIELDS: of the one condition K6Cond (K06AtConst.lean) all else is proved here by
calls.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  state_at_head: K6StateMg (Law/K6DueSplit.lean: nine fields) at piece6 := 4, at every Lk that is
      the chain's segment 24, at every "reached" that gives bare RchAt at border 341.
  cond_at_head: THERE IS Lk WITH K6Cond h ‹the frame› 4 Lk Rch Lp ‹the closed list of the messages'
      shapes› (h.row L).
  k06_kind_head: the kind's share at bare "reached": AtMgA → AtMgR at RchAt → K6LeftMg's nine →
      h.Kind (dAt h) L K6.

BY CALLS OF: Law/K6StateAtHead.lean (k6_reach_at_head · k6_bare_at_head ·
k6_start_at_head · link24_at_head · six_of_link_at_head: over K6's files under Johnson/P4R/,
six_at_seat (Johnson/P4SR/SixClosed.lean) and the opening of the description's value, IM.Open) and
Law/K6SeatedAtHead.lean (seated_at_head) · Law/RowLenAtConst.lean (atRow_in: the
first chain has 358 sub-protocols) · Law/K06Kind.lean (cond_of_row).
WHAT IS LEFT IN FRONT: q₁ q₂ q₃ (L's three lists are the IOP's own) · AtMgR (of its facts on every
reached state six are spent, at border 341) · K6LeftMg: planC, seatsC, namedC, callsC, maskC, book,
fenceT (tests with code on public data) · numbers (two equations on public numbers) · tokSmall (on
the state in front: what is heard as the reply is an entry of the vocabulary).
What it does not say. THAT THESE CAN BE MET: NO EXAMPLE. Nothing at another function for the second
hash function. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K06Kind
import Johnson.Desc.Kinds.Law.K6StateAtHead
import Johnson.Desc.Kinds.Law.K6SeatedAtHead
import Johnson.Desc.Kinds.Law.RowLenAtConst

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

/-- **The nine fields on reached states and on the chain's segment 24.** -/
theorem state_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x) (Fr : Sound.Frame)
    (Lk : Link S Claim) (hl : cF.links[24]? = some Lk)
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a) :
    K6StateMg (dAt h) Sound.mgBase Fr 4 Lk Rch := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := P4.six_of_link_at_head h hl
  exact
    { runs3 := a1
      reach := fun a hr hm => P4.k6_reach_at_head h a (hRch a hr) hm
      back3 := a2
      back2 := a4
      start := fun a _ hr hm => P4.k6_start_at_head h a (hRch a hr) hm
      runsObj := a5
      back := a6
      bare := fun a _ hr hm => P4.k6_bare_at_head h a (hRch a hr) hm
      runs2 := a3 }

/-- **THE ONE CONDITION, AT THE HEAD.** -/
theorem cond_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Rch : ℕ → (ProofFile.InstPub × S) × (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
            (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str → Prop)
    (hRch : ∀ a, Rch 341 a → RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 341 a)
    (Lp : K12.Door.Laid) (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF Rch (fun a => a.1) Lp)
    (hleft : K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) x Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    ∃ Lk : Link S Claim, K6Cond h
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) 4 Lk Rch Lp (K12.Door.msgsOfChain Zp.made.proof.1)
      (h.toAtMg.row L) := by
  obtain ⟨Lk, hl⟩ := P4.link24_at_head h
  refine ⟨Lk, cond_of_row h L q₁ q₂ q₃ (atRow_in h.toAtMg 341 (by decide)) 4 Lk Rch Lp hF hl
    (state_at_head h (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a)
      (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a)) (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) Lk hl
          Rch
      hRch) (fun q hq => ?_) hleft⟩
  obtain ⟨bef, B, bS, Hs⟩ := seated_at_head h L q₁ q₂ q₃ q hq
  exact ⟨bef, bS, B, Hs⟩

/-- **The kind's share at bare "reached".** -/
theorem k06_kind_head (h : P5J.AtMgA OnBytes.secondHashFunction Z Dw r Zp Np cF x)
    (L : P5J.Free numsFull Dw (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (Lp : K12.Door.Laid)
    (hF : P5J.AtMgR OnBytes.secondHashFunction Z Dw r Zp Np cF
      (RchAt (Str := (Sound.EAll (Dw.at OnBytes.Slice.frS.P.T.a)
      (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))).Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) (fun a
                      => a.1) Lp)
    (hleft : K6LeftMg (dAt h) Sound.mgBase (P5J.At.layout Zp) (P5J.At.num Zp)
      (Sound.frameAt (Dw.at OnBytes.Slice.frS.P.T.a) (Sound.allOf (Dw.at OnBytes.Slice.frS.P.T.a))
        (Dw.at OnBytes.Slice.frS.P.T.a).key₁ 0) x (RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) Lp
            (K12.Door.msgsOfChain Zp.made.proof.1)
      (cF.blocksInOrder.map (Sound.held (P := ProofFile.InstPub)))) :
    h.toAtMg.Kind (dAt h) L .K6 := by
  obtain ⟨Lk, C⟩ := cond_at_head h L q₁ q₂ q₃ _ (fun _ hr => hr) Lp hF hleft
  exact k06_kind h L 4 Lk Lp _ C

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.state_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.cond_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_kind_head
