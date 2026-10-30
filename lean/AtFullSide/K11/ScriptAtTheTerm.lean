-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/ScriptAtTheTerm.lean: the proof of K11ScriptAtTheTerm (E2E/K11AtTheTerm.lean): what the
kind asks of the script holds at the joined list of all three senders, at the base prover.

  k11ScriptAtTheTerm   the statement

Limits. Those of the statement.
-/
import E2E.K11AtTheTerm
import AtFullSide.K11.AtTheTerm
import AtFullSide.K11.TiesAtJoinUnderHead
import AtFullSide.K2.JoinFitFull
import Johnson.Desc.ProofFile.Honest.K11.Plays.CellsOfIndex
import Johnson.Desc.ProofFile.Honest.Thread.JoinAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.HonestTrace (Sz)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA F0T CellsM TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (PlaceIn k1MembersW mem_k1MembersW mem_k1Members)
open ProofFile.Honest.K2 (withSwitchData switchShareAt)
open ProofFile.Honest.K2.Law (joinFit_full publicOk_of_two digits_light_at_head share_msgs_mem)
open ProofFile.Honest.K11
open AtPublicFiles.AtFiles.HonestTerm.K11Term

/-- **The first of the kind's two facts on the script, at K1's members as a list of jobs.** -/
theorem k11_script_under_head {W₀ Xi Y : Type} {I : WiderIn W₀} {Z : VerifierAndGoals.PublicFiles} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    {Bs : ProofFile.PureBase} (hM : baseMaker I Z = .ok A)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (front : Nat)
    (mat : W₀ → CellsM OnBytes.Flat.numsFull) (tok : Input W₀ → P5J.At.Tok)
    (wit : Input W₀ → PlaceIn Xi) (own₀ : Y) (jobs : List (Nat × ProofFile.Honest.K1.SendJob (PlaceIn Xi) Y))
    (J₂ : ProofFile.Honest.K1.SendJob (PlaceIn Xi) Y) (Jl : ℕ → Bool → ProofFile.Honest.K1.SendJob (PlaceIn Xi) Y)
    (Jw : ProofFile.Honest.K1.SendJob (PlaceIn Xi) Y) (hjobs : jobs = k1MembersW J₂ Jl Jw)
    (readers : Input W₀ → Readers) (rest : Nat → TreeLot A.B (Input W₀))
    (O' Oth : Others A.B (Input W₀))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder front Zp Bs.G₀
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest).add O')
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : Input W₀ → Prop) (Rd : Nat → Input W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Input W₀)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf Zp Bs.G₀).lay))
    (seats : List (Nat × Nat))
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs Oth)
    (hP : J₂.P = VerifiableInference.Desc.K1.firstPar Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Zp))
    (hR : J₂.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (hD : ∀ v, Vd v → ProofFile.Honest.K2.Law.ReadsLight Zp Bs.G₀ v.x) :
    K11ScriptMsg
      (lettersHead h A.H (joinQ cF.blocksInOrder front (fun v => mat v.w₀) tok (P5J.At.arr Zp) wit own₀ jobs Oth)
        test carryX item n₁ n₂ 339 Vd Rd Kp w).thread
      SaidOk 346 (_root_.K11.parOf Zp Bs.G₀)
      (headMergeCoins
        (lettersHead h A.H (joinQ cF.blocksInOrder front (fun v => mat v.w₀) tok (P5J.At.arr Zp) wit own₀ jobs Oth)
          test carryX item n₁ n₂ 339 Vd Rd Kp w).thread
        (_root_.K11.parOf Zp Bs.G₀) (headClaimsAt cF Zp Bs.G₀) (I.weights Zp) IM.k11Place c₀)
      id id
      (dataAtHead h (joinQ cF.blocksInOrder front (fun v => mat v.w₀) tok (P5J.At.arr Zp) wit own₀ jobs Oth)
        carryX) 24 := by
  subst hjobs
  subst hO
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  have hf := k11_found h hM hb
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x Bs' h hb] at hf
  obtain ⟨p, hp, hl⟩ := place24_at_head h O
  have hJ : (2, J₂) ∈ k1MembersW J₂ Jl Jw := mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inl rfl)))
  refine k11_scriptMsg_at_join h A.H front (fun v => mat v.w₀) tok wit own₀ (k1MembersW J₂ Jl Jw) _ test
    carryX item n₁ n₂ 339 Vd Rd Kp w _ (I.weights Zp) c₀ hb (book_at_atPure h hM) hf hJ hP hR ?_
    (List.mem_append.2 (Or.inl (share_msgs_mem 0 _ _ readers _ _ _ _ _ _ _ rest hp _
      (senderLot_mem h O hp hl 0 _ readers _ _)))) ?_
    (k11MaskLot_covered_at_zero h O hb (book_at_atPure h hM) Unit _ _ _ readers _ hp hl _ 0 _
      fun v hv => publicOk_of_two h O (digits_light_at_head h O) (hD v hv) p hp)
  · exact F.msgs _ (List.mem_append.2 (Or.inl (openingLot_mem_list h O front wit own₀ J₂ hP _ hJ)))
  · exact F.msgs _ (List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inl (share_msgs_mem 0 _ _ readers
      _ _ _ _ _ _ _ rest hp _ (senderLot_mem h O hp hl 0 _ readers _ _))))))

set_option maxHeartbeats 1000000 in
/-- **What the kind asks of the script holds at the joined list.** -/
theorem k11ScriptAtTheTerm : K11ScriptAtTheTerm := by
  intro W₀ I Z D r Zp Np cF x A Bs Xi Y X₂ hM hb h front mat tok wit own₀ no Dt Dd readers rest ch
    Jt own₂ n₀ ok codes sh sh₁ rest₂ test carryX item n₁ n₂ ν st R f w Vd c₀ hJ hV hD hm
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hb)
  have F := joinFit_full (X := Y) h O hM no Dt Dd front wit own₀
    (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs'.G₀) readers rest ch Jt hJ own₂ n₀ ok codes sh
    sh₁ rest₂
  refine ⟨?_, ?_⟩
  · have hj := byNo_at_head (X := Y) h O no Dt Dd
    exact k11_script_under_head hM hb h front mat tok wit own₀ _ _ _ _ hj
      readers rest _ _ rfl test carryX item n₁ n₂ Vd _ _ w c₀ _ F rfl rfl hD
  · exact cellsOfIndex A.B W₀ IndexCommitterCoins Cells _ _ _ _ fun v hv => hm v.w₀ (hV v hv)

end AtFullSide.K11

#print axioms AtFullSide.K11.k11ScriptAtTheTerm
