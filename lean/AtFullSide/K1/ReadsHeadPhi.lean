-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/ReadsHeadPhi.lean: vecTie_head (ReadsHeadAll.lean) WITH hPhi PAID by phi_sizes_head (Johnson/AtFull/Shape/PhiHead.lean): the state behind the member is reached.

  vecTie_head_paid   VecTie at 342 at a seat of segment 24's U3, at nReads, under h, hSaid, hG, hwit, the seat

This letter is for the honest run's own forms alone. NEVER ON SOUNDNESS's ROAD.
NO PROPERTY IS CLAIMED. -/
import AtFullSide.K1.ReadsHeadAll
import Johnson.AtFull.Shape.PhiHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open OnBytes.HonestTrace.U3 (u3Seats)
open OnBytes.Model (HTailF2)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **VecTie at the output head's reads, no premise on a stand.** -/
theorem vecTie_head_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst} (hwit : ∀ v, (wit v).x = v.x)
    {st : OnBytes.HonestTrace.Seat} (hst : st ∈ u3Seats Zp G) (hseg : st.seg = 24) :
    VecTie (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said 342 wit Zp G 24
      (nReads (P5J.At.X Zp) 24) st.addr := by
  refine vecTie_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hSaid hG hwit hst hseg ?_
  intro blk hb k s μ E ds y cols s' hT hd hS tl htl
  have hbl : 342 ≤ cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hb).1.le
  have hr := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT.1
  obtain ⟨hfit, -⟩ := Block.step_ok.1 hS.2
  exact Johnson.AtFull.Shape.Phi.phi_sizes_head h
    (Reach.succ hr hb ⟨roundsOf y.1, cols, roundsFit_len _ _ hfit, hS.2⟩) htl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.vecTie_head_paid
