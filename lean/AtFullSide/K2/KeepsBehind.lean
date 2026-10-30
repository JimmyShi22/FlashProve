-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KeepsBehind.lean: the debt «behind» at a code switch (the kind K2), at the first chain's
letters with the list csHead and the family fHeadJ.

  k2_pile_kept     PileKept behind a yes
  k2_arm           the kind's arm of fHead
  k2_behindS       BehindS: the form, the riders and the kind's clause of fHeadJ

Limits. The library's head is a premise. Nothing here says that the member accepts.
-/
import AtFullSide.K2.KeepsCore
import AtFullSide.K2.FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Block Chain KindName Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Desc.First.Walk.Seat (framesOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **PileKept behind a yes of a member of the kind.** -/
theorem k2_pile_kept (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) {blk : Block TS ProofFile.Cl}
    (hblk : cF.blocksInOrder[b]? = some blk) {z : ProofFile.InstPub} {s s' : TS} (hyes : IM.Yes 0 blk s s')
    (hreach : Johnson.Desc.First.Walk.Tied.Reach 0
      (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) b (z, s))
    (hx : IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (P1K2.EQ (P5J.mgAtAll h) P5J.At.links P5J.At.ps z) b s = true) :
    PileKept s s' :=
  k2_pile_parts h ha hk hblk hyes hreach hx

/-- **The kind's arm of fHead.** -/
theorem k2_arm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2)
    {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[b]? = some blk) {s s' : TS}
    (hyes : IM.Yes 0 blk s s') :
    fHead Zp cF G take P11 p12 P13 KindName.K2 blk.place s s' := by
  rcases k2_keeps_core h ha hk hblk hyes with
    ⟨l, fs, f, m, el, hne, hfs, hff, hq, e⟩ | ⟨el, hq⟩ | ⟨el, hq⟩
  · exact (fHead_K2_link Zp cF G take P11 p12 P13 el hne s s').2
      ⟨m, hq, keepsOpenedR_of hfs hff (P1K2.leaveOpened_is e) (P1K2.leaveOpened_none e).2⟩
  · exact (fHead_K2_head Zp cF G take P11 p12 P13 el s s').2 hq
  · exact (fHead_K2_finish Zp cF G take P11 p12 P13 el s s').2 hq

/-- **The debt «behind» at a member of the kind.** Said: a letter, read through hOk. -/
theorem k2_behindS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) :
    BehindS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b := by
  intro blk hblk k s m E ds y cols s' hT _ hS
  have hT₀ : ThrS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread SaidOk b k s m E :=
    ⟨hT.1, hOk _ _ _ hT.2⟩
  have hblk' : cF.blocksInOrder[b]? = some blk := hblk
  have hForm := k2_form_behind h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w ha hk hblk' hT₀ hS
  have hThr := hT.1
  unfold Thr at hThr
  obtain ⟨-, -, hF, -, -, hR, -⟩ := hThr
  have hlen : b ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk').1
  have hyes : IM.Yes 0 blk s s' := ⟨roundsOf y.1, cols, cols.length, hS.2⟩
  have hreach := thrS_reach_below h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hlen hT₀
  have hx := xk_of_form (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w) hF
  have hp := head_place h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hblk
  have epl : pl = blk.place := Option.some.inj (ha.symm.trans hp)
  have hkb : blk.place.kind = KindName.K2 := epl ▸ hk
  -- the input stays
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hForm, ⟨fun hb => ?_, ?_⟩, ?_⟩
  · have hR₁ := head_reply h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w (k2_border_at ha hk hb) hR
    rw [ei, k2_reply_kept h ha hk hblk' hyes]
    exact hR₁
  · exact k2_riders_behind ν st R ha hk _ s'
  · refine (head_keeps_kind h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD) w hblk hkb s s').2 ?_
    exact ⟨⟨⟨⟨⟨k2_arm h G take P11 p12 P13 ha hk hblk' hyes,
      formsBehind_of_form h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp hForm⟩, trivial⟩,
      k2_pile_kept h ha hk hblk' hyes hreach hx⟩, trivial⟩, trivial⟩

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.k2_pile_kept
#print axioms AtFullSide.K2.Term.k2_arm
#print axioms AtFullSide.K2.Term.k2_behindS
