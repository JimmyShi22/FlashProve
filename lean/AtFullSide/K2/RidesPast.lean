-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/RidesPast.lean: the debt «rides past» at a code switch (the kind K2), at the first
chain's letters with the list csHead and the family fHeadJ. An item that is open at the switch and
that its row neither shuts nor owes passes over it.

  k2_keeps_facts      the kind's arm of fHead gives SmpStay, no mark behind, and in the head's
                      segment what goes out stays
  ridesPastAt_heard   the part lookCallsHeard passes over a member that leaves the heard token: it
                      reads of the state nothing else, and of the strings nothing
  k2_ridesPastS       RidesPastS, item by item over the sorts of RidesSorts.lean

Limits. The library's head is a premise. Nothing here says that any item holds at any state.
-/
import AtFullSide.K2.KeepsCore
import AtFullSide.K2.RidesSorts
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ
import Johnson.Desc.ProofFile.Honest.Thread.PinForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Goal.HonestTrace.ConstrAtThread
import Johnson.P5J.ConstrBackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Chain KindName Place Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2.Law (k2_place_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The kind's arm of fHead gives SmpStay and no mark behind**, at each sort of place, and in the
head's segment what goes out stays. -/
theorem k2_keeps_facts (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) {p : Place} {s s' : TS}
    (hf : fHead Zp cF G take P11 p12 P13 KindName.K2 p s s') :
    SmpStay s.st s'.st ∧ s'.failed = none ∧ (p.link = some 24 → s'.out = s.out) := by
  cases hl : p.link with
  | none =>
    obtain ⟨q, hq, k⟩ := (fHead_K2_finish Zp cF G take P11 p12 P13 hl s s').1 hf
    have c := k.common
    obtain ⟨-, k2⟩ := k
    rw [hq] at k2
    exact ⟨c.2.2.2.2.2, k2.2, fun _ => c.2.1⟩
  | some l =>
    by_cases e : l = 24
    · rw [e] at hl
      obtain ⟨q, hq, k⟩ := (fHead_K2_head Zp cF G take P11 p12 P13 hl s s').1 hf
      have c := k.common
      obtain ⟨-, k2⟩ := k
      rw [hq] at k2
      exact ⟨c.2.2.2.2.2, k2.2, fun _ => c.2.1⟩
    · obtain ⟨m, ⟨q, -, k⟩, ko⟩ := (fHead_K2_link Zp cF G take P11 p12 P13 hl e s s').1 hf
      refine ⟨?_, ko.1.1, fun h24 => ?_⟩
      · rw [keepsOpened_st ko.1]
        exact k.common.2.2.2.2.2
      · exact absurd (Option.some.inj h24) e

/-- What goes out gives the heard token. -/
theorem heard_of_out {s s' : TS} (e : s'.out = s.out) : s'.heardTok? = s.heardTok? := by
  rw [← P5J.replyTok_is_heardTok, ← P5J.replyTok_is_heardTok]
  unfold VerifiableInference.Desc.First.S.replyTok?
  rw [e]

/-- The public part and the heard token are the same. -/
def sameHeard : ProofFile.InstPub × TS → Strs → ProofFile.InstPub × TS → Strs → Prop :=
  fun a _ c _ => a.1 = c.1 ∧ a.2.heardTok? = c.2.heardTok?

set_option maxHeartbeats 2000000 in
/-- At a constant decoder the part lookCallsHeard goes back over sameHeard. -/
theorem heard_goes_back (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (c : CellsM OnBytes.Flat.numsFull) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (m : Nat) :
    VerifiableInference.Desc.Sound.GoesBack sameHeard
      ((VerifiableInference.Desc.Sound.mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX }
        VerifiableInference.Desc.Sound.mgBase).constr m .lookCallsHeard) := by
  rw [VerifiableInference.Desc.Sound.mgAll_constr]
  exact VerifiableInference.Desc.Sound.constrQAt_back_any _ _ _ _ _ m .lookCallsHeard (by decide)
    sameHeard (fun a _ b _ hr => P5J.req_public_at h a b hr.1) (fun _ _ _ _ _ => rfl)
    (fun i => VerifiableInference.Desc.Kinds.Head.Law.headPartK6_goesBack _ _ _ _ _ _ _ _ _ _ _ _
      sameHeard (fun a _ b _ hr => P5J.req_public_at h a b hr.1) .lookCallsHeard
      (fun _ _ _ _ _ hr => P5J.tokH_same hr.2) i)

set_option maxHeartbeats 2000000 in
/-- **The part lookCallsHeard passes over a member that leaves the heard token.** Of the state its
sentence reads that token and nothing else, of the strings nothing, since at the thread the decoder
is a constant. -/
theorem ridesPastAt_heard (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) (b m : Nat)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.heardTok? = s.heardTok?) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b
      (Item.constr m .lookCallsHeard) := by
  intro k s mm E s' ps v _ hK h0
  exact heard_goes_back h (Q.cells mm.st.input) carryX m
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k mm s')
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps))
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.seat k mm s)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    v ⟨rfl, hk s s' hK⟩ h0

/-- **The debt «rides past» at a member of the kind.** -/
theorem k2_ridesPastS (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said b := by
  have hb358 : b < 358 := by
    rcases P1K2.k2_spots b pl ha hk with ⟨l, -, h24, e⟩ | e | e <;> omega
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  have hfacts : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.keeps
      b s s' → SmpStay s.st s'.st ∧ s'.failed = none ∧ (pl.link = some 24 → s'.out = s.out) := by
    intro s s' hK
    have a : fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD pl.kind pl s s' :=
      (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
        (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w ha s s').1 hK
    have a1 : fHead Zp cF G take P11 p12 P13 pl.kind pl s s' := a.1.1.1.1.1
    rw [hk] at a1
    exact k2_keeps_facts G take P11 p12 P13 a1
  refine ridesPastS_shares _ _ fun i h1 h2 h3 => ?_
  obtain ⟨p, hpW, eb⟩ := k2_place_at ha hk
  have h1' : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (ProofFile.Honest.K2.Law.switchNo p) := by
    rw [← eb]
    exact h1
  have h2' : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (ProofFile.Honest.K2.Law.switchNo p)).shuts := by
    rw [← eb]
    exact h2
  have h3' : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (ProofFile.Honest.K2.Law.switchNo p)).owes := by
    rw [← eb]
    exact h3
  rcases k2_open_cases hpW h1' h2' h3' with e | e | e | e | ⟨m, q, hq, e⟩ | ⟨h339, m, e⟩ <;> rw [e]
  · exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
      fun s s' hK => (hfacts s s' hK).2.1)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b)
  · exact cellJ_of_I h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w G take P11
      p12 P13 Said (cellI_of_H h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) w G
        take P11 p12 P13 Said (cellH_pile h H Q test carryX item n₁ n₂ 339 Vd
          (ridersOf (csHead ν st R)) w G take P11 p12 P13 Said hb358 ha (Or.inl hk)))
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
      fun _ s _ _ s' hA hK _ _ hr => rowAt₀_smpStay (hfacts s s' hK).1
        (head_tidy h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
          (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hlen hA).noneYet hr)
  · exact ridesPastAtS_of _ _ (OnBytes.HonestTrace.ridesPastAt_constr h H Q test carryX item n₁ n₂
      339 Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b m hq)
  · have e339 : b = 339 := eb.trans h339
    have el : pl.link = some 24 := by
      have t := k2_head_link
      rw [← e339, ha] at t
      exact Option.some.inj t
    exact ridesPastAtS_of _ _ (ridesPastAt_heard h H Q test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w b m
      fun s s' hK => heard_of_out ((hfacts s s' hK).2.2 el))

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.k2_keeps_facts
#print axioms AtFullSide.K2.Term.heard_of_out
#print axioms AtFullSide.K2.Term.heard_goes_back
#print axioms AtFullSide.K2.Term.ridesPastAt_heard
#print axioms AtFullSide.K2.Term.k2_ridesPastS
