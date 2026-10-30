-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/AtFirstThread.lean: the five debts of the kind K11 at number 346 of the first thread
(Honest/Thread/TheFirstThread.lean), at every letter Said that gives SaidOk. Of K11Five's premises
the thread's own values pay these: the clause of keeps at the kind, both ways; what the head's lookup
establishes, past the merge; the two items of that lookup that ride past. What is left is what the
script says at this member.

  k11_clause_gives       the thread's clause at the kind gives the merge's clause
  k11_clause_of_step     behind the member's step the thread's clause holds
  k11_stand_stays        what the lookup on the digits heard stands past the merge's clause
  k11Five_at_firstThread the five debts

Limits. The script's two facts are premises here: K11ScriptAtTheTerm shows them at the joined list.
Nothing here says that the thread's sentence holds at any state.
-/
import AtFullSide.K11.AtTheTerm
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.FHeadJ
import Johnson.Desc.K11.Returns.KeepsSeat
import Johnson.Desc.K11.Returns.KeepsYes
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupWorthRidesPastTheHeadsMergeAtTheWrittenSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain KindName Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (carryExact)
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest
open ProofFile.Honest.SumLaw (SumCoins)
open ProofFile.Honest.K11
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K3.Law.AtThr (StandsHere standsHere_later)
open ProofFile.Honest.K3.Term (lookupWorthRidesPastTheHeadsMergeAtThePublicPlace)
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes headMergeKeepsSeat)

variable {W₀ : Type} {I : WiderIn W₀} {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- The thread's clause at the kind gives the merge's clause. -/
theorem k11_clause_gives (h : HeadAtReturn Z A) (s s' : TS)
    (hc : firstClauses h KindName.K11 IM.k11Place s s') :
    K11KeepsYes (_root_.K11.parOf A.Z (seatGround A)) s s' :=
  hc.1.1.1.1.1.2

/-- **What the lookup on the digits heard stands past the merge's clause.** -/
theorem k11_stand_stays {P : HeadMergeP} {s s' : TS} (hK : K11KeepsYes P s s') (first : Nat) :
    StandsHere true 5 first s → StandsHere true 5 first s' := by
  obtain ⟨htl, -, hF⟩ := headMergeKeepsSeat P s s' hK.1
  refine standsHere_later ?_ ?_
  · simp only [ProofFile.Honest.K3.Law.seatOf, if_true, VerifiableInference.Desc.K3.seatDigits, htl]
  · intro F hF'
    obtain ⟨F', e, hL, -⟩ := hF F hF'
    exact ⟨F', e, hL⟩

/-- **The five debts of the kind at number 346 of the first thread.** -/
theorem k11Five_at_firstThread (hM : baseMaker I Z = .ok A) (h : HeadAtReturn Z A)
    (parts : FirstThreadParts A) (w : Input W₀)
    (Said : Nat → Coins A.B → Mid (Input W₀) Unit → Prop) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (c₀ : SumCoins (runName maskRowRun ⟨headMergePlace (_root_.K11.parOf A.Z Bs.G₀), 1⟩ "sum")
      (runName indexMaskRun ⟨headMergePlace (_root_.K11.parOf A.Z Bs.G₀), 1⟩ "ends")
      (headMergeJob (_root_.K11.parOf A.Z Bs.G₀).lay))
    (hS : ∀ b k m, Said b k m → SaidOk b k m)
    (hSc : K11ScriptMsg (firstThread h parts w) SaidOk 346 (_root_.K11.parOf A.Z Bs.G₀)
      (headMergeCoins (firstThread h parts w) (_root_.K11.parOf A.Z Bs.G₀)
        (headClaimsAt h.firstChain A.Z Bs.G₀) (I.weights A.Z) IM.k11Place c₀)
      id id (dataAtHead h.head parts.script (carryExact A.Z (P5J.At.arr A.Z))) 24)
    (hC : K11CellsQ parts.script (_root_.K11.parOf A.Z Bs.G₀).lay (I.weights A.Z)
      (ReadyInput h.description A.H)) :
    PlaysS (firstThread h parts w) Said 346 ∧
      (∀ fall, AcceptedS (firstThread h parts w) Said fall 346) ∧
      BehindS (firstThread h parts w) Said 346 ∧
      ExchangeS (firstThread h parts w) Said 346 ∧
      RidesPastS (firstThread h parts w) Said 346 := by
  have eG : seatGround A = Bs.G₀ := seatGround_of_base hB
  have hf₁ : ∀ s s', firstClauses h KindName.K11 IM.k11Place s s' →
      K11KeepsYes (_root_.K11.parOf A.Z Bs.G₀) s s' := fun s s' hc => by
    have := k11_clause_gives h s s' hc
    rwa [eG] at this
  have hf₂ : ∀ blk k s m E ds y cols s',
      ThrS (firstThread h parts w) Said 346 k s m E →
      (firstThread h parts w).Stepped blk k s m E ds y cols s' →
      h.firstChain.blocksInOrder[346]? = some blk → K11KeepsYes (_root_.K11.parOf A.Z Bs.G₀) s s' →
      firstClauses h KindName.K11 IM.k11Place s s' := by
    intro blk k s m E ds y cols s' hT hSt hblk hK
    have hF := k11_form_behind h.head A.H parts.script
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
      (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w hblk
      ⟨hT.1, hS _ _ _ hT.2⟩ hSt
    have hfb : formsBehind h.head.𝔇.pubD IM.k11Place s' :=
      formsBehind_of_form h.head A.H parts.script
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
      (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w ps_k11
        (k := k) (m' := y.2) ⟨hF.1, hF.2⟩
    rw [← eG] at hK
    exact ⟨⟨⟨⟨⟨⟨rfl, hK⟩, hfb⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩
  have hst : ∀ s s', K11KeepsYes (_root_.K11.parOf A.Z Bs.G₀) s s' →
      digitsStand A.Z 24 s → digitsStand A.Z 24 s' :=
    fun s s' hK hd _ p hp => k11_stand_stays hK _ (hd rfl p hp)
  have hkeep : ∀ s s', (firstThread h parts w).keeps 346 s s' →
      s'.tl? = s.tl? ∧ ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ _root_.Fo.Later F F' := by
    intro s s' hK
    have hc := hf₁ s s' ((head_keeps h.head A.H parts.script
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
      (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w ps_k11
      s s').1 hK)
    obtain ⟨htl, -, hF⟩ := headMergeKeepsSeat _ s s' hc.1
    refine ⟨htl, fun F hF' => ?_⟩
    obtain ⟨F', e, hL, -⟩ := hF F hF'
    exact ⟨F', e, hL⟩
  have hrider : ∀ v s, (firstThread h parts w).rides 346 v s →
      ∀ p, VerifiableInference.Desc.First.Look.placeAt A.Z.p.X 24 true = some p →
        StandsHere true 5 p.first s := by
    intro v s hr p hp
    have hc : (⟨346, 347, fun _ _ s => digitsStand A.Z 24 s⟩ : RiderCl (Input W₀) TS) ∈
        csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z) :=
      (csHead_mem _ _ _ _).2
        (.inl (.inl (.inl (.inr (.inr (.inr (.inr (.inr (.inr rfl)))))))))
    exact hr.2 _ hc (by show 346 ≤ 346; omega) (by show 346 ≤ 347; omega) rfl p hp
  exact k11Five W₀ I Z _ _ A.Z h.places h.firstChain h.look A Bs hM hB h.head parts.script _ _ 0 _ _
    _ nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z) (firstClauses h) w Said c₀ hS
    hSc hC hf₁ hf₂ hst
    (lookupWorthRidesPastTheHeadsMergeAtThePublicPlace h.head A.H parts.script
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
      (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w
      Said hkeep hrider (.inl rfl))
    (lookupWorthRidesPastTheHeadsMergeAtThePublicPlace h.head A.H parts.script
      (fallsAfterBatching (firstFalls A parts.numbers) h.firstChain)
      (carryExact A.Z (P5J.At.arr A.Z)) 0 h.description.t₁ h.description.t₂ 339
      (ReadyInput h.description A.H)
      (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
      (kpBy (firstClauses h)) w
      Said hkeep hrider (.inr rfl))
    346 IM.k11Place ps_k11 rfl

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_clause_gives
#print axioms AtFullSide.K11.k11_stand_stays
#print axioms AtFullSide.K11.k11Five_at_firstThread
