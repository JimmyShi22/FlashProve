-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesGather.lean: THE SEVEN KINDS THAT ARE PAID, GATHERED: FirstOwed (OwesByKind.lean) at the first thread at
the Script firstScriptAt, from what is left of it.

  `RestOwed`          what is left: the kinds K2 and K10
  `digitsStand_kept`  the field hσ
  `next_of_behind`, `stands_of_behind`  the fields hnx, hs: both are clauses of the riders that the lookup's BehindS at 345 gives
  `first_owed_base`   FirstOwed from RestOwed: all else by its theorem
  `owes_one_base`     OwesS at the walk from the first stand, by owes_one

Limits. A joining at the base filling, at Sz.ref and openHonest, under the head. live and every field of RestOwed are premises. The
seven kinds' own limits stand: what they pay is that the sender plays and the exchange where they are asked, not that a step
accepts. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesCalled
import Johnson.AtFull.Shape.Scope.OwesK7
import Johnson.AtFull.Shape.Scope.OwesK3
import Johnson.AtFull.Shape.Scope.OwesK4
import Johnson.AtFull.Shape.Scope.OwesK5
import Johnson.AtFull.Shape.Scope.OwesOne
import Johnson.AtFull.Shape.Scope.OwesK9
import Johnson.AtFull.Shape.Scope.OwesK13
import Johnson.AtFull.Shape.Scope.OwesK1
import Johnson.AtFull.Shape.Scope.OwesRest
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open VerifiableInference.Desc (KindName)
open P5J (parts4)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **What is left of the first thread's debt.** -/
structure RestOwed (h : HeadAtReturn files A) (numbers : FallNumbers)
    (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (Bs : ProofFile.PureBase) : Prop where
  k2 : KindPaid (baseLetters h numbers w) Said KindName.K2
  k10 : KindPaid (baseLetters h numbers w) Said KindName.K10

/-- **What the lookup on the digits heard stands past what the merge's member keeps.** -/
theorem digitsStand_kept {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {Zp : ProofFile.Pub} {s s' : P5J.TS}
    (hK : Johnson.Desc.First.ForkMerge.Returns.K11Keeps P s s') :
    digitsStand Zp 24 s → digitsStand Zp 24 s' := fun hd _ p hp => by
  obtain ⟨htl, -, hF⟩ := Johnson.Desc.First.ForkMerge.Returns.headMergeKeepsSeat P s s' hK
  refine ProofFile.Honest.K3.Law.AtThr.standsHere_later ?_ ?_ (hd rfl p hp)
  · simp only [ProofFile.Honest.K3.Law.seatOf, if_true, VerifiableInference.Desc.K3.seatDigits, htl]
  · intro F hF'
    obtain ⟨F', e, hL, -⟩ := hF F hF'
    exact ⟨F', e, hL⟩

/-- The lookup on the digits of the head's link stands at 345. -/
theorem border_digits_head : VerifiableInference.Desc.Sound.MgAt.borderOf 24 true = 345 := by decide

section
variable (h : HeadAtReturn files A) (parts : FirstThreadParts A)
  (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
  (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)

/-- What the lookup's behind lays at 345: the clause on the next free slot. -/
theorem next_of_behind (hB : BehindS (firstThread h parts w) Said 345) :
    LaysAtS (firstThread h parts w) Said 345
      (riderHead 346 346 fun a => a.F.next = nextSlotBehindTheHead) :=
  fun blk hblk k s m E ds y cols s' hT hd hS =>
    (hB blk hblk k s m E ds y cols s' hT hd hS).2.1.2 _
      ((csHead_mem _ _ _ _).2 (.inl (.inl (.inl (.inr (.inr (.inr (.inl rfl))))))))
      (by show 346 ≤ 346; omega) (by show 346 ≤ 346; omega)

/-- What the lookup's behind lays at 345: the clause on what stands. -/
theorem stands_of_behind (hB : BehindS (firstThread h parts w) Said 345) :
    LaysAtS (firstThread h parts w) Said 345 ⟨346, 347, fun _ _ s => digitsStand A.Z 24 s⟩ :=
  fun blk hblk k s m E ds y cols s' hT hd hS =>
    (hB blk hblk k s m E ds y cols s' hT hd hS).2.1.2 _
      ((csHead_mem _ _ _ _).2
        (.inl (.inl (.inl (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))))))
      (by show 346 ≤ 346; omega) (by show 346 ≤ 347; omega)
end

/-- **FirstOwed from what is left.** -/
theorem first_owed_base (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (numbers : FallNumbers) (w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
    (Said : Nat → Coins A.B → Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (R : RestOwed h numbers w Said Bs) :
    FirstOwed h ⟨ProofFile.Honest.K1.firstScriptAt ProofFile.Honest.Term.matrixInput OnBytes.HonestTrace.Sz.ref
      openHonest A h.firstChain, numbers⟩ w Said Bs :=
  have hB345 : BehindS (firstThread h ⟨ProofFile.Honest.K1.firstScriptAt ProofFile.Honest.Term.matrixInput
      OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain, numbers⟩ w) Said 345 :=
    border_digits_head ▸ (AtPublicFiles.Lookup.lookupPaysAllFiveAtTheFirstThreadAtTheFirstScript made h _ rfl
      (AtFullSide.K2.Term.closing_at_return h.head made) w Said hS (fun _ _ _ => none) 24
      (by omega) true).behind
  {
  k1 := k1_paid made h _ rfl w Said hS
  k2 := R.k2
  k3 := K3_paid_at_script made h numbers w Said hS
  k4 := K4_paid h made numbers w Said
  k5 := K5_paid h made numbers w Said
  k6 := k6_paid_base made h numbers w Said
  k7 := k7_paid_first h.head.scope h.head.reads live made h _ rfl w Said hB
  k8 := k8_paid_base made h numbers w Said hS
  k9 := k9_paid ProofFile.Honest.Term.matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest made h _ w Said hS
  k10 := R.k10
  k11 := k11_paid_base made h numbers w Said hS
  k12 := playsS_of _ _ (ProofFile.Honest.K12.LotL.closingTestPlays_at_firstThread_paid
    (I := ProofFile.Honest.Term.matrixInput) (Op := openHonest) h made numbers w)
  k13 := k13_paid_base made h _ rfl w Said
  hσ := fun _ _ hK => digitsStand_kept hK
  noHalf := no_frame_at_base ProofFile.Honest.Term.matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest made
  hno := hno_at_base ProofFile.Honest.Term.matrixInput OnBytes.HonestTrace.Sz.ref openHonest made
  hhalf := ⟨_, Johnson.AtFull.Shape.k7_find ProofFile.Honest.Term.matrixInput OnBytes.HonestTrace.Sz.ref openHonest h made hB⟩
  htst := ProofFile.Honest.K9.step_silent_first h numbers
  hnx := next_of_behind h _ w Said hB345
  hs := stands_of_behind h _ w Said hB345
  hstl := hstl_at h _ w Said
  hatt := hatt_at h _ w Said hB }

/-- **owes₁ at the first Script, from what is left.** -/
theorem owes_one_base (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (numbers : FallNumbers) (Rd : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (R : RestOwed h numbers Rd.own (FirstWalk h ⟨ProofFile.Honest.K1.firstScriptAt
      ProofFile.Honest.Term.matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain, numbers⟩ Rd) Bs) :
    OwesS (firstThread h ⟨ProofFile.Honest.K1.firstScriptAt ProofFile.Honest.Term.matrixInput
        OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain, numbers⟩ Rd.own)
      (FirstWalk h ⟨ProofFile.Honest.K1.firstScriptAt ProofFile.Honest.Term.matrixInput
        OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain, numbers⟩ Rd) :=
  owes_one h _ Rd hB (first_owed_base made h numbers Rd.own _
    (fun b k m hs => saidOk_of_walk _ b k m hs) live hB R)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.first_owed_base
#print axioms Johnson.AtFull.Shape.Scope.owes_one_base
