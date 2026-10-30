-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/AtBaseMaker.lean: the smallness test's debts at the named maker: at the first thread with
the written Script of the first chain, over the prover that baseMaker returns. The only premises left
are the maker's return, the head at it, and that what is said gives SaidOk where the law reads it.

  k8_behindS_baseMaker, k8_ridesPastS_baseMaker, k8_playsS_baseMaker   at a member of the kind
  k8_readyLaws_baseMaker    the law on the input at that return
  k8_exchange_baseMaker     the items that the draw's row owes and that are not open in front
  k8_exchangeS_baseMaker    ExchangeS whole, with the two pins

Limits. That the thread stands at any border at any run is not shown; that the maker returns and that a
head stands at its return are premises.
-/
import AtFullSide.K8.ExchangeAtFirst
import AtFullSide.K8.PlaysFirst
import AtFullSide.K8.AtFirstThread
import AtFullSide.K8.PinsAtDraw
import AtFullSide.K1.FirstScriptIsSenders
import E2E.BaseMaker
import Johnson.HonestTrace.Joint.JointMeetsD
import Johnson.HonestTrace.Joint.ReadsLightPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.HonestTrace (Sz)
open P5J (TS)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K8 ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open ProofFile.Honest.FirstThread

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- The first thread at the named maker. -/
noncomputable abbrev baseThread (hd : HeadAtReturn files A) (numbers : FallNumbers) (w : LocB FullSizeMatrix) :=
  firstThread hd ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩ w

/-- **The law on the input at the named maker's return.** -/
theorem k8_readyLaws_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A) :
    ReadyLaws hd.description A := fun v hv => by
  obtain ⟨i, x, -, -, hi, hs, ht, hm, hb, hn, hp, hk⟩ :=
    HonestTraceRun.Meets.laws_of_readyInput_over_matrices hd.head.scope hd.head.reads rfl hA hv
  exact ⟨i, x, hi, hs, ht, hm, hb, hn, hp, hk⟩

/-- **«Behind» at a member of the kind, at the named maker.** -/
theorem k8_behindS_baseMaker (hd : HeadAtReturn files A) (numbers : FallNumbers) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    BehindS (baseThread hd numbers w) Said b :=
  k8_behindS_first hd _ w Said ha hk

/-- **«Past» at a member of the kind, at the named maker.** -/
theorem k8_ridesPastS_baseMaker (hd : HeadAtReturn files A) (numbers : FallNumbers) (w : LocB FullSizeMatrix)
    (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    RidesPastS (baseThread hd numbers w) Said b :=
  k8_ridesPastS_first hd _ w Said ha hk

/-- **«Plays» at a member of the kind, at the named maker.** -/
theorem k8_playsS_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    PlaysS (baseThread hd numbers w) Said b :=
  k8_playsS_first matrixInput OnBytes.secondHashFunction Sz.ref openHonest hd hA _ w Said ha hk

/-- **The items that the draw's row owes, at the named maker.** -/
theorem k8_exchange_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) :
    ∀ b (p : Place), P5J.At.ps[b]? = some p → p.kind = KindName.K8 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((baseThread hd numbers w).row b).owes →
      (j ∈ (baseThread hd numbers w).opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧ ∀ m q, q ∈ P5J.parts4 → j ≠ .constr m q) →
      ExchangeAtS (baseThread hd numbers w) Said b j := by
  obtain ⟨Bs, base₀, O⟩ := hd.head.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground hd.head.laid O.blank hA
  have eS : seatGround A = Bs.G₀ := seatGround_of_base O.made
  obtain ⟨pl, hf, six, -⟩ := firstScript_written_head (I := matrixInput) (S := Sz.ref)
    (Op := openHonest) hd.head hA
  have eO := otherSenders_at_head (I := matrixInput) (S := Sz.ref) (Op := openHonest) hd.head hA
  obtain ⟨pl', hf', eO⟩ := eO
  obtain rfl : pl = pl' := Option.some.inj (hf.symm.trans hf')
  exact k8_exchange_first hd hA (k8_readyLaws_baseMaker hA hd) _
    (firstRecord matrixInput Sz.ref openHonest A hd.firstChain) (firstScript_is_record hd hA) rfl w
    Said hOk noTree 0 (testJobAt matrixInput Sz.ref A.Z A.G pl) six () _ testOk pl.sizes.codes _ _
    noTree (by rw [eS, ← eG]; exact eO) (hex_base matrixInput OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)
    (ho_base matrixInput OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G) (fun _ _ => rfl)
    (fun ξ hξ => by
      rw [eS]
      exact OnBytes.HonestTrace.U3.Fit.readsLight_of_okStart hd.head O hξ)

/-- What a draw's row owes, as four cases. -/
theorem owes_cases {l : Nat} (hl : l < 25) {j : VerifiableInference.Desc.First.Item}
    (hj : j ∈ (FirstRows.rows P5J.At.links P5J.At.ps
      (14 * l + (if l = 24 then 5 else 4) + 2)).owes) :
    (∃ n, j = .forms l n "small") ∨ j = .constr l .lookDigits ∨ j = .pin l 0 ∨ j = .pin l 1 := by
  rw [k8_owes_at hl] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with h | h | h | h
  · exact Or.inl ⟨_, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- **ExchangeS at a member of the kind, at the named maker.** -/
theorem k8_exchangeS_baseMaker (hA : baseMaker files = .ok A) (hd : HeadAtReturn files A)
    (numbers : FallNumbers) (w : LocB FullSizeMatrix) (Said : Nat → Coins A.B → Mid (LocB FullSizeMatrix) Unit → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    ExchangeS (baseThread hd numbers w) Said b := by
  rw [exchangeS_iff]
  intro j hj
  obtain ⟨l, hl₀, hb⟩ := k8_number ha hk
  have hl : l < 25 := by omega
  have hb' : b = 14 * l + (if l = 24 then 5 else 4) + 2 := by
    rw [hb, P1K8T.drawAt_place]
  subst hb'
  have hj0 := hj
  have hj1 := owes_cases hl hj
  obtain ⟨p0, p1⟩ := k8_exchangeAtS_pins_first hd
    ⟨firstScriptAt matrixInput Sz.ref openHonest A hd.firstChain, numbers⟩ w Said ha hk hl rfl
  rcases hj1 with ⟨n, rfl⟩ | rfl | rfl | rfl
  · exact k8_exchange_baseMaker hA hd numbers w Said hOk _ pl ha hk _ hj0
      fun _ => ⟨fun m t e => (by cases e), (by simp), (by simp), fun m q _ e => (by cases e)⟩
  · exact k8_exchange_baseMaker hA hd numbers w Said hOk _ pl ha hk _ hj0
      fun _ => ⟨fun m t e => (by cases e), (by simp), (by simp),
        fun m q hq e => (by cases e; exact absurd hq (by decide))⟩
  · exact p0
  · exact p1

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_readyLaws_baseMaker
#print axioms AtFullSide.K8.Term.k8_behindS_baseMaker
#print axioms AtFullSide.K8.Term.k8_ridesPastS_baseMaker
#print axioms AtFullSide.K8.Term.k8_playsS_baseMaker
#print axioms AtFullSide.K8.Term.k8_exchange_baseMaker
#print axioms AtFullSide.K8.Term.owes_cases
#print axioms AtFullSide.K8.Term.k8_exchangeS_baseMaker
