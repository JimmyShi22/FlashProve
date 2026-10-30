-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtBase.lean: the shared sending (kind K1) at the base prover of the online proof: the five
statements of Honest/Thread/FiveAtBorder.lean, in the form FiveAtBorderJ, at 26 of the kind's 52 members of
the first chain: at number 2 (the opening) and at the 25 members "digits" (K1.noL l true).

  1  k1_fiveJ_two       FiveAtBorderJ at number 2
  2  k1_fiveJ_digits    FiveAtBorderJ at K1.noL l true, at each l below 25

The thread is lettersHead's at the base prover A.H, at the Script firstScriptAt (FirstScript.lean), at b₀ = 339,
the riders csHead and the clauses fHeadJ. TheFirstThread.lean's firstThread is meant to be an instance; no
theorem here says so. A join of laws
that lie; no new argument: playsS_k1_base (PlaysAtBase.lean), k1_behindS_two, k1_ridesPastS_two_I
(Honest/K1/Law/FiveAtTwo.lean), k1_behindS_fifty, k1_ridesPastS_fifty_I (BehindAtFifty.lean),
exchangeS_two_base, exchangeS_digits_base (ExchangeWhole.lean), k1_debtsJ_at, side_of_seated
(Johnson/AtFull/Shape/K1DebtsAll.lean).

Limits.
  * hyes is a hypothesis: the run on shapes returns over the 358 members. It is proved at no public files
    here. The fields accepted and next rest on it.
  * The fields accepted and next are asked with J in hand. Where J never holds at the border they say nothing.
    That J begins at the chain's start, and that it is carried, which needs NextJ at every member in front, of
    every kind, is not shown here. At an a₀ other than the start's shape (startShA) hyes may hold and J never
    begin. At a fall that always speaks, accepted and next are idle.
  * The head h, the return hA and hB (the public part's seat makes a base) are hypotheses. Under h such a base
    exists (reads_head_at, Johnson/AtFull/Shape/ReadsHeadAtHead.lean).
  * The other parameters of the thread are bound by "for all", with no hypothesis on them. At
    Vd := fun _ => False the thread's valid holds of nothing, and all six fields are idle.
  * Each field stands under the thread's invariant in front of the member. That the invariant holds there at
    a run needs the five statements at every member in front, of every kind.
  * The 25 members "reads" and number 356 are not here: ExchangeS is not whole there.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.PlaysAtBase
import AtFullSide.K1.ExchangeWhole
import Johnson.Desc.ProofFile.Honest.K1.Law.FiveAtTwo
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder
import Johnson.AtFull.Shape.K1DebtsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape

variable {Z : VerifierAndGoals.PublicFiles} {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **The five statements at number 2, at the base prover.** -/
theorem k1_fiveJ_two (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : LocB W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {a₀ : ShA}
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true) :
    FiveAtBorderJ (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall 2 := by
  obtain ⟨⟨b2, R2⟩, -, -⟩ := k1Seated_first h hA test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w
  have dJ := k1_debtsJ_at h hB _ Said fall rfl rfl (fun _ v _ _ hb => ⟨v.x.pub, hb⟩) hyes
    (Or.inl rfl) (side_of_seated R2)
  exact ⟨(playsS_k1_base h hA test carryX item n₁ n₂ 339 Vd _ _ w Said).1,
    k1_behindS_two h A.H _ test carryX item n₁ n₂ Vd w G take P11 p12 P13 Said,
    exchangeS_two_base h hA _ _ _ (othersApart_first h hA) test carryX item n₁ n₂ 339 Vd _ _ w Said,
    k1_ridesPastS_two_I h A.H _ test carryX item n₁ n₂ 339 Vd _ w G take P11 p12 P13 Said,
    dJ.1, dJ.2⟩

/-- **The five statements at each of the 25 members "digits", at the base prover.** -/
theorem k1_fiveJ_digits (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : LocB W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {a₀ : ShA}
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true)
    {l : ℕ} (hl : l < 25) :
    FiveAtBorderJ (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall (K1.noL l true) := by
  obtain ⟨-, RL, -⟩ := k1Seated_first h hA test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w
  obtain ⟨bl, Rl⟩ := RL l hl true
  have dJ := k1_debtsJ_at h hB _ Said fall rfl rfl (fun _ v _ _ hb => ⟨v.x.pub, hb⟩) hyes
    (Or.inr ⟨l, true, hl, rfl⟩) (side_of_seated Rl)
  exact ⟨(playsS_k1_base h hA test carryX item n₁ n₂ 339 Vd _ _ w Said).2.1 l hl true,
    k1_behindS_fifty h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl true,
    exchangeS_digits_base h hA _ _ _ (othersApart_first h hA) test carryX item n₁ n₂ 339 Vd _ _ w
      Said hl,
    k1_ridesPastS_fifty_I h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said 339 _ hl true,
    dJ.1, dJ.2⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1_fiveJ_two
#print axioms ProofFile.Honest.K1.k1_fiveJ_digits
