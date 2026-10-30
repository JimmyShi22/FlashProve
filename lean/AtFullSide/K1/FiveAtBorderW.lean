-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtBorderW.lean: the shared sending (kind K1): the five statements in the form FiveAtBorderJ at number
356 of the first chain, the sending of the message W, at the base prover of the online proof.

  1  sendW_noVals, vals_w   the table's cell at 356 has no test on values
  2  k1_fiveJ_w             FiveAtBorderJ at 356, at lettersHead with firstScriptAt
  3  k1_fiveJ_w_first       the same at firstThread h parts w (Honest/Thread/TheFirstThread.lean)

A join of laws that lie: playsS_k1_base (PlaysAtBase.lean), k1_w_behindS_head, k1_w_ridesPastS_head
(Honest/K1/Law/FiveAtWHead.lean), k1_w_exchangeS (Honest/K1/Law/FiveAtW.lean), k13_pileOneS_at_356
(Honest/K13/PileOneAt356.lean), debtsJ_at, side_of_seated (Johnson/AtFull/Shape/K1DebtsJ.lean, K1DebtsAll.lean).

Limits.
  * hWrow is a hypothesis: the share of the exchange at the item wrow at 356. It is the kind K13's
    (k13_wrowS_at_356, Honest/K13/WRowAt356.lean, gives it under WitnessHasW). hWrow_first (WrowAtFirst.lean) pays
    it where Op.pile is pileAnyK3, as the honest prover's is. It speaks of values.
  * hyes is a hypothesis: the run on shapes returns over the 358 members. It is proved at no public files here.
    The fields accepted and next rest on it; they are asked with J in hand. That J begins at the chain's start
    and is carried is not shown here. At a fall that always speaks they are idle.
  * The head, the return hA and, at the first thread, hQ are hypotheses.
  * Each field stands under the thread's invariant in front of the member. At an input that does not meet the
    thread's valid all six fields are idle.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtFirst
import Johnson.Desc.ProofFile.Honest.K1.Law.FiveAtWHead
import Johnson.Desc.ProofFile.Honest.K13.PileOneAt356

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape

theorem sendW_noVals (Z : ProofFile.Pub) : (Tab.sendW Z).2 = noVals := by
  unfold Tab.sendW
  split <;> rfl

/-- **The cell's test at number 356.** -/
theorem vals_w (Z : ProofFile.Pub) (G : ProofFile.Ground) : Tab.vals Z G 356 = noVals := by
  unfold Tab.vals Tab.cells
  rw [show (356 : Nat) = 353 + 3 from rfl, table_back]
  exact sendW_noVals Z

end Johnson.AtFull.Shape

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

/-- **The five statements at number 356, at the base prover.** -/
theorem k1_fiveJ_w (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : LocB W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (w : LocB W₀) (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {a₀ : ShA}
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true)
    (hWrow : ExchangeAtS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339
      Vd (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12
        (VerifiableInference.Desc.K13.whereOf A.Z) h.𝔇.pubD)) w).thread Said 356 .wrow) :
    FiveAtBorderJ (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12
        (VerifiableInference.Desc.K13.whereOf A.Z) h.𝔇.pubD)) w).thread Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall 356 := by
  obtain ⟨-, -, ⟨bw, Rw⟩⟩ := k1Seated_first h hA test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12
      (VerifiableInference.Desc.K13.whereOf A.Z) h.𝔇.pubD)) w
  have dJ := debtsJ_at h hB _ Said fall rfl hyes (by decide : 356 < 358) (side_of_seated Rw)
    (valuesJ_of_noVals _ Said _ fall A.Z Bs.G₀ (vals_w A.Z Bs.G₀))
  exact ⟨(playsS_k1_base h hA test carryX item n₁ n₂ 339 Vd _ _ w Said).2.2,
    k1_w_behindS_head h A.H _ test carryX item n₁ n₂ Vd ν st R G take P11 p12 w Said,
    k1_w_exchangeS h A.H _ test carryX item n₁ n₂ 339 Vd _ _ w Rw Said
      (K13.k13_pileOneS_at_356 h A.H _ test carryX item n₁ n₂ 339 Vd _ _ w Said) hWrow,
    k1_w_ridesPastS_head h A.H _ test carryX item n₁ n₂ Vd ν st R G take P11 p12 w Said,
    dJ.1, dJ.2⟩

/-- **The five statements at number 356, at the first thread.** -/
theorem k1_fiveJ_w_first {files : VerifierAndGoals.PublicFiles}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true)
    (hWrow : ExchangeAtS (firstThread h parts w) Said 356 .wrow) :
    FiveAtBorderJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
      356 := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  have e := seatGround_of_base hB
  obtain ⟨script, numbers⟩ := parts
  dsimp only at hQ
  subst hQ
  rw [e] at hyes
  have key := k1_fiveJ_w h.head hA hB _ _ _ _ _ _ _ _ _ (seatGround A) _ _ _ w Said fall hyes hWrow
  rw [← e] at key
  exact key

end ProofFile.Honest.K1

#print axioms Johnson.AtFull.Shape.vals_w
#print axioms ProofFile.Honest.K1.k1_fiveJ_w
#print axioms ProofFile.Honest.K1.k1_fiveJ_w_first
