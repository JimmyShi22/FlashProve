-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FiveAtBorderReads.lean: the shared sending (kind K1): the five statements in the form FiveAtBorderJ
at the 25 members "reads" (K1.noL l false) of the first chain, at the base prover of the online proof.

  1  exchangeS_reads_base   ExchangeS, whole, at K1.noL l false, from the share at the item tie l
  2  k1_fiveJ_reads         FiveAtBorderJ there, at lettersHead with firstScriptAt
  3  k1_fiveJ_reads_first   the same at firstThread h parts w (Honest/Thread/TheFirstThread.lean)

At such a member the row owes pin l 1, a sample row, tie l, the forms, and again pin l 0 and constr l small
where they are open in front (owed_reads, OwedAtMembers.lean, by the kernel). A join of laws that lie:
exchange_pin, exchange_rows_fifty_tied, exchangeAtS_forms_of_tie (as in k1_shares_reads, SharesAtMembers.lean),
exchangeAtS_pin0_reads, exchangeAtS_constr_reads (AgainAtReads.lean), playsS_k1_base, k1_behindS_fifty,
k1_ridesPastS_fifty_I, k1_debtsJ_at, side_of_seated.

Limits.
  * hTie is a hypothesis: the share of the exchange at the item tie l. It speaks of values: at parameters I, S,
    Op other than the honest prover's it need not be meetable. The forms' shares are drawn from it.
  * hSaid is a hypothesis: the condition Said gives SaidOk.
  * hyes is a hypothesis: the run on shapes returns over the 358 members. It is proved at no public files here.
    The fields accepted and next rest on it; they are asked with J in hand. That J begins at the chain's start
    and is carried is not shown here. At a fall that always speaks they are idle.
  * The head, the return hA and, at the first thread, hQ are hypotheses.
  * Each field stands under the thread's invariant in front of the member. At an input that does not meet the
    thread's valid all six fields are idle.
  * For the honest run's own forms alone: SharesAtMembers.lean imports twins at the honest meaning. Never on
    soundness's road.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.FiveAtFirst
import Johnson.Desc.ProofFile.Honest.K1.Law.AgainAtReads

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

/-- **ExchangeS at each of the 25 members "reads", from the share at tie l.** -/
theorem exchangeS_reads_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : LocB W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) {l : ℕ} (hl : l < 25)
    (hTie : ExchangeAtS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (K1.noL l false) (.tie l)) :
    ExchangeS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (K1.noL l false) := by
  obtain ⟨-, RL, -⟩ := k1Seated_first h hA test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w
  obtain ⟨bl, Rl⟩ := RL l hl false
  refine (exchangeS_iff _ Said).2 fun j hj => ?_
  rcases owed_reads hl hj with (rfl | rfl | rfl | ⟨y, hy, rfl⟩) | ⟨hc, -⟩
  · exact exchange_pin Rl Said l 1 rfl
  · exact exchange_rows_fifty_tied h A.H _ test carryX item n₁ n₂ 339 Vd _ _ w hl false Rl Said
  · exact hTie
  · exact exchangeAtS_forms_of_tie h A.H _ test carryX item n₁ n₂ 339 Vd _ _ w Said hSaid hl hy hTie
  · rcases hc with rfl | rfl
    · exact exchangeAtS_pin0_reads h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl
    · exact exchangeAtS_constr_reads h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl

/-- **The five statements at each of the 25 members "reads", at the base prover.** -/
theorem k1_fiveJ_reads (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ : Nat) (Vd : LocB W₀ → Prop) (ν : Nat) (st : Nat → TS → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {a₀ : ShA}
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true)
    {l : ℕ} (hl : l < 25)
    (hTie : ExchangeAtS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (K1.noL l false) (.tie l)) :
    FiveAtBorderJ (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ 339 Vd
      (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall (K1.noL l false) := by
  obtain ⟨-, RL, -⟩ := k1Seated_first h hA test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy (fHeadJ A.Z cF G take P11 p12 P13 h.𝔇.pubD)) w
  obtain ⟨bl, Rl⟩ := RL l hl false
  have dJ := k1_debtsJ_at h hB _ Said fall rfl rfl (fun _ v _ _ hb => ⟨v.x.pub, hb⟩) hyes
    (Or.inr ⟨l, false, hl, rfl⟩) (side_of_seated Rl)
  exact ⟨(playsS_k1_base h hA test carryX item n₁ n₂ 339 Vd _ _ w Said).2.1 l hl false,
    k1_behindS_fifty h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl false,
    exchangeS_reads_base h hA test carryX item n₁ n₂ Vd ν st R G take P11 p12 P13 w Said hSaid hl
      hTie,
    k1_ridesPastS_fifty_I h A.H _ test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said 339 _ hl
      false,
    dJ.1, dJ.2⟩

/-- **The five statements at each of the 25 members "reads", at the first thread.** -/
theorem k1_fiveJ_reads_first {files : VerifierAndGoals.PublicFiles}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (hQ : parts.script = firstScriptAt I S Op A h.firstChain) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))).yes startShA 358 =
      true) {l : ℕ} (hl : l < 25)
    (hTie : ExchangeAtS (firstThread h parts w) Said (K1.noL l false) (.tie l)) :
    FiveAtBorderJ (firstThread h parts w) Said
      (shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA) fall
      (K1.noL l false) := by
  obtain ⟨Bs, _, _, _, _, _, hB, -⟩ := reads_head_at h.head
  have e := seatGround_of_base hB
  obtain ⟨script, numbers⟩ := parts
  dsimp only at hQ
  subst hQ
  rw [e] at hyes
  have key := k1_fiveJ_reads h.head hA hB _ _ _ _ _ _ _ _ _ (seatGround A) _ _ _ _ w Said hSaid fall
    hyes hl hTie
  rw [← e] at key
  exact key

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.exchangeS_reads_base
#print axioms ProofFile.Honest.K1.k1_fiveJ_reads
#print axioms ProofFile.Honest.K1.k1_fiveJ_reads_first
