-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Top/ProofLaidOfDesc.lean: the maker of the proof file's laid description
(`FlashProve.theProofLaid`, Johnson/Goal/Description/ProofFold.lean) returns, from the return of the
description itself and facts on it.

Why. The test `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) asks that three makers return at the
public files. This file is a step toward "it says yes at `VerifierAndGoals.storedPublicFiles`"
(Johnson/AtFull/Top/LiveAtZFull.lean).

Main name.
* `proofLaid_of_desc`: at public files Z in the goals' scope: from the two makers' returns with the
  written parts, the return of `ProofFile.onlineDescription` at the description FW
  (Johnson/AtFull/Top/ProofLaidOfMade.lean), and facts on FW and on the public part, the maker
  returns the written data and the run of FW. What it asks is what
  Johnson/AtFull/Top/ProofLaidOfLedgers.lean names, with the one premise "`onlineDescription` returns FW" in
  the place of that file's seven on the steps of `onlineDescription`'s text, which serve for that return
  alone. Joins that end in the return of `onlineDescription`
  (Johnson/Desc/ProofFile/Law/Skel/Full/FirstRows.lean) fit this form.

How. From hX, hm, hF and e1 the lemmas of Johnson/AtFull/Pub/ give the public part's return and
three of the facts that the entry tests ask. That the description's plans and depth are the written
ones holds by definition: `fileDescBy` lays them from `ZqM`. The written declaration passes its test
by the closed `written_proof` (Johnson/AtFull/ProofRows/WrittenProof.lean). The fourteenth entry
test follows from e1, ha and K by `rowsMadeB_of_three` (Johnson/AtFull/Top/RowFourteenThree.lean).
The proof that the planner's sizes and first plan are the written ones stands a second time in a
working file of this project, which is not in this repository (sha256
a113f722e45f1aa5e8ce851c1d7884799b1103e9a9620b58ce2500c5552bd934).

Limits.
* AN IMPLICATION. None of its premises is shown in this file. That the premises of
  `proofLaid_of_desc` can be met together is shown at storedPublicFiles alone: `proofLaid_zFull`
  (Johnson/AtFull/Top/LiveAtZFull.lean), under two closed facts on the layout file whose proofs lie
  in the side library. No example of the head is shown in this file; two, at storedPublicFiles and at zGap
  alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are
  worth.
* e1 asks more than the sizes and the proof file's three plans, which are what is used of it beside
  the sendings: the key file's three plans and the copy's file's plan too.
* Over the fourteen entry tests that the maker asks (`lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean) as
  they stand.
* At the second hash function (`OnBytes.secondHashFunction`) and at a constant in the digest's place.
* A return of this maker is no sign that the verifier accepts anything. Nothing on soundness.

-/
import Johnson.AtFull.Top.ProofLaidOfMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open VerifiableInference.Desc.First.Att.P (K5Asks.rowW)
open Johnson.AtFull.Pub (DW)

/-- **The proof file's maker returns, from the return of its description** in the place of the seven
steps of that description's text. -/
theorem proofLaid_of_desc {Z : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {m : Made}
    {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}
    (hZ : VerifierAndGoals.InScope Z = true)
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : MadeFree.freeOf m.p.chains.made = writtenMade)
    (hDesc : onlineDescription OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c))
    (hW : (P2Law.ProofPlan.wOf cutFirstFull cutSharedFull cutSecondFull DW 32).planOk = true)
    (hC : cutIs (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c) = true)
    (hD : (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).roundsDeclaredByBlocks = DW)
    (b₁ : ∀ b ∈ (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).first.blocksInOrder, b.planOk = true)
    (b₂ : ∀ b ∈ (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).shared.blocksInOrder, b.planOk = true)
    (b₃ : ∀ b ∈ (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).second.blocksInOrder, b.planOk = true)
    (hFo : (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).fileOk = true)
    (att : ∀ k < 7, K5Asks.rowW k X₀ = true)
    (m₄ : xShapeOf X₀ = xShapeFull)
    (k₁ : Desc.K3Asks.digEntry (ZqM Z.pol Z.KL m) = true)
    (k₂ : Desc.K3Asks.readsEntry (ZqM Z.pol Z.KL m) = true)
    (k₃ : Desc.K3Asks.headEntry (ZqM Z.pol Z.KL m) = true)
    (ha : VerifiableInference.Desc.LinkJoin.armsB X₀ = true)
    (K : VerifiableInference.Desc.LinkJoin.rowsWB = true) :
    FlashProve.theProofLaid (VerifierAndGoals.asDescriptionFiles Z) =
      .ok (writtenPFull, LPFD.Full.proofDecisionOfDescription (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c)) := by
  have hx : m.p.X = X₀ := VerifiableInference.Desc.Key.madeAt_public hm
  have hz : m.p.chains.made.sized = writtenSized := congrArg (·.sized) e1
  have hpl : m.p.chains.made.proof =
      [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] := congrArg (·.proof) e1
  have hs : m.proof = proofSendsFull := proof_of_free hm e1
  have row14 : VerifiableInference.Desc.LinkJoin.rowsMadeB (ZqM Z.pol Z.KL m) = true :=
    rowsMadeB_of_three (Z := ZqM Z.pol Z.KL m) e1 (show _ from hx.symm ▸ ha) K
  have m₁ : MadeWritten m.p.chains.made := by
    refine ⟨?_, ?_⟩
    · rw [hz]
      rfl
    · rw [hpl]
      rfl
  have p₁ : pubPlain OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok (ZqM Z.pol Z.KL m) :=
    Johnson.AtFull.Pub.pubPlain_of_made hX hm hF hz hpl hs
  have hw : writtenOf "proof file" (FW OnBytes.secondHashFunction Z.pol Z.KL m A B c).roundsDeclaredByBlocks =
      .ok dryProofFull := by
    rw [hD]
    exact Johnson.AtFull.ProofRows.written_proof
  have m₄' : xShapeOf m.p.X = xShapeFull := by
    rw [hx]
    exact m₄
  show LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL = _
  unfold LPFD.Full.proofDataAndDecisionOfPublicFiles
  rw [hDesc]
  exact Johnson.AtFull.ProofRows.Fourteen.laid_of_rows hZ
    (P2Law.ProofPlan.planWord_of_cut hW hC hD rfl rfl b₁ b₂ b₃ hFo) hX p₁ hw rfl att m₁ hF hs m₄'
    (cutIs_eq hC).1 (cutIs_eq hC).2.1 (cutIs_eq hC).2.2 k₁ k₂ k₃ row14

end AtFull.Top

#print axioms AtFull.Top.proofLaid_of_desc
