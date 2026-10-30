-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/ProofLaidWhole.lean: the maker of the proof file's laid description
(`FlashProve.theProofLaid`) returns at `VerifierAndGoals.storedPublicFiles`, under two closed facts on the layout file,
the planner's return and four facts on the lookups (the kind K3).

Why. See Johnson/AtFull/Top/LiveAtZFull.lean. This file joins what pays the premises of
`proofLaid_of_desc` (Johnson/AtFull/Top/ProofLaidOfDesc.lean).

Main name.
* `proofLaid_zFull_at`: at a public part X₀ and a planner's answer m. The description's return, its
  first chain's cut, rounds and tests: `spine_zFull`, `first_of_skel`
  (Johnson/AtFull/Top/Spine.lean). The two later chains and the file's own test: `later_zFull`,
  `open_of_later` (Johnson/AtFull/Later/). The written plan's test: `hW_DW`
  (Johnson/AtFull/Later/PlanAtWritten.lean). Attention's seven entry tests: `att_zFull`
  (Johnson/AtFull/Entry/AttAtX0.lean). The fourteenth entry test: `rowsWB_true`
  (Johnson/AtFull/Rows/Rows.lean). The public part's arms and shape: `x_facts_at`
  (Johnson/AtFull/Top/ProofLaidAtFull.lean).

What stays a premise.
* hsz, bL: the layout file's size, and what `layoutRead` returns on it. Both are closed facts on a
  stored text.
* hX, hm, hF, e1: the two makers' returns, and that the planner's answer has the written parts.
* RX: what the lookups' lot reads of X₀ is the written value (`ReadsX`,
  Johnson/AtFull/Desc/Lots/K3RowX.lean).
* k₁, k₂, k₃: the lookups' three entry tests accept (Johnson/Desc/First/Look/K3AsksDoor.lean).
All are paid in Johnson/AtFull/Top/LiveAtZFull.lean but hsz and bL.

Limits.
* Over the fourteen entry tests that the maker asks as they stand.
* At the second hash function (`OnBytes.secondHashFunction`) and at a constant in the digest's place.
* Much beneath rests on evaluations in Lean's kernel at written values; each file says which.
* `VerifierAndGoals.storedPublicFiles` is a term. No Lean ties it to files in a folder of examples, and the example's
  weights are synthetic (Ladder/Stored.lean's head).
* A return of this maker is no sign that the verifier accepts anything. Nothing on soundness, on an
  honest prover or on hiding.

-/
import Johnson.AtFull.Top.Spine
import Johnson.AtFull.Top.ProofLaidOfDesc
import Johnson.AtFull.Top.ProofLaidAtFull
import Johnson.AtFull.Later.AtFull
import Johnson.AtFull.Later.Open
import Johnson.AtFull.Later.PlanAtWritten
import Johnson.AtFull.Rows.Rows
import Johnson.AtFull.Entry.AttAtX0
import Johnson.Second.Seam.CodesOneInScope
import Johnson.Road.K4.K4PlanTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number

/-- **The proof file's maker returns at `VerifierAndGoals.storedPublicFiles`**, at a public part X₀ and a planner's answer
m with their written parts, where what the lookups' lot reads of X₀ is the written value and the
lookups' three entry tests accept. The value: the written data and the description's run. -/
theorem proofLaid_zFull_at (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (bL : OnBytes.Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some Johnson.AtFull.LayoutRead.LW)
    {X₀ : OnBytes.Model.Verify.Public} {m : Made}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (e1 : MadeFree.freeOf m.p.chains.made = writtenMade)
    (RX : Johnson.AtFull.Lots.K3.ReadsX X₀)
    (k₁ : Desc.K3Asks.digEntry (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = true)
    (k₂ : Desc.K3Asks.readsEntry (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = true)
    (k₃ : Desc.K3Asks.headEntry (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) = true) :
    ∃ A B c, FlashProve.theProofLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) =
      .ok (writtenPFull,
        LPFD.Full.proofDecisionOfDescription (FW OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m A B c)) := by
  have hS := VerifierAndGoals.inScope_full
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have hZ := Johnson.AtFull.Entry.pubPlain_zFull hX hm hF e1
  obtain ⟨G, hG⟩ := LPFK9.blank_of_pub hS hR hZ
  have T := Johnson.AtFull.Entry.struck_zFull hsz hX hm hF e1 hG
  have hx : m.p.X = X₀ := VerifiableInference.Desc.Key.madeAt_public hm
  have R3 : Johnson.AtFull.Lots.K3.ReadsLeft (ZqM VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL m) :=
    Johnson.AtFull.Lots.K3.readsLeft_of (T.c13.trans Second.Seam.codes_written)
      (T.u1.symm.trans OnBytes.Road.K4.shape_one.symm) (show _ from hx.symm ▸ RX)
  obtain ⟨A, B, Lp⟩ := Johnson.AtFull.Later.later_zFull hsz bL hX hm
  obtain ⟨c, hD, hsk, d₁⟩ := spine_zFull hsz hX hm hF e1 Lp.r₆ Lp.r₇ R3
  obtain ⟨c₁, b₁⟩ := first_of_skel hsk
  obtain ⟨hC, hDd, b₂, b₃, hFo⟩ :=
    Johnson.AtFull.Later.open_of_later (o := OnBytes.secondHashFunction) Lp e1 c c₁ d₁
  exact ⟨A, B, c, proofLaid_of_desc hS hX hm hF e1 hD Johnson.AtFull.Later.hW_DW hC hDd b₁ b₂ b₃
    hFo (Johnson.AtFull.Entry.att_zFull hsz hX) (x_facts_at hsz hX).2 k₁ k₂ k₃
    (x_facts_at hsz hX).1 VerifiableInference.Desc.LinkJoin.rowsWB_true⟩

end AtFull.Top

#print axioms AtFull.Top.proofLaid_zFull_at
