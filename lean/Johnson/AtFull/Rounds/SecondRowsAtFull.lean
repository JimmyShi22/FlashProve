-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/SecondRowsAtFull.lean: THE JOIN OF THE FIFTEEN LOTS' SECOND ROWS AT THE STORED
FULL-SIZE PUBLIC FILES (`VerifierAndGoals.storedPublicFiles`): `second_rows_paid`
(Johnson/AtFull/Rounds/SecondRowsPaid.lean) with twelve premises for fifteen: five go and two come:
the scope and the reading of the files are the tree's own theorems at these files
(`VerifierAndGoals.inScope_full`, `VerifierAndGoals.filesRead.full`); K4's fifteen numbers (hn) and the attention's
plans' columns (hs) are conjuncts of `publicOfO_zFull_more` (Johnson/AtFull/Public/AtX0Shape.lean),
which brings (hsz); K12's premise (v12) comes from `H2K12.v12_of`
(Johnson/Loose/H2K12/K12HVOfWritten.lean), which brings (hp). Calls alone.

  **`second_rows_zFull`**: from (hsz) the stored layout file has 224975 bytes; (hZ) (hG) the two
    returns; the seven premises on the makers' returns (hX hm hF hz hpl u₃ u₄: u₃ at
    `declProofFull`); (hp) `m.proof = proofSendsFull`; (hB) `readsXB X₀ = true`:
  `∀ L ∈ onlineFirstChainBlockTables Z, RowL G L`.

Limits. A JOINING: ALL TWELVE ARE PREMISES: that they can be met together is not shown here. At the
stored full-size files and the second hash function `OnBytes.secondHashFunction` alone. The first chain alone.
Not an example of the head. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Rounds.SecondRowsPaid
import Johnson.AtFull.Public.AtX0Shape
import Johnson.Loose.H2K12.K12HVOfWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds

open OnBytes OnBytes.Model
open ProofFile (pubPlain blankBy pureRoad onlineFirstChainBlockTables toldOf Root)
open ProofFile.Law (blankM)
open ProofFile.Sk.Full (RowL)
open VerifiableInference.PlanWritten (publicOfO FirstWritten)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G (proofSendsFull)
open Johnson.G.OfPlan (Made declPOf)
open Johnson.AtFull.ProofRows (declProofFull)
open Johnson.AtFull.Lots.K3 (readsXB)
open Johnson.AtFull.Public (publicOfO_zFull_more)

variable {Z : ProofFile.Pub} {G : ProofFile.Ground} {X₀ : Verify.Public} {m : Made}
  {told : List Root × List Root × List Root}

/-- **The fifteen second rows at the stored full-size files**: under (hsz), the two returns, the
seven premises on the makers' returns, (hp) the proof file's sendings are the written ones, and
(hB). -/
theorem second_rows_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hZ : pubPlain OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL = .ok Z)
    (hG : blankBy pureRoad.links Z = some G)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀)
    (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    (hF : FirstWritten m.p.chains.proof.first)
    (hz : m.p.chains.made.sized = writtenSized)
    (hpl : m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (u₃ : declPOf (blankM m) = .ok declProofFull) (u₄ : toldOf (blankM m) = .ok told)
    (hp : m.proof = proofSendsFull)
    (hB : readsXB X₀ = true) :
    ∀ L ∈ onlineFirstChainBlockTables Z, RowL G L := by
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨X₁, hX₁, -, -, -, -, -, -, -, hn, hs⟩ := publicOfO_zFull_more hsz
  obtain rfl : X₁ = X₀ := Except.ok.inj (hX₁.symm.trans hX)
  exact second_rows_paid VerifierAndGoals.inScope_full hR hZ hG hX hm hF hz hpl u₃ u₄ hB hn hs
    (H2K12.v12_of hX hm hF hz hpl u₃ u₄ hZ hp)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.second_rows_zFull
