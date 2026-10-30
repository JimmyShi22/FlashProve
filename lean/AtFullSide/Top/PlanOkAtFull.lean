-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Top/PlanOkAtFull.lean: the descriptions of the proof file and of the key file that are
made of the three full-size public files as Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`) pass
their own tests on the plan (`FileDescription.planOk`, Johnson/Desc/Block.lean). With no premise. A joining
of laws of the library at two theorems of this side library; no definition; nothing is evaluated
here.

Why. A sentence on what an honest prover's proof meets takes "the description passes its own tests
on the plan" as a public premise: it reads the public files alone: no input, no coin, no challenge.
The test `protocolDataWellFormed`, with which the verifier gates its three decisions, rejects unless both
descriptions pass these tests. So where `protocolDataWellFormed` accepts they pass; and it accepts at `storedPublicFiles`
(`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean).

Main names.
* `proofPlanOk_zFull`: there is F with `ProofFile.onlineDescription secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL = .ok F`,
  `F.planOk = true` and `F.placesOk = true` (each sub-protocol names its own chain and no two stand
  at one place: one of the tests that planOk gathers). F stands under "there is"; that it is the
  description whose run the verifier asks is the last clause:
  `theProofRun (asDescriptionFiles storedPublicFiles) = (F.pull instanceAsPlainRecord).run`. By `pseat_name`
  (Johnson/Goal/Description/ProofSeat.lean).
* `headPlanOk_zFull`: the same at the term and under the head at which the library's laws on the
  proof file's first chain speak (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): there are Zp, Np, cF, x
  with the head; the description is `P5J.F0T secondHashFunction Zp Np cF`; it passes planOk; and every
  sub-protocol of the first chain's flat list `cF.blocksInOrder` passes its own test on the plan and is
  shaped. By `headMember_zFull` (AtFullSide/Top/HeadMemberAtFull.lean).
* `keyPlanOk_zFull`: the key file's description passes planOk, wantedOk and owedOk, and its run is
  the one that the verifier asks. By `kseat_name` (Johnson/Goal/Description/KeySeat.lean).

Limits. At `VerifierAndGoals.storedPublicFiles` alone: three terms written in Ladder/Stored.lean: no Lean code ties them
to files in a folder of examples; the example's weights are synthetic. At the second hash function
`OnBytes.secondHashFunction`; BOTH DESCRIPTIONS AT A CONSTANT IN THE PLACE OF THE PUBLIC FILES' DIGEST
(`fixedConfigurationDigest`, Johnson/Desc/TheCfg.lean), not at the digest of these files. The tests on the plan are
tests of a description against itself and against the plan; they read nothing of what a
sub-protocol decides: THAT THEY PASS IS NO SIGN THAT THE VERIFIER ACCEPTS ANY PROOF, and none that
an honest prover's proof is accepted. No fact beside `theLive_zFull` and `headMember_zFull` is
shown: the three name what these two already hold, and have all their limits. It proves one public
premise of such a sentence and no other. It lies in a side library, built with a larger thread
stack, because these two do. Nothing on soundness, completeness, binding or hiding is shown here.

-/
import AtFullSide.Top.LiveAtFull
import AtFullSide.Top.HeadMemberAtFull
import Johnson.Goal.Description.ProofSeat
import Johnson.Goal.Description.KeySeat
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open VerifierAndGoals FlashProve
open VerifierAndGoals.AtTheName (dpZ)

/-- **The proof file's description at `storedPublicFiles` passes its tests on the plan.** No premise. -/
theorem proofPlanOk_zFull :
    ∃ F, ProofFile.onlineDescription OnBytes.secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL = .ok F ∧ F.planOk = true ∧
      F.placesOk = true ∧ theProofRun (asDescriptionFiles storedPublicFiles) = (F.pull LPFD.Full.instanceAsPlainRecord).run := by
  obtain ⟨F, h1, h2, -, -, h5⟩ := pseat_name storedPublicFiles theLive_zFull
  exact ⟨F, h1, h2, ((F.planOk_ok).1 h2).places, h5⟩

/-- **The same under the head, at the head's own term.** No premise. -/
theorem headPlanOk_zFull :
    ∃ Zp Np cF x,
      P5J.AtMgA OnBytes.secondHashFunction storedPublicFiles (dpZ storedPublicFiles) (theProofRun (asDescriptionFiles storedPublicFiles)) Zp Np cF x ∧
      ProofFile.onlineDescription OnBytes.secondHashFunction storedPublicFiles.pol storedPublicFiles.lay storedPublicFiles.KL =
        .ok (P5J.F0T OnBytes.secondHashFunction Zp Np cF) ∧
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk = true ∧
      ∀ b ∈ cF.blocksInOrder, b.planOk = true ∧ b.shaped = true := by
  obtain ⟨-, -, Zp, Np, cF, x, h⟩ := headMember_zFull
  exact ⟨Zp, Np, cF, x, h, h.laid.value, h.laid.planOk,
    (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).blocks₁⟩

open VerifiableInference.Desc.Key in
/-- **The key file's description at `storedPublicFiles` passes its tests on the plan.** No premise. -/
theorem keyPlanOk_zFull :
    ∃ X₀ m X N P,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction storedPublicFiles.pol storedPublicFiles.KL
        (some storedPublicFiles.lay) = .ok X₀ ∧
      madeAt X₀ storedPublicFiles.lay fixedDigest = .ok m ∧
      descAt X₀ storedPublicFiles.lay fixedDigest = .ok (descriptionFromSource X N P) ∧ (descriptionFromSource X N P).planOk = true ∧
      (descriptionFromSource X N P).wantedOk = true ∧ (descriptionFromSource X N P).owedOk = true ∧
      theKeyRun (asDescriptionFiles storedPublicFiles) = ((descriptionFromSource X N P).pull keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨X₀, m, X, N, P, a1, a2, a3, a4, a5, a6, -, -, a9⟩ := kseat_name storedPublicFiles theLive_zFull
  exact ⟨X₀, m, X, N, P, a1, a2, a3, a4, a5, a6, a9⟩

end AtFullSide.Top

#print axioms AtFullSide.Top.proofPlanOk_zFull
#print axioms AtFullSide.Top.headPlanOk_zFull
#print axioms AtFullSide.Top.keyPlanOk_zFull
