-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/ProofWritten.lean: in scope, either the verifier at the name says no to
all, or the data of the proof file's seat are the written data, a closed term.
`proof_written_or_no`: by cases on the proof file's seat: where it refuses:
`theDescription_no_of_proof` (Dead.lean); where it returns: `LPFD.Full.laidPOf_written`
(Johnson/Desc/Laid/ProofFullScope.lean). `proof_written_of_live`: so where `protocolDataWellFormed` says yes the
data are the written ones. `proof_built_written`: and so are the data that the verifier reads, the
letter DP of the built record (`dp_built_live`, Johnson/Goal/Conditions/LiveAtThe.lean).
Limits. «No to all» is: at every commitment, prompt, output and form, at `hashOf O` with 32-byte
answers, at the description's own parser, at `atSecondHashFunction theDescription`: the second hash function.
For the key file, and at every o: KeyWritten.lean. `protocolDataWellFormed` says yes at the written copies by
theorem (AtFullSide/Top/), as bytes by evaluation alone. Nothing on soundness.

-/
import Johnson.Goal.Description.Dead
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Goal.Conditions.LiveAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **In scope: no to all, or the written data.** -/
theorem proof_written_or_no (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) :
    (∀ (O : ByteArray → ByteArray), (∀ b, (O b).size = 32) →
      ∀ (commitment : Commitment) (prompt output : List Token) (B : FormBytes),
        (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z) commitment
          prompt output B).evaluate (hashOf O) = false) ∨
      theProofData (asDescriptionFiles Z) = Johnson.G.writtenPFull := by
  cases h : theProofLaid (asDescriptionFiles Z) with
  | error e =>
    exact Or.inl fun O h32 c p out B => theDescription_no_of_proof Z scope e h O h32 c p out B
  | ok x =>
    obtain ⟨D, r⟩ := x
    refine Or.inr ?_
    rw [theProofData_ok h]
    exact LPFD.Full.laidPOf_written (o := OnBytes.secondHashFunction) (Z := Z) scope h

/-- In scope, where `protocolDataWellFormed` says yes, the proof file's data are the written data. -/
theorem proof_written_of_live (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : theProofData (asDescriptionFiles Z) = Johnson.G.writtenPFull := by
  obtain ⟨_, P, _, _, hP, _⟩ := theLive_made (asDescriptionFiles Z) live
  obtain ⟨D, r⟩ := P
  rw [theProofData_ok hP]
  exact LPFD.Full.laidPOf_written (o := OnBytes.secondHashFunction) (Z := Z) scope hP

/-- **In scope, where `protocolDataWellFormed` says yes, the data that the verifier reads are the written
data.** -/
theorem proof_built_written (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) : (dataAtFiles flashProveData Z).DP = Johnson.G.writtenPFull :=
  (dp_built_live Z live).trans (proof_written_of_live Z scope live)

end FlashProve

#print axioms FlashProve.proof_written_or_no
#print axioms FlashProve.proof_written_of_live
#print axioms FlashProve.proof_built_written
