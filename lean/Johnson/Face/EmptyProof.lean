-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/EmptyProof.lean: the verifier refuses a form with no bytes in its proof
file.
-/
import Johnson.Goal.Tie.DescriptionOfDataRefuse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open TypedOracleCompiler.Compile.Batch.Cms
open PV.Head (cThru sevenThru)

/-- The reader of a proof file refuses empty bytes. -/
theorem madeProofOf_empty (config : ByteArray) :
    ∃ message, LKF.FileInOf.madeProofOf config ByteArray.empty = .error message :=
  ⟨_, rfl⟩

/-- A form with no bytes in its proof file decodes to nothing. -/
theorem decodeD_empty (config : ByteArray) (form : FormBytes)
    (empty : form.pb = ByteArray.empty) : decodeD config form = none := by
  obtain ⟨message, refused⟩ := madeProofOf_empty config
  unfold decodeD
  rw [empty, refused]
  split <;> simp_all

/-- **The verifier refuses a form with no bytes in its proof file.** -/
theorem verify_refuses_empty (L : DescriptionData) (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (O : ByteArray → ByteArray) (hO : (cThru O (asDescriptionFiles Z)).size = 32)
    (h7 : ∀ b ∈ sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z)), b.size = 32)
    (commitment : Commitment) (prompt output : List Token) (B : FormBytes)
    (empty : B.pb = ByteArray.empty) :
    (VerifierAndGoals.verify (descriptionOfDataOnBytes L) Z ((descriptionOfDataOnBytes L).parse Z) commitment prompt output B).evaluate
        (hashOf O) = false :=
  verify_descriptionOfDataOnBytes_refused L Z scope O hO h7 commitment prompt output B (decodeD_empty _ B empty)

end FlashProve

#print axioms FlashProve.madeProofOf_empty
#print axioms FlashProve.decodeD_empty
#print axioms FlashProve.verify_refuses_empty
