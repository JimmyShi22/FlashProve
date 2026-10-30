-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/HonestProversAndSettingsValue.lean: the honest part as one closed term.

 1. thePartsAt is a value of the key file's part, at every public files: named stand-ins, and three
    things fixed at the written sizes. Nothing is proved of this value here. That no stand-in is reached at
    files in use is not shown here: it is part of completeness.
 2. honestProversAndSettings is honestProversAndSettingsOf at it: one closed term, of the public files and settings alone. The online
    prover's own fall-backs stand in it too.
 3. From completeness and zero knowledge of the interactive protocol, with the error's inequality,
    follow FinalComplete, FinalZeroKnowledge and RepliesFit of it. The line on the reply holds of it,
    with no premise. Binding is not reached here.
-/
import AtFullSide.Face.TheFinalStatementAtTerm
import AtFullSide.Face.TheReplyAtTerm
import E2E.KeyArgumentsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- The honest provers of the protocol and the settings beside them: the three IOPs' honest provers,
and what the honest side chooses beside them, among them where its salts start, how long a search
for a nonce may run and a fall-back instance. It holds no committer: the honest committer is what
compile makes. The verifier reads none of it. -/
noncomputable def honestProversAndSettings : HonestProversAndSettings := honestProversAndSettingsOf thePartsAt

/-- **The final statement of the honest part.** -/
abbrev TheFinalStatementAtValue (zeroKnowledgeError : ℝ≥0∞) : Prop :=
  TheFinalStatementAtTerm thePartsAt zeroKnowledgeError

/-- **From completeness and zero knowledge of the interactive protocol, with the inequality, three of
the compiled lines, of the honest part.** -/
theorem final_of_three (zeroKnowledgeError : ℝ≥0∞)
    (three : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
        TheThreeIOPStatements files inUse.read (thePartsAt files) offlineStops linkStops onlineStops ∧
        (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
          zeroKnowledgeError) :
    (FinalComplete honestProversAndSettings ∧ FinalZeroKnowledge honestProversAndSettings zeroKnowledgeError) ∧
      RepliesFit honestProversAndSettings :=
  final_at_T1_of_three thePartsAt zeroKnowledgeError three

/-- **The replies fit, at the honest part.** -/
theorem repliesFit_value : RepliesFit honestProversAndSettings := term_repliesFit thePartsAt

/-- **The reply, of the honest part.** -/
theorem finalHandsOutNoProof_value : FinalHandsOutNoProof honestProversAndSettings :=
  finalHandsOutNoProof_term thePartsAt

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.final_of_three
#print axioms VerifiableInference.Compilation.finalHandsOutNoProof_value
#print axioms VerifiableInference.Compilation.repliesFit_value
