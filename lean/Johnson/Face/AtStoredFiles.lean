-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/AtStoredFiles.lean: the top lines at the stored full-size public files.

 1. storedPublicFiles are the full-size files written in Ladder/Stored.lean. They are in scope, they read, and
    their policy is exact match (VerifierAndGoals.filesRead). That they are the bytes that ship is not said.
 2. storedParameters is what they read as.
 3. FinalStatementAtStoredFiles is the six lines there: a statement that a proof can reach at these
    files alone, without the lines at every file.
 4. The soundness line holds there, at every honest part.
 5. The lines that also ask the public test hold, given the test: protocolDataWellFormed at storedPublicFiles, which the side
    library proves, by a proof that no independent checker has replayed.
 6. zGap, the other named set, has another policy, at which soundness in this form is not expected to
    hold. Every line here is at exact match, so none speaks of it.
-/
import Johnson.Face.FinalSoundProof
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open scoped ENNReal

/-- The stored files are taken. -/
theorem exists_filesTaken_zFull : ∃ parameters, FilesTaken storedPublicFiles parameters :=
  let ⟨inScope, parameters, read, exactMatch⟩ := filesRead.full
  ⟨parameters, inScope, read, exactMatch⟩

/-- What the stored files read as. -/
def storedParameters : Inst.Model.ScalesAndPolicy := exists_filesTaken_zFull.choose

/-- They are taken at it. -/
theorem filesTaken_stored : FilesTaken storedPublicFiles storedParameters := exists_filesTaken_zFull.choose_spec

/-- **The six lines at the stored files.** -/
structure FinalStatementAtStoredFiles (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) :
    Prop where
  sound : SoundAtFiles honest storedPublicFiles storedParameters
  binding : BindingAtFiles honest storedPublicFiles storedParameters
  complete : CompleteAtFiles honest storedPublicFiles storedParameters
  zeroKnowledge : ZeroKnowledgeAtFiles honest zeroKnowledgeError storedPublicFiles storedParameters
  reply : ReplyAtFiles honest storedPublicFiles storedParameters
  repliesFit : RepliesFitAtFiles honest storedPublicFiles storedParameters

/-- **Soundness at the stored files, at every honest part.** -/
theorem finalSound_stored (honest : HonestProversAndSettings) : SoundAtFiles honest storedPublicFiles storedParameters :=
  finalSound honest storedPublicFiles storedParameters filesTaken_stored

/-- The lines at every file give them at the stored files, where the public test passes. -/
theorem atStoredFiles_of_finalStatement (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞)
    (live : protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true) (final : FinalStatement honest zeroKnowledgeError) :
    FinalStatementAtStoredFiles honest zeroKnowledgeError :=
  have inUse : FilesInUse storedPublicFiles storedParameters := ⟨filesTaken_stored, live⟩
  ⟨final.sound storedPublicFiles storedParameters filesTaken_stored,
    final.binding storedPublicFiles storedParameters inUse, final.complete storedPublicFiles storedParameters inUse,
    final.zeroKnowledge storedPublicFiles storedParameters inUse,
    final.handsOutNoProof storedPublicFiles storedParameters filesTaken_stored,
    final.repliesFit storedPublicFiles storedParameters inUse⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalSound_stored
#print axioms VerifiableInference.Compilation.atStoredFiles_of_finalStatement
