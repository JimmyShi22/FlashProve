-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`AtFullSide/E2E/ExtractorAtHonestTablesAtWritten.lean`: the statement `sound_and_tied` of `E2E/ExtractorAtHonestTables.lean` at
`VerifierAndGoals.storedPublicFiles`, the library's written copy of the full-size public files, with no premise.

What this file proves.
* `sound_and_tied_zFull`: at `VerifierAndGoals.storedPublicFiles`, the conclusion of the soundness theorem of the interactive oracle proof
  (`IndexKnowledgeSoundIOP` at the relation `relationAtFiles`, with the numbers 1 and 2^-128 as in that theorem) and
  `OneIndexOneRelationAt`, in one proposition. It imports the side library's proof that the public test `protocolDataWellFormed` returns true there
  (`AtFullSide/Bind/LiveAtNamed.lean`: `AtFullSide.Top.theLive_zFull`).

What this file does not say.
* All limits stated in `E2E/ExtractorAtHonestTables.lean` and in `E2E/SoundAsIOPAtFiles.lean` apply.
* It speaks of the files as they are written in the library, not of files on a disk.
-/
import E2E.ExtractorAtHonestTables
import AtFullSide.Bind.LiveAtNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles.AtHonestTables
open AtPublicFiles.AtFiles

/-- **At the written files: the soundness theorem's conclusion, and one index and one relation, in one proposition.** No premise. -/
theorem sound_and_tied_zFull :
    (protocolAtFiles VerifierAndGoals.storedPublicFiles).IndexKnowledgeSoundIOP (relationAtFiles VerifierAndGoals.storedPublicFiles) (filesAt VerifierAndGoals.storedPublicFiles).annT
      (offlinePlaces VerifierAndGoals.storedPublicFiles) (filesAt VerifierAndGoals.storedPublicFiles).annL 1 ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      OneIndexOneRelationAt VerifierAndGoals.storedPublicFiles :=
  let ⟨pp, hr⟩ := zFull_is_read
  sound_and_tied VerifierAndGoals.storedPublicFiles pp VerifierAndGoals.inScope_full hr AtFullSide.Top.theLive_zFull

end AtPublicFiles.AtFiles.AtHonestTables
end

#print axioms AtPublicFiles.AtFiles.AtHonestTables.sound_and_tied_zFull
#check @AtPublicFiles.AtFiles.AtHonestTables.sound_and_tied_zFull
