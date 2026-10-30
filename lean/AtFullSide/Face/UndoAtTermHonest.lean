-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Face/UndoAtTermHonest.lean: the parser undoes the writer at the one honest part, honestProversAndSettingsOf.

undoUpTo_at_termHonest: at public files in use, UndoUpTo at honestProversAndSettingsOf, at the relation of the served
requests, up to six chances of 2 ^ -256. It is term_parserUpTo at termPrints, carried to honestProversAndSettingsOf by
termHonest_eq.
-/
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve

/-- **THE PARSER UNDOES THE WRITER AT THE ONE HONEST PART.** -/
theorem undoUpTo_at_termHonest (parts : (files : PublicFiles) → AtPublicFiles.AtFiles.HonestTerm.Parts files)
    (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ParserAt files hr (honestProversAndSettingsOf parts files (settingsOfRead pp)) := by
  rw [termHonest_eq parts files hr]
  exact term_parserUpTo parts files hr scope live (termPrints parts files hr)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.undoUpTo_at_termHonest
