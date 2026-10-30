-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/ThreeAtFilesOfEnds.lean: the structure ThreeAtOneProtocol (E2E/ThreeAtOneProtocol.lean) at the public files, from
the theorem on soundness and the two other statements as their theorems end; and that the triple of provers bound in it
is the one inside the compiled system.

  threeAtFiles_of_ends              ThreeAtFiles Z hr (the plain provers) a b c. Soundness is called as a theorem
                                    (soundAsIOPAtTheProtocol); completeness and zero knowledge are premises, in the very
                                    forms in which their theorems end
  compiled_provers_are_the_triple   the provers of honestProversAndSettingsOf parts, at files that read, are the triple that ThreeAtFiles binds
  compiled_protocol_is_the_bound    the protocol over which flashProveAtFiles's provers are typed is protocolAtFiles files
  three_and_lines_of_ends           from the same two premises and the inequality, at one set of files in use: ThreeAtFiles,
                                    and the three compiled lines of AtFullSide/CompletenessAndZeroKnowledge/LinesAtFiles.lean

What it is for. A member of ThreeAtFiles needs the three ends to meet at one protocol, one triple, one relation and the
same files as Lean's terms, not by name. Here Lean checks that, with two of the three as premises.

Limits. Implications: completeness and zero knowledge of the interactive protocol are premises here. This file
gives no member of the structure. Nothing on soundness or on what is hidden beyond the fields' own text.
-/
import AtFullSide.CompletenessAndZeroKnowledge.LinesAtFiles
import E2E.ThreeAtOneProtocol
import E2E.SoundAsIOPAtFilesProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.OneProtocol (ThreeAtFiles threeAtOne_of_statements)

/-- **The three at one protocol, from the theorem on soundness and the two ends.** -/
theorem threeAtFiles_of_ends {Z : PublicFiles} (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) (P : Parts Z) {a b c : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles Z P hr)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests Z hr (HonestProvers.ofThreeProvers (honestProvers Z P)) a b c) :
    ThreeAtFiles Z hr (HonestProvers.ofThreeProvers (honestProvers Z P)) a b c := by
  have k : CompleteOnServedRequests Z hr (theProvers Z (settingsOfRead pp) P) := complete
  rw [theProvers_eq Z hr P] at k
  exact threeAtOne_of_statements (soundAsIOPAtTheProtocol Z pp scope hr live) k zeroKnowledge scope

variable (parts : (files : PublicFiles) → Parts files)

/-- **The provers inside the compiled system are the triple that the structure binds.** -/
theorem compiled_provers_are_the_triple (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hr : readFiles files = .ok pp) :
    (honestProversAndSettingsOf parts files (settingsOfRead pp)).provers =
      proversAtFiles files hr (HonestProvers.ofThreeProvers (honestProvers files (parts files))) :=
  theProvers_eq files hr (parts files)

/-- **The protocol over which these provers are typed is the one that the structure binds.** -/
theorem compiled_protocol_is_the_bound (files : PublicFiles) :
    (flashProveDescription.F files).withProvers (flashProveDescription.P files) = protocolAtFiles files := rfl

/-- **Both storeys from the same two premises**, at one set of files in use. -/
theorem three_and_lines_of_ends (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters)
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles files (parts files) inUse.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests files inUse.read
      (HonestProvers.ofThreeProvers (honestProvers files (parts files))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    ThreeAtFiles files inUse.read (HonestProvers.ofThreeProvers (honestProvers files (parts files))) offlineStops
        linkStops onlineStops ∧
      VerifiableInference.Compilation.CompleteAtFiles (honestProversAndSettingsOf parts) files parameters ∧
      ZeroKnowledgeAtFiles (honestProversAndSettingsOf parts) zeroKnowledgeError files parameters ∧
      RepliesFitAtFiles (honestProversAndSettingsOf parts) files parameters :=
  ⟨threeAtFiles_of_ends inUse.inScope inUse.pass inUse.read (parts files) complete zeroKnowledge,
    lines_at_files_of_ends parts files parameters inUse complete zeroKnowledge sum⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.threeAtFiles_of_ends
#print axioms VerifiableInference.Compilation.compiled_provers_are_the_triple
#print axioms VerifiableInference.Compilation.compiled_protocol_is_the_bound
#print axioms VerifiableInference.Compilation.three_and_lines_of_ends
