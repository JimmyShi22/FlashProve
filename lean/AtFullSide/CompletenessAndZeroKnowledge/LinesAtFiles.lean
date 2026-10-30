-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/LinesAtFiles.lean: the compiled lines at ONE set of public files in use, from the two statements on
the interactive protocol at these files alone.

final_at_T1 (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean) asks TermLeft at every public files in use and ends in the lines at
every public files in use. Its road goes file by file. Here each step is stated at one set of files.

  zeroKnowledgeOneBit_atFiles      the body of finalZeroKnowledgeOneBit_of_spent (Johnson/CompletenessAndZeroKnowledge/FinalRoadProof.lean)
  zeroKnowledgeAtFiles_of_oneBit   the two steps of Johnson/Face/Checks.lean behind it
  termLeft_of_ends                 TermLeft from completeness at theProvers, zero knowledge at the plain provers,
                                   and the inequality on the three numbers
  lines_at_files                   CompleteAtFiles, ZeroKnowledgeAtFiles and RepliesFitAtFiles of honestProversAndSettingsOf parts
  lines_at_files_of_ends           the same from the two statements as their theorems end

Limits. Implications: completeness and zero knowledge of the interactive protocol are premises here. parts and the
error are arguments. Three of the six lines. Nothing on soundness or on what is hidden.
-/
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf
import Johnson.CompletenessAndZeroKnowledge.TheProversEq
import E2E.CompleteAsIOPAtNamed
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover VerifiableInference.OnPublicFiles
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open IntegerTransformer (Settings)

/-- **The one-bit statement at one set of files in use**, from what the road's zero-knowledge half spends there. -/
theorem zeroKnowledgeOneBit_atFiles (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters) (l : RoadLetters files)
    (hRoad : RoadZeroKnowledgePremises files (settingsOfRead parameters)
      (honest files (settingsOfRead parameters)) zeroKnowledgeError l) :
    AtEveryRequest.ZeroKnowledgeBelowWhere (finalSystem honest files (settingsOfRead parameters))
      (fun _ => True) (AtEveryRequest.requestOutcome (settingsOfRead parameters)) finalVerifierQueries
      finalReplyCount zeroKnowledgeError := by
  obtain ⟨weights, -, -⟩ := someRequestIsServedInUse files parameters inUse
  refine ⟨fun t n => roadError (honest files (settingsOfRead parameters)) l (t + 1) n, ?_, ?_⟩
  · exact fun asked replies ha hr =>
      iSup_le fun reading => hRoad.hidingBelow reading asked replies ha hr
  · have onCanServe : ZeroKnowledgeOn (finalSystem honest files (settingsOfRead parameters))
        (CanServe (settingsOfRead parameters))
        (fun t n => roadError (honest files (settingsOfRead parameters)) l (t + 1) n) :=
      zeroKnowledgeOn_of_eq (compile_flashProve_eq files (settingsOfRead parameters)
          (honest files (settingsOfRead parameters))) rfl rfl
        (CanServe (settingsOfRead parameters)) _
        (zeroKnowledgeOn_slotSystemF (familyLaws_the files).noCoin
          (flash_firstBlockFits files (honestPartSide files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters))))
          (road_zeroKnowledge_atSlot files (settingsOfRead parameters)
            (honest files (settingsOfRead parameters)) zeroKnowledgeError l inUse.inScope
            (backThe files (settingsOfRead parameters) weights) hRoad))
    exact AtEveryRequest.zeroKnowledgeFollowsFromOn _ _ noProofForm
      (finalServedIsModelOutput honest files parameters inUse.toFilesTaken)
      (final_handsOut honest files parameters zeroKnowledgeError l hRoad) _
      (zeroKnowledgeOn_of_domain (fun w p o served _ =>
        ((AtEveryRequest.served_iff_canServe (valid_of_read inUse.read) w (p, o)).1 served).1)
        onCanServe)

/-- **The line on zero knowledge at one set of files**, from the one-bit statement there. -/
theorem zeroKnowledgeAtFiles_of_oneBit (honest : HonestProversAndSettings) (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy)
    (oneBit : AtEveryRequest.ZeroKnowledgeBelowWhere (finalSystem honest files (settingsOfRead parameters))
      (fun _ => True) (AtEveryRequest.requestOutcome (settingsOfRead parameters)) finalVerifierQueries
      finalReplyCount zeroKnowledgeError) :
    ZeroKnowledgeAtFiles honest zeroKnowledgeError files parameters := by
  obtain ⟨error, bounded, zeroKnowledge⟩ := oneBit
  have shown : AtEveryRequest.ZeroKnowledgeShownBelowWhere
      (finalSystem honest files (settingsOfRead parameters)) (fun _ => True)
      (AtEveryRequest.requestLabel (settingsOfRead parameters)) finalVerifierQueries finalReplyCount
      zeroKnowledgeError :=
    ⟨error, bounded,
      zeroKnowledgeShown_of_told (finalSystem honest files (settingsOfRead parameters))
        (AtEveryRequest.requestLabel (settingsOfRead parameters))
        (AtEveryRequest.requestOutcome (settingsOfRead parameters)) AtEveryRequest.bitOf
        (fun weights request => (AtEveryRequest.bitOf_requestLabel _ weights request).symm)
        (fun _ => True) error zeroKnowledge⟩
  exact AtEveryRequest.ZeroKnowledgeShownBelowWhere.narrow (fun _ _ => trivial) shown

variable (parts : (files : PublicFiles) → Parts files)

/-- **What is left at one set of files, from the two statements as their theorems end**: completeness at the
provers that refuse, zero knowledge at the plain provers. -/
theorem termLeft_of_ends (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles files (parts files) inUse.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests files inUse.read
      (HonestProvers.ofThreeProvers (honestProvers files (parts files))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    TermLeft parts files parameters inUse zeroKnowledgeError := by
  have c : CompleteOnServedRequests files inUse.read
      (theProvers files (settingsOfRead parameters) (parts files)) := complete
  rw [theProvers_eq files inUse.read (parts files)] at c
  exact ⟨offlineStops, linkStops, onlineStops,
    (completeOnServedRequests_refuse_iff files inUse.read _).1 c, zeroKnowledge, sum⟩

/-- **THREE COMPILED LINES AT ONE SET OF FILES IN USE**, from what is left at these files alone. -/
theorem lines_at_files (zeroKnowledgeError : ℝ≥0∞) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters)
    (left : TermLeft parts files parameters inUse zeroKnowledgeError) :
    VerifiableInference.Compilation.CompleteAtFiles (honestProversAndSettingsOf parts) files parameters ∧
      ZeroKnowledgeAtFiles (honestProversAndSettingsOf parts) zeroKnowledgeError files parameters ∧
      RepliesFitAtFiles (honestProversAndSettingsOf parts) files parameters := by
  obtain ⟨l, road, -⟩ := roadPremises_at_T1 parts zeroKnowledgeError files parameters inUse left
  exact ⟨(finalComplete_iff_completeOn (honestProversAndSettingsOf parts) files parameters inUse.toFilesTaken
      finalCompletenessError).2 (served_at_T1 parts zeroKnowledgeError files parameters inUse left).1,
    zeroKnowledgeAtFiles_of_oneBit (honestProversAndSettingsOf parts) zeroKnowledgeError files parameters
      (zeroKnowledgeOneBit_atFiles (honestProversAndSettingsOf parts) zeroKnowledgeError files parameters inUse l
        road.toZeroKnowledge),
    term_repliesFit parts files parameters inUse⟩

/-- **The same from the two statements as their theorems end.** -/
theorem lines_at_files_of_ends (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters)
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles files (parts files) inUse.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests files inUse.read
      (HonestProvers.ofThreeProvers (honestProvers files (parts files))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    VerifiableInference.Compilation.CompleteAtFiles (honestProversAndSettingsOf parts) files parameters ∧
      ZeroKnowledgeAtFiles (honestProversAndSettingsOf parts) zeroKnowledgeError files parameters ∧
      RepliesFitAtFiles (honestProversAndSettingsOf parts) files parameters :=
  lines_at_files parts zeroKnowledgeError files parameters inUse
    (termLeft_of_ends parts files parameters inUse complete zeroKnowledge sum)

/-- The lines at every files in use follow from the lines at each. -/
example (zeroKnowledgeError : ℝ≥0∞)
    (left : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      TermLeft parts files parameters inUse zeroKnowledgeError) :
    FinalComplete (honestProversAndSettingsOf parts) ∧ FinalZeroKnowledge (honestProversAndSettingsOf parts) zeroKnowledgeError :=
  ⟨fun files parameters inUse =>
      (lines_at_files parts zeroKnowledgeError files parameters inUse (left files parameters inUse)).1,
    fun files parameters inUse =>
      (lines_at_files parts zeroKnowledgeError files parameters inUse (left files parameters inUse)).2.1⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOneBit_atFiles
#print axioms VerifiableInference.Compilation.zeroKnowledgeAtFiles_of_oneBit
#print axioms VerifiableInference.Compilation.termLeft_of_ends
#print axioms VerifiableInference.Compilation.lines_at_files
#print axioms VerifiableInference.Compilation.lines_at_files_of_ends
