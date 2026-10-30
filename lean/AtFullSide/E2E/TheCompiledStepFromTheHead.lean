-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/TheCompiledStepFromTheHead.lean

This file brings completeness of the interactive oracle proof from the form in which it is proved
into the form that the compilation theorem final_at_T1 (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean) takes as a
hypothesis, and then calls final_at_T1 under two hypotheses.

Terms.
  * Public files are "in use" when FilesInUse files parameters holds
    (Johnson/Face/FinalStatement.lean): the files are in scope (InScope), they read as these
    parameters, their policy is exact match, and they pass protocolDataWellFormed, the verifier's first test on
    public files.
  * onlineProverFromPublicFiles (Johnson/Desc/ProofFile/Honest/AtPure.lean) is the function that builds the honest
    prover's data (the structure OnlineProverWithDescription) from the bytes of the public files and an argument, here
    matrixFilling. It can fail; A is a value that it returns.
  * HeadAtReturn files A (Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean) is a record:
    the data from which the online proof's description is made at A, and (its field head) the
    library's facts on the public part of A, among them that the files are in scope.
  * Two definitions have the short name CompleteAtFiles. This file uses
    AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles (E2E/CompleteAsIOPAtNamed.lean), which is at the level
    of the interactive oracle proof: CompleteOnServedRequests of the provers theProvers. The one
    in Johnson/Face/FinalStatement.lean is about the compiled system.

The two forms differ in two ways. The theorems on completeness are stated for every returned value
A with a record HeadAtReturn, while final_at_T1 quantifies over all public files in use. They are
stated of theProvers, which refuse a request that is not served, while TermLeft, the hypothesis of
final_at_T1, speaks of (termLetters parts).provers files, the same provers without the refusal.

Main statements.
  * stepComplete_of_completeAtFiles: CompleteAtFiles files (parts files) hr implies
    CompleteOnServedRequests files hr ((termLetters parts).provers files). By theProvers_eq and
    completeOnServedRequests_refuse_iff, completeness on served requests holds of the provers with
    the refusal exactly if it holds of the provers without it.
  * CompleteUnderTheHead is a definition, used as a hypothesis: for all public files Z that pass
    protocolDataWellFormed and read as pp, every A with onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling =
    .ok A, and every HeadAtReturn Z A, CompleteAtFiles Z (thePartsAt Z) hr holds.
  * complete_at_every_files_in_use: CompleteUnderTheHead implies that, at all public files in use,
    CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files) holds. The
    value A and the record are given by head_in_use.
  * final_from_the_head: assume CompleteUnderTheHead, and assume that at all public files in use
    there are numbers offlineStops, linkStops and onlineStops at which
    ZeroKnowledgeOnServedRequests holds of (termLetters thePartsAt).provers files and 2^-157 +
    (offlineStops + linkStops + 688127 * onlineStops) ≤ stepError. Then FinalComplete (honestProversAndSettingsOf
    thePartsAt), FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepError and RepliesFit (honestProversAndSettingsOf
    thePartsAt) hold.

Limits.
  * The names of the definitions mean exactly what the definitions say. The sentences in this
    header summarise them and do not replace them.
  * The theorems of this file are implications. This file proves neither completeness nor zero
    knowledge: neither hypothesis of final_from_the_head is proved here. CompleteUnderTheHead is
    proved in AtFullSide/E2E/CompleteAtEveryFilesInUse.lean (completeUnderTheHead_paid), and the
    hypothesis on zero knowledge in AtFullSide/E2E/TheCompiledStepFilled.lean
    (termLeftLaterClauses_filled), for every stepError of at least stepErrorAtTheStops, which is
    2^-157 + (0 + 0 + 688127 * 2^-174).
  * CompleteUnderTheHead asks for completeness with no premise beyond the test on the files, their
    reading, the returned value and the record at it. A theorem on completeness that has a further
    premise of its own does not give it.
  * All limits of final_at_T1 hold: its conclusion is three of the six fields of FinalStatement
    (complete, zeroKnowledge, repliesFit; not sound, binding, handsOutNoProof), at one commitment,
    one copy of the committed table and at most 688127 replies. The error stepError is a parameter
    of final_from_the_head, and this file gives it no value. The limits on these three fields are
    listed in the header of AtFullSide/E2E/TheCompiledStepFilled.lean.
  * This file adds no statement on what a proof hides beyond ZeroKnowledgeOnServedRequests, as
    defined in VerifiableInference/Final/ZeroKnowledgeAtTheProtocol.lean, and FinalZeroKnowledge,
    as defined in Johnson/Face/FinalStatement.lean.
  * The statements are about the honest prover as it is defined in Lean, default values included.
    It is a definition, not a program that runs. Nothing here is about the C++ programs.
  * The statements hold for the full-size layout alone (InScope: the layout file is that of the
    stored full-size example), and for the format's second hash function OnBytes.secondHashFunction alone.

Built on.
  * head_in_use (AtFullSide/E2E/HeadInUse.lean).
  * final_at_T1, TermLeft, honestProversAndSettingsOf (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean).
  * theProvers_eq (Johnson/CompletenessAndZeroKnowledge/TheProversEq.lean).
  * completeOnServedRequests_refuse_iff
    (VerifiableInference/Final/ZeroKnowledgeAtTheProtocolLaws.lean).
  * CompleteAtFiles (E2E/CompleteAsIOPAtNamed.lean) and thePartsAt (E2E/KeyArgumentsAt.lean).
-/
import AtFullSide.E2E.HeadInUse
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf
import Johnson.CompletenessAndZeroKnowledge.TheProversEq
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws
import E2E.CompleteAsIOPAtNamed
import E2E.KeyArgumentsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (OnlineProverWithDescription IndexCommitterCoins Cells onlineProverFromPublicFiles)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixFilling)

/-- Completeness on served requests of theProvers, which refuse a request that is not served,
gives it for the same provers without the refusal. -/
theorem stepComplete_of_completeAtFiles (parts : (files : PublicFiles) → Parts files) (files : PublicFiles)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles files (parts files) hr) :
    CompleteOnServedRequests files hr ((termLetters parts).provers files) := by
  unfold AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles at complete
  rw [theProvers_eq files hr (parts files)] at complete
  exact (completeOnServedRequests_refuse_iff files hr _).1 complete

/-- Completeness of the interactive oracle proof at every value A that onlineProverFromPublicFiles returns at
matrixFilling and every record HeadAtReturn Z A. A definition, used as a hypothesis in this file.
-/
def CompleteUnderTheHead : Prop :=
  ∀ (Z : PublicFiles) (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (pp : Inst.Model.ScalesAndPolicy),
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ hr : readFiles Z = .ok pp,
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A → HeadAtReturn Z A →
    AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles Z (thePartsAt Z) hr

/-- Conditional on CompleteUnderTheHead: completeness on served requests at all public files in
use, in the form of the first clause of TermLeft. -/
theorem complete_at_every_files_in_use (T2 : CompleteUnderTheHead) :
    ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      CompleteOnServedRequests files inUse.read ((termLetters thePartsAt).provers files) := by
  intro files parameters inUse
  obtain ⟨A, h, made⟩ := head_in_use files parameters inUse
  exact stepComplete_of_completeAtFiles thePartsAt files inUse.read
    (T2 files A parameters inUse.pass inUse.read made h)

/-- Conditional on both hypotheses: the conclusion of final_at_T1 at thePartsAt. -/
theorem final_from_the_head (stepError : ℝ≥0∞) (T2 : CompleteUnderTheHead)
    (T3 : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
        ZeroKnowledgeOnServedRequests files inUse.read ((termLetters thePartsAt).provers files)
          offlineStops linkStops onlineStops ∧
        (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
          stepError) :
    (FinalComplete (honestProversAndSettingsOf thePartsAt) ∧
        FinalZeroKnowledge (honestProversAndSettingsOf thePartsAt) stepError) ∧
      RepliesFit (honestProversAndSettingsOf thePartsAt) :=
  final_at_T1 thePartsAt stepError fun files parameters inUse =>
    let ⟨offlineStops, linkStops, onlineStops, hidden, sum⟩ := T3 files parameters inUse
    ⟨⟨offlineStops, linkStops, onlineStops,
      complete_at_every_files_in_use T2 files parameters inUse, hidden, sum⟩⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.stepComplete_of_completeAtFiles
#print axioms VerifiableInference.Compilation.complete_at_every_files_in_use
#print axioms VerifiableInference.Compilation.final_from_the_head
