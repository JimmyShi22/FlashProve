-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingLines.lean: the fourth top line,
FinalSoundAndBinding (FinalStatement.lean: SoundAndBinding (compile flashProveAtFiles) finalBindingError, at
FilesInUse), of an honest part at every set of public files, from finalBindingGoal
(FinalBindingProof.lean).

 1. finalSystem is compile flashProveAtFiles at the honest part of the public files and settings.
 2. The premise: at all public files in use the salts of a table's leaves have one length
    (TableSaltsOfOneLength). It is a premise that the top line does not show.
 3. Beside it: all six lines at finalSystem and finalExtractor (finalBindingAtFinalSystem), at
    FilesTaken; soundness for an opened commitment; correctness of extraction.
 4. The lines speak of honest : HonestProversAndSettings, an honest part at EVERY set of public files and
    settings. That type has a member (allHonestParts_nonempty, FinalBindingGuards.lean), and so has
    the premise (tableSaltsOfOneLength_met): members, not the honest part that is meant.
 5. FilesInUse asks the test on the public files. That any files pass it is no theorem of the main
    library: it is evaluated, and a theorem of the side library at the written full-size files.
 6. All limits of FinalBindingStatement.lean's head go with these lines.
-/
import Johnson.Face.FinalBindingProof
import Johnson.Face.FinalBindingGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)
open scoped ENNReal

/-- At all public files in use the salts of a table's leaves have one length. -/
def TableSaltsOfOneLength (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ∃ length, TableSaltsHaveLength (honest files (settingsOfRead parameters)) length

/-- **Soundness for an opened commitment.** -/
def FinalSoundOpened (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    SoundOpened (finalSystem honest files (settingsOfRead parameters))
      fun queries => 2 * finalBindingError queries

/-- **Correctness of extraction**, at every bound on the committer's own queries. -/
def FinalExtractsCommitted (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    ∀ queries, CommitterWithin (finalSystem honest files (settingsOfRead parameters)) queries →
      ExtractsCommittedWeights (finalSystem honest files (settingsOfRead parameters))
        (finalExtractor files (settingsOfRead parameters)) (finalOpeningError queries)

/-- **The six lines at the final system**, at public files that the verifier takes. -/
theorem finalBindingAtFinalSystem (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (taken : FilesTaken files parameters) (length : ℕ)
    (salts : TableSaltsHaveLength (honest files (settingsOfRead parameters)) length) :
    BindingOf (finalSystem honest files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) :=
  finalBindingGoal files parameters taken (honest files (settingsOfRead parameters)) length salts

/-- **FinalSoundAndBinding**, under the premise on salts. The extractor behind its ∃ is
finalExtractor. -/
theorem finalSoundAndBinding (honest : HonestProversAndSettings) (salts : TableSaltsOfOneLength honest) :
    FinalSoundAndBinding honest :=
  fun files parameters inUse =>
    (salts files parameters inUse).elim fun length h =>
      (finalBindingAtFinalSystem honest files parameters inUse.toFilesTaken length h).soundAndBinding

theorem finalSoundOpened (honest : HonestProversAndSettings) (salts : TableSaltsOfOneLength honest) :
    FinalSoundOpened honest :=
  fun files parameters inUse =>
    (salts files parameters inUse).elim fun length h =>
      (finalBindingAtFinalSystem honest files parameters inUse.toFilesTaken length h).soundOpened

theorem finalExtractsCommitted (honest : HonestProversAndSettings) (salts : TableSaltsOfOneLength honest) :
    FinalExtractsCommitted honest :=
  fun files parameters inUse =>
    (salts files parameters inUse).elim fun length h =>
      (finalBindingAtFinalSystem honest files parameters inUse.toFilesTaken length h).extracts

/-- **Correctness of extraction at 2^48**, where the replies fit (RepliesFit, FinalStatement.lean: its
last clause is the honest side's budget): the error is about 2^-155.2. -/
theorem finalExtractsWithinBudget (honest : HonestProversAndSettings) (salts : TableSaltsOfOneLength honest)
    (fit : RepliesFit honest) (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ExtractsCommittedWeights (finalSystem honest files (settingsOfRead parameters))
      (finalExtractor files (settingsOfRead parameters)) (finalOpeningError honestQueryBudget) :=
  (salts files parameters inUse).elim fun length h =>
    (finalBindingAtFinalSystem honest files parameters inUse.toFilesTaken length
      h).extractsWithinBudget (fit files parameters inUse).2.2

/-- The premise has a member. -/
theorem tableSaltsOfOneLength_met : ∃ honest : HonestProversAndSettings, TableSaltsOfOneLength honest :=
  ⟨fun files settings => silentPart files settings 0,
    fun files parameters _ => ⟨0, silentPart_salts files (settingsOfRead parameters) 0⟩⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalBindingAtFinalSystem
#print axioms VerifiableInference.Compilation.finalSoundAndBinding
#print axioms VerifiableInference.Compilation.finalSoundOpened
#print axioms VerifiableInference.Compilation.finalExtractsCommitted
#print axioms VerifiableInference.Compilation.finalExtractsWithinBudget
#print axioms VerifiableInference.Compilation.tableSaltsOfOneLength_met
