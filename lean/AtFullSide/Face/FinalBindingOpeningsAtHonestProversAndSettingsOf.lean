-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/FinalBindingOpeningsAtHonestProversAndSettingsOf.lean: the guard of Johnson/Face/FinalBindingOpeningsNamed.lean at
honestProversAndSettingsOf parts (AtFullSide/CompletenessAndZeroKnowledge/HonestProversAndSettingsOf.lean), at every value of the key file's arguments: at public files in use, at
every reading, every encoding randomness of the first table and every member of the list of its salts
are named together by a number up to that part's coinBound. So item 4 of FinalBindingStatement.lean's
head (at a small coinBound binding says next to nothing) does not bite at this part.
Limits. Those of FinalBindingOpeningsNamed.lean. No number is given for coinBound. Nothing on the later
digits: the key file's proofs, the copies, the links. It reads no prover.
-/
import Johnson.Face.FinalBindingOpeningsNamed
import AtFullSide.Face.FinalBindingAtHonestProversAndSettingsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.Face
open VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open AtPublicFiles.AtFiles.HonestTerm (Parts)
open IntegerTransformer (Settings)

variable (parts : (files : PublicFiles) → Parts files)

/-- That part's coinBound is theCoinBound at its own letters. -/
theorem coinBound_termHonest (files : PublicFiles) (settings : Settings) :
    (honestProversAndSettingsOf parts files settings).coinBound =
      theCoinBound files settings neverBuiltRequest (theProvers files settings (parts files))
        ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files settings))
        (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) := rfl

/-- **Every opening of the first table is named at the honest part of the protocol's provers.** -/
theorem everyRandomness_termHonest (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) (reading : FlashReading files) (leaves : ℕ)
    (r : (FlashProtocol files).EncodingRandomness)
    (b : Fin ((theSideAt files (settingsOfRead parameters) neverBuiltRequest
      (theProvers files (settingsOfRead parameters) (parts files))
      ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files (settingsOfRead parameters)))
      (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) reading).sl.n + 1)) :
    ∃ n, n ≤ (honestProversAndSettingsOf parts files (settingsOfRead parameters)).coinBound ∧
      firstRandomness (theSideAt files (settingsOfRead parameters) neverBuiltRequest
        (theProvers files (settingsOfRead parameters) (parts files))
        ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files (settingsOfRead parameters)))
        (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) reading) n = r ∧
      firstSalts (theSideAt files (settingsOfRead parameters) neverBuiltRequest
        (theProvers files (settingsOfRead parameters) (parts files))
        ((saltStartsAtHonestProvers files (parts files)).underRefusal (ServedAt files (settingsOfRead parameters)))
        (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) reading) leaves n =
        OnBytes.WholeKey.cutS leaves
          ((theSideAt files (settingsOfRead parameters) neverBuiltRequest
            (theProvers files (settingsOfRead parameters) (parts files))
            ((saltStartsAtHonestProvers files (parts files)).underRefusal
              (ServedAt files (settingsOfRead parameters)))
            (writtenLimits files) (flashProveRequestLeafSaltLayout files 40) reading).sl.e b) := by
  rw [coinBound_termHonest]
  exact everyRandomness_atTheSettings files (settingsOfRead parameters) neverBuiltRequest _ _ _ _
    inUse.inScope inUse.pass
    (termStarts_underRefusal_lengths parts files (settingsOfRead parameters)) reading
    (formatSlotSalts_fit (flashLayout files (settingsOfRead parameters) neverBuiltRequest reading) 40)
    leaves r b

end Johnson.Face

#print axioms Johnson.Face.coinBound_termHonest
#print axioms Johnson.Face.everyRandomness_termHonest
