-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/OneHashByFirstBlockTestAtSettings.lean: THE BUDGET AT THE COMPILER'S SETTINGS AT flashProveAtFiles: at theSettings, with
one copy and the search limits 2 ^ (work + 6), the honest side of slotSystemF stays within the budget of the
final statement. It is stated at slotSystemF; compile's committer and prover are slotSystemF's
(compile_eq_slotSystemF, Johnson/Face/Compiler.lean), and OneHashByFirstBlockTestTies.lean carries this bound to compile. A hash
query is one call at a string of any length. What is claimed is an upper bound on every path at the written data;
this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestAtFiles
import Johnson.CompletenessAndZeroKnowledge.TheSettingsFit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad
open VerifiableInference.AtEveryRequest (WithinBudget)
open IntegerTransformer (Settings)

/-- The search limits of the budget: 2 ^ (work + 6) tries in a round with work bits. -/
def writtenLimits (files : PublicFiles) : SearchLimits :=
  ⟨capT (dataAtFiles flashProveData files), capL, capB (dataAtFiles flashProveData files)⟩

/-- **The honest side of slotSystemF at theSettings stays within honestQueryBudget.** -/
theorem theSettings_withinBudgetF (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (starts : SaltStarts provers) (slotSalts : RequestLeafSaltLayout) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (h : starts.LengthsFit 256 256)
    (slots : ∀ reading, slotSalts.Fit (flashLayout files settings fallbackInstance reading))
    (bound : ℕ) :
    WithinBudget (slotSystemF flashProveDescription files allZeroDigest [] (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
        (fun reading => (honestSide (flashLayout files settings fallbackInstance reading) provers
          (theSettings files settings fallbackInstance provers starts (writtenLimits files) slotSalts
            reading)).side)
        (fun _ => moreP (firstBlockTestAtDescriptionData (dataAtFiles flashProveData files) allZeroDigest [])) settings (backThe files settings)
        fallbackInstance flashProveDescription.Form (flashProveDescription.parse files) (bytesWriter files) bound)
      honestQueryBudget :=
  slotSystemF_two_pow_48 files scope live _ 0 (fun _ => rfl) (by norm_num) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl)
    (fun reading => theSettings_paths files settings fallbackInstance provers (writtenLimits files)
      slotSalts scope live starts h reading (slots reading))
    settings _ _ _ _ _ bound

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.theSettings_withinBudgetF
