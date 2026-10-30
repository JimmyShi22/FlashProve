-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/FirstNumber.lean: THE COMPLETENESS ERROR AT THE SETTINGS, BUT FOR THE PROVERS' LETTERS. At
theSettings with the chosen search limits, at public files in scope where protocolDataWellFormed says yes, at every value
of the public reading: the searches' part of completenessError is at most 71 · 2^-92, since 71 rounds have
a test and each search runs out with chance at most 2^-92. The layout at a reading keeps the wire of the
base input, and the searches' part reads the wire alone. Nothing here is claimed of a protocol:
this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.OneHashByFirstBlockTestAtSettings
import Johnson.Goal.Conditions.NumberAtHome

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad
open IntegerTransformer (Settings)

/-- The searches' part at the wire of the base input. -/
theorem searches_le (files : PublicFiles) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) :
    alphaAll (flashProveDescription.input files allZeroDigest []).queryLayout (capT (dataAtFiles flashProveData files)) capL
        (capB (dataAtFiles flashProveData files)) ζ₁ ζ₂ δT δL δB ≤
      71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (ζ₁ + ζ₂) + (δT + δL + δB) := by
  unfold alphaAll
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  refine (add_le_add (add_le_add
    (failT_written (dataAtFiles flashProveData files) allZeroDigest [] (key_built_written files scope live))
    (failL_written (dataAtFiles flashProveData files) allZeroDigest []))
    (failB_written (dataAtFiles flashProveData files) allZeroDigest [] (proof_built_written files scope live))).trans
    (le_of_eq ?_)
  rw [← add_mul, ← add_mul]
  norm_num

/-- **THE FIRST NUMBER, BUT FOR THE PROVERS' LETTERS.** -/
theorem completenessError_theSettings (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (starts : SaltStarts provers) (slotSalts : RequestLeafSaltLayout) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (E : CompletenessErrors)
    (reading : FlashReading files) :
    completenessError (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers starts (writtenLimits files) slotSalts
          reading) E ≤
      71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (E.offline + E.link + E.online) := by
  have e : 71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (0 + 0) + (E.offline + E.link + E.online) =
      71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (E.offline + E.link + E.online) := by simp
  exact (searches_le files scope live 0 0 E.offline E.link E.online).trans_eq e

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.searches_le
#print axioms VerifiableInference.Compilation.completenessError_theSettings
