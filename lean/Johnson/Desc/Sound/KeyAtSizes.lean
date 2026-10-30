-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyAtSizes.lean: THE KEY FILE'S NAMED HYPOTHESIS ON SOUNDNESS AS THE LIBRARY'S
FRAME AT THE TWO SIZES ASKS IT (`RemainingSoundnessConditionsWithFixedLinkAtFullSize.keySound`, `RemainingSoundnessConditionsWithFixedLinkAtSmallSize.keySound`,
Johnson/Flat/TwoSizesAt.lean) IS `KeyCore` (Johnson/Desc/Sound/KeyCore.lean) at that frame's own
letters.

The setting. Johnson/Flat/TwoSizesAt.lean has the top theorem's input at the full and at the small
size, general in the two files' written rounds' data (DK, DP) and in the two decisions (runK, runP).
What is left there of the key file is the field `keySound : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T)`
(and the like at the small size).

What is said. `keySound_full_iff`, `keySound_small_iff`: that field IS `KeyCore` at the size's
configuration (`lettersAt A (relationsAndEncodingOfClaims A E)`), the data DK, the frame's own silent rounds and test on
them, THE FRAME'S OWN DECISION runK, 2 ^ T.depthReqT leaves and T.εs: by unfolding.
`keySound_full_of_desc`, `keySound_small_of_desc`: so at runK := a description's own decision
`F.run` and depth 0 the field follows from `KeyCore` at `F.run`: which `keyCoreAtDesc`
(Johnson/Desc/Sound/KeyAtDesc.lean) gives from one law for each block.

Limits. By unfolding alone: nothing is proved of any decision. That the description which runs is
laid as runK in what ships is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAtDesc
import Johnson.Flat.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → Fmt.View → Fmt.View → Fmt.View → Bool}
  {runP : X × RecFull → Fmt.View → Fmt.View → Fmt.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}

/-- **The field at the full size is `KeyCore`.** -/
theorem keySound_full_iff
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T) ↔
      KeyCore (lettersAt A (relationsAndEncodingOfClaims A E)) DK (front₀ rK) (join₀ rK) ByteArray.empty silK runK
        (2 ^ T.depthReqT) T.εs :=
  Iff.rfl

/-- **At a description's own decision and one leaf, the field follows from `KeyCore` at `F.run`.**
-/
theorem keySound_full_of_desc (F : FileDescription RecFull)
    {P' : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP F.run runP rK rP depthReq early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP F.run runP rK rP depthReq early salt K P')
    (h0 : T.depthReqT = 0)
    (h : KeyCore (lettersAt A (relationsAndEncodingOfClaims A E)) DK (front₀ rK) (join₀ rK) ByteArray.empty silK F.run 1
      T.εs) : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T) := by
  rw [keySound_full_iff, h0, pow_zero]
  exact h

end Full

section Small
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → Fmt.View → Fmt.View → Fmt.View → Bool}
  {runP : X × RecSmall → Fmt.View → Fmt.View → Fmt.View → Bool} {rK rP : RecSmall} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}

/-- **The field at the small size is `KeyCore`.** -/
theorem keySound_small_iff
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize A E DK DP runK runP rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtSmallSize T) ↔
      KeyCore (lettersAt A (relationsAndEncodingOfClaims A E)) DK (front₀ rK) (join₀ rK) ByteArray.empty silK runK
        (2 ^ T.depthReqT) T.εs :=
  Iff.rfl

/-- **The like at the small size.** -/
theorem keySound_small_of_desc (F : FileDescription RecSmall)
    {P' : (threeProtocolsWithFixedLinkAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP F.run runP rK rP depthReq early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize A E DK DP F.run runP rK rP depthReq early salt K P')
    (h0 : T.depthReqT = 0)
    (h : KeyCore (lettersAt A (relationsAndEncodingOfClaims A E)) DK (front₀ rK) (join₀ rK) ByteArray.empty silK F.run 1
      T.εs) : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtSmallSize T) := by
  rw [keySound_small_iff, h0, pow_zero]
  exact h

end Small

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.keySound_full_iff
#print axioms VerifiableInference.Desc.Sound.keySound_small_iff
#print axioms VerifiableInference.Desc.Sound.keySound_full_of_desc
#print axioms VerifiableInference.Desc.Sound.keySound_small_of_desc
