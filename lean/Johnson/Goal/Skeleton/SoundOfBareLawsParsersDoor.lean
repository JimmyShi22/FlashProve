-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/SoundOfBareLawsParsersDoor.lean: Soundness at one set of public files for
every form of proof, every prover's side and every parser that asks at most n queries, at the error
`VerifierAndGoals.soundnessErrorInQueries t n`, from the conditions of `sound_of_bare_laws_door_at`: kinds alone (every kind's
law a bare field). One call. Over the entry tests with fourteen rows alone; it speaks of the
verifier with fourteen entry tests.

What it adds over the top at the description's own parser. `sound_of_bare_laws_door_at` ends in
`Sound (systemOfRecord (atSecondHashFunction theDescription) Z …)` at `VerifierAndGoals.soundnessErrorInQueries t 1`: `systemOfRecord` is the
case Form := the description's own, parse := its own parser, n := 1 (so
Johnson/Goal/Skeleton/TopAtZ.lean makes `sound_at` from `sound_of_atZ`). Here Form, prove, parse and
n are letters under "for all": `Sound` (VerifiableInference/Statements.lean) of `system (atSecondHashFunction
theDescription) Z (settingsOfRead pp) Form prove parse` at `VerifierAndGoals.soundnessErrorInQueries t n`, for every parse with
`parse.Within n`. The verifier behind the parser is the same.

  **`sound_of_bare_laws_door_parsers_at`**: by `sound_of_atZ` at `soundUnderPolicyAtZ_of_two`
    (Johnson/Goal/Skeleton/TopAtZ.lean), at `KeySoundAt Z` (a theorem: `keySound_at_live_holds`) and
    `ProofSoundAt Z` (`proofSoundAt_of_bare_laws_door`).

Limits. It pays no law and no condition. kinds is the whole list of the kinds' laws. Elsewhere in
this library it is not left open: kinds is a theorem under every head (`kindsLaws_at_head`,
KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (at secondHashFunction,
with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at other files: evaluated, not
proved). What that is worth is told in the head of SoundOfVerifyAt.lean, whose limits hold of every
theorem here once the premise is struck. The error grows with n: at a parser that asks many queries
it says little. At one Z, in scope, read, at the exact-match policy. `Sound` alone: nothing on
binding, completeness or zero knowledge.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfBareLawsDoorNearest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FOR EVERY FORM, EVERY PROVER's SIDE AND EVERY PARSER
WITHIN n QUERIES, AT `VerifierAndGoals.soundnessErrorInQueries t n`.** -/
theorem sound_of_bare_laws_door_parsers_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theDescription).Rand → List Token →
      List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (n : ℕ) (hn : parse.Within n) :
    VerifiableInference.Sound
      (system (atSecondHashFunction theDescription) Z (settingsOfRead pp) Form prove parse)
      fun t => VerifierAndGoals.soundnessErrorInQueries t n :=
  sound_of_atZ _ _ Z pp
    (soundUnderPolicyAtZ_of_two Z pp scope read (keySound_at_live_holds Z scope)
      (proofSoundAt_of_bare_laws_door Z pp scope read kinds))
    exact Form prove parse n hn

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.sound_of_bare_laws_door_parsers_at
