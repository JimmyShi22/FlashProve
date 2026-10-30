-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean: SOUNDNESS UNDER THE FILES' OWN POLICY, WITHOUT THE
PREMISE "exact match", WITH NO FURTHER HYPOTHESIS. OVER THE PROOF FILE'S ENTRY TESTS'
LIST OF FOURTEEN ROWS ALONE. Calls alone.

WHAT IT ADDS. `sound_of_verify_at` and the forms beside it end in `VerifiableInference.Sound` and
have the premise exact : pp.pol = Inst.Model.AcceptancePolicy.exact. That is a condition on the public files
which, BY READING (not checked here), `verify` DOES NOT TEST; a set of files in scope
can have another policy (the goals' own `zGap`: Ladder.lean's guard names its policy), and there
those theorems are silent. The goals' `SoundUnderPolicyAt` (Ladder.lean) has no such premise: AT
EVERY POLICY IN SCOPE it says: but with probability at most the error, nobody has an output accepted
that does not meet the files' policy at the weights that the description's extractor gives; for
every form of proof, every prover's side and every parser within n queries, at `VerifierAndGoals.soundnessErrorInQueries t n`. At
exact match "meets the policy" is "is the model's output": so `sound_of_atZ`
(Johnson/Goal/Skeleton/TopAtZ.lean) makes `Sound` from it.

  **`soundUnderPolicy_of_verify_at`**:
    `SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp` at one Z in scope, read as pp.
  **`soundUnderPolicyAt_of_verify`**: the goals' `SoundUnderPolicyAt (atSecondHashFunction theDescription) soundnessErrorInQueries`.
  **`g8bits_of_verify`**: the goal `G8bits theDescription` (Ladder/Bits.lean).
  `KeySoundAt Z` is `keySound_at_live_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean),
  `ProofSoundAt Z` is `proofSoundAt_of_verify` (Johnson/Goal/Skeleton/SoundOfVerifyMore.lean);
  `soundUnderPolicyAtZ_of_two` (Johnson/Goal/Skeleton/TopAtZ.lean) joins them.

Limits. CALLS ALONE: NOTHING IS PROVED IN THIS FILE. What it is worth is what the called theorems
and the definitions in the statements are worth.
The limits of Johnson/Goal/Skeleton/SoundOfVerifyAt.lean travel whole: where
`protocolDataWellFormed` says no, `verify` rejects everything and the statements hold for that reason; THAT
`protocolDataWellFormed` SAYS YES AT THE RELEASE'S FILES AS BYTES, AND THAT THE HONEST PROOF IS ACCEPTED THERE, IS
EVALUATED, NOT PROVED; the public files are fixed before the hash function is drawn; the second hash
is a fixed function; at the full size alone; the verifier with fourteen entry tests; beneath five of
the called theorems (the tenth and the twelfth kind's lemmas on the first chain, the key file's, the
one that gives the five rows, the shared chain's among them, and the one on the last chain's rest)
stand files on coding theory adapted from third-party Lean (lean/LIMITS.md, L15). What "meets the
policy" says at a policy other than exact match is the definition's (Policy/Front/MeetsPolicy.lean):
not read here. The error grows with n. Nothing on opening-form binding, correctness of extraction, completeness or hiding, nor on
anything else that names the honest committer or prover. By itself it bars nothing against a
committer who commits to weights under which every output meets the policy:
it means something only together with correctness of extraction at the same extractor and with whose commitment it is.

-/
import Johnson.Goal.Skeleton.SoundOfVerifyMore

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

/-- **SOUNDNESS UNDER THE FILES' POLICY AT ONE SET OF PUBLIC FILES, IN SCOPE, READ: NO "exact
match", NO FURTHER HYPOTHESIS.** -/
theorem soundUnderPolicy_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) :
    SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp :=
  soundUnderPolicyAtZ_of_two Z pp scope read (keySound_at_live_holds Z scope)
    (proofSoundAt_of_verify Z pp scope read)

/-- **The goals' `SoundUnderPolicyAt`, of the name itself, at `VerifierAndGoals.soundnessErrorInQueries`.** -/
theorem soundUnderPolicyAt_of_verify : SoundUnderPolicyAt (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries :=
  (soundUnderPolicyAt_iff_atZ _ _).2 fun Z pp scope read =>
    soundUnderPolicy_of_verify_at Z pp scope read

/-- **The goal `G8bits`, of the name itself.** -/
theorem g8bits_of_verify : G8bits theDescription :=
  ⟨verifierIsWithin, soundUnderPolicyAt_of_verify⟩

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundUnderPolicy_of_verify_at
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_verify
#print axioms VerifierAndGoals.AtTheName.g8bits_of_verify
