-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfVerifyMore.lean: MORE FORMS OVER THE TOP WITH NO FURTHER HYPOTHESIS
(`sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean). OVER THE LIST OF FOURTEEN
ROWS OF THE PROOF FILE'S ENTRY TESTS ALONE.

The theorems of Johnson/Goal/Skeleton/SoundOfBareLawsDoorNearest.lean and
SoundOfBareLawsParsersDoor.lean with their one premise kinds struck: it is proved, as in
`sound_of_verify_at`, by `kindsLaws_at_head` (Johnson/Goal/Skeleton/KindsLawsAtHead.lean, which says
field by field which theorem proves what).

AT ONE SET OF PUBLIC FILES Z, in scope, read as pp:
  `proofSoundAt_of_verify`: `ProofSoundAt Z`.
  **`sound_of_verify_parsers_at`** (with exact match): `VerifiableInference.Sound` of
    `system (atSecondHashFunction theDescription) Z (settingsOfRead pp) Form prove parse` at `VerifierAndGoals.soundnessErrorInQueries t n`,
    for every form of proof, every prover's side and every parser with `parse.Within n`.
    `sound_of_verify_at` is the case of the description's own form and parser, n := 1.
  **`soundAndBinding_level_digits_of_verify_at`**, **`soundOpened_level_digits_of_verify_at`** (with
    exact match): of the closed stand-in `theWideDigits`, at `levelError` and at twice it.
OVER ALL SETS IN SCOPE:
  **`nearestSoundAndBinding_level_digits_of_verify`**,
  **`nearestSoundOpened_level_digits_of_verify`**: the goals' two
    nearest forms that read openings, at `theWideDigits`, at `levelError` and at twice it.
  (`NearestSound theDescription` is `nearestSound_of_verify` in SoundOfVerifyAt.lean. The pair at
  `theBound K` is not stated: there the clause on opening-form binding is without content.)

Limits. CALLS ALONE: NOTHING IS PROVED IN THIS FILE. What it is worth is what the called theorems
and the definitions in the statements are worth.
The head under which the sixteen laws (fourteen lemmas with content: the fields k14
and k15 are idle, these kinds having no place on the first chain) are had is BUILT inside the top
from the scope, the reading, the yes of `protocolDataWellFormed` and `rowsRead`; where `protocolDataWellFormed` says no, `verify`
rejects everything and the statements hold for that reason. THAT `protocolDataWellFormed` SAYS YES AT THE RELEASE'S
FILES AS BYTES, AND THAT THE HONEST PROOF IS ACCEPTED THERE, IS EVALUATED, NOT PROVED. THE FOUR THAT
READ OPENINGS ARE NOT OF `theDescription`, whose own committer is hollow: they are of a stand-in
that keeps the verifier and the extractor and ADDS a committer tied to no program (by reading; that
the extractor is kept is a theorem of Johnson/Goal/SameExtractorWide.lean, which this file
does not import); the limits of Johnson/Goal/TopAtZBinding.lean and BindingOfCoreLevel.lean travel
whole. The error of the form for every parser grows with n. No completeness, nothing on hiding. One
set of public files at a time, fixed before the hash function is drawn; the second hash is a fixed
function; at the full size alone; the verifier with fourteen entry tests. Beneath five of the called
theorems (the tenth and the twelfth kind's lemmas on the first chain, the key file's, the one that
gives the five rows, the shared chain's among them, and the one on the last chain's rest) stand
files on coding theory adapted from third-party Lean (lean/LIMITS.md, L15).

-/
import Johnson.Goal.Skeleton.SoundOfVerifyAt
import Johnson.Goal.Skeleton.SoundOfBareLawsDoorNearest
import Johnson.Goal.Skeleton.SoundOfBareLawsParsersDoor

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

/-! ## At one set of public files -/

/-- **`ProofSoundAt Z`, at a Z in scope whose files are read: no further hypothesis.** -/
theorem proofSoundAt_of_verify (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) : ProofSoundAt Z :=
  proofSoundAt_of_bare_laws_door Z pp scope read fun _ _ _ _ _ h => kindsLaws_at_head h

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FOR EVERY FORM, EVERY PROVER's SIDE AND EVERY PARSER
WITHIN n QUERIES, AT `VerifierAndGoals.soundnessErrorInQueries t n`: NO FURTHER HYPOTHESIS.** -/
theorem sound_of_verify_parsers_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theDescription).Rand → List Token →
      List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (n : ℕ) (hn : parse.Within n) :
    VerifiableInference.Sound
      (system (atSecondHashFunction theDescription) Z (settingsOfRead pp) Form prove parse)
      fun t => VerifierAndGoals.soundnessErrorInQueries t n :=
  sound_of_bare_laws_door_parsers_at Z pp scope read exact (fun _ _ _ _ _ h => kindsLaws_at_head h)
    Form prove parse n hn

/-- **`SoundAndBinding` at Z, of the stand-in `theWideDigits`, at `levelError`: no further
hypothesis.** -/
theorem soundAndBinding_level_digits_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundAndBinding (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) levelError :=
  soundAndBinding_level_digits_of_bare_laws_door_at Z pp scope read exact
    fun _ _ _ _ _ h => kindsLaws_at_head h

/-- **`SoundOpened`**, at twice that error. -/
theorem soundOpened_level_digits_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) :
    SoundOpened (systemOfRecord (atSecondHashFunction theWideDigits) Z (settingsOfRead pp)) fun t =>
      2 * levelError t :=
  soundOpened_level_digits_of_bare_laws_door_at Z pp scope read exact
    fun _ _ _ _ _ h => kindsLaws_at_head h

/-! ## Over all sets of public files in scope -/

/-- **The goals' `NearestSoundAndBinding` at the stand-in `theWideDigits`, at `levelError`.** -/
theorem nearestSoundAndBinding_level_digits_of_verify :
    NearestSoundAndBinding theWideDigits levelError :=
  nearestSoundAndBinding_level_digits_of_bare_laws_door
    fun _ _ _ _ _ _ _ h => kindsLaws_at_head h

/-- **And `NearestSoundOpened`**, at twice that error. -/
theorem nearestSoundOpened_level_digits_of_verify :
    NearestSoundOpened theWideDigits fun t => 2 * levelError t :=
  nearestSoundOpened_level_digits_of_bare_laws_door
    fun _ _ _ _ _ _ _ h => kindsLaws_at_head h

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_verify
#print axioms VerifierAndGoals.AtTheName.sound_of_verify_parsers_at
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_level_digits_of_verify_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_level_digits_of_verify_at
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_level_digits_of_verify
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_level_digits_of_verify
