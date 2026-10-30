-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/TopOfThreeBinding.lean: the statements `SoundAndBinding` and `SoundOpened`
(VerifiableInference/Statements.lean), in their nearest forms, from three unproved hypotheses. They
are stated of two stand-in descriptions, not of `VerifierAndGoals.theDescription`.

"Nearest form" (Ladder/Package.lean): the statement at the public files in scope whose policy is
exact match.
The prover writes three files: a key file, an entry file and a proof file. `KeySound`, `EntrySound`
and `ProofSound` (Johnson/Goal/Conditions/RowsAtTheRecord.lean) are one hypothesis on each.
Johnson/Goal/TopOfThree.lean derives `NearestSound` for `theDescription` from them. The two
statements here also speak of the honest committer. `theDescription`'s own is a placeholder, without opening-form binding, so
they are stated of two descriptions that keep its verifier and add a committer and an extractor:
  `theBound K` (Johnson/Goal/Conditions/BindsAtThe.lean), for every K : `TheCoins`;
  `theWide K W` (Johnson/Goal/Conditions/WideAtThe.lean), for every K and W : `WideCoins K`: there
    the number of the committer's coins is a free variable.
The binding part needs no further hypothesis (`G9bits_at`, Johnson/Goal/Description/AtBound.lean;
`bindLaws_wide`, WideAtThe.lean). See the limits below for what it binds. The theorems:
  `top_soundAndBinding_of_three`: at `theWide K W`, at the error
    `joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)`. `top_soundOpened_of_three`: at twice it.
  `g8bits_bound_of_three`: the goal `G8bits` (Ladder/Bits.lean: soundness under the files' policy at
    the error `soundnessErrorInQueries`) at `theBound K`.
  `top_soundAndBinding_level_of_three`: at `theBound K`, at `levelError` (Ladder/PackageBits.lean).
    `top_soundOpened_level_of_three`: at twice it.
  `the_description_is`: `atSecondHashFunction theDescription`, of which the goals speak, is `flashProveDescription`, that is
    `descriptionOfDataOnBytes flashProveData`.
  `same_verifier_bound`, `same_verifier_wide`: the verifier of both stand-ins is that of `flashProveDescription`.
  `same_extractor_bound`: the extractor of `theBound K` is that of `atSecondHashFunction theDescription`.

Limits. None of the three hypotheses is proved in this file, and each is itself an assumption of
soundness; where they are proved, and how far: the head of Johnson/Goal/TopOfThree.lean,
limit (1).
The statements are not about `theDescription` itself. The limits of BindsAtThe.lean and
WideAtThe.lean hold here: at `theBound K` the committer samples no randomness, so opening-form binding speaks of
one setting of its coins, fixed in K before the hash function is drawn; no theorem ties this
committer to the release's program that commits; nothing is said on hiding, or on completeness with
this committer. That the extractor of `theWide K W` is `theDescription`'s is not shown here; it is
`same_extractor_wide` (Johnson/Goal/SameExtractorWide.lean). The security
level that `soundnessErrorInQueries` and `levelError` give is stated in Ladder/Bits.lean and Ladder/PackageBits.lean.

-/
import Johnson.Goal.TopOfThree
import Johnson.Goal.Conditions.WideBitsAtThe
import Johnson.Goal.Description.Asks57
import Ladder.PackageBits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

variable (K : TheCoins) (W : WideCoins K)

/-- **The three hypotheses give `SoundAndBinding`, in its nearest form, at `theWide K W`.** -/
theorem top_soundAndBinding_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    NearestSoundAndBinding (theWide K W) (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_theWide_bits K W kS eS pS

/-- **The three hypotheses give `SoundOpened`, in its nearest form, at `theWide K W`.** -/
theorem top_soundOpened_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    NearestSoundOpened (theWide K W) fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_theWide_bits K W kS eS pS

/-- The three hypotheses give `G8bits` at `theBound K`. -/
theorem g8bits_bound_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    G8bits (theBound K) :=
  G8bits_theBound K he2_the kS eS pS

/-- **The three hypotheses give `SoundAndBinding`, in its nearest form, at `theBound K`, at
`levelError`.** -/
theorem top_soundAndBinding_level_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    NearestSoundAndBinding (theBound K) levelError :=
  nearestSoundAndBinding_of_bits (theBound K) (g8bits_bound_of_three K kS eS pS) (G9bits_at K)

/-- **The three hypotheses give `SoundOpened`, in its nearest form, at `theBound K`, at twice
`levelError`.** -/
theorem top_soundOpened_level_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    NearestSoundOpened (theBound K) fun t => 2 * levelError t :=
  nearestSoundOpened_of_bits (theBound K) (g8bits_bound_of_three K kS eS pS) (G9bits_at K)

/-- `atSecondHashFunction theDescription`, of which the goals speak, is `flashProveDescription`, that is `descriptionOfDataOnBytes flashProveData`. -/
theorem the_description_is : atSecondHashFunction theDescription = flashProveDescription := theDescription_eq

/-- The verifier of `theBound K` is that of `flashProveDescription`. -/
theorem same_verifier_bound (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theBound K o) Z parse = verify flashProveDescription Z parse := verify_theBound K o Z parse

section
/- Keep `descriptionOfDataOnBytes` folded here: unfolding it exceeds Lean's limit of heartbeats. -/
attribute [local irreducible] descriptionOfDataOnBytes

/-- The verifier of `theWide K W` is that of `flashProveDescription`. -/
theorem same_verifier_wide (o : SecondHashFunctionType) (Z : PublicFiles) {Form : Type} (parse : Parser flashProveDescription Z Form) :
    verify (theWide K W o) Z parse = verify flashProveDescription Z parse := verify_theWide K W o Z parse

end

/-- The extractor of `theBound K` is that of `atSecondHashFunction theDescription`. -/
theorem same_extractor_bound (o : SecondHashFunctionType) :
    (theBound K o).extractor = (atSecondHashFunction theDescription).extractor := one_extractor K o

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_of_three
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_of_three
#print axioms VerifierAndGoals.AtTheName.g8bits_bound_of_three
#print axioms VerifierAndGoals.AtTheName.top_soundAndBinding_level_of_three
#print axioms VerifierAndGoals.AtTheName.top_soundOpened_level_of_three
#print axioms VerifierAndGoals.AtTheName.the_description_is
#print axioms VerifierAndGoals.AtTheName.same_verifier_bound
#print axioms VerifierAndGoals.AtTheName.same_verifier_wide
#print axioms VerifierAndGoals.AtTheName.same_extractor_bound
