-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/SoundOfBareLawsHeadNearest.lean: More conclusions from the two conditions
of `sound_of_bare_laws_head_at` (Johnson/Goal/Skeleton/SoundOfBareLawsHead.lean): owed (the one
reading condition) and kinds (every kind's law a bare field). The test `coreAt` on the public files,
third in Johnson/Goal/Skeleton/SoundOfBareLawsCore.lean, is not among them: another file pays what
it pays from the head alone (`lastLeft_at_head_alone`, Johnson/P2LawR/LastLeftAlone.lean). The
theorems of Johnson/Goal/Skeleton/SoundOfBareLawsCoreMore.lean [not in this library] and
SoundOfBareLawsCoreNearest.lean [not in this library] with that premise struck. Calls alone.

At one set of public files Z, in scope, read, at the exact-match policy:
  `five_of_head_alone`: `h.Five h.free (depthZ Z)` under every head, where the live test accepts:
    the top's own inner term, under a name.
  `proofSoundAt_of_bare_laws_head`: the two conditions give `ProofSoundAt Z`.
  **`soundAndBinding_plain_of_bare_laws_head_at`**, **`soundOpened_plain_of_bare_laws_head_at`**:
    the two statements of VerifiableInference/Statements.lean that read openings, of the name's
    system of record with the committer written in Lean beside the IOP, a placeholder that
    corresponds to no program of the release (`plainSystemAt`), at `plainError` and at twice it.
Over all sets in scope, the two conditions asked at every one where the live test accepts:
  **`nearestSound_of_bare_laws_head`**: `NearestSound theDescription` at `VerifierAndGoals.soundnessErrorInQueries t 1`: of the
    name itself.
  `nearestSoundAndBinding_bound_of_bare_laws_head`, `nearestSoundOpened_bound_of_bare_laws_head`: at
    the stand-in `theBound K`, for every K : `TheCoins`, at `levelError` and at twice it. At
    `theBound K` the clause on opening-form binding is without content (its bound is 0):
    whoever cites this pair cites it with that sentence.
  `nearestSoundAndBinding_digits_of_bare_laws_head`, `nearestSoundOpened_digits_of_bare_laws_head`:
    at the closed stand-in `theWideDigits`, at
    `joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)` and at twice it.

What the form over all sets costs. Where one condition fails at one set in scope at which the live
test accepts, the five nearest forms say nothing at all, at any set; the statements at one Z still
speak at each of the other sets.

Limits. They pay no law and no condition. kinds is the whole list of the kinds' laws. Elsewhere in
this library neither condition is left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved), and owed follows from the live test's yes (`P5J.owed_of_live`,
OwedOfLive.lean), because that check is a fourteenth entry test of `verify`: without that test it is
not proved. What these are worth is told in the head of
SoundOfVerifyAt.lean, whose limits hold of every theorem here once the premises are struck.
`plainSystemAt` has the written committer in the place of the description's own, which is hollow;
that committer is tied to no program. The four nearest forms that read openings are at stand-ins
that keep `theDescription`'s verifier and add a committer, not of `theDescription`: the limits of
Johnson/Goal/TopAtZBinding.lean travel whole. Nothing on completeness; nothing on zero knowledge.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfBareLawsHead
import Johnson.Goal.Skeleton.SoundOfBareLawsMore
import Johnson.Goal.TopAtZBinding

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

/-- The five fitting conditions at the closed filling, from the head alone. -/
theorem five_of_head_alone (Z : VerifierAndGoals.PublicFiles) :
    protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z) :=
  fun hl _ _ _ _ h => five_at_free2_laid2 h hl h.lastLeft_at_head_alone

/-- **The two conditions at Z give `ProofSoundAt Z`.** -/
theorem proofSoundAt_of_bare_laws_head (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    ProofSoundAt Z :=
  proofSoundAt_of_bare_laws_five Z pp scope read owed kinds (five_of_head_alone Z)

/-- **THE STATEMENT `SoundAndBinding` OF THE NAME's SYSTEM OF RECORD WITH THE COMMITTER WRITTEN IN
LEAN BESIDE THE IOP, A PLACEHOLDER THAT CORRESPONDS TO NO PROGRAM OF THE RELEASE, AT ONE SET OF
PUBLIC FILES, FROM THE KINDS' BARE LAWS AND ONE TEST ON THE PUBLIC FILES.** -/
theorem soundAndBinding_plain_of_bare_laws_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_of_bare_laws_five_at Z pp scope read exact owed kinds
    (five_of_head_alone Z) b sample prove

/-- **`SoundOpened` of it**, at twice the error. -/
theorem soundOpened_plain_of_bare_laws_head_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_of_bare_laws_five_at Z pp scope read exact owed kinds
    (five_of_head_alone Z) b sample prove

/-! ## Over all sets of public files in scope -/

/-- **THE GOALS' NEAREST FORM OF SOUNDNESS, OF THE NAME ITSELF, FROM THE KINDS' BARE LAWS AND ONE
TEST ON THE PUBLIC FILES AT EVERY Z.** -/
theorem nearestSound_of_bare_laws_head
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  fun Z pp scope read ex =>
    sound_of_bare_laws_head_at Z pp scope read ex (owed Z scope) (kinds Z scope)

/-- **`NearestSoundAndBinding` at the stand-in `theBound K`, at the written error.** -/
theorem nearestSoundAndBinding_bound_of_bare_laws_head (K : TheCoins)
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundAndBinding (theBound K) levelError :=
  fun Z pp scope read ex =>
    soundAndBinding_level_at K Z pp scope read ex (keySound_at_live_holds Z scope)
      (proofSoundAt_of_bare_laws_head Z pp scope read (owed Z scope) (kinds Z scope))

/-- **`NearestSoundOpened` at it**, at twice the written error. -/
theorem nearestSoundOpened_bound_of_bare_laws_head (K : TheCoins)
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundOpened (theBound K) fun t => 2 * levelError t :=
  fun Z pp scope read ex =>
    soundOpened_level_at K Z pp scope read ex (keySound_at_live_holds Z scope)
      (proofSoundAt_of_bare_laws_head Z pp scope read (owed Z scope) (kinds Z scope))

/-- **`NearestSoundAndBinding` at the closed stand-in `theWideDigits`.** -/
theorem nearestSoundAndBinding_digits_of_bare_laws_head
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundAndBinding theWideDigits
      (joinError soundnessErrorInQueries fun t => epsBind honestBudget (t + 2)) := by
  unfold theWideDigits
  exact fun Z pp scope read ex =>
    soundAndBinding_at digitCoins digitWide Z pp scope read ex (keySound_at_live_holds Z scope)
      (proofSoundAt_of_bare_laws_head Z pp scope read (owed Z scope) (kinds Z scope))

/-- **`NearestSoundOpened` at it**, at twice that error. -/
theorem nearestSoundOpened_digits_of_bare_laws_head
    (owed : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free) :
    NearestSoundOpened theWideDigits fun t =>
      2 * joinError soundnessErrorInQueries (fun t => epsBind honestBudget (t + 2)) t := by
  unfold theWideDigits
  exact fun Z pp scope read ex =>
    soundOpened_at digitCoins digitWide Z pp scope read ex (keySound_at_live_holds Z scope)
      (proofSoundAt_of_bare_laws_head Z pp scope read (owed Z scope) (kinds Z scope))

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.five_of_head_alone
#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_bare_laws_head_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_bare_laws_head_at
#print axioms VerifierAndGoals.AtTheName.nearestSound_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_bound_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_bound_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_digits_of_bare_laws_head
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_digits_of_bare_laws_head
