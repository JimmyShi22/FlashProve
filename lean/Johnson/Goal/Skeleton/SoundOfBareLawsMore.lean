-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Goal/Skeleton/SoundOfBareLawsMore.lean: Two more conclusions from the conditions of the
top with every kind's law a bare field. Where Johnson/Goal/Skeleton/SoundOfKindsAtFree.lean
(`sound_of_kinds_at_free`) concludes `Sound` (VerifiableInference/Statements.lean) at one set of
public files Z, the same conditions give `SoundAndBinding` and `SoundOpened`. Calls alone.

The conditions, at one Z in scope whose files are read: owed (`At.CondsOwed Z`: the one reading
condition), kinds (`KindsLaws h h.free` under every head: each kind's law, whole, by name), five
(`h.Five h.free (depthZ Z)` under every head). Each is asked only where the verifier's live test
accepts. Paid inside, as in the top itself: `KeySoundAt Z` (`keySound_at_live_holds`), `At.Conds Z`
(`conds_of_laid`), the last chain's typing (`H2K12.lastTypedAt_of_live`).

  `proofSoundAt_of_bare_laws_five`: they give `ProofSoundAt Z`.
  **`soundAndBinding_plain_of_bare_laws_five_at`**, **`soundOpened_plain_of_bare_laws_five_at`**:
    `SoundAndBinding` at the error `plainError`, and `SoundOpened` at twice it, of the
    name's system of record with the committer written in Lean beside the IOP, a placeholder that
    corresponds to no program of the release (`plainSystemAt`,
    Johnson/Goal/Skeleton/SoundAndBindingPlain.lean), at that Z.
  `proofSound_of_bare_laws_five`: the conditions at every Z in scope give `ProofSound`.
  `nearestSoundAndBinding_of_bare_laws_five`, `nearestSoundOpened_of_bare_laws_five`: then the
    goals' own `NearestSoundAndBinding` at `levelError` and `NearestSoundOpened` at twice it, at the
    closed stand-in `theWideDigits` (Johnson/Goal/Skeleton/TopOfTwoMore.lean).

Limits. It pays no law and no condition. kinds is the whole list of the kinds' laws. Elsewhere in
this library none of the three conditions is left open: kinds is a theorem under every head
(`kindsLaws_at_head`, KindsLawsAtHead.lean; that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved); owed follows from the live test's yes (`P5J.owed_of_live`,
OwedOfLive.lean), because that check is a fourteenth entry test of `verify`: without that test it is
not proved; and five is a theorem where the live test accepts
(`five_of_head_alone`, SoundOfBareLawsHeadNearest.lean). What these are worth is told in the head of
SoundOfVerifyAt.lean, whose limits hold of every theorem here once the premises are struck. The
first pair is no `NearestSoundAndBinding` of a description: the committer stands beside the
description, not in it: it is written in Lean and tied to no program of the release. The second pair
asks the conditions at every Z in scope, with "the files are read" among them, and speaks of the
stand-in, not of `theDescription`. Nothing on completeness; nothing on zero knowledge.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfKindsAtFree
import Johnson.Goal.Skeleton.SoundOfKindsAtZMore
import Johnson.Goal.Skeleton.TopOfTwoMore
import Johnson.Goal.Skeleton.CondsOfLaid
import Johnson.Loose.H2K12.LastTypedOfLaid
import Johnson.Goal.Conditions.KeyOpenHolds

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

/-- **The conditions at Z give `ProofSoundAt Z`.** -/
theorem proofSoundAt_of_bare_laws_five (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (five : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z)) :
    ProofSoundAt Z :=
  proofSoundAt_of_kinds Z scope (fun hl => conds_of_laid scope hl read (owed hl))
    (fun hl => H2K12.lastTypedAt_of_live Z scope hl) fun hl Zp Np cF x h =>
      proofKinds_at_free h (kinds hl Zp Np cF x h) (five hl Zp Np cF x h)

/-- **THE STATEMENT `SoundAndBinding` OF THE NAME's SYSTEM OF RECORD WITH THE COMMITTER WRITTEN IN
LEAN BESIDE THE IOP, A PLACEHOLDER THAT CORRESPONDS TO NO PROGRAM OF THE RELEASE, AT ONE SET OF
PUBLIC FILES, EVERY KIND's LAW A BARE FIELD.** -/
theorem soundAndBinding_plain_of_bare_laws_five_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (five : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z))
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_at Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_bare_laws_five Z pp scope read owed kinds five) b sample prove

/-- **`SoundOpened` of it**, at twice the error. -/
theorem soundOpened_plain_of_bare_laws_five_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact)
    (owed : protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (five : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z))
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_at Z pp scope read exact (keySound_at_live_holds Z scope)
    (proofSoundAt_of_bare_laws_five Z pp scope read owed kinds five) b sample prove

/-- **The conditions at every Z in scope give `ProofSound`.** -/
theorem proofSound_of_bare_laws_five
    (H : ∀ Z : VerifierAndGoals.PublicFiles, InScope Z = true → ∃ pp : Inst.Model.ScalesAndPolicy, readFiles Z = .ok pp ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          KindsLaws h h.free) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          h.Five h.free (depthZ Z))) :
    ProofSound :=
  proofSound_iff_at.2 fun Z scope => by
    obtain ⟨pp, read, owed, kinds, five⟩ := H Z scope
    exact proofSoundAt_of_bare_laws_five Z pp scope read owed kinds five

/-- **The goals' `NearestSoundAndBinding`, at the closed stand-in and the written error, from the
conditions at every Z in scope.** -/
theorem nearestSoundAndBinding_of_bare_laws_five
    (H : ∀ Z : VerifierAndGoals.PublicFiles, InScope Z = true → ∃ pp : Inst.Model.ScalesAndPolicy, readFiles Z = .ok pp ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          KindsLaws h h.free) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          h.Five h.free (depthZ Z))) :
    NearestSoundAndBinding theWideDigits levelError :=
  soundAndBinding_level_digits_of_two
    (keySound_iff_at.2 fun Z scope => keySound_at_live_holds Z scope)
    (proofSound_of_bare_laws_five H)

/-- **And `NearestSoundOpened`**, at twice the written error. -/
theorem nearestSoundOpened_of_bare_laws_five
    (H : ∀ Z : VerifierAndGoals.PublicFiles, InScope Z = true → ∃ pp : Inst.Model.ScalesAndPolicy, readFiles Z = .ok pp ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → At.CondsOwed Z) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          KindsLaws h h.free) ∧
      (protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
        (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
          h.Five h.free (depthZ Z))) :
    NearestSoundOpened theWideDigits fun t => 2 * levelError t :=
  soundOpened_level_digits_of_two
    (keySound_iff_at.2 fun Z scope => keySound_at_live_holds Z scope)
    (proofSound_of_bare_laws_five H)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_bare_laws_five
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_bare_laws_five_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_bare_laws_five_at
#print axioms VerifierAndGoals.AtTheName.proofSound_of_bare_laws_five
#print axioms VerifierAndGoals.AtTheName.nearestSoundAndBinding_of_bare_laws_five
#print axioms VerifierAndGoals.AtTheName.nearestSoundOpened_of_bare_laws_five
