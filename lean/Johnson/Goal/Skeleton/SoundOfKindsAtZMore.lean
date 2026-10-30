-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfKindsAtZMore.lean: the siblings of `sound_of_kinds_at`
(Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean): at one set of public files Z, from the named
conditions
at that Z alone. Seven theorems; each is one call.
  `proofSoundAt_of_proofFileAt`: `ProofFileAt Z` where `protocolDataWellFormed` accepts gives `ProofSoundAt Z`
    (Johnson/Goal/Skeleton/TopAtZ.lean's `proofSound_at_of_proofFileAt`, under that name).
  `sound_at_of_proofFileAt`: `sound_at` at it.
  `proofSoundAt_of_kinds`: the proof file's conditions of `sound_of_kinds_at` give `ProofSoundAt Z`:
    that theorem's inner term under a name.
  `soundAndBinding_plain_of_proofFileAt`, `soundOpened_plain_of_proofFileAt`,
  **`soundAndBinding_plain_of_kinds_at`**, `soundOpened_plain_of_kinds_at`: `SoundAndBinding` and
    `SoundOpened` (VerifiableInference/Statements.lean) of the name's own system of record with the
    committer written in Lean beside the IOP, a placeholder that corresponds to no program of the
    release (`plainSystemAt OnBytes.secondHashFunction Z …`; Johnson/Goal/Skeleton/SoundAndBindingPlain.lean's
    "…_plain_at"), at `plainError` and at twice it.

Limits. No condition is shown to be met in this file. Elsewhere in this library `KeySoundAt Z` is a
theorem at every Z in scope (`keySound_at_live_holds`, Johnson/Goal/Conditions/KeyOpenHolds.lean),
and so is `ProofSoundAt Z`, which the other conditions yield, at every Z in scope whose files are
read (`proofSoundAt_of_verify`, SoundOfVerifyMore.lean; of the verifier with fourteen entry tests):
each under the live test's yes, which is evaluated at the release's files, not proved. What these
are worth is told in the head of SoundOfVerifyAt.lean. Those of SoundOfKindsAtZ.lean, TopAtZ.lean
and SoundAndBindingPlain.lean travel whole: the laws of the kinds, the five rows and `KeySoundAt Z`
are assumptions of soundness themselves; the statements that read openings are those of
VerifiableInference/Statements.lean, of `plainSystemAt`, not the goals' nearest forms; the committer
stands beside the description and is tied to no program.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.SoundOfKindsAtZ
import Johnson.Goal.Skeleton.SoundAndBindingPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- `ProofFileAt Z` where `protocolDataWellFormed` accepts gives `ProofSoundAt Z`. -/
theorem proofSoundAt_of_proofFileAt (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (h : protocolDataWellFormed (asDescriptionFiles Z) = true → ProofFileAt Z) : ProofSoundAt Z :=
  fun hl => proofSound_at_of_proofFileAt Z scope hl (h hl)

/-- **Soundness at one Z, from `KeySoundAt Z` and `ProofFileAt Z`.** -/
theorem sound_at_of_proofFileAt (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (h : protocolDataWellFormed (asDescriptionFiles Z) = true → ProofFileAt Z) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_at Z pp scope hr exact kS (proofSoundAt_of_proofFileAt Z scope h)

/-- `SoundAndBinding` (VerifiableInference/Statements.lean) of the name's system of record with the
committer written in Lean beside the IOP, a placeholder that corresponds to no program of the
release, at one Z, from `KeySoundAt Z` and `ProofFileAt Z`. -/
theorem soundAndBinding_plain_of_proofFileAt (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (h : protocolDataWellFormed (asDescriptionFiles Z) = true → ProofFileAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_at Z pp scope hr exact kS (proofSoundAt_of_proofFileAt Z scope h) b sample
    prove

/-- `SoundOpened` of it, at twice the error. -/
theorem soundOpened_plain_of_proofFileAt (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (h : protocolDataWellFormed (asDescriptionFiles Z) = true → ProofFileAt Z) (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_at Z pp scope hr exact kS (proofSoundAt_of_proofFileAt Z scope h) b sample
    prove

/-- **The proof file's conditions at Z give `ProofSoundAt Z`**: `sound_of_kinds_at`'s inner term. -/
theorem proofSoundAt_of_kinds (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), ProofKinds h) :
    ProofSoundAt Z :=
  proofSoundAt_of_proofFileAt Z scope fun hl =>
    proofFileAt_of_kinds Z scope hl (conds hl) (lastTyped hl) (kinds hl)

/-- **THE STATEMENT `SoundAndBinding` OF THE NAME's SYSTEM OF RECORD WITH THE COMMITTER WRITTEN IN
LEAN BESIDE THE IOP, A PLACEHOLDER THAT CORRESPONDS TO NO PROGRAM OF THE RELEASE, AT ONE SET OF
PUBLIC FILES, FROM THE NAMED CONDITIONS AT THESE FILES.** -/
theorem soundAndBinding_plain_of_kinds_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), ProofKinds h)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundAndBinding (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      plainError :=
  soundAndBinding_plain_at Z pp scope hr exact kS
    (proofSoundAt_of_kinds Z scope conds lastTyped kinds) b sample prove

/-- **`SoundOpened` of it**, at twice the error. -/
theorem soundOpened_plain_of_kinds_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), ProofKinds h)
    (b : (RAt OnBytes.secondHashFunction Z).LeafBody)
    (sample : RandomizedAlgorithm (CoinsAt OnBytes.secondHashFunction Z))
    (prove : ModelWeights (settingsOfRead pp) → CoinsAt OnBytes.secondHashFunction Z → List Token →
      List Token → RandomizedAlgorithm (theDescriptionO OnBytes.secondHashFunction).Form) :
    SoundOpened (plainSystemAt OnBytes.secondHashFunction Z (settingsOfRead pp) b sample prove)
      fun t => 2 * plainError t :=
  soundOpened_plain_at Z pp scope hr exact kS
    (proofSoundAt_of_kinds Z scope conds lastTyped kinds) b sample prove

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_proofFileAt
#print axioms VerifierAndGoals.AtTheName.sound_at_of_proofFileAt
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_proofFileAt
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_proofFileAt
#print axioms VerifierAndGoals.AtTheName.proofSoundAt_of_kinds
#print axioms VerifierAndGoals.AtTheName.soundAndBinding_plain_of_kinds_at
#print axioms VerifierAndGoals.AtTheName.soundOpened_plain_of_kinds_at
