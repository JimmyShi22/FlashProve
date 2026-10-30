-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfKindsAtFree.lean: `sound_of_kinds_at_free`: `sound_of_kinds_at`
(Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean) with the tower's free letters laid at a closed term.

Why. `ProofKinds h` (Johnson/Goal/Skeleton/SoundOfKindsTop.lean) says "there is a filling 𝔏 of the
tower's free letters at which the sixteen fields and the five rows hold": the filling is the payer's
choice. Another file has one filling written as a term of the head alone: `P5J.AtMgA.free`
(Johnson/P5J/FreeAll.lean). Here the conditions are asked at that term.
  `proofKinds_at_free`: `KindsLaws h h.free` and `h.Five h.free (depthZ Z)` give `ProofKinds h`: the
    four equations on the filling are that file's lemmas.
  `sound_of_kinds_at_free`: as `sound_of_kinds_at`, with these two in the place of `ProofKinds h`.
So no "there is" is left in a hypothesis; the letters Zp Np cF x are bound by "for all" under the
head `P5J.AtMgA`, which holds of at most one such four by reading (not spent here).

Limits. Those of the files that are called. NO CONDITION IS SHOWN TO BE MET IN THIS FILE. Elsewhere
in this library kinds and five are had at this filling, under every head (a head is proved at a
written copy alone, not the release's files (see `headMember_zFull`)): kinds by `kindsLaws_at_head`
(KindsLawsAtHead.lean), five by `five_of_head_alone` (SoundOfBareLawsHeadNearest.lean); the other
three, which stand at Z, on the road of `sound_of_verify_at` (SoundOfVerifyAt.lean), whose head says
what these are worth. A law that is proved at another filling does not pay a field here.

-/
import Johnson.Goal.Skeleton.SoundOfKindsAtZ
import Johnson.P5J.FreeAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The proof file's conditions under one head, from the same at the closed filling.** -/
theorem proofKinds_at_free (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (L : KindsLaws h h.free) (V : h.Five h.free (depthZ Z)) : ProofKinds h :=
  ⟨h.free, h.toAtMg.dIdle, h.free_rP, h.free_q₁, h.free_q₂, h.free_q₃, L, V⟩

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, THE CONDITIONS AT CLOSED TERMS.** -/
theorem sound_of_kinds_at_free (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsLaws h h.free)
    (five : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z)) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_kinds_at Z pp scope read exact kS conds lastTyped fun hl Zp Np cF x h =>
    proofKinds_at_free h (kinds hl Zp Np cF x h) (five hl Zp Np cF x h)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.proofKinds_at_free
#print axioms VerifierAndGoals.AtTheName.sound_of_kinds_at_free
