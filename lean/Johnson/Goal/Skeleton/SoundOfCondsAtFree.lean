-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/SoundOfCondsAtFree.lean: soundness at one set of public files Z from the
kinds' own named conditions AT THE CLOSED FILLING `P5J.AtMgA.free` (Johnson/P5J/FreeAll.lean).

  `kindsLaws_at_free`: `KindsConds h h.free` → `KindsLaws h h.free`: the three lists' heads are
    theorems at that filling (`AtMgA.free_q₁`, `free_q₂`, `free_q₃`).
  `sound_of_conds_at_free`: `sound_of_kinds_at_free`
    (Johnson/Goal/Skeleton/SoundOfKindsAtFree.lean) with `KindsConds h h.free` in
    `KindsLaws h h.free`'s place; every other token of the statement is that theorem's.

Limits. TWO CALLS: THEY PAY NOTHING. NO CONDITION IS SHOWN TO BE MET AT ANY Z: THE THEOREM MAY BE
EMPTY. The limits of the files that are called stand, Johnson/Goal/Skeleton/KindsOfConds.lean's
first. BEFORE THIS IS QUOTED, READ Johnson/Goal/Skeleton/KindsOfConds.lean's HEAD: some of
`KindsConds`' fields are the bare law of a kind, and some kinds' conditions hold an unpaid part of
the conclusion as a field: "named conditions" does not mean "conditions that are smaller than the
laws".

-/
import Johnson.Goal.Skeleton.KindsLawsOfConds
import Johnson.Goal.Skeleton.SoundOfKindsAtFree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open OnBytes.Flat
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The top's sixteen fields at the closed filling.** -/
theorem kindsLaws_at_free
    {h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x}
    (C : KindsConds h h.free) : KindsLaws h h.free :=
  kindsLaws_of_conds h.free_q₁ h.free_q₂ h.free_q₃ C

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE KINDS' OWN NAMED CONDITIONS AT CLOSED
TERMS.** Some of these "conditions" are bare laws or hold a part of the conclusion: see
KindsOfConds.lean's head. No condition is shown to be met. -/
theorem sound_of_conds_at_free (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        KindsConds h h.free)
    (five : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x),
        h.Five h.free (depthZ Z)) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_kinds_at_free Z pp scope read exact kS conds lastTyped
    (fun hl Zp Np cF x h => kindsLaws_at_free (kinds hl Zp Np cF x h)) five

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.kindsLaws_at_free
#print axioms VerifierAndGoals.AtTheName.sound_of_conds_at_free
