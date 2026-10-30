-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsLawsOfConds.lean: the top's hypothesis "one law for each kind of
sub-protocol" (`KindsLaws`, Johnson/Goal/Skeleton/SoundOfKindsTop.lean) from the kinds' own named
conditions (`KindsConds`, Johnson/Goal/Skeleton/KindsOfConds.lean), and soundness at one set of
public files Z with `KindsConds` in `KindsLaws`' place.


  `kindsLaws_of_conds`: the three lists' heads are 𝔏's → `KindsConds h 𝔏` → `KindsLaws h 𝔏`.
  `ProofConds h`: `ProofKinds h` (SoundOfKindsTop.lean) with `KindsConds h 𝔏` in `KindsLaws h 𝔏`'s
    place; every other token is that definition's. `ProofConds.kinds`: it gives `ProofKinds h`.
  `sound_of_conds_at`: `sound_of_kinds_at` (Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean) with
    `ProofConds h` in `ProofKinds h`'s place; every other token of the statement is that theorem's.

Limits. THREE CALLS: THEY PAY NOTHING. NO CONDITION IS SHOWN TO BE MET AT ANY Z: THE THEOREM MAY BE
EMPTY. The filling 𝔏 is the payer's choice, one for all kinds and the five rows. The limits of the
three files that are called stand, KindsOfConds.lean's first: which fields are bare, which condition
cannot be met as typed, which conditions hold a part of the conclusion. BEFORE THIS IS QUOTED,
READ Johnson/Goal/Skeleton/KindsOfConds.lean's HEAD: some of `KindsConds`' fields are the bare law
of a kind, and some kinds' conditions hold an unpaid part of the conclusion as a field: "named
conditions" does not mean "conditions that are smaller than the laws".

-/
import Johnson.Goal.Skeleton.KindsOfConds
import Johnson.Goal.Skeleton.SoundOfKindsAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName

section
/- The names in scope are those of Johnson/Goal/Skeleton/SoundOfKindsTop.lean. -/
open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifierAndGoals FlashProve FlashProve
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The top's sixteen fields from the kinds' own conditions.** -/
theorem kindsLaws_of_conds
    {h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x}
    {𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok}
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : KindsConds h 𝔏) : KindsLaws h 𝔏 where
  k1 := C.all q₁ q₂ q₃ .K1 fun e => nomatch e
  k2 := C.all q₁ q₂ q₃ .K2 fun e => nomatch e
  k3 := C.all q₁ q₂ q₃ .K3 fun e => nomatch e
  k4 := C.all q₁ q₂ q₃ .K4 fun e => nomatch e
  k5 := C.all q₁ q₂ q₃ .K5 fun e => nomatch e
  k6 := C.all q₁ q₂ q₃ .K6 fun e => nomatch e
  k7 := C.all q₁ q₂ q₃ .K7 fun e => nomatch e
  k8 := C.all q₁ q₂ q₃ .K8 fun e => nomatch e
  k9 := C.all q₁ q₂ q₃ .K9 fun e => nomatch e
  k10 := C.all q₁ q₂ q₃ .K10 fun e => nomatch e
  k11 := C.all q₁ q₂ q₃ .K11 fun e => nomatch e
  k12 := fun hT => C.all q₁ q₂ q₃ .K12 fun _ => hT
  k13 := C.all q₁ q₂ q₃ .K13 fun e => nomatch e
  k14 := C.all q₁ q₂ q₃ .K14 fun e => nomatch e
  k15 := C.all q₁ q₂ q₃ .K15 fun e => nomatch e
  frame := C.all q₁ q₂ q₃ .frame fun e => nomatch e

/-- **The proof file's conditions under one head at the name, the kinds' by their files' own
names**: there is a filling of the tower's free letters at which the lists' heads are the
description's, and the kinds' conditions and the five rows hold. -/
def ProofConds (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x) : Prop :=
  ∃ (𝔏 : Free numsFull (dpZ Z) (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (_ : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str),
    𝔏.rP = recZ Z ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂ ∧
    (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃ ∧
    KindsConds h 𝔏 ∧ h.Five 𝔏 (depthZ Z)

/-- They give what the top asks. -/
theorem ProofConds.kinds
    {h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x}
    (P : ProofConds h) : ProofKinds h := by
  obtain ⟨𝔏, d, hr, q₁, q₂, q₃, C, V⟩ := P
  exact ⟨𝔏, d, hr, q₁, q₂, q₃, kindsLaws_of_conds q₁ q₂ q₃ C, V⟩

end

section
/- The names in scope are those of Johnson/Goal/Skeleton/SoundOfKindsAtZ.lean. -/
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- **SOUNDNESS AT ONE SET OF PUBLIC FILES, FROM THE KINDS' OWN NAMED CONDITIONS AT THESE
FILES.** Some of these "conditions" are bare laws or hold a part of the conclusion: see
KindsOfConds.lean's head. No condition is shown to be met. -/
theorem sound_of_conds_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (conds : protocolDataWellFormed (asDescriptionFiles Z) = true → At.Conds Z)
    (lastTyped : protocolDataWellFormed (asDescriptionFiles Z) = true →
      H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL)
    (kinds : protocolDataWellFormed (asDescriptionFiles Z) = true → ∀ Zp Np cF x
      (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x), ProofConds h) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_kinds_at Z pp scope read exact kS conds lastTyped
    fun hl Zp Np cF x h => (kinds hl Zp Np cF x h).kinds

end

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.kindsLaws_of_conds
#print axioms VerifierAndGoals.AtTheName.ProofConds.kinds
#print axioms VerifierAndGoals.AtTheName.sound_of_conds_at
