-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our kinds' clauses at the letters.
/-
AtFullSide/M1/KOursLetters.lean: `theG_pays_of_holds` and `kOurs_pays` at the value `parts h P` of the
threads' letters, `theG` of AtFullSide/Honest/TheLetters.lean. Each is one line. `O`, `P` are that file's
named holes; `K`: the kinds' rows. At `kOurs` nine lots stay bare: not the K of the zero-knowledge theorem.
No property of the protocol is claimed here.
-/
import AtFullSide.M1.KRecord
import AtFullSide.Honest.TheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.FirstThread (HeadAtReturn)
open AtFullSide.Honest.TheLetters (OpenShared OpenLast OpenG)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {O : OpenShared A} (P : OpenLast h O)

/-- **At the letters, at any K that holds ours.** -/
theorem letters_pays_of_holds (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFill = .ok A) (K : OpenG A Z)
    (h₁ : k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id ∈ K.rows.lots)
    (h₂ : wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id ∈ K.rows.lots)
    (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.rows.lots)
    (hsix : ∀ r ∈ baseRows A.Z h.places, r ∈ K.rows.shared) :
    VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P K) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P K) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P K) KindName.K14 :=
  theG_pays_of_holds h hS hL made (AtFullSide.Honest.TheLetters.parts h P) K.rows h₁ h₂ h₃ hsix

/-- **At the letters, at our rows.** -/
theorem letters_kOurs (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFill = .ok A) :
    VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P ⟨kOurs A h.head⟩)
        KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P ⟨kOurs A h.head⟩)
        KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P ⟨kOurs A h.head⟩)
        KindName.K14 :=
  kOurs_pays h hS hL made (AtFullSide.Honest.TheLetters.parts h P)

/-- **At the letters, at the K of record.** -/
theorem letters_theK (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFill = .ok A)
    (E : AtPublicFiles.TheSides.TheThirteen baseFill A.Z A.G) (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K14 :=
  theK_pays h hS hL made (AtFullSide.Honest.TheLetters.parts h P) E apart h₁ h₂ h₃

end AtFullSide.M1

#print axioms AtFullSide.M1.letters_pays_of_holds
#print axioms AtFullSide.M1.letters_kOurs
#print axioms AtFullSide.M1.letters_theK
