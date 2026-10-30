-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OfflineAtFiles.lean: from the library's form of exactness at the offline proof to the run-by-run line.

1.  The offline prover's line in ZeroKnowledgeBeforeHashing.lean says: outside the private stops the honest output and the simulator's
    have one law. The library's OneExact says the same at tied pairs, at every message.
2.  So OneExact, with every valid pair tied, gives the line, at every map on the messages.
3.  Nothing here proves zero knowledge of the protocol: OneExact is a premise.
-/
import VerifiableInference.Final.ZeroKnowledgeBeforeHashing
import E2E.KeyBridge
import E2E.KeyExact

set_option autoImplicit false
set_option maxRecDepth 20000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob

section General
variable {I X : Type} {L : HolographicProtocol I X}

/-- **The library's form at the offline proof is this layer's.** -/
theorem exactOutsideStops_of_keyOneExact (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    {sim : AtPublicFiles.KeyBridge.SimT L} {Tied : AtPublicFiles.KeyBridge.TiedT L} {inRange : I → Prop}
    (exact : AtPublicFiles.KeyBridge.OneExact hT sim Tied)
    (tied : AtPublicFiles.KeyBridge.ValidTied Tied inRange fun _ => True)
    (clear : Rho L.offline.shape → Rho L.offline.shape) :
    ExactOutsideStops hT (fun w y => inRange w.1 ∧ L.validT w y) clear sim := by
  rintro ⟨i, r, e⟩ y ⟨hi, hy⟩ ρ hρ
  obtain rfl : y = L.recOf i r e := hy
  exact exact (i, r, e) _ (tied i r e hi trivial) (clear ρ) hρ

/-- With no private stop the bound is 0. -/
theorem privateStopsAtMost_of_noHid (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
    (valid : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → Prop) (work : WorkBits L.offline.shape)
    (hno : ∀ w y ρ, ρ ∉ hT.Hid w y) : PrivateStopsAtMost hT valid work 0 :=
  fun w y _ => show pr (unif (Rho L.offline.shape)) {ρ | work.cleared ρ ∈ hT.Hid w y} ≤ 0 from
    le_of_eq (pr_eq_zero_of_forall_not_mem _ (E := {ρ | work.cleared ρ ∈ hT.Hid w y})
      fun ρ _ hρ => hno w y (work.cleared ρ) hρ)

end General

section AtFiles
open OnBytes (TableKey)
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed relAt)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open LPFD.Full (XF)
open AtPublicFiles.AtFiles AtPublicFiles.Committed
open OnBytes.Slice (frS)
open P5J

local instance (priority := high) offlineAtFilesInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) offlineAtFilesInstance2 {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts)
  [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃] (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  (GK : Sides (keyFileDescription X N P) BT (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) TableKey TrT X₀T XT)
  (HK : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)

/-- **The offline line from the rows' rule at the key file.** Owed is a premise: no member of it is given here.
-/
theorem offline_exact_of_owed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (named : KeyNamed Z X N P) (x₀ : XF)
    (owed : Owed (keyFileDescription X N P) BT ((cmKey Z).proverAt 0 HK) GK.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i _ => inRange i) wrK))
    (owns : GK.owns = true) (clear : Rho (protocolAtFiles Z).offline.shape → Rho (protocolAtFiles Z).offline.shape) :
    ExactOutsideStops (offlineProverWithEncodedTable Z (keyFileDescription X N P) BT (provK Z (keyFileDescription X N P) BT GK HK) val₂ val₃ (keyFirst X N P))
      (fun w y => inRange w.1 ∧ (protocolAtFiles Z).validT w y) clear
      (simKey Z (keyFileDescription X N P) BT val₂ val₃ (keyFirst X N P) GK HK GK.sims) :=
  have paid := key_paid Z X N P scope live named
  exactOutsideStops_of_keyOneExact _
    (oneExact_keyZ_of_owedAt Z (keyFileDescription X N P) BT val₂ val₃ (keyFirst X N P) GK HK (fun i _ => inRange i) x₀
      paid.1 paid.2.1 paid.2.2.1 paid.2.2.2 owed owns)
    (validTied_key Z x₀ fun _ h => h) clear

/-- **The private stops' bound at the key file's shell, with no second stop.** Public stops cost nothing here. -/
theorem offline_stops_of_quiet (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (Fx : VerifiableInference.Desc.FileDescription KeyInst) (shT : TableKey → Fx.S₂) {BT' : ProverCoinCounts}
    (h : AtPublicFiles.Stops.NoSecondStop HT) (valid : _ → (protocolAtFiles Z).Rec → Prop) (work : WorkBits (protocolAtFiles Z).offline.shape) :
    PrivateStopsAtMost (offlineProverWithEncodedTable Z Fx BT' HT val₂ val₃ shT) valid work 0 :=
  privateStopsAtMost_of_noHid _ _ _ fun w y ρ hρ => by
    rw [hid_keyZ_of_quiet Z Fx BT' val₂ val₃ shT HT h w y] at hρ
    exact hρ

end AtFiles

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.exactOutsideStops_of_keyOneExact
#print axioms VerifiableInference.Compilation.privateStopsAtMost_of_noHid
#print axioms VerifiableInference.Compilation.offline_exact_of_owed
#print axioms VerifiableInference.Compilation.offline_stops_of_quiet
