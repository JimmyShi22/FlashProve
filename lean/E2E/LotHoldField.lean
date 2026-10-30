-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHoldField.lean: THE FIELD hold OF LastLeft (E2E/OfflineLastFields.lean), in that structure's own words, from lotHoldAtLast
(E2E/LotHoldAtLastProved.lean).

  holdField        the field's own type, under live, hd, scope, fullPub = some K₀; «tied» is not read
  lastLeft_fits    a probe of fit: a value of LastLeft with its field hold laid anew by holdField: what counts is that it elaborates

Limits. Those of E2E/LotHoldAtLastProved.lean. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.OfflineLastFields
import E2E.LotHoldAtLastProved

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (WitLens)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.FirstH (LaterFill)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.AtFiles.HonestTerm.Lots (lotHoldAtLast)
open AtPublicFiles.Committed (PadZ pads_nonempty)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) padsAtHoldField : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) someRunValueAtHoldField : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) zeroRunValueAtHoldField : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (d : OfflineDescription) (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **The field hold.** -/
theorem holdField (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (hK : fullPub = some K₀) :
    ∀ w x, TiedAt Z d w x → ∀ k st m E
      (c : RowCoins [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest]),
    ThrS (lastThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x)
      (lastSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ w x) 2 k st m E →
    lendRow (keyBook K₀) ((keyBook K₀).rowsOf 2) (k.look 2) (lastJobAt (Z := Z) d).toRun.toTest.p.place
      [(firstPart (lastJobAt (Z := Z) d).toRun.toTest :
          Part (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit),
        restPart (lastJobAt (Z := Z) d).toRun.toTest] 0 = .ok c →
    OldAt E ((lastJobAt (Z := Z) d).toRun.toTest.trees₀ m.st.input (frontOf m)
        (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1).mem
        ((lastJobAt (Z := Z) d).toRun.toTest.first m.st.input (frontOf m)
          (restCoins (lastJobAt (Z := Z) d).toRun.toTest c.2.1)))
      (fun k => [Fmt.TreeSource.taken 0 0, .taken 0 5, .taken 1 1].getD k (.own 0)) :=
  fun w x _ k st m E c hT hc =>
    lotHoldAtLast live hd scope hK ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ Q S₁ w x k st m E c hT hc

/-- A probe of fit: LastLeft takes holdField as its field hold. -/
theorem lastLeft_fits (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (hK : fullPub = some K₀)
    (L : LastLeft ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁) :
    LastLeft ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ :=
  { L with hold := holdField ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d Q S₁ live hd scope hK }

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.holdField
#print axioms AtPublicFiles.OfflineRows.lastLeft_fits
