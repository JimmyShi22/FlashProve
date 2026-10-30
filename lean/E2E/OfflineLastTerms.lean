-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLastTerms.lean: what `last_done` and `last_laid` ask of the terms of E2E/OfflineLastLetters.lean, by `rfl`.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.OfflineLastLetters

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Coins Common Local Mid Table)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyLastChain (threadOwn saidOwn mlKey val₁Key)
open AtPublicFiles.FirstH (LaterFill HCells HTab fillH tbH)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyStandMember (keyOf)
open VerifierAndGoals (PublicFiles)
open AtPublicFiles.KeyStandWalked (offlineValue)
open ProofFile.Honest.Term (tableCoins)

variable {Z : PublicFiles} {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub) (description : OfflineDescription) (Q : LaterFill (keyBook K₀) AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness)

variable
  (S₁ : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi)

/-- `hd` of `last_laid`. -/
theorem d_lin (x : Xi) : (dValue description x).1.2.lin = none := rfl

/-- `hdM`. -/
theorem dM_opened : (dMValue (Z := Z) w x).opened.isSome = true := rfl

/-- `hsame`. -/
theorem same_value (x : Xi) : (fillAtValue description Q x).R.same = fun a b => OnBytes.Slice.readE a = OnBytes.Slice.readE b := rfl

/-- 'ho₀'. -/
theorem orc_zero : (Johnson.RunOne.KeyRows1.plan₁ (AtPublicFiles.KeyThread.one₀ description.source)).orc 0 = some 0 := rfl

/-- `hDt`. -/
theorem dot_value (x : Xi) (v : Local AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness Xi Unit) :
    (dtValue description Q x v).dot = VerifiableInference.Desc.Third.Law.dotI
      (VerifiableInference.Desc.Key.thirdPar description.source.chains).S AtPublicFiles.KeyLastChain.gKey (fun _ u => u.2)
      (fun _ => AtPublicFiles.KeyLastChain.wvK (val₁Key description.source (fillAtValue description Q x))
        (VerifiableInference.Desc.Key.thirdPar description.source.chains).S AtPublicFiles.AtFiles.CF AtPublicFiles.AtFiles.Full.A0.2.w) := rfl

/-- `hown`. -/
theorem own_value : (keyAtValue (Z := Z) Z₀ description).own =
    AtPublicFiles.KeyLay.proverSideOfGuardedSending description.source description.numbers description.later
      (offlineSenders (files := Z) description).idx (offlineSenders (files := Z) description).w
      (offlineSenders (files := Z) description).send id
      (ProofFile.Honest.K12.Light.askOf (offlineSenders (files := Z) description).send
        (fun w => (offlineSenders (files := Z) description).weights w.w₀)
        (fun w => AtPublicFiles.KeyFile.randK14 ((offlineSenders (files := Z) description).rand w.rc))) := rfl

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.AtFiles.HonestTerm.d_lin
#print axioms AtPublicFiles.AtFiles.HonestTerm.dM_opened
#print axioms AtPublicFiles.AtFiles.HonestTerm.same_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.orc_zero
#print axioms AtPublicFiles.AtFiles.HonestTerm.dot_value
#print axioms AtPublicFiles.AtFiles.HonestTerm.own_value
