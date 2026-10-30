-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinShared.lean: THE SHARED CHAIN's TWO PROXIMITY TESTS (members 9 and 10) AT THE OFFLINE PROVER's OWN SHARED THREAD: the ten sentences that the
join (TheLots, E2E/OfflineJoin.lean) asks in its fields testU, testOmega, testYesU, testYesOmega, in that structure's own words written out
(`threadAt`, `walkedLetter`, E2E/KeyStandWalked.lean, at `offlineValue d`, `matrixReader`, `tableCoins Z`), from `tests_at_laid`
(Johnson/Desc/ProofFile/Honest/K12/AtKey/ULaid.lean), by five ties, each by unfolding once the later places are the written ones.

  `frontParts Z d`: the senders under the laying: what `offlineSenders d` hands to `withStoredColumnsAndPlan`.
  `ttAt Z d K₀ Z₀ B`: the letter tt: `ttF` at the offline prover's senders.
  `sharedAt`, `sharedSaidAt`: the join's sharedThread and sharedSaid at tt := ttAt, Kp := `keepsKey`; ℓ, Nm, Mg₀, tk, rest, Vd, Z₀ stay letters.
  `shared_is_laid`: THE FIVE TIES AS ONE EQUATION: at the written places that thread IS `laidThread`: by unfolding.
  `sharedSaid_is_laid`: and its letter IS `laidLetter`: by unfolding.
  `LotJoinShared`: THE STATEMENT: the four at 9, the four at 10, AcceptedS at 9 and at 10, at every fall.

THE FIVE TIES: (a) offlineSenders d is keyOf (pubKey Z₀ …) … (frontParts Z d) … (`laidFromChains_is_keyOf`: rfl) · (b) d.later = PF (`later_sourced`) ·
(c) offlineTestParametersOnU PF, offlineTestOnOmega PF are pU, pO · (d) tt := ttF at these senders · (e) `withTests` unfolded: its rng and own are the
free halves r, o.

Premises that stay: KeySourced, InScope, fullPub = some K₀ · the instance is the committer's sample at some seed (hx) · Nm.tenant injective ·
CellsAlone (Mg₀ v) · Vd at the input. B : Eight (parKey d.source PF) is a letter: in scope there is one (`plan_key`, `Plan2.eight`).




Limits. ALL CONTENT IS IN THE IMPORTS, OF THE GRADE «TRIAL»; here: the ties. Every sentence has the thread's pair (ThrS) as a premise inside.
At the written sizes. Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.ULaid
import E2E.KeyStandWalked

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12.AtKey (laidThread laidLetter tests_at_laid keepsKey)
open ProofFile.Honest.Term (matrixInput tableCoins)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.Full (PF later_sourced)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader idleRecord)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeySharedQuiet (CellsAlone)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyValues (WitK faceAt keyBatt withSendingsAndLookups)
open AtPublicFiles.KeyPartsIdle (fixedKeyParts)
open AtPublicFiles.TableFilled (ttF)
open AtPublicFiles.StandAtNine (K1)
open Bind.ForProver (shapeOf oodSh Seed)

variable (Z : VerifierAndGoals.PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- The senders under the laying. -/
abbrev frontParts : KeyParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Unit Unit WitK :=
  withSendingsAndLookups
    (fixedKeyParts (faceAt d.source 0) (keyBatt d.source) matrixInput.dummy () () idleRecord)
    d.source d.numbers matrixReader matrixInput.inRange matrixInput.dummy

/-- **The letter tt**: `ttF`, at the offline prover's senders. -/
abbrev ttAt (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF)) :=
  ttF K₀ d.source (K1 d.source (frontParts Z d) matrixReader (tableCoins Z) Z₀) B ()

variable {P₁ Wt : Type} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)
  (B : Eight (parKey d.source PF)) (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : Xi)

/-- The join's shared thread, tt laid. -/
abbrev sharedAt :=
  threadAt d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk (ttAt Z d K₀ Z₀ B) rest
    Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x

/-- Its letter. -/
abbrev sharedSaidAt :=
  walkedLetter d.source d.numbers d.later K₀ (offlineValue (files := Z) d) ℓ Nm Mg₀ tk (ttAt Z d K₀ Z₀ B)
    rest Kp Vd matrixReader (tableCoins Z) Z₀ w₀ rc x

/-- **The five ties as one equation**, at the written places. -/
theorem shared_is_laid (src : VerifiableInference.Desc.Key.Source) (num : H2U.PlaceNums)
    (B : Eight (parKey src PF)) :
    sharedAt Z ⟨src, num, PF⟩ K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ B w₀ rc x =
      laidThread src num K₀ (frontParts Z ⟨src, num, PF⟩) ℓ Nm Mg₀ tk rest Kp Vd matrixReader
        (tableCoins Z) Z₀ w₀ rc x B () (offlineValue (files := Z) ⟨src, num, PF⟩).rng
        (offlineValue (files := Z) ⟨src, num, PF⟩).own := rfl

/-- **And the letters are one**, at the written places. -/
theorem sharedSaid_is_laid (src : VerifiableInference.Desc.Key.Source) (num : H2U.PlaceNums)
    (B : Eight (parKey src PF)) :
    sharedSaidAt Z ⟨src, num, PF⟩ K₀ ℓ Nm Mg₀ tk rest Kp Vd Z₀ B w₀ rc x =
      laidLetter src num K₀ (frontParts Z ⟨src, num, PF⟩) ℓ Nm Mg₀ tk rest Kp Vd matrixReader
        (tableCoins Z) Z₀ w₀ rc x B () (offlineValue (files := Z) ⟨src, num, PF⟩).rng
        (offlineValue (files := Z) ⟨src, num, PF⟩).own := rfl

/-- **The ten sentences at the two proximity tests, at the offline prover's own shared thread.** -/
def LotJoinShared : Prop :=
  ∀ {Z' : VerifierAndGoals.PublicFiles}, KeySourced Z' d.source d.numbers d.later → VerifierAndGoals.InScope Z' = true →
    fullPub = some K₀ →
    ∀ sd : Seed (shapeOf (pubKey Z₀ d.source.chains)) × ℕ,
    x = ⟨oodSh (shapeOf (pubKey Z₀ d.source.chains)) (pubKey Z₀ d.source.chains)
      ⟨matrixReader w₀, tableCoins Z rc, sd⟩⟩ →
    Function.Injective Nm.tenant → (∀ v, CellsAlone (Mg₀ v)) → Vd (AtPublicFiles.KeyStandOne.inK w₀ rc x) →
    ∀ fall : ℕ → St → List Fmt.Drawn → Option String,
      (PlaysS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 9 ∧
        BehindS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 9 ∧
        ExchangeS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 9 ∧
        RidesPastS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 9) ∧
      (PlaysS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 10 ∧
        BehindS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 10 ∧
        ExchangeS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 10 ∧
        RidesPastS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
          (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) 10) ∧
      AcceptedS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
        (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) fall 9 ∧
      AcceptedS (sharedAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x)
        (sharedSaidAt Z d K₀ ℓ Nm Mg₀ tk rest keepsKey Vd Z₀ B w₀ rc x) fall 10

theorem lotJoinShared : LotJoinShared Z d K₀ ℓ Nm Mg₀ tk rest Vd Z₀ B w₀ rc x := by
  intro Z' hs scope hK sd hx hN hC hVd fall
  obtain ⟨src, num, later⟩ := d
  obtain rfl : later = PF := later_sourced hs scope
  exact tests_at_laid src num K₀ (frontParts Z ⟨src, num, PF⟩) ℓ Nm Mg₀ tk rest Vd matrixReader
    (tableCoins Z) Z₀ w₀ rc x B () (offlineValue (files := Z) ⟨src, num, PF⟩).rng
    (offlineValue (files := Z) ⟨src, num, PF⟩).own hs scope hK sd hx hN hC hVd fall

end AtPublicFiles.KeyStandWalked.Lots

#print axioms AtPublicFiles.KeyStandWalked.Lots.shared_is_laid
#print axioms AtPublicFiles.KeyStandWalked.Lots.sharedSaid_is_laid
#print axioms AtPublicFiles.KeyStandWalked.Lots.lotJoinShared
