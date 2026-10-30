-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/RoadRowsPaid.lean: two fields of `HonDebts` (E2E/RoadHonDebts.lean), `seeds` and `keyZero`, in
that structure's own letters, at the choices at which theorems of the library give them. Toward
completeness; nothing is claimed.

  `seedsAside_none`: where no OOD seed is set aside, `SeedsAside` holds at the bound 0
  `keyZeroAt_of_fallZero`: at the shell `offlineProverWithEncodedTable`, `KeyZeroAt` follows from `FallZero`
    (E2E/KeyBridge.lean) at the same fall, unguarded
  `keyZeroAt_empty`: at the shell `offlineProverWithEncodedTable` and the empty fall `KeyZeroAt` holds, with no hypothesis

By what. `prZ_none` (E2E/BridgeSeeds.lean). `badZero_obj` and `hidZero_obj`
(E2E/KeyBridgeFilled.lean), called as in `sentences_keyZ` (E2E/BridgeKeyEight.lean); the steps of
`whT_of` (E2E/KeyBridge.lean) without the guard.

Limits.
- Where no seed is set aside, the fields `threads`, `falls` and `keyAccepts` of `HonDebts` are asked
  at every OOD seed.
- At the empty fall the field `keyAccepts` asks acceptance outside the abort set alone.
- Nothing here says that any verifier accepts anything.
-/
import E2E.RoadHonDebts
import E2E.BridgeSeeds
import E2E.BridgeKeyEight

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}
  (hT : Honest L.offline (I × L.EncodingRandomness × L.OutOfDomainSeed))
  {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (FT : I × L.EncodingRandomness × L.OutOfDomainSeed → L.Rec → hT.Coin → Set (Rho L.offline.shape))
  (Z : I → L.EncodingRandomness → Set L.OutOfDomainSeed)

/-- Where no OOD seed is set aside, the clause on the seeds that are set aside holds at the bound 0.
-/
theorem seedsAside_none (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (Yes : I → X → Prop) :
    SeedsAside W (fun _ _ => ∅) S Yes 0 :=
  fun i _ r _ => le_of_eq (prZ_none S i r)

end AtPublicFiles.Bridge

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Premises
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀ relationsAndEncodingOfClaims)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides Purse halvedAll rootedAll ready)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR homeT allZeroDigest)
open OnBytes.K.Arm.Pub (D8)
open OnBytes.Prover (HonFit ThreeProvers Falls)
open OnBytes.WholeKey (CoinNums)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)

/-- **At the shell `offlineProverWithEncodedTable`: `KeyZeroAt` from `FallZero`**, at the same fall. -/
theorem keyZeroAt_of_fallZero (FT : AtPublicFiles.KeyBridge.FallT (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT))
    (hf : AtPublicFiles.KeyBridge.FallZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT) :
    KeyZeroAt (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W FT := by
  have hb : AtPublicFiles.KeyBridge.BadZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W :=
    badZero_obj Z Fx BT (dataAtFiles flashProveData Z).P _ _ HT _ shT _
  have hh : AtPublicFiles.KeyBridge.HidZero (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W :=
    hidZero_obj Z Fx BT (dataAtFiles flashProveData Z).P _ _ HT _ shT _
  rintro w x c ρ ((h | h) | h)
  · exact Or.inl (Or.inl (hb ρ h))
  · exact Or.inl (Or.inr (hh w x ρ h))
  · exact hf w x c ρ h

/-- **At the shell `offlineProverWithEncodedTable` and the empty fall `KeyZeroAt` holds.** -/
theorem keyZeroAt_empty :
    KeyZeroAt (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (lettersZ Z c₀ m₀).W (fun _ _ _ => ∅) :=
  keyZeroAt_of_fallZero c₀ m₀ Z Fx BT HT val₂ val₃ shT (fun _ _ _ => ∅) fun _ _ _ _ h => h.elim

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.Bridge.seedsAside_none
#print axioms AtPublicFiles.AtFiles.keyZeroAt_of_fallZero
#print axioms AtPublicFiles.AtFiles.keyZeroAt_empty
