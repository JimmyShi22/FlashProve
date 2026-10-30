-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLetters.lean: the definitions of the offline join, beneath its proofs: `TiedOffline`, the families of threads and letters,
`descOf`, `proverOf`, `TiedAt`, `sharedThread`, `sharedSaid`, `TheLots`. Each text stood in a file of proofs; that file now imports this one.

Why. AtFullSide/Honest/TheKeyLetters.lean reads these, and every payer imports it.

What lies beneath all the same. This file imports E2E.KeyStandWalked, E2E.KeyTied, E2E.KeyAcceptPairsLaid, E2E.BridgeJoinAtFiles, E2E.TheHonestProver, which hold proofs beside the definitions read here.

Nothing on soundness, completeness, hiding or binding: names.

-/
import E2E.BridgePremWKey
import Johnson.Goal.Conditions.BindsAtThe
import E2E.BridgeJoinAtFiles
import E2E.KeyAcceptPairsLaid
import E2E.KeyTied
import E2E.KeyStandWalked
import E2E.TheHonestProver

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (Files relationsAndEncodingOfClaims RecFull front₀ join₀ codingHonest)
open OnBytes.Slice (frS frZ)
open _root_.Run (ckP)
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Key (Source LaterPlaces keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover ProverCoinCounts Sides Fall Thread Local Common Coins Mid Tied halvedAll tied_atItem)
open OnBytes.Prover (AccLaw)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed allZeroDigest)
open LPFD.Full (XF)

local instance (priority := high) instNonemptyPadZOfflineLettersA : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyOfInhabitedOfflineLetters {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

section
variable (Z : PublicFiles) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) {Q₂ Q₃ : Type} [Fintype Q₂]
  [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃] (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray)
  {X₀ Xh Wk : Type} (B : ProverCoinCounts)
  (K : KeyParts FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) X₀ Xh Wk)

/-- **An input is tied**: the frame's `Tied` at the key's prover, the seat's letters and the committer's relation. -/
def TiedOffline (ok : FullSizeMatrix → Prop) (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst) :
    Prop :=
  Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P) (keyProver K)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z ok) w x


end

end AtPublicFiles.AtFiles

namespace AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi)
open _root_.Desc.K14 (St)
open ProofFile.Honest (Fall Thread Local Common Coins Mid Sits OwesS YesS SaidNext PlaysS BehindS ExchangeS
  RidesPastS AcceptedS Table fallsBy)
open ProofFile.Honest.K14 (WitLens)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (allZeroDigest committerCoinCountLessOne protocolDataWellFormed)
open ProofFile.Honest.Term (tableCoins)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStandWalked (offlineValue threadAt walkedLetter)
open LPFD.Full (XF)
open AtPublicFiles.Committed (PadZ pads_nonempty)

local instance (priority := high) instNonemptyPadZOfflineLetters : Nonempty PadZ := pads_nonempty frS 402653181

local instance (priority := high) instNonemptyRunValueOfflineLetters : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) instInhabitedRunValueOfflineLetters : Inhabited RunValue := ⟨fun _ => 0⟩


/-- A family of the first chain's threads. -/
abbrev FirstFamily (Z : PublicFiles) (description : OfflineDescription) (B : ProofFile.Honest.ProverCoinCounts) :=
  AtPublicFiles.AtFiles.FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → KeyInst →
    Thread B (keyFileDescription description.source description.numbers description.later).S₁
      (keyFileDescription description.source description.numbers description.later).Cl
      (Local AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) KeyInst Unit)
      (Local AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) KeyInst Unit) Unit KeyInst

/-- A family of the shared chain's threads. -/
abbrev SharedFamily (Z : PublicFiles) (description : OfflineDescription) (B : ProofFile.Honest.ProverCoinCounts) :=
  AtPublicFiles.AtFiles.FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → KeyInst →
    Thread B (keyFileDescription description.source description.numbers description.later).S₂
      (keyFileDescription description.source description.numbers description.later).Cl Empty
      (Common AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) TableKey) Unit TableKey

/-- A family of the last chain's threads. -/
abbrev LastFamily (Z : PublicFiles) (description : OfflineDescription) (B : ProofFile.Honest.ProverCoinCounts) :=
  AtPublicFiles.AtFiles.FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → KeyInst →
    Thread B (keyFileDescription description.source description.numbers description.later).S₃
      (keyFileDescription description.source description.numbers description.later).Cl
      (Local AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) KeyInst Unit)
      (Local AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) KeyInst Unit) Unit KeyInst

/-- A family of letters at an own chain. -/
abbrev OwnLetter (Z : PublicFiles) (B : ProofFile.Honest.ProverCoinCounts) :=
  AtPublicFiles.AtFiles.FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → KeyInst → Nat →
    Coins B → Mid (Local AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) KeyInst Unit) Unit → Prop

/-- A family of letters at the shared chain. -/
abbrev SharedLetter (Z : PublicFiles) (B : ProofFile.Honest.ProverCoinCounts) :=
  AtPublicFiles.AtFiles.FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → KeyInst → Nat →
    Coins B → Mid (Common AtPublicFiles.AtFiles.FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) TableKey) Unit → Prop


section
variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}

/-- The description at these files. -/
abbrev descOf (description : OfflineDescription) :=
  keyFileDescription description.source description.numbers description.later

/-- The offline prover. -/
abbrev proverOf (Z : PublicFiles) (description : OfflineDescription) :=
  keyProver (offlineValue (files := Z) description)

/-- An input is tied. -/
abbrev TiedAt (Z : PublicFiles) (description : OfflineDescription)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) : Prop :=
  AtPublicFiles.AtFiles.TiedOffline Z description.source description.numbers description.later runValueBytes
    runValueBytes (offlineValue (files := Z) description) AtPublicFiles.AtFiles.inRange w x

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub)

/-- The shared thread at an input. -/
abbrev sharedThread (description : OfflineDescription)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  threadAt description.source description.numbers description.later K₀
    (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀
    w.1 w.2.1 x

/-- The shared thread's letter at an input. -/
abbrev sharedSaid (description : OfflineDescription)
    (w : AtPublicFiles.AtFiles.FullSizeMatrix × (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness × (AtPublicFiles.AtFiles.protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  walkedLetter description.source description.numbers description.later K₀
    (offlineValue (files := Z) description) ℓ Nm Mg₀ tk tt rest Kp Vd matrixReader (tableCoins Z) Z₀
    w.1 w.2.1 x


end

section
variable {Z : PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {description : OfflineDescription}
  {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey →
    List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common AtPublicFiles.AtFiles.FullSizeMatrix (AtPublicFiles.AtFiles.protocolAtFiles Z).EncodingRandomness TableKey → Prop)
  (Z₀ : ProofFile.Pub)

/-- **Every lot of the offline prover's debts, at no fall.** `w`, `x`: a tied input. -/
structure TheLots (description : OfflineDescription) (U₁ : FirstFamily Z description (keyBook K₀))
    (U₃ : LastFamily Z description (keyBook K₀)) (S₁ S₃ : OwnLetter Z (keyBook K₀)) : Prop where
  /-- the three threads sit -/
  sits : ∀ w x, TiedAt Z description w x → (descOf description).okStart x = true →
    Sits (descOf description)
      ((bareSides (descOf description) (keyBook K₀) (proverOf Z description) [] [] []).prover
        (proverOf Z description))
      (U₁ w x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (U₃ w x)
  /-- the first chain's four debts at every member -/
  firstOwes : ∀ w x, TiedAt Z description w x → OwesS (U₁ w x) (S₁ w x)
  /-- the last chain's -/
  lastOwes : ∀ w x, TiedAt Z description w x → OwesS (U₃ w x) (S₃ w x)
  /-- the first chain's letter goes on from a move -/
  firstNext : ∀ w x, TiedAt Z description w x → ∀ b, SaidNext (U₁ w x) (S₁ w x) b
  /-- the last chain's -/
  lastNext : ∀ w x, TiedAt Z description w x → ∀ b, SaidNext (U₃ w x) (S₃ w x) b
  /-- the first chain accepts at no fall -/
  firstYes : ∀ w x, TiedAt Z description w x →
    YesS (U₁ w x) (S₁ w x) (fallsBy [] (descOf description).first.blocksInOrder)
  /-- the last chain -/
  lastYes : ∀ w x, TiedAt Z description w x →
    YesS (U₃ w x) (S₃ w x) (fallsBy [] (descOf description).second.blocksInOrder)
  /-- the test on G_u, member 9 of the shared chain, its four debts -/
  testU : ∀ w x, TiedAt Z description w x →
    PlaysS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
      BehindS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
      ExchangeS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9 ∧
      RidesPastS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 9
  /-- the test on G_omega, member 10, its four debts -/
  testOmega : ∀ w x, TiedAt Z description w x →
    PlaysS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
      BehindS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
      ExchangeS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10 ∧
      RidesPastS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
        (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) 10
  /-- the two tests accept at no fall -/
  testYesU : ∀ w x, TiedAt Z description w x →
    AcceptedS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
      (fallsBy [] (descOf description).shared.blocksInOrder) 9
  testYesOmega : ∀ w x, TiedAt Z description w x →
    AcceptedS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x)
      (fallsBy [] (descOf description).shared.blocksInOrder) 10
  /-- what a run owes: the test on the instance, ready, the plan, the starts, the door, the end -/
  run : ∀ w x (c : CoinOne (keyBook K₀) RunValue RunValue), TiedAt Z description w x →
    AtRunS (descOf description) (proverOf Z description) (U₁ w x)
      (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (U₃ w x) (S₁ w x)
      (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ description w x) (S₃ w x) w x c


end

end AtPublicFiles.AtFiles.HonestTerm
