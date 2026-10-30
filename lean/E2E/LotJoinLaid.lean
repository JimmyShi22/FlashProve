-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinLaid.lean: THE JOIN's TWELVE FIELDS (TheLots, E2E/OfflineJoin.lean) AT LAID TERMS FOR THE FIRST CHAIN, FROM ONE STRUCTURE
OF WHAT IS LEFT, with every field that a proved lot pays discharged inside. The join itself is not among this file's imports (it was typed
before the join had met Lean). "An input is tied" stands as a letter Tied with ONE premise (a tied input
meets the relation); the twelve fields stand in a twin structure, LotsAt, in the join's own words at letters.

  (laidFirst's and laidSaid's text lies in E2E/LotLetters.lean.)
  `laidFirst Z d K₀ w x`: U₁ := joinThread d (laterValue Z d K₀) w x: NO LETTER LEFT
    in the first chain's thread. `laidSaid`: S₁ := joinSaid … the same.
  `FirstFamilyText`, `OwnLetterText`, `laidFirst_fits`, `laidSaid_fits`: the join's two types for U₁ and S₁, copied by their text,
    and that the laid terms have them.
  `LotsAt`: the join's twelve fields, at letters Tied, H (the sides' prover), U₁, U₂, U₃, S₁, S₂, S₃.
  **`leftJoin_laid`**: OF THE FIRST CHAIN's 95 CELLS NONE IS LEFT: LeftJoin (E2E/LotJoinFirst.lean) holds at the laid thread, at every input, from KeySourced, InScope and
    fullPub = some K₀ alone. `firstLaid`: so OwesS, SaidNext at every member and YesS at no fall, at the laid U₁, S₁.
  `LeftLots`: WHAT IS LEFT, THE ONE STRUCTURE OF RECORD: run (LeftRun: six clauses of AtRunS) · and the eight
    fields that no lot of ours touches, as they stand: sits, lastOwes, lastNext, lastYes, testU, testOmega, testYesU,
    testYesOmega.
  **`lotsFromLeft`**: LotsAt at the laid first chain, from LeftLots.

PAID INSIDE: firstOwes, firstYes (joinFirstOwes, joinFirstYes, over leftJoin_laid: ExchangeS at 5, 11: lotExchangeLayer, E2E/LotExchangeLayer.lean; (Eval) at 17 and row 16: eval_item, exchange_batt,
E2E/FirstHEvalDone.lean, with lotHeardOfFold, w_public and coinsAtSlots, E2E/KeyCoinsAtSlots.lean; PlaysS, ExchangeS at 4, 10: leftJoin_of_six_laid, E2E/LotWitnessReads.lean; PlaysS,
AcceptedS at 15: fiveAtRanges, E2E/LotFiveAtRanges.lean) · firstNext (joinFirstNext) · of run's ten clauses four: ready
returns, the plan serves, the first chain begins, its letter at the start (runFromLeft, E2E/LotJoinRun.lean) · hQ by rfl · that a
tied input's matrix passes the prover's test (rel_passes).

THE SHARED AND THE LAST CHAIN STAY LETTERS: U₂, S₂, U₃, S₃. At the join U₂ and S₂ are threadAt and walkedLetter
(E2E/KeyStandWalked.lean) at letters ℓ, Nm, Mg₀, tk, tt, rest, Kp, Vd, Z₀: NONE OF THESE IS LAID HERE.

Limits. AN IMPLICATION: no member of LeftLots is known. LotsAt IS A TWIN, TYPED BY READING E2E/OfflineJoin.lean:
THAT TheLots FOLLOWS FROM IT FIELD BY FIELD IS CHECKED BY LEAN in E2E/LotJoinAtTheLots.lean (theLots_of_lotsAt). «ready returns» rests on E2E/LotReadyWhole.lean:
all that its head says goes with it. At no fall. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.LotLetters
import E2E.LotJoinFirst
import E2E.LotJoinFirstStruck
import E2E.LotJoinFirstLookups
import E2E.LotWitnessReads
import E2E.LotFiveAtRanges
import E2E.KeyCoinsAtSlots
import E2E.LotExchangeLayer
import E2E.LotJoinRun
import E2E.LotLaterValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open OnBytes (TableKey)
open AtPublicFiles.KeyLink (CoinOne AtRunS)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- The join's type of U₁ (FirstFamily, E2E/OfflineAtTheTerm.lean), COPIED by its text. -/
abbrev FirstFamilyText (Z : PublicFiles) (d : OfflineDescription) (B : ProverCoinCounts) :=
  FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → AtPublicFiles.AtFiles.KeyInst →
    Thread B (keyFileDescription d.source d.numbers d.later).S₁ (keyFileDescription d.source d.numbers d.later).Cl
      (Local FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) AtPublicFiles.AtFiles.KeyInst Unit)
      (Local FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) AtPublicFiles.AtFiles.KeyInst Unit) Unit
      AtPublicFiles.AtFiles.KeyInst

/-- The join's type of S₁ (OwnLetter), COPIED by its text. -/
abbrev OwnLetterText (Z : PublicFiles) (B : ProverCoinCounts) :=
  FullSizeMatrix × ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) × (AtPublicFiles.AtFiles.Cz Z).Seed → AtPublicFiles.AtFiles.KeyInst → Nat →
    Coins B →
    Mid (Local FullSizeMatrix ((AtPublicFiles.AtFiles.Cz Z).Pad × (AtPublicFiles.AtFiles.Cz Z).Rnd) AtPublicFiles.AtFiles.KeyInst Unit) Unit → Prop

/-- The laid thread has the join's type. -/
def laidFirst_fits : FirstFamilyText Z d (keyBook K₀) := laidFirst Z d K₀

/-- The laid letter has the join's type. -/
def laidSaid_fits : OwnLetterText Z (keyBook K₀) := laidSaid Z d K₀

variable {Z d K₀} {R₂ R₃ : Type}
  (Tied : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Prop)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi TableKey Unit Unit Unit)
  (U₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₁ (keyFileDescription d.source d.numbers d.later).Cl
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
  (U₂ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₂ (keyFileDescription d.source d.numbers d.later).Cl Empty
    (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit TableKey)
  (U₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Thread (keyBook K₀)
    (keyFileDescription d.source d.numbers d.later).S₃ (keyFileDescription d.source d.numbers d.later).Cl
    (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit Xi)
  (S₁ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)
  (S₂ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey) Unit → Prop)
  (S₃ : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → Xi → Nat → Coins (keyBook K₀) →
    Mid (Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Xi Unit) Unit → Prop)

/-- **The join's twelve fields, at letters.** A twin of TheLots (E2E/OfflineJoin.lean). -/
structure LotsAt (R₂ R₃ : Type) : Prop where
  sits : ∀ w x, Tied w x → (keyFileDescription d.source d.numbers d.later).okStart x = true →
    Sits (keyFileDescription d.source d.numbers d.later) H (U₁ w x) (U₂ w x) (U₃ w x)
  firstOwes : ∀ w x, Tied w x → OwesS (U₁ w x) (S₁ w x)
  lastOwes : ∀ w x, Tied w x → OwesS (U₃ w x) (S₃ w x)
  firstNext : ∀ w x, Tied w x → ∀ b, SaidNext (U₁ w x) (S₁ w x) b
  lastNext : ∀ w x, Tied w x → ∀ b, SaidNext (U₃ w x) (S₃ w x) b
  firstYes : ∀ w x, Tied w x →
    YesS (U₁ w x) (S₁ w x) (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder)
  lastYes : ∀ w x, Tied w x →
    YesS (U₃ w x) (S₃ w x) (fallsBy [] (keyFileDescription d.source d.numbers d.later).second.blocksInOrder)
  testU : ∀ w x, Tied w x → PlaysS (U₂ w x) (S₂ w x) 9 ∧ BehindS (U₂ w x) (S₂ w x) 9 ∧
    ExchangeS (U₂ w x) (S₂ w x) 9 ∧ RidesPastS (U₂ w x) (S₂ w x) 9
  testOmega : ∀ w x, Tied w x → PlaysS (U₂ w x) (S₂ w x) 10 ∧ BehindS (U₂ w x) (S₂ w x) 10 ∧
    ExchangeS (U₂ w x) (S₂ w x) 10 ∧ RidesPastS (U₂ w x) (S₂ w x) 10
  testYesU : ∀ w x, Tied w x → AcceptedS (U₂ w x) (S₂ w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder) 9
  testYesOmega : ∀ w x, Tied w x → AcceptedS (U₂ w x) (S₂ w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder) 10
  run : ∀ w x (c : CoinOne (keyBook K₀) R₂ R₃), Tied w x →
    AtRunS (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d)) (U₁ w x)
      (U₂ w x) (U₃ w x) (S₁ w x) (S₂ w x) (S₃ w x) w x c

/-- **OF THE FIRST CHAIN NOTHING IS LEFT**: LeftJoin at the laid thread, at every input. -/
theorem leftJoin_laid {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}
    (hs : AtPublicFiles.AtFiles.KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    LeftJoin d (laterValue Z d K₀) w x :=
  leftJoin_of_six_laid hs scope hK
    { exchangeLayer := lotExchangeLayer d.source d.numbers d.later (offlineValue (files := Z) d)
        matrixReader (laterValue Z d K₀) w.1 w.2.1 x hs scope _
      playsRanges := (fiveAtRanges d (laterValue Z d K₀) w.1 w.2.1 x hs scope hK rfl _
        (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder)).plays
      acceptedRanges := (fiveAtRanges d (laterValue Z d K₀) w.1 w.2.1 x hs scope hK rfl _ _).accepted
      pile := exchangeS_of _ _
        (exchange_batt hs scope (firstPublic_atValue hs scope) (lotHeardOfFold hs scope)
          (coinsAtSlots hK hs scope (firstPublic_atValue hs scope)))
      eval := fun _ hb _ _ _ _ _ _ _ _ hT hd hS =>
        eval_item hs scope (firstPublic_atValue hs scope) (w_public hs scope)
          (lotHeardOfFold hs scope) hb hT hd hS }

/-- **The first chain's three fields at the laid thread and letter**, at every input: from the public files' premises alone. -/
theorem firstLaid {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :
    OwesS (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) ∧
      (∀ b, SaidNext (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) b) ∧
      YesS (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x)
        (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) :=
  have h := joinFirst hd scope live rfl (leftJoin_laid (sourced_of_description hd live) scope hK w x)
  ⟨h.1, joinFirstNext (fun _ _ => True) w x trivial, h.2⟩

/-- **WHAT IS LEFT OF THE JOIN**, at the laid first chain. A premise's form: no member is known. -/
structure LeftLots (R₂ R₃ : Type) : Prop where
  /-- a run: six clauses of AtRunS -/
  run : ∀ w x (c : CoinOne (keyBook K₀) R₂ R₃), Tied w x →
    LeftRun d (laterValue Z d K₀) (U₂ w x) (U₃ w x) (S₂ w x) (S₃ w x) w x c
  sits : ∀ w x, Tied w x → (keyFileDescription d.source d.numbers d.later).okStart x = true →
    Sits (keyFileDescription d.source d.numbers d.later) H (laidFirst Z d K₀ w x) (U₂ w x) (U₃ w x)
  lastOwes : ∀ w x, Tied w x → OwesS (U₃ w x) (S₃ w x)
  lastNext : ∀ w x, Tied w x → ∀ b, SaidNext (U₃ w x) (S₃ w x) b
  lastYes : ∀ w x, Tied w x →
    YesS (U₃ w x) (S₃ w x) (fallsBy [] (keyFileDescription d.source d.numbers d.later).second.blocksInOrder)
  testU : ∀ w x, Tied w x → PlaysS (U₂ w x) (S₂ w x) 9 ∧ BehindS (U₂ w x) (S₂ w x) 9 ∧
    ExchangeS (U₂ w x) (S₂ w x) 9 ∧ RidesPastS (U₂ w x) (S₂ w x) 9
  testOmega : ∀ w x, Tied w x → PlaysS (U₂ w x) (S₂ w x) 10 ∧ BehindS (U₂ w x) (S₂ w x) 10 ∧
    ExchangeS (U₂ w x) (S₂ w x) 10 ∧ RidesPastS (U₂ w x) (S₂ w x) 10
  testYesU : ∀ w x, Tied w x → AcceptedS (U₂ w x) (S₂ w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder) 9
  testYesOmega : ∀ w x, Tied w x → AcceptedS (U₂ w x) (S₂ w x)
    (fallsBy [] (keyFileDescription d.source d.numbers d.later).shared.blocksInOrder) 10

variable {Tied H U₂ U₃ S₂ S₃}

/-- **THE JOIN's TWELVE FIELDS AT THE LAID FIRST CHAIN, FROM WHAT IS LEFT.** -/
theorem lotsFromLeft (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK : fullPub = some K₀)
    (rel : ∀ w x, Tied w x → (laterValue Z d K₀).Rel w.1 w.2.1 x)
    (left : LeftLots (K₀ := K₀) Tied H U₂ U₃ S₂ S₃ R₂ R₃) :
    LotsAt Tied H (laidFirst Z d K₀) U₂ U₃ (laidSaid Z d K₀) S₂ S₃ R₂ R₃ where
  sits := left.sits
  firstOwes := joinFirstOwes Tied hd scope live rfl fun w x _ =>
    leftJoin_laid (sourced_of_description hd live) scope hK w x
  lastOwes := left.lastOwes
  firstNext := joinFirstNext Tied
  lastNext := left.lastNext
  firstYes := joinFirstYes Tied hd scope live rfl fun w x _ =>
    leftJoin_laid (sourced_of_description hd live) scope hK w x
  lastYes := left.lastYes
  testU := left.testU
  testOmega := left.testOmega
  testYesU := left.testYesU
  testYesOmega := left.testYesOmega
  run := runFromLeft Tied U₂ U₃ S₂ S₃ live hd scope hK rel
    (fun w x ht => rel_passes (rel w x ht)) left.run

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.leftJoin_laid
#print axioms AtPublicFiles.FirstH.Lots.firstLaid
#print axioms AtPublicFiles.FirstH.Lots.lotsFromLeft
