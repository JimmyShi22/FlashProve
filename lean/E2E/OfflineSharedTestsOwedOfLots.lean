-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineSharedTestsOwedOfLots.lean: owed AT THE ROWS OF THE SHARED CHAIN's TWO PROXIMITY TESTS (`OwedSharedAt`, E2E/OfflineRowsByPlace.lean), AT THE LAID
SIMULATORS AND LETTERS: the four tests' lists (`k12Lists`, Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsOffline.lean) over any value T of the other lists, and the
four tests' letters (`testConditions`, E2E/OfflineTestRowsByPlace.lean) over any value t of the others: from what is spent of the offline
prover's debts on acceptance (`LotsSpent`, E2E/OfflineLotsSpent.lean) at the table's letter `ttLaid` and the letter `keepsKey`.

  `foldedLetters_laid`, `omegaLetters_laid`   what the two rows ask of the simulators and the letters holds there: by unfolding
  `testOnFoldedRowOwed_of_lots`, `testOnOmegaOwed_of_lots`   owed at the two rows

Limits. CONDITIONAL on `LotsSpent`: no thread is shown here to meet any field. The limits of
E2E/OfflineFoldedOwedOfLots.lean and E2E/OfflineOmegaOwedOfLots.lean stand. Nothing on any property.
-/
import E2E.OfflineTestRowsByPlace
import E2E.OfflineFoldedOwedOfLots
import E2E.OfflineOmegaOwedOfLots

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Sim2 (simOmegaKey stateAtOmegaKey pKU k12Lists)
open ProofFile.Honest.K12.AtKey (keepsKey)
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open LPFD.Full (XF)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Honest (Eight)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles.Full (PF)
open AtPublicFiles.OfflineRows.Folded (FoldedLetters)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) sharedTestsOwedOfLotsPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) sharedTestsOwedOfLotsValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) sharedTestsOwedOfLotsDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} (d : OfflineDescription) (T : TheirSimulators)
  (t : TheirConditions (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Unit Unit)

/-- The sixteen lists: the four tests' over T. -/
abbrev listsOver : OfflineSimulators :=
  laidSimulators (senderValue (files := Z) d)
    (k12Lists T d.source d.numbers d.later (offlineSenders (files := Z) d))

/-- The rows' letters: the four tests' over t. -/
abbrev lettersOver : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness
    TableKey Unit Unit Unit :=
  laidConditions _ offlineProverCoinCounts (senderValue (files := Z) d) (testConditions d t)

/-- What the row of the test on the folded row's group asks of the simulators and the letters holds at the laid lists and letters. -/
theorem foldedLetters_laid :
    FoldedLetters (Xs := d.source) (N := d.numbers) (Pl := d.later) (senderValue (files := Z) d)
      (listsOver (Z := Z) d T) (lettersOver (Z := Z) d t) :=
  ⟨rfl, rfl, fun _ _ _ h => h⟩

/-- The simulators' job at the test on Omega's group, at the laid lists and letters. -/
abbrev omegaSimAtFiles : SimJob TableKey :=
  simOmegaKey (stateAtOmegaKey d.source d.numbers d.later (offlineSenders (files := Z) d).send (pKU d.later))

/-- What the row of the test on Omega's group asks of the simulators and the letters holds at the laid lists and letters. -/
theorem omegaLetters_laid :
    OmegaLetters (files := Z) d (listsOver (Z := Z) d T) (lettersOver (Z := Z) d t)
      (omegaSimAtFiles (Z := Z) d) :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ h => h, fun _ _ _ h => h⟩

variable {d}
variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub) (B : Eight (parKey d.source PF))

/-- **owed at the row of the test on the folded row's group.** -/
theorem testOnFoldedRowOwed_of_lots {U₁ : FirstFamily Z d (keyBook K₀)}
    {U₃ : LastFamily Z d (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d U₁ U₃ S₁ S₃) :
    OwedSharedAt (files := Z) d (listsOver (Z := Z) d T) (lettersOver (Z := Z) d t) 
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) foldedTestPlace :=
  foldedOwed_of_lots ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ hd scope live hK₀ hs L _ _
    (foldedLetters_laid d T t)

/-- **owed at the row of the test on Omega's group.** -/
theorem testOnOmegaOwed_of_lots {U₁ : FirstFamily Z d (keyBook K₀)}
    {U₃ : LastFamily Z d (keyBook K₀)} {S₁ S₃ : OwnLetter Z (keyBook K₀)}
    (hd : offlineDescription Z = .ok d) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (L : LotsSpent (Z := Z) ℓ Nm Mg₀ tk (ttLaid Z d K₀ Z₀ B) rest keepsKey Vd Z₀ d U₁ U₃ S₁ S₃) :
    OwedSharedAt (files := Z) d (listsOver (Z := Z) d T) (lettersOver (Z := Z) d t) 
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK)
      ((partsOfDescription (files := Z) d).prover d) omegaTestPlace :=
  omegaOwed_of_lots ℓ Nm Mg₀ tk rest Vd Z₀ B hd scope live hK₀ hs hN L _ _ _
    (omegaLetters_laid d T t)

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.foldedLetters_laid
#print axioms AtPublicFiles.OfflineRows.omegaLetters_laid
#print axioms AtPublicFiles.OfflineRows.testOnFoldedRowOwed_of_lots
#print axioms AtPublicFiles.OfflineRows.testOnOmegaOwed_of_lots
