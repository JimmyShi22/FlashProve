-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-P2) `lookupFiveAtTheKeyAtTheNamedLetters` (E2E/Lookup/Key/LookupFiveAtTheKey.lean) with the two senders' debts
  paid at the two owners' sendings (`maskEntriesReadAsTheCoinsAtTheSendersRows`) and the field `bits` of `WitnessReadsAsTheProver`
  paid from the sender's main rows (`bitsReadAsTheSendersMainRows`), and its field `keys` from the stored table's cells
  (`keysReadAsTheIndexsMatrix`): that the thread's witness reads those senders' rows and the cells spell the matrix is left.

AtFullSide/Honest/K3/Key/LookupFiveAtTheKeyAtTheSendersRows.lean. One theorem, with its proof.

  `lookupFiveAtTheKeyAtTheSendersRows`   **`FiveAtBorder` at 4 and 10 at the named letters**, at every `Said` and every fall

WHAT STAYS A PREMISE:
  `halfFirst`, `halfSecond`: the half found at each lookup's place is the lookup's seat
  `inRange`: a valid input's matrix is in range: at `laterValue`'s `Rel`
  `byText`: `LookupsKeepByText`: at `kindFirst`
  `reads`: `ReadsL`: `readsLK` at the library's `baseK`
  `witnessReads`: the thread's witness reads the senders' rows (its fields `masks` and `main`)
  `same`: what reads alike is `same`
  `cells`: the stored table's cells spell the index's matrix. This debt is the neighbour of the item `pinT`
      (`meetsT r w.cells`): whoever lays `filling.cells` pays both with one definition

`witnessReads` is said at every pair of coins that are the book's at the two owners' addresses (`OwnIs`), because the join gives
such a pair by "there are".

Limits. `KeySourced`, `InScope` and `fullPub = some data` are public premises. Each statement holds also where the thread stands
at nothing. At `filling.Rel` false everywhere the premises on valid inputs hold and the end is idle.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import AtFullSide.Honest.K3.Key.MaskEntriesReadAsTheCoinsAtTheSendersRows
import AtFullSide.Honest.K3.Key.BitsReadAsTheSendersMainRows
import E2E.Lookup.Key.KeysReadAsTheIndexsMatrix
import E2E.Lookup.Key.LookupFiveAtTheKey

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open OnBytes (E)
open OnBytes.Slice (readE)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open ProofFile.Honest
open ProofFile.Honest.K1 (dueR)
open ProofFile.Honest.K3 (keyOwners proverSideOfLookupInChain)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace msgPlace idxPlace rideMsg)
open AtPublicFiles.KeyThread
open AtPublicFiles.KeyValues (lookOf witAt keyWit keyReads keyJobs0 keyJobs1 multiplicitiesSending indexMaskSending)

/-- **`FiveAtBorder` AT THE TWO LOOKUPS AT THE NAMED LETTERS, WITH THE SENDERS' DEBTS PAID**, at every `Said` and every fall. -/
theorem lookupFiveAtTheKeyAtTheSendersRows {Rc Cells M Smp Rec X X' : Type} (data : KeyPub)
    (written : fullPub = some data) {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}
    {filling : KeyFill (keyBook data) FullSizeMatrix Rc Cells M Smp Rec} {w₀ : FullSizeMatrix} {rc : Rc} {x : Xi}
    {halves : List (Placed (Local FullSizeMatrix Rc Xi Unit) (Local FullSizeMatrix Rc Xi Unit) X')}
    {tables : Fmt.TreeSource → Coins (keyBook data) → Local FullSizeMatrix Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table}
    {files : VerifierAndGoals.PublicFiles} (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (byText : LookupsKeepByText filling)
    (said : Nat → Coins (keyBook data) → Mid (Local FullSizeMatrix Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (halfFirst : halves.find? (fun h => h.place == lookPlace 0) =
      some (proverSideOfLookupInChain (keyOwners (lookOf source numbers 0).face) keyReads (keyJobs0 source)
        (keyWit matrixWeights source) (lookOf source numbers 0)))
    (halfSecond : halves.find? (fun h => h.place == lookPlace 1) =
      some (proverSideOfLookupInChain (keyOwners (lookOf source numbers 1).face) keyReads (keyJobs1 source)
        (keyWit matrixWeights source) (lookOf source numbers 1)))
    (inRange : ∀ input, (laid₁ source numbers later filling w₀ rc x halves tables).valid input →
      VerifiableInference.OnPublicFiles.Flat.InRange input.w₀)
    (own₀ : X)
    (witnessReads : ∀ number, number < 2 → ∀ ownCoins keyCoins,
      OwnIs (keyBook data) 0 ⟨msgPlace, 0⟩
        (dueR (multiplicitiesSending (Rc := Rc) (X := X) matrixWeights source).P rideMsg) ownCoins →
      OwnIs (keyBook data) 0 ⟨idxPlace, 0⟩
        (dueR (indexMaskSending (W₀ := FullSizeMatrix) (Rc := Rc) (X := X) source).P fun _ => none) keyCoins →
      WitnessReadsTheSendersRows data matrixWeights source numbers later filling w₀ rc x halves tables own₀ number
        (lookOf source numbers number).base ownCoins keyCoins)
    (same : ∀ a b, readE a = readE b → filling.R.same a b)
    (cells : ∀ number, number < 2 → CellsSpellTheIndexsMatrix filling matrixWeights source number) :
    ∀ b ∈ [4, 10], FiveAtBorder (laid₁ source numbers later filling w₀ rc x halves tables) said fall b := by
  refine lookupFiveAtTheKey data written sourced scope reads byText said fall (lookOf source numbers)
    (witAt matrixWeights source) (keyReaderAt matrixWeights) (bitReaderAt matrixWeights) ?_
    (fun number below => lookupValuesAtTheNamedLetters _ inRange number below) ?_ ?_
  · intro number below
    refine lookupIsSeatedAtTheNamedLetters data source numbers later filling w₀ rc x halves tables sourced scope
      number below ?_
    have isLookup : number = 0 ∨ number = 1 := by omega
    rcases isLookup with rfl | rfl
    · exact halfFirst.trans (congrArg some (firstSeatIsItsOwnLookups matrixWeights source _ _))
    · exact halfSecond.trans (congrArg some (secondSeatIsItsOwnLookups matrixWeights source _ _))
  · intro number below
    obtain ⟨ownCoins, keyCoins, ownIs, keyIs, -⟩ := maskEntriesReadAsTheCoinsAtTheSendersRows (X := X)
      data matrixWeights source numbers later filling w₀ rc x halves tables own₀ sourced scope written number
      (lookOf source numbers number).base below
    exact ⟨same, fun k input heard _ part _ i _ => keysReadAsTheIndexsMatrix filling matrixWeights source sourced scope
        number (cells number below) k input heard part i, bitsReadAsTheSendersMainRows data matrixWeights source numbers later filling
      w₀ rc x halves tables own₀ sourced scope number (lookOf source numbers number).base below ownCoins keyCoins
      (witnessReads number below ownCoins keyCoins ownIs keyIs)⟩
  · intro number below
    obtain ⟨ownCoins, keyCoins, ownIs, keyIs, conclusion⟩ := maskEntriesReadAsTheCoinsAtTheSendersRows (X := X)
      data matrixWeights source numbers later filling w₀ rc x halves tables own₀ sourced scope written number
      (lookOf source numbers number).base below
    exact conclusion (witnessReads number below ownCoins keyCoins ownIs keyIs)

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupFiveAtTheKeyAtTheSendersRows
