-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR:  THE FIVE STATEMENTS `FiveAtBorder` (Honest/Thread/FiveAtBorder.lean) AT NUMBERS 4 AND 10 OF THE KEY FILE's
  FIRST THREAD, at every `Said` and every fall; then the same at the named letters, with every premise that has a payer paid.

E2E/Lookup/Key/LookupFiveAtTheKey.lean. Theorems with proofs.

  `lookupFiveAtTheKey`                  **`FiveAtBorder` at 4 and 10**, under the exchange's premises and `LookupsKeepByText`
  `lookupIsSeatedAtTheNamedLetters`     `LookupIsSeatedAtTheKey` at `lookOf`, `witAt` and the two readers, from the half by name
  `lookupValuesAtTheNamedLetters`       `LookupValuesMeetTheRelation` at the two readers, at matrices in range
  `maskEntriesAtTheNamedLetters`        `MaskEntriesReadAsTheCoins` from the sender's two debts and the witness's reading
  `lookupFiveAtTheKeyAtTheNamedLetters` **`FiveAtBorder` at 4 and 10 at the named letters**

WHAT STAYS A PREMISE OF THE LAST:
  `halfFirst`, `halfSecond`: the half found at each lookup's place is the lookup's seat
  `inRange`: a valid input's matrix is in range: whoever lays `filling.Rel` at the offline prover
  `byText`: `LookupsKeepByText`
  `reads`: `ReadsL`: `LettersOk.readsL`, or `readsLK` at the library's `baseK`
  `ownLays`, `keyLays`: the two senders lay their coins in the order of taking
  `witnessReads`, `witness`: the thread's witness reads the prover's messages and records: not shown here

Limits. `KeySourced`, `InScope` and `fullPub = some data` are public premises. Each statement holds also where the thread stands
at nothing. Nothing here shows that a filling meets the premises. `inRange` HAS NO HOLDER YET: `laid₁`'s `valid` is
`w = ⟨w₀, rc, x, ()⟩ ∧ filling.Rel w₀ rc x`, so `filling.Rel` must give the range, and `Rel` is a letter that this file does not
lay. At `Rel := False` all premises on valid inputs hold and the end is idle: whoever lays `Rel` at the offline prover owes it.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupExchangeAtTheKey
import E2E.Lookup.Key.LookupPlaysAndIsAcceptedAtTheKey
import E2E.Lookup.Key.LookupValuesAtTheNamedParts
import E2E.Lookup.Key.LookupsOfTheNamedPartsStandAtTheirBorders
import E2E.Lookup.Key.MaskEntriesReadAsTheCoins
import Johnson.Desc.ProofFile.Honest.Thread.FiveAtBorder

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open OnBytes (E)
open OnBytes.Slice (readE)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces mkOf)
open Johnson.RunOne.KeyRows1 (plan₁)
open ProofFile.Honest
open ProofFile.Honest.K3 (At Ask fastJobs keyOwners proverSideOfLookupInChain)
open ProofFile.Honest.K3.Parts.Key (rowK)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace msgPlace idxPlace tableAt)
open AtPublicFiles.KeyThread
open AtPublicFiles.KeyValues (lookOf witAt jobsAt keyWit keyReads keyJobs0 keyJobs1)
open Inst.Model.Layout (kRef)

/-! ## 1 The five at the two lookups -/

/-- **`FiveAtBorder` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD**, at every `Said` and every fall. -/
theorem lookupFiveAtTheKey {W₀ Rc Cells M Smp Rec X' : Type} (data : KeyPub) (written : fullPub = some data)
    {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}
    {filling : KeyFill (keyBook data) W₀ Rc Cells M Smp Rec} {w₀ : W₀} {rc : Rc} {x : Xi}
    {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
    {tables : Fmt.TreeSource → Coins (keyBook data) → Local W₀ Rc Xi Unit → List Fmt.Drawn →
      VerifiableInference.Desc.Place × Table}
    {files : VerifierAndGoals.PublicFiles} (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (byText : LookupsKeepByText filling)
    (said : Nat → Coins (keyBook data) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (lookup : Nat → At) (wit : Nat → Local W₀ Rc Xi Unit → Ask)
    (keyReader : Nat → Local W₀ Rc Xi Unit → Nat → Nat → E) (bitReader : Nat → Local W₀ Rc Xi Unit → Nat → E)
    (seated : ∀ number, number < 2 → LookupIsSeatedAtTheKey halves
      (laid₁ source numbers later filling w₀ rc x halves tables).bs number (lookup number) (wit number)
      (keyReader number) (bitReader number))
    (values : ∀ number, number < 2 → LookupValuesMeetTheRelation
      (laid₁ source numbers later filling w₀ rc x halves tables).valid number (keyReader number) (bitReader number))
    (witness : ∀ number, number < 2 → WitnessReadsAsTheProver filling source number (lookup number).base
      (keyReader number) (bitReader number))
    (masks : ∀ number, number < 2 →
      MaskEntriesReadAsTheCoins data source numbers later filling w₀ rc x halves tables number) :
    ∀ b ∈ [4, 10], FiveAtBorder (laid₁ source numbers later filling w₀ rc x halves tables) said fall b := by
  have two := sourceLookupsAreTheWrittenLookups sourced scope
  intro b atLookup
  have exchange := lookupExchangeAtTheKey data written sourced scope reads said lookup wit keyReader bitReader
    seated values witness masks b atLookup
  have four : b ∈ [4, 10] → (b = 4 ∨ b = 10) := by
    intro member
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using member
  rcases four atLookup with rfl | rfl
  · obtain ⟨plays, behind, rides, accepted⟩ := lookupFourStatementsAtTheKey source numbers later filling w₀ rc x
      sourced scope two byText reads (keyOwners (lookup 0).face) (lookup 0)
      (fastJobs (writtenFace 0) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup 0))).asked (wit 0) said fall 4 atLookup
      (seated 0 (by decide)).half (seated 0 (by decide)).place (seated 0 (by decide)).face
      (seated 0 (by decide)).base
    exact ⟨plays, behind, exchange, rides, accepted⟩
  · obtain ⟨plays, behind, rides, accepted⟩ := lookupFourStatementsAtTheKey source numbers later filling w₀ rc x
      sourced scope two byText reads (keyOwners (lookup 1).face) (lookup 1)
      (fastJobs (writtenFace 1) (rowK 1 ⟨kRef, 3076096⟩ (writtenLookup 1))).asked (wit 1) said fall 10 atLookup
      (seated 1 (by decide)).half (seated 1 (by decide)).place (seated 1 (by decide)).face
      (seated 1 (by decide)).base
    exact ⟨plays, behind, exchange, rides, accepted⟩

/-! ## 2 At the named letters -/

section
variable {Rc Cells M Smp Rec X' : Type} (data : KeyPub) (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill (keyBook data) FullSizeMatrix Rc Cells M Smp Rec) (w₀ : FullSizeMatrix) (rc : Rc) (x : Xi)
  (halves : List (Placed (Local FullSizeMatrix Rc Xi Unit) (Local FullSizeMatrix Rc Xi Unit) X'))
  (tables : Fmt.TreeSource → Coins (keyBook data) → Local FullSizeMatrix Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  {files : VerifierAndGoals.PublicFiles}

/-- **`lookOf`, `witAt` and the two readers are seated**, where the half at the place is the seat at the lookup's record. -/
theorem lookupIsSeatedAtTheNamedLetters (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2)
    (half : halves.find? (fun h => h.place == lookPlace number) =
      some (proverSideOfLookupInChain (keyOwners (lookOf source numbers number).face) keyReads (jobsAt source number)
        (witAt matrixWeights source number) (lookOf source numbers number))) :
    LookupIsSeatedAtTheKey halves (laid₁ source numbers later filling w₀ rc x halves tables).bs number
      (lookOf source numbers number) (witAt matrixWeights source number) (keyReaderAt matrixWeights number)
      (bitReaderAt matrixWeights number) := by
  obtain ⟨place, -, face, base⟩ := lookOfStandsAtItsBorder source numbers later filling w₀ rc x
    (halves := halves) (tables := tables) sourced scope number below
  refine ⟨?_, place, face, base, fun input heard =>
    witAtIsTheWrittenRecord matrixWeights sourced scope number below input heard⟩
  rw [half, jobsAtAreTheWrittenSums sourced scope number below]
  rfl

/-- **The two readers meet the relation at a matrix in range.** -/
theorem lookupValuesAtTheNamedLetters (valid : Local FullSizeMatrix Rc Xi Unit → Prop)
    (inRange : ∀ input, valid input → VerifiableInference.OnPublicFiles.Flat.InRange input.w₀) (number : Nat)
    (below : number < 2) :
    LookupValuesMeetTheRelation valid number (keyReaderAt matrixWeights number)
      (bitReaderAt matrixWeights number) :=
  { relation := fun input isValid theta alpha =>
      valuesMeetTheRelationAtTheNamedParts input (inRange input isValid) number below theta alpha
    idle := fun input _ u inTable j notReal inBlock =>
      valuesAreIdleAtTheNamedParts input number below u inTable j notReal inBlock }

/-- **The mask entries read as the coins**, from the two senders' debts and the witness's reading. -/
theorem maskEntriesAtTheNamedLetters (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (written : fullPub = some data) (number : Nat) (below : number < 2)
    (ownEntry keyEntry : Coins (keyBook data) → Local FullSizeMatrix Rc Xi Unit → List Fmt.Drawn → Nat → E)
    (ownLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨msgPlace, 0⟩
      (one₀ source).ranges.message.shape.maskRows (tableAt data.sMsg 0) (takesOfBothLookups data).1 ownEntry)
    (keyLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨idxPlace, 0⟩
      (one₀ source).indexMasks.shape.maskRows (tableAt data.sIdx 0) (takesOfBothLookups data).2 keyEntry)
    (witnessReads : ∀ k s (m : Mid (Local FullSizeMatrix Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables) (borderOfLookup number) k s m E →
      ∀ more ν,
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
            ⟨(one₀ source).ranges.messageId, ν⟩) =
          readE (ownEntry k m.st.input (m.st.heard ++ more) ν) ∧
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) ⟨s.idx, ν⟩) =
          readE (keyEntry k m.st.input (m.st.heard ++ more) ν)) :
    MaskEntriesReadAsTheCoins data source numbers later filling w₀ rc x halves tables number :=
  maskEntriesReadAsTheCoinsOfTheTwoDebts data source numbers later filling w₀ rc x sourced scope written number
    below ownEntry keyEntry ownLays keyLays witnessReads

end

/-- **`FiveAtBorder` AT THE TWO LOOKUPS AT THE NAMED LETTERS**, at every `Said` and every fall. -/
theorem lookupFiveAtTheKeyAtTheNamedLetters {Rc Cells M Smp Rec X' : Type} (data : KeyPub)
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
    (ownEntry keyEntry : Coins (keyBook data) → Local FullSizeMatrix Rc Xi Unit → List Fmt.Drawn → Nat → E)
    (ownLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨msgPlace, 0⟩
      (one₀ source).ranges.message.shape.maskRows (tableAt data.sMsg 0) (takesOfBothLookups data).1 ownEntry)
    (keyLays : SenderLaysItsCoinsInTheOrderOfTaking data ⟨idxPlace, 0⟩
      (one₀ source).indexMasks.shape.maskRows (tableAt data.sIdx 0) (takesOfBothLookups data).2 keyEntry)
    (witnessReads : ∀ number, number < 2 → ∀ k s (m : Mid (Local FullSizeMatrix Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables) (borderOfLookup number) k s m E →
      ∀ more ν,
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) [])
            ⟨(one₀ source).ranges.messageId, ν⟩) =
          readE (ownEntry k m.st.input (m.st.heard ++ more) ν) ∧
        readE (mkOf (plan₁ (one₀ source)) filling.R
            (filling.wit k m.st.input.w₀ m.st.input.rc (m.st.heard ++ more) []) ⟨s.idx, ν⟩) =
          readE (keyEntry k m.st.input (m.st.heard ++ more) ν))
    (witness : ∀ number, number < 2 → WitnessReadsAsTheProver filling source number
      (lookOf source numbers number).base (keyReaderAt matrixWeights number) (bitReaderAt matrixWeights number)) :
    ∀ b ∈ [4, 10], FiveAtBorder (laid₁ source numbers later filling w₀ rc x halves tables) said fall b := by
  refine lookupFiveAtTheKey data written sourced scope reads byText said fall (lookOf source numbers)
    (witAt matrixWeights source) (keyReaderAt matrixWeights) (bitReaderAt matrixWeights) ?_
    (fun number below => lookupValuesAtTheNamedLetters _ inRange number below) witness
    (fun number below => maskEntriesAtTheNamedLetters data source numbers later filling w₀ rc x halves tables
      sourced scope written number below ownEntry keyEntry ownLays keyLays (witnessReads number below))
  intro number below
  refine lookupIsSeatedAtTheNamedLetters data source numbers later filling w₀ rc x halves tables sourced scope
    number below ?_
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · exact halfFirst.trans (congrArg some (firstSeatIsItsOwnLookups matrixWeights source _ _))
  · exact halfSecond.trans (congrArg some (secondSeatIsItsOwnLookups matrixWeights source _ _))

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupFiveAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupIsSeatedAtTheNamedLetters
#print axioms AtPublicFiles.Lookup.Key.lookupValuesAtTheNamedLetters
#print axioms AtPublicFiles.Lookup.Key.maskEntriesAtTheNamedLetters
#print axioms AtPublicFiles.Lookup.Key.lookupFiveAtTheKeyAtTheNamedLetters
