-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: the named parts of the key's prover (E2E/KeyLookups.lean) read the two readers of
  E2E/Lookup/Key/LookupDataMeetTheRelationAtTheWrittenKey.lean: the record that the lookups' rows are handed is the structure of
  keys and bits of those readers, the sums are the sums at the written numbers, and at a matrix in range the readers meet the
  relation after the challenge.

E2E/Lookup/Key/LookupValuesAtTheNamedParts.lean. Theorems with proofs.

  `theKeyRecordIsTheLibrarysRecord`       `hiddenKey` is `hidK` of the library's two readers
  `onHalfIsJobsThrough`, `firstSeatIsItsOwnLookups`, `secondSeatIsItsOwnLookups`   a seat at half a record is the seat at that record
  `writtenStructure`, `keyReaderAt`, `bitReaderAt`   the two readers, by the lookup's number
  `lookAtIsTheWrittenLookup`, `jobsAtAreTheWrittenSums`, `witAtIsTheWrittenRecord`   in scope, at the written numbers
  `matrixWeights`                         the reader of a matrix, written out
  `valuesMeetTheRelationAtTheNamedParts`  **`KeyMidHyp`** at a matrix in range
  `valuesAreIdleAtTheNamedParts`          the bits read 0 at planes that are not real

Limits. That the prover runs at a matrix in range alone is a premise of the last two. The written sizes alone. No round, no sumcheck,
no mask, no coin. Nothing on any property of a protocol.
-/
import E2E.KeyLookups
import E2E.ObjectAtFiles
import E2E.Lookup.Key.LookupDataMeetTheRelationAtTheWrittenKey
import E2E.Lookup.Key.OneFaceUnderThreeNames
import Johnson.Desc.ProofFile.Honest.K3.Key.OwnedSeatReadsThroughAHalf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Lookup.Key
open OnBytes
open OnBytes.Slice (GE readE toF ofF)
open OnBytes.Params (WfLookup)
open ProofFile.Honest (Weights)
open ProofFile.Honest.K3 (Ask At LookJobs Owners proverSideOfLookupInChain fastJobs Hidden)
open ProofFile.Honest.K3.Key (jobsThrough ownedSeatReadsThroughAHalf)
open ProofFile.Honest.K3.Parts.Key (faceK rowK hidK KeyMidHyp)
open AtPublicFiles.AtFiles (KeySourced FullSizeMatrix)
open AtPublicFiles.Key (planesVal)
open AtPublicFiles.KeyFile (In1)
open AtPublicFiles.KeyValues (WitK witAt keyWit onHalf jobsAt keyJobs0 keyJobs1 keyReads lookAt faceAt oneOf matOf mainOf matrixEntryOf readOf)
open VerifiableInference.Desc.Key (Source LaterPlaces lookupsOf keyVec bitVec)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)

/-! ## 1 The record and the seat -/

/-- **The record that a lookup's stages read is the structure of keys and bits of the library's two readers.** -/
theorem theKeyRecordIsTheLibrarysRecord (ranges : Params.WfPublic) (codes : Codes) (l : Nat) (m : Wf.Matrix)
    (L : WfLookup) (mat : Nat → Nat → F) (valB : Nat → E) :
    AtPublicFiles.KeyLookup.hiddenKey ranges codes l m L mat valB = hidK L (keyVec m L mat) (bitVec ranges codes l valB) :=
  rfl

/-- The sums at a half (`onHalf`) are the sums read through a map (`jobsThrough`). -/
theorem onHalfIsJobsThrough (pr : WitK → Ask) (J : LookJobs Ask) : onHalf pr J = jobsThrough pr J := rfl

section
variable {V₁ W₀ Rc X₁ : Type} (f : W₀ → Weights) (source : Source) (owners : Owners) (lookup : At)

/-- **The seat at the first half of the record is the seat at the first lookup's record.** -/
theorem firstSeatIsItsOwnLookups :
    proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners keyReads (keyJobs0 source) (keyWit (Rc := Rc) f source) lookup =
      proverSideOfLookupInChain owners keyReads (jobsAt source 0) (witAt (Rc := Rc) f source 0) lookup :=
  ownedSeatReadsThroughAHalf owners keyReads Prod.fst (jobsAt source 0) (keyWit (Rc := Rc) f source) lookup

/-- **The like at the second.** -/
theorem secondSeatIsItsOwnLookups :
    proverSideOfLookupInChain (V₁ := V₁) (X₁ := X₁) owners keyReads (keyJobs1 source) (keyWit (Rc := Rc) f source) lookup =
      proverSideOfLookupInChain owners keyReads (jobsAt source 1) (witAt (Rc := Rc) f source 1) lookup :=
  ownedSeatReadsThroughAHalf owners keyReads Prod.snd (jobsAt source 1) (keyWit (Rc := Rc) f source) lookup

end

/-! ## 2 The two readers, by the lookup's number -/

/-- The public structure of a written lookup, by its number. -/
abbrev writtenStructure (number : Nat) : WfLookup := if number = 0 then lk0Full else lk1Full

/-- **The keys' reader.** -/
def keyReaderAt {W₀ Rc : Type} (f : W₀ → Weights) (number : Nat) (input : In1 W₀ Rc) : Nat → Nat → E :=
  keyVec ⟨kRef, 3076096⟩ (writtenStructure number) (matOf f input)

/-- **The bits' reader.** -/
def bitReaderAt {W₀ Rc : Type} (f : W₀ → Weights) (number : Nat) (input : In1 W₀ Rc) : Nat → E :=
  bitVec keyFull.ranges.x keyFull.codes number
    (planesVal (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) 1)

section
variable {files : VerifierAndGoals.PublicFiles} {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}

/-- **In scope a lookup's public record is the written one.** -/
theorem lookAtIsTheWrittenLookup (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2) :
    lookAt source number = Wf.lookupOf 1 ⟨kRef, 3076096⟩ (writtenStructure number) := by
  have lookups := sourceLookupsAreTheWrittenLookups sourced scope
  unfold lookAt oneOf
  rw [lookups]
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl <;> rfl

/-- **In scope a lookup's sums are those at the written numbers.** -/
theorem jobsAtAreTheWrittenSums (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2) :
    jobsAt source number =
      (fastJobs (faceK 1 ⟨kRef, 3076096⟩ (writtenStructure number))
        (rowK 1 ⟨kRef, 3076096⟩ (writtenStructure number))).asked := by
  unfold jobsAt faceAt
  rw [lookAtIsTheWrittenLookup sourced scope number below]
  rfl

/-- **In scope a lookup's record, at every input and all challenges, is the structure of the two readers.** -/
theorem witAtIsTheWrittenRecord {W₀ Rc : Type} (f : W₀ → Weights) (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2) (input : In1 W₀ Rc)
    (heard : List Fmt.Drawn) :
    witAt f source number input heard =
      hidK (writtenStructure number) (keyReaderAt f number input) (bitReaderAt f number input) := by
  obtain ⟨_, _, read, made, fromMade, -, -⟩ := sourced.source
  obtain ⟨-, ranges, shape, -, codes⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO read) made fromMade sourced.named.plan
  obtain ⟨items, rows, ell, -, matrix⟩ := AtPublicFiles.Key.item_written
  have hLog : OnBytes.ceilLog2 2 = 1 := by decide
  have hRecord : witAt f source number input heard =
      AtPublicFiles.KeyLookup.hiddenKey keyFull.ranges.x keyFull.codes number ⟨kRef, 3076096⟩
        ([lk0Full, lk1Full].getD number default) (matOf f input)
        (planesVal (matrixEntryOf f input) kRef [lk0Full, lk1Full] (2 ^ 18) 1) := by
    show AtPublicFiles.KeyLookup.hiddenKey source.Y.k.oneTime.ranges source.Y.k.oneTime.codes number
      (Wf.matrixOf source.Y.k.oneTime.lin) (source.Y.k.oneTime.ranges.lookups.getD number default)
      (matOf f input)
      (planesVal (matrixEntryOf f input) (Wf.matrixOf source.Y.k.oneTime.lin).kCol source.Y.k.oneTime.ranges.lookups
        ((source.Y.k.oneTime.codes.base.getD source.Y.k.oneTime.ranges.message.shape.code default).ell)
        (ceilLog2 source.Y.k.oneTime.ranges.message.shape.mainRows)) = _
    rw [ranges, shape, codes, matrix, items, ell, rows, hLog]
  rw [hRecord]
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl <;> rfl

end

/-! ## 3 The relation at a matrix in range -/

/-- The reader of a matrix (`matrixReader`, E2E/KeyArgumentsAt.lean), written out. -/
def matrixWeights : FullSizeMatrix → Weights := fun matrix => ⟨AtPublicFiles.Key.cellsReader matrix⟩

section
variable {Rc : Type} (input : In1 FullSizeMatrix Rc)

theorem matrixWordsReadAsTheEntries :
    (fun y c => toF (matOf matrixWeights input y c)) = matrixEntryOf matrixWeights input := by
  funext y c
  exact OnBytes.Slice.toF_ofF _

theorem matrixWordsSpellTheCells (y c : Nat) (hy : y < Inst.Model.Layout.hRef) (hc : c < 2 ^ kRef) :
    toF (matOf matrixWeights input y c) = (input.w₀ ⟨y, hy⟩ ⟨c, hc⟩).c0 := by
  have hEntry : matrixEntryOf matrixWeights input y c = (input.w₀ ⟨y, hy⟩ ⟨c, hc⟩).c0 := by
    show AtPublicFiles.Key.cellsReader input.w₀ y c = _
    unfold AtPublicFiles.Key.cellsReader
    rw [dif_pos ⟨hy, hc⟩]
  rw [← hEntry]
  exact OnBytes.Slice.toF_ofF _

/-- **AT A MATRIX IN RANGE THE TWO READERS MEET THE RELATION AFTER THE CHALLENGE**, at both lookups, at every shift and alpha. -/
theorem valuesMeetTheRelationAtTheNamedParts (inRange : VerifiableInference.OnPublicFiles.Flat.InRange input.w₀)
    (number : Nat) (below : number < 2) (theta alpha : E) :
    KeyMidHyp 1 ⟨kRef, 3076096⟩ (writtenStructure number) (keyReaderAt matrixWeights number input)
      (bitReaderAt matrixWeights number input) theta alpha := by
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · have h := keyMidHypAtTheFirstWrittenLookup input.w₀ inRange (matOf matrixWeights input)
      (matrixWordsSpellTheCells input) theta alpha
    rw [matrixWordsReadAsTheEntries input] at h
    exact h
  · have h := keyMidHypAtTheSecondWrittenLookup input.w₀ inRange (matOf matrixWeights input)
      (matrixWordsSpellTheCells input) theta alpha
    rw [matrixWordsReadAsTheEntries input] at h
    exact h

/-- **The bits read 0 at planes that are not real**, at every matrix: the field `idle`. -/
theorem valuesAreIdleAtTheNamedParts (number : Nat) (below : number < 2) (u : Nat)
    (inTable : u < 2 ^ (writtenStructure number).d) (j : Nat)
    (notReal : (faceK 1 ⟨kRef, 3076096⟩ (writtenStructure number)).planes ≤ j)
    (inBlock : j < 2 ^ (writtenStructure number).mu) :
    readE (bitReaderAt matrixWeights number input (j + 2 ^ (writtenStructure number).mu * u)) = 0 := by
  obtain ⟨items, rows, ell, -, -⟩ := AtPublicFiles.Key.item_written
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · have hPlanes : 40 ≤ j := by
      have h := planesAtTheWrittenLookups.1
      have notReal' : (faceK 1 ⟨kRef, 3076096⟩ lk0Full).planes ≤ j := notReal
      omega
    have hBelow : j < 64 := inBlock
    have hu : u < 2 ^ 8 := inTable
    have h := (AtPublicFiles.Key.bitVec_full (matrixEntryOf matrixWeights input) keyFull.ranges.x keyFull.codes items rows ell
      j hBelow).1 u hu
    rw [if_neg (by omega)] at h
    exact h
  · have hPlanes : 39 ≤ j := by
      have h := planesAtTheWrittenLookups.2.1
      have notReal' : (faceK 1 ⟨kRef, 3076096⟩ lk1Full).planes ≤ j := notReal
      omega
    have hBelow : j < 64 := inBlock
    have hu : u < 2 ^ 13 := inTable
    have h := (AtPublicFiles.Key.bitVec_full (matrixEntryOf matrixWeights input) keyFull.ranges.x keyFull.codes items rows ell
      j hBelow).2 u hu
    rw [if_neg (by omega)] at h
    exact h

end

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.theKeyRecordIsTheLibrarysRecord
#print axioms AtPublicFiles.Lookup.Key.onHalfIsJobsThrough
#print axioms AtPublicFiles.Lookup.Key.firstSeatIsItsOwnLookups
#print axioms AtPublicFiles.Lookup.Key.secondSeatIsItsOwnLookups
#print axioms AtPublicFiles.Lookup.Key.lookAtIsTheWrittenLookup
#print axioms AtPublicFiles.Lookup.Key.jobsAtAreTheWrittenSums
#print axioms AtPublicFiles.Lookup.Key.witAtIsTheWrittenRecord
#print axioms AtPublicFiles.Lookup.Key.valuesMeetTheRelationAtTheNamedParts
#print axioms AtPublicFiles.Lookup.Key.valuesAreIdleAtTheNamedParts
