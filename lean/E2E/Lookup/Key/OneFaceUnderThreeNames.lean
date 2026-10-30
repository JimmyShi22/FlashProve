-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
ONE FACE UNDER THREE NAMES. A lookup's public numbers stand under three names in the key file's files: the book's
`data.faces[number]` (E2E/KeyBook.lean), the table's `faceOfLkp Sg` with `lkpOf … l = some Sg`
(Johnson/Desc/Key/KeyK3Items.lean), and the values' `faceK 1 ⟨kRef, 3076096⟩ lk0Full` and `… lk1Full`
(Honest/K3/Parts/KeyFace.lean). Theorems with proofs: they tie the three, so that what is shown under one name can be laid
on one course with what is shown under another.

  `keyBookFacesAreTheLookupsFaces`       where `KeyPub.of` returns, its faces are the faces of the sizes' lookups
  `keyBookFacesAreTheWrittenFaces`       at the written sizes they are the two values `faceK …`
  `sourceLookupsAreTheWrittenLookups`    in scope the lookups of the source's one-time chain are the two written ones
  `tableRecordIsTheWrittenLookup`        so `lkpOf` at `plan₁` returns them at 0 and 1
  `oneFaceUnderThreeNames`               **the join**: at l = 0, 1 one record stands behind all three names

The source's one-time chain is `source.Y.k.oneTime`: `one₀ source` (E2E/KeyRest.lean) and `oneOf source`
(E2E/KeyFirstSends.lean) are abbreviations of it.

Limits. Public data alone. The full size alone. `KeySourced` is a premise: `key_sourced` (E2E/KeyPublic.lean) has it where
the verifier's own test on the public files accepts.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.KeyMidAtWritten
import E2E.KeyBookSourced
import E2E.KeyPublic
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyFace
import Johnson.RunOne.KeyRows1At

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open OnBytes
open AtPublicFiles.KeyBook
open AtPublicFiles.AtFiles (KeySourced)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Source LaterPlaces lookupsOf lkpOf)
open Johnson.RunOne.KeyRows1 (plan₁)
open ProofFile.Honest.K3.Parts.Key (faceK)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)

/-- **Where `KeyPub.of` returns, the book's faces are the faces of the sizes' lookups.** -/
theorem keyBookFacesAreTheLookupsFaces {sizes : Plan.KeySized} {answers : Nat} {data : KeyPub}
    (made : KeyPub.of sizes answers = some data) :
    data.faces = (Wf.lookupsOf sizes.ranges.x (Wf.matrixOf sizes.once.shape)).map faceOfLkp := by
  unfold KeyPub.of at made
  iterate 14 obtain ⟨_, -, made⟩ := Option.bind_eq_some_iff.1 made
  obtain rfl := Option.some.inj made
  rfl

/-- **At the written sizes the book's faces are the two values.** -/
theorem keyBookFacesAreTheWrittenFaces {data : KeyPub} (written : fullPub = some data) :
    data.faces = [faceK 1 ⟨kRef, 3076096⟩ lk0Full, faceK 1 ⟨kRef, 3076096⟩ lk1Full] := by
  have faces : data.faces = _ := keyBookFacesAreTheLookupsFaces (sizes := keyFull) written
  rw [faces, AtPublicFiles.Key.faces_written]
  rfl

section
variable {files : PublicFiles} {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}

/-- **In scope the lookups of the source's one-time chain are the two written ones.** -/
theorem sourceLookupsAreTheWrittenLookups (sourced : KeySourced files source numbers later)
    (scope : InScope files = true) :
    lookupsOf source.Y.k.oneTime =
      [Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk0Full, Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk1Full] := by
  obtain ⟨_, _, read, made, fromMade, -, -⟩ := sourced.source
  obtain ⟨-, ranges, shape, -, -⟩ := Johnson.RunOne.Law.KeyInScope.five_in_scope scope
    (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO read) made fromMade sourced.named.plan
  unfold lookupsOf
  rw [ranges, shape]
  exact AtPublicFiles.Key.faces_written

/-- **So the table's record at each of the two lookups is the written one.** -/
theorem tableRecordIsTheWrittenLookup (sourced : KeySourced files source numbers later)
    (scope : InScope files = true) :
    lkpOf (plan₁ source.Y.k.oneTime) source.Y.k.oneTime.ranges 0 =
        some (Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk0Full) ∧
      lkpOf (plan₁ source.Y.k.oneTime) source.Y.k.oneTime.ranges 1 =
        some (Wf.lookupOf 1 ⟨kRef, 3076096⟩ lk1Full) := by
  have lookups := sourceLookupsAreTheWrittenLookups sourced scope
  constructor
  · show (lookupsOf source.Y.k.oneTime)[0]? = _
    rw [lookups]
    rfl
  · show (lookupsOf source.Y.k.oneTime)[1]? = _
    rw [lookups]
    rfl

/-- **THE JOIN: ONE RECORD BEHIND THE THREE NAMES**, at each of the two lookups: the table's record, the book's face is
its face, and that face is the value. -/
theorem oneFaceUnderThreeNames (sourced : KeySourced files source numbers later) (scope : InScope files = true)
    {data : KeyPub} (written : fullPub = some data) :
    ∀ number, number < 2 → ∃ record,
      lkpOf (plan₁ source.Y.k.oneTime) source.Y.k.oneTime.ranges number = some record ∧
      data.faces[number]? = some (faceOfLkp record) ∧
      faceOfLkp record = faceK 1 ⟨kRef, 3076096⟩ (if number = 0 then lk0Full else lk1Full) := by
  intro number below
  obtain ⟨first, second⟩ := tableRecordIsTheWrittenLookup sourced scope
  have faces := keyBookFacesAreTheWrittenFaces written
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · exact ⟨_, first, by rw [faces]; rfl, rfl⟩
  · exact ⟨_, second, by rw [faces]; rfl, rfl⟩

end

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.keyBookFacesAreTheLookupsFaces
#print axioms AtPublicFiles.Lookup.Key.keyBookFacesAreTheWrittenFaces
#print axioms AtPublicFiles.Lookup.Key.sourceLookupsAreTheWrittenLookups
#print axioms AtPublicFiles.Lookup.Key.tableRecordIsTheWrittenLookup
#print axioms AtPublicFiles.Lookup.Key.oneFaceUnderThreeNames
