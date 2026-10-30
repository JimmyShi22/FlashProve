-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyRangeOne.lean: the four texts of «the index is in range» at thePartsAt are one predicate, as
B-RANGE asks. The prover's test (matrixInput.inRange), the object's cut
(E2E/ObjectAtFiles.lean's inRange, the library's Flat.InRange), the lookups' own (PartsIn of both
lookups at the written sizes) and the model's weights (every ModelWeights has a matrix in range).

  inRange_iff            the prover's test is Flat.InRange, both ways
  inRange_iff_parts      it is the lookups' own, both ways, at the written sizes
  inRange_keysIn         it gives what the lookups' law asks: KeysIn at both lookups
  inRange_matrixOf       every index's matrix passes
  inRange_weights        every ModelWeights' matrix passes: no index of the statement's range falls
                         out of the prover's test

Limits. PartsIn is at the written sizes, as partsIn_iff_inRange is. KeysIn is one way: a matrix whose
live keys lie in their tables may fail InRange by what no key reads. T3's text is not read here: it
must name one of these. Nothing on any property.
-/
import E2E.TheHonestProver
import E2E.KeyPlanesAtFull
import Johnson.Flat.ThreeFull
import Johnson.Top.H.KeyMeaning
import IntegerModel.Arrays.OfIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.OnPublicFiles (Flat)
open Johnson.Pack (PartsIn cubeOf lk0Full lk1Full partsIn_iff_inRange)
open Inst.Model.Layout (kRef)
open AtPublicFiles.Key (KeysIn entryOf keysIn_full)

/-- **The prover's test is the object's cut, both ways.** -/
theorem inRange_iff (matrix : FullSizeMatrix) :
    matrixInput.inRange matrix = true ↔ VerifiableInference.OnPublicFiles.Flat.InRange matrix := by
  show ((VerifiableInference.OnPublicFiles.Flat.indexOf matrix).isSome = true) ↔ _
  unfold VerifiableInference.OnPublicFiles.Flat.indexOf
  by_cases h : VerifiableInference.OnPublicFiles.Flat.InRange matrix
  · simp [h]
  · simp [h]

/-- **It is the lookups' own, both ways, at the written sizes.** -/
theorem inRange_iff_parts (matrix : FullSizeMatrix) :
    matrixInput.inRange matrix = true ↔ PartsIn lk0Full lk1Full kRef (cubeOf matrix) :=
  (inRange_iff matrix).trans (partsIn_iff_inRange matrix).symm

/-- **It gives what the lookups' law asks.** -/
theorem inRange_keysIn {matrix : FullSizeMatrix} (h : matrixInput.inRange matrix = true) :
    KeysIn (entryOf matrix) kRef lk0Full ∧ KeysIn (entryOf matrix) kRef lk1Full :=
  keysIn_full matrix ((inRange_iff matrix).1 h)

/-- **Every index's matrix passes.** -/
theorem inRange_matrixOf (index : Cm.Idx) :
    matrixInput.inRange (VerifiableInference.OnPublicFiles.Flat.matrixOf index) = true :=
  (inRange_iff _).2 ⟨index, VerifiableInference.OnPublicFiles.Flat.holds_matrixOf index⟩

/-- **Every weights' matrix passes**: no member of the statement's type falls out of the test. -/
theorem inRange_weights {settings : IntegerTransformer.Settings}
    (valid : VerifiableInference.settingsAreValid settings = true)
    (weights : VerifiableInference.ModelWeights settings) :
    matrixInput.inRange (VerifiableInference.OnPublicFiles.Flat.matrixOf
      (VerifiableInference.indexOfWeights valid weights)) = true :=
  inRange_matrixOf _

end AtPublicFiles.AtFiles.HonestTerm
