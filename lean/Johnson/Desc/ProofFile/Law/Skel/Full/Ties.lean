-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/Full/Ties.lean: this folder's file of data (Full/Data.lean) against
the values that other modules write out: five closed facts, so that what these modules prove of
their own written values meets `back_at_full`'s premises on the places, the shape, the sorts and the
batchings' places, and its conclusion gives the written cut. Statements and proofs.
  `spots_tie`     `spotsW` is `Johnson.AtFull.Desc.spotsWritten`
                  (Johnson/AtFull/Desc/SpotsWritten.lean)
  `shape_tie`     `shapeW` is `Johnson.AtFull.Desc.shapeW` (Johnson/AtFull/Desc/ShapeIsCut.lean):
                  the names and places of the written cut's rows
  `subs_tie`      `subsW` is `Johnson.AtFull.Desc.subsW` (Johnson/AtFull/Desc/ShapeAtWritten.lean)
  `batchAt_tie`   `batchAtW` is `ProofFile.baseOf`'s own term for the batchings' places, at `subsW`
  `cut_tie`       the six fields `Skel.row` of `flatW`'s skeletons are the written cut's rows
                  (`cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean), by the comparison
                  `sameRows` (Johnson/Desc/Ok/PlanWritten/CutTest.lean)
Limits. All these texts come off prints of the same code: none is an independent witness of another.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Full.Data
import Johnson.Desc.ProofFile.Law.Skel.SkelCut
import Johnson.AtFull.Desc.ShapeIsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk.Full
open ProofFile ProofFile.Sk
open VerifiableInference.Desc.First (kindsBeforeBatching)

theorem spots_tie : spotsW = Johnson.AtFull.Desc.spotsWritten := rfl

theorem shape_tie : shapeW = Johnson.AtFull.Desc.shapeW := by decide +kernel

theorem subs_tie : subsW = Johnson.AtFull.Desc.subsW := by decide +kernel

theorem batchAt_tie :
    batchAtW = subsW.zipIdx.map fun x =>
      (x.2, ⟨1, some x.2, (kindsBeforeBatching x.1 (x.2 == 0)).length + 1,
        VerifiableInference.Desc.KindName.K9⟩) := by
  decide +kernel

theorem cut_tie :
    VerifiableInference.PlanWritten.sameRows (flatW.map Skel.row)
      VerifiableInference.PlanWritten.cutFirstFull = true := by
  decide +kernel

end ProofFile.Sk.Full

#print axioms ProofFile.Sk.Full.spots_tie
#print axioms ProofFile.Sk.Full.shape_tie
#print axioms ProofFile.Sk.Full.subs_tie
#print axioms ProofFile.Sk.Full.batchAt_tie
#print axioms ProofFile.Sk.Full.cut_tie
