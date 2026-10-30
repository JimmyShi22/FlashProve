-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLookupCounts.lean: A TEST OF EMPTINESS for the sentences on the rows of the key file's two
lookups (E2E/OfflineLookupRowsGood.lean): in scope the two faces have 935 and 920 stages, of which 976
have a masked sumcheck and 879 send nothing. So the two rows have that many parts.

  `writtenLookupFace`      the face of lookup number i at the written sizes
  `faceAt_written`         in scope the description's face is that face
  `written_counts`         the four numbers at the written sizes, by evaluation in the kernel
  `lookup_parts_counted`   the four numbers at the description's faces, in scope

Numbers of stages alone. Nothing on any property.
-/
import E2E.KeyFirstSends
import E2E.KeyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc.Key (Source LaterPlaces)
open AtPublicFiles.KeyValues (faceAt lookAt oneOf)
open AtPublicFiles.AtFiles (KeySourced five_sourced)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)

/-- The face of lookup number i at the written sizes. -/
def writtenLookupFace (i : Nat) : K3.LFace :=
  VerifiableInference.Desc.K3.faceOfLkp
    ((OnBytes.Wf.lookupsOf keyFull.ranges.x (OnBytes.Wf.matrixOf keyFull.once.shape)).getD i default)

/-- How many stages of a face have a masked sumcheck. -/
def sumStages (f : K3.LFace) : Nat := ((K3.stages f).filter fun s => (s.call f).isSome).length

/-- **In scope the description's face is the written one.** -/
theorem faceAt_written {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (i : Nat) :
    faceAt Xs i = writtenLookupFace i := by
  obtain ⟨-, er, el, -, -⟩ := five_sourced hs scope
  unfold faceAt lookAt writtenLookupFace VerifiableInference.Desc.Key.lookupsOf
  show VerifiableInference.Desc.K3.faceOfLkp ((OnBytes.Wf.lookupsOf Xs.Y.k.oneTime.ranges
    (OnBytes.Wf.matrixOf Xs.Y.k.oneTime.lin)).getD i default) = _
  rw [er, el]

/-- **The numbers at the written sizes.** By evaluation. -/
theorem written_counts :
    ((K3.stages (writtenLookupFace 0)).length == 935 && (K3.stages (writtenLookupFace 1)).length == 920 &&
      sumStages (writtenLookupFace 0) + sumStages (writtenLookupFace 1) == 976) = true := by
  decide +kernel

/-- **The numbers at the description's faces, in scope**: 935 and 920 stages; 976 of the 1,855 have a
masked sumcheck, so 879 send nothing. -/
theorem lookup_parts_counted {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (K3.stages (faceAt Xs 0)).length = 935 ∧ (K3.stages (faceAt Xs 1)).length = 920 ∧
      sumStages (faceAt Xs 0) + sumStages (faceAt Xs 1) = 976 := by
  rw [faceAt_written hs scope 0, faceAt_written hs scope 1]
  have h := written_counts
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.faceAt_written
#print axioms AtPublicFiles.OfflineRows.written_counts
#print axioms AtPublicFiles.OfflineRows.lookup_parts_counted
