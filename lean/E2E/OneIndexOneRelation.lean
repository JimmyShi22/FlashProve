-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OneIndexOneRelation.lean: SOUNDNESS AND COMPLETENESS SPEAK OF ONE INDEX AND OF NESTED RELATIONS. At a served request, on the honest committer's table with that
table's own out-of-domain sample: soundness's extractor returns THE HONEST INDEX; the table has no collision at the sample's point; and the
served request lies in the relation at which soundness concludes.

  `extractor_returns_the_index`   at every matrix in range, every randomness of the encoding and every seed:
                                  `(protocolAtFiles Z).extractIndex (encodeIndex i r) (recOf i r e) = some i`
  `honest_table_has_no_collision` so, by soundness's clause on collisions, the honest table has none at any seed
  `served_in_range`               the index of a served request is in range
  `one_index_one_relation`        **the three together, at a served request**

By what. The extractor is the index decoder (`HolographicProtocol.extractIndex`, Hiop/SoundAsIOP.lean); the decoder's clause at the matrices in range is the
library's (`wired_objAt`, E2E/ObjectAtFiles.lean; carried from the object cut to the range by `wired_cut_iff`, E2E/CutIndex.lean). The first
sentence spends neither soundness nor completeness. The second spends one clause of soundness in parts (nothingAtCollision), a premise here.

Why. Completeness starts from an index i, its table `encodeIndex i r` and sample `recOf i r e`; soundness ends at «the extractor answers an index, and the
relation holds of THAT index». This says that on honest data the two indices are one.

Limits. Nothing on a table that is not an honest encoding. Nothing on a matrix out of range: there the decoder cannot return the index. The
copy's table and the link are not spoken of. No property is proved here.
-/
import E2E.ThreeAtOneProtocol
import E2E.ObjectAtFiles
import Johnson.FrontRoad.RangeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OneProtocol
open Iop
open AtPublicFiles.AtFiles AtPublicFiles.Cut
open VerifiableInference.Compilation (rangeAtFiles)
open VerifierAndGoals (PublicFiles readFiles InScope)
open FlashProve (committerCoinCountLessOne)

variable {Z : PublicFiles}

/-- **Soundness's extractor returns the honest index**, on the honest table with its own sample, at every matrix in range. -/
theorem extractor_returns_the_index (i : FullSizeMatrix) (hi : rangeAtFiles i) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i :=
  ((wired_cut_iff (I := FullSizeMatrix) (X := LPFD.Full.XF) (protocolAtFiles Z) inRange).1
    (wired_objAt Z (filesAt Z).fixedMessageProvers (ext_cutObj_silent (filesAt Z)))).1 i hi r e

#print axioms AtPublicFiles.OneProtocol.extractor_returns_the_index

/-- **The honest table has no collision at any seed**, by soundness's clause on collisions. -/
theorem honest_table_has_no_collision {errors : (protocolAtFiles Z).RoundErrors}
    (sound : (protocolAtFiles Z).SoundInParts (relationAtFiles Z) errors) (i : FullSizeMatrix) (hi : rangeAtFiles i)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) : ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) e := by
  intro hc
  have h1 := sound.nothingAtCollision ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) hc
  have h2 : (protocolAtFiles Z).decodeIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i :=
    extractor_returns_the_index i hi r e
  rw [h1] at h2
  cases h2

#print axioms AtPublicFiles.OneProtocol.honest_table_has_no_collision

variable {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **The index of a served request is in range.** -/
theorem served_in_range {i : FullSizeMatrix} {x : LPFD.Full.XF} (h : ServedRequest committerCoinCountLessOne Z hr i x) :
    rangeAtFiles i := by
  obtain ⟨w, -, -, hi, -⟩ := h
  rw [hi]
  exact OnBytes.FrontRoad.inRange_backThe Z _ w

#print axioms AtPublicFiles.OneProtocol.served_in_range

/-- **ONE INDEX, NESTED RELATIONS**: at a served request, on the honest table with its own sample. -/
theorem one_index_one_relation {errors : (protocolAtFiles Z).RoundErrors}
    (sound : (protocolAtFiles Z).SoundInParts (relationAtFiles Z) errors) (scope : InScope Z = true) (i : FullSizeMatrix)
    (x : LPFD.Full.XF) (h : ServedRequest committerCoinCountLessOne Z hr i x) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) :
    (protocolAtFiles Z).extractIndex ((protocolAtFiles Z).encodeIndex i r) ((protocolAtFiles Z).recOf i r e) = some i ∧
      ¬ (protocolAtFiles Z).hasCollisionAt ((protocolAtFiles Z).encodeIndex i r) e ∧ relationAtFiles Z i x :=
  ⟨extractor_returns_the_index i (served_in_range h) r e,
    honest_table_has_no_collision sound i (served_in_range h) r e, served_is_true scope i x h⟩

end AtPublicFiles.OneProtocol

#print axioms AtPublicFiles.OneProtocol.one_index_one_relation
