-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestVerifySubproofs.lean: tests of layerNumbers and withReply of
OnBytes/Model/VerifySubproofs.lean, run when this file compiles. rangeChecksOf is tested in
OnBytes/Model/TestVerifyHiding.lean, and closingParts only through it. linkRounds, subproofsWith and
shapesWith have no test, and no test makes shapesWith refuse.

The program does not import this file.

For a small configuration, spelled out in OnBytes/Model/TestLayer.lean and
OnBytes/Model/TestAttentionPlan.lean, the numbers that the plans of the layer and attention
sub-proofs hand to the planner are compared with the numbers written out in
OnBytes/Params/TestDerive.lean. That file makes the plan of the proof's first chain from those
numbers; it compares neither that plan's bytes nor its rounds and verdict with a print of the C++
verifier. The sizes of the lookups and of the smallness tests and the numbers of batched rows are
repeated here by hand from subWithRounds in that file. The last tests compare the places where this
library writes the width of a weight. In the C++ a static_assert in buildLinksH
(verifier/src/vf_segments.inc) does that.
-/
import OnBytes.Model.VerifySubproofs
import OnBytes.Model.TestLayer
import OnBytes.Model.TestAttentionPlan
import OnBytes.Params.TestDerive

namespace OnBytes.Model.TestVerifySubproofs

open Verify

/-- For the layer sub-proof of group g: the sizes of its lookup, its own numbers, the sizes of its
smallness test, and what its last round batches. -/
def layerOf (g : Nat) :
    Option (Params.ForestSize × Params.LayerRounds × Params.SmallSize × Nat) :=
  Layer.Test.plans.toOption.bind fun (P, hps) =>
    hps[g]?.map fun hp => (forestSize P.y.fo, layerNumbers P hp g, smallSize hp.tl, hp.nBatched)

#guard layerOf 0 ==
  some (⟨24, 19, true⟩, Params.TestDerive.layers true, ⟨3099, 128, ⟨24, 11, true⟩⟩, 4347789)
#guard layerOf 1 ==
  some (⟨24, 19, true⟩, Params.TestDerive.layers false, ⟨3099, 128, ⟨24, 11, true⟩⟩, 4343660)

#guard (Attention.smallPlan.toOption.map fun a => (forestSize a.fs, a.own, smallSize a.seam.tl)) ==
  some (⟨22, 18, true⟩, Params.TestDerive.attention, ⟨1276, 128, ⟨23, 11, true⟩⟩)

-- the reply's token goes out before the last link's first message
#guard (withReply [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]).map (·.plain) == [0, 0, 1]
#guard (withReply []).isEmpty

-- How wide a weight is: what a key's range proof covers (OnBytes/Plan/Units.lean), what the
-- no-overflow conditions of the layers and of the head assume, and the weight of a number's second
-- digit in the rows on the committed matrix. It must not cover less than a request assumes.
#guard Layer.WB == Plan.weightBits
#guard Layer.BW == 2 ^ (Plan.weightBits - 1)
#guard Head.weightBound == 2 ^ (Plan.weightBits - 1)
#guard wsSecondDigit.toNat == 2 ^ Plan.byteBits
#guard Plan.byteBits == 8

end OnBytes.Model.TestVerifySubproofs
