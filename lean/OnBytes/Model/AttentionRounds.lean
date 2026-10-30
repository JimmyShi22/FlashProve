-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionRounds.lean: what the plan of a proof's first chain takes from an attention
sub-proof.

Each sub-proof of a request is one link of the proof's first chain. The plan of that chain lists
every round. The rounds of an attention link follow from a few numbers, which this file takes from
the sub-proof's plan (OnBytes/Model/AttentionPlan.lean) and passes on to the planner
(OnBytes/Params/SubRounds.lean).
 1. The sizes of the lookup of the sub-proof's calls (OnBytes/Model/RoundSizes.lean).
 2. The sizes of the sub-proof's own rounds, which the plan stores as Plan.own.
 3. The sizes of the smallness test: its matrix of combinations and the lookup on its digits
    (OnBytes/Model/RoundSizes.lean).
A link has three moments: the points at which the prover sends commitments. Moment 0 holds the
symbol arrays of the sub-proof's own matrices, moment 1 the vector of tables, and moment 2 the two
arrays of the smallness test.

The C++ source is vf_attention_check.h: the routine rounds that AttentionSubProof::plan sets up.

Main definition: rounds.

This file reads no proof and holds no theorem.
-/
import OnBytes.Model.RoundSizes
import OnBytes.Model.AttentionPlan

namespace OnBytes.Attention

/-! ## The rounds -/

/-- The rounds of the sub-proof that follow a moment of its link. After moment 0: the lookup of its
calls, then its own rounds. After moment 1: the matrix of the smallness test. After moment 2: the
lookup on the digits, then the element that batches all claims. The equations of the smallness test
have no challenge of their own: they are under further powers of that element, and its round counts
them with the claims (Plan.own.rows). A moment above 2 is refused (Params.planSmall). One test of
the sub-proof has no round of its own: see Params.planAttentionOwn. -/
def rounds (P : Plan) (moment : Nat) : Params.Planning Unit :=
  Params.attentionRounds (Model.forestSize P.fs) P.own (Model.smallSize P.seam.tl) moment

end OnBytes.Attention
