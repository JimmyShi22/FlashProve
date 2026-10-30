-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReadsAtWritten.lean: where the planner returns and its sizes, shapes and plans
are the written full-size values, the readers of a key's and of a proof's three chains return on the
planner's parameter bytes, at written-out values. No premise on a plan is left.

THE PREMISES ARE NOT SHOWN TOGETHER. Each law takes the planner's return, and equations that say
that parts of what it returns, or of what it was handed, are the written values. To show these is
other files' business.

These are the two laws of Johnson/AtFull/Made/ReadsAtFull.lean at the written plans `keyThree` and
`proofThree` (Johnson/Desc/Ok/NumberPrices/), with the closed facts of
Johnson/AtFull/Made/PlansAtFull.lean in the place of the tests on the plans.

`key_read_written`: what stays of the premises: the planner's return; the digest's 32 bytes; two
equations. `proof_read_written`: the planner's return; the digest's 32 bytes; five equations; and
that each of the links' identifiers is below 2 ^ 64.

Limits. As in Johnson/AtFull/Made/ReadsAtFull.lean. Nothing on soundness.
-/
import Johnson.AtFull.Made.ReadsAtFull
import Johnson.AtFull.Made.PlansAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G (layoutFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (keyThree proofThree)
open Lk6.AtPlan (keyFull)

/-- **A key's three chains at the written sizes and plans.** -/
theorem key_read_written {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made)
    (hk : made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan]) (h32 : cfg.size = 32)
    (hz : made.sized.key = keyFull) :
    KeyChains.read made.keyOneTime made.keyShared made.keySecond =
      some (keyOf cfg keyFull keyThree.A.plan.plan keyThree.B.plan.plan keyThree.C.plan.plan) :=
  key_read_full hc hk h32 hz planB_key0 planB_key1 planB_key2 sameWords_key.1 sameWords_key.2
    noSample_key1 noSample_key2

/-- **A proof's three chains at the written sizes, layout, numbers and plans.** -/
theorem proof_read_written {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (hc : configure l x cfg bits = .ok made)
    (hp : made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan])
    (h32 : cfg.size = 32) (hz : made.sized.proof = proofSizedFull)
    (hb : (⟨clog2 l.slots, made.sized.set.saltBytes⟩ : LinBindingShape) = ⟨6, 40⟩)
    (hy : x.layout = layoutFull) (hn : x.sub.pendingRows = 13)
    (hI : wordsB x.identifiers = true) :
    ProofChains.read made.first made.shared made.second =
      some (proofOf cfg l x made.sized proofThree.A.plan.plan proofThree.B.plan.plan
        proofThree.C.plan.plan) :=
  proof_read_full hc hp h32 hz hb hy hn hI planB_proof0 planB_proof1 planB_proof2
    sameWords_proof.1 sameWords_proof.2 noSample_proof0 noSample_proof1 noSample_proof2

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.key_read_written
#print axioms Johnson.AtFull.Made.proof_read_written
