-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Written/Made.lean: the written parts of what the planner configures at the full size,
joined into one closed term. Definitions alone.

The file stands under Johnson/Goal/ because the key file's typed sizes (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) stand above Ladder.lean.

The parts, and whence each is.
  The lines, the setting, the entry file's sizes and codes: the library's typed values
    (`recordLines`, `recordSet`, `recordLink`, `recordTable`, `recordG1`, `recordStages`,
    `recordCodes`, OnBytes/Params/EntryStagesRecord.lean).
  The key file's sizes: `keyFull`. The proof file's sizes: `proofSizedFull`
    (Johnson/Desc/Ok/PlanWritten/SizedLit.lean).
  The key file's three priced plans: `keyThree` (Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean).
    The entry file's: `pricedEntryFull` (Johnson/G/PricedEntryLit.lean). The proof file's three:
    `proofThree` (Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean), which stands on prints of the
    library's own planner: see its head.

Definitions.
  `writtenMade`: the four fields that do not hang on the digest (`Free`, Johnson/G/MadeFree.lean):
    `joinMade` (Johnson/Desc/Ok/NumberPrices/MadeAtWritten.lean) at the written parts.
    `writtenSized`: its sizes.

What of OnBytes/Model/ is used: nothing by name.

Limits. No theorem is here. The closed facts at the term are in
Johnson/Goal/Written/MadeFacts.lean;
what of the plans follows from the sizes is in Johnson/Goal/Written/MadeOfSized.lean. That the term
is what the planner configures at any public files is said nowhere. Nothing on soundness.

-/
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.Ok.NumberPrices.MadeAtWritten
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference.Number.ByRuns VerifiableInference.PlanWritten
open OnBytes.Params Johnson.G.MadeFree Lk6.AtPlan

/-- **The written parts, joined.** -/
def writtenMade : Free := joinMade proofSizedFull keyFull proofThree

/-- The sizes. -/
def writtenSized : Sized := writtenMade.sized

end VerifiableInference.PlanWritten.Joined
