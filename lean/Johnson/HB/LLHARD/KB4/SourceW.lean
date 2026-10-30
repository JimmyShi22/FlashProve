-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/SourceW.lean: the slim values of a key file's source (Slim.lean) at the full
size's written values, as closed terms. Definitions alone.

Main names: kW (the three chains' values: the three written priced plans' plans, keyThree; the items
as keyFull has them), YW (with the written declared rounds, KB8/Written.lean, and the tenants as
told, Told.lean), chainsW.
Limits. THESE ARE NOT WHAT Key.sourceOf RETURNS AT ANY PUBLIC FILES: they hold no bytes, no digest,
no item and no unit of rows. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Slim
import Johnson.HB.LLHARD.KB4.Told
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull)

/-- The three chains' values. -/
def kW : KeyChains :=
  ⟨⟨givenAt keyThree.A.plan.plan, keyFull.once.input, keyFull.ranges.x, keyFull.binding,
      keyFull.codes, keyFull.once.shape⟩,
    ⟨givenAt keyThree.B.plan.plan, keyFull.codes, keyFull.once.shape⟩,
    ⟨givenAt keyThree.C.plan.plan⟩⟩

/-- The record of a key file's source (`KeySource`) at the written values: a closed term. -/
def YW : KeySource :=
  ⟨kW, keyFull.once.shape, (keyFull.codes, keyFull.codes, keyFull.codes), keyFull.once.input,
    keyFull.ranges.x, recordSet.samples, declKeyFull, toldKeyFull, []⟩

/-- The planner's record of the seven chains, by `chainsAt` at the written values: a closed term. -/
def chainsW : Model.Verify.Chains :=
  chainsAt keyFull [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] kW

end Johnson.KB4
