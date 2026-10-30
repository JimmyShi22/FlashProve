-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Lay.lean: the record of letters. `flashProveData`: `flashProveDataNoExtractor` with `theExtractor`
laid in. Every field is a named definition of a file beside this one; no letter is left.
True: the claims, the coding, the extractor, the fallback form, the test with the plan of the branch
that refuses, the three gates, the request's item. In part: the named side. What sits in the three
seats and in the plan's place is told in KeyFold.lean, ProofFold.lean, LinkDec.lean and Plan.lean.
Place-holders: the provers, the honest side. Two idle constants: verify reads neither.
`flashProveDataAtSecondHash o`: the same at a function o in the second hash function's place; `theLayAt_older`: at
the format's it is `flashProveData`, by `rfl`.
Limits. Three plans meet in this record: the frame's (Plan.lean: the record of `plannedAtO`), the
one of which the key file's description is made (`Key.madeAt`), and the one that `ProofFile.onlineDescription`
makes inside. The first two are one (`thePlan_key`, PlanKey.lean); no theorem ties the third.
`protocolDataWellFormed` holds the frame's plan against both files' data in numbers; in scope the proof file's
data are the written ones (`LPFD.Full.laidPOf_written`); for the key file's data there is no such
law. The two files' seats ask unlike things: the key's asks `wantedOk` and `owedOk`, the proof's
does not.

-/
import Johnson.Goal.Description.Extractor

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve

def flashProveDataAtSecondHash (o : VerifierAndGoals.SecondHashFunctionType) : FlashProve.DescriptionData := { flashProveDataNoExtractorAtHash o with ext := theExtractorAt o }

def flashProveData : FlashProve.DescriptionData := { flashProveDataNoExtractor with ext := theExtractor }

/- Lean compares these three names and does not open them: else the `rfl` runs into Lean's limit. -/
attribute [local irreducible] VerifierAndGoals.par7O OnBytes.K.Arm.Pub.par7 OnBytes.K.Arm.Pub.pub8 in
theorem theLayAt_older : flashProveDataAtSecondHash OnBytes.secondHashFunction = flashProveData := rfl

end FlashProve
