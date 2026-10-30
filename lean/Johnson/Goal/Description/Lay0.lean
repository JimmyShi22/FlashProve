-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Lay0.lean: the record of letters before the extractor is laid in.
`flashProveDataNoExtractor`: all of `flashProveData`'s parts, with an extractor that finds nothing. It exists so that
`theExtractor` (Extractor.lean) can be made of the told record over this record's family.
`hStar` is the function that returns no byte: the verdict does not read that letter
(`FlashProve.verify_is_steps`, Johnson/Goal/Tie/TieSteps.lean, holds at every such function), so no
hash function is named for it.
`flashProveDataNoExtractorAtHash o`: the same record at a function o in the second hash function's place.
`theLay₀At_older`: at the format's it is `flashProveDataNoExtractor`: two texts of one record, tied by `rfl`, so that
the laws go on speaking of the names without o.

-/
import Johnson.Goal.Description.Named
import Johnson.Goal.Description.Honest
import Johnson.Goal.Description.Form0
import Johnson.Goal.Description.Item

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve

def flashProveDataNoExtractorAtHash (o : VerifierAndGoals.SecondHashFunctionType) : FlashProve.DescriptionData where
  A := theClaims
  E := theCoding
  DK := theKeyDataAt o
  DP := theProofDataAt o
  runK := theKeyGateAt o
  runP := theProofGateAt o
  dec := theLinkGateAt o
  G := thePlanAt o
  it := theItemAt o
  P := theProversAt o
  N := theNamedAt o
  ext := fun _ _ _ _ => none
  honest := theHonest
  hStar := fun _ _ _ _ _ => ByteArray.empty
  d₀ := fun _ => false
  f₀ := theForm0
  hf₀ := theForm0_aux
  live := protocolDataWellFormedAt o
  hlive := theLiveAt_fit o
  Gd := theDeadPlanAt o

def flashProveDataNoExtractor : FlashProve.DescriptionData where
  A := theClaims
  E := theCoding
  DK := theKeyData
  DP := theProofData
  runK := theKeyGate
  runP := theProofGate
  dec := theLinkGate
  G := thePlan
  it := theItem
  P := theProvers
  N := theNamed
  ext := fun _ _ _ _ => none
  honest := theHonest
  hStar := fun _ _ _ _ _ => ByteArray.empty
  d₀ := fun _ => false
  f₀ := theForm0
  hf₀ := theForm0_aux
  live := protocolDataWellFormed
  hlive := theLive_fit
  Gd := theDeadPlan

theorem theLay₀At_older : flashProveDataNoExtractorAtHash OnBytes.secondHashFunction = flashProveDataNoExtractor := rfl

end FlashProve
