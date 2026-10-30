-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K13StartFacts.lean: closed facts on the names of the proof file's first chain's 48,293
written rounds, around the round at which the members' batching starts (48270), in forms that Lean's
kernel walks: loops (List.all, take, drop), no length and no map of the whole list.
  base_at: the names of the rounds 48268, 48269, 48270: "BASE lambda", "BASE", "BAT-sigma"
  base_not_before, base_not_after: no other round of the list bears the name "BASE lambda"
  tail_names: the list's rounds from 48290 on: "SEND seed", "SEND answer", "SEAL": so it has 48,293
  batt_names: the twenty rounds from 48270 on: "BAT-sigma", "PSC epsilon", eighteen "PSC round"

They serve a law on the table of steps (cutOf, Johnson/Desc/First/Driver/Cut.lean): front_of_base
(Johnson/Desc/First/Driver/CutFront.lean). With it and base_not_before | base_not_after,
startOf_written (Johnson/Desc/K14/Law/StartWritten.lean) shows: if cutOf returns a table at the
written entries, the batching starts at round 48270 there. That cutOf returns one is not shown.

What is not claimed. Anything on cutOf. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.WrittenAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G

theorem base_at : ((dryProofFull.1.drop 48268).take 3).map (·.1.entry.name) =
    ["BASE lambda", "BASE", "BAT-sigma"] := by decide +kernel

theorem base_not_before :
    ((dryProofFull.1.take 48268).all fun d => d.1.entry.name != "BASE lambda") = true := by
  decide +kernel

theorem base_not_after :
    ((dryProofFull.1.drop 48269).all fun d => d.1.entry.name != "BASE lambda") = true := by
  decide +kernel

theorem tail_names : (dryProofFull.1.drop 48290).map (·.1.entry.name) =
    ["SEND seed", "SEND answer", "SEAL"] := by decide +kernel

theorem batt_names : ((dryProofFull.1.drop 48270).take 20).map (·.1.entry.name) =
    "BAT-sigma" :: "PSC epsilon" :: List.replicate 18 "PSC round" := by decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.base_at
#print axioms Desc.K14.Law.base_not_before
#print axioms Desc.K14.Law.base_not_after
#print axioms Desc.K14.Law.tail_names
#print axioms Desc.K14.Law.batt_names
