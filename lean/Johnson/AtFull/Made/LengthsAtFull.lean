-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/LengthsAtFull.lean: at the written full-size values, how many bytes the
spellings of the layout and of the request's shape have; and that each of the five items of a key's
one-time chain has fewer than 2 ^ 64 bytes.

`layoutSize_full`, `reqSize_full`: closed facts, by Lean's kernel (`decide +kernel`), on the sums of
Johnson/AtFull/Made/Lengths.lean: numbers and the lengths of names; no spelling is laid. The two
right sides are the lengths that an evaluation of the spellings themselves printed, so each fact
also tests its sum. `short_key_full`: from two bounds (`ranges_full`, `others_full`,
Johnson/Goal/Conditions/KeyBytesFitAtScope.lean).

Limits. That the written values are what the planner makes or is handed is not said here.
Nothing on soundness.
-/
import Johnson.AtFull.Made.Lengths
import Johnson.G.LayoutLit
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Goal.Conditions.KeyBytesFitAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.G (layoutFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open Lk6.AtPlan (keyFull ranges_full others_full)

set_option maxRecDepth 1000000 in
theorem layoutSize_full : layoutSize layoutFull = 399910 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem reqSize_full : reqSize proofSizedFull.request = 5424 := by decide +kernel

theorem short_key_full : Short (Plan.oneTimeItems keyFull) := by
  have a := ranges_full
  have b := others_full
  intro y hy
  simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · show (spellNotice keyFull.once.input).size < 2 ^ 64
    omega
  · show (spellRanges keyFull.ranges.x).size < 2 ^ 64
    omega
  · show (spellBinding keyFull.binding).size < 2 ^ 64
    omega
  · show (spellCodes keyFull.codes).size < 2 ^ 64
    omega
  · show (spellLin keyFull.once.shape).size < 2 ^ 64
    omega

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.layoutSize_full
#print axioms Johnson.AtFull.Made.reqSize_full
#print axioms Johnson.AtFull.Made.short_key_full
