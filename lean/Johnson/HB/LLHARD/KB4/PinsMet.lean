-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/PinsMet.lean: the twenty-three equations of Pins
(Johnson/HB/LLHARD/KB4/Pins.lean) do not contradict each other: a closed source meets them.

  pins_met: Pins XW rangesNumsFull laterPlacesFull, at XW := the written slim values
  (Johnson/HB/LLHARD/KB4/SourceW.lean).
WHAT IT IS NOT. XW IS NOT THE SOURCE OF THE RELEASE's PUBLIC FILES, AND IT DOES NOT MEET ALL THE
OTHER PREMISES OF key_planOk (Johnson/HB/LLHARD/KB4/Row.lean): its chains hold no bytes, so no
reader has returned them (hread fails at it: the clause "read" says no there: read_no), and it holds
no unit of rows. So this is no example of key_planOk's premises together. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Pins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (rangesNumsFull laterPlacesFull)

/-- The closed source. -/
def XW : Source := ⟨YW, chainsW, keyFull.set⟩

theorem pins_met : Pins XW rangesNumsFull laterPlacesFull :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- At the closed source the clause "read" says no. -/
theorem read_no : readAgainOk XW.Y.k = false := by decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.pins_met
#print axioms Johnson.KB4.read_no
