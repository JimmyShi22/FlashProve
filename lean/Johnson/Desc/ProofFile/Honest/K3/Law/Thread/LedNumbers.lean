-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LedNumbers.lean: two numbers of a ledger can be read off
its shape: its count of slots taken and its number of owed claims. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a ledger F is `ledSh F`
(Johnson/Desc/First/Shape/Parts.lean). The ledger's count of slots taken is its field next; its owed
claims are its field owed. The shape of what was heard is `lookHeardSh`
(Honest/K3/Shape/HeardOps.lean), a function of a lookup's shape and two numbers.

What is shown. Three equations, at every ledger.
  `led_next`: the shape's count is the ledger's.
  `led_owed`: the shape's list of owed claims is as long as the ledger's.
  `heardSh_led`: hence `lookHeardSh` at the ledger's two numbers is `lookHeardSh` at its shape's two
    numbers.

Imported, through Honest/K3/Shape/HeardOps.lean: the library's Johnson/Desc/First/Shape/Parts.lean.

Users. CallsParts.lean, DigitsParts.lean and HeadParts.lean in this folder state equations whose
right-hand side contains `lookHeardSh` at these two numbers of the ledger; with the equations here
that right-hand side is code on the ledger's shape. `heardSh_led` is called in CarriesCalls.lean,
CarriesDigits.lean and CarriesHeadDigits.lean in this folder.

Limits. Three small equations.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.HeardOps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First.Shape (ledSh)
open ProofFile.Honest.K3.Shape (lookHeardSh)

theorem led_next (F : Fork) : (ledSh F).next = F.next := rfl

theorem led_owed (F : Fork) : (ledSh F).owed.length = F.owed.size := by
  show (F.owed.toList.map (·.added)).length = F.owed.size
  rw [List.length_map, Array.length_toList]

/-- **The shape of what was heard, as code on the ledger's shape.** `lookHeardSh` at the ledger's
count and number of owed claims is `lookHeardSh` at the same two numbers of the ledger's shape. -/
theorem heardSh_led (h : OnBytes.Model.Forest.Shape) (F : Fork) :
    lookHeardSh h F.next F.owed.size = lookHeardSh h (ledSh F).next (ledSh F).owed.length := by
  rw [led_next, led_owed]

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.led_next
#print axioms ProofFile.Honest.K3.Law.AtThr.led_owed
#print axioms ProofFile.Honest.K3.Law.AtThr.heardSh_led
