-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (Item flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)

/-- The test: the item pinI is open at the border in front of each of the fifty later places. -/
def pinIOpenB : Bool :=
  (List.range 25).all fun l => [true, false].all fun d =>
    (openAt linksFull (flatPlacesOf linksFull true) (noL l d)).contains Item.pinI

set_option maxRecDepth 1000000 in
theorem pinIOpenB_true : pinIOpenB = true := by decide +kernel

/-- **The item pinI is open at the border in front of each of the fifty later places.** -/
theorem pinI_open (l : ℕ) (hl : l < 25) (d : Bool) :
    Item.pinI ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) := by
  have h := pinIOpenB_true
  unfold pinIOpenB at h
  rw [List.all_eq_true] at h
  have h1 := h l (List.mem_range.2 hl)
  rw [List.all_eq_true] at h1
  have h2 := h1 d (by cases d <;> simp)
  exact List.contains_iff_mem.1 h2

set_option maxRecDepth 1000000 in
/-- A negative test: at the chain's first border the item is not open: the test can say no. -/
theorem pinI_shut_at_0 :
    (openAt linksFull (flatPlacesOf linksFull true) 0).contains Item.pinI = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pinIOpenB_true
#print axioms VerifiableInference.Desc.K1.pinI_open
#print axioms VerifiableInference.Desc.K1.pinI_shut_at_0
