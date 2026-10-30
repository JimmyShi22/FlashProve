-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CtxOpen.lean: K01_law: THE TWO ITEMS THAT THE TABLE's ROW AT A READS' PLACE HAS BESIDE WHAT IT CLOSES («pin l 0» · «constr l small») ARE OPEN IN FRONT OF THAT PLACE: by evaluation in Lean's kernel, after PinIOpen.lean. So the top's own arms at pins and at
constraints carry them back over the piece's accept.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (Item flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)

def ctxOpenB : Bool :=
  (List.range 25).all fun l =>
    (openAt linksFull (flatPlacesOf linksFull true) (noL l false)).contains (Item.pin l 0) &&
      (openAt linksFull (flatPlacesOf linksFull true) (noL l false)).contains (Item.constr l .small)

set_option maxRecDepth 1000000 in
theorem ctxOpenB_true : ctxOpenB = true := by decide +kernel

theorem pin0_open (l : ℕ) (hl : l < 25) : Item.pin l 0 ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l false) := by
  have h := List.all_eq_true.1 ctxOpenB_true l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h
  exact List.contains_iff_mem.1 h.1

theorem small_open (l : ℕ) (hl : l < 25) :
    Item.constr l .small ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l false) := by
  have h := List.all_eq_true.1 ctxOpenB_true l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h
  exact List.contains_iff_mem.1 h.2

set_option maxRecDepth 1000000 in
/-- A negative test: at the chain's first border «pin 0 0» is not open: the test can say no. -/
theorem pin0_shut_at_0 : (openAt linksFull (flatPlacesOf linksFull true) 0).contains (Item.pin 0 0) = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pin0_open
#print axioms VerifiableInference.Desc.K1.small_open
