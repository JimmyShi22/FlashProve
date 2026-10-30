-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrontsFullRows.lean: the code switch's law: THREE CLOSED FACTS MORE AT THE 25
WRITTEN ENTRIES OF THE FULL SIZE, BY LEAN's KERNEL: the written front's carried rows name the
written shape's two codes and count two mask rows. A law file; no running text imports it.

Why. The walk along the fold gives of the real front's carried rows: their two codes' numbers are
the public shape's, and they count two mask rows. The test on the front (frontB2) compares them
with the WRITTEN front's. So the written front's must be held against the written shape's: these
three.

  rowsPubB x₀ code maskCode, rowsPub_of_test   the three equations, as a test and as Props.
  rowsPub_full     at each of the 25 written entries, at the written shape's two numbers: yes.
  rowsPub_at       what that gives at entry i.
  neg_rows_*       negative tests, by the kernel: with one number bent the test says no at entry 0.
Limits. Closed facts on written values. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hands.FrontsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit)
open Johnson.G (fxAt)

/-- The written front's carried rows name these two codes and count two mask rows. -/
def rowsPubB (x₀ : _root_.Tw.K2.Front) (code maskCode : ℕ) : Bool :=
  x₀.f.rows.code == code && x₀.f.rows.maskCode == maskCode && x₀.f.rows.masks == 2

theorem rowsPub_of_test {x₀ : _root_.Tw.K2.Front} {code maskCode : ℕ}
    (h : rowsPubB x₀ code maskCode = true) :
    x₀.f.rows.code = code ∧ x₀.f.rows.maskCode = maskCode ∧ x₀.f.rows.masks = 2 := by
  simp only [rowsPubB, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

set_option maxRecDepth 1000000 in
/-- **At each of the 25 written entries.** -/
theorem rowsPub_full :
    (tableFullLit.all fun r => rowsPubB (fxAt r) shW.code shW.maskCode) = true := by
  decide +kernel

theorem rowsPub_at {i : ℕ} {r : SwRow} (hr : tableFullLit[i]? = some r) :
    (fxAt r).f.rows.code = shW.code ∧ (fxAt r).f.rows.maskCode = shW.maskCode ∧
      (fxAt r).f.rows.masks = 2 :=
  rowsPub_of_test ((List.all_eq_true.1 rowsPub_full) r (List.mem_of_getElem? hr))

set_option maxRecDepth 1000000 in
theorem neg_rows_code : rowsPubB x0W (shW.code + 1) shW.maskCode = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_rows_maskCode : rowsPubB x0W shW.code (shW.maskCode + 1) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem neg_rows_masks : rowsPubB
    { x0W with f := { x0W.f with rows := { x0W.f.rows with masks := 1 } } } shW.code shW.maskCode =
      false := by decide +kernel

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.rowsPub_full
#print axioms VerifiableInference.Desc.First.K2Hands.rowsPub_at
