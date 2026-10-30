-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/SizedLit.lean: the four inequalities that the library asks of a stage's
sizes (`Sg.Sized`, OnBytes/Slice/Numbers.lean) at the stage of a place's record, as a test; and the
test at the written records of LitRows.lean: it says yes at each of the 5 and the 25.

The test of Row.lean (`SwRow.ok`) does not ask them. They are what the laws of the folded complex's
code hang on.
  SwRow.sizedB: the code's length has at most 32 bits; the mask rows are no longer than the main
      rows; at both codes a row has no more coefficients than positions
  sized_of: a yes gives `Sg.Sized` at `stageOf r.g t₀`, for every t₀
  small_sized, full_sized: the test says yes at each written record: evaluations in Lean's kernel,
      one at each different record
  sized_can_fail: at each different record it says no if the main code's tail is longer by the
      code's length
Limits: written numbers. Those of LitRows.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params Johnson.Top.H

/-- The four inequalities at the record's stage, as a test. -/
def SwRow.sizedB (r : SwRow) : Bool :=
  decide ((stageOf r.g 0).C.a ≤ 32) && decide ((stageOf r.g 0).Z.a ≤ (stageOf r.g 0).C.a) &&
    decide ((stageOf r.g 0).C.r + (stageOf r.g 0).C.l ≤ 2 ^ (stageOf r.g 0).C.a) &&
    decide ((stageOf r.g 0).Z.r + (stageOf r.g 0).Z.l ≤ 2 ^ (stageOf r.g 0).Z.a)

theorem sized_of {r : SwRow} (h : r.sizedB = true) (t₀ : ℕ) : (stageOf r.g t₀).Sized := by
  unfold SwRow.sizedB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem small_sized : (tableSmallLit.all fun r => r.sizedB) = true :=
  small_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

theorem full_sized : (tableFullLit.all fun r => r.sizedB) = true :=
  full_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- A record whose main code's tail is longer by the code's length. -/
def longTail (r : SwRow) : SwRow :=
  { r with g := { r.g with main := { r.g.main with r := r.g.main.r + 2 ^ r.g.main.logN } } }

/-- The test can fail. -/
theorem sized_can_fail :
    (tableSmallLit.all fun r => !(longTail r).sizedB) = true ∧
      (tableFullLit.all fun r => !(longTail r).sizedB) = true :=
  ⟨small_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel),
    full_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.sized_of
#print axioms VerifiableInference.Desc.First.K2Caller.small_sized
#print axioms VerifiableInference.Desc.First.K2Caller.full_sized
#print axioms VerifiableInference.Desc.First.K2Caller.sized_can_fail
