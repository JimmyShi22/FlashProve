-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Own/OwnScalesTest.lean: "the table of scales off two files' bytes is the reference
table", as a test with code, and what a yes of the test gives.

`Cm.Scales` holds a function on the 48 layers, so an equation between two tables is not decided by
an instance. `scalesRefB pol KL` asks `Flat.scalesAtRef pol KL` (Johnson/Flat/ModelLines.lean) for
its table and compares it with `Cm.sRef` layer by layer, and in the final normalisation.

Main definition: `scalesRefB`.
Main theorem: `scalesAtRef_of_test`: scalesRefB pol KL = true → scalesAtRef pol KL = .ok Cm.sRef.
What is not claimed. That the test says yes at any files: nothing on a file is evaluated here (runs:
Johnson/Top/Own/OwnStoredFullRun.lean). Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.ModelLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.K.Arm.Own

/-- The test: `scalesAtRef` returns a table, and it has the reference table's words at all 48 layers
and its final normalisation. -/
def scalesRefB (pol KL : ByteArray) : Bool :=
  match OnBytes.Flat.scalesAtRef pol KL with
  | .ok s =>
    ((List.finRange 48).all fun L => decide (s.w L = Cm.sRef.w L)) && decide (s.nf = Cm.sRef.nf)
  | .error _ => false

/-- If the test says yes, `scalesAtRef` returns the reference table. -/
theorem scalesAtRef_of_test {pol KL : ByteArray} (t : scalesRefB pol KL = true) :
    OnBytes.Flat.scalesAtRef pol KL = .ok Cm.sRef := by
  unfold scalesRefB at t
  cases h : OnBytes.Flat.scalesAtRef pol KL with
  | error e =>
    rw [h] at t
    cases t
  | ok s =>
    rw [h] at t
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at t
    obtain ⟨w, nf⟩ := s
    have hw : w = Cm.sRef.w := funext fun L => t.1 L (List.mem_finRange L)
    have hn : nf = Cm.sRef.nf := t.2
    subst hw hn
    rfl

end OnBytes.K.Arm.Own
