-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RootsFastProofs.lean: the proof of the statement of Run/RootsFast.lean: the test "the roots that
the file sends are pairwise different" by the fast lenient reader equals the test of Run/PageIs.lean
at `Fmt.formatHash`.

Limits: what is not claimed is told in the head of Run/RootsFast.lean, under 4.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.RootsFast

set_option autoImplicit false

namespace Run.PQ

theorem rootsF_eq : Spec.rootsF_eq := fun S file => by
  unfold rootsDifferF rootsDiffer
  rw [laxFast_lax S file]
  rfl

end Run.PQ
