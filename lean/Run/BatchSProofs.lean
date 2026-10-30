-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/BatchSProofs.lean: the proofs of the six statements of Run/BatchS.lean, two of them on the
scheme's whole verifier and two on its verifiers of Test and Link, at an interface whose Test and
Link have no round. Of the strict format's six conditions (`proofHasStrictFormat`) only the one on the salt's
length needs a rewriting step; the other five hold of the constant string by evaluation; there is no
forest; the decision is "yes".

Limits: what the six statements do not say is told in the head of Run/BatchS.lean, under Limits.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.BatchS

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch Run.Twin

theorem batch_types : Spec.batch_types := fun _ _ _ => ⟨rfl, rfl⟩

theorem batch_test : Spec.batch_test := by
  intro B K wB sMT sFS cm
  have hs : decide ((List.replicate sFS false).length = sFS) = true := by
    rw [List.length_replicate]; exact decide_eq_true rfl
  show (if (decide ((List.replicate sFS false).length = sFS) && _ && _ && _ && _ && _) = true then _
      else _) = _
  rw [hs]
  rfl

theorem batch_link : Spec.batch_link := by
  intro B K wB sMT sFS cm cm'
  have hs : decide ((List.replicate sFS false).length = sFS) = true := by
    rw [List.length_replicate]; exact decide_eq_true rfl
  show (if (decide ((List.replicate sFS false).length = sFS) && _ && _ && _ && _ && _) = true then _
      else _) = _
  rw [hs]
  rfl

theorem batch_V : Spec.batch_V := by
  intro B K wB p cm cm' π
  show (if 0 ≤ p.M then
      (vTS (Wb K wB) p.sMT p.sFS cm (piT0 p.sFS)).bind fun a =>
        (vLS (Wb K wB) p.sMT p.sFS cm cm' (piL0 p.sFS)).bind fun b =>
          (vBS (Wb K wB) p.sMT p.sFS cm' () π).bind fun c => pure (a && b && c) else pure false) = _
  rw [if_pos (Nat.zero_le _), batch_test, batch_link]
  rfl

theorem batch_arg : Spec.batch_arg := fun B K wB _ p cm cm' π => batch_V B K wB p cm cm' π

theorem batch_same : Spec.batch_same := fun _ _ _ => ⟨rfl, fun _ _ => rfl⟩

end Run.PQ
