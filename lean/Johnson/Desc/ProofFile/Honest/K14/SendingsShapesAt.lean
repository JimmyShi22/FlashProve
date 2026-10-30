-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsShapesAt.lean: the one public test on the two sendings'
shapes (sendingsFit, Honest/K14/SendingsShapes.lean) accepts the two typed shapes: kernel
evaluations.

  sendingsFit_key    at the typed sizes of a key of full size
  sendingsFit_real   at the typed sizes over a proof file's own codes

Limits. That a proof's sizes at the release's files are the typed ones is not claimed; into the
typed sizes over a proof file's codes numbers are written by hand. Of Johnson/Goal/ it imports one
module, for the typed sizes of a key alone: evaluated numbers; no goal is stated or used. Nothing on
a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes
import Johnson.Desc.K1.Law.CondReal
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open Desc.K14 (P14)

/-- It accepts the typed sizes of a key of full size. It reads neither the item nor the list of the
first chain's messages. -/
theorem sendingsFit_key (item : Nat) (bp : List (Nat × Nat)) :
    sendingsFit ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ = true := by
  have h : sendingsFit ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, 0, []⟩ = true := by
    decide +kernel
  exact h

/-- It accepts the typed sizes over a proof file's own codes. -/
theorem sendingsFit_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)),
      sendingsFit ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ = true := by
  obtain ⟨x, _, _, hx, _⟩ := VerifiableInference.Desc.K1.real_members
  refine ⟨x, hx, fun item bp => ?_⟩
  have h : (realSized.all fun p =>
      sendingsFit ⟨recordSet, .shared, codesFull2, p.1.shape, 0, []⟩) = true := by decide +kernel
  rw [hx] at h
  exact h

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendingsFit_key
#print axioms ProofFile.Honest.K14.sendingsFit_real
