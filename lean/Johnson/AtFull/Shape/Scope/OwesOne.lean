-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesOne.lean: THE FIELD owes₁ OF L25's ThreadFields
(AtFullSide/Honest/ThreadsAtTheTerm.lean): OwesS at the first thread of a run, at the walk from the
first stand, from its debt by houses. One theorem; a joining; nothing is evaluated.

Limits. FirstOwed is a premise. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.OwesByKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type}

/-- **owes₁.** -/
theorem owes_one {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (parts : FirstThreadParts A) (R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (F : FirstOwed h parts R.own (FirstWalk h parts R) Bs) :
    OwesS (firstThread h parts R.own) (FirstWalk h parts R) :=
  owes_of_kinds h parts R.own _ (fun b k m hs => saidOk_of_walk _ b k m hs) hB F

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.owes_one
