-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ShapeAtFirst.lean: AT THE FIRST THREAD OF A RETURN OF THE MAKER THE FAMILY shapeJ
HOLDS AT EVERY BORDER WHERE THE INVARIANT DOES. A joining; nothing is evaluated.

* **shapeJ_at_first**: Thr (firstThread h parts w) b k s m E ⊢ shapeJ … b s, from hyes alone: the list and
  ft of that thread by rfl, its first state by its text, the request's test by reqOk_of_okStart off
  ReadyInput's first clause.

Limits. It needs that the thread's valid holds okStart at the input. hyes stays a premise. It frees the family J and what carries it from stops and falls; it says
nothing of the acceptance of a member at the honest play. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Shape.Scope.BlockYesClosed
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import E2E.StartReqOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc
open ProofFile.Honest
open ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **THE SHAPE AT THE FIRST THREAD: NO FAMILY J AS A PREMISE.** -/
theorem shapeJ_at_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    {b : Nat} {k : Coins A.B} {s : VerifiableInference.Desc.First.S}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hb : b ≤ 358)
    (hA : Thr (firstThread h parts w) b k s m E) :
    shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA b s :=
  shape_at_thr h.head hB (firstThread h parts w) rfl rfl hyes
    (fun _ w' _ _ hv hg => ⟨w'.x.pub, hg, AtPublicFiles.Start.reqOk_of_okStart hv.2.1⟩) hb hA

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.shapeJ_at_first
