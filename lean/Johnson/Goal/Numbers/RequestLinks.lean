-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/RequestLinks.lean: two closed facts on the written shape of a request, and what
they give in scope. The written shape of a request has 25 links, and says one answer to each
out-of-domain (OOD) sample; and so, in the goals' scope and under the tests' yes, has the shape in
the planner's sizes of a proof file and the shape in the first chain's parameters as read back.

Statements.
  `request_links_written`: `proofSizedFull.request.link.length = 25`
    (Johnson/Desc/Ok/PlanWritten/SizedLit.lean). By an evaluation in Lean's kernel (`decide
    +kernel`).
  `request_links_in_scope`: by `sized_in_scope`. `first_links_in_scope`: by `first_in_scope`
    (Johnson/Goal/Numbers/KeyInScope.lean).
  `request_answers_written`: `proofSizedFull.request.answers = 1`. By the kernel.
    `par_one_in_scope`: so the first chain's two numbers (`Par`, Johnson/Desc/First/State.lean) are
    0 and 1: from the text of `parP`, the first state's own test (`startOk`; `pubBy_start`,
    `startP_ok`, Johnson/Desc/ProofFile/Law/PureMade.lean; `pubBy_fields`,
    Johnson/Desc/ProofFile/Law/PlainMade.lean) and the third equation of `first_in_scope`.

Limits. Those in scope have a member only where the public part is computed and the test says yes.
Nothing on soundness.
-/
import Johnson.Goal.Numbers.KeyInScope
import Johnson.Desc.ProofFile.Law.PlainMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

/-- The written shape of a request has 25 links. -/
theorem request_links_written : proofSizedFull.request.link.length = 25 := by decide +kernel

/-- The written shape of a request says one answer to each out-of-domain (OOD) sample. -/
theorem request_answers_written : proofSizedFull.request.answers = 1 := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}

theorem request_links_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : sizedPinnedAt Z.p.X.P Z.p.chains.made = true) :
    Z.p.chains.made.sized.proof.request.link.length = 25 := by
  rw [sized_in_scope hW h hy]
  exact request_links_written

theorem first_links_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : firstPinnedAt Z.p.X.P Z.first = true) : Z.first.shape.link.length = 25 := by
  rw [(first_in_scope hW h hy).2.2.1]
  exact request_links_written

/-- **The first chain's two numbers in scope**: it takes over no tree, and there is one answer to
each OOD sample. Where the public part is computed the first state has passed its own test, that
the shape's number of answers is the chain's. -/
theorem par_one_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : firstPinnedAt Z.p.X.P Z.first = true) : Z.P = ⟨0, 1⟩ := by
  have hZ : ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts W.pol W.lay W.KL = .ok Z := h
  have hP : Z.P = Desc.First.parP Z.first := (ProofFile.Law.pubBy_fields hZ).2.2.2.2.1
  have hok := ProofFile.Law.startP_ok (ProofFile.Law.pubBy_start hZ)
  unfold Desc.First.S.startOk at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  have ha : Z.first.shape.answers = (Desc.First.parP Z.first).samples := hok.2.1.2
  rw [(first_in_scope hW h hy).2.2.1, request_answers_written] at ha
  rw [hP]
  show (⟨0, (Desc.First.parP Z.first).samples⟩ : Desc.First.Par) = _
  rw [← ha]

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.request_links_written
#print axioms VerifiableInference.PlanWritten.request_links_in_scope
#print axioms VerifiableInference.PlanWritten.first_links_in_scope
#print axioms VerifiableInference.PlanWritten.request_answers_written
#print axioms VerifiableInference.PlanWritten.par_one_in_scope
