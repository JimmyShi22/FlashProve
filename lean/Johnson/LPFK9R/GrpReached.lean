-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/GrpReached.lean: ONE OF THE DEBTS (`K9Owes.grp`,
ArmsAtFlat.lean [not in this library]: in front of the one equation «the group
that the link's context names is the plan's group of the segment»), AT THE FENCE «REACHED»
(`Reach`, Johnson/Top/H0/Walk/Reach.lean), IN THE GOALS' SCOPE. The statement and the proof's plan
are taken over (read in a text of this project that is not in this repository); the line
that that text left open («the batching's reader returns the open link's context») is `part_reads`
(Johnson/Desc/First/Link/Law/RbRuns.lean).

What is said.
  `grp_reached`: **in scope, at every link l < 25 and every state s reached at the border in front
    of the one equation (number 14 l + nAt l + 4): where the batching's reader returns the part a:
    `N.groupAt l = a.L.check.group`**, for numbers N with `N.groupAt l = l`.

Limits. `N.groupAt l = l` is a premise: a sentence on the plan's numbers (it holds at the closed
constant by definition). The scope's three premises stand. It says nothing of the promise's public
tests: `K9Owes.grp` has them as a hypothesis more, which is not spent. Nothing on soundness.

-/
import Johnson.IMR.GroupHead
import Johnson.IMR.TableW
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.First.Link.Law.RbRuns

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin (part_reads)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S Numbers)
open IM (nAt)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **K9Owes.grp AT THE FENCE «REACHED».** -/
theorem grp_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (p : ProofFile.InstPub)
    {N : Numbers} {l : ℕ} (hl : l < 25) (hNg : N.groupAt l = l) :
    ∀ s a, Johnson.Desc.First.Walk.Tied.Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + nAt l + 4 + 0)
        (p, s) → atS.get? s = some a → N.groupAt l = a.L.check.group := by
  intro s a hf ha
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.Reach.fold hf
  rw [hNg]
  exact ((Meaning.K2.group_is hS hR O hl (by omega) (by unfold IM.nAt; split <;> omega) f a.L
    (part_reads s a ha).1).1).symm

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.grp_reached
