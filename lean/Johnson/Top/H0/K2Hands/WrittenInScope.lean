-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/WrittenInScope.lean: the code switch: A TIE FROM THE WRITTEN VALUES TO THE
PUBLIC PART: the closed facts by Lean's kernel of this kind's law stand at the written codes,
shape and list of shapes (`csW`, `shW`, `MW`: FrontsFull.lean) and at the written table
(`tableFullLit`); this file says that the public part's own are these, in the goals' scope, where
the public part is made and the named test `madePinnedAt` accepts. A join of other files'
theorems; nothing is evaluated.

Main names:
  `written_in_scope`: the public part's first chain's codes are `csW` · its shape of a request is
    `shW` · the shapes listed off its first chain's sendings are `MW` · each entry of
    `tableFullLit` has the public part's codes. By `first_written_in_scope` and `sends_in_scope`
    (Johnson/Goal/Numbers/MadeInScope.lean), `codes_written`
    (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean) and `cs_at25`
    (Johnson/Top/H0/K2Caller/ClosedAt25.lean).
Limits. `madePinnedAt` is a named test that the sealed verifier does not ask.
(Where this and lean/THEOREM.md differ, the page
holds.) That the verifier's
typed structure at a place IS the written table's entry is not said here: it is read off the three
files by another road. Nothing on soundness. On hiding nothing.

-/
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Top.H0.K2Caller.ClosedAt25
import Johnson.Top.H0.K2Hands.FrontsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit cs_at25)
open VerifiableInference.PlanWritten (madePinnedAt codes_written)
open VerifiableInference.PlanWritten.Joined (sends_in_scope first_written_in_scope)

/-- **The public part's codes, shape and listed shapes are the written ones, and each written entry
    of
the code switch's table has these codes**: in the goals' scope, where the public part is made and
    the
test `madePinnedAt` accepts. -/
theorem written_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.first.codes = csW ∧ Z.first.shape = shW ∧ K12.Door.msgsOfChain Z.made.proof.1 = MW ∧
      ∀ (m : ℕ) (r : SwRow), tableFullLit[m]? = some r → r.cs = Z.first.codes := by
  have f := first_written_in_scope hW h hy
  refine ⟨f.1, f.2.2.1, by rw [sends_in_scope hW h hy]; rfl, fun m r hr => ?_⟩
  rw [f.1, codes_written]
  exact cs_at25 hr

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.written_in_scope
