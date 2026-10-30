-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AcceptedOfGuard.lean: the proofs of `ReadyIsReady` and
`HeadMergeAcceptedOfGuard` (Honest/K11/Plays/AcceptedOfGuardStatement.lean), to the letter. Lemmas;
none of the library's goals.

How. The two definitions have one text: by definition. Then `guardIsReady`
(Johnson/Desc/K11/Shape/Step.lean) and `headMergeAccepted` (Honest/K11/Plays/Accepted.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.AcceptedOfGuardStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Accepted
import Johnson.Desc.K11.Shape.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.ShapeStep (guardIsReady)

/-- **One sentence.** -/
theorem readyIsReady : ReadyIsReady := fun _ _ => Iff.rfl

/-- **The member's step says yes, from the test on the shape.** -/
theorem headMergeAcceptedOfGuard : HeadMergeAcceptedOfGuard := by
  intro Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf hg
  exact headMergeAccepted Bk W₀ Rc Xi Tr X Pb T b P claims weights name pl hmem hhalf
    fun k s m E hT => (readyIsReady P s).2 ((guardIsReady P s).1 (hg k s m E hT))

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.readyIsReady
#print axioms ProofFile.Honest.K11.headMergeAcceptedOfGuard
