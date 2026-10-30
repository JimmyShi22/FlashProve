-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/AtStep.lean: the proofs of `LaterDrawsNoDigest` and
`HeadMergeLiveAtStep` (Honest/K11/Mark/AtStepStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. Taking the digest off leaves a round's drawn elements: by definition. A filled slot lies below
the next free number where nothing at or above that number is filled. Then `headMergeMarkSilent`
(Proofs.lean of this folder), `headMergeLaterFit` (Join.lean) and `headMergeLiveBehind`
(Johnson/Desc/K11/Live/Behind.lean), the last at the rounds without the digests.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.AtStepStatement
import Johnson.Desc.ProofFile.Honest.K11.Mark.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (noDigest)
open Johnson.Desc.First.ForkMerge.Live (laterDraws headMergeLiveBehind)

/-- **The drawn elements are the same with and without the digest.** -/
theorem laterDrawsNoDigest : LaterDrawsNoDigest := by
  intro R
  unfold laterDraws
  rw [← List.map_drop, List.flatMap_map]
  rfl

/-- **The condition behind the member's step, where the mark says nothing.** -/
theorem headMergeLiveAtStep : HeadMergeLiveAtStep := by
  intro P fr s s' R a x hs hf h ha hx hfil hfree
  have hsv : x.sV < a.F.next := by
    by_contra hc
    exact hfree x.sV (by omega) hfil
  refine headMergeLiveBehind P s s' (R.map noDigest) a x h ha hx hsv ?_
  rw [laterDrawsNoDigest R]
  exact headMergeMarkSilent P fr R hs (headMergeLaterFit P R hf)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.laterDrawsNoDigest
#print axioms ProofFile.Honest.K11.headMergeLiveAtStep
