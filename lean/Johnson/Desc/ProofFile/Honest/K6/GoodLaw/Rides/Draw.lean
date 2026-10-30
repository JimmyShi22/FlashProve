-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Rides/Draw.lean: THE INVARIANT `K6GoodAt`
(Honest/K6/GoodLaw/Runs.lean) RIDES THE BATCHING's OWN SAMPLE: where it stands at the state in front
of the batching's one round, it stands at the state behind that round's accepting decision, at every
sample. One lemma, by three calls. None of the library's goals.

  `good_across_draw`   at the decision of `K9.drawAlone` at any place p, on one round with the one
                    sample y: the form of the first clause of a gatherer's law on the head's
                    segment, at the invariant `K6GoodAt` alone, where the invariant stands in front

Who pays what. That the round leaves what the head has heard, and its ledger, alike:
`ProofFile.Honest.K9.draw_alikeFront` (Honest/K9/DrawFront.lean). That the invariant rides along that
relation: `k6GoodAt_front` (Runs.lean). That a state with the invariant stands in the head's
segment: `k6GoodAt_head` (same file).

Limits. AN IMPLICATION: THAT THE INVARIANT STANDS AT ANY STATE IS NOT SHOWN HERE. OF `K6GoodAt`
ALONE: another sub-protocol's condition that stands beside it in a joint invariant is that
sub-protocol's to carry. No hypothesis on the public files is asked: p, the shape, the parameters
and the window's two ends b and e are letters.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Runs
import Johnson.Desc.ProofFile.Honest.K9.DrawFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6.GoodLaw
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds

/-- **ACROSS THE BATCHING's OWN SAMPLE.** No hypothesis on the public files: p is a letter. -/
theorem good_across_draw {h : OnBytes.Model.Head.Shape} {iU3 : Nat} {q : Head.Par} {b e : Nat}
    (p : VerifiableInference.Desc.K9.Where) (s t : S) (y : OnBytes.E)
    (hd : (VerifiableInference.Desc.K9.drawAlone (Cl := Claim) VerifiableInference.Desc.K9.atS
      p).decide s [⟨[], ProofFile.Honest.K9.drawnOne y⟩] [] = .ok t)
    (k : K6GoodAt h iU3 q b e s) : K6GoodAt h iU3 q b e t := by
  obtain ⟨o, ho⟩ := k6GoodAt_head k
  exact k6GoodAt_front h iU3 q (ProofFile.Honest.K9.draw_alikeFront p s t y o ho hd) k

#print axioms good_across_draw

end ProofFile.Honest.K6.GoodLaw
