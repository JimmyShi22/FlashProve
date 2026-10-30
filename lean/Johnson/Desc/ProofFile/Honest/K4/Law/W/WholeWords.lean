-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/WholeWords.lean: CONDITIONAL.

What is here. WHERE THE DESCRIPTION's OWN TEST ON THE INSTANCE ACCEPTS, THE REQUEST FILE IS WHOLE
WORDS: its size is a multiple of 4. The library's `ProofFile.holdBy` (Johnson/Desc/ProofFile/Pub.lean)
asks that first, under the name «the words test»; `ProofFile.okBy` is the same as a Bool, and the
description's field okStart holds it (Johnson/Desc/ProofFile/Frames1.lean). What it is for: the
hypothesis h4 | hW4 of Law/W/TokOfFine.lean, which the verifier's tests on the request's words do
not give. Each proof unfolds the test.

  `whole_of_hold`   from a return of `holdBy`.
  `whole_of_okBy`   **from `okBy … = true`.**

Not shown here. THAT THE TEST ACCEPTS AT ANY INSTANCE: a hypothesis. THAT A RUN OF THE HONEST SIDE
HAS PASSED IT: the frame's `ready` (Honest/Frame.lean) does not call okStart: whoever wants the
clause at a run's instance must hold the test's answer from elsewhere: THE FRAME's STATEMENTS OVER A
RUN EACH TAKE IT AS A PREMISE (hx : F.okStart x = true: Honest/Thread/FileYes.lean,
Honest/Law/AcceptJ.lean and their like), and Law/W/WholeAtStart.lean has the step from okStart to
`okBy` at the seated description's own term. Nothing on the reply file, though the same test asks
the like of it. General in the public part, in the function o that stands for the format's second
hash function, and in the maker of the links' data. No test stands beside it. Nothing on soundness, on
completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH: Johnson/Desc/ProofFile/Pub.lean and what that imports; by a
program's walk from import to import: no module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or
ThirdParty/, none whose name begins Cb.Bridge, and none whose name holds RecCompile. It imports
nothing of the honest side.
-/
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W

/-- CONDITIONAL: on h. The request file is whole words, from a return of the test on the
instance. -/
theorem whole_of_hold {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    {G : ProofFile.Ground} (h : ProofFile.holdBy o mk Z x = .ok G) : x.pub.request.size % 4 = 0 := by
  by_contra hn
  have hb : (x.pub.request.size % 4 != 0 || x.y.size % 4 != 0) = true := by
    rw [Bool.or_eq_true]
    exact Or.inl (bne_iff_ne.mpr hn)
  unfold ProofFile.holdBy at h
  rw [hb] at h
  have h' : (Except.error ("the words test", "statement-required") :
      Except (String × String) ProofFile.Ground) = .ok G := h
  cases h'

/-- CONDITIONAL: on h. **THE REQUEST FILE IS WHOLE WORDS WHERE THE TEST ON THE INSTANCE
ACCEPTS.** -/
theorem whole_of_okBy {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) : x.pub.request.size % 4 = 0 := by
  unfold ProofFile.okBy at h
  cases hh : ProofFile.holdBy o mk Z x with
  | ok G => exact whole_of_hold hh
  | error e =>
    rw [hh] at h
    simp [Except.toOption] at h

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.whole_of_hold
#print axioms ProofFile.Honest.K4.W.whole_of_okBy
