-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/WholeAtStart.lean: CONDITIONAL.

What is here. AT THE SEATED DESCRIPTION's OWN TERM `P5J.F0T` (Johnson/P5J/AtTerm.lean), WHERE ITS
FIELD okStart ACCEPTS AN INSTANCE, THE INSTANCE's REQUEST FILE IS WHOLE WORDS: its size is a
multiple of 4. The field is `ProofFile.okBy` at the library's own maker of the links' data, and a test of
the shared chain's seat (`ProofFile.fileDescBy`, Johnson/Desc/ProofFile/Frames1.lean): by unfolding;
`whole_of_okBy` (Law/W/WholeWords.lean) does the rest. What it is for: the frame's statements over a
run each take «okStart accepts the run's instance» as a premise (hx in Honest/Thread/FileYes.lean,
Honest/Law/AcceptJ.lean and their like): so whoever states such a statement AT THIS TERM has, by
this lemma, that the run's instance's request file is whole words. TWO STEPS LIE BETWEEN THAT AND
THE HYPOTHESIS hW4 OF Law/W/TokOfFine.lean, neither made here: the frame's premise speaks of a
description F at large, this lemma of the one term: that the description which the maker returns is
this term is `atPure_desc` (Law/DescAtPure.lean), under the library's hypothesis on the public
files; and hW4 speaks of the instance in the thread's own input, which is the run's by
`own_x_of_ready` (Law/TokensSeatReady.lean) at a run that is ready.

  `okBy_of_okStart`   the first half of the field.
  `whole_of_okStart`   **the request file is whole words.**

Not shown here. THAT okStart ACCEPTS AT ANY INSTANCE: a hypothesis. THAT A RUN OF THE HONEST SIDE
HAS PASSED IT: the frame's `ready` (Honest/Frame.lean) does not call it. No call of a statement of
the frame's is made here: that its premise hx is this lemma's h is by reading. General in the public
part, in the function o that stands for the format's second hash function, in the places and in the first
chain. No test stands beside it. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 3 modules under Johnson/Goal/ and at 3 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 6 is not counted: all the numbers are floors. They come with
Johnson/P5J/AtTerm.lean. It imports nothing of the honest side but Law/W/WholeWords.lean. A LAW, NOT
A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.WholeWords
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W

/-- CONDITIONAL: on h. The first half of the field okStart of the seated description's own term. -/
theorem okBy_of_okStart (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) {x : ProofFile.Inst}
    (h : (P5J.F0T o Zp Np cF).okStart x = true) :
    ProofFile.okBy o ProofFile.pureRoad.links Zp x = true := by
  change (ProofFile.okBy o ProofFile.pureRoad.links Zp x && _) = true at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- CONDITIONAL: on h. **THE REQUEST FILE IS WHOLE WORDS WHERE THE SEATED DESCRIPTION's okStart
ACCEPTS.** -/
theorem whole_of_okStart (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl) {x : ProofFile.Inst}
    (h : (P5J.F0T o Zp Np cF).okStart x = true) : x.pub.request.size % 4 = 0 :=
  whole_of_okBy (okBy_of_okStart o Zp Np cF h)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.okBy_of_okStart
#print axioms ProofFile.Honest.K4.W.whole_of_okStart
