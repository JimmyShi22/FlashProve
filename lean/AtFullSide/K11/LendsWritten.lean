-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsWritten.lean: at the written rows and entries of the maker's book the public test
k11Lends (Honest/K11/Plays/LotsPublicStatement.lean: whether the book lends the merge's row of parts)
says yes, on chain 0, at the merge's place, at 18 column bits, and no at three bends. The terms stand
in LendsBook.lean; each of the four closed facts stands in a file of its own, so that they build side
by side: k11LendsW (LendsYes.lean), k11LendsW_short, k11LendsW_elsewhere, k11LendsW_other_chain.

What it is not. Nothing on any book but the written term: that what bookWhole returns has these rows
and entries, and that the test reads no cuts, stand in LotsAnswerAtTheBook.lean. Whether, not what.

Limits. Four closed facts by evaluation in Lean's kernel, three of them controls, each led past
String.splitOn and String.toNat? by Johnson.Unfolds.splitOn_eq and slice_toNat?_eq. maxRecDepth is
raised to 1000000 and maxHeartbeats to 0 at each. Replayed by no independent checker. Full size only,
at the hash function secondHashFunction.
-/
import AtFullSide.K11.LendsYes
import AtFullSide.K11.LendsShort
import AtFullSide.K11.LendsElsewhere
import AtFullSide.K11.LendsOtherChain

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.k11BookW
#print axioms AtFullSide.K11.k11ParW
#print axioms AtFullSide.K11.k11LendsW
#print axioms AtFullSide.K11.k11LendsW_short
#print axioms AtFullSide.K11.k11LendsW_elsewhere
#print axioms AtFullSide.K11.k11LendsW_other_chain
