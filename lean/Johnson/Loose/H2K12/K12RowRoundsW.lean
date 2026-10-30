-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12RowAlone
import Johnson.AtFull.Rounds.ListAt
/-
Johnson/Loose/H2K12/K12RowRoundsW.lean: THE PROXIMITY TEST's (the kind K12's) SECOND
ROW AMONG THE ROWS THAT "what the sub-protocols themselves declare is the written list of declared
rounds" WANTS OF EACH LOT: THE CLOSED FACTS. Apart in its file, since they are evaluations in Lean's
kernel (decide +kernel): two.
  roundsL_full     at the written member piLFull (Johnson/Desc/K12/Law/PlacesFull.lean) the declared
                   rounds of the lot's one sub-protocol (lotB, H2K12/K12RowAlone.lean) are the list
                   that the written table bears at the name "F:2"
                   (Johnson.AtFull.Rounds.listAt, Johnson/AtFull/Rounds/ListAt.lean:
                   its list number 51: 33 rounds). Both sides are closed terms
  placeL_full      and its place is ⟨1, none, 2, K12⟩
THE NAME IS WRITTEN IN FULL: other definitions in this library bear the short name listAt.
WHAT IT IS NOT: that the list of rounds gives the written member is not said here
(H2K12/K12MemberWritten.lean). That a spot at that place bears the name "F:2" is not said here. The
full size alone. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open H2K.Member (piLFull)

/-- **AT THE WRITTEN MEMBER: THE WRITTEN LIST OF DECLARED ROUNDS.** -/
theorem roundsL_full : (lotB piLFull).rounds = Johnson.AtFull.Rounds.listAt "F:2" := by
  decide +kernel

theorem placeL_full : (lotB piLFull).place = ⟨1, none, 2, .K12⟩ := by
  decide +kernel

end H2K12

#print axioms H2K12.roundsL_full
#print axioms H2K12.placeL_full
