-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12CutSplitW
import Johnson.Loose.H2K12.K12CutSumW
import Johnson.Loose.H2K12.K12CutNamesW
import Johnson.Loose.H2K12.K12LocsW
import Johnson.Loose.H2K12.K12OffW
import Johnson.Loose.H2K12.K12OffLaterW
import Johnson.Desc.K12.Law.PlacesFull
/-
H2K12/K12CutW.lean: FOR THE PROXIMITY TEST's (the kind K12's) ROW: WHAT
H2U.placesOfMade ASKS OF THE FIRST CHAIN's LONG LIST, AT THE WRITTEN LIST (proofThree.A,
Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean): THE JOININGS. No evaluation in Lean's kernel
stands in this file: each closed fact that it spends stands alone in a file of its own.
  free77           the written member's first free own number is 77: by the member's text
  cutW             cutLAt (H2K12/K12MemberOfParts.lean: H2U.cutTestL's text) at proofThree's three
                   lists and the written stages of the last test returns: chain 0, start 48,237, 77
                   roots in front, these stages. From splitW, sumW, namesW by cutLAt_of_split
                   (H2K12/K12CutSplit.lean)
  locsP            the first written plan has 25 rounds named "LOC". From locsW by count_of_lit
  offP0            the first written plan has no entry that is no round. From offW0 by off_of_lit.
                   offP1, offP2: the like for the two short plans, from offW1, offW2
                   (H2K12/K12OffLaterW.lean)
WRITTEN VALUES: that the planner makes them of any public files is not said here. No soundness
statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params H2U
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree)
open H2K.Member (piLFull)

theorem free77 : piLFull.nums.free = 77 := rfl

/-- **The last test's cut at the written list.** -/
theorem cutW :
    cutLAt [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan]
        proofSizedFull.request.last =
      some ⟨0, 48237,
        ((proofThree.A.plan.rounds.map (·.entry)).drop 48237).take
          (1 + towerLen proofSizedFull.request.last),
        77, proofSizedFull.request.last⟩ :=
  cutLAt_of_split rfl splitW sumW namesW

theorem locsP :
    (proofThree.A.plan.plan.rounds.filter fun e => e.name == "LOC").length = 25 :=
  (count_of_lit proofThree.A fun e => e.name == "LOC").trans locsW

theorem offP0 :
    proofThree.A.plan.plan.entries.length - proofThree.A.plan.plan.rounds.length = 0 :=
  (off_of_lit proofThree.A).trans offW0

theorem offP1 :
    proofThree.B.plan.plan.entries.length - proofThree.B.plan.plan.rounds.length = 0 :=
  (off_of_lit proofThree.B).trans offW1

theorem offP2 :
    proofThree.C.plan.plan.entries.length - proofThree.C.plan.plan.rounds.length = 0 :=
  (off_of_lit proofThree.C).trans offW2

end H2K12

#print axioms H2K12.free77
#print axioms H2K12.cutW
#print axioms H2K12.locsP
#print axioms H2K12.offP0
#print axioms H2K12.offP1
#print axioms H2K12.offP2
