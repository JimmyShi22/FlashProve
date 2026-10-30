-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, UNDER THE HEAD `P5J.AtMgA`: no prover and no filling is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupBaseWritten.lean: the kind "lookup" (K3): the closed
test `lookupBaseTest` (Honest/K3/Term/LookupBaseIsTheChainsCount.lean) accepts at the two written
lists, by Lean's kernel; four controls, in which it refuses; eight of the fifty numbers; and the law
without the test as a hypothesis. No definition.

Terms. Honest/K3/GLOSSARY.md. The written cut is `cutFirstFull` (358 rows;
Johnson/Desc/Ok/PlanWritten/CutLit.lean); the written list of places is `spotsWritten` (282 places;
Johnson/AtFull/Desc/SpotsWritten.lean).

What is shown.
  `lookupBaseWritten`: by Lean's kernel: at each link below 25 and both sorts the written cut has a
    row at `IM.k3Place l d`, and its start there is `baseIn spotsWritten` of that place.
  `lookupBaseWrittenRefusesALongerRow`: a control, by Lean's kernel: with one round more in the
    written cut's third row ("G0:1", the first row that has a round) the test refuses.
  `lookupBaseWrittenRefusesTheLastLookupAlone`: a control, by Lean's kernel: with one round more in
    the row "H:7", which stands in front of the last of the fifty lookups alone, the test accepts at
    the first 49 and refuses at the last.
  `lookupBaseWrittenRefusesALostPlace`: a control, by Lean's kernel: without the first of the
    written places the test refuses.
  `lookupBaseWrittenRefusesLinkTwentyFive`: a control, by Lean's kernel: at link 25 it refuses.
  `lookupStartsWritten`: by Lean's kernel: eight of the fifty starts in the written cut, as
    numerals.
  `lookupBaseIsTheChainsCount`: THE LAW: under the head, at every site of `lookSites Zp`:
    `roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base`.
  `lookupBaseIsTheRoundsToTheBorder`: the same in the form that a thread's seat asks:
    `s.at_.base = roundsTo cF.blocksInOrder (borderOf s.link s.digits)`.

Hypotheses that remain. `h`: `P5J.AtMgA`.

Whether the law is empty. It is not: Honest/K3/Term/LookupSiteFitsAtLiveFiles.lean
[not in this library] has a head with fifty sites at all live public files in the goals' scope, and
AtFullSide/Honest/K3/Term/LookupSiteFitsAtTheFullFiles.lean [not in this library] at the named files
`VerifierAndGoals.storedPublicFiles`, with no premise. Neither is called here.

Limits. The closed facts stand at two written lists: that these are what the planner makes of any
public files is said under the head alone (`AtMg.cut_written`, Johnson/P5J/NumbersAtHead.lean;
`spots_at`, Johnson/AtFull/Shape/SitesAtHead.lean). Four controls. The full size alone. On public
data alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBaseIsTheChainsCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Desc (spotsWritten)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- **The closed fact**, by Lean's kernel: the test accepts the two written lists. -/
theorem lookupBaseWritten : lookupBaseTest cutFirstFull spotsWritten = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: one round more in the written cut's third row: refused. -/
theorem lookupBaseWrittenRefusesALongerRow :
    lookupBaseTest (cutFirstFull.modify 2 fun row => (row.1, row.2.1, row.2.2.1 + 1, row.2.2.2))
      spotsWritten = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: one round more in the row "H:7", number 344, which stands in front
of the last of the fifty lookups alone: accepted at the first 49, refused at the last. -/
theorem lookupBaseWrittenRefusesTheLastLookupAlone :
    ((List.range 25).flatMap fun l => [false, true].map fun d =>
      lookupBaseTestAt
        (cutFirstFull.modify 344 fun row => (row.1, row.2.1, row.2.2.1 + 1, row.2.2.2))
        spotsWritten l d) = List.replicate 49 true ++ [false] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: without the first of the written places: refused. -/
theorem lookupBaseWrittenRefusesALostPlace :
    lookupBaseTest cutFirstFull (spotsWritten.eraseIdx 0) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control, by Lean's kernel: there is no link 25. -/
theorem lookupBaseWrittenRefusesLinkTwentyFive :
    ([false, true].any fun d => lookupBaseTestAt cutFirstFull spotsWritten 25 d) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first and the last four of the fifty starts in the written cut, as numerals. -/
theorem lookupStartsWritten :
    [(0, false), (0, true), (1, false), (1, true), (23, false), (23, true), (24, false),
      (24, true)].map (fun y => startInCutRows cutFirstFull (IM.k3Place y.1 y.2)) =
    [some 2, some 1223, some 1982, some 3133, some 44409, some 45560, some 46289, some 47456] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT EVERY SITE THE NUMBER OF ROUNDS IN FRONT THAT THE SITE BEARS IS THE CHAIN's OWN COUNT.**
Conditional on the head. -/
theorem lookupBaseIsTheChainsCount (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base :=
  lookupBaseIsTheChainsCountOfWritten lookupBaseWritten h s hs

/-- **The same in the form that a thread's seat asks.** Conditional on the head. -/
theorem lookupBaseIsTheRoundsToTheBorder (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) :
    s.at_.base =
      roundsTo cF.blocksInOrder (VerifiableInference.Desc.Sound.MgAt.borderOf s.link s.digits) :=
  lookupBaseIsTheRoundsToTheBorderOfWritten lookupBaseWritten h s hs

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupBaseIsTheRoundsToTheBorder
#print axioms ProofFile.Honest.K3.Term.lookupBaseWritten
#print axioms ProofFile.Honest.K3.Term.lookupBaseWrittenRefusesALongerRow
#print axioms ProofFile.Honest.K3.Term.lookupBaseWrittenRefusesTheLastLookupAlone
#print axioms ProofFile.Honest.K3.Term.lookupBaseWrittenRefusesALostPlace
#print axioms ProofFile.Honest.K3.Term.lookupBaseWrittenRefusesLinkTwentyFive
#print axioms ProofFile.Honest.K3.Term.lookupStartsWritten
#print axioms ProofFile.Honest.K3.Term.lookupBaseIsTheChainsCount
