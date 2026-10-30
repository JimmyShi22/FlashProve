-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PublicAtWritten.lean: the kind "the code switch" (K2): FIVE
PUBLIC TESTS AT THE WRITTEN PLAN, BY LEAN's KERNEL, EACH WITH A CONTROL: at the closed list of the
kind's 25 places (`placesW`, Honest/K2/Law/PlacesWritten.lean): `Sizes.serves` · `Sizes.roomy` ·
`placeFits` · the honest sending's number of answers is the plan's (`answersFit`) · and at the links
1 to 23: every tree that the switch reads is told in front of it. Definitions with code; every
theorem is `decide +kernel` under a raised recursion depth. No head, no state, no prover.

  NOT FOR NOTHING: that the list has 25 members, and at each place `switchPlaceAt l`, l from 1 to
  23, just one, are `placesW_count` and `placesW_one` (Honest/K2/Law/PlacesCount.lean).
  `servesW`, `roomyW`, `fitsW` the three tests on a place's own data say yes at all 25
  `servesW_can_fail` CONTROL: no at the first place with the target's rest moved to the mask's rows,
                    and no with its main block moved there, WHILE THE CLAUSE ON THE COUNT OF KEPT
                    TARGETS STILL HOLDS at the first bend: so it is the clause on the part that
                    fails
  `roomyW_can_fail` CONTROL: no at the first place with each kept shape's main rows raised by one,
                    WHILE THE REST STILL HAS ROOM THERE (`restFits`): so it is the verifier's own
                    test on the target that fails
  `fitsW_can_fail` CONTROL: no at the first place with the next fold's row variables raised by
                    100000, WHILE ALL CLAUSES BUT THE ONE ON THE RIDING TABLE STILL SAY YES THERE
                    (`fitsNoRide`): so it is the fresh mask's fit that fails
  `answersW` at all 25: the plan has numbers at the place's link, and `answersFit` says yes
  `answersW_can_fail` CONTROL: the first place's count against the plan's numbers at link 2, which
                    are there: no
  `opensW` at the links 1 to 23: the plan has numbers, and each tree that they read is below
                    `treesTold toldFull (14 l + 2)`
  `opensW_three` NOT FOR NOTHING: at each of these links three trees are read
  `opensW_can_fail` CONTROL, A PAIR THAT PINS THE BORDER: counted eight sub-protocols in front of
                    each switch the test still says yes; counted nine in front it says no, at one
                    link at the least
  `spotsW_nodup` the written places of the kind K2 have no place twice: WITHOUT A CONTROL

By: nothing but the definitions. THE PATTERN, AND NEAR RELATIVES, NOT CALLED: `switchesTest`,
`switches_written`, `switch_shifted_no` (Johnson/Desc/K1/Law/SitsSwitch.lean): at `IM.prepW`, group
by group: the numbers' codes and announced messages are the written ones · `index_below_written`
(Johnson/Top/H0/K2Ties/IndexBelow.lean), `told_trees` (Johnson/Top/H0/K2Ties/ToldAt.lean): other
looks at `treesTold toldFull` · `placesW_nodup` (Johnson/LPFK9R/ToldInScope.lean): the flat list's
358 places. · FOR THE SMALL EXAMPLE THERE IS NO THEOREM, ONLY WHAT LEAN's PLAIN EVALUATOR SAID: a
sheet of tests beside Honest/K2/Law/PlaysAtPlan.lean (K2PlaysPremises: no file of this library): at
each member of `switchPlaces` itself at the small example's public files (five places): the plan has
numbers · `serves` · `roomy` · `placeFits` · the light closing test · `answersFit`: yes, and no at
two bent controls a place; of the trees that a switch reads it asks nothing.

Limits. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. THEY SAY THAT PUBLIC
TESTS PASS AT THE WRITTEN PLAN: nothing on what a prover sends, nothing on a run. That the closed
list is the kind's places at any public files is another file's (Honest/K2/Law/PlacesWritten.lean,
under the head). `Sizes.roomy` calls the verifier's own test at stand-ins made of the sizes: that
these are a run's own statement and rows is not shown (Honest/K2/Part.lean says so). The closing's
test is not here. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesCount
import Johnson.Desc.ProofFile.Honest.K2.Law.PlanAsks
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysAtPlan
import Johnson.Desc.K2.Honest.Returns.SeatAtLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt)
open Johnson.AtFull.Desc (spotsWritten)

/-- The plan's numbers at a link, at the written plan. -/
def numsW (l : Option Nat) : Option P1K2.Nums := IM.prepW.bind fun P => P1K2.numsAt P l

/-- The number of answers, place by place. lk: at which link the plan's numbers are taken. -/
def answersB (ps : List SwitchPlace) (lk : SwitchPlace → Option Nat) : Bool :=
  ps.all fun p => (numsW (lk p)).any fun n => answersFit p n

/-- The trees that the switches into the groups 1 to 23 read. back: how many sub-protocols in front
of the switch the told trees are counted; 0 is the test. -/
def opensB (back : Nat) : Bool :=
  (List.range 23).all fun i => (numsW (some (i + 1))).any fun n =>
    n.read.all fun t => decide (t.1 < treesTold toldFull (14 * (i + 1) + 2 - back))

/-- For a control: the target's rest moved to the mask's rows. -/
def restToMask (p : SwitchPlace) : SwitchPlace :=
  { p with sizes := { p.sizes with
      target := { p.sizes.target with rest := { p.sizes.target.rest with part := .mask } } } }

/-- For a control: the target's main block moved to the mask's rows. -/
def mainToMask (p : SwitchPlace) : SwitchPlace :=
  { p with sizes := { p.sizes with
      target := { p.sizes.target with main := { p.sizes.target.main with part := .mask } } } }

/-- For a control of the closing's test (Honest/K2/Law/ClosingTest.lean):
the kept shapes struck. Nothing in this file calls it. -/
def noKept (p : SwitchPlace) : SwitchPlace := { p with sizes := { p.sizes with kept := [] } }

/-- For a control: the second clause of `Sizes.roomy` alone: the rest is no longer than the places
that the verifier's text counts for it. -/
def restFits (p : SwitchPlace) : Bool :=
  decide (p.sizes.restLength ≤ (OnBytes.SwitchPlaces.make p.sizes.codes p.sizes.target).size)

/-- For a control: each kept shape's main rows raised by one. -/
def moreRows (p : SwitchPlace) : SwitchPlace :=
  { p with sizes := { p.sizes with
      kept := p.sizes.kept.map fun s => { s with mainRows := s.mainRows + 1 } } }

/-- For a control: the next fold's row variables raised by 100000. -/
def longFold (p : SwitchPlace) : SwitchPlace := { p with foldVars := p.foldVars + 100000 }

/-- For that control: `placeFits` with no table riding: all its clauses but the one on the ride. -/
def fitsNoRide (p : SwitchPlace) : Bool :=
  K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others)) fun _ => none

set_option maxRecDepth 1000000 in
theorem servesW : (placesW.all fun p => p.sizes.serves) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem servesW_can_fail :
    (((placesW.take 1).map restToMask).all fun p => p.sizes.serves) = false ∧
      (((placesW.take 1).map mainToMask).all fun p => p.sizes.serves) = false ∧
      (((placesW.take 1).map restToMask).all fun p =>
        p.sizes.target.kept.size == p.sizes.kept.length) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem roomyW : (placesW.all fun p => p.sizes.roomy) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem roomyW_can_fail :
    (((placesW.take 1).map moreRows).all fun p => p.sizes.roomy) = false ∧
      (((placesW.take 1).map moreRows).all restFits) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem fitsW : (placesW.all placeFits) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem fitsW_can_fail : (((placesW.take 1).map longFold).all placeFits) = false ∧
    (((placesW.take 1).map longFold).all fitsNoRide) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem answersW : answersB placesW (·.place.link) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem answersW_can_fail :
    answersB (placesW.take 1) (fun _ => some 2) = false ∧ (numsW (some 2)).isSome = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem opensW : opensB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opensW_three : ((List.range 23).all fun i =>
    (numsW (some (i + 1))).any fun n => n.read.length == 3) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem opensW_can_fail : opensB 8 = true ∧ opensB 9 = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem spotsW_nodup :
    ((spotsWritten.filter fun sp => sp.place.kind == .K2).map (·.place)).Nodup := by
  decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.numsW
#print axioms ProofFile.Honest.K2.Law.answersB
#print axioms ProofFile.Honest.K2.Law.opensB
#print axioms ProofFile.Honest.K2.Law.restToMask
#print axioms ProofFile.Honest.K2.Law.mainToMask
#print axioms ProofFile.Honest.K2.Law.noKept
#print axioms ProofFile.Honest.K2.Law.restFits
#print axioms ProofFile.Honest.K2.Law.moreRows
#print axioms ProofFile.Honest.K2.Law.longFold
#print axioms ProofFile.Honest.K2.Law.fitsNoRide
#print axioms ProofFile.Honest.K2.Law.servesW
#print axioms ProofFile.Honest.K2.Law.servesW_can_fail
#print axioms ProofFile.Honest.K2.Law.roomyW
#print axioms ProofFile.Honest.K2.Law.roomyW_can_fail
#print axioms ProofFile.Honest.K2.Law.fitsW
#print axioms ProofFile.Honest.K2.Law.fitsW_can_fail
#print axioms ProofFile.Honest.K2.Law.answersW
#print axioms ProofFile.Honest.K2.Law.answersW_can_fail
#print axioms ProofFile.Honest.K2.Law.opensW
#print axioms ProofFile.Honest.K2.Law.opensW_three
#print axioms ProofFile.Honest.K2.Law.opensW_can_fail
#print axioms ProofFile.Honest.K2.Law.spotsW_nodup
