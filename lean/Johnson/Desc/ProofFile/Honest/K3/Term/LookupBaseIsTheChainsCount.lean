-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, UNDER THE HEAD `P5J.AtMgA`: no prover and no filling is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupBaseIsTheChainsCount.lean: the kind "lookup" (K3): the
number of rounds in front that a site bears is the first chain's own count, at every site, under the
library's hypothesis at the full size (`P5J.AtMgA`, "the head") and ONE CLOSED TEST ON TWO WRITTEN
LISTS, which stays a hypothesis in this file. Three definitions; theorems.

Terms. Honest/K3/GLOSSARY.md ("site", "description", "table of places").

Why. A site's number (`s.at_.base`) is added up off the chain's table of places (`baseIn`,
Honest/K3/Lot.lean). The chain's count (`roundsInFront`, Honest/ForKinds.lean) is added up off the
description's sub-protocols. The first clause of `siteFits` (Honest/K3/Law/SiteFits.lean) asks that
the two are one number.

What is defined.
  `startInCutRows rows a`: the rounds of the rows in front of the first row at the place a, at a
    list of rows of the form that `cutOf` (Johnson/Desc/Ok/PlanWritten/CutTest.lean) makes.
  `lookupBaseTestAt rows ps l d`: at link l and sort d: the rows have a row at `IM.k3Place l d`, and
    its start in the rows is `baseIn ps` of that place.
  `lookupBaseTest rows ps`: the same at each link below 25 and both sorts.

What is shown.
  `roundsInFrontIsTheStartInTheCut`: at every list of sub-protocols and every place:
    `roundsInFront bs a = startInCutRows (cutOf bs) a`. No hypothesis.
  `siteBaseIsTheTablesCount`: a site that `siteAt` makes at an address bears `baseIn` of the
    address's place.
  `lookupBaseIsTheTablesCountAtTheHead`: under the head: a site's number is `baseIn spotsWritten`
    of `IM.k3Place` at the site's link and sort.
  `lookupBaseIsTheChainsCountOfWritten`: under the head (`h`) and the closed test at the two written
    lists (`written`): at every site of `lookSites Zp`:
    `roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base`.
  `lookupBaseIsTheRoundsToTheBorderOfWritten`: under the same two: the form that a thread's seat
    asks (`K3PlaysAt.base`, Honest/K3/Law/Thread/PlaysAnyState.lean, at front 0):
    `s.at_.base = roundsTo cF.blocksInOrder (borderOf s.link s.digits)`.

Hypotheses that remain. `h`: `P5J.AtMgA`. `written`: a closed test:
`lookupBaseTest cutFirstFull spotsWritten = true`; Honest/K3/Term/LookupBaseWritten.lean has it by
Lean's kernel.

Limits. The full size alone: that limit comes with the head. On public data alone. No instance of
the head is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteFits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw
import Johnson.AtFull.Shape.SitesAtHead
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Place Oracle)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.AtFull.Desc (spotsWritten)
open ProofFile.Honest.K3.Law (site_facts)
open ProofFile.Honest.K3.Law.AtThr (link_lt_head site_place_head places_head ps_nodup borderNo_of_nodup)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 The chain's count is a function of the chain's cut -/

/-- **The rounds of the rows in front of the first row at the place a**; nothing if no row stands at
a. A row is what `cutOf` makes of a sub-protocol: its second field is the place, its third the
number of rounds. -/
def startInCutRows :
    List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)) → Place →
      Option Nat
  | [], _ => none
  | row :: rows, a =>
    if row.2.1 == a then some 0 else (startInCutRows rows a).map (· + row.2.2.1)

/-- **The chain's count in front of a place reads the chain's cut alone.** -/
theorem roundsInFrontIsTheStartInTheCut {S Cl : Type} (bs : List (Block S Cl)) (a : Place) :
    roundsInFront bs a = startInCutRows (cutOf bs) a := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (if b.place == a then some 0 else (roundsInFront bs a).map (· + b.rounds.length)) =
      (if b.place == a then some 0 else (startInCutRows (cutOf bs) a).map (· + b.rounds.length))
    rw [ih]

/-! ## 2 The site's number is the table's count -/

/-- A site that is made at an address bears the table's count in front of the address's place. -/
theorem siteBaseIsTheTablesCount (X : OnBytes.Model.Verify.Public) (ps : List ProofFile.Spot)
    (address : Nat × Bool × Place) (s : Site) (made : siteAt X ps address = some s) :
    baseIn ps address.2.2 = some s.at_.base := by
  unfold siteAt at made
  obtain ⟨p, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨shape, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨n, count, made⟩ := Option.bind_eq_some_iff.1 made
  dsimp only at made
  split at made
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 made
    exact count
  · obtain rfl := Option.some.inj made
    exact count

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head a site's number is the count of the written list of places in front of
`IM.k3Place` at the site's link and sort. -/
theorem lookupBaseIsTheTablesCountAtTheHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) :
    baseIn spotsWritten (IM.k3Place s.link s.digits) = some s.at_.base := by
  have place := site_place_head h s hs
  unfold lookSites at hs
  obtain ⟨address, _, made⟩ := List.mem_filterMap.1 hs
  have count := siteBaseIsTheTablesCount _ _ address s made
  obtain ⟨-, -, -, -, atAddress, -⟩ := site_facts _ _ _ s made
  rw [Johnson.AtFull.Shape.spots_at h, ← atAddress, place] at count
  exact count

/-! ## 3 The closed test, and the law under it -/

/-- At link l and sort d: the rows have a row at the lookup's place, and its start in the rows is
the count of the list of places in front of that place. -/
def lookupBaseTestAt
    (rows : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)))
    (ps : List ProofFile.Spot) (l : Nat) (d : Bool) : Bool :=
  (startInCutRows rows (IM.k3Place l d)).isSome &&
    startInCutRows rows (IM.k3Place l d) == baseIn ps (IM.k3Place l d)

/-- **The closed test**: the same at each link below 25 and both sorts. -/
def lookupBaseTest
    (rows : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)))
    (ps : List ProofFile.Spot) : Bool :=
  (List.range 25).all fun l => [false, true].all fun d => lookupBaseTestAt rows ps l d

/-- **AT EVERY SITE THE NUMBER OF ROUNDS IN FRONT THAT THE SITE BEARS IS THE CHAIN's OWN COUNT.**
Conditional on the head and on the closed test at the two written lists. -/
theorem lookupBaseIsTheChainsCountOfWritten
    (written : lookupBaseTest cutFirstFull spotsWritten = true)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    roundsInFront cF.blocksInOrder s.at_.place = some s.at_.base := by
  have below := link_lt_head h s hs
  have cut : cutOf cF.blocksInOrder = cutFirstFull := h.toAtMg.cut_written
  have atLink := List.all_eq_true.1 written s.link (List.mem_range.2 below)
  have atSort := List.all_eq_true.1 atLink s.digits (by cases s.digits <;> simp)
  unfold lookupBaseTestAt at atSort
  rw [Bool.and_eq_true] at atSort
  rw [roundsInFrontIsTheStartInTheCut, cut, site_place_head h s hs, eq_of_beq atSort.2]
  exact lookupBaseIsTheTablesCountAtTheHead h s hs

/-- **The same in the form that a thread's seat asks**: the site's number is the count of the rounds
of the sub-protocols in front of the lookup's border. Conditional on the head and on the closed test
at the two written lists. -/
theorem lookupBaseIsTheRoundsToTheBorderOfWritten
    (written : lookupBaseTest cutFirstFull spotsWritten = true)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    s.at_.base = roundsTo cF.blocksInOrder (borderOf s.link s.digits) := by
  have below := link_lt_head h s hs
  have atBorder : (cF.blocksInOrder.map (·.place))[borderOf s.link s.digits]? =
      some (IM.k3Place s.link s.digits) := by
    rw [places_head h]
    exact places_are_k3 below s.digits
  rw [List.getElem?_map] at atBorder
  obtain ⟨member, stands, place⟩ := Option.map_eq_some_iff.1 atBorder
  have nodup : (cF.blocksInOrder.map (·.place)).Nodup := by
    rw [places_head h]
    exact ps_nodup
  have number := borderNo_of_nodup cF.blocksInOrder _ member s.at_.place stands
    (place.trans (site_place_head h s hs).symm) nodup
  rw [← number]
  exact (roundsTo_inFront cF.blocksInOrder _ _
    (lookupBaseIsTheChainsCountOfWritten written h s hs)).symm

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupBaseIsTheRoundsToTheBorderOfWritten
#print axioms ProofFile.Honest.K3.Term.roundsInFrontIsTheStartInTheCut
#print axioms ProofFile.Honest.K3.Term.siteBaseIsTheTablesCount
#print axioms ProofFile.Honest.K3.Term.lookupBaseIsTheTablesCountAtTheHead
#print axioms ProofFile.Honest.K3.Term.lookupBaseIsTheChainsCountOfWritten
