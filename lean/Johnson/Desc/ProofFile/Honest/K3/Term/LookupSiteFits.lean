-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT NO FILLING: ON PUBLIC DATA ALONE, UNDER THE HEAD `P5J.AtMgA`: no prover and no filling is read.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSiteFits.lean: the kind "lookup" (K3): the public test
`siteFits` (Honest/K3/Law/SiteFits.lean) accepts at every site, under the library's hypothesis at
the full size (`P5J.AtMgA`, "the head") and TWO CLOSED TESTS ON WRITTEN LISTS, which stay hypotheses
in this file. Two definitions; theorems.

Terms. Honest/K3/GLOSSARY.md ("site", "description", "table of places").

What `siteFits` asks. (i) The site's number of rounds in front is the chain's own count:
Honest/K3/Term/LookupBaseIsTheChainsCount.lean. (ii) At a site that names a round r (the round that
samples the matrix of the link's smallness test): r stands in front of the lookup, and just one
sub-protocol of the link stands behind r rounds and has one round, named "RNG", which samples matrix
entries. This file is on (ii), and joins the two.

What is defined.
  `lookupDrawTestAt rows ps entries l`: at link l, with r the round that `rngIn ps l` returns and n
    the count `baseIn ps` in front of the link's lookup on the digits: r < n; just one row of the
    link starts at r and has one round; entry number r is named "RNG" and has trits.
  `lookupDrawTest rows ps entries`: the same at each link below 25.

What is shown.
  `roundAtTheStartOfABlock`: in every list of sub-protocols: the one round of a sub-protocol with
    one round is the round, of all the list's rounds in a row, whose number is the count of the
    rounds in front of that sub-protocol.
  `memberOfAny`: a helper on optional values.
  `siteDrawIsTheTables`: a site that `siteAt` makes and that names a round is on the digits, and the
    round is what `rngIn` returns at its link.
  `siteOnTheDigitsNamesARound`: at every public part: a site on the digits names a round: so the
    second clause of `siteFits` is asked there.
  `firstChainsEntriesAreWritten`: under the head the entries of the first chain's rounds, in a row,
    are the written entries `P5T.esFull.1`.
  `lookupSiteFitsOfWritten`: under the head (`h`) and the two closed tests (`baseWritten`,
    `drawWritten`): at every site of `lookSites Zp`: `siteFits cF.blocksInOrder s = true`.

Hypotheses that remain. `h`: `P5J.AtMgA`. `baseWritten`, `drawWritten`: closed tests at written
lists; Honest/K3/Term/LookupBaseWritten.lean and LookupDrawWritten.lean have them by Lean's kernel.

Limits. The full size alone: that limit comes with the head. On public data alone. Which kind's
sub-protocol has the round named "RNG" is not said: `siteFits` does not ask it. No instance of the
head is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupBaseIsTheChainsCount
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Place Oracle)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.AtFull.Desc (spotsWritten)
open ProofFile.Honest.K3.Law (siteFits site_facts)
open ProofFile.Honest.K3.Law.AtThr (link_lt_head places_head ps_nodup borderNo_of_nodup)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 General laws -/

/-- **The one round of a sub-protocol with one round**, among all the list's rounds in a row, has
the number of the rounds in front of that sub-protocol. -/
theorem roundAtTheStartOfABlock {S Cl : Type} : ∀ (bs : List (Block S Cl)) (j : Nat)
    (b : Block S Cl) (d : Fmt.DeclaredRound), bs[j]? = some b → b.rounds = [d] →
    (bs.flatMap (·.rounds))[roundsTo bs j]? = some d
  | [], _, _, _, h, _ => by simp at h
  | c :: bs, 0, b, d, h, one => by
    have e : c = b := by simpa using h
    subst e
    simp [roundsTo, declsTo, one]
  | c :: bs, j + 1, b, d, h, one => by
    have ih := roundAtTheStartOfABlock bs j b d (by simpa using h) one
    have count : roundsTo (c :: bs) (j + 1) = c.rounds.length + roundsTo bs j := by
      simp [roundsTo, declsTo]
    rw [count, List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
    exact ih

/-- Where a test accepts at an optional value, there is a value, and the test accepts it. -/
theorem memberOfAny {α : Type} (o : Option α) (p : α → Bool) (h : o.any p = true) :
    ∃ a, o = some a ∧ p a = true := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, rfl, by simpa using h⟩

/-- A site that is made at an address and names a round is on the digits, and the round is the
table's at the address's link. -/
theorem siteDrawIsTheTables (X : OnBytes.Model.Verify.Public) (ps : List ProofFile.Spot)
    (address : Nat × Bool × Place) (s : Site) (made : siteAt X ps address = some s) (round : Nat)
    (named : s.rng = some round) : address.2.1 = true ∧ rngIn ps address.1 = some round := by
  unfold siteAt at made
  obtain ⟨p, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨shape, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨n, _, made⟩ := Option.bind_eq_some_iff.1 made
  dsimp only at made
  split at made
  · rename_i digits
    obtain ⟨round', table, rfl⟩ := Option.map_eq_some_iff.1 made
    obtain rfl : round' = round := Option.some.inj named
    exact ⟨digits, table⟩
  · obtain rfl := Option.some.inj made
    cases named

/-- **A site on the digits names a round**, at every public part. -/
theorem siteOnTheDigitsNamesARound (Zq : Pub) (s : Site) (hs : s ∈ lookSites Zq)
    (digits : s.digits = true) : s.rng.isSome = true := by
  unfold lookSites at hs
  obtain ⟨address, _, made⟩ := List.mem_filterMap.1 hs
  obtain ⟨-, -, -, sort, -⟩ := site_facts _ _ _ s made
  unfold siteAt at made
  obtain ⟨p, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨shape, _, made⟩ := Option.bind_eq_some_iff.1 made
  obtain ⟨n, _, made⟩ := Option.bind_eq_some_iff.1 made
  dsimp only at made
  split at made
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 made
    rfl
  · rename_i calls
    exact absurd (sort.symm.trans digits) calls

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 2 Under the head -/

/-- **Under the head the entries of the first chain's rounds are the written entries.** -/
theorem firstChainsEntriesAreWritten (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.flatMap (·.rounds)).map (·.entry) = P5T.esFull.1 := by
  have written := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
    (LPFD.asks_written h.laid.asks)).1
  exact (Johnson.G.OfPlan.writtenOf_entries written).1.symm

/-- Under the head a site that names a round is on the digits, and the round is what the written
list of places gives at the site's link. -/
theorem lookupDrawIsTheTablesAtTheHead (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (round : Nat) (named : s.rng = some round) :
    s.digits = true ∧ rngIn spotsWritten s.link = some round := by
  unfold lookSites at hs
  obtain ⟨address, _, made⟩ := List.mem_filterMap.1 hs
  obtain ⟨digits, table⟩ := siteDrawIsTheTables _ _ address s made round named
  obtain ⟨-, -, link, sort, -⟩ := site_facts _ _ _ s made
  rw [Johnson.AtFull.Shape.spots_at h, ← link] at table
  exact ⟨sort.trans digits, table⟩

/-! ## 3 The closed test, and the law under it -/

/-- At link l: the table names a round in front of the link's lookup on the digits; just one row of
the link starts there and has one round; the entry of that number is named "RNG" and has trits. -/
def lookupDrawTestAt
    (rows : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)))
    (ps : List ProofFile.Spot) (entries : List Fmt.Entry) (l : Nat) : Bool :=
  match rngIn ps l, baseIn ps (IM.k3Place l true) with
  | some round, some count =>
    decide (round < count) &&
      (rows.filter fun row => row.2.1.link == some l &&
        startInCutRows rows row.2.1 == some round && row.2.2.1 == 1).length == 1 &&
      (entries[round]?).any fun e => e.name == "RNG" && e.trits != 0
  | _, _ => false

/-- **The closed test**: the same at each link below 25. -/
def lookupDrawTest
    (rows : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat)))
    (ps : List ProofFile.Spot) (entries : List Fmt.Entry) : Bool :=
  (List.range 25).all fun l => lookupDrawTestAt rows ps entries l

/-- **THE PUBLIC TEST `siteFits` ACCEPTS AT EVERY SITE.** Conditional on the head and on the two
closed tests at the written lists. -/
theorem lookupSiteFitsOfWritten (baseWritten : lookupBaseTest cutFirstFull spotsWritten = true)
    (drawWritten : lookupDrawTest cutFirstFull spotsWritten P5T.esFull.1 = true)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    siteFits cF.blocksInOrder s = true := by
  have base := lookupBaseIsTheChainsCountOfWritten baseWritten h s hs
  unfold siteFits
  rw [base, beq_self_eq_true, Bool.true_and]
  cases named : s.rng with
  | none => rfl
  | some round =>
    obtain ⟨digits, table⟩ := lookupDrawIsTheTablesAtTheHead h s hs round named
    have count := lookupBaseIsTheTablesCountAtTheHead h s hs
    rw [digits] at count
    have atLink := List.all_eq_true.1 drawWritten s.link
      (List.mem_range.2 (link_lt_head h s hs))
    unfold lookupDrawTestAt at atLink
    rw [table, count] at atLink
    simp only [Bool.and_eq_true, decide_eq_true_eq] at atLink
    obtain ⟨⟨inFront, once⟩, entry⟩ := atLink
    obtain ⟨e, entryAt, isDraw⟩ := memberOfAny _ _ entry
    have cut : cutOf cF.blocksInOrder = cutFirstFull := h.toAtMg.cut_written
    have nodup : (cF.blocksInOrder.map (·.place)).Nodup := by
      rw [places_head h]
      exact ps_nodup
    -- sub-protocol by sub-protocol the chain's test is the test on the cut's row
    have same : ∀ c ∈ cF.blocksInOrder,
        (c.place.link == some s.link && roundsInFront cF.blocksInOrder c.place == some round &&
          c.rounds.map (fun d => (d.entry.name, d.entry.trits != 0)) == [("RNG", true)]) =
        (c.place.link == some s.link && startInCutRows cutFirstFull c.place == some round &&
          c.rounds.length == 1) := by
      intro c hc
      rw [roundsInFrontIsTheStartInTheCut, cut]
      cases front : (c.place.link == some s.link &&
          startInCutRows cutFirstFull c.place == some round) with
      | false => rfl
      | true =>
        rw [Bool.true_and, Bool.true_and, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
        constructor
        · intro names
          have lengths := congrArg List.length names
          rwa [List.length_map] at lengths
        · intro one
          obtain ⟨d, rounds⟩ := List.length_eq_one_iff.1 one
          obtain ⟨j, atJ⟩ := List.getElem?_of_mem hc
          rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at front
          have start : roundsInFront cF.blocksInOrder c.place = some round := by
            rw [roundsInFrontIsTheStartInTheCut, cut]
            exact front.2
          have number : roundsTo cF.blocksInOrder j = round := by
            rw [← borderNo_of_nodup cF.blocksInOrder j c c.place atJ rfl nodup]
            exact roundsTo_inFront cF.blocksInOrder c.place round start
          have found := roundAtTheStartOfABlock cF.blocksInOrder j c d atJ rounds
          rw [number] at found
          have foundEntry : P5T.esFull.1[round]? = some d.entry := by
            rw [← firstChainsEntriesAreWritten h, List.getElem?_map, found]
            rfl
          obtain rfl : e = d.entry := Option.some.inj (entryAt.symm.trans foundEntry)
          rw [Bool.and_eq_true, beq_iff_eq] at isDraw
          rw [rounds, List.map_cons, List.map_nil, isDraw.1, isDraw.2]
    show (decide (round < s.at_.base) && _) = true
    rw [decide_eq_true inFront, Bool.true_and, List.filter_congr same]
    have rows : (cF.blocksInOrder.filter fun c => c.place.link == some s.link &&
        startInCutRows cutFirstFull c.place == some round && c.rounds.length == 1).length =
        ((cutOf cF.blocksInOrder).filter fun row => row.2.1.link == some s.link &&
          startInCutRows cutFirstFull row.2.1 == some round && row.2.2.1 == 1).length := by
      unfold cutOf
      rw [List.filter_map, List.length_map]
      rfl
    rw [rows, cut]
    exact once

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.roundAtTheStartOfABlock
#print axioms ProofFile.Honest.K3.Term.memberOfAny
#print axioms ProofFile.Honest.K3.Term.siteDrawIsTheTables
#print axioms ProofFile.Honest.K3.Term.siteOnTheDigitsNamesARound
#print axioms ProofFile.Honest.K3.Term.firstChainsEntriesAreWritten
#print axioms ProofFile.Honest.K3.Term.lookupDrawIsTheTablesAtTheHead
#print axioms ProofFile.Honest.K3.Term.lookupSiteFitsOfWritten
