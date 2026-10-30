-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/HB/LLHARD/PlanOk3AtHead.lean: four of the tests on the numbers that the last chain's
table asks (the fields elderBelow, sampled, wIn and iIn of the structure PlanOk₃, which lies outside
this library), as theorems under the structure of conditions `P5J.AtMg` (Johnson/P5J/AtMg.lean), at
the numbers `P5J.At.N Zp cF`.
(Where this and lean/THEOREM.md differ, the page holds.) Theorems with their proofs.

Why. The last chain's table takes these four as premises: the seats of the index masks' message and
of W lie in trees of the first chain; every sampled seat that is open at the first table's last
border lies in a tree below the last chain's first; and these two seats are among them.

WHAT THE FOUR ARE WORTH, so that nobody counts four facts. wIn and iIn say nothing on the numbers:
they are facts on the table of open items alone. The sampled seats that are open at the last border
are these two and no other, so sampled at lo = 83 + 11 says "both trees are below 94", which is
weaker than elderBelow. The whole content: 1 < 83 and 82 < 83 at the written values; the two
comparisons that tie the public files to these values; and one closed evaluation of the table.

How. One fact and calls. THE FACT: the core of the table's numbers is the written one
(`seats_in_scope`, Johnson/P5T/PlanSeatsTie.lean), so both seats' trees are below 83
(`hI_hV_in_scope`, IdxBelowWritten.lean). The four premises of both are had from the structure: the
scope; the public part (the field pub of `LaidAt`); the comparison of what is made for these files
with the written values, `madePinnedAt` (`pins_of_laid`, Johnson/Goal/Skeleton/PinsOfLaid.lean, out
of the field asks); that the value is laid (`laidPOf_of`). The table's numbers `At.N Zp cF` have the
seats of that core. THE CALLS: the data's numbers of trees are 83 and 11 (`AtMg.trees`,
`AtMg.trees_at`, HeadFacts.lean); the three tests on the last border follow from the two comparisons
at the written list of the segments' sorts (`endTests_full`, Johnson/Desc/K13/Law/EndTests.lean).

Main names:
  `links_are`: the list of sorts at which `endTests_full` stands (`K13.Law.linksFull`) is
    `P5J.fullLinks`: by evaluation. (These are two of the library's three written lists; the third
    is `Sound.linksFull`.)
  `AtMg.seats_are`: the core of the numbers is `P5T.N0Full` (a private lemma); so (At.N Zp cF).index
    = (1, 0) and (At.N Zp cF).w = (82, 0). (Where it finds no such seat the core's maker gives (0,
    0), at which "below 83" would accept idly: under the structure that is not the case.)
  `AtMg.seats_below`: (At.N Zp cF).index.1 < 83 and (At.N Zp cF).w.1 < 83.
  `AtMg.w_not_below_82`: NEGATIVE TEST: W's tree is not below 82: the number 83 is tight.
  `AtMg.elderBelow`, `AtMg.elderBelow_at`: both are below D.t₁; below (D.at frS.P.T.a).t₁.
  `endTests_links`: `endTests_full`'s three at `fullLinks`, at any numbers N and any lo above both
    seats' trees.
  `AtMg.endTests`, `AtMg.endTests_at`: sampled, wIn and iIn, in the fields' own text, at lo := t₁ +
    t₂ of D, and of D.at frS.P.T.a; N₁ := At.N Zp cF; links := `fullLinks`; ps := First.flatPlaces
    true fullLinks true.
The seven under the structure stand at every o.

Limits. A member of `AtMg` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/): where there is none, the seven under it speak of nothing.
THEY OPEN TWO OF THE STRUCTURE's OWN CONDITIONS: the field asks of `LaidAt` holds the tests that
compare what is made for these public files, and the declared rounds, with written values: "below
83" is a fact on the written values, and 83 and 11 are the written lists' numbers; nothing is said
on what the maker returns at the shipped files. `madePinnedAt` comes out of madeRow, one of the five
tests of the field asks that came later. All thirteen have been seen to accept at the release's
three public files, at o := `OnBytes.secondHashFunction` alone, by an evaluation (Lean's evaluator; no theorem);
that evaluation is not called here. (The page of which HeadFacts.lean's Limits tell is older and has
eight.) (The list of these tests, `LPFD.lawsAsk`, has fourteen entries in this library: of the
fourteenth nothing is said here.)
Of the fields of `AtMg` two are spent: scope and laid (of it pub, value, planOk, data and
asks); not the other three. The field elderBelow stands at a letter V, meant ⟨N₁.index, N₁.w, …⟩:
that V's two seats are these is not said here. The structure PlanOk₃ is not imported: that the four
texts here are its fields' texts has been held by a program that compares the texts, at the two
files' sums of the day; not by Lean. The field omega is not here. NEGATIVE TESTS: one here
(`AtMg.w_not_below_82`); at the written values `hV_rejects` (IdxBelowWritten.lean: W's tree is not
below 82) and, outside this file's imports and at the third written list, `hbelow_rejects`
(Johnson/Desc/Sound/ReadsBelowWritten.lean: `sampledBelow` at 82 rejects). The
full size alone.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.HeadFacts
import Johnson.HB.LLHARD.IdxBelowWritten
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Desc.K13.Law.EndTests
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (openSets start sampledIn)
open VerifiableInference.Desc.Sound (sampledBelow)
open OnBytes.Maker (WholeD)

/-- These two of the library's three written lists of the segments' sorts are one list. -/
theorem links_are : VerifiableInference.Desc.K13.Law.linksFull = fullLinks := by decide

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The core of the table's numbers is the written one. (Private: the same statement stands, under
a public name, in another file on this structure.) -/
private theorem AtMg.coreIs (h : AtMg o Z D r Zp Np cF) :
    P5T.numbersOf (P5T.planSeats Zp Zp.D.1) = P5T.N0Full :=
  (P5T.seats_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)).2.2

/-- The two seats, as numbers. -/
theorem AtMg.seats_are (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).index = (1, 0) ∧ (At.N Zp cF).w = (82, 0) := by
  have e1 : (At.N Zp cF).index = P5T.N0Full.index := congrArg (·.index) h.coreIs
  have e2 : (At.N Zp cF).w = P5T.N0Full.w := congrArg (·.w) h.coreIs
  exact ⟨e1.trans (congrArg Prod.fst P5T.N0Full_seats),
    e2.trans (congrArg Prod.snd P5T.N0Full_seats)⟩

/-- NEGATIVE TEST: W's tree is not below 82: the number 83 is tight. -/
theorem AtMg.w_not_below_82 (h : AtMg o Z D r Zp Np cF) : ¬ (At.N Zp cF).w.1 < 82 := by
  have e2 : (At.N Zp cF).w = P5T.N0Full.w := congrArg (·.w) h.coreIs
  rw [e2]
  exact VerifiableInference.Desc.K13.Law.hV_rejects

/-- **The seats of the index masks' message and of W lie in trees below 83.** -/
theorem AtMg.seats_below (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).index.1 < 83 ∧ (At.N Zp cF).w.1 < 83 :=
  VerifiableInference.Desc.K13.Law.hI_hV_in_scope h.scope h.laid.pub
    (pins_of_laid h.scope h.laid).1
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- The field elderBelow's text, with V's two seats unfolded, at the structure's data. -/
theorem AtMg.elderBelow (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).index.1 < D.t₁ ∧ (At.N Zp cF).w.1 < D.t₁ := by
  rw [h.trees.1]
  exact h.seats_below

/-- **The field elderBelow's text, with V's two seats unfolded**, at the data with the stored
table's depth overwritten. -/
theorem AtMg.elderBelow_at (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).index.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁ ∧
      (At.N Zp cF).w.1 < (D.at OnBytes.Slice.frS.P.T.a).t₁ := by
  rw [h.trees_at.1]
  exact h.seats_below

/-- The three tests on the first table's last border, at any number lo above both seats' trees. -/
theorem endTests_links (lo : ℕ) (N : VerifiableInference.Desc.First.Numbers) (hI : N.index.1 < lo)
    (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets fullLinks (VerifiableInference.Desc.First.flatPlaces true fullLinks
        true) (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) = true ∧
      N.w ∈ sampledIn N ((openSets fullLinks (VerifiableInference.Desc.First.flatPlaces true
        fullLinks true) (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) ∧
      N.index ∈ sampledIn N ((openSets fullLinks (VerifiableInference.Desc.First.flatPlaces true
        fullLinks true) (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) := by
  rw [← links_are]
  exact VerifiableInference.Desc.K13.Law.endTests_full lo N hI hV

/-- The fields sampled, wIn and iIn at the structure's data. -/
theorem AtMg.endTests (h : AtMg o Z D r Zp Np cF) :
    sampledBelow (D.t₁ + D.t₂) (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) :=
  endTests_links _ _ (Nat.lt_of_lt_of_le h.elderBelow.1 (Nat.le_add_right _ _))
    (Nat.lt_of_lt_of_le h.elderBelow.2 (Nat.le_add_right _ _))

/-- **The fields sampled, wIn and iIn** at the data with the stored table's depth overwritten. -/
theorem AtMg.endTests_at (h : AtMg o Z D r Zp Np cF) :
    sampledBelow ((D.at OnBytes.Slice.frS.P.T.a).t₁ + (D.at OnBytes.Slice.frS.P.T.a).t₂)
        (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) = true ∧
      (At.N Zp cF).w ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) ∧
      (At.N Zp cF).index ∈ sampledIn (At.N Zp cF) ((openSets fullLinks
        (VerifiableInference.Desc.First.flatPlaces true fullLinks true)
        (start fullLinks))[(VerifiableInference.Desc.First.flatPlaces true fullLinks
        true).length]?.getD []) :=
  endTests_links _ _ (Nat.lt_of_lt_of_le h.elderBelow_at.1 (Nat.le_add_right _ _))
    (Nat.lt_of_lt_of_le h.elderBelow_at.2 (Nat.le_add_right _ _))

end P5J

#print axioms P5J.links_are
#print axioms P5J.AtMg.coreIs
#print axioms P5J.AtMg.seats_are
#print axioms P5J.AtMg.w_not_below_82
#print axioms P5J.AtMg.seats_below
#print axioms P5J.AtMg.elderBelow
#print axioms P5J.AtMg.elderBelow_at
#print axioms P5J.endTests_links
#print axioms P5J.AtMg.endTests
#print axioms P5J.AtMg.endTests_at
