-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/Table.lean: WHICH CLAIMS STAY OPEN ACROSS THE CODE SWITCHES, AS A TEST WITH
CODE ON
THE TABLE OF JOINTS, AND THAT TEST's ACCEPT BY LEAN's KERNEL AT THE TWO WRITTEN LISTS OF SEGMENTS.
Two
definitions, five theorems. A law file: no sub-protocol imports it.

What is said.
  `ridersB links ps k m`: every claim that stays open across sub-protocol number k is of the four
    sorts (`fourSortsB`, Johnson/Desc/Sound/RidersTie.lean), and a part of a segment's relation
    among
    them is a segment's from m on.
  `riders_of_B`: its accept gives the two fields riders and fromM of `K2Owes` (T5.lean).
  `switches n`: the numbers of the code switches' sub-protocols at a list of n + 1 segments whose
  last
    is the output head, each with the number of the segment (or, behind the last, group) that it
    opens.
  `riders_small`, `riders_full`: THE TEST ACCEPTS AT ALL 5 | 25, by `decide`.
  `places_small`, `places_full`: at these numbers stands a place of the kind K2, by `decide`.
  `riders_can_fail`: A NEGATIVE TEST: at the first switch of the small list, asked from segment 2
  on, the
    test refuses (parts of segment 1's relation stay open there).

Limits. The two lists of segments are the written ones (`linksSmall`, `linksFull`,
Johnson/Desc/Sound/AtDriver.lean); that a real plan has them is not said here. No soundness is
claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.RidersTie
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item flatPlacesOf)

/-- Four sorts alone stay open across sub-protocol number k; the parts among them are those of the
segments from m on. -/
def ridersB (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  (ridersL links ps k).all fun i => fourSortsB i && match i with
    | .constr j _ => decide (m ≤ j)
    | _ => true

/-- What the test's accept gives. -/
theorem riders_of_B (links : List ModelPart) (ps : List Place) (k m : ℕ)
    (h : ridersB links ps k m = true) : (ridersL links ps k).all fourSortsB = true ∧
      ∀ j q, Item.constr j q ∈ ridersL links ps k → m ≤ j := by
  have h' := List.all_eq_true.1 h
  refine ⟨List.all_eq_true.2 fun i hi => (Bool.and_eq_true _ _ ▸ h' i hi).1, fun j q hi => ?_⟩
  exact of_decide_eq_true (Bool.and_eq_true _ _ ▸ h' _ hi).2

/-- The code switches' numbers at n + 1 segments, the last the output head; with what each opens. -/
def switches (n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (n - 1)).map fun i => (14 * (i + 1) + 2, i + 1)) ++
    [(14 * n + 3, n), (14 * n + 17, n + 1)]

set_option maxRecDepth 1000000 in
theorem riders_small : (switches 4).all (fun x =>
    ridersB linksSmall (flatPlacesOf linksSmall true) x.1 x.2) = true := by decide

set_option maxRecDepth 1000000 in
theorem places_small : (switches 4).all (fun x =>
    ((flatPlacesOf linksSmall true)[x.1]?).any fun p => p.kind == KindName.K2) = true := by decide

set_option maxRecDepth 1000000 in
theorem riders_can_fail :
    ridersB linksSmall (flatPlacesOf linksSmall true) 16 2 = false := by decide

set_option maxRecDepth 1000000 in
theorem places_full : (switches 24).all (fun x =>
    ((flatPlacesOf linksFull true)[x.1]?).any fun p => p.kind == KindName.K2) = true := by decide

set_option maxRecDepth 1000000 in
theorem riders_full : (switches 24).all (fun x =>
    ridersB linksFull (flatPlacesOf linksFull true) x.1 x.2) = true := by decide +kernel

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.riders_full
#print axioms VerifiableInference.Desc.First.K2Ties.riders_of_B
#print axioms VerifiableInference.Desc.First.K2Ties.riders_small
#print axioms VerifiableInference.Desc.First.K2Ties.places_small
#print axioms VerifiableInference.Desc.First.K2Ties.riders_can_fail
#print axioms VerifiableInference.Desc.First.K2Ties.places_full
