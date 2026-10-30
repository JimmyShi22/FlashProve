-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkPlacesFit.lean: WHAT THE LAWS ON A LINK's LAST BLOCKS (the batching,
the frame's block behind it, the one equation, the shutting) ASK OF THE TABLE OF CONDITIONS AND OF
THE WRITTEN LIST OF PLACES, AS ONE BOOL ALONG THE LIST; its yes at the list of the full size, by the
kernel; a list bent at one place, at which it says no; and the facts drawn from the yes.
Definitions, theorems, three evaluations. The table alone is read: no description, no state of the
verifier, no number of the plan.

What is said.
  `hearN links m`: how many hearing blocks segment m has. `fitAt links ps k`: at number k of the
    list: if the place is one of the four (of a segment m, at piece n + 1, n + 2, n + 3 or n + 5, n
    := `hearN`): the next place is of the same segment, and the table asks the same stand at both;
    at the batching and behind it: the row closes and opens no class of rows and no pin, and a count
    of rows may wait at the next place; at the one equation: the row closes just the total of m and
    opens just the class «equation» of m, that class is not open in front, another class of m is; at
    the shutting: the row is quiet and no count may wait in front. `linkFit links ps`: at every
    number. `fit_batch`, `fit_behind`, `fit_eq`, `fit_shut`: **the facts, from the Bool's yes**, in
    the forms that ShapeRides.lean (`NextIn`), EqHands.lean and the rule for a quiet row take.
    `fullList`, `linkFit_full`: **the yes at 25 segments (twelve pairs of a layers' and an attention
    segment, and the head's).** `asksAt`, `asks_full`: the test asks something at 100 numbers of
    that list, four a segment: so its yes is not empty. `linkFit_bent`: with the places of the first
    segment's batching and of the block behind it changed over: no.

Limits. That the written list is the list of the places of a description's blocks is another file's.
The plan's numbers (where the class «equation» lies; which group; the counts of trees and messages)
are not read here. Nothing on soundness.

-/
import Johnson.Desc.First.BordersKeep
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (ModelPart Item RowClass kindsBeforeBatching flatPlacesOf start rowOf openSets
  quietRow standAt mayWait rowSegs)

/-- How many hearing blocks segment m has. -/
def hearN (links : List ModelPart) (m : Nat) : Nat :=
  (kindsBeforeBatching ((links[m]?).getD .layers) (m == 0)).length

/-- The two places are of one segment, and the table asks one stand at both. -/
def nextB (links : List ModelPart) (p p' : Place) : Bool :=
  decide (standAt links p' = standAt links p) && decide (p'.link = p.link)

/-- **The test at number k of the list.** -/
def fitAt (links : List ModelPart) (ps : List Place) (k : Nat) : Bool :=
  match ps[k]?, ps[k + 1]? with
  | some p, some p' =>
    match p.link with
    | some m =>
      let n := hearN links m
      let O := (openSets links ps (start links))[k]?.getD []
      if p.piece == n + 1 || p.piece == n + 2 then
        nextB links p p' && quietRow (rowOf links p) && mayWait links p'
      else if p.piece == n + 3 then
        nextB links p p' && decide ((rowOf links p).ins = [.total m]) &&
          decide ((rowOf links p).outs = [.row m .equation]) &&
          !O.contains (.row m .equation) && (rowSegs O).contains m
      else if p.piece == n + 5 then
        nextB links p p' && quietRow (rowOf links p) && !mayWait links p
      else true
    | none => true
  | _, _ => true

/-- **The test along the list.** -/
def linkFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (fitAt links ps)

theorem fitAt_of (links : List ModelPart) (ps : List Place) (h : linkFit links ps = true) (k : Nat)
    (p : Place) (hp : ps[k]? = some p) : fitAt links ps k = true := by
  unfold linkFit at h
  rw [List.all_eq_true] at h
  exact h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)

theorem nextB_gives {links : List ModelPart} {p p' : Place} (h : nextB links p p' = true) :
    standAt links p' = standAt links p ∧ p'.link = p.link := by
  unfold nextB at h
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨of_decide_eq_true a, of_decide_eq_true b⟩

/-- **At the batching.** -/
theorem fit_batch (links : List ModelPart) (ps : List Place) (h : linkFit links ps = true) (k m : Nat)
    (p p' : Place) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 1) :
    (standAt links p' = standAt links p ∧ p'.link = p.link) ∧
      quietRow (rowOf links p) = true ∧ mayWait links p' = true := by
  have h0 := fitAt_of links ps h k p hp
  unfold fitAt at h0
  rw [hp, hp'] at h0
  simp only [hl, hpc, beq_self_eq_true, Bool.true_or, if_true, Bool.and_eq_true] at h0
  exact ⟨nextB_gives h0.1.1, h0.1.2, h0.2⟩

/-- **At the frame's block behind the batching.** -/
theorem fit_behind (links : List ModelPart) (ps : List Place) (h : linkFit links ps = true) (k m : Nat)
    (p p' : Place) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 2) :
    (standAt links p' = standAt links p ∧ p'.link = p.link) ∧
      quietRow (rowOf links p) = true ∧ mayWait links p' = true := by
  have h0 := fitAt_of links ps h k p hp
  unfold fitAt at h0
  rw [hp, hp'] at h0
  simp only [hl, hpc, beq_self_eq_true, Bool.or_true, if_true, Bool.and_eq_true] at h0
  exact ⟨nextB_gives h0.1.1, h0.1.2, h0.2⟩

/-- **At the one equation.** -/
theorem fit_eq (links : List ModelPart) (ps : List Place) (h : linkFit links ps = true) (k m : Nat)
    (p p' : Place) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3) :
    (standAt links p' = standAt links p ∧ p'.link = p.link) ∧
      (rowOf links p).ins = [.total m] ∧ (rowOf links p).outs = [.row m .equation] ∧
      Item.row m .equation ∉ (openSets links ps (start links))[k]?.getD [] ∧
      m ∈ rowSegs ((openSets links ps (start links))[k]?.getD []) := by
  have h0 := fitAt_of links ps h k p hp
  unfold fitAt at h0
  rw [hp, hp'] at h0
  have e1 : (hearN links m + 3 == hearN links m + 1) = false := by simp
  have e2 : (hearN links m + 3 == hearN links m + 2) = false := by simp
  simp only [hl, hpc, e1, e2, Bool.or_false, Bool.false_eq_true, if_false, beq_self_eq_true,
    if_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h0
  exact ⟨nextB_gives h0.1.1.1.1, h0.1.1.1.2, h0.1.1.2, h0.1.2, h0.2⟩

/-- **At the shutting.** -/
theorem fit_shut (links : List ModelPart) (ps : List Place) (h : linkFit links ps = true) (k m : Nat)
    (p p' : Place) (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 5) :
    (standAt links p' = standAt links p ∧ p'.link = p.link) ∧
      quietRow (rowOf links p) = true ∧ mayWait links p = false := by
  have h0 := fitAt_of links ps h k p hp
  unfold fitAt at h0
  rw [hp, hp'] at h0
  have e1 : (hearN links m + 5 == hearN links m + 1) = false := by simp
  have e2 : (hearN links m + 5 == hearN links m + 2) = false := by simp
  have e3 : (hearN links m + 5 == hearN links m + 3) = false := by simp
  simp only [hl, hpc, e1, e2, e3, Bool.or_false, Bool.false_eq_true, if_false, beq_self_eq_true,
    if_true, Bool.and_eq_true, Bool.not_eq_true'] at h0
  exact ⟨nextB_gives h0.1.1, h0.1.2, h0.2⟩

/-- The segments' sorts at the full size: twelve pairs, and the head's. -/
def fullList : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE FULL SIZE.** -/
theorem linkFit_full : linkFit fullList (flatPlacesOf fullList true) = true := by decide +kernel

/-- The place at number k is one of the four, and a place stands behind it: there the test asks
something. -/
def asksAt (links : List ModelPart) (ps : List Place) (k : Nat) : Bool :=
  match ps[k]?, ps[k + 1]? with
  | some p, some _ =>
    match p.link with
    | some m =>
      let n := hearN links m
      p.piece == n + 1 || p.piece == n + 2 || p.piece == n + 3 || p.piece == n + 5
    | none => false
  | _, _ => false

set_option maxRecDepth 1000000 in
/-- **THE TEST ASKS SOMETHING AT 100 NUMBERS OF THE FULL LIST: four a segment.** -/
theorem asks_full : ((List.range (flatPlacesOf fullList true).length).filter
    (asksAt fullList (flatPlacesOf fullList true))).length = 100 := by decide +kernel

/-- The written list with the members at numbers i and i + 1 changed over. -/
def swapAt (ps : List Place) (i : Nat) : List Place :=
  match ps[i]?, ps[i + 1]? with
  | some a, some b => (ps.set i b).set (i + 1) a
  | _, _ => ps

set_option maxRecDepth 1000000 in
/-- **A CONTROL: THE FIRST SEGMENT's BATCHING AND THE BLOCK BEHIND IT CHANGED OVER: NO.** -/
theorem linkFit_bent : linkFit fullList (swapAt (flatPlacesOf fullList true) 9) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fit_batch
#print axioms VerifiableInference.Desc.LinkJoin.fit_behind
#print axioms VerifiableInference.Desc.LinkJoin.fit_eq
#print axioms VerifiableInference.Desc.LinkJoin.fit_shut
#print axioms VerifiableInference.Desc.LinkJoin.linkFit_full
#print axioms VerifiableInference.Desc.LinkJoin.linkFit_bent
#print axioms VerifiableInference.Desc.LinkJoin.asks_full
