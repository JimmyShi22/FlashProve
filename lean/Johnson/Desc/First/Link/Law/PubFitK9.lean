-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PubFitK9.lean: THE BOOL UNDER WHICH THE PUBLIC ITEMS PASS A LINK's THREE
QUIET SUB-PROTOCOLS OF THE BATCHING KIND AND THE FRAME (`stepB`, PubStep.lean), ALONG THE WRITTEN
LIST OF PLACES, AT A FILLING OF THE TABLE's LIST OF EXTRA PUBLIC TESTS; its yes at the composed
filling (`moreAll`, Johnson/Desc/Sound/MoreAll.lean) and the full list, by the kernel; a negative
test. Definitions, a theorem that draws the fact at a place, and evaluations.

What is said.
  `pubAt9 M links ps k`, `pubFit9 M links ps`: at each place of a batching, of the frame's
    sub-protocol behind it, and of a shutting: every public item that is asked behind is asked in
    front and is «the ledger is well laid» or reads the four readers that these sub-protocols leave;
    but that behind the frame's sub-protocol «the one sum can be taken» comes new. And none of the
    two public items that say something beside their Bool («what the lookup left», in its two forms)
    is open behind; and each that is open behind is «hasRow» or one to which a table
    gives «no sentence is meant» (`First.saysNone`): so that the composed meaning's public sentence
    without a test holds at it over the base of Johnson/Desc/Sound/MgBase.lean. `fit9_at`: **the
    fact at a place, in the very terms of `MgRides.pub`.** `pubFit9_full`: the yes at `moreAll` and
    the full list. `pubAsks9_full`: the test asks something at 75 numbers. `pubFit9_bent`: a
    negative test: with nothing counted as made behind the frame's sub-protocol: no.

Limits. An evaluation on the table and the written list alone: it reads no state of the verifier.
That the written list is the list of the places of the IOP as written in Lean is another file's.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PubStep
import Johnson.Desc.First.Link.Law.LinkPlacesFit
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.AllSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.First (ModelPart Item Pub More flatPlacesOf start openSets stepOpen rowOf
  pubSets pubStep pubRowM pubOfItems)
open VerifiableInference.Desc.Sound (moreAll)

/-- What comes new behind the place: mk: is «the one sum can be taken» counted as made behind the
frame's sub-protocol? (false: for the negative test.) -/
def madeAt (mk : Bool) (links : List ModelPart) (m : ℕ) (p : Place) : List Pub :=
  if mk && p.piece == hearN links m + 2 then [.totalIn m] else []

/-- The item is none of the two that say something beside their Bool; and it is «hasRow», or one to
which a table gives «no sentence is meant» (`First.saysNone`,
Johnson/Desc/First/AllSaid.lean): so the composed meaning's public sentence without a test holds at
it over the base. -/
def notLeft : Pub → Bool
  | .left _ => false
  | .leftOn _ => false
  | .hasRow _ => true
  | q => (First.saysNone q).isSome

/-- **The test at number k of the list.** -/
def pubAt9 (mk : Bool) (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m =>
      if p.piece == hearN links m + 1 || p.piece == hearN links m + 2 ||
          p.piece == hearN links m + 5 then
        stepB (madeAt mk links m p)
          ((pubSets M links ps)[k]?.getD [] ++
            pubOfItems ((openSets links ps (start links))[k]?.getD []))
          (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) ++
            pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p)))
          && (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p)).all notLeft
      else true
    | none => true
  | none => true

/-- **The test along the list.** -/
def pubFit9 (mk : Bool) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all (pubAt9 mk M links ps)

/-- **THE FACT AT A PLACE.** -/
theorem fit9_at (M : More) (links : List ModelPart) (ps : List Place)
    (h : pubFit9 true M links ps = true) (k m i : ℕ) (p : Place) (hp : ps[k]? = some p)
    (hl : p.link = some m) (hpc : p.piece = hearN links m + i) (hi : i = 1 ∨ i = 2 ∨ i = 5) :
    stepB (if i = 2 then [.totalIn m] else [])
      ((pubSets M links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []))
      (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p) ++
        pubOfItems (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links p))) =
      true ∧
    (pubStep ((pubSets M links ps)[k]?.getD []) (pubRowM M links p)).all notLeft = true := by
  unfold pubFit9 at h
  rw [List.all_eq_true] at h
  have h0 := h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  unfold pubAt9 madeAt at h0
  rw [hp] at h0
  rcases hi with rfl | rfl | rfl <;> simpa [hl, hpc] using h0

set_option maxRecDepth 1000000 in
/-- **THE YES AT THE COMPOSED FILLING AND THE FULL LIST.** -/
theorem pubFit9_full : pubFit9 true moreAll fullList (flatPlacesOf fullList true) = true := by
  decide +kernel

/-- The place at number k is one of the three. -/
def pubAsks9 (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p =>
    match p.link with
    | some m => p.piece == hearN links m + 1 || p.piece == hearN links m + 2 ||
        p.piece == hearN links m + 5
    | none => false
  | none => false

set_option maxRecDepth 1000000 in
/-- **THE TEST ASKS SOMETHING AT 75 NUMBERS OF THE FULL LIST.** -/
theorem pubAsks9_full : ((List.range (flatPlacesOf fullList true).length).filter
    (pubAsks9 fullList (flatPlacesOf fullList true))).length = 75 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A NEGATIVE TEST: NOTHING COUNTED AS MADE BEHIND THE FRAME's SUB-PROTOCOL.** -/
theorem pubFit9_bent : pubFit9 false moreAll fullList (flatPlacesOf fullList true) = false := by
  decide +kernel

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.fit9_at
#print axioms VerifiableInference.Desc.LinkJoin.pubFit9_full
#print axioms VerifiableInference.Desc.LinkJoin.pubAsks9_full
#print axioms VerifiableInference.Desc.LinkJoin.pubFit9_bent
