-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Open.lean: which public items are open in front of the fifty blocks of the
kind "lookup" (K3), at the table of joints' promise with what the composed meaning adds (`mgMore`,
Johnson/Desc/Sound/MgAllAt.lean), at the full size's list of segments. A closed fact on the table.
OVER THE COMPOSED MEANING, whose door is small:
the name "frame.liveIs" is struck there, so
it is not wanted; `live_not_open` says that it is open at none of the fifty borders.

What it is for. The premises of the kind's laws at a place ask that certain public items stand in
the open set at the border in front of the place's block (`pubSets`,
Johnson/Desc/First/Borders.lean). With `mgAll_more_closed` (MgAllAt.lean) the composed meaning's own
filling of the promise's table is the closed term `mgMore` wherever the meaning beneath adds
nothing: so these premises are closed facts.

Which terms. The list of segments is `linksFull` of Johnson/Desc/Sound/AtDriver.lean: twelve times
layers and attention, then the head. The places are `First.flatPlacesOf linksFull true`. The index
of a lookup in its segment and its piece are written out here as `ixOf` and `pieceOf`: 1 for the
lookup on the calls and 6 for that on the digits, one more at the head's segment 24; the piece is
one more. That they are `IM.k3Ix` and the piece of `IM.k3Place` (Johnson/IMR/K3Seat.lean) is not
shown here: that file is not imported; `places_are_k3` holds them against the list of places itself:
at each of the fifty numbers stands the place of the kind K3 with that segment and piece.

Definitions.
  `ixOf l digits`, `pieceOf l digits`, `borderOf l digits` := 14 l + `ixOf l digits` + 2.
  `openAt k`: the open public set at border k.
  `wantedAt l`: the pairs (border, item) of segment l: in front of the calls' lookup: lookIn,
    freeAbove, linkFresh; in front of the digits' lookup: ledger and these three; at segment 24,
    in front of the calls' lookup, tokenSmall besides.
  `k3OpenB`: every wanted item of the segments 0 to 24 is in its open set. `k3PlacesB`: the fifty
    places.
Statements.
  `k3OpenB_full`, `k3PlacesB_full`: the two tests say yes.
  `k3_open_calls`, `k3_open_digits`, `k3_open_token`: read back: for every l < 25 the three and
    the four memberships, and the one at the head.
  `places_are_k3`: for every l < 25 and either lookup: the place at that border's number.
  `not_open`: the test can say no: tokenSmall is not open in front of the calls' lookup of segment
    0.
By evaluations in Lean's kernel (`decide +kernel`): `k3OpenB_full`, `k3PlacesB_full`, `not_open`,
`live_not_open`.

What of OnBytes/Model/ is used: nothing by name.

Limits. A fact on the table's own text and on `mgMore`: that an item is open says nothing on whether
it holds of any state of the chain. The full size's list of segments alone. Nothing on soundness.

-/
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound.MgAt
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.First.Look (liveItem)

/-- The index of the lookup on the calls, or on the digits, in segment l. -/
def ixOf (l : ℕ) (digits : Bool) : ℕ := (if digits then 6 else 1) + (if l = 24 then 1 else 0)

/-- Its piece. -/
def pieceOf (l : ℕ) (digits : Bool) : ℕ := ixOf l digits + 1

/-- The number of the border in front of its block. -/
def borderOf (l : ℕ) (digits : Bool) : ℕ := 14 * l + ixOf l digits + 2

/-- The open public set at border k, at the composed meaning's own filling. -/
def openAt (k : ℕ) : List Pub :=
  (pubSets mgMore linksFull (flatPlacesOf linksFull true))[k]?.getD []

/-- The items that are wanted open, each with its border. -/
def wantedAt (l : ℕ) : List (ℕ × Pub) :=
  [(borderOf l false, .lookIn l (pieceOf l false)), (borderOf l false, .freeAbove l),
    (borderOf l false, .linkFresh l),
    (borderOf l true, .ledger l), (borderOf l true, .lookIn l (pieceOf l true)),
    (borderOf l true, .linkFresh l), (borderOf l true, .freeAbove l)] ++
  if l = 24 then [(borderOf l false, .tokenSmall)] else []

/-- Every wanted item of the segments 0 to 24 is in its open set. -/
def k3OpenB : Bool :=
  (List.range 25).all fun l => (wantedAt l).all fun x => (openAt x.1).contains x.2

/-- At each of the fifty numbers stands the place of the kind K3 with that segment and piece. -/
def k3PlacesB : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    decide ((flatPlacesOf linksFull true)[borderOf l d]? =
      some { chain := 1, link := some l, piece := pieceOf l d, kind := .K3 })

set_option maxRecDepth 1000000 in
theorem k3OpenB_full : k3OpenB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem k3PlacesB_full : k3PlacesB = true := by decide +kernel

/-- A wanted item is open. -/
theorem open_of_wanted {l : ℕ} (hl : l < 25) {x : ℕ × Pub} (hx : x ∈ wantedAt l) :
    x.2 ∈ openAt x.1 :=
  List.contains_iff_mem.1
    (List.all_eq_true.1 (List.all_eq_true.1 k3OpenB_full l (List.mem_range.2 hl)) x hx)

/-- The wanted item number i of segment l is open. -/
theorem open_at {l : ℕ} (hl : l < 25) (i : ℕ) {x : ℕ × Pub} (h : (wantedAt l)[i]? = some x) :
    x.2 ∈ openAt x.1 :=
  open_of_wanted hl (List.mem_of_getElem? h)

/-- **In front of the lookup on the calls.** -/
theorem k3_open_calls {l : ℕ} (hl : l < 25) :
    Pub.lookIn l (pieceOf l false) ∈ openAt (borderOf l false) ∧
      Pub.freeAbove l ∈ openAt (borderOf l false) ∧
      Pub.linkFresh l ∈ openAt (borderOf l false) :=
  ⟨open_at hl 0 (x := (borderOf l false, .lookIn l (pieceOf l false))) rfl,
    open_at hl 1 (x := (borderOf l false, .freeAbove l)) rfl,
    open_at hl 2 (x := (borderOf l false, .linkFresh l)) rfl⟩

/-- **In front of the lookup on the digits.** -/
theorem k3_open_digits {l : ℕ} (hl : l < 25) :
    Pub.ledger l ∈ openAt (borderOf l true) ∧
      Pub.lookIn l (pieceOf l true) ∈ openAt (borderOf l true) ∧
      Pub.linkFresh l ∈ openAt (borderOf l true) ∧ Pub.freeAbove l ∈ openAt (borderOf l true) :=
  ⟨open_at hl 3 (x := (borderOf l true, .ledger l)) rfl,
    open_at hl 4 (x := (borderOf l true, .lookIn l (pieceOf l true))) rfl,
    open_at hl 5 (x := (borderOf l true, .linkFresh l)) rfl,
    open_at hl 6 (x := (borderOf l true, .freeAbove l)) rfl⟩

/-- **At the head's calls.** -/
theorem k3_open_token : Pub.tokenSmall ∈ openAt (borderOf 24 false) :=
  open_at (l := 24) (by decide) 7 (x := (borderOf 24 false, .tokenSmall)) rfl

/-- **The fifty numbers are the numbers of K3's fifty places.** -/
theorem places_are_k3 {l : ℕ} (hl : l < 25) (d : Bool) :
    (flatPlacesOf linksFull true)[borderOf l d]? =
      some { chain := 1, link := some l, piece := pieceOf l d, kind := .K3 } :=
  of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 k3PlacesB_full l (List.mem_range.2 hl)) d (by cases d <;> simp))

set_option maxRecDepth 1000000 in
/-- The test can say no. -/
theorem not_open : (openAt (borderOf 0 false)).contains .tokenSmall = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At the composed meaning's small door the name "frame.liveIs" is open nowhere in front of the
lookups: its fact is taken from "reached". -/
theorem live_not_open : (List.range 25).all (fun l => [false, true].all fun d =>
    !(openAt (borderOf l d)).contains (liveItem l)) = true := by decide +kernel

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Sound.MgAt.k3OpenB_full
#print axioms VerifiableInference.Desc.Sound.MgAt.k3PlacesB_full
#print axioms VerifiableInference.Desc.Sound.MgAt.open_of_wanted
#print axioms VerifiableInference.Desc.Sound.MgAt.open_at
#print axioms VerifiableInference.Desc.Sound.MgAt.k3_open_calls
#print axioms VerifiableInference.Desc.Sound.MgAt.k3_open_digits
#print axioms VerifiableInference.Desc.Sound.MgAt.k3_open_token
#print axioms VerifiableInference.Desc.Sound.MgAt.places_are_k3
#print axioms VerifiableInference.Desc.Sound.MgAt.not_open
#print axioms VerifiableInference.Desc.Sound.MgAt.live_not_open
