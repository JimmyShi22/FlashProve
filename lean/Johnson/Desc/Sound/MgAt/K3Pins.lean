-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3Pins.lean: which pins are open in front of the fifty blocks of the kind
"lookup" (K3) in the table of joints (Johnson/Desc/First/Borders.lean), at the full size's list of
segments; which places stand behind these blocks; and that the kind's rows close and open no pin and
no class of rows. Closed facts on the table. No meaning is named.

What it is for. The premises of the kind's laws at a place ask that the seats of the oracle messages
that the lookup reads are among the sampled tenants whose pin is open at the border in front
(`sampledIn`). Whoever has "the seat is among what segment l sends at moment t" gets that from the
pins that are open there.

Which terms. `linksFull` (Johnson/Desc/Sound/AtDriver.lean), `First.flatPlacesOf linksFull true`,
and `ixOf`, `pieceOf`, `borderOf` of Johnson/Desc/Sound/MgAt/K3Open.lean, which this file imports
for these three definitions alone.

Definitions.
  `itemsAt k`: the items that are open at border k (`openSets`, from `start`).
  `placeOf l d`: the place of the lookup on the calls (d false) or on the digits (d true) of segment
    l. `nextOf l d`: the place behind it: behind the calls' lookup the segment's own kind: K4 at a
    segment of layers (l even), K5 at attention (l odd), K6 at the head (l = 24); behind the digits'
    lookup K9, at the head K11; the piece is one more.
  `pinsB`, `nextB`, `quietB`: the three tests, each over the segments 0 to 24.
Statements.
  `pinsB_full`, `nextB_full`, `quietB_full`: the tests say yes.
  `pin_open_calls`: for l < 25 the pin of segment l's moment 0 is open in front of the calls'
    lookup. `pin_open_digits`: the pins of the moments 2, 0 and 1 are open in front of the digits'
    lookup.
  `sampled_of_pin`: a tool: what a segment sends at a moment whose pin is among the items O is among
    `sampledIn N O`. `sampled_calls`, `sampled_digits`: so, at all numbers N, whatever segment l
    sends at these moments is among the sampled tenants whose pin is open there.
  `next_place`: the place behind each of the fifty blocks.
  `quiet_row`: the row of each of the fifty places passes `quietRow`
    (Johnson/Desc/First/BordersKeep.lean).
  `pin_not_open`: the test can say no: the pin of segment 0's moment 1 is not open in front of its
    calls' lookup.
By evaluations in Lean's kernel (`decide +kernel`): the three tests' yes and `pin_not_open`.

What of OnBytes/Model/ is used: nothing.

Limits. Facts on the table's own text: that a pin is open says nothing on whether it holds of any
witness. The full size's list of segments alone. Nothing on soundness.
-/
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.Desc.First.BordersKeep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound.MgAt
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item Numbers openSets start sampledIn rowOf quietRow
  flatPlacesOf)

/-- The items that are open at border k. -/
def itemsAt (k : ℕ) : List Item :=
  (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD []

/-- The place of the lookup on the calls, or on the digits, of segment l. -/
def placeOf (l : ℕ) (d : Bool) : Place :=
  { chain := 1, link := some l, piece := pieceOf l d, kind := .K3 }

/-- The place behind it. -/
def nextOf (l : ℕ) (d : Bool) : Place :=
  { chain := 1, link := some l, piece := pieceOf l d + 1
    kind := if d then (if l = 24 then .K11 else .K9)
      else if l = 24 then .K6 else if l % 2 = 0 then .K4 else .K5 }

/-- The pins that are wanted open are open. -/
def pinsB : Bool :=
  (List.range 25).all fun l => (itemsAt (borderOf l false)).contains (.pin l 0) &&
    [2, 0, 1].all fun t => (itemsAt (borderOf l true)).contains (.pin l t)

/-- Behind each of the fifty blocks stands the place `nextOf`. -/
def nextB : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    decide ((flatPlacesOf linksFull true)[borderOf l d + 1]? = some (nextOf l d))

/-- The row of each of the fifty places closes and opens no pin and no class of rows. -/
def quietB : Bool :=
  (List.range 25).all fun l => [false, true].all fun d => quietRow (rowOf linksFull (placeOf l d))

set_option maxRecDepth 1000000 in
theorem pinsB_full : pinsB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem nextB_full : nextB = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem quietB_full : quietB = true := by decide +kernel

/-- **In front of the lookup on the calls the pin of moment 0 is open.** -/
theorem pin_open_calls {l : ℕ} (hl : l < 25) : Item.pin l 0 ∈ itemsAt (borderOf l false) := by
  have h := List.all_eq_true.1 pinsB_full l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h
  exact List.contains_iff_mem.1 h.1

/-- **In front of the lookup on the digits the pins of the moments 2, 0 and 1 are open.** -/
theorem pin_open_digits {l : ℕ} (hl : l < 25) :
    ∀ t ∈ [2, 0, 1], Item.pin l t ∈ itemsAt (borderOf l true) := by
  intro t ht
  have h := List.all_eq_true.1 pinsB_full l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at h
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h.2 t ht)

/-- What a segment sends at a moment whose pin is open is among the sampled tenants there. -/
theorem sampled_of_pin (N : Numbers) {O : List Item} {l t : ℕ} (h : Item.pin l t ∈ O) :
    ∀ e ∈ N.sent l t, e ∈ sampledIn N O := fun _ he =>
  List.mem_flatMap.2 ⟨.pin l t, h, he⟩

/-- **So, at all numbers.** -/
theorem sampled_calls (N : Numbers) {l : ℕ} (hl : l < 25) :
    ∀ e ∈ N.sent l 0, e ∈ sampledIn N (itemsAt (borderOf l false)) :=
  sampled_of_pin N (pin_open_calls hl)

theorem sampled_digits (N : Numbers) {l : ℕ} (hl : l < 25) :
    ∀ t ∈ [2, 0, 1], ∀ e ∈ N.sent l t, e ∈ sampledIn N (itemsAt (borderOf l true)) :=
  fun t ht => sampled_of_pin N (pin_open_digits hl t ht)

/-- **The place behind each of the fifty blocks.** -/
theorem next_place {l : ℕ} (hl : l < 25) (d : Bool) :
    (flatPlacesOf linksFull true)[borderOf l d + 1]? = some (nextOf l d) :=
  of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 nextB_full l (List.mem_range.2 hl)) d (by cases d <;> simp))

/-- **The kind's rows close and open no pin and no class of rows.** -/
theorem quiet_row {l : ℕ} (hl : l < 25) (d : Bool) :
    quietRow (rowOf linksFull (placeOf l d)) = true :=
  List.all_eq_true.1 (List.all_eq_true.1 quietB_full l (List.mem_range.2 hl)) d
    (by cases d <;> simp)

set_option maxRecDepth 1000000 in
/-- The test can say no. -/
theorem pin_not_open : (itemsAt (borderOf 0 false)).contains (.pin 0 1) = false := by
  decide +kernel

end VerifiableInference.Desc.Sound.MgAt

#print axioms VerifiableInference.Desc.Sound.MgAt.pinsB_full
#print axioms VerifiableInference.Desc.Sound.MgAt.nextB_full
#print axioms VerifiableInference.Desc.Sound.MgAt.quietB_full
#print axioms VerifiableInference.Desc.Sound.MgAt.pin_open_calls
#print axioms VerifiableInference.Desc.Sound.MgAt.pin_open_digits
#print axioms VerifiableInference.Desc.Sound.MgAt.sampled_of_pin
#print axioms VerifiableInference.Desc.Sound.MgAt.sampled_calls
#print axioms VerifiableInference.Desc.Sound.MgAt.sampled_digits
#print axioms VerifiableInference.Desc.Sound.MgAt.next_place
#print axioms VerifiableInference.Desc.Sound.MgAt.quiet_row
#print axioms VerifiableInference.Desc.Sound.MgAt.pin_not_open
