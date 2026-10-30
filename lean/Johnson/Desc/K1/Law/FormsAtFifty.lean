-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/FormsAtFifty.lean: TWO FACTS ON THE
TABLE OF JOINTS AT K1's FIFTY LATER PLACES OF THE FULL SIZE, BY EVALUATION IN LEAN's KERNEL, on the
public items formsIn | formsInT. Tests with code, what a yes of each says, and the evaluations.

OBJECT. The table's own lists at First.flatPlacesOf linksFull true: openAt, First.pubOfItems,
First.pubSets, and tiedAt (RowLFull.lean, this folder), at the numbers 14 l + k1Ix l d + 2, l < 25.
USER. (1) R1: the premise hpub of k01_reads_tied: every tied public item that comes at a link's
reads' place is a formsIn l j r whose formsInT l j r is tied to an item open in front: so the
promise in front holds h0 of GoAtLaterForms.lean's pub_formsIn_new_later. (2) The binder hseg
of PubAtLaterCall.lean's hPub_of.
LETTERS. M: the door's filling, at hseg_full; none at hseg_door.
Main names:
  tiedFormsB · tiedForms_of · formsSegB · noFormsB · hseg_of     the tests; what a yes says
  tiedForms_full · formsSeg_full · noForms_door   [kernel]
  formsTests_fail   [kernel] THE TESTS CAN FAIL: at another segment's number (twice); one block in
                    front of a reads' place
  tied_reads_full   **R1's fact**
  hseg_full         **hseg at the fifty**, at any door M with noFormsB M .. = true
  hseg_door         **no premise left** at Sound.mgMore (Johnson/Desc/Sound/MgAllAt.lean: the
                    composed meaning's closed door).
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000), as in RowLFull.lean: for
the kernel's evaluations' elaboration alone.
What is not claimed. That a base meaning's door is empty. That the table is right. At a digits'
place tiedAt is empty (tiedAt_counts): tiedFormsB would hold there idly: it is evaluated at the
reads' alone. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RowLFull
import Johnson.Desc.Sound.MgAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open IM (k1Ix)

/-! ## 1 The tests, and what a yes of each says -/

/-- Every tied public item that comes at block k is a formsIn of segment l whose formsInT is tied to
an item that is open in front. -/
def tiedFormsB (links : List ModelPart) (ps : List Place) (k l : ℕ) : Bool :=
  (tiedAt links ps k).all fun q =>
    match q with
    | .formsIn m j r =>
      m == l && (First.pubOfItems (openAt links ps k)).contains (.formsInT m j r)
    | _ => false

theorem tiedForms_of {links : List ModelPart} {ps : List Place} {k l : ℕ}
    (h : tiedFormsB links ps k l = true) (q : Pub) (hq : q ∈ tiedAt links ps k) :
    ∃ j r, q = .formsIn l j r ∧
      Pub.formsInT l j r ∈ First.pubOfItems (openAt links ps k) := by
  unfold tiedFormsB at h
  have h1 := List.all_eq_true.1 h q hq
  cases q with
  | formsIn m j r =>
    have h2 : (m == l &&
        (First.pubOfItems (openAt links ps k)).contains (.formsInT m j r)) = true := h1
    rw [Bool.and_eq_true] at h2
    obtain rfl : m = l := eq_of_beq h2.1
    exact ⟨j, r, rfl, by simpa using h2.2⟩
  | _ => cases h1

/-- Every formsIn that is tied to an item open in front of block k is segment l's. -/
def formsSegB (links : List ModelPart) (ps : List Place) (k l : ℕ) : Bool :=
  (First.pubOfItems (openAt links ps k)).all fun q =>
    match q with
    | .formsIn m _ _ => m == l
    | _ => true

/-- No formsIn stands in the open public set in front of block k, at the door's filling M. -/
def noFormsB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((First.pubSets M links ps)[k]?.getD []).all fun q =>
    match q with
    | .formsIn _ _ _ => false
    | _ => true

/-- **hPub_of's binder hseg** (PubAtLaterCall.lean), from the two tests. -/
theorem hseg_of {M : More} {links : List ModelPart} {ps : List Place} {k l : ℕ}
    (h1 : formsSegB links ps k l = true) (h2 : noFormsB M links ps k = true) (m j : ℕ)
    (r : String)
    (h : Pub.formsIn m j r ∈ (First.pubSets M links ps)[k]?.getD [] ++
      First.pubOfItems (openAt links ps k)) : m = l := by
  rcases List.mem_append.1 h with h | h
  · unfold noFormsB at h2
    exact nomatch List.all_eq_true.1 h2 _ h
  · unfold formsSegB at h1
    exact eq_of_beq (List.all_eq_true.1 h1 _ h)

/-! ## 2 At the full size's written list of places, by evaluation in Lean's kernel -/

theorem tiedForms_full : ((List.range 25).all fun l =>
    tiedFormsB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) l) = true := by
  decide +kernel

theorem formsSeg_full : ((List.range 25).all fun l => [false, true].all fun d =>
    formsSegB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) l) = true := by
  decide +kernel

/-- At the composed meaning's closed door. -/
theorem noForms_door : ((List.range 25).all fun l => [false, true].all fun d =>
    noFormsB (Sound.mgMore) linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l d + 2)) = true := by
  decide +kernel

/-- **The tests can fail**: at another segment's number; and a formsIn does ride at a digits'
place. -/
theorem formsTests_fail :
    tiedFormsB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 2) 4 = false ∧
    formsSegB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2) 4 = false ∧
    tiedFormsB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 1) 3 = false := by
  decide +kernel

/-- **R1's kernel fact**: the tied public items that come at a link's reads' place. -/
theorem tied_reads_full (l : ℕ) (hl : l < 25) (q : Pub)
    (hq : q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)) :
    ∃ j r, q = .formsIn l j r ∧ Pub.formsInT l j r ∈ First.pubOfItems
      (openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)) :=
  tiedForms_of (List.all_eq_true.1 tiedForms_full l (List.mem_range.2 hl)) q hq

/-- **hseg at the fifty**, at any door M at which no formsIn stands in the open public set. -/
theorem hseg_full (M : More) (l : ℕ) (hl : l < 25) (d : Bool)
    (hM : noFormsB M linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) = true)
    (m j : ℕ) (r : String)
    (h : Pub.formsIn m j r ∈
      (First.pubSets M linksFull (flatPlacesOf linksFull true))[14 * l + k1Ix l d + 2]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
          (14 * l + k1Ix l d + 2))) : m = l :=
  hseg_of (List.all_eq_true.1 (List.all_eq_true.1 formsSeg_full l (List.mem_range.2 hl)) d
    (by cases d <;> simp)) hM m j r h

/-- **hseg at the fifty, at the composed meaning's closed door**: no premise left. -/
theorem hseg_door (l : ℕ) (hl : l < 25) (d : Bool) (m j : ℕ) (r : String)
    (h : Pub.formsIn m j r ∈ (First.pubSets (Sound.mgMore) linksFull
        (flatPlacesOf linksFull true))[14 * l + k1Ix l d + 2]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
          (14 * l + k1Ix l d + 2))) : m = l :=
  hseg_full _ l hl d (List.all_eq_true.1 (List.all_eq_true.1 noForms_door l
    (List.mem_range.2 hl)) d (by cases d <;> simp)) m j r h

end VerifiableInference.Desc.K1
