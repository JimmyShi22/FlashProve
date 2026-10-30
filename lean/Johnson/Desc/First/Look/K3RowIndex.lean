-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3RowIndex.lean: the lookup on a link's CALLS AT THE TABLE OF JOINTS: THE
FIVE FIELDS OF AttAtTable AND LayAtTable THAT SPEAK OF THE TABLE's INDEX (ins, outs, ctx, askIn,
seats), FROM: "block number k of the index stands at the lookup's address" · ONE BOOL ON THE TABLE,
which a run or Lean's own evaluation can say at a real list of segments · "every seat of the link's
list is a tenant that segment m sends at moment 0". Statements and proofs; the Bool at the small and
at the full list of segments. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs in the verifier: the table of joints' own functions rowOf, openSets,
  pubSets (Johnson/Desc/First/Borders.lean) at the driver's own list of places.
Used by K3CallsMeanOf.lean, K3CallsMeanR.lean, K3Rides.lean (Johnson/Desc/First/Look/) and 2 more.
LETTERS: links, ps, k, m free in the lemmas; in the evaluations: the small list (layers, attention,
  layers, attention, head) and the full one (twelve pairs and the head), ps := flatPlaces true links
  true.

Main names:
  `att_row_at`, `lay_row_at`: where ps[k]? is a place of segment m, piece 2, and the segment is an
    attention | a layers' one: the row's ins, outs, ctx, to the letter of the two structures.
  `callsOpenB M links ps k m`: a Bool: lookIn m 2 is open in the promise's table (at the filling M
    of the table's door) in front of block k, and pin m 0 among the items.
  `askIn_of`, `seats_of`: what a yes gives.
  `callsAtB links m`: the Bool at the index's own number of the address (1, m, 2, K3), AT THE EMPTY
    FILLING OF THE DOOR.
  `callsAt_small`, `callsAt_full`: yes at every segment but the head's, at both lists.
  `callsLiveB`, `callsLive_small`, `callsLive_full`: the same AT THE FILLING liveMore
    (Johnson/Desc/First/Look/K3LiveIs.lean), with liveItem m open there; `callsLive_control`: at the
    empty filling it is open nowhere.
  `callsKeptB`, `callsKept_small`, `callsKept_full`: at liveMore freeAbove m and linkFresh m are
    open in front of the block; `callsKept_control`: the next segment's two are not.
  CONTROLS, at the small list: `callsNear_behind`, `callsNear_before`: one border later, one
    earlier: no at all four · `callsAt_small_head`: no at the head's segment · `callsOpen_other`:
    no at the next segment's number.

Limits. THE EVALUATIONS STAND AT TWO FILLINGS OF THE TABLE's DOOR ({}, liveMore): at another filling
Mg.more the Bool is to be evaluated anew (unproved here: a filling can neither
strike nor move a row of the table's own: no lemma of that is spent here). The head's segment:
nothing. That a real description's list of segments IS the small or the full list, and its flat
list of places flatPlaces true links true: not here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.First.Look.K3LiveIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (liveMore liveItem)
open VerifiableInference.Desc.First (ModelPart Item Pub Numbers More openSets pubSets start sampledIn
  rowOf segRow flatPlaces borderAt)

/-- The row at an attention segment's lookup on the calls. -/
theorem att_row_at {links : List ModelPart} {ps : List Place} {k m : ℕ} {p : Place}
    (hp : ps[k]? = some p) (hl : p.link = some m) (hs : links[m]? = some .attention)
    (hpc : p.piece = 2) :
    (rowQ links ps k).ins = [.constr m .lookCalls, .constr m .rider] ∧
      (rowQ links ps k).outs =
        [.formsT m 2 "objects", .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider"] ∧
      (rowQ links ps k).ctx = [.pin m 0, .constr m .small] := by
  have e : rowQ links ps k = segRow .attention m 2 := by
    unfold rowQ rowOf
    rw [hp]
    simp only [Option.map_some, Option.getD_some, hl, hs, hpc]
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

/-- The row at a layers' segment's lookup on the calls. -/
theorem lay_row_at {links : List ModelPart} {ps : List Place} {k m : ℕ} {p : Place}
    (hp : ps[k]? = some p) (hl : p.link = some m) (hs : links[m]? = some .layers)
    (hpc : p.piece = 2) :
    (rowQ links ps k).ins = [.constr m .lookCalls, .constr m .rider] ∧
      (rowQ links ps k).outs =
        [.formsT m 2 "objects", .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider"] ∧
      (rowQ links ps k).ctx = [.pin m 0, .constr m .small, .pinW] := by
  have e : rowQ links ps k = segRow .layers m 2 := by
    unfold rowQ rowOf
    rw [hp]
    simp only [Option.map_some, Option.getD_some, hl, hs, hpc]
  rw [e]
  exact ⟨rfl, rfl, rfl⟩

/-- In front of block k: lookIn m 2 is open in the promise's table, pin m 0 among the items. -/
def callsOpenB (M : More) (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  ((pubSets M links ps)[k]?.getD []).contains (.lookIn m 2) &&
    ((openSets links ps (start links))[k]?.getD []).contains (.pin m 0)

theorem askIn_of {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ}
    (h : callsOpenB M links ps k m = true) :
    Pub.lookIn m 2 ∈ (pubSets M links ps)[k]?.getD [] := by
  simp only [callsOpenB, Bool.and_eq_true] at h
  simpa using h.1

theorem seats_of {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ} (N : Numbers)
    {ι : Type} (seatT : ι → ℕ × ℕ) (h : callsOpenB M links ps k m = true)
    (hs : ∀ i, seatT i ∈ N.sent m 0) :
    ∀ i, seatT i ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []) := by
  intro i
  simp only [callsOpenB, Bool.and_eq_true] at h
  have hm : Item.pin m 0 ∈ (openSets links ps (start links))[k]?.getD [] := by simpa using h.2
  unfold sampledIn
  exact List.mem_flatMap.2 ⟨_, hm, hs i⟩

/-- The Bool at the index's own number of the address. -/
def callsAtB (links : List ModelPart) (m : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, 2, .K3⟩).map fun k =>
    callsOpenB {} links (flatPlaces true links true) k m).getD false

/-- The small list of segments. -/
def smallSubs : List ModelPart := [.layers, .attention, .layers, .attention, .head]

/-- The full list. -/
def fullSubs : List ModelPart :=
  (List.range 24).map (fun i => if i % 2 == 0 then ModelPart.layers else ModelPart.attention) ++ [.head]

theorem callsAt_small : (List.range 4).all (callsAtB smallSubs) = true := by decide

theorem callsAt_full : (List.range 24).all (callsAtB fullSubs) = true := by decide +kernel

/-! ## At the filling of the door that brings "frame.liveIs" -/

/-- At liveMore: the Bool, and liveItem m open in front of the block. -/
def callsLiveB (links : List ModelPart) (m : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, 2, .K3⟩).map fun k =>
    callsOpenB liveMore links (flatPlaces true links true) k m &&
      ((pubSets liveMore links (flatPlaces true links true))[k]?.getD []).contains
        (liveItem m)).getD false

/-- At liveMore: freeAbove m and linkFresh m are open in front of the block too. -/
def callsKeptB (links : List ModelPart) (m : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, 2, .K3⟩).map fun k =>
    ((pubSets liveMore links (flatPlaces true links true))[k]?.getD []).contains (.freeAbove m) &&
      ((pubSets liveMore links (flatPlaces true links true))[k]?.getD []).contains
        (.linkFresh m)).getD false

theorem callsKept_small : (List.range 4).all (callsKeptB smallSubs) = true := by decide +kernel

theorem callsKept_full : (List.range 24).all (callsKeptB fullSubs) = true := by decide +kernel

/-- A control: the next segment's two items are not open there. -/
theorem callsKept_control : (List.range 4).all (fun m =>
    !((borderAt (flatPlaces true smallSubs true) ⟨1, some m, 2, .K3⟩).map fun k =>
      ((pubSets liveMore smallSubs (flatPlaces true smallSubs true))[k]?.getD []).contains
          (.freeAbove (m + 1)) ||
        ((pubSets liveMore smallSubs (flatPlaces true smallSubs true))[k]?.getD []).contains
          (.linkFresh (m + 1))).getD false) = true := by decide +kernel

theorem callsLive_small : (List.range 4).all (callsLiveB smallSubs) = true := by decide +kernel

theorem callsLive_full : (List.range 24).all (callsLiveB fullSubs) = true := by decide +kernel

/-- A control: at the empty filling liveItem is open nowhere. -/
theorem callsLive_control : (List.range 4).all (fun m =>
    !((borderAt (flatPlaces true smallSubs true) ⟨1, some m, 2, .K3⟩).map fun k =>
      ((pubSets {} smallSubs (flatPlaces true smallSubs true))[k]?.getD []).contains
        (liveItem m)).getD false) = true := by decide +kernel

/-! ## Controls: the Bool can say no -/

/-- The Bool one border later (d = 2) or earlier (d = 0) than the address's own (d = 1). -/
def callsNearB (links : List ModelPart) (m d : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, 2, .K3⟩).map fun k =>
    callsOpenB {} links (flatPlaces true links true) (k + d - 1) m).getD false

/-- At the address's own border callsNearB is callsAtB. -/
theorem callsNear_own : (List.range 4).all (fun m => callsNearB smallSubs m 1) = true := by decide

/-- BEHIND the lookup's block the Bool says no at all four segments: lookIn is dropped. -/
theorem callsNear_behind : (List.range 4).all (fun m => !callsNearB smallSubs m 2) = true := by
  decide

/-- ONE BLOCK EARLIER it says no at all four: lookIn is not yet made. -/
theorem callsNear_before : (List.range 4).all (fun m => !callsNearB smallSubs m 0) = true := by
  decide

/-- At the head's segment, whose piece 2 is no lookup, it says no. -/
theorem callsAt_small_head : callsAtB smallSubs 4 = false := by decide

/-- At another segment's number it says no. -/
theorem callsOpen_other : (List.range 4).all (fun m =>
    !((borderAt (flatPlaces true smallSubs true) ⟨1, some m, 2, .K3⟩).map fun k =>
      callsOpenB {} smallSubs (flatPlaces true smallSubs true) k (m + 1)).getD false) = true := by
  decide

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.callsKept_small
#print axioms VerifiableInference.OnPublicFiles.callsKept_full
#print axioms VerifiableInference.OnPublicFiles.callsKept_control
#print axioms VerifiableInference.OnPublicFiles.callsLive_small
#print axioms VerifiableInference.OnPublicFiles.callsLive_full
#print axioms VerifiableInference.OnPublicFiles.callsLive_control
#print axioms VerifiableInference.OnPublicFiles.callsNear_own
#print axioms VerifiableInference.OnPublicFiles.callsNear_behind
#print axioms VerifiableInference.OnPublicFiles.callsNear_before
#print axioms VerifiableInference.OnPublicFiles.callsAt_small_head
#print axioms VerifiableInference.OnPublicFiles.callsOpen_other
#print axioms VerifiableInference.OnPublicFiles.att_row_at
#print axioms VerifiableInference.OnPublicFiles.lay_row_at
#print axioms VerifiableInference.OnPublicFiles.askIn_of
#print axioms VerifiableInference.OnPublicFiles.seats_of
#print axioms VerifiableInference.OnPublicFiles.callsAt_small
#print axioms VerifiableInference.OnPublicFiles.callsAt_full
