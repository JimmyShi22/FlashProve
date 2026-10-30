-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/TableAtK8.lean: CLOSED FACTS ON THE TABLE OF JOINTS AT THE SMALLNESS TEST's 25 PLACES
OF THE WRITTEN LIST, BY LEAN's KERNEL (decide +kernel; no native code), at the composed meaning's
closed list of extra public tests (mgMore, Johnson/Desc/Sound/MgAllAt.lean).
  k8PubB_full      in front of the draw in segment l every public item that is open, or tied to an open item, is of one of the sorts k8Sort (Johnson/Desc/First/K8/BlindPub.lean); behind the draw just one more is asked: formsIn l (pcOf l) "small"; no open public item comes (whether one goes is not tested: none is needed).
  k8_row_full      what the draw's row closes, opens and reads. (THE LIKE STANDS IN Johnson/Desc/First/K8/RowAtDraw.lean, row_at_draw_full, which others call; this one is for Johnson/P1K8R/BlindAtMg.lean's own use alone.)
  k8RidersB_full   every item that is open in front of the draw and that its row neither closes nor reads is of one of the sorts k8ItemSort (of the runs of forms: those of the segment's pieces in front of the draw's).
  k8_pins_open     the index masks' pin and the pins of the segment's first two sendings are open in front of the draw.
  tableOkB_full    the table's own two tests readsOpen and rowsApart say yes at the written list: so the rule's open set at a border has just the members of the table's list (openL_iff_openSets, Johnson/Desc/Sound/SpineList.lean).
LIMITS. Facts on written lists. Nothing on a state of the verifier. No soundness.
-/
import Johnson.P1K8R.TiedBlind
import Johnson.Desc.First.K8.BlindPub
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers flatPlacesOf openSets pubSets
  start stepOpen pubStep pubRowM rowOf pubOfItems readsOpen)
open VerifiableInference.Desc.First.K8 (k8Sort)

/-- The draw's piece in segment l. -/
def pcOf (l : ℕ) : ℕ := if l = 24 then 6 else 5

/-- A TEST ON THE TABLE, at the closed list of extra public tests: in front of the draw in segment l
every public item that is open or tied to an open item is of one of the sorts `k8Sort`; behind the
draw just one more is asked: the test that is tied to the run of forms "small". -/
def k8PubAt (l : ℕ) : Bool :=
  let links := linksFull
  let ps := flatPlacesOf links true
  let O := (openSets links ps (start links))[ixOf l]?.getD []
  let Q := (pubSets mgMore links ps)[ixOf l]?.getD []
  match ps[ixOf l]? with
  | none => false
  | some p =>
    (Q ++ pubOfItems O).all (k8Sort l (pcOf l)) &&
      ((pubStep Q (pubRowM mgMore links p) ++ pubOfItems (stepOpen O (rowOf links p))).all fun q =>
        (Q ++ pubOfItems O).contains q || q == Pub.formsIn l (pcOf l) "small") &&
      (pubStep Q (pubRowM mgMore links p)).all Q.contains

set_option maxRecDepth 1000000 in
theorem k8PubB_full : ((List.range 25).all k8PubAt) = true := by decide +kernel

/-- A TEST ON THE TABLE: what the draw's row closes, opens and reads in segment l. -/
def k8RowAt (l : ℕ) : Bool :=
  let r := rowQ linksFull (flatPlacesOf linksFull true) (ixOf l)
  decide (r.ins = [Item.constr l .small, Item.tie l]) &&
    decide (r.outs = [Item.forms l (pcOf l) "small", Item.constr l .lookDigits]) &&
    decide (r.ctx = [Item.pin l 0, Item.pin l 1])

set_option maxRecDepth 1000000 in
theorem k8RowB_full : ((List.range 25).all k8RowAt) = true := by decide +kernel

/-- **The draw's row at each of the 25 numbers.** -/
theorem k8_row_full {l : ℕ} (hl : l ≤ 24) :
    (rowQ linksFull (flatPlacesOf linksFull true) (ixOf l)).ins =
        [Item.constr l .small, Item.tie l] ∧
      (rowQ linksFull (flatPlacesOf linksFull true) (ixOf l)).outs =
        [Item.forms l (pcOf l) "small", Item.constr l .lookDigits] ∧
      (rowQ linksFull (flatPlacesOf linksFull true) (ixOf l)).ctx =
        [Item.pin l 0, Item.pin l 1] := by
  have h := List.all_eq_true.1 k8RowB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8RowAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The sorts of item that ride past the draw in segment l. -/
def k8ItemSort (l : ℕ) : Item → Bool
  | .constr m p => decide (l < m) && p != .lookDigits
  | .pinW => true
  | .pile => true
  | .pinI => true
  | .row m _ => m == l
  | .wo m => m == l
  | .forms m k _ => m == l && decide (k < pcOf l)
  | _ => false

/-- A TEST ON THE TABLE: the riders' sorts. -/
def k8RidersAt (l : ℕ) : Bool :=
  let links := linksFull
  let ps := flatPlacesOf links true
  let O := (openSets links ps (start links))[ixOf l]?.getD []
  (O.filter fun i => !(insL links ps (ixOf l)).contains i).all (k8ItemSort l)

set_option maxRecDepth 1000000 in
theorem k8RidersB_full : ((List.range 25).all k8RidersAt) = true := by decide +kernel

/-- A TEST ON THE TABLE: the index masks' pin and the pins of the segment's first two sendings are
open in front of the draw. -/
def k8PinsAt (l : ℕ) : Bool :=
  let O := (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[ixOf l]?.getD []
  O.contains Item.pinI && O.contains (Item.pin l 0) && O.contains (Item.pin l 1)

set_option maxRecDepth 1000000 in
theorem k8PinsB_full : ((List.range 25).all k8PinsAt) = true := by decide +kernel

/-- **Three pins are open in front of the draw, at each of the 25 numbers.** -/
theorem k8_pins_open {l : ℕ} (hl : l ≤ 24) :
    Item.pinI ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[ixOf l]?.getD [] ∧
      Item.pin l 0 ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[ixOf l]?.getD [] ∧
      Item.pin l 1 ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[ixOf l]?.getD [] := by
  have h := List.all_eq_true.1 k8PinsB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8PinsAt at h
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

set_option maxRecDepth 1000000 in
theorem tableOkB_full :
    (readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) &&
      rowsApart linksFull (flatPlacesOf linksFull true)) = true := by decide +kernel

end P1K8T

#print axioms P1K8T.k8PubB_full
#print axioms P1K8T.k8_row_full
#print axioms P1K8T.k8RidersB_full
#print axioms P1K8T.k8_pins_open
#print axioms P1K8T.tableOkB_full
