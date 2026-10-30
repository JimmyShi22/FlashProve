-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyRowsFull.lean: r5 OF THE KEY FILE's BACK: UNDER THE
NAMED EQUATIONS (Johnson.KB8.Pins) AND ONE MORE (hs): THE ROWS OF A KEY FILE's DESCRIPTION ARE THE
THREE WRITTEN LISTS W₁ | W₂ | W₃, THE TABLE «wanted» IS THE SAME THREE, AND SO wantedOk SAYS YES.


WHAT IS SAID.
  looks_rows_eq      a lookup's number of rounds off the planner's run is that of the plain list.
  first_rows_at      so the first chain's rows at the typed sizes are W₁.
  key_rows           **under Pins: the three chains' rows (rowsOf) are W₁ | W₂ | W₃.**
  key_wantedOk       **r5, to the ledger's letter (IM.keyBack_of_rows): (Key.descriptionFromSource X N P).wantedOk =
                     true**, under Pins X N P and hs.
CALLED, NOT TYPED AGAIN: W₁ | W₂ | W₃ · first_rows_full | shared_rows_full |
second_rows_full (THE TABLE's three parts at keyFull are these lists: by the kernel) · rowsOf ·
placesOf_rows (Johnson/RunOne/Sound/KeyPlacesInScope.lean · KeyListsAtFK.lean). THESE FILES GO FROM
wantedOk TO THE ROWS; THIS ONE GOES FROM THE SUB-PROTOCOLS' OWN TEXTS TO THE ROWS, AND SO TO
wantedOk.
The closed facts on the sub-protocols' side: IMR/KeyRowsFirst.lean · KeyRowsLater.lean.
THE PREMISES, BY NAME. h : Johnson.KB8.Pins X N P: thirteen equations on what the rows read, each at
a written value. hs : X.Y.k.shared.lin = keyFull.once.shape: THE SHARED CHAIN's LINEAR SHAPE, AS THE
PROGRAM READS IT BACK FROM THE PARAMETER BYTES, IS THE TYPED ONE-TIME SHAPE: the table's second and
third part read it; it is r8′'s own premise. NO planOk: r5 LEANS ON NO OTHER ROW.
What is not claimed. THAT THE PREMISES HOLD AT THE RELEASE's OWN X N P: Johnson.KB8.pins_met
is at an X made for the purpose. What a sub-protocol at a place DOES: a row holds its place and its
NUMBER of rounds (Block.lean's own limit on wantedOk). No soundness.

-/
import Johnson.IMR.KeyRowsFirst
import Johnson.IMR.KeyRowsLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Johnson.KB8
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Sound (rowsOf W₁ W₂ W₃ placesOf_rows)

theorem looks_rows_eq {set : Setting} (hf : First.Look.Made.FieldFit set .once) :
    ∀ (l : List Lookup) (n : Nat), l.all (lookOk set) = true →
      ((l.zipIdx n).flatMap fun x => wantedLink x.2 (lookRounds set x.1).length) =
        (l.zipIdx n).flatMap fun x => wantedLink x.2 (lookList set x.1).length
  | [], _, _ => rfl
  | x :: l, n, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    rw [List.zipIdx_cons, List.flatMap_cons, List.flatMap_cons, look_eq hf h.1,
      looks_rows_eq hf l (n + 1) h.2]

theorem first_rows_at : firstRowsOf (fun x => (lookRounds keyFull.set x).length)
    keyFull.ranges.x keyFull.once.shape keyFull.once.input keyFull.codes rsR.length = W₁ := by
  unfold firstRowsOf
  rw [looks_rows_eq fit_full _ 0 looks_ok_full]
  exact first_rows_list

/-- **Under the named equations the three chains' rows are the three written lists.** -/
theorem key_rows {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P) :
    rowsOf (descriptionFromSource X N P).first.blocksInOrder = W₁ ∧ rowsOf (descriptionFromSource X N P).shared.blocksInOrder = W₂ ∧
      rowsOf (descriptionFromSource X N P).second.blocksInOrder = W₃ := by
  obtain ⟨O, hO, hOc, hOn⟩ := h.o
  have kR : (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Key.Claim).rounds = rsR :=
    k12_rounds_at K12.guardedProximityTestParts (place := rangesPlace) (x := N) h.nC.symm
      (by rw [h.nN]; exact some_R)
  have kU : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) :
      Block K12.T12 Unit).rounds = rsU :=
    k12_rounds_at K12.guardedProximityTestParts h.uC.symm (by rw [h.uN]; exact some_U)
  have kO : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O) :
      Block K12.T12 Unit).rounds = rsO :=
    k12_rounds_at K12.guardedProximityTestParts hOc.symm (by rw [hOn]; exact some_O)
  have kW : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
      Block K12.T12 Unit).rounds = declKeyFull.2.2 :=
    k12_rounds_at K12.guardedProximityTestParts h.wC.symm (by rw [h.wN]; exact third_full)
  refine ⟨?_, ?_, ?_⟩
  · show (firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).blocksInOrder.map rowOf = W₁
    rw [first_rows, kR, h.set, h.ranges, h.lin, h.idx, h.codes]
    exact first_rows_at
  · show ((sharedChain X.chains P).retype : Chain _root_.Desc.K14.St Key.Claim).blocksInOrder.map rowOf = W₂
    rw [shared_rows, kU, hO, h.sized]
    show sharedRowsOf keyFull rsU.length
      [(K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O) :
        Block K12.T12 Unit).rounds.length] = W₂
    rw [kO]
    exact shared_rows_list
  · show ((thirdChain X.chains P).retype : Chain Third.S₃ Key.Claim).blocksInOrder.map rowOf = W₃
    rw [third_rows, kW, third_len]
    rfl

/-- **r5: the sub-protocols' places and numbers of rounds are the table's.** hs: the shared chain's
linear shape as read back is the typed one-time shape. -/
theorem key_wantedOk {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    (hs : X.Y.k.shared.lin = keyFull.once.shape) : (descriptionFromSource X N P).wantedOk = true := by
  obtain ⟨r1, r2, r3⟩ := key_rows h
  unfold FileDescription.wantedOk FileDescription.places
  rw [List.map_append, List.map_append, placesOf_rows, placesOf_rows, placesOf_rows, r1, r2, r3]
  show (W₁ ++ W₂ ++ W₃ == wantedFirst X.Y.k.oneTime ++ wantedShared X.Y.k.shared.lin ++
    wantedSecond X.Y.k.shared.lin) = true
  rw [Johnson.RunOne.Sound.first_rows_full _ h.ranges h.lin, hs,
    Johnson.RunOne.Sound.shared_rows_full, Johnson.RunOne.Sound.second_rows_full]
  exact beq_self_eq_true _

end IM

#print axioms IM.looks_rows_eq
#print axioms IM.first_rows_at
#print axioms IM.key_rows
#print axioms IM.key_wantedOk
