-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LightWritten.lean: the kind "the code switch" (K2): FOUR OF THE
SIX PUBLIC TESTS OF `publicOk_of_six` (LightByAddress.lean of this folder) SAY YES AT THE WRITTEN
PLAN, AT THE REFERENCE SIZES `Sz.ref`: every own message has an address · the light test at the
switches' own data · the light test at the opening's data · each switch's own sending's share.
Definitions with code; closed facts by Lean's kernel, each with a control; three small laws.

  `lightBy`, `addressedBy`   `lightAt` and `addressed` with the place's reader of addresses as a
                    letter: they read nothing else of the place
  `lightBy_take`, `addressedBy_take`   a yes at a list of segments is a yes at each beginning of it
  `addrsW`, `addrs_written`   all written places have ONE reader of addresses
  `ownSeatsW`, `switchSeatW`, `mineSwitchW`, `mineFirstW`   the switches' seats off the written
                    places and the written shape of a request; whose an address is
  `switchDataL`, `firstFillL`   the switches' own data and the opening's at the written codes, shape
                    and layout, over the sizes' twin that the kernel reduces (`cellsValsL`,
                    LabelByList.lean of this folder)
  `ownShareL`       `ownShare` at these
  `addressedW`, `switchesW`, `openingW`, `ownSharesW`   THE FOUR, BY LEAN's KERNEL, the first three
                    at all 25 written segments at once
  `…_can_fail`      controls: with no address the first says no; at the small example's sizes
                    `Sz.small` the second and the fourth say no; at the data that lay nothing the
                    third says no: so none of them is idle

Limits. PUBLIC DATA ALONE: written places, segments, codes, shape, layout, sizes. THE WRITTEN PLAN:
nothing on any description: LightAtHead.lean of this folder carries these to the head. The full
size; the format's second hash function. The light test reads where a datum lays an element, not what.
Nothing on the digits' or the reads' data. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LightDebts
import Johnson.Desc.ProofFile.Honest.K2.Law.LabelByList
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes.HonestTrace (Sz)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull)
open Johnson.AtFull.Desc (spotsWritten)

/-! ## 1 The place's reader of addresses as a letter -/

/-- `lightAt`, with the reader of addresses as a letter. -/
def lightBy (D : RowData) (mine : MsgAddr → Bool) (lay : OnBytes.Params.ReqLayout)
    (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub) : Bool :=
  segs.zipIdx.all fun y =>
    (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s =>
      (addrs y.2 s.2).all fun a =>
        !mine a || arraysLaidLight D lay y.1.sizes.codes s.1 y.2 s.2 a

/-- `addressed`, with the reader of addresses as a letter. -/
def addressedBy (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub) : Bool :=
  segs.zipIdx.all fun y =>
    (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s => (addrs y.2 s.2).isSome

theorem lightAt_by (D : RowData) (mine : MsgAddr → Bool) (lay : OnBytes.Params.ReqLayout)
    (p : SwitchPlace) (segs : List SegmentPub) :
    lightAt D mine lay p segs = lightBy D mine lay p.addrs segs := rfl

theorem addressed_by (p : SwitchPlace) (segs : List SegmentPub) :
    addressed p segs = addressedBy p.addrs segs := rfl

/-- A numbered member of a list's beginning is a numbered member of the list. -/
theorem zipIdx_take_mem {α : Type} (l : List α) (n : Nat) {y : α × Nat}
    (hy : y ∈ (l.take n).zipIdx) : y ∈ l.zipIdx := by
  rw [List.mem_zipIdx_iff_getElem?] at hy ⊢
  rw [List.getElem?_take] at hy
  split at hy
  · exact hy
  · cases hy

/-- **A yes at a list of segments is a yes at each of its beginnings.** -/
theorem lightBy_take {D : RowData} {mine : MsgAddr → Bool} {lay : OnBytes.Params.ReqLayout}
    {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub}
    (h : lightBy D mine lay addrs segs = true) (n : Nat) :
    lightBy D mine lay addrs (segs.take n) = true :=
  List.all_eq_true.2 fun y hy => List.all_eq_true.1 h y (zipIdx_take_mem segs n hy)

/-- The like for `addressedBy`. -/
theorem addressedBy_take {addrs : Nat → Nat → Option MsgAddr} {segs : List SegmentPub}
    (h : addressedBy addrs segs = true) (n : Nat) : addressedBy addrs (segs.take n) = true :=
  List.all_eq_true.2 fun y hy => List.all_eq_true.1 h y (zipIdx_take_mem segs n hy)

/-! ## 2 The written terms -/

/-- The written places' one reader of addresses. -/
def addrsW : Nat → Nat → Option MsgAddr :=
  match IM.prepW with
  | some P =>
    addrOf { shape := P.z.request, groups := OnBytes.reqGroups P.z.request } spotsWritten
  | none => fun _ _ => none

/-- **All written places have that reader.** -/
theorem addrs_written : ∀ p ∈ placesW, p.addrs = addrsW := by
  intro p hp
  unfold placesW at hp
  unfold addrsW
  cases hP : IM.prepW with
  | none =>
    rw [hP] at hp
    cases hp
  | some P =>
    rw [hP] at hp
    obtain ⟨sp, _, rfl⟩ := List.mem_map.1 hp
    rfl

/-- The switches' own seats, off the written places. -/
def ownSeatsW : List (Addr × Nat × Nat) :=
  placesW.map fun p => (⟨p.place, 0⟩, p.link, 1 + p.sizes.kept.length)

/-- The seat of a switch's own message, at the written shape. -/
def switchSeatW : MsgAddr → Option (Nat × Nat) := seatBy proofSizedFull.request ownSeatsW

/-- The address has a seat among the switches' own. -/
def mineSwitchW (a : MsgAddr) : Bool := (switchSeatW a).isSome

/-- It has none, and its sender is the opening's. -/
def mineFirstW (a : MsgAddr) : Bool := !mineSwitchW a && a.sender == K1.firstAddr

/-- The switches' own data at the written plan, over the sizes' twin. -/
def switchDataL (S : Sz) : RowData :=
  laidData proofSizedFull.codes proofSizedFull.request layoutFull switchSeatW (fun _ => 0)
    (cellsValsL S)

/-- The opening's data at the written plan, over the sizes' twin. -/
def firstFillL (S : Sz) : RowData :=
  laidData proofSizedFull.codes proofSizedFull.request layoutFull
    (K1.firstSeat proofSizedFull.request 0) (fun _ => 0) (cellsValsL S)

/-- `ownShare` at the written terms. -/
def ownShareL (S : Sz) (p : SwitchPlace) : Bool :=
  (p.others.toList.take (p.others.size - 1)).zipIdx.all fun n =>
    mineSwitchW (p.ownAddr n.2) &&
      arraysLaidLight (switchDataL S) layoutFull p.sizes.codes n.1.shape p.link n.2
        (p.ownAddr n.2) &&
      (switchDataL S).readyAt [] (p.ownAddr n.2)

/-! ## 3 The four, by Lean's kernel -/

set_option maxRecDepth 1000000 in
/-- **Every own message of every written segment has an address.** -/
theorem addressedW : addressedBy addrsW segsW = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with no address the test says no. -/
theorem addressedW_can_fail : addressedBy (fun _ _ => none) segsW = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The light test at the switches' own data, at all written segments.** -/
theorem switchesW : lightBy (switchDataL Sz.ref) mineSwitchW layoutFull addrsW segsW = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the small example's sizes it says no: so some address is a switch's. -/
theorem switchesW_can_fail :
    lightBy (switchDataL Sz.small) mineSwitchW layoutFull addrsW segsW = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The light test at the opening's data, at all written segments.** -/
theorem openingW : lightBy (firstFillL Sz.ref) mineFirstW layoutFull addrsW segsW = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the data that lay nothing it says no: so some address is the opening's, and the
layout lays an array into its message. -/
theorem openingW_can_fail :
    lightBy RowData.empty mineFirstW layoutFull addrsW segsW = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Each written switch's own sending's share.** -/
theorem ownSharesW : (placesW.all (ownShareL Sz.ref)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the small example's sizes it says no. -/
theorem ownSharesW_can_fail : (placesW.all (ownShareL Sz.small)) = false := by decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lightBy
#print axioms ProofFile.Honest.K2.Law.addressedBy
#print axioms ProofFile.Honest.K2.Law.lightAt_by
#print axioms ProofFile.Honest.K2.Law.addressed_by
#print axioms ProofFile.Honest.K2.Law.zipIdx_take_mem
#print axioms ProofFile.Honest.K2.Law.lightBy_take
#print axioms ProofFile.Honest.K2.Law.addressedBy_take
#print axioms ProofFile.Honest.K2.Law.addrsW
#print axioms ProofFile.Honest.K2.Law.addrs_written
#print axioms ProofFile.Honest.K2.Law.ownSeatsW
#print axioms ProofFile.Honest.K2.Law.switchSeatW
#print axioms ProofFile.Honest.K2.Law.mineSwitchW
#print axioms ProofFile.Honest.K2.Law.mineFirstW
#print axioms ProofFile.Honest.K2.Law.switchDataL
#print axioms ProofFile.Honest.K2.Law.firstFillL
#print axioms ProofFile.Honest.K2.Law.ownShareL
#print axioms ProofFile.Honest.K2.Law.addressedW
#print axioms ProofFile.Honest.K2.Law.addressedW_can_fail
#print axioms ProofFile.Honest.K2.Law.switchesW
#print axioms ProofFile.Honest.K2.Law.switchesW_can_fail
#print axioms ProofFile.Honest.K2.Law.openingW
#print axioms ProofFile.Honest.K2.Law.openingW_can_fail
#print axioms ProofFile.Honest.K2.Law.ownSharesW
#print axioms ProofFile.Honest.K2.Law.ownSharesW_can_fail
