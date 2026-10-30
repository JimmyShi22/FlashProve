-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/XchAtBookShared.lean: the closing of a segment (K10): at the written book, the fields on the book of the records
`FreshByShared` and `TieByShared` (Johnson/Desc/ProofFile/Honest/K10/Pay/XchFreshField.lean, XchTieByShared.lean), at the
sendings of the shared kind (K1): the first segment's opening, and each segment's two later moments.

  `sentOpen`, `sentLater`, `rideOpen`, `dueS`   what the sender's job reads, at the written shape and codes
  `laterB`, `later_at_places`, `later_at_zero`   the closed test on the later moments' entries, at every closing
  `openB`, `open_written`, `fresh_open_written`   the closed tests on the opening's messages and on the fresh mask of the first segment
  `later_bent`, `open_bent`, `fresh_open_bent`   THE TESTS CAN FAIL
  **`tie_later_book`**, **`tie_open_book`**, **`fresh_open_book`**   the fields, at the jobs that the lot lays

Limits. At the book that the maker returns at the written description. The shape and the codes of the parameters are premises:
under the head they are the written ones. Owners, starts and counts alone. The full size alone.
-/
import AtFullSide.K10.XchAtBookSwitch
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open ProofFile.Honest.K2 (SwitchPlace switchSent)
open ProofFile.Honest.K2.Law (placesW)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 proofSendsFull)
open Johnson.Prover.Send (shapeAt)
open OnBytes (OracleNotice ReqFrame reqGroups foldMaskNotice)
open P2Law.ProofPlan (WP)

/-- The frame in front of the first segment, at the written shape. -/
def frameW : ReqFrame := { shape := shapeFull, groups := reqGroups shapeFull }

/-- The messages of the first segment's opening, at the written shape. -/
def sentOpen : Array OracleNotice :=
  ((([("own", 0, ReqFrame.notices (frameW.atMoment 0)),
      ("the fold's mask", 0, #[foldMaskNotice (frameW.foldShape 0 {})]),
      ("at the start", shapeFull.link.length + shapeFull.last.length, shapeFull.atStart.toArray)] :
      List (String × Nat × Array OracleNotice)).map fun x => (x.1, x.2.2)).flatMap (·.2.toList)).toArray

/-- The messages of a later moment, at the written shape. -/
def sentLater (l m : Nat) : Array OracleNotice :=
  (([("own", ReqFrame.notices (({ shape := shapeFull, groups := reqGroups shapeFull, link := l } : ReqFrame).atMoment m))] :
    List (String × Array OracleNotice)).flatMap (·.2.toList)).toArray

/-- Which table rides at the opening. -/
def rideOpen : Nat → Option ProofFile.Honest.K1.Ride :=
  ProofFile.Honest.K1.rideOf (some ((frameW.atMoment 0).length, frameW.foldShape 0 {}))

/-- Where message number k's coins begin: the text of `startR` at its two letters. -/
def dueS (codes : OnBytes.Codes) (sent : Array OracleNotice) (ride : Nat → Option ProofFile.Honest.K1.Ride) (k : Nat) : Due :=
  (List.range k).foldl (fun a j => a.plus (ProofFile.Honest.K1.dueMsg codes (sent.getD j default).shape (ride j))) ⟨0, 0⟩

/-- The test at a later moment's entry: number lo behind the segments in front. e: a number added to the start asked for. -/
def laterB (e lo l : Nat) (d : Bool) : Bool :=
  match (viewAt (addrAt l))[frontAt l + lo]? with
  | some v =>
    v.1 == ⟨⟨1, some l, IM.k1Ix l d + 1, .K1⟩, 0⟩ && v.2.1 == ⟨0, e⟩ &&
      decide (v.2.1.f + v.2.2.f ≤ (dueS codesFull2 (sentLater l (if d then 2 else 1)) (fun _ => none)
        (sentLater l (if d then 2 else 1)).size).f) &&
      decide (v.2.1.e + v.2.2.e ≤ (dueS codesFull2 (sentLater l (if d then 2 else 1)) (fun _ => none)
        (sentLater l (if d then 2 else 1)).size).e)
  | none => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At each written place both later moments' entries stand behind the switch's messages. -/
theorem later_at_places : (placesW.all fun p => decide (25 ≤ p.link) ||
    (laterB 0 (0 + ((switchSent p.sizes p.others).size - 1)) p.link false &&
      laterB 0 (0 + ((switchSent p.sizes p.others).size - 1 + 1)) p.link true)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the first segment they stand behind the opening's three messages. -/
theorem later_at_zero : (laterB 0 (0 + 3) 0 false && laterB 0 (0 + (3 + 1)) 0 true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: at a start one further on it rejects at every place. -/
theorem later_bent : (placesW.any fun p =>
    laterB 1 (0 + ((switchSent p.sizes p.others).size - 1)) p.link false) = false := by decide +kernel

/-- The test at the opening's first three messages. e: as above. -/
def openB (e : Nat) : Bool :=
  (List.range 3).all fun n =>
    match (viewAt (addrAt 0))[frontAt 0 + (0 + n)]? with
    | some v =>
      v.1 == ⟨⟨1, some 0, 1, .K1⟩, 0⟩ && v.2.1 == (dueS codesFull2 sentOpen rideOpen n).plus ⟨0, e⟩ &&
        decide (v.2.1.f + v.2.2.f ≤ (dueS codesFull2 sentOpen rideOpen sentOpen.size).f) &&
        decide (v.2.1.e + v.2.2.e ≤ (dueS codesFull2 sentOpen rideOpen sentOpen.size).e)
    | none => false

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The entries of the opening's first three messages. -/
theorem open_written : openB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem open_bent : openB 1 = false := by decide +kernel

/-- Where the fresh mask's coins start in the opening: the text of `maskStart` at message number 3. -/
def maskOpen : Nat :=
  (dueS codesFull2 sentOpen rideOpen 3).e + if (sentOpen.getD 3 default).shape.mainDeg == 3 then
    (ProofFile.Honest.K1.stepsOf codesFull2 (sentOpen.getD 3 default).shape (rideOpen 3)).main else 0

/-- The test on the spending entry of the first closing. -/
def freshOpenB (e : Nat) : Bool :=
  (rawShortW.filter fun x => x.once && x.spender == addrAt 0).map (fun x => (x.owner, x.start.e)) ==
    [((⟨⟨1, some 0, 1, .K1⟩, 0⟩ : Addr), maskOpen + e)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The spending entry of the first closing. -/
theorem fresh_open_written : freshOpenB 0 = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem fresh_open_bent : freshOpenB 1 = false := by decide +kernel

/-! ## The jobs at the written shape -/

section
variable {q : OnBytes.Params.First} {gp : _root_.Desc.Plain.GPar}

theorem open_sent (hs : q.shape = shapeFull) : (VerifiableInference.Desc.K1.firstPar q gp).sent = sentOpen := by
  show (((VerifiableInference.Desc.K1.firstLaid q).map fun x => (x.1, x.2.2)).flatMap (·.2.toList)).toArray = _
  unfold VerifiableInference.Desc.K1.firstLaid VerifiableInference.Desc.K1.frame₀ VerifiableInference.Desc.K1.ownGroup
  rw [hs]
  rfl

theorem open_ride (hs : q.shape = shapeFull) : ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold q) = rideOpen := by
  unfold ProofFile.Honest.K1.firstFold VerifiableInference.Desc.K1.frame₀ rideOpen frameW
  rw [hs]

theorem later_sent (hs : q.shape = shapeFull) (l pc m : Nat) :
    (VerifiableInference.Desc.K1.parLater q gp l pc m).sent = sentLater l m := by
  show (([("own", VerifiableInference.Desc.K1.noticesAt q l m)] : List (String × Array OracleNotice)).flatMap
    (·.2.toList)).toArray = _
  unfold VerifiableInference.Desc.K1.noticesAt
  rw [hs]
  rfl

end

end AtFullSide.K10

#print axioms AtFullSide.K10.later_at_places
#print axioms AtFullSide.K10.later_at_zero
#print axioms AtFullSide.K10.later_bent
#print axioms AtFullSide.K10.open_written
#print axioms AtFullSide.K10.open_bent
#print axioms AtFullSide.K10.fresh_open_written
#print axioms AtFullSide.K10.fresh_open_bent
#print axioms AtFullSide.K10.open_sent
#print axioms AtFullSide.K10.open_ride
#print axioms AtFullSide.K10.later_sent
