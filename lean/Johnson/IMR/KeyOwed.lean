-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyOwed.lean: WHO STANDS IN A KEY FILE's DESCRIPTION's THREE FLAT LISTS,
AS Block.lean's beforesOf SEES THEM: for each sub-protocol that the table «owed» names: its place,
whether one of its rounds draws, and what it names in «before»: GENERAL IN X N P: no evaluation.
For the row r6 (owedOk) of KeyBackOfRows.lean.

WHAT IS SAID.
  tripOf b · beforesOf_map     what beforesOf keeps of a sub-protocol.
  trip_of_back · trip_of_hear · trip_of_retype_back   a sub-protocol of a chain's back, or heard in
                   one of its links, stands in the chain's flat list with these three unchanged.
  k12_before_at · test_trip    the proximity test's sub-protocol at a place's numbers names
                   beforeOf chain nums; the like of k12_rounds_at
                   (Johnson/HB/LLHARD/KB8/Laws.lean), by its steps.
  look_trip · ranges_trip · batt_trip · shared_trip · gu_trip · gomega_trip · own_trip   **the ten
                   that the table names.** batt_trip: THE BATCHING OF THE ROWS ON THE TABLE NAMES
                   THE TREES 0 … sent − 1 OF CHAIN 1, WITH sent := rootsBefore D (batchRound D): IT
                   READS THE DECLARED ROUNDS AS HANDED IN.
  all_any_mono     a tool: a list that holds more says yes where a list that holds less does.
What is not claimed. Any number. That owedOk says yes: IMR/KeyOwedFull.lean. No soundness.

-/
import Johnson.IMR.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Johnson.KB8
open Lk6.AtPlan (keyFull)
open _root_.Desc.K14.Law (p12At_place k12_place)

variable {S Cl Cl' : Type}

/-- What Block.lean's beforesOf keeps of a sub-protocol: its place, whether one of its rounds draws,
and what it names in «before». -/
def tripOf (b : Block S Cl) : Place × Bool × List (Nat × Nat) :=
  (b.place, b.rounds.any drawsAny, b.before)

theorem beforesOf_map (bs : List (Block S Cl)) : beforesOf bs = bs.map tripOf := rfl

/-! ## Who stands in a chain's flat list -/

theorem trip_of_back (c : Chain S Cl) {b : Block S Cl} (hb : b ∈ c.back) :
    tripOf b ∈ beforesOf c.blocksInOrder := by
  have h : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl) ∈ c.blocksInOrder :=
    List.mem_append_left _ (List.mem_append_right _
      (List.mem_map_of_mem (f := fun b : Block S Cl => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }) hb))
  have h' := List.mem_map_of_mem (f := tripOf) h
  exact h'

theorem trip_of_hear (c : Chain S Cl) {L : Link S Cl} (hL : L ∈ c.links) {b : Block S Cl}
    (hb : b ∈ L.hear) : tripOf b ∈ beforesOf c.blocksInOrder := by
  have h1 : b ∈ L.blocksInOrder :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ hb)))
  have h2 : b ∈ c.blocksInOrder :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨L, hL, h1⟩)))
  exact List.mem_map_of_mem (f := tripOf) h2

theorem trip_of_retype_back (c : Chain S Cl) {b : Block S Cl} (hb : b ∈ c.back) :
    tripOf b ∈ beforesOf (c.retype : Chain S Cl').blocksInOrder :=
  trip_of_back (c.retype : Chain S Cl') (b := b.retype) (List.mem_map_of_mem hb)

/-! ## The proximity test's «before» -/

/-- What a proximity test's sub-protocol names in «before», at a place's numbers. The like of
k12_rounds_at (Johnson/HB/LLHARD/KB8/Laws.lean), whose steps these are. -/
theorem k12_before_at {T : Type} (X : K12.Parts T) {place : Place} {x : H2U.PlaceNums}
    {rs : List Fmt.DeclaredRound} (hc : place.chain = x.chain)
    (hr : H2U.roundsOfNums x.nums = some rs) :
    (K12.proximityTestKind X (H2U.proximityTestParametersAt place x) : Block T Cl).before = H2U.beforeOf x.chain x.nums ∧
      (H2U.proximityTestParametersAt place x).before = H2U.beforeOf x.chain x.nums := by
  obtain ⟨s, rest, hs⟩ := stages_of_rounds hr
  obtain ⟨os, ho⟩ : ∃ os, H2U.testOracles5 x.nums x.firstGroup = some os :=
    ⟨_, by unfold H2U.testOracles5; rw [hr]; rfl⟩
  obtain ⟨os', ho'⟩ : ∃ os', H2U.testOracles x.nums = some os' :=
    ⟨_, by unfold H2U.testOracles; rw [hr]; rfl⟩
  have e : H2U.proximityTestParametersAt place x = ⟨place, x.nums, x.idx, os, H2U.beforeOf x.chain x.nums, x.answers,
                          x.early⟩ := by
    unfold H2U.proximityTestParametersAt
    rw [hc, ho]
    simp
  rw [e]
  refine ⟨?_, rfl⟩
  unfold K12.proximityTestKind
  split
  · rfl
  · rename_i hno
    exact (hno s rest rs os' hs hr ho').elim

theorem test_trip {T : Type} (X : K12.Parts T) {place : Place} {x : H2U.PlaceNums}
    {rs : List Fmt.DeclaredRound} (hc : place.chain = x.chain)
    (hr : H2U.roundsOfNums x.nums = some rs) :
    tripOf (K12.proximityTestKind X (H2U.proximityTestParametersAt place x) : Block T Cl) =
      (place, rs.any drawsAny, H2U.beforeOf x.chain x.nums) := by
  unfold tripOf
  rw [k12_place, p12At_place, k12_rounds_at X hc hr, (k12_before_at X hc hr).1]

/-! ## The key file's three chains -/

theorem look_trip (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting)
    (N : H2U.PlaceNums) {x : Lookup × Nat} (h : x ∈ (lookupsOf one).zipIdx) :
    ((⟨1, some x.2, 2, .K3⟩ : Place), (lookRounds set x.1).any drawsAny, [(1, 0), (1, 1)]) ∈
      beforesOf (firstChain one D told set N).blocksInOrder :=
  trip_of_hear (firstChain one D told set N) (L := lookupLink one set x.2 x.1)
    (List.mem_map_of_mem (f := fun x : Lookup × Nat => lookupLink one set x.2 x.1) h)
    (b := K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set x.2 x.1))
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem ranges_trip (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting)
    {N : H2U.PlaceNums} {rs : List Fmt.DeclaredRound} (hc : N.chain = 1)
    (hr : H2U.roundsOfNums N.nums = some rs) :
    ((⟨1, none, 5, .K12⟩ : Place), rs.any drawsAny, H2U.beforeOf N.chain N.nums) ∈
      beforesOf (firstChain one D told set N).blocksInOrder := by
  have h := trip_of_back (firstChain one D told set N)
    (b := rangesTest (enterRanges one) leaveRanges N)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have e : tripOf (rangesTest (enterRanges one) leaveRanges N : Block FirstState Key.Claim) =
      tripOf (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt rangesPlace N) : Block K12.T12 Key.Claim) := rfl
  rw [e, test_trip K12.guardedProximityTestParts (place := rangesPlace) hc.symm hr] at h
  exact h

theorem batt_trip (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting)
    (N : H2U.PlaceNums) :
    ((⟨1, none, 13, .K13⟩ : Place), (battRoundsOf one.ranges one.lin).any drawsAny,
        (List.range (rootsBefore D (batchRound D))).map fun n => (1, n)) ∈
      beforesOf (firstChain one D told set N).blocksInOrder := by
  have h := trip_of_back (firstChain one D told set N)
    (b := batchTableRows (·.keys) one pieces (rootsBefore D (batchRound D)))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have e : tripOf (batchTableRows (·.keys) one pieces (rootsBefore D (batchRound D)) :
      Block FirstState Key.Claim) = ((⟨1, none, 13, .K13⟩ : Place),
        (battRoundsOf one.ranges one.lin).any drawsAny,
        (List.range (rootsBefore D (batchRound D))).map fun n => (1, n)) := by
    unfold tripOf
    rw [batch_rounds]
    show (_, _, (([] ++ []) ++ (List.range (rootsBefore D (batchRound D))).map fun n => (1, n)) ++
      []) = _
    rw [List.append_nil]
    rfl
  rw [e] at h
  exact h

theorem shared_trip (c : Model.Verify.Chains) (P : LaterPlaces)
    {b : Block _root_.Desc.K14.St Unit}
    (hb : b ∈ _root_.Desc.K14.blocksOr (par14 c.made.sized.key (beforeSharedPoint P))) :
    tripOf b ∈ beforesOf ((sharedChain c P).retype : Chain _root_.Desc.K14.St Key.Claim).blocksInOrder :=
  trip_of_retype_back (sharedChain c P) (List.mem_append_left _ hb)

theorem gu_trip (c : Model.Verify.Chains) {P : LaterPlaces} {rs : List Fmt.DeclaredRound}
    (hc : P.U.chain = 2) (hr : H2U.roundsOfNums P.U.nums = some rs) :
    ((⟨2, none, 9, .K12⟩ : Place), rs.any drawsAny, H2U.beforeOf P.U.chain P.U.nums) ∈
      beforesOf ((sharedChain c P).retype : Chain _root_.Desc.K14.St Key.Claim).blocksInOrder := by
  have h := trip_of_retype_back (Cl' := Key.Claim) (sharedChain c P)
    (b := K12.Seat.onGu (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)))
    (List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_self ..)))
  have e : tripOf (K12.Seat.onGu (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U))) =
      tripOf (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block K12.T12 Unit) := rfl
  rw [e, test_trip K12.guardedProximityTestParts (place := ⟨2, none, 9, .K12⟩) hc.symm hr] at h
  exact h

theorem gomega_trip (c : Model.Verify.Chains) {P : LaterPlaces} {O : H2U.PlaceNums}
    {rs : List Fmt.DeclaredRound} (hO : P.O = some O) (hc : O.chain = 2)
    (hr : H2U.roundsOfNums O.nums = some rs) :
    ((⟨2, none, 10, .K12⟩ : Place), rs.any drawsAny, H2U.beforeOf O.chain O.nums) ∈
      beforesOf ((sharedChain c P).retype : Chain _root_.Desc.K14.St Key.Claim).blocksInOrder := by
  have hm : K12.Seat.onGomega (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O)) ∈
      sharedTests P := by
    unfold sharedTests
    rw [hO]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have h := trip_of_retype_back (Cl' := Key.Claim) (sharedChain c P)
    (List.mem_append_right _ hm)
  have e : tripOf (K12.Seat.onGomega (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O))) =
      tripOf (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ O) : Block K12.T12 Unit) := rfl
  rw [e, test_trip K12.guardedProximityTestParts (place := ⟨2, none, 10, .K12⟩) hc.symm hr] at h
  exact h

theorem own_trip (c : Model.Verify.Chains) {P : LaterPlaces} {rs : List Fmt.DeclaredRound}
    (hc : P.W.chain = 3) (hr : H2U.roundsOfNums P.W.nums = some rs) :
    ((⟨3, none, 2, .K12⟩ : Place), rs.any drawsAny, H2U.beforeOf P.W.chain P.W.nums) ∈
      beforesOf ((thirdChain c P).retype : Chain Third.S₃ Key.Claim).blocksInOrder := by
  have h := trip_of_retype_back (Cl' := Key.Claim) (thirdChain c P)
    (b := Third.ownAt (ownTest P)) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have t := test_trip (Cl := Unit) K12.guardedProximityTestParts (place := ⟨3, none, 2, .K12⟩) hc.symm hr
  have e : tripOf (Third.ownAt (ownTest P)) =
      (({ (tripOf (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
          Block K12.T12 Unit)).1 with chain := 3, link := none, piece := 2 } : Place),
        (tripOf (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
          Block K12.T12 Unit)).2) := rfl
  rw [e, t] at h
  exact h

/-- A list that holds more says yes where a list that holds less does. -/
theorem all_any_mono {α β : Type} (p : α → β → Bool) (l : List α) (A B : List β)
    (hAB : ∀ t ∈ A, t ∈ B) (h : (l.all fun r => A.any (p r)) = true) :
    (l.all fun r => B.any (p r)) = true := by
  rw [List.all_eq_true] at h ⊢
  intro r hr
  obtain ⟨t, ht, hp⟩ := List.any_eq_true.1 (h r hr)
  exact List.any_eq_true.2 ⟨t, hAB t ht, hp⟩

end IM

#print axioms IM.beforesOf_map
#print axioms IM.trip_of_back
#print axioms IM.trip_of_hear
#print axioms IM.trip_of_retype_back
#print axioms IM.k12_before_at
#print axioms IM.test_trip
#print axioms IM.look_trip
#print axioms IM.ranges_trip
#print axioms IM.batt_trip
#print axioms IM.shared_trip
#print axioms IM.gu_trip
#print axioms IM.gomega_trip
#print axioms IM.own_trip
#print axioms IM.all_any_mono
