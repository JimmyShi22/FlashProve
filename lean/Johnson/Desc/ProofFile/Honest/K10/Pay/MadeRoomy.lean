-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeRoomy.lean: at the written plan's segments behind the first, by Lean's kernel, four
segments to a declaration: the switch's sizes fit (`Sizes.roomy`), and the carrying message has room. So the job's public test
`segsRoomy` (Honest/K10/SegmentClosing.lean) says yes at every first part of the list.

  `oneRoomy`        the test at one segment
  `roomy_each`      it says yes at each segment behind the first
  `roomy_at`, `roomy_take`   what `groupRows_ok` and the job ask, at a first part of the list

Limits. Closed facts. The full size alone.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K10.SegmentClosing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2 (SegmentPub)
open ProofFile.Honest.K2.Law (segsW)

/-- The test at one segment behind the first. -/
def oneRoomy (S : SegmentPub) : Bool :=
  S.sizes.roomy && (S.sizes.serves &&
    decide ((VerifiableInference.Desc.K2.Honest.rest S.sizes noLeft).length ≤
      (OnBytes.SwitchPlaces.make S.sizes.codes S.sizes.target).size) &&
    decide ((S.sizes.codes.base.getD S.sizes.code default).ell ≤
      (S.sizes.codes.base.getD S.sizes.target.shape.code default).ell * 2 ^ S.sizes.target.main.bits))

set_option maxRecDepth 10000000 in
/-- The written plan has 25 segments. -/
theorem segs_len : segsW.length = 25 := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_1 : ((List.range' 1 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_2 : ((List.range' 5 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_3 : ((List.range' 9 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_4 : ((List.range' 13 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_5 : ((List.range' 17 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem roomy_6 : ((List.range' 21 4).all fun i => (segsW[i]?).all oneRoomy) = true := by decide +kernel

/-- The test says yes at each segment behind the first. -/
theorem roomy_each {i : Nat} {S : SegmentPub} (h : segsW[i]? = some S) (hi : i ≠ 0) : oneRoomy S = true := by
  have hlt : i < 25 := by
    have := (List.getElem?_eq_some_iff.1 h).1
    rwa [segs_len] at this
  have one : (segsW[i]?).all oneRoomy = true := by
    have c : (1 ≤ i ∧ i < 5) ∨ (5 ≤ i ∧ i < 9) ∨ (9 ≤ i ∧ i < 13) ∨ (13 ≤ i ∧ i < 17) ∨ (17 ≤ i ∧ i < 21) ∨
        (21 ≤ i ∧ i < 25) := by omega
    rcases c with c | c | c | c | c | c
    · exact List.all_eq_true.1 roomy_1 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
    · exact List.all_eq_true.1 roomy_2 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
    · exact List.all_eq_true.1 roomy_3 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
    · exact List.all_eq_true.1 roomy_4 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
    · exact List.all_eq_true.1 roomy_5 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
    · exact List.all_eq_true.1 roomy_6 i (List.mem_range'_1.2 ⟨c.1, by omega⟩)
  rw [h] at one
  exact one

theorem of_take {n i : Nat} {S : SegmentPub} (h : (segsW.take n)[i]? = some S) : segsW[i]? = some S := by
  rw [List.getElem?_take] at h
  split at h
  · exact h
  · cases h

/-- What `groupRows_ok` asks, at a first part of the list. -/
theorem roomy_at (n i : Nat) (S : SegmentPub) (h : (segsW.take n)[i]? = some S) (hi : i ≠ 0) :
    S.sizes.roomy = true :=
  (Bool.and_eq_true _ _ ▸ roomy_each (of_take h) hi).1

/-- What the job asks, at a first part of the list. -/
theorem roomy_take (n : Nat) : segsRoomy (segsW.take n) = true := by
  unfold segsRoomy
  rw [List.all_eq_true]
  intro S hS
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hS
  have e : (segsW.take n)[1 + j]? = some ((segsW.take n).drop 1)[j] := by
    rw [← List.getElem?_drop]
    exact List.getElem?_eq_getElem hj
  exact (Bool.and_eq_true _ _ ▸ roomy_each (of_take e) (by omega)).2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.oneRoomy
#print axioms ProofFile.Honest.K10.segs_len
#print axioms ProofFile.Honest.K10.roomy_1
#print axioms ProofFile.Honest.K10.roomy_2
#print axioms ProofFile.Honest.K10.roomy_3
#print axioms ProofFile.Honest.K10.roomy_4
#print axioms ProofFile.Honest.K10.roomy_5
#print axioms ProofFile.Honest.K10.roomy_6
#print axioms ProofFile.Honest.K10.roomy_each
#print axioms ProofFile.Honest.K10.of_take
#print axioms ProofFile.Honest.K10.roomy_at
#print axioms ProofFile.Honest.K10.roomy_take
