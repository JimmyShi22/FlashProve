-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchPublic.lean: the closing of a segment (K10): the public fields of the record
`TieBySwitch` (Pay/XchTieBySwitch.lean) and of `FreshBySwitch` (Pay/XchFreshField.lean), at the written segments and the written
places of the code switch (`segsW`, `placesW`, Honest/K2/Law/PlacesWritten.lean).

  `pubTest`, `pub_written`   by Lean's kernel, at segments 1 to 24: the written list of places has a place p of that link; the
                    written segment's sizes are p's, field by field; its first sending is the switch's list of messages; its
                    count of the fold's row variables is p's; no message of the sending has main rows and no sample; the
                    sending holds a message
  `pub_bent`          THE TEST CAN FAIL: held against the segment behind, it rejects at every link
  `first_written`     every written segment's first sending holds a message · `segs_count`: there are 25
  `gamTest`, `gam_written`   the challenges of the folds of the segments in front of link l have numbers below the count of rounds
                    in front of the switch into l, off the written cut
  **`pub_at`**          what `pub_written` says at one link, as equations
  **`lot_last`**, **`lot_front`**   where the segments are the written ones and the closing's link is l: the last of the job's segments is
                    the written segment l; those in front are the first l

Limits. Written values alone, at the full size; that the head's segments and places are the written ones is
`segments_at_head`, `places_at_head` (same file of the library), premises here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeStand
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace switchSent segmentsOf NoWord)
open ProofFile.Honest.K2.Law (segsW placesW)

/-- The test at link l, the written segment taken at number j. -/
def pubTest (j l : Nat) : Bool :=
  match placesW.find? (·.link == l), segsW[j]? with
  | some p, some S =>
    decide (S.sizes.codes = p.sizes.codes) && decide (S.sizes.code = p.sizes.code) &&
      decide (S.sizes.maskCode = p.sizes.maskCode) && decide (S.sizes.kept = p.sizes.kept) &&
      decide (S.sizes.target = p.sizes.target) && decide (S.sent.headD #[] = switchSent p.sizes p.others) &&
      decide (S.foldVars = p.foldVars) && K2.noWord (switchSent p.sizes p.others) &&
      decide (0 < (switchSent p.sizes p.others).size)
  | _, _ => false

set_option maxRecDepth 1000000 in
theorem pub_written : ((List.range 24).all fun i => pubTest (i + 1) (i + 1)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail. -/
theorem pub_bent : ((List.range 23).any fun i => pubTest (i + 2) (i + 1)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem first_written : (segsW.all fun S => decide (0 < (S.sent.headD #[]).size)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem segs_count : segsW.length = 25 := by decide +kernel

/-- The folds' challenges of the segments in front of link l lie in front of the switch into l. -/
def gamTest (l : Nat) : Bool :=
  match placesW.find? (·.link == l) with
  | some p => (segsW.take l).all fun S => S.gamma.all fun i =>
      decide (i < roundsW (P5J.At.ps.findIdx (· == p.place)))
  | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem gam_written : ((List.range 24).all fun i => gamTest (i + 1)) = true := by decide +kernel

/-- **What the closed test says at one link.** -/
theorem pub_at {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) :
    ∃ (p : SwitchPlace) (S : SegmentPub), placesW.find? (·.link == l) = some p ∧ segsW[l]? = some S ∧
      S.sizes = p.sizes ∧ S.sent.headD #[] = switchSent p.sizes p.others ∧ S.foldVars = p.foldVars ∧
      NoWord (switchSent p.sizes p.others) ∧ 0 < (switchSent p.sizes p.others).size := by
  have h := List.all_eq_true.1 pub_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at h
  unfold pubTest at h
  cases hp : placesW.find? (·.link == l) with
  | none =>
    rw [hp] at h
    cases h
  | some p =>
    cases hS : segsW[l]? with
    | none =>
      rw [hp, hS] at h
      cases h
    | some S =>
      rw [hp, hS] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h
      refine ⟨p, S, rfl, rfl, ?_, a6, a7, K2.noWord_yes a8, a9⟩
      obtain ⟨⟨c1, c2, c3, c4, c5⟩, _, _, _, _⟩ := S
      obtain ⟨_, _, ⟨d1, d2, d3, d4, d5⟩, _, _, _, _⟩ := p
      obtain rfl : c1 = d1 := a1
      obtain rfl : c2 = d2 := a2
      obtain rfl : c3 = d3 := a3
      obtain rfl : c4 = d4 := a4
      obtain rfl : c5 = d5 := a5
      rfl

/-- The last of the job's segments is the written segment l. -/
theorem lot_last {Zp : ProofFile.Pub} {Gr : ProofFile.Ground} {Qc : Par} {l : Nat} (hS : segmentsOf Zp Gr = segsW)
    (hQ : Qc.link = l) (hl : l < 25) : (lotSegs Zp Gr Qc).getLast? = segsW[l]? := by
  have eS : lotSegs Zp Gr Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Gr).take (Qc.link + 1) = _
    rw [hS, hQ]
  have hlen : (segsW.take (l + 1)).length = l + 1 := by
    rw [List.length_take, segs_count]
    omega
  rw [eS, List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel, List.getElem?_take_of_lt (Nat.lt_succ_self l)]

/-- Those in front are the first l. -/
theorem lot_front {Zp : ProofFile.Pub} {Gr : ProofFile.Ground} {Qc : Par} {l : Nat} (hS : segmentsOf Zp Gr = segsW)
    (hQ : Qc.link = l) (hl : l < 25) : (lotSegs Zp Gr Qc).dropLast = segsW.take l := by
  have eS : lotSegs Zp Gr Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Gr).take (Qc.link + 1) = _
    rw [hS, hQ]
  have hlen : (segsW.take (l + 1)).length = l + 1 := by
    rw [List.length_take, segs_count]
    omega
  rw [eS, List.dropLast_eq_take, hlen, Nat.add_sub_cancel, List.take_take, Nat.min_eq_left (Nat.le_succ l)]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.pub_written
#print axioms ProofFile.Honest.K10.pub_bent
#print axioms ProofFile.Honest.K10.first_written
#print axioms ProofFile.Honest.K10.segs_count
#print axioms ProofFile.Honest.K10.gam_written
#print axioms ProofFile.Honest.K10.pub_at
#print axioms ProofFile.Honest.K10.lot_last
#print axioms ProofFile.Honest.K10.lot_front
