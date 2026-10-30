-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchOwnAt.lean: the closing of a segment (K10): the two clauses on data in the field stand of
`TieBySwitch` (Pay/XchTieBySwitch.lean), at a place of the code switch.

  **`own_front_at`**   the own main rows of a segment in front: the closing's job's, at all that it has heard, are the switch's
                   closing's, at the challenges in front of the switch. Premises: p is a place of the kind; the count of challenges
                   that the data of an own message of that segment read is no more than fx (hD1); fx challenges have been heard
  `ownTest`, `own_written`, `own_bent`   by Lean's kernel, at links 1 to 24, at each message n of the switch's sending behind the
                   carrying message and the copies, but the last: the written place's address of the segment's own message number
                   n − 1 − (copies) is the switch's own address of that number, and the written segment's shape of it is the shape
                   in the switch's list "others". THE TEST CAN FAIL: asked of the own message one further on, it rejects at every
                   link
  **`own_now_at`**     the segment's own main rows of moment 0: the closing's job's are the switch's own. Premises: the segments are
                   the written ones; p is the written place of link l and a place of the kind; the data of a switch's own message,
                   the last message apart, read no challenge (hzero)

By: `ownBy_front`, `ownBy_sender` (Pay/XchData.lean); `addrs_of_place` (Pay/MadeReady.lean).

Limits. hD1 and hzero are premises on the filling. Written values at the full size.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchData
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchPublic
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeReady

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace switchSent switchPlaces segmentsOf ownBy)
open ProofFile.Honest.K2.Law (senderOwn segsW placesW)

variable {W₀ Rc Xi Tr : Type}

/-- **The own main rows of a segment in front.** -/
theorem own_front_at (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) {Zp : ProofFile.Pub} {Gr : ProofFile.Ground}
    (Qc : Par) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Gr) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) {fx : Nat}
    (hfx : fx ≤ heard.length) {i : Nat} {S : SegmentPub} (hi : (lotSegs Zp Gr Qc).dropLast[i]? = some S)
    (hD1 : ∀ m a, p.addrs (0 + i) m = some a → (rows w.x).heardAt a ≤ fx) :
    lotOwn readers rows Zp Gr Qc w heard (0 + i) =
      ownBy (rows w.x) (readers w) p.addrs
        (fun s m' => ((((segmentsOf Zp Gr)[s]?).map (·.ownShapes (s == 0))).getD []).getD m' {}) (heard.take fx)
        (0 + i) := by
  have hlt : 0 + i < Qc.link + 1 := by
    have h1 := (List.getElem?_eq_some_iff.1 hi).1
    rw [List.length_dropLast, List.length_take] at h1
    omega
  refine ownBy_front _ _ _ _ _ _ heard fx (0 + i) (addrs_of_place hp).symm ?_ hD1 hfx
  funext m'
  show ((((segmentsOf Zp Gr).take (Qc.link + 1))[0 + i]?.map (·.ownShapes (0 + i == 0))).getD []).getD m' {} = _
  rw [List.getElem?_take_of_lt hlt]

/-- The test at link l. d: a number added to the own message's number on the job's side: 0 in the test. -/
def ownTest (d l : Nat) : Bool :=
  match placesW.find? (·.link == l), segsW[l]? with
  | some p, some S =>
    (List.range ((switchSent p.sizes p.others).size - 1)).all fun n =>
      decide (n ≤ p.sizes.kept.length) ||
        (decide (p.addrs l (n - 1 - p.sizes.kept.length + d) = some (p.ownAddr (n - 1 - p.sizes.kept.length))) &&
          decide ((S.ownShapes (l == 0)).getD (n - 1 - p.sizes.kept.length + d) {} =
            (p.others.getD (n - 1 - p.sizes.kept.length) default).shape))
  | _, _ => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem own_written : ((List.range 24).all fun i => ownTest 0 (i + 1)) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem own_bent : ((List.range 24).any fun i => ownTest 1 (i + 1)) = false := by decide +kernel

/-- **The segment's own main rows of moment 0.** -/
theorem own_now_at (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) {Zp : ProofFile.Pub} {Gr : ProofFile.Ground}
    {Qc : Par} {l : Nat} (hS : segmentsOf Zp Gr = segsW) (hQ : Qc.link = l) (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Gr) (hpw : placesW.find? (·.link == l) = some p) (w : Local W₀ Rc Xi Tr)
    (heard : List Fmt.Drawn)
    (hzero : ∀ m, 1 + p.sizes.kept.length + m + 1 < (switchSent p.sizes p.others).size →
      (rows w.x).heardAt (p.ownAddr m) = 0) :
    ∀ n, n + 1 < (switchSent p.sizes p.others).size → p.sizes.kept.length < n →
      lotOwn readers rows Zp Gr Qc w heard ((lotSegs Zp Gr Qc).length - 1) (n - 1 - p.sizes.kept.length) =
        senderOwn (rows w.x) (readers w) p (n - 1 - p.sizes.kept.length) := by
  intro n hn hk
  have eS : lotSegs Zp Gr Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Gr).take (Qc.link + 1) = _
    rw [hS, hQ]
  have hlen : (lotSegs Zp Gr Qc).length - 1 = l := by
    rw [eS, List.length_take, segs_count]
    omega
  have ht := List.all_eq_true.1 own_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at ht
  unfold ownTest at ht
  rw [hpw] at ht
  cases hSl : segsW[l]? with
  | none =>
    rw [hSl] at ht
    cases ht
  | some S =>
    rw [hSl] at ht
    have h3 := List.all_eq_true.1 ht n (List.mem_range.2 (by omega))
    rw [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, Nat.add_zero] at h3
    obtain ⟨a1, a2⟩ := h3.resolve_left (by omega)
    rw [hlen]
    refine ownBy_sender _ _ _ _ heard p l _ ?_ ?_ (hzero _ (by omega))
    · rw [← addrs_of_place hp]
      exact a1
    · show ((((lotSegs Zp Gr Qc)[l]?).map (·.ownShapes (l == 0))).getD []).getD _ {} = _
      rw [eS, List.getElem?_take_of_lt (Nat.lt_succ_self l), hSl]
      exact a2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.own_front_at
#print axioms ProofFile.Honest.K10.own_written
#print axioms ProofFile.Honest.K10.own_bent
#print axioms ProofFile.Honest.K10.own_now_at
