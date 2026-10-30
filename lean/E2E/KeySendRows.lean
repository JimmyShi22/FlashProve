-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySendRows.lean: what the honest side's part of a sending lays into the main rows at two of the
jobs of E2E/KeySendJobs.lean: the data, and no coin. Statements and proofs.

What is shown.
  `rowsR_mainF`, `rowsR_mainE`: for a message that gets an OOD sample and has a mask row (so that
    its pad lies in a mask row): an entry of a main row, within the rows and the code's message
    length, is the caller's datum there, or 0 where there is none. General in the place, over the
    base field and over the extension field. (`rowsR`: Johnson/Desc/ProofFile/Honest/K1/Coins.lean.)
  **`msg_rows`**: so at the job of the multiplicities, at every coin, at both of the part's rounds:
    the entry at (main row r, place j) of message 0 is `planesData`'s bit there, 0 where no block of
    planes lies.
  **`msg_val`**: so the main table that the part lays, numbered as the library numbers it (row in
    the low bits), and spelled in machine words, is the honest array `planesVal` of
    E2E/KeyPlanesRead.lean: the array at which `bitVec_read`, `midPs` and their kin are stated.
  **`w_rows`**: at W's job: the entry at (r, j) of message 0 is W's entry there by the library's own
    layout of W (`linLayW`, through `laidE`, Johnson/Prover/Send/Core.lean).

Limits. The main rows' entries alone: nothing on mask rows, pads, encoding randomness, columns,
trees or OOD answers. The three premises on the message's shape are premises; at the written sizes
of the key they are evaluated in the two tests at the end, by Lean's evaluator, outside the kernel.
Nothing on hiding follows from
this file.


-/
import E2E.KeySendJobsTests

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params
open OnBytes.Slice (GF GE readE)
open ProofFile.Honest (Front State Seen Cs)
open ProofFile.Honest.K1 (SendJob Ride rowsR dueR stepsOf)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (K1.Par)
open VerifiableInference.Desc.Key (Pieces weightAt)

/-! ## 1. A main row's entry is the caller's datum -/

section
variable (P : K1.Par) (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
  (c : Cs (dueR P ride)) (k r j : Nat)
  (hans : (shapeAt P k).answers ≠ 0) (hmask : (shapeAt P k).maskRows ≠ 0)
  (hr : r < (shapeAt P k).mainRows) (hj : j < (P.codes.base.getD (shapeAt P k).code default).ell)
include hans hmask hr hj

theorem rowsR_mainF (hdeg : (shapeAt P k).mainDeg ≠ 3) :
    (rowsR P ride data c k).mainF r j =
      match data k r j with
      | some (.inl x) => x
      | _ => 0 := by
  have h1 : ((shapeAt P k).mainDeg == 3) = false := by simpa using hdeg
  have h2 : ((shapeAt P k).answers == 0) = false := by simpa using hans
  have h3 : ((shapeAt P k).maskRows == 0) = false := by simpa using hmask
  have h4 : decide ((shapeAt P k).mainRows ≤ r) = false := by simpa using hr
  have h5 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false := by
    simpa using hj
  simp only [rowsR, stepsOf, h1, h2, h3, h4, h5, Bool.and_false, Bool.false_and, Bool.or_false,
    Bool.false_or, Bool.false_eq_true, if_false, bne_self_eq_false, Option.map_none]
  rcases data k r j with _ | (x | x) <;> rfl

theorem rowsR_mainE (hdeg : (shapeAt P k).mainDeg = 3) :
    (rowsR P ride data c k).mainE r j =
      match data k r j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  have h1 : ((shapeAt P k).mainDeg == 3) = true := by simpa using hdeg
  have h2 : ((shapeAt P k).answers == 0) = false := by simpa using hans
  have h3 : ((shapeAt P k).maskRows == 0) = false := by simpa using hmask
  have h4 : decide ((shapeAt P k).mainRows ≤ r) = false := by simpa using hr
  have h5 : decide ((P.codes.base.getD (shapeAt P k).code default).ell ≤ j) = false := by
    simpa using hj
  simp only [rowsR, stepsOf, h1, h2, h3, h4, h5, Bool.and_false, Bool.false_and, Bool.or_false,
    Bool.false_or, Bool.not_true, Bool.false_eq_true, if_false, bne_self_eq_false, Option.map_none]
  rcases data k r j with _ | (x | x) <;> rfl

end

/-! ## 2. At the jobs -/

section
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)

/-- Message 0 of the second sending is the oracle message of the multiplicities. -/
theorem msg_shape :
    shapeAt (msgJob (X := X) entry one N groups first ride).P 0 = one.ranges.message.shape := by
  unfold shapeAt msgJob VerifiableInference.Desc.Key.sendingPar VerifiableInference.Desc.K1.Par.sent
    Wf.messageOf
  cases one.ranges.stages.head? with
  | none => rfl
  | some t =>
    dsimp only
    split <;> rfl

/-- **What the part lays into the multiplicities' main rows**: the bits, at every coin and at both
of its rounds. -/
theorem msg_rows (hans : one.ranges.message.shape.answers ≠ 0)
    (hmask : one.ranges.message.shape.maskRows ≠ 0) (hdeg : one.ranges.message.shape.mainDeg ≠ 3)
    (c : Cs (dueR (msgJob (X := X) entry one N groups first ride).P ride)) (s : Seen)
    (t : State W X) (n r j : Nat) (hr : r < one.ranges.message.shape.mainRows)
    (hj : j < (one.codes.base.getD one.ranges.message.shape.code default).ell) :
    ((msgJob entry one N groups first ride).rows c s t n 0).mainF r j =
      (planesData (entry t.input) (Wf.matrixOf one.lin).kCol one.ranges.lookups
        (one.codes.base.getD one.ranges.message.shape.code default).ell r j).getD 0 := by
  have e := msg_shape (X := X) entry one N groups first ride
  unfold SendJob.rows
  refine (rowsR_mainF (msgJob (X := X) entry one N groups first ride).P ride _ c 0 r j
    (by rw [e]; exact hans) (by rw [e]; exact hmask) (by rw [e]; exact hr) (by rw [e]; exact hj)
    (by rw [e]; exact hdeg)).trans ?_
  show (match msgData (entry t.input) (Wf.matrixOf one.lin).kCol one.ranges.lookups
      (one.codes.base.getD one.ranges.message.shape.code default).ell 0 r j with
    | some (.inl x) => x
    | _ => 0) = _
  unfold msgData
  rw [if_pos rfl]
  cases planesData (entry t.input) (Wf.matrixOf one.lin).kCol one.ranges.lookups
    (one.codes.base.getD one.ranges.message.shape.code default).ell r j <;> rfl

/-- **The main table that the part lays is the honest array**: at the index i, with the row's number
in the low rb bits, within the rows and the code's message length. -/
theorem msg_val (hans : one.ranges.message.shape.answers ≠ 0)
    (hmask : one.ranges.message.shape.maskRows ≠ 0) (hdeg : one.ranges.message.shape.mainDeg ≠ 3)
    (c : Cs (dueR (msgJob (X := X) entry one N groups first ride).P ride)) (s : Seen)
    (t : State W X) (n rb i : Nat) (hr : i % 2 ^ rb < one.ranges.message.shape.mainRows)
    (hj : i / 2 ^ rb < (one.codes.base.getD one.ranges.message.shape.code default).ell) :
    OnBytes.ofF (OnBytes.Slice.ofF
        (((msgJob entry one N groups first ride).rows c s t n 0).mainF (i % 2 ^ rb) (i / 2 ^ rb))) =
      planesVal (entry t.input) (Wf.matrixOf one.lin).kCol one.ranges.lookups
        (one.codes.base.getD one.ranges.message.shape.code default).ell rb i := by
  rw [msg_rows entry one N groups first ride hans hmask hdeg c s t n _ _ hr hj]
  rfl

/-- The first notice of the message with W is W's. -/
theorem w_first (msg : Array OracleNotice) (h : linMessageW one.lin = some msg) :
    (msg.getD 0 default).shape = one.lin.w := by
  unfold linMessageW at h
  simp only [bind, Option.bind, pure] at h
  by_cases h1 : one.lin.masksAhead = true <;> by_cases h2 : one.lin.ownSplitNeeded = true
  all_goals
    simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at h
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | (cases hm : linMaskNotice one.lin.testOwn one.lin.wLeafClass with
          | none => rw [hm] at h; exact absurd h (by simp)
          | some q => rw [hm] at h; obtain rfl := Option.some.inj h; rfl)

variable (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)

/-- **What the part lays into W's main rows**: W, at every coin and at both of its rounds; the
weights are made of the challenges heard in front of the part. -/
theorem w_rows (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J)
    (hans : one.lin.w.answers ≠ 0) (hmask : one.lin.w.maskRows ≠ 0) (hdeg : one.lin.w.mainDeg = 3)
    (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X) (n r j : Nat)
    (hr : r < one.lin.w.mainRows) (hj : j < (one.codes.base.getD one.lin.w.code default).ell) :
    (J.rows c s t n 0).mainE r j =
      Johnson.Prover.Send.laidE (linLayW one.codes one.lin)
        (wVec one (entry t.input) (wWeights one points a (t.heard.take (t.heard.length - n)))) r
        j := by
  unfold wJob at hJ
  cases hm : linMessageW one.lin with
  | none => rw [hm] at hJ; exact absurd hJ (by simp)
  | some msg =>
    rw [hm] at hJ
    obtain rfl := Option.some.inj hJ
    have e : shapeAt (VerifiableInference.Desc.Key.sendingPar one N.w "W and what rides with it" msg
        groups) 0 = one.lin.w := by
      rw [← w_first one msg hm]
      unfold shapeAt VerifiableInference.Desc.Key.sendingPar VerifiableInference.Desc.K1.Par.sent
      simp
    unfold SendJob.rows
    refine (rowsR_mainE _ ride _ c 0 r j (by rw [e]; exact hans) (by rw [e]; exact hmask)
      (by rw [e]; exact hr) (by rw [e]; exact hj) (by rw [e]; exact hdeg)).trans ?_
    rfl

end

/-! ## 3. The premises on the shapes, at the written sizes of the key -/

#guard Tests.one.ranges.message.shape.answers != 0 &&
  Tests.one.ranges.message.shape.maskRows != 0 && Tests.one.ranges.message.shape.mainDeg != 3
#guard Tests.one.lin.w.answers != 0 && Tests.one.lin.w.maskRows != 0 && Tests.one.lin.w.mainDeg == 3

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.rowsR_mainF
#print axioms AtPublicFiles.Key.rowsR_mainE
#print axioms AtPublicFiles.Key.msg_shape
#print axioms AtPublicFiles.Key.msg_rows
#print axioms AtPublicFiles.Key.msg_val
#print axioms AtPublicFiles.Key.w_first
#print axioms AtPublicFiles.Key.w_rows
