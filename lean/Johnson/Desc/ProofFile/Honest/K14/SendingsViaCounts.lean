-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsViaCounts.lean: UNDER Plan2 AND SendShapes THE TWO TEXTS
TAKE AS MANY COINS: the count of a call of the shared sending's part (dueR, Honest/K1/Coins.lean) is
the count of this kind's own part for the same sending (takesOf, Honest/K14/Sendings.lean). (The
frame's lending reads of a part its three counts alone, and both parts spend and carry nothing: so a
book that lends to one should lend to the other; no statement here says so.)

  due_vec, due_mask, due_ride   one message's count in the two texts: a message that carries a
                  vector (degree 3, an answer) and has no mask row; a message without main rows on
                  which no table rides; a riding table (no main row, no answer)
  due_two         a sending of two messages
  due_u, due_omega   **the two counts**, under Plan2 and SendShapes. (All coins are of the extension
                  field: that is the form of takesOf, no clause of these two statements)
  maskStart_noMain, split_start   where the mask rows' coins of o_sp begin, in the shared part's
                  words (maskStart) and in this kind's (offsetOf): one number

What is assumed. Plan2 and SendShapes, in due_u, due_omega and split_start; in the others what each
names of a shape.
Kin. Honest/K14/TieCounts.lean, above this file, states the like of due_u, due_omega and split_start
(due_tie, start_tie), general in the job, under another premise: the test sendShapeFits.
What is not claimed. That any book has these counts. That a number which a law names lies below the
count: the shared part's own laws on that (Honest/K1/CoinsIn.lean) are called nowhere here. Nothing
on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsViaShows
import Johnson.Desc.ProofFile.Honest.K14.SendingsWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (K1.Par)
open Desc.K14 (P14)
open Desc.K14.Honest
open Desc.K14.Law (parU)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (Ride dueR startR dueMsg maskStart)

variable {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- A message that carries a vector (main rows of degree 3, at least one answer) and has no mask
row. -/
theorem due_vec (codes : Codes) (s : OracleShape) (high : Bool) (h3 : s.mainDeg = 3)
    (hz : s.maskRows = 0) (ha : s.answers ≠ 0) :
    dueMsg codes s none = ⟨0, dueOf codes s (.plain high)⟩ := by
  simp [dueMsg, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, dueOf, h3, hz, ha]

/-- A message without main rows, on which no table rides: with a mask row, or without an answer. -/
theorem due_mask (codes : Codes) (s : OracleShape) (high : Bool) (hm : s.mainRows = 0)
    (hza : s.maskRows ≠ 0 ∨ s.answers = 0) :
    dueMsg codes s none = ⟨0, dueOf codes s (.plain high)⟩ := by
  rcases hza with hz | ha
  · by_cases h3 : s.mainDeg = 3 <;>
      simp [dueMsg, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, dueOf, hm, hz, h3]
  · by_cases h3 : s.mainDeg = 3 <;>
      simp [dueMsg, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, dueOf, hm, ha, h3]

/-- A riding table: a message without main rows and without an answer, on which a table rides. -/
theorem due_ride (codes : Codes) (s : OracleShape) (k h : Nat) (hm : s.mainRows = 0)
    (ha : s.answers = 0) : dueMsg codes s (some ⟨k, h⟩) = ⟨0, dueOf codes s (.fresh k h)⟩ := by
  by_cases h3 : s.mainDeg = 3 <;>
    simp [dueMsg, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, ProofFile.Honest.K1.Ride.count, dueOf,
      hm, ha, h3]

/-- A sending of two messages. -/
theorem due_two (P : K1.Par) (ride : Nat → Option Ride) (sort : Nat → MsgSort)
    (hsz : P.sent.size = 2)
    (h0 : dueMsg P.codes (shapeAt P 0) (ride 0) = ⟨0, dueOf P.codes (shapeAt P 0) (sort 0)⟩)
    (h1 : dueMsg P.codes (shapeAt P 1) (ride 1) = ⟨0, dueOf P.codes (shapeAt P 1) (sort 1)⟩) :
    dueR P ride = takesOf P.codes P.sent sort := by
  have e1 : dueR P ride = ((⟨0, 0⟩ : Due).plus (dueMsg P.codes (shapeAt P 0) (ride 0))).plus
      (dueMsg P.codes (shapeAt P 1) (ride 1)) := by
    unfold dueR
    rw [hsz]
    rfl
  obtain ⟨a, b, hl⟩ : ∃ a b, P.sent.toList = [a, b] := by
    have hn : P.sent.toList.length = 2 := by rw [Array.length_toList]; exact hsz
    match hl : P.sent.toList, hn with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have g0 : shapeAt P 0 = a.shape := by
    show (P.sent.getD 0 default).shape = _
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hl]
    rfl
  have g1 : shapeAt P 1 = b.shape := by
    show (P.sent.getD 1 default).shape = _
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hl]
    rfl
  have e2 : takesOf P.codes P.sent sort =
      ⟨0, 0 + dueOf P.codes a.shape (sort 0) + dueOf P.codes b.shape (sort 1)⟩ := by
    unfold takesOf offsetOf
    rw [hsz, hl]
    rfl
  rw [e1, e2, h0, h1, g0, g1]
  rfl

/-- **"send o_u": the call's count is that of this kind's own part**, under Plan2 and SendShapes.
(The proof treats both cases: the test on G_u has a first stage, or has none. No statement of this
file says that the second case cannot occur under Plan2.) -/
theorem due_u (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (a n : Nat) :
    dueR (viaU ⟨Q, a, n⟩).P (viaU ⟨Q, a, n⟩).ride = (sendingPart (jobU ⟨Q, a⟩)).takes := by
  have gU : Desc.K14.withU Q.S = some sentU := hQ.facts.goes
  have sU : (viaU ⟨Q, a, n⟩).P.sent = sentU := by
    have e : (viaU ⟨Q, a, n⟩).P.sent = (Desc.K14.withU Q.S).getD #[] :=
      Desc.K14.Law.parK1_sent Q 2 _ _
    rw [e, gU, Option.getD_some]
  have hs0 : shapeAt (viaU ⟨Q, a, n⟩).P 0 = Q.S.fold.u := u_first Q 0 gU
  have hm1 : (shapeAt (viaU ⟨Q, a, n⟩).P 1).mainRows = 0 := hSh.mask
  have ha1 : (shapeAt (viaU ⟨Q, a, n⟩).P 1).answers = 0 := by
    show ((viaU ⟨Q, a, n⟩).P.sent.getD 1 default).shape.answers = 0
    rw [sU]
    exact firstMask_noAnswer gU
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.S).1 hQ.facts.lin
  have ha0 : Q.S.fold.u.answers ≠ 0 := by
    have := hlin.1.1.2.2.2.2.1
    omega
  refine due_two (viaU ⟨Q, a, n⟩).P (viaU ⟨Q, a, n⟩).ride (jobU ⟨Q, a⟩).sort
    (by rw [sU]; exact hQ.facts.goesTwo) ?_ ?_
  · rw [hs0]
    exact due_vec Q.codes Q.S.fold.u Q.S.fold.rowsHigh hSh.u.overE hSh.u.noMask ha0
  · show dueMsg Q.codes (shapeAt (viaU ⟨Q, a, n⟩).P 1)
        (Q.S.testU.head?.map fun s => ({ k := s.k, h := s.h } : Ride)) =
      ⟨0, dueOf Q.codes (shapeAt (viaU ⟨Q, a, n⟩).P 1)
        (match Q.S.testU.head? with
          | some s => .fresh s.k s.h
          | none => .plain false)⟩
    cases Q.S.testU.head? with
    | some s => exact due_ride Q.codes _ s.k s.h hm1 ha1
    | none => exact due_mask Q.codes _ false hm1 (Or.inr ha1)

/-- **"send o_omega": the call's count is that of this kind's own part**, under Plan2 and
SendShapes. -/
theorem due_omega (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (a n : Nat) :
    dueR (viaOmega ⟨Q, a, n⟩).P (viaOmega ⟨Q, a, n⟩).ride =
      (sendingPart (jobOmega ⟨Q, a⟩)).takes := by
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (viaOmega ⟨Q, a, n⟩).P.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0 : shapeAt (viaOmega ⟨Q, a, n⟩).P 0 = Q.S.omega := omega_first Q 0
  have hs1 : shapeAt (viaOmega ⟨Q, a, n⟩).P 1 = Q.par.S.sharedSplit :=
    (shapeAt_of_get (viaOmega ⟨Q, a, n⟩).P 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.par.S).1 hQ.facts.lin
  have ha0 : Q.S.omega.answers ≠ 0 := by
    have h1 : 1 ≤ Q.S.omega.answers := hlin.1.2.2.2.2.2.2.1.2.2.2
    omega
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits Q.par.S.sharedSplit
      Q.par.S.sharedMaskCode := by
    rcases hlin.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hQ.facts.two] at e
      cases e
    · exact e
  refine due_two (viaOmega ⟨Q, a, n⟩).P (viaOmega ⟨Q, a, n⟩).ride (jobOmega ⟨Q, a⟩).sort
    (by rw [sO]; exact w2) ?_ ?_
  · rw [hs0]
    exact due_vec Q.codes Q.S.omega Q.S.omegaRowsHigh hSh.omega.overE hSh.omega.noMask ha0
  · rw [hs1]
    exact due_mask Q.codes Q.par.S.sharedSplit Q.S.omegaRowsHigh hSp.1 (Or.inl hSp.2.1)

/-- Where a message has no main row, its mask rows' coins begin where its coins begin. -/
theorem maskStart_noMain (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (hm : (shapeAt P k).mainRows = 0) (hz : (shapeAt P k).maskRows ≠ 0) :
    maskStart P ride k = (startR P ride k).e := by
  simp [maskStart, ProofFile.Honest.K1.Steps.main, ProofFile.Honest.K1.stepsOf, hm, hz]

/-- **Where the mask rows' coins of o_sp begin**: the shared part's number is this kind's: that by
which the book's entry for "SPLIT" is worded (bookSplitFits, Honest/K14/Thread2Full.lean). -/
theorem split_start (hQ : Plan2 Q sentU layO) (hSh : SendShapes Q) (a n : Nat) :
    maskStart (viaOmega ⟨Q, a, n⟩).P (viaOmega ⟨Q, a, n⟩).ride 1 =
      offsetOf (jobOmega ⟨Q, a⟩).Q.codes (jobOmega ⟨Q, a⟩).Q.sent (jobOmega ⟨Q, a⟩).sort 1 := by
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (viaOmega ⟨Q, a, n⟩).P.sent = Desc.K14.withOmega Q.S :=
    Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0 : shapeAt (viaOmega ⟨Q, a, n⟩).P 0 = Q.S.omega := omega_first Q 0
  have hs1 : shapeAt (viaOmega ⟨Q, a, n⟩).P 1 = Q.par.S.sharedSplit :=
    (shapeAt_of_get (viaOmega ⟨Q, a, n⟩).P 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hlin := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.par.S).1 hQ.facts.lin
  have hSp : VerifiableInference.Desc.Own.SplitMessageFits Q.par.S.sharedSplit
      Q.par.S.sharedMaskCode := by
    rcases hlin.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
    · rw [hQ.facts.two] at e
      cases e
    · exact e
  rw [maskStart_noMain _ _ 1 (by rw [hs1]; exact hSp.1) (by rw [hs1]; exact hSp.2.1)]
  exact start_one (viaOmega ⟨Q, a, n⟩).P (viaOmega ⟨Q, a, n⟩).ride (jobOmega ⟨Q, a⟩).sort
    Q.S.omegaRowsHigh (by
      have w2' : (Desc.K14.withOmega Q.S).size = 2 := w2
      rw [sO, w2']
      exact Nat.zero_lt_two) rfl rfl
    (by rw [hs0]; exact hSh.omega.overE) (by rw [hs0]; exact hSh.omega.noMask) (by
      rw [hs0]
      have h1 : 1 ≤ Q.S.omega.answers := hlin.1.2.2.2.2.2.2.1.2.2.2
      omega)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.due_vec
#print axioms ProofFile.Honest.K14.due_mask
#print axioms ProofFile.Honest.K14.due_ride
#print axioms ProofFile.Honest.K14.due_two
#print axioms ProofFile.Honest.K14.due_u
#print axioms ProofFile.Honest.K14.due_omega
#print axioms ProofFile.Honest.K14.maskStart_noMain
#print axioms ProofFile.Honest.K14.split_start
