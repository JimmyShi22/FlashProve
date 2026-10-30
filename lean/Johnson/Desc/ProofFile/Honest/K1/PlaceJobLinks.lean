-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceJobLinks.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: THREE LAWS ON THE JOB AT THE FIRST PLACE THAT LEAN ON THE DESCRIPTION's LAWS ON
THE LINKS. No definition.

  first_rideOwn   AT THE FIRST PLACE THE TEST rideOwn (Honest/K1/PlaceJob.lean) HOLDS, AT EVERY q
  own_le_sent   the segment's own messages of moment 0 are no more than the first sending's messages
  seat_first    the general test at the first place, at nothing heard, gives the first place's own
                test (firstSeatOk, Honest/K1/PlaceFirst.lean)

Why here. They call K1.firstPar_sent (Johnson/Desc/K1/Law/Links.lean). That law file's import cone
is wide; a file with code that imports it cannot stand in a compiled set that is closed under
imports and leaves that cone out. So the code stays in PlaceJob.lean, and these three stand apart.
Statements and proofs are as they stood in PlaceJob.lean.

Limits. Laws on public tests and counts at the first place alone: rideOwn cannot see a fold's k;
seat_first speaks at nothing heard. Nothing is sent or played. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.K1.Law.Links

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable {V W X Xi : Type}

/-- **AT THE FIRST PLACE THE TEST HOLDS, AT EVERY q.** -/
theorem first_rideOwn (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    rideOwn (K1.firstPar q gp) (firstFold q) = true := by
  have h := K1.firstPar_sent q gp
  unfold K1.firstSent at h
  have e : (ReqFrame.notices ((K1.frameAt q.shape 0).atMoment 0)).toList.length =
      ((K1.frame₀ q).atMoment 0).length := by
    show (((((K1.frame₀ q).atMoment 0).map _).toArray).toList).length = _
    rw [List.toList_toArray, List.length_map]
  show ((K1.firstPar q gp).sent[((K1.frame₀ q).atMoment 0).length]? ==
    some (foldMaskNotice ((K1.frame₀ q).foldShape 0 {}))) = true
  rw [← Array.getElem?_toList, h, List.append_assoc, ← e,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  exact beq_self_eq_true _

/-- The segment's own messages of moment 0 are no more than the first sending's messages. -/
theorem own_le_sent (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    ((K1.frame₀ q).atMoment 0).length ≤ (K1.firstPar q gp).sent.size := by
  have h := congrArg List.length (K1.firstPar_sent q gp)
  unfold K1.firstSent at h
  simp only [Array.length_toList, List.length_append] at h
  have e : (ReqFrame.notices ((K1.frameAt q.shape 0).atMoment 0)).size =
      ((K1.frame₀ q).atMoment 0).length := by
    show ((((K1.frame₀ q).atMoment 0).map _).toArray).size = _
    rw [List.size_toArray, List.length_map]
  omega

theorem seat_first (S : OnBytes.HonestTrace.Sz) (q : Params.First)
    (gp : _root_.Desc.Plain.GPar)
    (h : placeSeatOk (K1.firstPar q gp) (firstFold q) (firstFill S q) [] = true) :
    firstSeatOk S q gp = true := by
  unfold placeSeatOk at h
  unfold firstSeatOk
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, ← firstRide_eq] at h
  rw [Bool.and_eq_true, List.all_eq_true]
  refine ⟨h.1.2, fun k hk => ?_⟩
  have := own_le_sent q gp
  exact h.2 k (List.mem_range.2 (by have := List.mem_range.1 hk; omega))

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.first_rideOwn
#print axioms ProofFile.Honest.K1.own_le_sent
#print axioms ProofFile.Honest.K1.seat_first
