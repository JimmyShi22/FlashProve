-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimKeeps.lean: beside the laws of the lookup's three runs
of claims (Honest/K3/Shape/ClaimRuns.lean, Honest/K3/Shape/ClaimPlanes.lean,
Honest/K3/Shape/ClaimPlanesHead.lean): each run, without the guard, leaves the reply and the
statement; and the hypothesis of each law whose hypothesis is "true", as a test with code. One
definition; theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the statement is the state's field st; a run leaves the
reply if `sameReply` accepts the states in front of and behind it. A law is a value of `RunLaw`
(Johnson/Desc/First/Batch/Shape/ClaimShape.lean, which
ClaimRuns.lean imports); its hypothesis is the field
pre.

What is shown.
  `guestsRun_reply`: "guests" leaves the reply ("objects": `objectsRun_reply`, ClaimRuns.lean;
    "planes": `planesRun_reply`, ClaimPlanes.lean).
  `objectsRun_st`, `guestsRun_st`, `planesRun_st`: each leaves the statement; "planes" at every
    caller's readers.
  `guard_st`: so does the run behind a guard; general in the run.
  `truePreB`: the test that always accepts.
  `objects_preB`, `guests_preB`, `planesHead_preB`: an acceptance of that test gives the law's
    hypothesis: that hypothesis is "true".

Hypotheses that remain.
  `h`, `hz`: the run returns (each theorem on a run).
  The three on `truePreB` have, without a name, that the test accepts, which it always does.

How the proof goes. The proofs call the library's `K1.Rel.putFork_st`
(Johnson/Desc/K1/KeepsAtS.lean), `P4.planesRun_putFork` (Johnson/P4SR/ObjectsAtSeat.lean) and
`guestsRun_nil` (Johnson/Top/H/Keep/RunsGuests.lean).

Limits. Whether a run returns is not spoken of. No instance of these hypotheses is exhibited in this
file. At an attention link the law of "planes" has the hypothesis `ReadersAgree` (ClaimPlanes.lean),
which is no test with code and is not shown in this file; in this folder it is shown at the head's
readers alone (`readersAgree_head`, ClaimPlanesHead.lean). Nothing on it here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Shape.ClaimPlanesHead
import Johnson.Desc.K1.KeepsAtS
import Johnson.P4SR.ObjectsAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Shape
open VerifiableInference.Desc (Claim named)
open VerifiableInference.Desc.K3 (seatCalls planesRun Readers)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun seatOf guestsRun_nil)
open ProofFile (sameReply)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "RunT" => VerifiableInference.Desc.K9.Shape.Run

/-- "guests" leaves the reply. -/
theorem guestsRun_reply (n : Nat) (s : FS) (z : List Claim × FS)
    (h : guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)) n s = .ok z) :
    sameReply s z.2 = true := by
  rw [guestsRun_nil] at h
  obtain rfl := Except.ok.inj h
  unfold sameReply
  simp

/-- "objects" leaves the statement. -/
theorem objectsRun_st (d : Bool) (n : Nat) (s : FS) (z : List Claim × FS)
    (h : objectsRun (seatOf K3Lot.ofForm d) n s = .ok z) : z.2.st = s.st := by
  unfold objectsRun at h
  cases hF : (seatOf K3Lot.ofForm d).fork s with
  | none => simp [hF, named, bind, Except.bind] at h
  | some F =>
    cases hg : (seatOf K3Lot.ofForm d).heard s with
    | none => simp [hF, hg, named, bind, Except.bind] at h
    | some g =>
      simp only [hF, hg, named, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      show ((seatOf K3Lot.ofForm d).mark s _).st = s.st
      rw [mark_is]
      exact VerifiableInference.Desc.K1.Rel.putFork_st s _

/-- "guests" leaves the statement. -/
theorem guestsRun_st (n : Nat) (s : FS) (z : List Claim × FS)
    (h : guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)) n s = .ok z) :
    z.2.st = s.st := by
  rw [guestsRun_nil] at h
  obtain rfl := Except.ok.inj h
  rfl

/-- "planes" leaves the statement, at every caller's readers. -/
theorem planesRun_st (lm : Nat) (readers : Readers FS) (n : Nat) (s : FS) (z : List Claim × FS)
    (h : planesRun (seatCalls K3Lot.ofForm) lm readers n s = .ok z) : z.2.st = s.st := by
  obtain ⟨G, e⟩ := P4.planesRun_putFork K3Lot.ofForm lm readers n s z h
  rw [e]
  exact VerifiableInference.Desc.K1.Rel.putFork_st s G

/-- **General in the run**: a run behind a guard leaves the statement where the run does. -/
theorem guard_st {same : FS → FS → Bool} {run : RunT}
    (h : ∀ n s z, run n s = .ok z → z.2.st = s.st) (n : Nat) (s : FS) (z : List Claim × FS)
    (hz : IM.guardRun same run n s = .ok z) : z.2.st = s.st :=
  h n s z (guard_back hz)

/-- The test that always accepts. -/
def truePreB : Nat → FS → Bool := fun _ _ => true

theorem objects_preB (d : Bool) (n : Nat) (s : FS) (_ : truePreB n s = true) :
    (objectsLaw d).pre n s :=
  trivial

theorem guests_preB (n : Nat) (s : FS) (_ : truePreB n s = true) : guestsLaw.pre n s :=
  trivial

theorem planesHead_preB (lm iU3 n : Nat) (s : FS) (_ : truePreB n s = true) :
    (planesLawHead lm iU3).pre n s :=
  trivial

end ProofFile.Honest.K3.Shape

#print axioms ProofFile.Honest.K3.Shape.guestsRun_reply
#print axioms ProofFile.Honest.K3.Shape.objectsRun_st
#print axioms ProofFile.Honest.K3.Shape.guestsRun_st
#print axioms ProofFile.Honest.K3.Shape.planesRun_st
#print axioms ProofFile.Honest.K3.Shape.guard_st
#print axioms ProofFile.Honest.K3.Shape.objects_preB
#print axioms ProofFile.Honest.K3.Shape.guests_preB
#print axioms ProofFile.Honest.K3.Shape.planesHead_preB
