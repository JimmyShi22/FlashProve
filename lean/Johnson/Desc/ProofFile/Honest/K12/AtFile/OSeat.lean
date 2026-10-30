-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OSeat.lean: a block like the seat of the test on G_omega at a job's place
seats the job: with `tailLike_shared` (Honest/K14/OmegaAtShared.lean) that is `StandO.member` and `StandO.seat` at
lettersShared's list.

  `seat_of_like_O`   the statement

Limits. A law on blocks: no run, no coin. That member 10 of a thread's list is like that seat is the caller's.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat
import Johnson.Desc.K14.Honest.FlatSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open Desc.K14.Honest (Like)
open ProofFile.Honest.K12

variable {W X : Type}

/-- **A block like the seat at a job's place seats the job.** -/
theorem seat_of_like_O {Cl : Type} {x : Block St Cl} {J : TestJob W X}
    (hl : Like x (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit))) :
    SeatOf x J (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
      VerifiableInference.Desc.K12.Seat.leave := by
  have h := seatOf_inside (Cl := Unit) J
    (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none)
    VerifiableInference.Desc.K12.Seat.leave
  exact ⟨hl.place.trans h.place, hl.rounds.trans h.rounds, hl.oracles.trans h.oracles,
    fun s rs gs => by rw [hl.decide]; exact h.decide s rs gs⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.seat_of_like_O
