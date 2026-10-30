-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyNineClosed.lean: three closed questions at the test on G_u, at the written book and place.

Why. The chain's own numbers of that test's place are `H2U.proximityTestParametersAt … PF.U`; IOP's facts stand at `piKUFull`; the
book's test `laysB` stands at public fields. Each of the three lines can say no, and each is asked
before a stand is typed at member 9.

Main names.
  `place_full`: the chain's numbers at the place are `piKUFull`.
  `lays_full`, `lays_bent`: `laysB` at `jobFolded` with those numbers, at the written book; a bent place is
    refused.
  `carried_full`: the entries that the book hands the second part of that test as carried: their owners
    and first coins.

What stays open. Public numbers: nothing is played, and `chainSteps` is not here. `lays_of_B` wants more.

No coin is named here. No law over coins.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyShapeSharedFull
import E2E.KeyTestSizes
import E2E.KeyBookSplit
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyNineClosed
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.K12
open AtPublicFiles.KeyBook (KeyPub keyBook atFull foldedTestPlace)
open AtPublicFiles.KeyTest (jobFolded)
open AtPublicFiles.AtFiles.Full (PF QK)
open H2K.Member (piKUFull)

/-- The chain's numbers of the place. -/
theorem place_full : H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ PF.U = piKUFull := by
  first
    | decide +kernel
    | rfl

/-- The book's test at the job with those numbers. -/
theorem lays_full : atFull (fun K => laysB (keyBook K) 1 { jobFolded with p := piKUFull }) = true := by
  decide +kernel

/-- A control: at a place that the book has no cut for, the book's test refuses. -/
theorem lays_bent : atFull (fun K => laysB (keyBook K) 1
    { jobFolded with p := { piKUFull with place := ⟨2, none, 99, .K12⟩ } }) = false := by
  decide +kernel

/-- The owners and first coins that the book hands the second part as carried. -/
def carriedAt (K : KeyPub) : List (Addr × Due) :=
  ((keyBook K).ahead.filter fun e => e.spender == ⟨foldedTestPlace, 1⟩ && !e.once).map
    fun e => (e.owner, e.start)

/-- **What they should be**: o_u's from its start, o_sp's at «send o_omega», and the fresh table's. -/
def carriedOught : List (Addr × Due) :=
  [(⟨sendPlace 2, 0⟩, ⟨0, offsetOf (jobU ⟨QK, 0⟩).Q.codes (jobU ⟨QK, 0⟩).Q.sent (jobU ⟨QK, 0⟩).sort 0⟩),
   (⟨sendPlace 5, 0⟩,
     ⟨0, offsetOf (jobOmega ⟨QK, 0⟩).Q.codes (jobOmega ⟨QK, 0⟩).Q.sent (jobOmega ⟨QK, 0⟩).sort 1⟩),
   (⟨sendPlace 2, 0⟩, ⟨0, offsetOf (jobU ⟨QK, 0⟩).Q.codes (jobU ⟨QK, 0⟩).Q.sent (jobU ⟨QK, 0⟩).sort 1⟩)]

theorem carried_full : atFull (fun K => carriedAt K == carriedOught) = true := by
  decide +kernel

end AtPublicFiles.KeyNineClosed

#print axioms AtPublicFiles.KeyNineClosed.place_full
#print axioms AtPublicFiles.KeyNineClosed.lays_full
#print axioms AtPublicFiles.KeyNineClosed.lays_bent
#print axioms AtPublicFiles.KeyNineClosed.carried_full
