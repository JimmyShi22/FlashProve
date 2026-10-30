-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OmegaAtKeyBookGuards.lean

The book's two tests at the key file's test on G_omega, by Lean's evaluator. OmegaAtKeyBookKernel.lean
imports this file, so that the kernel is asked only where the evaluator has said yes.

  `jobKOB`    `jobOmega` (E2E/KeyTestSizes.lean) with the place's written numbers `piKOFull`
  `laysO`, `tiesO`   `laysB` and `tiesOB` there, at a book

Limits. Evaluations outside the kernel: no theorem. Public numbers alone: nothing is played. The
members and the sender of the fresh table are `jobOmega`'s literals. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.ProofFile.Honest.K12.Own.AgreeOwn
import Johnson.Desc.K12.Law.PlacesKeyFull
import E2E.KeyBookHeldK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.OmegaAtKeyBook
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKOFull)
open ProofFile.Honest.K12.Own (tiesOB)

/-- `jobOmega` with the place's written numbers. -/
def jobKOB : TestJob Unit Unit := { AtPublicFiles.KeyTest.jobOmega with p := piKOFull }

/-- `laysB` in the shared chain at a book and a job. -/
def laysO (B : ProverCoinCounts) (J : TestJob Unit Unit) : Bool := laysB B 1 J

/-- `tiesOB` at a book and a number of members. -/
def tiesO (B : ProverCoinCounts) (n : ℕ) : Bool := tiesOB B piKOFull.place n

-- The place and the number of members that the two lines use.
#guard piKOFull.place == AtPublicFiles.KeyTest.jobOmega.p.place
#guard AtPublicFiles.KeyTest.jobOmega.members.length == 2 && AtPublicFiles.KeyTest.jobOmega.fresh.isNone
#guard piKOFull.nums.stages == AtPublicFiles.KeyTest.jobOmega.p.nums.stages

-- THE TWO LINES. Foretold: yes.
#guard atFull fun K => laysO (keyBook K) jobKOB
#guard atFull fun K => tiesO (keyBook K) 2

-- CONTROLS on `laysB`. Foretold: no. A place that the book has no cut for; the job with its last
-- member dropped, so that what the second part carries is not the book's.
#guard atFull fun K => !laysO (keyBook K)
  { jobKOB with p := { piKOFull with place := ⟨2, none, 99, .K12⟩ } }
#guard atFull fun K => !laysO (keyBook K) { jobKOB with members := jobKOB.members.dropLast }
-- CONTROLS on `tiesOB`. Foretold: no. The book without its carried entries; one member more; one
-- member fewer, where entry 1 is a member's and not the first part's own coins.
#guard atFull fun K => !tiesO (keyBook K false) 2
#guard atFull fun K => !tiesO (keyBook K) 3
#guard atFull fun K => !tiesO (keyBook K) 1

end ProofFile.Honest.K12.OmegaAtKeyBook

#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.jobKOB
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.laysO
#print axioms ProofFile.Honest.K12.OmegaAtKeyBook.tiesO
