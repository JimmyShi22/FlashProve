-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FoldedAtKeyBookGuards.lean

The book's test on laying at the key file's test on G_u, by Lean's evaluator: the twin of
OmegaAtKeyBookGuards.lean's first line. FoldedAtKeyBookKernel.lean imports this file, so that the
kernel is asked only where the evaluator has said yes.

  jobKUB    jobFolded (E2E/KeyTestSizes.lean) with the place's written numbers piKUFull
  laysU     laysB in the shared chain there, at a book

Limits. Evaluations outside the kernel: no theorem. Public numbers alone: nothing is played. The
members and the sender of the fresh table are jobFolded's literals. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.K12.Law.PlacesKeyFull
import E2E.KeyBookHeldK12

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.FoldedAtKeyBook
open AtPublicFiles.KeyBook (atFull keyBook)
open H2K.Member (piKUFull)

/-- jobFolded with the place's written numbers. -/
def jobKUB : TestJob Unit Unit := { AtPublicFiles.KeyTest.jobFolded with p := piKUFull }

/-- laysB in the shared chain at a book and a job. -/
def laysU (B : ProverCoinCounts) (J : TestJob Unit Unit) : Bool := laysB B 1 J

-- The place and the members that the line uses.
#guard piKUFull.place == AtPublicFiles.KeyTest.jobFolded.p.place
#guard AtPublicFiles.KeyTest.jobFolded.members.length == 2 && AtPublicFiles.KeyTest.jobFolded.fresh.isSome
#guard piKUFull.nums.stages == AtPublicFiles.KeyTest.jobFolded.p.nums.stages

-- THE LINE. Foretold: yes.
#guard atFull fun K => laysU (keyBook K) jobKUB

-- CONTROLS. Foretold: no. A place that the book has no cut for; the job with its last member
-- dropped, so that what the second part carries is not the book's.
#guard atFull fun K => !laysU (keyBook K)
  { jobKUB with p := { piKUFull with place := ⟨2, none, 99, .K12⟩ } }
#guard atFull fun K => !laysU (keyBook K) { jobKUB with members := jobKUB.members.dropLast }

end ProofFile.Honest.K12.FoldedAtKeyBook

#print axioms ProofFile.Honest.K12.FoldedAtKeyBook.jobKUB
#print axioms ProofFile.Honest.K12.FoldedAtKeyBook.laysU
