-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OpensLines.lean: the one pass `opensEach` (OpensLaw.lean) at
the shared and the last chain of the written description `WP` (Johnson/AtFull/ProofPlan/WP.lean), first
by Lean's evaluator, then by the kernel; and so `opensAvailable` at every border of any thread whose list
is alike to them: the proof file's own two chains in the goals' scope. It can say no. The first chain's
line stands alone in OpensFirstLine.lean: its list has 48293 rounds.

  `sharedR`, `lastR`   the two written lists of rounds and counts
  `takenLast` (WLaidDefs.lean)   the trees that the last chain takes over: the three of its test's first reading round
  `opens_shared`, `opens_last`   the pass says yes
  `opens_bent_hand`, `opens_bent_trees`, `opens_bent_taken`   controls: the shared chain with member 10's
                 rounds in member 9's stead; with member 9 sending no tree; the last chain with one
                 taken tree less
  `front_opens_nothing`, `nine_opens`   the shared chain's members 0 to 8 open nothing; with member 9 in,
                 something is opened
  `opensAvailable_shared`, `opensAvailable_last`   the test at every border, at any thread alike to the
                 written lists

Limits. `WP` is a written term: that a description is alike to it is `alike_shared_at_laid`,
`alike_last_at_laid` (Honest/K14/WrittenAtHead.lean), under `LaidAt`. `takenLast` is a list that this
file chooses: whether a last chain's thread lays it is that thread's field: `opens_last` says that this
list suffices. Public lists: nothing of a run. The full size alone. Nothing on completeness, on soundness
or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLaw
import Johnson.AtFull.ProofPlan.WP
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLaidDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Block Alike₂)
open P2Law.ProofPlan (WP)
open H2K.Member (piWFull)

/-- The shared chain's written list. -/
def sharedR : List (List Fmt.DeclaredRound × Nat) := WP.shared.blocksInOrder.map roundsTrees

/-- The last chain's written list. -/
def lastR : List (List Fmt.DeclaredRound × Nat) := WP.second.blocksInOrder.map roundsTrees

/-- A source to print. -/
def srcNum : Fmt.TreeSource → Nat
  | .own n => n
  | .taken c k => 100000 + 1000 * c + k

/-- Control: member 10's rounds in member 9's stead, with member 9's count. -/
def bentHand : List (List Fmt.DeclaredRound × Nat) :=
  sharedR.set 9 ((sharedR.getD 10 ([], 0)).1, (sharedR.getD 9 ([], 0)).2)

/-- Control: member 9 sends no tree. -/
def bentTrees : List (List Fmt.DeclaredRound × Nat) := sharedR.set 9 ((sharedR.getD 9 ([], 0)).1, 0)

-- Member by member: rounds, trees, and what the rounds open.
#eval sharedR.map fun x => (x.1.length, x.2, (x.1.flatMap (·.opens)).map fun o => srcNum o.2)
#eval lastR.map fun x => (x.1.length, x.2, (x.1.flatMap (·.opens)).map fun o => srcNum o.2)
#eval takenLast.map srcNum

-- Foretold: twelve members and four; yes at both passes.
#guard sharedR.length == 12 && lastR.length == 4
#guard opensEach [] sharedR
#guard opensEach takenLast lastR
-- Controls. Foretold: no.
#guard !opensEach [] bentHand
#guard !opensEach [] bentTrees
#guard !opensEach takenLast.tail lastR

theorem opens_shared : opensEach [] sharedR = true := by decide +kernel

theorem opens_last : opensEach takenLast lastR = true := by decide +kernel

theorem opens_bent_hand : opensEach [] bentHand = false := by decide +kernel

theorem opens_bent_trees : opensEach [] bentTrees = false := by decide +kernel

theorem opens_bent_taken : opensEach takenLast.tail lastR = false := by decide +kernel

/-- Members 0 to 8 of the shared chain open nothing. -/
theorem front_opens_nothing :
    ((sharedR.take 9).flatMap (·.1)).all (fun d => d.opens.length == 0) = true := by
  decide +kernel

/-- Control: with member 9 in, something is opened. -/
theorem nine_opens :
    ((sharedR.take 10).flatMap (·.1)).all (fun d => d.opens.length == 0) = false := by
  decide +kernel

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **`opensAvailable` at every border of a thread alike to the written shared list**, with no tree
taken over. -/
theorem opensAvailable_shared (T : Thread Bk S Cl V W X Pb)
    (hl : List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs) (ht : T.taken = []) (n : Nat) :
    T.opensAvailable n = true :=
  opens_of_alike T hl (by rw [ht]; exact opens_shared) n

/-- **`opensAvailable` at every border of a thread alike to the written last list**, that takes over
the three trees. -/
theorem opensAvailable_last (T : Thread Bk S Cl V W X Pb)
    (hl : List.Forall₂ Alike₂ WP.second.blocksInOrder T.bs) (ht : T.taken = takenLast) (n : Nat) :
    T.opensAvailable n = true :=
  opens_of_alike T hl (by rw [ht]; exact opens_last) n

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.opens_shared
#print axioms ProofFile.Honest.K12.AtFile.opens_last
#print axioms ProofFile.Honest.K12.AtFile.opens_bent_hand
#print axioms ProofFile.Honest.K12.AtFile.opens_bent_trees
#print axioms ProofFile.Honest.K12.AtFile.opens_bent_taken
#print axioms ProofFile.Honest.K12.AtFile.front_opens_nothing
#print axioms ProofFile.Honest.K12.AtFile.nine_opens
#print axioms ProofFile.Honest.K12.AtFile.opensAvailable_shared
#print axioms ProofFile.Honest.K12.AtFile.opensAvailable_last
