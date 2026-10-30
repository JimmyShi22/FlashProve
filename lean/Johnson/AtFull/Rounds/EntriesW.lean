-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/EntriesW.lean: THE ENTRIES OF THE WRITTEN DECLARED ROUNDS OF A PROOF FILE OF
FULL SIZE (`declProofFull`, Johnson/AtFull/ProofRows/WrittenProof.lean) ARE THE ENTRIES OF THE
WRITTEN DRY LISTS (`dryProofFull`, Johnson/G/DryProofLit.lean), CHAIN BY CHAIN. One law and its
corollaries. NOTHING IS EVALUATED HERE: no new closed fact.

Why. Several lots' rows at the full size take the premise "the first chain's declared rounds'
entries are the written ones" (he : Z.D.1.map (·.entry) = ‹the dry list's entries›: kind K9's lot's
two rows, Johnson/AtFull/Desc/Lots/K9RowWritten.lean and Johnson/AtFull/Rounds/K9At.lean; the like
for all three chains in Johnson/Road/K4/K4PlanTied.lean's field entries). Whoever holds
Z.D = declProofFull wants it from that equation.

How. It is shown, run by run and by Lean's kernel, that the test `walk`
(Johnson/HB/LLHARD/KB8/WrittenFull.lean) accepts along the declared and the dry list of each chain
(`walk_of_runs` at `ok_first`, `ok_shared`, `ok_second`). The test asks at each place that the
declared round is laid as the dry round; and a declared round, laid, keeps its entry
(`LPFK10.round_entry`, Johnson/LPFK10R/WorksLive.lean). So the two lists of entries
are one, by an induction along the walk: 48,293 members are never laid out.

  entries_of_walk   THE LAW: walk e l R = true ⊢ l.map (·.entry) = R.map (·.1.entry): every e, l, R.
  entries_first · entries_shared · entries_second   at the three written chains.
  entries_all       the three as one triple: `P5T.esFull` (Johnson/P5T/PlanSeatsFull.lean).
  entries_at · entries_all_at   hP : Z.D = declProofFull ⊢ the same of Z.D.
`Johnson.AtFull.Desc.Lots.esW` is `dryProofFull.1.map (·.1.entry)` by definition: this file does not
import it; that `entries_at hP` fits the premise he is for the caller's file to show.

Limits. Both sides are written values. That Z.D = declProofFull holds at any public files is not
said here. The law gives equal entries and nothing on the other fields of a declared round.
It stands over WrittenProof.lean and what that file imports.
The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.ProofRows.WrittenProof
import Johnson.LPFK10R.WorksLive
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Rounds
open Johnson.G (dryProofFull)
open Johnson.KB8 (walk)
open OnBytes.Params (Rounds)
open Johnson.AtFull.ProofRows (declProofFull walk_of_runs ok_first ok_shared ok_second)

/-- **Where the walk along a declared and a dry list accepts, their entries are one list.** -/
theorem entries_of_walk {e : List (List ByteArray × ByteArray)} :
    ∀ (l : List Fmt.DeclaredRound) (R : Rounds), walk e l R = true →
      l.map (·.entry) = R.map (·.1.entry)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [walk] at h
  | _ :: _, [], h => by simp [walk] at h
  | r :: l, x :: R, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.map_cons, List.map_cons, LPFK10.round_entry h.1.1, entries_of_walk l R h.2]

/-- The first chain. -/
theorem entries_first : declProofFull.1.map (·.entry) = dryProofFull.1.map (·.1.entry) :=
  have h : walk [] declProofFull.1 dryProofFull.1 = true := walk_of_runs _ ok_first
  entries_of_walk _ _ h

/-- The shared chain. -/
theorem entries_shared : declProofFull.2.1.map (·.entry) = dryProofFull.2.1.map (·.1.entry) :=
  have h : walk [] declProofFull.2.1 dryProofFull.2.1 = true := walk_of_runs _ ok_shared
  entries_of_walk _ _ h

/-- The last chain. -/
theorem entries_second : declProofFull.2.2.map (·.entry) = dryProofFull.2.2.map (·.1.entry) :=
  entries_of_walk _ _ (walk_of_runs _ ok_second)

/-- The three as one triple. -/
theorem entries_all :
    (declProofFull.1.map (·.entry), declProofFull.2.1.map (·.entry),
      declProofFull.2.2.map (·.entry)) = P5T.esFull := by
  rw [entries_first, entries_shared, entries_second]
  rfl

/-- **The premise he, from the equation on the declared rounds.** -/
theorem entries_at {Z : ProofFile.Pub} (hP : Z.D = declProofFull) :
    Z.D.1.map (·.entry) = dryProofFull.1.map (·.1.entry) := by
  rw [hP]
  exact entries_first

/-- All three chains. -/
theorem entries_all_at {Z : ProofFile.Pub} (hP : Z.D = declProofFull) :
    (Z.D.1.map (·.entry), Z.D.2.1.map (·.entry), Z.D.2.2.map (·.entry)) = P5T.esFull := by
  rw [hP]
  exact entries_all

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.entries_of_walk
#print axioms Johnson.AtFull.Rounds.entries_first
#print axioms Johnson.AtFull.Rounds.entries_shared
#print axioms Johnson.AtFull.Rounds.entries_second
#print axioms Johnson.AtFull.Rounds.entries_all
#print axioms Johnson.AtFull.Rounds.entries_at
#print axioms Johnson.AtFull.Rounds.entries_all_at
