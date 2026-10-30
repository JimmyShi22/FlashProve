-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofRows/WrittenProof.lean: `writtenOf` (Johnson/G/RoundsOfPlan.lean) lays the
written declared rounds of a proof file of full size as the written dry lists (`dryProofFull`,
Johnson/G/DryProofLit.lean). A general law on lists written as records and runs, and closed
statements by evaluations in Lean's kernel.

How. Both sides are written as records and runs, AND THE RUNS ARE THE SAME: the declared rounds are
the 136 records `declRecsFull` (Johnson/Unfolds/DeclRecsLit.lean) along `dryProofRunsFull0`, `1`,
`2`; the dry lists are the 136 records `dryProofRecsFull` along these same runs. So the test `walk`
(Johnson/HB/LLHARD/KB8/WrittenFull.lean) need not go along 48,293 rounds: it is enough that, run by
run, the declared record is laid as the dry record of the same number (`okRuns`, `walk_of_runs`).

Main names.
  `okPair`, `okRuns`; `walk_append`, `walk_replicate`, `walk_of_runs`: the test and the law.
  `declProofFull`: the written declared rounds.
  `ok_first`, `ok_shared`, `ok_second`; `roots_first`, `roots_shared`: the closed statements: the
    first chain sends 83 trees, the shared 11.
  `written_proof`: **writtenOf "proof file" declProofFull = .ok dryProofFull.**
  `ok_first_bent`, `ok_second_bent`: against the dry records less their first; and where the first
    chain is said to send 82 trees: the tests say no.

It calls `written_of_walks` and `rootsOf_filter` of KB8/WrittenFull.lean.
Limits. Both sides are written values. That `declProofFull` is what `declPOf` returns at any public
files is not said here. No soundness is claimed.
-/
import Johnson.HB.LLHARD.KB8.WrittenFull
import Johnson.Unfolds.DeclRecsLit
import Johnson.G.DryProofLit
import Johnson.G.RunsDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows

open Johnson.G Johnson.G.OfPlan Johnson.G.Runs
open Johnson.KB8 (walk written_of_walks rootsOf_filter)
open OnBytes.Params (Rounds)
open OnBytes.Three (tagRoot tagRun)
open VerifiableInference.PlanWritten (declRecsFull)

/-! ## The law -/

/-- A declared record is laid as a dry record, with the same stored tables. -/
def okPair (e : List (List ByteArray × ByteArray)) (r : Fmt.DeclaredRound)
    (y : Fmt.Round × List Fmt.Stored) : Bool :=
  decide (r.round e = some y.1) && decide (r.stored = y.2)

/-- Run by run: the two records of the run's number fit, or neither list has that number. -/
def okRuns (e : List (List ByteArray × ByteArray)) (A : List Fmt.DeclaredRound)
    (B : List (Fmt.Round × List Fmt.Stored)) (runs : List (Nat × Nat)) : Bool :=
  runs.all fun x =>
    match A[x.2]?, B[x.2]? with
    | some r, some y => okPair e r y
    | none, none => true
    | _, _ => false

theorem walk_append {e : List (List ByteArray × ByteArray)} :
    ∀ (l₁ : List Fmt.DeclaredRound) (R₁ : Rounds) {l₂ : List Fmt.DeclaredRound} {R₂ : Rounds},
      walk e l₁ R₁ = true → walk e l₂ R₂ = true → walk e (l₁ ++ l₂) (R₁ ++ R₂) = true
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, h, _ => by simp [walk] at h
  | r :: l, y :: R, _, _, h, h' => by
    simp only [walk, Bool.and_eq_true] at h
    simp only [List.cons_append, walk, Bool.and_eq_true]
    exact ⟨h.1, walk_append l R h.2 h'⟩

theorem walk_replicate {e : List (List ByteArray × ByteArray)} {r : Fmt.DeclaredRound}
    {y : Fmt.Round × List Fmt.Stored} (h : okPair e r y = true) :
    ∀ n : Nat, walk e (List.replicate n r) (List.replicate n y) = true
  | 0 => rfl
  | n + 1 => by
    unfold okPair at h
    simp only [List.replicate_succ, walk, Bool.and_eq_true]
    exact ⟨Bool.and_eq_true_iff.1 h, walk_replicate (by unfold okPair; exact h) n⟩

/-- **A yes run by run gives the test's yes along the two lists.** -/
theorem walk_of_runs {e : List (List ByteArray × ByteArray)} {A : List Fmt.DeclaredRound}
    {B : List (Fmt.Round × List Fmt.Stored)} :
    ∀ runs : List (Nat × Nat), okRuns e A B runs = true →
      walk e (unrunG A runs) (unrunR B runs) = true
  | [], _ => rfl
  | x :: xs, h => by
    unfold okRuns at h
    rw [List.all_cons, Bool.and_eq_true] at h
    have ih : walk e (unrunG A xs) (unrunR B xs) = true := walk_of_runs xs h.2
    have h₁ := h.1
    unfold unrunG unrunR at ih ⊢
    rw [List.flatMap_cons, List.flatMap_cons]
    refine walk_append _ _ ?_ ih
    cases hA : A[x.2]? with
    | none =>
      cases hB : B[x.2]? with
      | none => rfl
      | some y =>
        rw [hA, hB] at h₁
        cases h₁
    | some r =>
      cases hB : B[x.2]? with
      | none =>
        rw [hA, hB] at h₁
        cases h₁
      | some y =>
        rw [hA, hB] at h₁
        exact walk_replicate h₁ x.1

/-! ## The closed statements -/

/-- The written declared rounds of a proof file of full size. -/
def declProofFull : Decl3 :=
  (unrunG declRecsFull dryProofRunsFull0, unrunG declRecsFull dryProofRunsFull1,
    unrunG declRecsFull dryProofRunsFull2)

set_option maxRecDepth 1000000 in
theorem ok_first : okRuns [] declRecsFull dryProofRecsFull dryProofRunsFull0 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ok_shared : okRuns [] declRecsFull dryProofRecsFull dryProofRunsFull1 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ok_second : okRuns
    [((List.range 83).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]
    declRecsFull dryProofRecsFull dryProofRunsFull2 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem senders_first :
    rootsOf (declProofFull.1.filter fun r => r.entry.roots != 0) = 83 := by decide +kernel

/-- The first chain sends 83 trees. -/
theorem roots_first : rootsOf declProofFull.1 = 83 := by
  rw [rootsOf_filter]
  exact senders_first

set_option maxRecDepth 1000000 in
/-- The shared chain sends eleven. -/
theorem roots_shared : rootsOf declProofFull.2.1 = 11 := by decide +kernel

/-- **`writtenOf` lays the written declared rounds as the written dry lists.** -/
theorem written_proof : writtenOf "proof file" declProofFull = .ok dryProofFull :=
  written_of_walks roots_first roots_shared (walk_of_runs _ ok_first) (walk_of_runs _ ok_shared)
    (walk_of_runs _ ok_second)

/-! ## The tests can fail -/

set_option maxRecDepth 1000000 in
/-- Against the dry records less their first: no. -/
theorem ok_first_bent :
    okRuns [] declRecsFull dryProofRecsFull.tail dryProofRunsFull0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Where the first chain is said to send 82 trees, its last tree cannot be taken over. -/
theorem ok_second_bent : okRuns
    [((List.range 82).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]
    declRecsFull dryProofRecsFull dryProofRunsFull2 = false := by
  decide +kernel

end Johnson.AtFull.ProofRows

#print axioms Johnson.AtFull.ProofRows.walk_append
#print axioms Johnson.AtFull.ProofRows.walk_replicate
#print axioms Johnson.AtFull.ProofRows.walk_of_runs
#print axioms Johnson.AtFull.ProofRows.ok_first
#print axioms Johnson.AtFull.ProofRows.ok_shared
#print axioms Johnson.AtFull.ProofRows.ok_second
#print axioms Johnson.AtFull.ProofRows.senders_first
#print axioms Johnson.AtFull.ProofRows.roots_first
#print axioms Johnson.AtFull.ProofRows.roots_shared
#print axioms Johnson.AtFull.ProofRows.written_proof
#print axioms Johnson.AtFull.ProofRows.ok_first_bent
#print axioms Johnson.AtFull.ProofRows.ok_second_bent
