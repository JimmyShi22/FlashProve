-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FrameLens.lean: the lengths of the lists of rounds that the frame of a
proximity test (the kind K12) hands from stage to stage.

Theorems on the lengths of lists alone; no Mathlib beneath. `stagesFrom`
(Johnson/Desc/K12/Frame.lean) cuts the rounds that are still to be dealt by `take` and `drop`; at a
list that is too short these cuts shrink without a word. The block's test on the plan asks the whole
number once (`rs.length == roundsIn stages` and `p.oracles.length == rs.length`). Whoever ties a
part's rounds to the written rounds of a chain needs the numbers at every stage: 1 + k for a fold, 2
for a switch and 2 for the base case.
Main names:
  `roundsFor cur rest`: the rounds that the stages from `cur` on need: k + 3 for each stage but the
    last, then 2.
  `roundsIn_cons`: `roundsIn (first :: rest) = 1 + roundsFor first rest`.
  `lens_step`: where a list has `roundsFor cur (next :: rest)` members, the fold's slice has 1 +
    cur.k, the switch's has 2, and what is handed on has `roundsFor next rest`.
  `lens_last`: at the last stage the list has 2 members.
  `lens_top`: where the block's test on the plan says yes, the batching's slice has 1 member and
    what is handed to the first stage has `roundsFor first rest`.
Limits: Nothing is said on what a part decides, and nothing on soundness.

-/
import Johnson.Desc.K12.Frame

set_option autoImplicit false
namespace H2K.FrameLens
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The rounds that the stages from `cur` on need. -/
def roundsFor : Fmt.M1.Stage → List Fmt.M1.Stage → Nat
  | _, [] => 2
  | cur, next :: rest => cur.k + 3 + roundsFor next rest

/-- The sum that `roundsIn` takes over all stages but the last, with 2 more, is `roundsFor`. -/
theorem sum_dropLast (cur : Fmt.M1.Stage) : ∀ (rest : List Fmt.M1.Stage),
    (((cur :: rest).dropLast.map (·.k + 3)).sum) + 2 = roundsFor cur rest := by
  intro rest
  induction rest generalizing cur with
  | nil => simp [roundsFor]
  | cons next rest ih =>
    have h := ih next
    simp only [List.dropLast_cons₂, List.map_cons, List.sum_cons, roundsFor]
    omega

/-- The frame's count of a test's rounds: one for the batching, then `roundsFor`. -/
theorem roundsIn_cons (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    roundsIn (first :: rest) = 1 + roundsFor first rest := by
  have h := sum_dropLast first rest
  unfold roundsIn
  omega

/-- A stage but the last: the lengths of the fold's slice, of the switch's, and of what is handed
on. -/
theorem lens_step {α : Type} (l : List α) (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (h : l.length = roundsFor cur (next :: rest)) :
    (l.take (1 + cur.k)).length = 1 + cur.k ∧ ((l.drop (1 + cur.k)).take 2).length = 2 ∧
      (l.drop (cur.k + 3)).length = roundsFor next rest := by
  have h2 : 2 ≤ roundsFor next rest := by cases rest <;> simp [roundsFor] <;> omega
  simp only [roundsFor] at h
  simp only [List.length_take, List.length_drop]
  omega

/-- The last stage: two rounds are left. -/
theorem lens_last {α : Type} (l : List α) (cur : Fmt.M1.Stage) (h : l.length = roundsFor cur []) :
    l.length = 2 := by simpa [roundsFor] using h

/-- The top, at any parts: what a yes of the block's own test on the plan gives on the lengths. -/
theorem lens_top {T Cl : Type} (X : Parts T) (p : P12) (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    ∃ (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (rds : List Fmt.DeclaredRound),
      p.nums.stages = first :: rest ∧ H2U.roundsOfNums p.nums = some rds ∧
      ((rds.zip p.oracles).take 1).length = 1 ∧
      ((rds.zip p.oracles).drop 1).length = roundsFor first rest := by
  simp only [proximityTestKind] at hp
  split at hp
  · rename_i first rest rds os h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hl : rds.length = roundsIn p.nums.stages := hp.1.1.1.2
    have ho : p.oracles.length = rds.length := hp.1.1.2
    rw [h1, roundsIn_cons] at hl
    refine ⟨first, rest, rds, h1, h2, ?_, ?_⟩
    · simp only [List.length_take, List.length_zip]; omega
    · simp only [List.length_drop, List.length_zip]; omega
  · simp at hp

end H2K.FrameLens
