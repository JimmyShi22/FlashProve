-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontRuns.lean: WHEN TWO LISTS THAT ARE WRITTEN BY RUNS ARE ONE LIST: a
walker over two lists of runs (how often, which value) that Lean's kernel can follow, with its law.
The two lists' runs may be cut differently. Definitions and laws; nothing is evaluated.

  `outOf l`: a list of runs written out.
  `sameRunsB n a b`: walks a and b together, taking off both fronts the smaller of the two counts;
    in tail position; n: fuel.
  **`sameRuns_sound`**: `sameRunsB n a b = true → outOf a = outOf b`.
  `outOf_val`: `Johnson.G.Runs.unrunG recs runs` (Johnson/G/RunsDefs.lean) is `outOf` of
    `Johnson.G.Runs.valRuns recs runs`; `outOf_map`: a function goes through.
Limits. General: no value is treated. One direction. Nothing on soundness. On hiding nothing.

-/
import Johnson.G.RunsDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open Johnson.G.Runs (unrunG valRuns)

variable {α β : Type}

/-- A list of runs, written out. -/
def outOf : List (Nat × α) → List α
  | [] => []
  | x :: xs => List.replicate x.1 x.2 ++ outOf xs

/-- The two lists of runs, walked together. -/
def sameRunsB [DecidableEq α] : Nat → List (Nat × α) → List (Nat × α) → Bool
  | _, [], [] => true
  | 0, _, _ => false
  | n + 1, (0, _) :: xs, ys => sameRunsB n xs ys
  | n + 1, xs, (0, _) :: ys => sameRunsB n xs ys
  | n + 1, (i + 1, a) :: xs, (j + 1, b) :: ys =>
    if a = b then
      if i + 1 ≤ j + 1 then sameRunsB n xs ((j + 1 - (i + 1), b) :: ys)
      else sameRunsB n ((i + 1 - (j + 1), a) :: xs) ys
    else false
  | _ + 1, _, _ => false

theorem replicate_split (a : α) {i j : Nat} (h : i ≤ j) :
    List.replicate j a = List.replicate i a ++ List.replicate (j - i) a := by
  rw [List.replicate_append_replicate, Nat.add_sub_cancel' h]

/-- **A yes of the walker: the two lists, written out, are one.** -/
theorem sameRuns_sound [DecidableEq α] : ∀ (n : Nat) (a b : List (Nat × α)),
    sameRunsB n a b = true → outOf a = outOf b := by
  intro n
  induction n with
  | zero =>
    intro a b h
    cases a <;> cases b <;> first | rfl | (simp [sameRunsB] at h)
  | succ n ih =>
    intro a b h
    match a, b, h with
    | [], [], _ => rfl
    | (0, x) :: xs, ys, h =>
      have h' : sameRunsB n xs ys = true := by
        cases ys <;> simpa [sameRunsB] using h
      simpa [outOf] using ih xs ys h'
    | [], (0, y) :: ys, h =>
      have h' : sameRunsB n [] ys = true := by simpa [sameRunsB] using h
      simpa [outOf] using ih [] ys h'
    | (i + 1, x) :: xs, (0, y) :: ys, h =>
      have h' : sameRunsB n ((i + 1, x) :: xs) ys = true := by simpa [sameRunsB] using h
      simpa [outOf] using ih _ ys h'
    | (i + 1, x) :: xs, (j + 1, y) :: ys, h =>
      unfold sameRunsB at h
      by_cases e : x = y
      · subst e
        rw [if_pos rfl] at h
        by_cases l : i + 1 ≤ j + 1
        · rw [if_pos l] at h
          have := ih _ _ h
          simp only [outOf] at this ⊢
          rw [replicate_split x l, List.append_assoc, this]
        · rw [if_neg l] at h
          have := ih _ _ h
          simp only [outOf] at this ⊢
          rw [replicate_split x (Nat.le_of_lt (Nat.lt_of_not_le l)), List.append_assoc, this]
      · rw [if_neg e] at h
        cases h
    | [], (j + 1, y) :: ys, h => simp [sameRunsB] at h
    | (i + 1, x) :: xs, [], h => simp [sameRunsB] at h

theorem outOf_val (recs : List α) : ∀ runs : List (Nat × Nat),
    unrunG recs runs = outOf (valRuns recs runs)
  | [] => rfl
  | x :: xs => by
    have ih := outOf_val recs xs
    unfold unrunG at ih ⊢
    rw [List.flatMap_cons, ih, valRuns]
    cases recs[x.2]? <;> rfl

theorem outOf_map (f : α → β) : ∀ l : List (Nat × α),
    (outOf l).map f = outOf (l.map fun x => (x.1, f x.2))
  | [] => rfl
  | x :: xs => by
    simp only [outOf, List.map_append, List.map_replicate, List.map_cons, outOf_map f xs]

end H2K5.Row

#print axioms H2K5.Row.sameRuns_sound
#print axioms H2K5.Row.outOf_val
#print axioms H2K5.Row.outOf_map
