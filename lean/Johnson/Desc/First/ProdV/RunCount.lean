--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/RunCount.lean: the grand product: the error as a number. Round by round,
how many elements of the field the law's bad sets have at most
(Johnson/Desc/First/ProdV/LevelSound.lean, Johnson/Desc/First/ProdV/Chain.lean); the sums; the sums
at the public numbers of two stored proofs. Definitions, statements and proofs; plain arithmetic.

`levelErr m`: one number for each of the level's m + 4 rounds, in the order of levelEntries: PSC
epsilon 1; PSC round 2, m times; PSC Y 2; PSC values 0 (nothing is drawn); LINE 1. `runErr m0 n`:
the same for a run, in the order of runEntries. `runBad' m0 n`: its sum, n * n + (2 * m0 + 3) * n.
`lookBad v d`: a lookup's two runs: run 0 v and run 5 d. `small_bad`, `full_bad`: 10,394 and
64,848.

Limits. What is a theorem: the count of bad elements of the field, round by round and summed
(here); that 64,848 * 2^175 is less than the number of elements of Cb.Gl.E, and that among drawn
values with words below the prime there are no more bad drawn values than bad elements
(Johnson/Desc/First/ProdV/Drawn.lean). What is prose: the union bound over the rounds; the division
by the field's size; that a round's element is drawn evenly among the values with words below the
prime. The pairs (v, d) of the 10 and 50 lookups are data, typed by hand from a print of Lean's
over the library's typed public bytes: no theorem ties these lists to the plans.
Not claimed: any probability.

-/
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.ProdV

/-- How many bad elements a round of the level with m variables has at most. -/
def levelErr (m : ℕ) : List ℕ := 1 :: (List.replicate m 2 ++ [2, 0, 1])

theorem levelErr_length (m : ℕ) : (levelErr m).length = m + 4 := by
  simp [levelErr]

theorem levelErr_sum (m : ℕ) : (levelErr m).sum = 2 * m + 4 := by
  simp [levelErr, List.sum_replicate]
  omega

/-- The same for a run of n levels with m0, m0 + 1, .. variables. -/
def runErr (m0 n : ℕ) : List ℕ := (List.range n).flatMap fun i => levelErr (m0 + i)

/-- THE COUNT of a run. -/
def runBad' (m0 n : ℕ) : ℕ := ((List.range n).map fun i => 2 * (m0 + i) + 4).sum

theorem runErr_sum (m0 n : ℕ) : (runErr m0 n).sum = runBad' m0 n := by
  unfold runErr runBad'
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.sum_append, ih, List.map_append, List.sum_append]
    simp [levelErr_sum]

theorem runBad'_succ (m0 n : ℕ) : runBad' m0 (n + 1) = runBad' m0 n + (2 * (m0 + n) + 4) := by
  unfold runBad'
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- In closed form. -/
theorem runBad'_eq (m0 n : ℕ) : runBad' m0 n = n * n + (2 * m0 + 3) * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [runBad'_succ, ih]
    ring

/-- A lookup's two runs: the key side's v levels from the root; the table side's d levels from five
coordinates. -/
def lookBad (v d : ℕ) : ℕ := runBad' 0 v + runBad' 5 d

/-- The lookups of the small stored proof: (v, d), how many. DATA. -/
def smallLooks : List ((ℕ × ℕ) × ℕ) :=
  [((24, 19), 2), ((24, 11), 3), ((22, 18), 2), ((23, 11), 2), ((23, 19), 1)]

/-- The lookups of the full-size stored proof: (v, d), how many. DATA. -/
def fullLooks : List ((ℕ × ℕ) × ℕ) :=
  [((30, 19), 12), ((27, 11), 13), ((29, 18), 12), ((26, 11), 12), ((31, 19), 1)]

def looksCount (l : List ((ℕ × ℕ) × ℕ)) : ℕ := (l.map (·.2)).sum
def looksLevels (l : List ((ℕ × ℕ) × ℕ)) : ℕ := (l.map fun x => x.2 * (x.1.1 + x.1.2)).sum
def looksBad (l : List ((ℕ × ℕ) × ℕ)) : ℕ := (l.map fun x => x.2 * lookBad x.1.1 x.1.2).sum

example : looksCount smallLooks = 10 := by first | rfl | decide
example : looksCount fullLooks = 50 := by first | rfl | decide
example : looksLevels smallLooks = 381 := by first | rfl | decide
example : looksLevels fullLooks = 2140 := by first | rfl | decide
/-- THE PART's WHOLE COUNT AT THE SMALL PROOF. -/
theorem small_bad : looksBad smallLooks = 10394 := by first | rfl | decide
/-- THE PART's WHOLE COUNT AT THE FULL SIZE. -/
theorem full_bad : looksBad fullLooks = 64848 := by first | rfl | decide
/-- The largest lookup at the full size. -/
example : lookBad 31 19 = 1662 := by first | rfl | decide

end VerifiableInference.Desc.First.ProdV
