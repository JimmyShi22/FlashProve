-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/FullPub.lean: the public numbers and shapes of the two lookups of a key of full
size, as closed values, and that they are admissible.

A lookup whose keys come in parts has its public numbers and shapes in a record (`Lk6.Pub`,
Cb/Pv/KeyLookup/Letters.lean), and the statements on such a lookup ask conditions on that record
(`Lk6.Pub.Adm`). This file writes the record out for the two lookups of a key of full size and
proves the conditions. It imports no file of the program.

The first lookup: 12 parts of 2^36 keys; a table of 2^8 rows; 40 real planes of 64; two runs of
padding, both in the last part (the places 25232932864 to 2^35 - 1 and 59592671232 to 2^36 - 1), at
row 0. The second: 12 parts of 2^35 keys; 2^13 rows; 39 real planes of 64; one run of padding in the
last part (the places 22546481152 to 2^35 - 1), at row 0. In both, the first rounds of each part's
last key level bind the variables 2, 1, 0, 5, 4, 3, 8, 7, 6.

Main definitions: `pubFull₁`, `pubFull₂`. Main theorems: `adm_pubFull₁`, `adm_pubFull₂`: all clauses
of `Pub.Adm p`, for every p above 2^d (2^planes - 1). Each clause is evaluated at the closed value,
except that the two runs of the first lookup have no place in common, which is shown by arithmetic.

Where the numbers come from: three public files, typed as Lean values in Johnson/G/KitFull.lean:
prover/examples/target_full_f2:
  policy.txt (2,629 bytes; sha256
    ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae),
  layout.txt (224,975 bytes; sha256
    a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80),
  KL.bin (2,784 bytes; sha256
    1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919).
How they were made: the program's own planning on the copies of these three, run by Lean's
evaluator, printed the two lookups; the numbers were then typed. By what they are held: neither a
test nor a theorem that holds them against the planning's is in this library yet.

Not claimed. That these are the numbers of the program's public files. Nothing on soundness.

-/
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6

/-- The first lookup of a key of full size. -/
def pubFull₁ : Pub :=
  { parts := List.replicate 12 36, d := 8, mu := 6, pl := 40,
    runs := [⟨11, 25232932864, 0, 9126805504⟩, ⟨11, 59592671232, 0, 9126805504⟩],
    padRow := 0, order := [2, 1, 0, 5, 4, 3, 8, 7, 6] }

/-- The second lookup of a key of full size. -/
def pubFull₂ : Pub :=
  { parts := List.replicate 12 35, d := 13, mu := 6, pl := 39,
    runs := [⟨11, 22546481152, 0, 11813257216⟩],
    padRow := 0, order := [2, 1, 0, 5, 4, 3, 8, 7, 6] }

/-- A place of a run is not before the run's first place, and its number in the run is below the
run's length. -/
private theorem holds_bounds (r : Run) (i k : ℕ) (h : r.holds i k = true) :
    r.first ≤ k ∧ (k - r.first) / 2 ^ r.logStep < r.length := by
  unfold Run.holds at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.2⟩

/-- The first lookup's numbers and shapes are admissible. -/
theorem adm_pubFull₁ (p : ℕ) (hp : 2 ^ 8 * (2 ^ 40 - 1) < p) : pubFull₁.Adm p where
  some := by decide
  planes := by decide
  room := by decide
  bits := by decide
  keys := by decide
  pads := by decide
  char := hp
  tabs := by decide
  row := by decide
  inPart := by decide
  apart := by
    show List.Pairwise _ [_, _]
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro b hb i k hc
    obtain rfl : b = ⟨11, 59592671232, 0, 9126805504⟩ := by simpa using hb
    have h1 : (k - 25232932864) / 2 ^ 0 < 9126805504 := (holds_bounds _ i k hc.1).2
    have h2 : 59592671232 ≤ k := (holds_bounds _ i k hc.2).1
    rw [pow_zero, Nat.div_one] at h1
    omega
  notAll := by decide
  order := by decide

/-- The second lookup's numbers and shapes are admissible. -/
theorem adm_pubFull₂ (p : ℕ) (hp : 2 ^ 13 * (2 ^ 39 - 1) < p) : pubFull₂.Adm p where
  some := by decide
  planes := by decide
  room := by decide
  bits := by decide
  keys := by decide
  pads := by decide
  char := hp
  tabs := by decide
  row := by decide
  inPart := by decide
  apart := by
    show List.Pairwise _ [_]
    exact List.pairwise_singleton _ _
  notAll := by decide
  order := by decide

end Lk6

#print axioms Lk6.adm_pubFull₁
#print axioms Lk6.adm_pubFull₂
