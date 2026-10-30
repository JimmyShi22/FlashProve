-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Value.lean: the left-hand side of an equation (OnBytes.Row) on words, at a
statement S (Means.value, Johnson/Desc/Means/Says.lean), is additive in the words, and on words that
are 0 except at one index inside the tables of S it is the equation's coefficient there times the
entry.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model"; Johnson/SendSim/At/Sim.lean, "Terms". Limits
of the folder: Johnson/SendSim/Defs.lean.

An equation here is OnBytes.Row, which the library calls a row; it is not a row of the model. It has
a coefficient on each index of each table (main or mask) of each oracle message. Words (Means.Words)
give each such index a value.

What this file proves, for every commutative ring, reading of coefficients, statement S and
equation.
  onTable_add, value_add   The left-hand side on a sum of two families of words is the sum of the
                           two left-hand sides.
  oneAt                    The definition: the words with s at (oracle message o, table part, index
                           j), and 0 elsewhere.
  onTable_oneAt, onTable_oneAt_ne   An equation applied to one table of such words.
  value_oneAt              If S has the oracle message o and j is inside its table, the left-hand
                           side on oneAt o part j s is the coefficient at (o, part, j) times s.
  value_add_oneAt          So, under the same two premises, adding s at one index adds the
                           coefficient there times s.

Limits. Outside the statement's tables the left-hand side reads nothing, so nothing is said there.

How it fits. value_sampleRow_pad (Johnson/SendSim/Tie/Sample.lean) applies value_add_oneAt to an
answer's equation. No other file of Johnson/SendSim/ uses these lemmas, and no file applies
value_sampleRow_pad, so this file serves none of the folder's main theorems.
-/
import Johnson.Desc.Means.Says

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes OnBytes.Means

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- An equation applied to one table is additive in the words. -/
theorem onTable_add (S : Statement) (r : Row) (m m' : Words K) (o : ℕ) (part : Part) :
    onTable ρ S r (m + m') o part = onTable ρ S r m o part + onTable ρ S r m' o part := by
  unfold onTable
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => mul_add _ _ _

/-- The left-hand side of an equation on a sum of two families of words is the sum of its left-hand
sides on the two. -/
theorem value_add (S : Statement) (r : Row) (m m' : Words K) :
    value ρ S r (m + m') = value ρ S r m + value ρ S r m' := by
  unfold value
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [onTable_add, onTable_add]
  ring

open Classical in
/-- The words with s at (oracle message o, table part, index j), and 0 elsewhere. -/
noncomputable def oneAt (o : ℕ) (part : Part) (j : ℕ) (s : K) : Words K := fun o' p' j' =>
  if o' = o ∧ p' = part ∧ j' = j then s else 0

/-- If j is inside the table (o, part), an equation applied to that table of oneAt o part j s is its
coefficient there times s. -/
theorem onTable_oneAt (S : Statement) (r : Row) (o : ℕ) (part : Part) (j : ℕ) (s : K)
    (hj : j < tableSize S o part) :
    onTable ρ S r (oneAt o part j s) o part = ρ.val (r.coefficient o part j) * s := by
  unfold onTable
  rw [Finset.sum_eq_single j]
  · rw [show oneAt o part j s o part j = s from if_pos ⟨rfl, rfl, rfl⟩]
  · intro i _ hi
    rw [show oneAt o part j s o part i = 0 from if_neg fun h => hi h.2.2, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

/-- An equation applied to any other table of oneAt o part j s is 0. -/
theorem onTable_oneAt_ne (S : Statement) (r : Row) (o : ℕ) (part : Part) (j : ℕ) (s : K) (o' : ℕ)
    (p' : Part) (h : ¬ (o' = o ∧ p' = part)) : onTable ρ S r (oneAt o part j s) o' p' = 0 := by
  unfold onTable
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show oneAt o part j s o' p' i = 0 from if_neg fun e => h ⟨e.1, e.2.1⟩, mul_zero]

/-- If the statement has the oracle message o and j is inside its table part, the left-hand side of
an equation on oneAt o part j s is the equation's coefficient at (o, part, j) times s. -/
theorem value_oneAt (S : Statement) (r : Row) (o : ℕ) (part : Part) (j : ℕ) (s : K)
    (ho : o < S.oracles.size) (hj : j < tableSize S o part) :
    value ρ S r (oneAt o part j s) = ρ.val (r.coefficient o part j) * s := by
  unfold value
  rw [Finset.sum_eq_single o]
  · cases part
    · rw [onTable_oneAt ρ S r o .main j s hj,
        onTable_oneAt_ne ρ S r o .main j s o .mask (fun e => by cases e.2), add_zero]
    · rw [onTable_oneAt ρ S r o .mask j s hj,
        onTable_oneAt_ne ρ S r o .mask j s o .main (fun e => by cases e.2), zero_add]
  · intro o' _ h
    rw [onTable_oneAt_ne ρ S r o part j s o' .main (fun e => h e.1),
      onTable_oneAt_ne ρ S r o part j s o' .mask (fun e => h e.1), add_zero]
  · intro h
    exact absurd (Finset.mem_range.2 ho) h

/-- Under the same two premises, adding s to the words at (o, part, j) adds the equation's
coefficient there times s to the left-hand side. -/
theorem value_add_oneAt (S : Statement) (r : Row) (m : Words K) (o : ℕ) (part : Part) (j : ℕ)
    (s : K) (ho : o < S.oracles.size) (hj : j < tableSize S o part) :
    value ρ S r (m + oneAt o part j s) = value ρ S r m + ρ.val (r.coefficient o part j) * s := by
  rw [value_add, value_oneAt ρ S r o part j s ho hj]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.value_add
#print axioms OnBytes.SendSim.value_oneAt
#print axioms OnBytes.SendSim.value_add_oneAt
