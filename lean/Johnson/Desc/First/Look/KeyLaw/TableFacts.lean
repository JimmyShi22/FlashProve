-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/TableFacts.lean: facts on numbers for the range table: the
multilinear extension of "the corner's number"; a row of the range table, read.

Main names:
  mle_coord, mle_numLE: the extension of a coordinate's bit; of the numbers of the cube's corners.
  numLE_lt: a corner's number is below 2 ^ k.
  bitsVal_take: the weighted sum of the first d members of a list.
  read_rowAt: row t of the range table of a key file's lookup, read, is the number t.

Limits. Nothing on any other table.

-/
import OnBytes.Slice.BlkTableRead
import Cb.Ld.LdLkpNumProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid

open OnBytes OnBytes.Slice OnBytes.Slice.Planes Cb Cb.LdLkp
open OnBytes.Params (WfLookup)

/-- The extension of a coordinate's bit is the coordinate. -/
theorem mle_coord {k : ℕ} (j : Fin k) (z : Fin k → GE) :
    Alg.mle (fun b : Fin k → Bool => if b j then (1 : GE) else 0) z = z j :=
  ((Alg.DegLE.coord j).eq_mle (fun _ => le_refl 1) z).symm

/-- The extension of the numbers of the cube's corners. -/
theorem mle_numLE {k : ℕ} (z : Fin k → GE) :
    Alg.mle (fun r : Fin k → Bool => ((numLE r : ℕ) : GE)) z = ∑ t : Fin k, 2 ^ (t : ℕ) * z t := by
  have e : (fun r : Fin k → Bool => ((numLE r : ℕ) : GE)) =
      fun r => ∑ t : Fin k, 2 ^ (t : ℕ) * (if r t then (1 : GE) else 0) := by
    funext r
    unfold numLE
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : r t <;> simp [h]
  rw [e, Alg.mle_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Alg.mle_smul, mle_coord]

theorem numLE_lt {k : ℕ} (r : Fin k → Bool) : numLE r < 2 ^ k := by
  rw [numLE_ofBits]
  exact Nat.ofBits_lt_two_pow _

/-- `bitsVal` of the first d members of a list. -/
theorem bitsVal_take : ∀ (d : ℕ) (q : List GE),
    bitsVal (q.take d) = ∑ t : Fin d, 2 ^ (t : ℕ) * q.getD t 0
  | 0, q => by simp [bitsVal]
  | d + 1, [] => by simp [bitsVal]
  | d + 1, x :: xs => by
    rw [List.take_succ_cons, bitsVal, bitsVal_take d xs, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [_root_.one_mul]
    refine congrArg (x + ·) (Finset.sum_congr rfl fun t _ => ?_)
    ring

/-- A row of the range table, read. -/
theorem read_rowAt (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (θ : E) (t : ℕ) (h : t < 2 ^ l.d)
    (hd : l.d ≤ 64) : readE (Lkp.rowAt (Wf.lookupOf id m l) θ t) = (t : GE) := by
  have h64 : t < 2 ^ 64 := lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hd)
  have hr : Lkp.rowAt (Wf.lookupOf id m l) θ t =
      addE (Lkp.natE (t % 2 ^ l.d)) (mulE (Lkp.natE 0) θ) := by
    unfold Lkp.rowAt
    simp [Wf.lookupOf, h]
  rw [hr, readE_add, readE_mul, Nat.mod_eq_of_lt h, Leaves.read_natE _ h64,
    Leaves.read_natE 0 (by decide), Nat.cast_zero, zero_mul, add_zero]

end Lk6.Mid

#print axioms Lk6.Mid.mle_numLE
#print axioms Lk6.Mid.bitsVal_take
#print axioms Lk6.Mid.read_rowAt
