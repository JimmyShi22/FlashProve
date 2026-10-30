-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/SizeOf.lean: the sizes of the typed smallness test (Cb/Pv/Tail/Tables.lean) read
off the record that the Lean verifier keeps of a sub-proof's smallness test.

The verifier's record is HTailF2 (OnBytes/Model/Tail.lean). The typed block takes its public
numbers as a TSize. This file has the one function from the first to the second, and says that what
the planner reads of the record (smallSize, OnBytes/Model/RoundSizes.lean) is what it reads of
these sizes. Definitions, statements and proofs.

Main names:
  `sizeOf tl`: the number of matrices; each matrix's rows of cells and columns; tau; the radix of
    the packing; the sizes of the two digits' tables; the shift; the tables of reads, as the
    record's closed list has them.
  `sizeOf_ok`: the two digits together do not reach beyond twice the shift.
  `sizeOf_columns`: if the record's number of matrices is the length of its list, the columns of
    all matrices together are the record's foldColumns.
  `smallSize_eq`: under the same premise the planner's record of the test is smallOf at these
    sizes.
  `before_eq`: the number of columns before matrix μ, as the verifier's second computation has it
    (the test of a tie's weights), is firstCol (OnBytes/Tie/Pv/Tail/Draw.lean). The first
    computation (foldSums) takes the number from the field cfFirst: OnBytes/Tie/Pv/Tail/First.lean.

Limits: nothing here says that a record is well made. That its number of matrices is the length of
its list is a premise. The moment matters: the record's list of tables is empty until the verifier
closes it (closeFuns); at an earlier record sizeOf has no table, and the typed block then speaks of
the packing alone. Whoever takes the block's letters from sizeOf must take the record that the
smallness test's messages start from, at which the verifier has tested that the list is closed
(funClosed). Of a table the field that says which vector holds it is dropped: the typed block has
one vector of reads, and in this verifier every table lies in that one. The tables' weights are no
part of the sizes: they are letters of the explicit statement.
-/
import OnBytes.Model.RoundSizes
import OnBytes.Tie.Pv.Tail.TieBlock
import OnBytes.Tie.Pv.Tail.Draw
import Cb.Pv.Tail.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open OnBytes OnBytes.Model OnBytes.Params Cb.Pv.Tail

/-- The sizes of the typed smallness test, read off the verifier's record. -/
def sizeOf (tl : HTailF2) : TSize where
  NM := tl.NM
  m := fun μ => (tl.mats.getD μ {}).m
  k := fun μ => (tl.mats.getD μ {}).k
  tau := tl.tau
  rad := radb
  lo := 2 ^ t2D0
  hi := 2 ^ t2D1
  beta := 2 ^ lbz
  tabs := tl.funs.toList.map fun Fn => ⟨Fn.mat, Fn.len, Fn.start⟩

/-- The two digits together do not reach beyond twice the shift. -/
theorem sizeOf_ok (tl : HTailF2) : (sizeOf tl).size.OK := by
  show 2 ^ t2D0 * 2 ^ t2D1 ≤ 2 * 2 ^ lbz
  decide

theorem sizeOf_tau (tl : HTailF2) : (sizeOf tl).size.tau = tl.tau := rfl

/-- A sum that is gathered from the left. -/
theorem foldl_add {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun s x => s + f x) a = a + (l.map f).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_add f l, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- The sum of a list, place by place. -/
theorem sum_range_getD {α : Type} (f : α → ℕ) (d : α) : ∀ l : List α,
    ∑ i ∈ Finset.range l.length, f (l.getD i d) = (l.map f).sum
  | [] => by simp
  | x :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons,
      ← sum_range_getD f d l, Nat.add_comm]
    simp

/-- The sum over the numbers below n, as a list and as a finite sum. -/
theorem sum_map_range (g : ℕ → ℕ) : ∀ n : ℕ,
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_map_range g n,
      Finset.sum_range_succ]
    simp

/-- The columns of all matrices together. -/
theorem sizeOf_columns (tl : HTailF2) (h : tl.NM = tl.mats.size) :
    (sizeOf tl).size.columns = tl.foldColumns := by
  show ∑ μ : Fin tl.NM, (tl.mats.getD μ.val {}).k = tl.mats.foldl (fun s M => s + M.k) 0
  rw [Fin.sum_univ_eq_sum_range (fun i => (tl.mats.getD i {}).k), h, ← Array.foldl_toList,
    foldl_add, Nat.zero_add, ← sum_range_getD (fun M : TMat => M.k) {}]
  simp

/-- What the planner reads of the record is what it reads of these sizes. -/
theorem smallSize_eq (tl : HTailF2) (h : tl.NM = tl.mats.size) :
    smallSize tl = smallOf (sizeOf tl).size (forestSize tl.f9) := by
  show ({ columns := tl.foldColumns, tau := tl.tau, digits := forestSize tl.f9 } : SmallSize) =
    { columns := (sizeOf tl).size.columns, tau := tl.tau, digits := forestSize tl.f9 }
  rw [sizeOf_columns tl h]

/-- The number of columns before matrix μ, as the verifier's test of a tie computes it. -/
theorem before_eq (tl : HTailF2) (μ : Fin (sizeOf tl).size.NM) :
    (List.range μ.val).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0 =
      firstCol (sizeOf tl).size μ := by
  rw [foldl_add, Nat.zero_add, sum_map_range]
  show _ = ∑ ν : Fin μ.val, (tl.mats.getD ν.val {}).k
  rw [Fin.sum_univ_eq_sum_range (fun i => (tl.mats.getD i {}).k)]

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.sizeOf_ok
#print axioms OnBytes.Tie.Pv.Tail.sizeOf_columns
#print axioms OnBytes.Tie.Pv.Tail.smallSize_eq
#print axioms OnBytes.Tie.Pv.Tail.before_eq
