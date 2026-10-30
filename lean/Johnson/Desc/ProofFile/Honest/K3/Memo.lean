-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Memo.lean: an array that stands for a function on the numbers below
its size. Definitions with code, and theorems without a hypothesis.

Terms. In this file: a table of a function f is an array whose entry number i is f i.

What is defined.
  `Memo.read a f i`: the array's entry number i where there is one; f i beyond the array's end.
  `Memo.tab n f`: the table of f on the numbers below n.
  `Memo.tab2 m k f`: of a function of two numbers: m tables, number i that of f i below k.
  `Memo.read2 a f i j`: `read` at row number i of an array of arrays; beyond the rows, f i j.

What is shown.
  `read_tab`: read at the table of f is f: at every number, below the table's end or beyond it.
  `read_empty`: read at the empty array is f.
  `getD_tab`: a table's entry by `getD`: f i below the end, the fallback beyond.
  `read_row`: read at row number i of `tab2 m k f` (the empty array beyond the rows) is f i.
  `read2_tab2`: `read2` at `tab2 m k f` is f.

How it is meant. `read` takes the array: whoever wants a table made once binds `tab n f` by a let in
front of the function that reads it. A function that took n and f and made the array itself would
make it anew at every call. As f itself is read beyond the end, no statement needs a bound on a
number.

Imported. Nothing.

Users. This file is imported by Honest/K3/DigitsTabCore.lean, Honest/K3/Tab/SisterG.lean,
Honest/K3/Tab/TabH.lean and Honest/K3/Tab/TabG.lean; Honest/K3/WitDigitsTab.lean has it through the
first.

Limits. Nothing says how long anything takes.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Memo

variable {α : Type}

/-- The array's entry number i where there is one; f i beyond the array's end. -/
def read (a : Array α) (f : Nat → α) (i : Nat) : α := if h : i < a.size then a[i] else f i

/-- The table of f on the numbers below n. Kin in the library, not tied here:
`IntegerTransformer.tabulate` (IntegerModel/Model.lean), by `Array.ofFn`. -/
def tab (n : Nat) (f : Nat → α) : Array α := (Array.range n).map f

/-- m tables: number i is that of f i on the numbers below k. -/
def tab2 (m k : Nat) (f : Nat → Nat → α) : Array (Array α) := tab m fun i => tab k (f i)

/-- `read` at row number i of an array of arrays; beyond the rows, f i j. -/
def read2 (a : Array (Array α)) (f : Nat → Nat → α) (i j : Nat) : α := read (a.getD i #[]) (f i) j

/-- **Read at the table of f is f.** -/
theorem read_tab (n : Nat) (f : Nat → α) (i : Nat) : read (tab n f) f i = f i := by
  unfold read tab
  by_cases h : i < n
  · simp [h]
  · simp [h]

/-- Read at the empty array is f. -/
theorem read_empty (f : Nat → α) (i : Nat) : read #[] f i = f i := by
  simp [read]

/-- A table's entry, or the fallback beyond its end. -/
theorem getD_tab (n : Nat) (f : Nat → α) (i : Nat) (d : α) :
    (tab n f).getD i d = if i < n then f i else d := by
  unfold tab
  by_cases h : i < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- **Read at row number i of `tab2 m k f` is f i.** -/
theorem read_row (m k : Nat) (f : Nat → Nat → α) (i j : Nat) :
    read ((tab2 m k f).getD i #[]) (f i) j = f i j := by
  unfold tab2
  rw [getD_tab]
  by_cases h : i < m
  · rw [if_pos h]
    exact read_tab k (f i) j
  · rw [if_neg h]
    exact read_empty (f i) j

/-- **`read2` at `tab2 m k f` is f.** -/
theorem read2_tab2 (m k : Nat) (f : Nat → Nat → α) (i j : Nat) :
    read2 (tab2 m k f) f i j = f i j := read_row m k f i j

end ProofFile.Honest.K3.Memo

#print axioms ProofFile.Honest.K3.Memo.read_tab
#print axioms ProofFile.Honest.K3.Memo.read_empty
#print axioms ProofFile.Honest.K3.Memo.getD_tab
#print axioms ProofFile.Honest.K3.Memo.read_row
#print axioms ProofFile.Honest.K3.Memo.read2_tab2
