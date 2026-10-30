-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxTables.lean: the two tables that the program fills with several members'
symbols, and the three folded words of any readers.

Before a code switch the program reads the rows of a group at the listed positions
(OnBytes/Iop/Fold.lean: singleRowsSymbols). At each position it writes each member's symbols into a
main table and a mask table, from the first row of the member's block on, over zeros, and folds the
tables. OnBytes/Slice/BlkCsRead.lean (symS_of_cols) concludes that the symbols read are the long
symbols of three folded words, if the tables have the entries of a column in the format's form. This
file has two things for a group of any members. First, what an entry of such a table is: a member's
symbol, if the row is in that member's block and in no other's; zero, if it is in no block. Second,
symS_of_cols for words that are given by readers, functions from a position and a row's number to
the field, with no format between.

Main definitions.
  putAll     a table, entry by entry, as n members' columns fill it.
  wordOf, freshOf   the word of main rows and carried mask rows, and the word of fresh mask rows,
             from readers.
  colOf      columns in the format's form that have the readers' values.
Main theorems.
  mainAt_eq, maskAt_eq   the program's two tables are cases of putAll.
  putAll_hit, putAll_miss   an entry in one member's block; an entry in no block.
  wordIn_colOf, wordFr_colOf   the standard readings of colOf are wordOf and freshOf.
  symS_of_tables   if the program's two tables and its fresh column are read as the readers' values
             at each listed position, the symbols read are the long symbols of the three folded
             words of wordOf and freshOf.

Not claimed. Nothing on where the readers' values come from.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkCsRead
import OnBytes.Slice.BlkCuts

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb _root_.Run

/-! ## A table that several members fill -/

/-- A table, entry by entry, as the columns of the members number 0 to n - 1 fill it, over zeros.
first w: the first row of the block of member w, if it has one. col w: its symbols. -/
def putAll (n : ℕ) (first : ℕ → Option ℕ) (col : ℕ → Array E) : ℕ → E :=
  (List.range n).foldl (fun base w => putAt (first w) (col w) base) fun _ => zeroE

/-- The program's main table of a listed position. -/
theorem mainAt_eq (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    mainAt L opened i =
      putAll L.members.size (fun w => L.mainFirst.getD w none) fun w => (colB opened w i).main :=
  rfl

/-- The program's mask table of a listed position. -/
theorem maskAt_eq (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    maskAt L opened i =
      putAll L.members.size (fun w => L.maskFirst.getD w none) fun w => (colB opened w i).mask :=
  rfl

/-- One member more. -/
theorem putAll_succ (n : ℕ) (first : ℕ → Option ℕ) (col : ℕ → Array E) :
    putAll (n + 1) first col = putAt (first n) (col n) (putAll n first col) := by
  unfold putAll
  rw [List.range_succ, List.foldl_append]
  rfl

/-- An entry outside a member's block is as it was before the member's symbols were put. -/
theorem putAt_out (first : Option ℕ) (col : Array E) (base : ℕ → E) (b : ℕ)
    (h : ∀ f, first = some f → b < f ∨ f + col.size ≤ b) : putAt first col base b = base b := by
  unfold putAt
  cases first with
  | none => rfl
  | some f =>
    have := h f rfl
    exact if_neg (by omega)

/-- An entry in no member's block is zero. -/
theorem putAll_miss (first : ℕ → Option ℕ) (col : ℕ → Array E) (b : ℕ) : ∀ n : ℕ,
    (∀ w, w < n → ∀ f, first w = some f → b < f ∨ f + (col w).size ≤ b) →
    putAll n first col b = zeroE
  | 0, _ => rfl
  | n + 1, h => by
    rw [putAll_succ, putAt_out _ _ _ _ (h n (Nat.lt_succ_self n))]
    exact putAll_miss first col b n fun w hw => h w (Nat.lt_succ_of_lt hw)

/-- An entry in the block of the member w, and in no other member's, is that member's symbol. -/
theorem putAll_hit (first : ℕ → Option ℕ) (col : ℕ → Array E) (w f r : ℕ)
    (hf : first w = some f) (hr : r < (col w).size) : ∀ n : ℕ, w < n →
    (∀ w', w' < n → w' ≠ w → ∀ f', first w' = some f' →
      f + r < f' ∨ f' + (col w').size ≤ f + r) →
    putAll n first col (f + r) = (col w).getD r zeroE
  | 0, hw, _ => absurd hw (Nat.not_lt_zero _)
  | n + 1, hw, h => by
    rw [putAll_succ]
    by_cases e : w = n
    · subst e
      unfold putAt
      rw [hf]
      show (if f ≤ f + r ∧ f + r < f + (col w).size then (col w).getD (f + r - f) zeroE else _) = _
      rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hr _⟩, Nat.add_sub_cancel_left]
    · rw [putAt_out _ _ _ _ (h n (Nat.lt_succ_self n) fun e' => e e'.symm)]
      exact putAll_hit first col w f r hf hr n (by omega) fun w' hw' => h w' (Nat.lt_succ_of_lt hw')

/-! ## Words from readers -/

section
variable (s : Sg)

/-- The word of main rows and carried mask rows from two readers: rm x b is the symbol of main row
number b at the position x, rz x b that of mask row number b. -/
def wordOf (rm rz : ℕ → ℕ → GE) : s.cIn.Word := fun p =>
  match p with
  | .inl x => fun a => rm x.val (Sz.rowNo a.1)
  | .inr x => fun a => rz x.val (Sz.rowNo a.1)

/-- The word of the fresh mask rows from a reader. -/
def freshOf (rf : ℕ → ℕ → GE) : s.cFr.Word := fun x a => rf x.val (Sz.rowNo a.1)

/-- Columns in the format's form that have the readers' values. -/
def colOf (rm rz rf : ℕ → ℕ → GE) (x : ℕ) : Fmt.M1.Col where
  main := Array.ofFn fun b : Fin (2 ^ (s.h + s.g)) => ofE (rm x b.val)
  mask := Array.ofFn fun b : Fin (2 ^ s.h) => ofE (rz x b.val)
  fresh := Array.ofFn fun b : Fin (2 ^ s.h) => ofE (rf x b.val)

/-- An entry of an array that is made of a function's values. -/
theorem vec_ofFn (n : ℕ) (f : ℕ → GE) (b : ℕ) (hb : b < n) :
    vec (Array.ofFn fun i : Fin n => ofE (f i.val)) b = f b := by
  unfold vec Fmt.M1.ent
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact hb),
    Option.getD_some, Array.getElem_ofFn, toE_ofE]

/-- The standard reading of the columns as the word of main rows and carried mask rows. -/
theorem wordIn_colOf (rm rz rf : ℕ → ℕ → GE) : wordIn s (colOf s rm rz rf) = wordOf s rm rz := by
  funext p
  rcases p with x | x
  · funext a
    exact vec_ofFn _ (rm x.val) _ (rowNo_lt a.1)
  · funext a
    exact vec_ofFn _ (rz x.val) _ (rowNo_lt a.1)

/-- The standard reading of the columns as the word of fresh mask rows. -/
theorem wordFr_colOf (rm rz rf : ℕ → ℕ → GE) : wordFr s (colOf s rm rz rf) = freshOf s rf := by
  funext x a
  exact vec_ofFn _ (rf x.val) _ (rowNo_lt a.1)

/-- If the program's two tables and its fresh column are read as the readers' values at each
listed position, the symbols read are the long symbols of the three folded words. Also asked: two
mask rows, no kept member, the stage's numbers of row bits. -/
theorem symS_of_tables (old : SingleRows) (pos : Positions) (opened : Array (Array Column))
    (y : Array E) (rm rz rf : ℕ → ℕ → GE)
    (hsym : singleRowsSymbols old opened pos.all.size = some y) (hm : old.masks = 2)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = false)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (hmain : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ (s.h + s.g) →
      readE (mainAt old.layout opened i b) = rm (pos.all.getD i 0) b)
    (hmask : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readE (maskAt old.layout opened i b) = rz (pos.all.getD i 0) b)
    (hfresh : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readV (colB opened old.layout.members.size i).mask b = rf (pos.all.getD i 0) b)
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (foldWords s (wordOf s rm rz) (freshOf s rf) (readP _ old.gamma)) x α =
      symS s old pos y x.val α := by
  rw [← wordIn_colOf s rm rz rf, ← wordFr_colOf s rm rz rf, foldWords_std]
  exact symS_of_cols s old pos opened y (colOf s rm rz rf) hsym hm hkept hk hh
    (fun i hi b hb => (hmain i hi b hb).trans (vec_ofFn _ (rm _) b hb).symm)
    (fun i hi b hb => (hmask i hi b hb).trans (vec_ofFn _ (rz _) b hb).symm)
    (fun i hi b hb => (hfresh i hi b hb).trans (vec_ofFn _ (rf _) b hb).symm) x hx α

end

end OnBytes.Slice.ProxRun
