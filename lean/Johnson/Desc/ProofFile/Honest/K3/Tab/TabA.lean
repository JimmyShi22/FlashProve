-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabA.lean: tables of the factors of the two long sums in the
key formulas of an attention sub-proof's lookup, the rows off these tables, and that these rows'
values are the library's own factors. Definitions with code, and theorems: the two on the tables
without a hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: a table is an array made by `Memo.tab`
(Honest/K3/Memo.lean); a row is a value of `TabG.Row` (Honest/K3/Tab/SisterG.lean); the rows that
the sums read are a value of `InnerA` (Honest/K3/Tab/SisterA.lean).

What is defined. Generic in the ring, at a shape S and a reading cell of the names:
  `qTab`, `kTab`: layer, token, feature: `A.ten` at `S.atQ`, at S.dq features; at `S.atK`, at
    S.G * S.dh features.
  `vTab`: layer, feature, token: `A.ten` at `S.atV`.
  `wTab isD`: layer, head of a group, place: `A.wt`, at 2 ^ S.nD or 2 ^ S.nM places.
  `innerTabA S cell tq tk tv wm wd`: the rows off five arrays. Beyond an array's end the library's
    formula is read: so no statement needs a bound on a number.

What is shown.
  `read3`: reading in an array of arrays of arrays that was made of tables gives the function's
    value, at all three numbers, inside the arrays or beyond. Conditional on `h`: each innermost
    array, read with the function behind it, gives the function's value.
  `innerTabA_is`: **at the five tables the rows' values are the library's own factors**:
    `InnerA.Is S cell (innerTabA S cell (qTab S cell) (kTab S cell) (vTab S cell) (wTab S cell
    false) (wTab S cell true))`.
  `kvABy_tab`: so `kvABy` at these rows is `A.kvA`.

How it is meant. The five tables are arguments of `innerTabA`: whoever wants them made once binds
them by a let in front of the function that reads a key.

Imported. Honest/K3/Tab/SisterA.lean and what it imports. No file of the frame.

Users. Honest/K3/Tab/TabALaw.lean.

Limits. How many entries the tables have, and how long anything takes, is not said here. The sizes
are this file's reading of which numbers the formulas ask for: a size that is too small costs time,
not truth.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Tab.SisterA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabA
open OnBytes.Model OnBytes.Ends OnBytes.Ends.A
open ProofFile.Honest.K3.TabG (Row)
open ProofFile.Honest.K3.Memo (read tab read_tab read_empty getD_tab)

/-- Reading in an array of arrays of arrays that was made of tables. -/
theorem read3 {α : Type} (n m : ℕ) (B : ℕ → ℕ → Array α) (F : ℕ → ℕ → ℕ → α)
    (h : ∀ a b c, read (B a b) (F a b) c = F a b c) (a b c : ℕ) :
    read (((tab n fun a => tab m (B a)).getD a #[]).getD b #[]) (F a b) c = F a b c := by
  rw [getD_tab]
  split
  · rw [getD_tab]
    split
    · exact h a b c
    · exact read_empty _ _
  · have e : (#[] : Array (Array α)).getD b #[] = #[] := by simp
    rw [e]
    exact read_empty _ _

section Tables
variable {R : Type} [CommRing R] (S : Sh) (cell : NameA → R)

/-- q's entries: layer, token, feature. -/
def qTab : Array (Array (Array R)) :=
  tab S.Lam fun lam => tab S.T fun i => tab S.dq fun f => ten S cell S.atQ lam f i

/-- k's entries: layer, token, feature. -/
def kTab : Array (Array (Array R)) :=
  tab S.Lam fun lam => tab S.T fun i => tab (S.G * S.dh) fun f => ten S cell S.atK lam f i

/-- v's entries: layer, feature, token. -/
def vTab : Array (Array (Array R)) :=
  tab S.Lam fun lam => tab (S.G * S.dh) fun f => tab S.T fun i => ten S cell S.atV lam f i

/-- The softmax weights: layer, head of a group, place. isD: the places of the diagonal tiles. -/
def wTab (isD : Bool) : Array (Array (Array R)) :=
  tab S.Lam fun lam => tab S.HA fun a =>
    tab (2 ^ (if isD then S.nD else S.nM)) fun π => wt S cell lam a isD π

/-- **The rows off five arrays.** Beyond an array's end the library's formula is read. -/
def innerTabA (tq tk tv wm wd : Array (Array (Array R))) : InnerA R :=
  { q := fun lam i => ⟨(tq.getD lam #[]).getD i #[], fun f => ten S cell S.atQ lam f i⟩
    k := fun lam i => ⟨(tk.getD lam #[]).getD i #[], fun f => ten S cell S.atK lam f i⟩
    v := fun lam f => ⟨(tv.getD lam #[]).getD f #[], fun i => ten S cell S.atV lam f i⟩
    w := fun isD lam a =>
      ⟨((if isD then wd else wm).getD lam #[]).getD a #[], fun π => wt S cell lam a isD π⟩ }

/-- **At the five tables the rows' values are the library's own factors.** -/
theorem innerTabA_is :
    (innerTabA S cell (qTab S cell) (kTab S cell) (vTab S cell) (wTab S cell false)
      (wTab S cell true)).Is S cell where
  q := fun lam i f =>
    read3 S.Lam S.T (fun lam i => tab S.dq fun f => ten S cell S.atQ lam f i)
      (fun lam i f => ten S cell S.atQ lam f i) (fun _ _ _ => read_tab _ _ _) lam i f
  k := fun lam i f =>
    read3 S.Lam S.T (fun lam i => tab (S.G * S.dh) fun f => ten S cell S.atK lam f i)
      (fun lam i f => ten S cell S.atK lam f i) (fun _ _ _ => read_tab _ _ _) lam i f
  v := fun lam f i =>
    read3 S.Lam (S.G * S.dh) (fun lam f => tab S.T fun i => ten S cell S.atV lam f i)
      (fun lam f i => ten S cell S.atV lam f i) (fun _ _ _ => read_tab _ _ _) lam f i
  w := fun isD lam a π => by
    cases isD
    · exact read3 S.Lam S.HA
        (fun lam a => tab (2 ^ (if false = true then S.nD else S.nM)) fun π =>
          wt S cell lam a false π)
        (fun lam a π => wt S cell lam a false π) (fun _ _ _ => read_tab _ _ _) lam a π
    · exact read3 S.Lam S.HA
        (fun lam a => tab (2 ^ (if true = true then S.nD else S.nM)) fun π =>
          wt S cell lam a true π)
        (fun lam a π => wt S cell lam a true π) (fun _ _ _ => read_tab _ _ _) lam a π

/-- **`kvABy` at the rows off the five tables is `A.kvA`.** -/
theorem kvABy_tab (h : Forest.Shape) (q X : ℕ) :
    kvABy S cell
      (innerTabA S cell (qTab S cell) (kTab S cell) (vTab S cell) (wTab S cell false)
        (wTab S cell true)) h q X = kvA S h cell q X :=
  kvABy_of (innerTabA_is S cell) h q X

end Tables

end ProofFile.Honest.K3.TabA

#print axioms ProofFile.Honest.K3.TabA.read3
#print axioms ProofFile.Honest.K3.TabA.innerTabA_is
#print axioms ProofFile.Honest.K3.TabA.kvABy_tab
