-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2CloseEq.lean: the second toy (a test protocol, a chain of three links): for a list of rows
that is not empty, batching the rows member by member and laying the sum into the group's table once
gives the same row as laying every row and batching on the group's table:
toK ms l lz (sumM f x rows) = sumK f x (rows.map (toK ms l lz)).

Theorems. Core Lean. The file uses two notions of Fmt/M1CsEq.lean: the entry of a list at an index,
which counts as 0 beyond the list's end (`at0`); a step u + w r (`stepL`).
A row is a linear claim: vectors of coefficients, called forms, on tables, with a target value. A
group consists of the oracle messages that are tested together, its members. To lay a row (`toK`) is
to put the forms on the members' own tables side by side into the group's tables (`layAll`); the
kept member's form becomes `kp`. `MRow`, `KRow`, `toK`, `layAll`, `sumM`, `sumK` are defined in
Fmt/M2Types.lean.

Main names:
  `layAll_axpyL`: laying is linear.
  `Spec.toK_sumM`, `toK_sumM`: the equation above, under its condition.

Notation:
  `f`: the field (`Fld`, Fmt/Rules1.lean);
  `x`: the element whose powers 1, x, x^2, .. are the coefficients;
  `ms`: the group's members;
  `l`: the number of entries of a main row;
  `lz`: the number of entries of a mask row;
  of `layAll`,
    the numbers `w`: the bits of the table's rows; `n`: its entries;
    the list `L`: for each member where its block begins and the bits of its rows.

Limits: this file says nothing on what the rows are. It says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Close
import Fmt.M1CsEq

set_option autoImplicit false

namespace Fmt.M2.CloseEq
open Fmt.M1 Fmt.M1.CsEq

/-! ## Arrays by their entries -/

theorem ent_at0 (v : Array E) (i : Nat) : ent v i = at0 v.toList i := by
  unfold ent at0
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

theorem ext_ent (a b : Array E) (hs : a.size = b.size) (h : ∀ i, i < a.size → ent a i = ent b i) :
    a = b := by
  apply Array.toList_inj.1
  apply ext_at0
  · rw [Array.length_toList, Array.length_toList]
    exact hs
  · intro i hi
    rw [← ent_at0, ← ent_at0]
    exact h i (by rw [Array.length_toList] at hi; exact hi)

theorem size_axpy (f : Fld) (u : Array E) (s : E) (v : Array E) :
    (axpy f u s v).size = max u.size v.size := by
  rw [axpy_stepL, List.size_toArray, length_stepL, Array.length_toList, Array.length_toList]

/-- An entry of u + s v, at every index. -/
theorem ent_axpy (f : Fld) (u : Array E) (s : E) (v : Array E) (i : Nat) :
    ent (axpy f u s v) i = f.addE (ent u i) (f.mulEF s (ent v i)) := by
  rw [ent_at0, ent_at0, ent_at0, axpy_stepL]
  show at0 (stepL f u.toList s v.toList) i = _
  by_cases h : i < max u.toList.length v.toList.length
  · exact at0_stepL f _ s _ i h
  · rw [at0_ge _ i (by rw [length_stepL]; omega), at0_ge u.toList i (by omega),
      at0_ge v.toList i (by omega), mulEF_zero, addE_zero_zero]

theorem ent_empty (i : Nat) : ent #[] i = Fld.zeroE := rfl

theorem axpy_empty_empty (f : Fld) (s : E) : axpy f #[] s #[] = #[] := rfl

/-! ## A sum of two rows, member by member -/

theorem getD_map {α β : Type} (g : α → β) (d : α) (d' : β) (hd : g d = d') :
    ∀ (l : List α) (j : Nat), (l.map g).getD j d' = g (l.getD j d)
  | [], j => by simp [hd]
  | a :: l, 0 => rfl
  | a :: l, j + 1 => by
      show (l.map g).getD j d' = g (l.getD j d)
      exact getD_map g d d' hd l j

/-- Member number j of the sum, for every j; a member that a list lacks counts as the empty form. -/
theorem axpyL_getD (f : Fld) (s : E) :
    ∀ (u v : List (Array E)) (j : Nat),
      (axpyL f u s v).getD j #[] = axpy f (u.getD j #[]) s (v.getD j #[])
  | [], v, j => by
      show (v.map (axpy f #[] s)).getD j #[] = _
      rw [getD_map (axpy f #[] s) #[] #[] (axpy_empty_empty f s)]
      simp
  | a :: u, [], j => by
      show ((a :: u).map fun a => axpy f a s #[]).getD j #[] = _
      rw [getD_map (fun a => axpy f a s #[]) #[] #[] (axpy_empty_empty f s)]
      simp
  | a :: u, b :: v, 0 => rfl
  | a :: u, b :: v, j + 1 => by
      show (axpyL f u s v).getD j #[] = axpy f (u.getD j #[]) s (v.getD j #[])
      exact axpyL_getD f s u v j

/-! ## Laying is linear -/

theorem size_layAll (w n : Nat) (L : List (Option Nat × Nat)) (parts : List (Array E)) :
    (layAll w n L parts).size = n := by
  unfold layAll
  simp

theorem ent_layAll (w n : Nat) (L : List (Option Nat × Nat))
    (parts : List (Array E)) (i : Nat) (h : i < n) :
    ent (layAll w n L parts) i = match pickRow L (i % 2 ^ w) 0 with
      | some (j, st, b) => ent (parts.getD j #[]) ((i % 2 ^ w - st) + 2 ^ b * (i / 2 ^ w))
      | none => Fld.zeroE := by
  conv => lhs; unfold ent layAll
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos h]
  rfl

/-- Laying is linear. -/
theorem layAll_axpyL (f : Fld) (w n : Nat) (L : List (Option Nat × Nat)) (u : List (Array E))
    (s : E) (v : List (Array E)) :
    layAll w n L (axpyL f u s v) = axpy f (layAll w n L u) s (layAll w n L v) := by
  apply ext_ent
  · rw [size_layAll, size_axpy, size_layAll, size_layAll]
    omega
  · intro i hi
    rw [size_layAll] at hi
    rw [ent_axpy, ent_layAll _ _ _ _ i hi, ent_layAll _ _ _ _ i hi, ent_layAll _ _ _ _ i hi]
    cases pickRow L (i % 2 ^ w) 0 with
    | none =>
        show Fld.zeroE = f.addE Fld.zeroE (f.mulEF s Fld.zeroE)
        rw [mulEF_zero, addE_zero_zero]
    | some x =>
        obtain ⟨j, st, b⟩ := x
        show ent ((axpyL f u s v).getD j #[]) _ =
          f.addE (ent (u.getD j #[]) _) (f.mulEF s (ent (v.getD j #[]) _))
        rw [axpyL_getD, ent_axpy]

/-- What is laid of no member is zeros: under a step with a form c of n entries (`hc`) it does what
the empty form does. -/
theorem axpy_layNil (f : Fld) (w n : Nat) (L : List (Option Nat × Nat)) (s : E)
    (c : Array E) (hc : c.size = n) :
    axpy f (layAll w n L []) s c = axpy f #[] s c := by
  apply ext_ent
  · rw [size_axpy, size_axpy, size_layAll, hc]
    simp
  · intro i hi
    rw [size_axpy, size_layAll, hc] at hi
    rw [ent_axpy, ent_axpy, ent_layAll _ _ _ _ i (by omega)]
    cases pickRow L (i % 2 ^ w) 0 with
    | none => rfl
    | some x => rfl

/-! ## The two folds -/

/-- `stK`: a step of `sumK`. `stM`, below it: a step of `sumMFrom`. -/
def stK (f : Fld) (x : E) (s : KRow × E) (R : KRow) : KRow × E :=
  (⟨axpy f s.1.c s.2 R.c, axpy f s.1.kp s.2 R.kp,
      axpy f s.1.d s.2 R.d, f.addE s.1.t (f.mulE s.2 R.t)⟩,
    f.mulE s.2 x)
def stM (f : Fld) (x : E) (s : MRow × E) (R : MRow) : MRow × E :=
  (⟨axpyL f s.1.main s.2 R.main, axpyL f s.1.mask s.2 R.mask, f.addE s.1.t (f.mulE s.2 R.t)⟩,
    f.mulE s.2 x)

theorem sumK_fold (f : Fld) (x : E) (rows : List KRow) :
    sumK f x rows = (rows.foldl (stK f x) (⟨#[], #[], #[], Fld.zeroE⟩, Fld.oneE)).1 := rfl
theorem sumMFrom_fold (f : Fld) (x first : E) (rows : List MRow) :
    sumMFrom f x first rows = rows.foldl (stM f x) (⟨[], [], Fld.zeroE⟩, first) := rfl

theorem toK_step (f : Fld) (x : E) (ms : List Mem) (l lz : Nat) (s : MRow × E) (R : MRow) :
    stK f x (toK ms l lz s.1, s.2) (toK ms l lz R) =
      (toK ms l lz (stM f x s R).1, (stM f x s R).2) := by
  unfold stK stM toK
  simp only [layAll_axpyL]
  cases keptIdx ms with
  | none => rfl
  | some j => simp only [axpyL_getD]

theorem first_step (f : Fld) (x w : E) (ms : List Mem) (l lz : Nat) (R : MRow) :
    stK f x (⟨#[], #[], #[], Fld.zeroE⟩, w) (toK ms l lz R) =
      stK f x (toK ms l lz ⟨[], [], Fld.zeroE⟩, w) (toK ms l lz R) := by
  unfold stK toK
  simp only [axpy_layNil _ _ _ _ _ _ (size_layAll _ _ _ _)]
  cases keptIdx ms with
  | none => rfl
  | some j => simp

theorem fold_toK (f : Fld) (x : E) (ms : List Mem) (l lz : Nat) :
    ∀ (rows : List MRow) (s : MRow × E),
      (rows.map (toK ms l lz)).foldl (stK f x) (toK ms l lz s.1, s.2) =
        (toK ms l lz (rows.foldl (stM f x) s).1, (rows.foldl (stM f x) s).2)
  | [], _ => rfl
  | R :: rows, s => by
      show (rows.map (toK ms l lz)).foldl
          (stK f x) (stK f x (toK ms l lz s.1, s.2) (toK ms l lz R)) = _
      rw [toK_step]
      exact fold_toK f x ms l lz rows (stM f x s R)

/-- The statement of `fold_toK` with both folds begun at the empty sums, for a list that is not
empty. -/
theorem fold_start (f : Fld) (x w : E) (ms : List Mem) (l lz : Nat) (R : MRow) (rows : List MRow) :
    ((R :: rows).map (toK ms l lz)).foldl (stK f x) (⟨#[], #[], #[], Fld.zeroE⟩, w) =
      (toK ms l lz ((R :: rows).foldl (stM f x) (⟨[], [], Fld.zeroE⟩, w)).1,
        ((R :: rows).foldl (stM f x) (⟨[], [], Fld.zeroE⟩, w)).2) := by
  show (rows.map (toK ms l lz)).foldl
      (stK f x) (stK f x (⟨#[], #[], #[], Fld.zeroE⟩, w) (toK ms l lz R)) = _
  rw [first_step]
  have h := toK_step f x ms l lz (⟨[], [], Fld.zeroE⟩, w) R
  rw [show stK f x (toK ms l lz ⟨[], [], Fld.zeroE⟩, w) (toK ms l lz R) = _ from h]
  exact fold_toK f x ms l lz rows _

def Spec.toK_sumM : Prop :=
  ∀ (f : Fld) (x : E) (ms : List Mem) (l lz : Nat) (rows : List MRow),
    rows ≠ [] → toK ms l lz (sumM f x rows) = sumK f x (rows.map (toK ms l lz))

/-- Proves `Spec.toK_sumM`: for a list of rows that is not empty, batching member by member and
laying once gives the same row as laying every row and batching. -/
theorem toK_sumM : Spec.toK_sumM := by
  intro f x ms l lz rows h
  cases rows with
  | nil => exact absurd rfl h
  | cons R rows =>
      rw [sumK_fold, fold_start]
      rfl

end Fmt.M2.CloseEq
