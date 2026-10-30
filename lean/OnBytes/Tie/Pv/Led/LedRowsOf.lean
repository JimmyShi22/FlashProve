-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedRowsOf.lean: which virtual rows a form of the shipped Lean verifier names,
through the operations by which forms are made.

Some virtual rows' weights hold the batching element. To say that a claim does not read such a row,
one must know which rows its form names. This file has the notion and its rules.

Main names.
  RowsIn Q f: each entry of a virtual row that the form f names lies in a row (array t, virtual row
    r) with Q t r.
  The rules: rowsIn_ofConst, rowsIn_slot, rowsIn_empty, rowsIn_ent, rowsIn_addMul, rowsIn_scale,
    rowsIn_add, rowsIn_sub, rowsIn_foldl (a sum over a list), rowsIn_claimForm (a form and runs,
    LedAdds.lean), rowsIn_mono.
  rowsIn_weights: if the rows with Q have the same weights in two states, a form with RowsIn Q meets
    the premise on the weights of fresh_ofAff (LedFresh.lean [not in this library]) and cutRows_same
    (LedSameRows.lean [not in this library]).

What this file does not claim. No form of a sub-proof is treated here.


-/
import OnBytes.Tie.Pv.Led.LedAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open OnBytes.Model

/-- Each entry that the form names lies in a virtual row with Q. -/
def RowsIn (Q : Nat → Nat → Prop) (f : Aff) : Prop := ∀ y ∈ f.ents.toList, Q y.tree y.row

variable {Q : Nat → Nat → Prop}

theorem rowsIn_mono {Q' : Nat → Nat → Prop} (h : ∀ t r, Q t r → Q' t r) {f : Aff}
    (a : RowsIn Q f) : RowsIn Q' f := fun y hy => h _ _ (a y hy)

theorem rowsIn_ofConst (v : E) : RowsIn Q (Aff.ofConst v) := fun y hy => by
  simp [Aff.ofConst] at hy

theorem rowsIn_slot (j : Nat) : RowsIn Q (Aff.slot j) := fun y hy => by
  simp [Aff.slot] at hy

theorem rowsIn_empty : RowsIn Q ({} : Aff) := fun y hy => by
  simp at hy

theorem rowsIn_ent {t r : Nat} (i : Nat) (h : Q t r) : RowsIn Q (Aff.ent t r i) := fun y hy => by
  have e : y = { tree := t, row := r, idx := i, coef := oneE } := by simpa [Aff.ent] using hy
  rw [e]
  exact h

theorem rowsIn_addMul {a b : Aff} (k : E) (ha : RowsIn Q a) (hb : RowsIn Q b) :
    RowsIn Q (Aff.addMul a b k) := fun y hy => by
  simp only [Aff.addMul, foldl_push_toList, List.mem_append, List.mem_map] at hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · exact ha y hy
  · exact hb x hx

theorem rowsIn_scale {a : Aff} (k : E) (ha : RowsIn Q a) : RowsIn Q (Aff.scale a k) :=
  rowsIn_addMul k rowsIn_empty ha

theorem rowsIn_add {a b : Aff} (ha : RowsIn Q a) (hb : RowsIn Q b) : RowsIn Q (a + b) :=
  rowsIn_addMul oneE ha hb

theorem rowsIn_sub {a b : Aff} (ha : RowsIn Q a) (hb : RowsIn Q b) : RowsIn Q (a - b) :=
  rowsIn_addMul (subE zeroE oneE) ha hb

/-- A sum over a list. -/
theorem rowsIn_foldl {α : Type} (step : Aff → α → Aff)
    (hs : ∀ f x, RowsIn Q f → RowsIn Q (step f x)) :
    ∀ (l : List α) (f : Aff), RowsIn Q f → RowsIn Q (l.foldl step f)
  | [], _, h => h
  | x :: l, f, h => rowsIn_foldl step hs l (step f x) (hs f x h)

theorem runEnts_rows (r : Run2) : ∀ (count i : Nat), ∀ y ∈ runEnts r count i,
    y.tree = r.tree ∧ y.row = r.row
  | 0, _, y, hy => absurd hy List.not_mem_nil
  | count + 1, i, y, hy => by
    unfold runEnts at hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨rfl, rfl⟩
    · exact runEnts_rows r count (i + 1) y hy

/-- A form and runs. -/
theorem rowsIn_claimForm {a : Aff} {rs : Array Run2} (ha : RowsIn Q a)
    (hr : ∀ r ∈ rs.toList, Q r.tree r.row) : RowsIn Q (claimForm a rs) := fun y hy => by
  simp only [claimForm, Array.toList_append, List.mem_append, List.mem_flatMap] at hy
  rcases hy with hy | ⟨r, hr', hy⟩
  · exact ha y hy
  · obtain ⟨e1, e2⟩ := runEnts_rows r _ _ y hy
    rw [e1, e2]
    exact hr r hr'

/-- The premise on the weights, from the rows with Q. -/
theorem rowsIn_weights {K : Type} [Field K] (ρ : Reading K) {G G' : Fork}
    (hw : ∀ t r, Q t r → rowWeight ρ G'.trees t r = rowWeight ρ G.trees t r) {f : Aff}
    (a : RowsIn Q f) : ∀ y ∈ f.ents.toList,
      rowWeight ρ G'.trees y.tree y.row = rowWeight ρ G.trees y.tree y.row :=
  fun y hy => hw _ _ (a y hy)

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.rowsIn_addMul
#print axioms OnBytes.Road.Rows.rowsIn_claimForm
