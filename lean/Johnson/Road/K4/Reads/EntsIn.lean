-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/EntsIn.lean: WHICH ENTRIES A FORM NAMES, through the operations by which
forms are made. The notion `RowsIn` (OnBytes/Tie/Pv/Led/LedRowsOf.lean) sees an entry's array
and its virtual row; this one sees the INDEX inside the row too. Definitions, statements and proofs;
the proofs are that file's, with one letter more.

`EntsIn Q f`: each entry that the form f names (array t, virtual row r, index i) has Q t r i. The
rules: `entsIn_mono`, `entsIn_ofConst`, `entsIn_slot`, `entsIn_empty`, `entsIn_ent`,
`entsIn_addMul`, `entsIn_scale`, `entsIn_add`, `entsIn_sub`, `entsIn_foldl`.

No form of a sub-proof is treated here.
-/
import OnBytes.Tie.Pv.Led.LedAdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Reads
open OnBytes.Model
open OnBytes.Road.Rows

/-- Each entry that the form names has Q: its array, its virtual row, its index in the row. -/
def EntsIn (Q : Nat → Nat → Nat → Prop) (f : Aff) : Prop :=
  ∀ y ∈ f.ents.toList, Q y.tree y.row y.idx

variable {Q : Nat → Nat → Nat → Prop}

theorem entsIn_mono {Q' : Nat → Nat → Nat → Prop} (h : ∀ t r i, Q t r i → Q' t r i) {f : Aff}
    (a : EntsIn Q f) : EntsIn Q' f := fun y hy => h _ _ _ (a y hy)

theorem entsIn_ofConst (v : E) : EntsIn Q (Aff.ofConst v) := fun y hy => by
  simp [Aff.ofConst] at hy

theorem entsIn_slot (j : Nat) : EntsIn Q (Aff.slot j) := fun y hy => by
  simp [Aff.slot] at hy

theorem entsIn_empty : EntsIn Q ({} : Aff) := fun y hy => by
  simp at hy

theorem entsIn_ent {t r i : Nat} (h : Q t r i) : EntsIn Q (Aff.ent t r i) := fun y hy => by
  have e : y = { tree := t, row := r, idx := i, coef := oneE } := by simpa [Aff.ent] using hy
  rw [e]
  exact h

theorem entsIn_addMul {a b : Aff} (k : E) (ha : EntsIn Q a) (hb : EntsIn Q b) :
    EntsIn Q (Aff.addMul a b k) := fun y hy => by
  simp only [Aff.addMul, foldl_push_toList, List.mem_append, List.mem_map] at hy
  rcases hy with hy | ⟨x, hx, rfl⟩
  · exact ha y hy
  · exact hb x hx

theorem entsIn_scale {a : Aff} (k : E) (ha : EntsIn Q a) : EntsIn Q (Aff.scale a k) :=
  entsIn_addMul k entsIn_empty ha

theorem entsIn_add {a b : Aff} (ha : EntsIn Q a) (hb : EntsIn Q b) : EntsIn Q (a + b) :=
  entsIn_addMul oneE ha hb

theorem entsIn_sub {a b : Aff} (ha : EntsIn Q a) (hb : EntsIn Q b) : EntsIn Q (a - b) :=
  entsIn_addMul (subE zeroE oneE) ha hb

/-- A sum over a list. -/
theorem entsIn_foldl {α : Type} (step : Aff → α → Aff)
    (hs : ∀ f x, EntsIn Q f → EntsIn Q (step f x)) :
    ∀ (l : List α) (f : Aff), EntsIn Q f → EntsIn Q (l.foldl step f)
  | [], _, h => h
  | x :: l, f, h => entsIn_foldl step hs l (step f x) (hs f x h)

end OnBytes.Desc.First.K4.Reads
