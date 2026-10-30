-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/TermsEnts.lean: THE READERS OF THE TABLES NAME ENTRIES INSIDE THE
FAMILIES OF TABLES. A layers' sub-proof names an entry of the array of reads through one function
alone, `Env.U3at` (OnBytes/Model/LayerForms.lean:220), which hands out entry i of the family that
begins at t only if such a family stands in the list `v.tab` and i is below its length. So every
form that is made of such entries by sums and factors names entries INSIDE A FAMILY OF v.tab alone.
Statements and proofs.

MADE BY PROGRAM out of Johnson/Road/Rows/LayerTermsRows.lean, which shows the same walk
for a weaker notion (the array alone): `RowsIn` became `EntsIn`, `InU3` became `InTab`; ONE PROOF IS
NEW: `inTab_U3at`.

Main names: `inTab v t r i`: t is the array of reads, and r * K3 + i lies in a family of v.tab.
`InTab v f`. `inTab_U3at`; `inTab_sumForms`, `inTab_limbs`, `inTab_shortA`, `inTab_shA`,
`inTab_rowCells`, `inTab_rowR`; `termsL_rows`: every form of the list termsL.

Limits: no hypothesis but that the list is returned. NOT SAID: that the families of v.tab fill, or
lie in, the part of the array that the reads' test covers: other files' to show. An index that
strays to another tensor, layer or limb of the same family is not caught.
-/
import Johnson.Road.Rows.LayerEnds3S
import Johnson.Road.K4.Reads.EntsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Reads

open OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road OnBytes.Road.Rows

/-- An entry of the array of reads that lies in one of the families of tables: r * K3 + i is its
place in the array. -/
def inTab (v : Env) (t r i : ℕ) : Prop :=
  t = v.iU3 ∧ ∃ x ∈ v.tab, x.first ≤ r * v.K3 + i ∧ r * v.K3 + i < x.first + x.len

/-- Each entry that the form names lies in the array of reads, in one of the families of tables. -/
abbrev InTab (v : Env) (f : Aff) : Prop := EntsIn (inTab v) f

variable {v : Env}

theorem inTab_aff0 : InTab v aff0 := entsIn_ofConst _

theorem inTab_U3at {t i : ℕ} {f : Aff} (h : v.U3at t i = some f) : InTab v f := by
  unfold Env.U3at at h
  split at h
  · cases h
  · rename_i x hx
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      have hm : x ∈ v.tab := List.mem_of_find?_eq_some hx
      have hf : x.first = t := by
        have h1 := List.find?_some hx
        simpa using h1
      have hi : i < x.len := by
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact hc.1.1
      have e : (t + i) / v.K3 * v.K3 + (t + i) % v.K3 = t + i := Nat.div_add_mod' _ _
      exact entsIn_ent ⟨rfl, x, hm, by rw [e]; omega, by rw [e]; omega⟩
    · cases h

/-- A sum made by a fold that may refuse. -/
theorem inTab_foldlM {g : ℕ → Option (Aff × E)} (hg : ∀ x p, g x = some p → InTab v p.1) :
    ∀ (l : List ℕ) (a s : Aff), InTab v a →
      l.foldlM (fun a x => (g x).map fun t => a.addMul t.1 t.2) a = some s → InTab v s
  | [], a, s, ha, h => by
    cases h
    exact ha
  | x :: l, a, s, ha, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨p, hp, e⟩ := map_some hb
    subst e
    exact inTab_foldlM hg l _ s (entsIn_addMul _ ha (hg x p hp)) h

theorem inTab_sumForms {n : ℕ} {g : ℕ → Option (Aff × E)} {s : Aff}
    (hg : ∀ x p, g x = some p → InTab v p.1) (h : sumForms n g = some s) : InTab v s :=
  inTab_foldlM hg _ _ s inTab_aff0 h

theorem inTab_limbs {t nl : ℕ} {cell : ℕ → ℕ} {s : Aff} (h : v.limbs t nl cell = some s) :
    InTab v s :=
  inTab_sumForms (fun _ p hp => by
    obtain ⟨a, ha, e⟩ := map_some hp
    subst e
    exact inTab_U3at ha) h

theorem inTab_shortA {t : ℕ} {X : Ten} {i j : ℕ} {s : Aff} (h : v.shortA t X i j = some s) :
    InTab v s := inTab_limbs h

theorem inTab_shA {X P : String} {i j : ℕ} {s : Aff} (h : v.shA X P i j = some s) : InTab v s := by
  obtain ⟨x, -, h⟩ := bind_some h
  exact inTab_shortA h

/-- What holds of every value that a function returns holds of all members of the list. -/
theorem all_mapM {α β : Type} {g : α → Option β} {Pr : β → Prop}
    (hg : ∀ a b, g a = some b → Pr b) :
    ∀ (xs : List α) (ys : List β), xs.mapM g = some ys → ∀ y ∈ ys, Pr y
  | [], ys, h, y, hy => by
    cases h
    cases hy
  | a :: xs, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_some h
    obtain ⟨bs, hbs, h⟩ := bind_some h
    cases h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hg a _ hb
    · exact all_mapM hg xs bs hbs y hy

theorem inTab_rowCells {P : String} {i n : ℕ} {cells : Array Aff}
    (h : v.rowCells P i n = some cells) (j : ℕ) : InTab v (cells.getD j aff0) := by
  unfold Env.rowCells at h
  obtain ⟨t, -, h⟩ := bind_some h
  obtain ⟨tr, -, h⟩ := bind_some h
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hys, e⟩ := map_some h
  subst e
  by_cases hj : j < ys.length
  · have e : ys.toArray.getD j aff0 = ys[j] := by simp [Array.getD, hj]
    rw [e]
    exact all_mapM (Pr := InTab v) (fun _ _ hb => inTab_U3at hb) _ ys hys _ (List.getElem_mem hj)
  · have e : ys.toArray.getD j aff0 = aff0 := by simp [Array.getD, hj]
    rw [e]
    exact inTab_aff0

/-- The number that digits spell, in the row of five limbs. -/
theorem inTab_ledDig {Dg : Array Aff} (hD : ∀ j, InTab v (Dg.getD j (LedK.c zeroE)))
    (first n : ℕ) : InTab v (ledDig Dg first n) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_add hf (entsIn_scale _ (hD _))) _ _ (entsIn_ofConst _)

/-- The same in the row of four limbs. -/
theorem inTab_digits {Dg : Array Aff} (hD : ∀ j, InTab v (Dg.getD j aff0)) (a n : ℕ) :
    InTab v (Env.digits Dg a n) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (hD _)) _ _ inTab_aff0

theorem inTab_rowR {P : String} {i : ℕ} {f : Aff} (h : v.rowR P i = some f) : InTab v f := by
  unfold Env.rowR at h
  split at h
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.row5At at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    obtain rfl : row5 (fun j => cells.getD j aff0) = r := Option.some.inj hr
    have hD : ∀ j, InTab v ((Array.ofFn (n := 99) fun j : Fin 99 =>
        (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE)) := by
      intro j
      by_cases hj : j < 99
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.add (cells.getD j aff0) (LedK.c (ofNat 128)) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (inTab_rowCells hc j) (entsIn_ofConst _)
      · have e : (Array.ofFn (n := 99) fun j : Fin 99 =>
            (LedK.add (cells.getD j.val aff0) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE) =
            LedK.c zeroE := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_ofConst _
    exact entsIn_add (inTab_ledDig hD 80 3) (entsIn_scale _ (inTab_ledDig hD 83 3))
  · obtain ⟨r, hr, e⟩ := map_some h
    subst e
    unfold Env.rowAt at hr
    obtain ⟨cells, hc, hr⟩ := bind_some hr
    have hr' := Option.some.inj hr
    subst hr'
    have hD : ∀ j, InTab v ((cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0) := by
      intro j
      by_cases hj : j < cells.size
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 =
            cells.getD j aff0 + Aff.ofConst (ofNat 128) := by
          simp [Array.getD, hj]
        rw [e]
        exact entsIn_add (inTab_rowCells hc j) (entsIn_ofConst _)
      · have e : (cells.map fun a => a + Aff.ofConst (ofNat 128)).getD j aff0 = aff0 := by
          simp [Array.getD, hj]
        rw [e]
        exact inTab_aff0
    exact entsIn_add (inTab_digits hD 57 3) (entsIn_scale _ (inTab_digits hD 60 3))

/-- What holds of every list that a function returns holds of all lists laid end to end. -/
theorem all_flatten_mapM {α : Type} {g : α → Option (List Aff)} {Pr : Aff → Prop}
    (hg : ∀ a x, g a = some x → ∀ y ∈ x, Pr y) :
    ∀ (xs : List α) (L : List (List Aff)), xs.mapM g = some L → ∀ y ∈ L.flatten, Pr y
  | [], L, h, y, hy => by
    cases h
    cases hy
  | a :: xs, L, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨x, hx, h⟩ := bind_some h
    obtain ⟨L', hL, h⟩ := bind_some h
    cases h
    rw [List.flatten_cons, List.mem_append] at hy
    rcases hy with hy | hy
    · exact hg a x hx y hy
    · exact all_flatten_mapM hg xs L' hL y hy

/-- A slot less a form that names entries of the reads alone. -/
theorem inTab_one {o : Option Aff} {j : ℕ} {x : List Aff}
    (ho : ∀ f, o = some f → InTab v f)
    (h : (o.bind fun f => some [Aff.slot j - f]) = some x) : ∀ y ∈ x, InTab v y := by
  obtain ⟨f, hf, h⟩ := bind_some h
  cases h
  intro y hy
  rw [List.mem_singleton.mp hy]
  exact entsIn_sub (entsIn_slot _) (ho f hf)

/-- Every claim on the end values of the second token sumcheck names entries of the reads alone. -/
theorem termsL_rows {sEnd : ℕ} {l : List Aff} (h : termsL v sEnd = some l) :
    ∀ f ∈ l, InTab v f := by
  unfold termsL at h
  obtain ⟨la, lb, ha, hb, rfl⟩ := appL_some h
  obtain ⟨La, hLa, rfl⟩ := map_some ha
  have A := all_flatten_mapM (Pr := InTab v)
    (fun i x hx => inTab_one (fun f hf => inTab_rowR hf) hx) _ La hLa
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact A f hf
  · split at hb
    · obtain ⟨lc, ld, hc, hd, rfl⟩ := appL_some hb
      obtain ⟨Lc, hLc, rfl⟩ := map_some hc
      obtain ⟨Ld, hLd, rfl⟩ := map_some hd
      rcases List.mem_append.mp hf with hf | hf
      · exact all_flatten_mapM (Pr := InTab v)
          (fun i x hx => inTab_one (fun f hf => inTab_shA hf) hx) _ Lc hLc f hf
      · exact all_flatten_mapM (Pr := InTab v)
          (fun i x hx => inTab_one (fun f hf => inTab_shA hf) hx) _ Ld hLd f hf
    · cases hb
      cases hf

end OnBytes.Desc.First.K4.Reads

