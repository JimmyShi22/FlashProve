-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/SymbolLaws.lean: the symbols that the program makes of opened columns, taken apart.

After a fold the verifier reads the folded rows at listed positions. For each position the program
(OnBytes/Iop/Fold.lean: `singleRowsSymbols`) puts the symbols of the members' opened columns into a
main table and a mask table, each member's from its first row on (`putRows`). It folds the tables
at the fold's point, and it writes the results one after the other. This file says, for a call
that succeeds, what the tables hold and which entry of the result is which folded table.

All statements are equations between the program's own values (arrays of E). No ring or field of
mathematics occurs, and only the program's file is imported.

Main definitions: `putAt` (a table, as a function, with symbols put into it), `colB` (the column at
a place), `memberStep`, `tablesAt`, `symStep` (the bodies of the program's two loops, as definitions
of this file), `mainTable`, `maskTable`, `keptSymbols` (what the tables of a position hold),
`blockOf`.
Main theorems.
 `putRows_inv`: the symbols are at the rows from the first on; the rest and the size are as before.
 `singleRowsSymbols_eq`: the program's function equals the same text written with these definitions
   (by rfl). It is the only statement that unfolds the function; all others go through it.
 `tablesAt_all`: the two tables and the kept symbols of a position; `tablesAt_inv`: the same
   without a kept member.
 `singleRowsSymbols_inv`: the size of the result, and each of its entries.

Not claimed. Nothing on a call that fails. Nothing on where the opened columns come from. Nothing
for s.masks > 2: the function can then succeed with fewer entries for a position than s.rows.
-/
import OnBytes.Iop.Fold

set_option autoImplicit false

namespace OnBytes

/-! ## Symbols put into a table -/

/-- A table, given by its entries, with the symbols col from row f on, if first names a row f. -/
def putAt (first : Option Nat) (col : Array E) (base : Nat → E) (j : Nat) : E :=
  match first with
  | some f => if f ≤ j ∧ j < f + col.size then col.getD (j - f) zeroE else base j
  | none => base j

/-- An entry of an array in which one entry was set, if it is there. -/
private theorem getD_setIfInBounds (xs : Array E) (i : Nat) (v : E) (j : Nat) :
    (xs.setIfInBounds i v).getD j zeroE = if i = j ∧ j < xs.size then v else xs.getD j zeroE := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < xs.size
    · rw [if_pos rfl, if_pos h2, if_pos ⟨rfl, h2⟩]
      rfl
    · rw [if_pos rfl, if_neg h2, if_neg (fun c => h2 c.2), Array.getElem?_eq_none (by omega)]
  · rw [if_neg h1, if_neg fun c => h1 c.1]

/-- The loop of `putRows`, after n symbols. -/
private theorem putLoop (f : Nat) (col : Array E) : ∀ (n : Nat) (table : Array E),
    ((List.range n).foldl (fun t b => t.setIfInBounds (f + b) (col.getD b zeroE)) table).size
        = table.size ∧
      ∀ j, ((List.range n).foldl (fun t b => t.setIfInBounds (f + b) (col.getD b zeroE))
          table).getD j zeroE
        = if f ≤ j ∧ j < f + n ∧ j < table.size then col.getD (j - f) zeroE
          else table.getD j zeroE
  | 0, table => ⟨rfl, fun j => by
      rw [if_neg (by omega)]
      rfl⟩
  | n + 1, table => by
    obtain ⟨hs, hg⟩ := putLoop f col n table
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [Array.size_setIfInBounds, hs], fun j => ?_⟩
    rw [getD_setIfInBounds, hs, hg j]
    by_cases h1 : f + n = j ∧ j < table.size
    · obtain ⟨rfl, h2⟩ := h1
      rw [if_pos ⟨rfl, h2⟩, if_pos ⟨by omega, by omega, h2⟩, Nat.add_sub_cancel_left]
    · rw [if_neg h1]
      by_cases h3 : f ≤ j ∧ j < f + n ∧ j < table.size
      · rw [if_pos h3, if_pos ⟨h3.1, by omega, h3.2.2⟩]
      · rw [if_neg h3, if_neg (by omega)]

/-- Symbols that were put into a table are at the rows from the first on. The other entries,
and the table's size, are as before. -/
theorem putRows_inv (table : Array E) (first : Option Nat) (col t' : Array E)
    (h : putRows table first col = some t') :
    t'.size = table.size ∧
      ∀ j, t'.getD j zeroE = putAt first col (fun j => table.getD j zeroE) j := by
  unfold putRows at h
  by_cases he : col.isEmpty = true
  · rw [if_pos he] at h
    obtain rfl := Option.some.inj h
    have hz : col.size = 0 := by simpa using he
    refine ⟨rfl, fun j => ?_⟩
    cases first with
    | none => rfl
    | some f => exact (if_neg (by omega)).symm
  · rw [if_neg he] at h
    cases first with
    | none => cases h
    | some f =>
      by_cases hfit : f + col.size ≤ table.size
      · have h' : some ((List.range col.size).foldl
            (fun t b => t.setIfInBounds (f + b) (col.getD b zeroE)) table) = some t' := by
          rw [← h]
          exact (if_pos hfit).symm
        obtain rfl := Option.some.inj h'
        obtain ⟨hs, hg⟩ := putLoop f col col.size table
        refine ⟨hs, fun j => ?_⟩
        rw [hg j]
        by_cases hc : f ≤ j ∧ j < f + col.size
        · rw [if_pos ⟨hc.1, hc.2, by omega⟩]
          exact (if_pos hc).symm
        · rw [if_neg (by omega)]
          exact (if_neg hc).symm
      · have h' : (none : Option (Array E)) = some t' := by
          rw [← h]
          exact (if_neg hfit).symm
        cases h'

/-! ## The tables of one listed position -/

/-- The column of the oracle message number w of the list, at the listed position number i. -/
def colB (opened : Array (Array Column)) (w i : Nat) : Column := (opened.getD w #[]).getD i {}

/-- One member's column goes into the tables: its mask symbols into the mask table; its main
symbols into the main table, or after the kept symbols if the member is kept. -/
def memberStep (L : GroupLayout) (opened : Array (Array Column)) (i : Nat)
    (t : Array E × Array E × Array E) (w : Nat) : Option (Array E × Array E × Array E) := do
  let col ← (← opened[w]?)[i]?
  let mask ← putRows t.2.1 (L.maskFirst.getD w none) col.mask
  if L.kept.getD w false then pure (t.1, mask, t.2.2 ++ col.main)
  else pure (← putRows t.1 (L.mainFirst.getD w none) col.main, mask, t.2.2)

/-- The main table, the mask table and the kept symbols of the listed position number i. -/
def tablesAt (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    Option (Array E × Array E × Array E) :=
  (List.range L.members.size).foldlM (memberStep L opened i)
    (Array.replicate (2 ^ L.k) zeroE, Array.replicate (2 ^ L.h) zeroE, #[])

/-- The symbols of the listed position number i are appended to those of the positions before. -/
def symStep (s : SingleRows) (opened : Array (Array Column)) (y : Array E) (i : Nat) :
    Option (Array E) := do
  let t ← tablesAt s.layout opened i
  if t.2.2.size != s.keptRows then none
  let y1 := (y.push ((foldLow t.1 s.gamma).getD 0 zeroE)) ++ t.2.2
  let low := s.gamma.take s.layout.h
  let y2 := if 1 ≤ s.masks then y1.push ((foldLow t.2.1 low).getD 0 zeroE) else y1
  if s.masks == 2 then
    let fresh ← (← opened[s.layout.members.size]?)[i]?
    if fresh.mask.size != 2 ^ s.layout.h then none
    pure (y2.push ((foldLow fresh.mask low).getD 0 zeroE))
  else pure y2

/-- The program's function equals the same text written with memberStep, tablesAt and symStep. -/
theorem singleRowsSymbols_eq (s : SingleRows) (opened : Array (Array Column)) (n : Nat) :
    singleRowsSymbols s opened n = (do
      if s.gamma.length != s.layout.k || s.layout.k < s.layout.h then none
      if s.layout.kept.size != s.layout.members.size ||
          s.layout.mainFirst.size != s.layout.members.size ||
          s.layout.maskFirst.size != s.layout.members.size then none
      (List.range n).foldlM (symStep s opened) #[]) :=
  rfl

/-- A column that was found in the list is the column of that place. -/
theorem colB_of (opened : Array (Array Column)) (w i : Nat) (a : Array Column) (col : Column)
    (ha : opened[w]? = some a) (hc : a[i]? = some col) : colB opened w i = col := by
  have e : opened.getD w #[] = a := by
    rw [Array.getD_eq_getD_getElem?, ha, Option.getD_some]
  unfold colB
  rw [e, Array.getD_eq_getD_getElem?, hc, Option.getD_some]

/-- The group's main table at the listed position number i, as a function: each member's main
symbols from its first row on, a later member's over an earlier one's; a kept member's are not in
it; all other entries are 0. -/
def mainTable (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) : Nat → E :=
  (List.range L.members.size).foldl
    (fun base w =>
      if L.kept.getD w false then base
      else putAt (L.mainFirst.getD w none) (colB opened w i).main base)
    (fun _ => zeroE)

/-- The group's mask table at the listed position number i, likewise, of all members. -/
def maskTable (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) : Nat → E :=
  (List.range L.members.size).foldl
    (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base) (fun _ => zeroE)

/-- The main symbols of the kept members at the listed position number i, by member and row. -/
def keptSymbols (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) : List E :=
  (List.range L.members.size).flatMap fun w =>
    if L.kept.getD w false then (colB opened w i).main.toList else []

/-- One member: its mask symbols are put into the mask table; its main symbols are put into the main
table, or are appended to the kept symbols if it is kept. -/
theorem memberStep_inv (L : GroupLayout) (opened : Array (Array Column)) (i : Nat)
    (t t' : Array E × Array E × Array E) (w : Nat) (h : memberStep L opened i t w = some t') :
    putRows t.2.1 (L.maskFirst.getD w none) (colB opened w i).mask = some t'.2.1 ∧
      if L.kept.getD w false = true then
        t'.1 = t.1 ∧ t'.2.2 = t.2.2 ++ (colB opened w i).main
      else
        putRows t.1 (L.mainFirst.getD w none) (colB opened w i).main = some t'.1 ∧
          t'.2.2 = t.2.2 := by
  unfold memberStep at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
  obtain ⟨a, ha, col, hc, mask, hmask, h⟩ := h
  rw [colB_of opened w i a col ha hc]
  by_cases hk : L.kept.getD w false = true
  · rw [if_pos hk] at h
    obtain rfl := Option.some.inj h
    rw [if_pos hk]
    exact ⟨hmask, rfl, rfl⟩
  · rw [if_neg hk] at h
    obtain ⟨main, hmain, h⟩ := Option.bind_eq_some_iff.1 h
    obtain rfl := Option.some.inj h
    rw [if_neg hk]
    exact ⟨hmask, hmain, rfl⟩

/-- The loop over the members, from any tables on. -/
theorem tablesFold_inv (L : GroupLayout) (opened : Array (Array Column)) (i : Nat) :
    ∀ (ws : List Nat) (t0 t : Array E × Array E × Array E),
      ws.foldlM (memberStep L opened i) t0 = some t →
      t.1.size = t0.1.size ∧ t.2.1.size = t0.2.1.size ∧
        t.2.2.toList = t0.2.2.toList ++ (ws.flatMap fun w =>
          if L.kept.getD w false then (colB opened w i).main.toList else []) ∧
        (∀ j, t.1.getD j zeroE = ws.foldl
          (fun base w =>
            if L.kept.getD w false then base
            else putAt (L.mainFirst.getD w none) (colB opened w i).main base)
          (fun j => t0.1.getD j zeroE) j) ∧
        ∀ j, t.2.1.getD j zeroE = ws.foldl
          (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base)
          (fun j => t0.2.1.getD j zeroE) j
  | [], t0, t, h => by
    obtain rfl : t0 = t := Option.some.inj h
    exact ⟨rfl, rfl, (List.append_nil _).symm, fun _ => rfl, fun _ => rfl⟩
  | w :: ws, t0, t, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a2, a1⟩ := memberStep_inv L opened i t0 t1 w h1
    obtain ⟨z1, z2⟩ := putRows_inv _ _ _ _ a2
    obtain ⟨b1, b2, b3, b4, b5⟩ := tablesFold_inv L opened i ws t1 t h2
    have hmask : ∀ j, t.2.1.getD j zeroE = (w :: ws).foldl
        (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base)
        (fun j => t0.2.1.getD j zeroE) j := fun j => by
      rw [b5 j, List.foldl_cons, show (fun j => t1.2.1.getD j zeroE) = _ from funext z2]
    by_cases hk : L.kept.getD w false = true
    · rw [if_pos hk] at a1
      obtain ⟨m1, m2⟩ := a1
      refine ⟨by rw [b1, m1], b2.trans z1, ?_, fun j => ?_, hmask⟩
      · rw [b3, m2, List.flatMap_cons, if_pos hk, Array.toList_append, List.append_assoc]
      · rw [b4 j, List.foldl_cons, if_pos hk, m1]
    · rw [if_neg hk] at a1
      obtain ⟨m0, m3⟩ := a1
      obtain ⟨m1, m2⟩ := putRows_inv _ _ _ _ m0
      refine ⟨b1.trans m1, b2.trans z1, ?_, fun j => ?_, hmask⟩
      · rw [b3, m3, List.flatMap_cons, if_neg hk, List.nil_append]
      · rw [b4 j, List.foldl_cons, if_neg hk,
          show (fun j => t1.1.getD j zeroE) = _ from funext m2]

/-- An array of zeros has the entry 0 everywhere. -/
private theorem getD_zeros (n : Nat) :
    (fun j => (Array.replicate n zeroE).getD j zeroE) = fun _ => zeroE := by
  funext j
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- If the tables of a listed position are there, they have 2^k and 2^h entries, their entries are
mainTable's and maskTable's, and the kept symbols are keptSymbols. -/
theorem tablesAt_all (L : GroupLayout) (opened : Array (Array Column)) (i : Nat)
    (t : Array E × Array E × Array E) (h : tablesAt L opened i = some t) :
    t.1.size = 2 ^ L.k ∧ t.2.1.size = 2 ^ L.h ∧ t.2.2.toList = keptSymbols L opened i ∧
      (∀ j, t.1.getD j zeroE = mainTable L opened i j) ∧
      ∀ j, t.2.1.getD j zeroE = maskTable L opened i j := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := tablesFold_inv L opened i _ _ t h
  refine ⟨b1.trans Array.size_replicate, b2.trans Array.size_replicate, b3, fun j => ?_,
    fun j => ?_⟩
  · rw [b4 j, getD_zeros]
    rfl
  · rw [b5 j, getD_zeros]
    rfl

/-- Two loops that take the same step at each element of the list give the same. -/
private theorem foldl_same_on {α β : Type} (f g : β → α → β) : ∀ (l : List α) (b : β),
    (∀ a, a ∈ l → ∀ c, f c a = g c a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h a List.mem_cons_self b]
    exact foldl_same_on f g l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The tables of a listed position, without a kept member: each member's symbols are at the rows
from its first row on, a later member's over an earlier one's; all other entries are 0. -/
theorem tablesAt_inv (L : GroupLayout) (opened : Array (Array Column)) (i : Nat)
    (t : Array E × Array E × Array E) (h : tablesAt L opened i = some t)
    (hk : ∀ w, w < L.members.size → L.kept.getD w false = false) :
    t.1.size = 2 ^ L.k ∧ t.2.1.size = 2 ^ L.h ∧ t.2.2 = #[] ∧
      (∀ j, t.1.getD j zeroE = (List.range L.members.size).foldl
        (fun base w => putAt (L.mainFirst.getD w none) (colB opened w i).main base)
        (fun _ => zeroE) j) ∧
      ∀ j, t.2.1.getD j zeroE = (List.range L.members.size).foldl
        (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base)
        (fun _ => zeroE) j := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := tablesAt_all L opened i t h
  refine ⟨b1, b2, ?_, fun j => ?_, b5⟩
  · have hn : keptSymbols L opened i = [] := by
      unfold keptSymbols
      rw [List.flatMap_eq_nil_iff]
      intro w hw
      rw [hk w (List.mem_range.1 hw)]
      rfl
    rw [hn] at b3
    exact Array.toList_eq_nil_iff.1 b3
  · rw [b4 j]
    unfold mainTable
    rw [foldl_same_on _ (fun base w => putAt (L.mainFirst.getD w none) (colB opened w i).main base)
      _ _ fun w hw c => by rw [hk w (List.mem_range.1 hw)]; rfl]

/-! ## The symbols of one listed position, and of all -/

/-- The symbols of the listed position number i, from its tables t: the main table folded, the kept
symbols, the mask table folded if there is a mask row, the fresh mask's column folded if there are
two. -/
def blockOf (s : SingleRows) (opened : Array (Array Column)) (i : Nat)
    (t : Array E × Array E × Array E) : List E :=
  [(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList
    ++ (if 1 ≤ s.masks then [(foldLow t.2.1 (s.gamma.take s.layout.h)).getD 0 zeroE] else [])
    ++ (if s.masks = 2 then
        [(foldLow (colB opened s.layout.members.size i).mask
          (s.gamma.take s.layout.h)).getD 0 zeroE] else [])

/-- A position has as many symbols as there are rows. -/
private theorem length_blockOf (s : SingleRows) (opened : Array (Array Column)) (i : Nat)
    (t : Array E × Array E × Array E) (hm : s.masks ≤ 2) (hk : t.2.2.size = s.keptRows) :
    (blockOf s opened i t).length = s.rows := by
  unfold blockOf SingleRows.rows
  simp only [List.length_append, List.length_cons, List.length_nil, Array.length_toList, hk]
  by_cases h1 : 1 ≤ s.masks
  · by_cases h2 : s.masks = 2
    · rw [if_pos h1, if_pos h2]
      simp only [List.length_cons, List.length_nil]
      omega
    · rw [if_pos h1, if_neg h2]
      simp only [List.length_cons, List.length_nil]
      omega
  · rw [if_neg h1, if_neg (by omega)]
    simp only [List.length_nil]
    omega

/-- One listed position: its tables are there, and its symbols are appended to the others. -/
theorem symStep_inv (s : SingleRows) (opened : Array (Array Column)) (y0 : Array E) (i : Nat)
    (y : Array E) (h : symStep s opened y0 i = some y) :
    ∃ t, tablesAt s.layout opened i = some t ∧ t.2.2.size = s.keptRows ∧
      (s.masks = 2 → (colB opened s.layout.members.size i).mask.size = 2 ^ s.layout.h) ∧
      y.toList = y0.toList ++ blockOf s opened i t := by
  unfold symStep at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨t, ht, ?_⟩
  by_cases hc : (t.2.2.size != s.keptRows) = true
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    have hsz : t.2.2.size = s.keptRows := by simpa using hc
    refine ⟨hsz, ?_⟩
    by_cases h2 : (s.masks == 2) = true
    · have hm2 : s.masks = 2 := by simpa using h2
      simp only [Option.bind_some, h2, if_true] at h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨fresh, hf, h⟩ := Option.bind_eq_some_iff.1 h
      have hcol := colB_of opened _ i a fresh ha hf
      by_cases hs : (fresh.mask.size != 2 ^ s.layout.h) = true
      · rw [if_pos hs] at h
        cases h
      · rw [if_neg hs] at h
        obtain rfl := Option.some.inj h
        refine ⟨fun _ => by rw [hcol]; simpa using hs, ?_⟩
        unfold blockOf
        rw [hcol, if_pos (by omega), if_pos (by omega), if_pos hm2]
        simp
    · have hm2 : ¬ s.masks = 2 := by simpa using h2
      simp only [Option.bind_some, h2, Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      refine ⟨fun c => absurd c hm2, ?_⟩
      unfold blockOf
      rw [if_neg hm2]
      by_cases h1 : 1 ≤ s.masks
      · rw [if_pos h1, if_pos h1]
        simp
      · rw [if_neg h1, if_neg h1]
        simp

/-- An entry of the first of two lists, one after the other. -/
private theorem getD_app_left (l l' : List E) (k : Nat) (h : k < l.length) :
    (l ++ l').getD k zeroE = l.getD k zeroE := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- An entry of the second of two lists, one after the other. -/
private theorem getD_app_right (l l' : List E) (k : Nat) :
    (l ++ l').getD (l.length + k) zeroE = l'.getD k zeroE := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- An entry of an array, read in its list. -/
private theorem getD_toListB (v : Array E) (k : Nat) : v.toList.getD k zeroE = v.getD k zeroE := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- The loop over the listed positions. -/
theorem symFold_inv (s : SingleRows) (opened : Array (Array Column)) (hm : s.masks ≤ 2) :
    ∀ (n : Nat) (y : Array E), (List.range n).foldlM (symStep s opened) #[] = some y →
      y.size = n * s.rows ∧
        ∀ i, i < n → ∃ t, tablesAt s.layout opened i = some t ∧ t.2.2.size = s.keptRows ∧
          (s.masks = 2 → (colB opened s.layout.members.size i).mask.size = 2 ^ s.layout.h) ∧
          ∀ r, r < s.rows →
            y.getD (i * s.rows + r) zeroE = (blockOf s opened i t).getD r zeroE
  | 0, y, h => by
    obtain rfl : #[] = y := Option.some.inj h
    exact ⟨(Nat.zero_mul _).symm, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | n + 1, y, h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨y0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hs0, he0⟩ := symFold_inv s opened hm n y0 h0
    have h1' : symStep s opened y0 n = some y := by
      rw [List.foldlM_cons] at h1
      obtain ⟨y1, a1, a2⟩ := Option.bind_eq_some_iff.1 h1
      obtain rfl : y1 = y := Option.some.inj a2
      exact a1
    obtain ⟨t, ht, hk, hf, hy⟩ := symStep_inv s opened y0 n y h1'
    have hlen := length_blockOf s opened n t hm hk
    have hl0 : y0.toList.length = n * s.rows := by rw [Array.length_toList, hs0]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← Array.length_toList, hy, List.length_append, hl0, hlen, Nat.succ_mul]
    · by_cases hin : i < n
      · obtain ⟨t', b1, b2, b3, b4⟩ := he0 i hin
        refine ⟨t', b1, b2, b3, fun r hr => ?_⟩
        have hle : (i + 1) * s.rows ≤ n * s.rows := Nat.mul_le_mul_right _ hin
        rw [Nat.succ_mul] at hle
        rw [← b4 r hr, ← getD_toListB, hy, getD_app_left _ _ _ (by rw [hl0]; omega), getD_toListB]
      · obtain rfl : i = n := by omega
        refine ⟨t, ht, hk, hf, fun r _ => ?_⟩
        rw [← getD_toListB, hy, ← hl0, getD_app_right]

/-- For a call that succeeds, on a complex with at most two mask rows (s.masks ≤ 2, which the
function does not test): the symbols of the single rows, taken apart. For each listed position in
turn: the main table folded at the whole point; the kept symbols; the mask table, and then the fresh
mask's column, folded at the point's first coordinates. -/
theorem singleRowsSymbols_inv (s : SingleRows) (opened : Array (Array Column)) (n : Nat)
    (y : Array E) (hm : s.masks ≤ 2) (h : singleRowsSymbols s opened n = some y) :
    s.gamma.length = s.layout.k ∧ s.layout.h ≤ s.layout.k ∧ y.size = n * s.rows ∧
      ∀ i, i < n → ∃ t, tablesAt s.layout opened i = some t ∧ t.2.2.size = s.keptRows ∧
        y.getD (i * s.rows) zeroE = (foldLow t.1 s.gamma).getD 0 zeroE ∧
        (∀ j, j < s.keptRows → y.getD (i * s.rows + 1 + j) zeroE = t.2.2.getD j zeroE) ∧
        (1 ≤ s.masks → y.getD (i * s.rows + s.maskRow 0) zeroE
          = (foldLow t.2.1 (s.gamma.take s.layout.h)).getD 0 zeroE) ∧
        (s.masks = 2 → (colB opened s.layout.members.size i).mask.size = 2 ^ s.layout.h ∧
          y.getD (i * s.rows + s.maskRow 1) zeroE
            = (foldLow (colB opened s.layout.members.size i).mask
                (s.gamma.take s.layout.h)).getD 0 zeroE) := by
  rw [singleRowsSymbols_eq] at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  by_cases c1 : (s.gamma.length != s.layout.k || decide (s.layout.k < s.layout.h)) = true
  · rw [if_pos c1] at h
    cases h
  rw [if_neg c1] at h
  by_cases c2 : (s.layout.kept.size != s.layout.members.size ||
      s.layout.mainFirst.size != s.layout.members.size ||
      s.layout.maskFirst.size != s.layout.members.size) = true
  · simp only [Option.bind_some] at h
    rw [if_pos c2] at h
    cases h
  simp only [Option.bind_some] at h
  rw [if_neg c2] at h
  have hc1 : s.gamma.length = s.layout.k ∧ s.layout.h ≤ s.layout.k := by
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Decidable.not_not,
      Nat.not_lt] at c1
    exact c1
  obtain ⟨hsize, hall⟩ := symFold_inv s opened hm n y h
  refine ⟨hc1.1, hc1.2, hsize, fun i hi => ?_⟩
  obtain ⟨t, ht, hk, hf, hr⟩ := hall i hi
  have hK : t.2.2.toList.length = s.keptRows := by rw [Array.length_toList, hk]
  refine ⟨t, ht, hk, ?_, fun j hj => ?_, fun h1 => ?_, fun h2 => ⟨hf h2, ?_⟩⟩
  · have e := hr 0 (by unfold SingleRows.rows; omega)
    rw [Nat.add_zero] at e
    exact e
  · have e := hr (1 + j) (by unfold SingleRows.rows; omega)
    rw [← Nat.add_assoc] at e
    rw [e]
    unfold blockOf
    have l1 : 1 + j < ([(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, hK]
      omega
    rw [getD_app_left _ _ _ (by rw [List.length_append]; omega), getD_app_left _ _ _ l1]
    exact (getD_app_right [_] _ j).trans (getD_toListB _ _)
  · have e := hr (s.maskRow 0) (by unfold SingleRows.rows SingleRows.maskRow; omega)
    rw [e]
    unfold blockOf
    have hl : ([(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList).length + 0 = s.maskRow 0 := by
      simp only [List.length_append, List.length_cons, List.length_nil, hK]
      unfold SingleRows.maskRow
      omega
    have l2 : ([(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList).length + 0
        < ([(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList
          ++ [(foldLow t.2.1 (s.gamma.take s.layout.h)).getD 0 zeroE]).length := by
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos h1, ← hl, getD_app_left _ _ _ l2, getD_app_right]
    rfl
  · have e := hr (s.maskRow 1) (by unfold SingleRows.rows SingleRows.maskRow; omega)
    rw [e]
    unfold blockOf
    rw [if_pos (by omega), if_pos h2]
    have hl : ([(foldLow t.1 s.gamma).getD 0 zeroE] ++ t.2.2.toList
        ++ [(foldLow t.2.1 (s.gamma.take s.layout.h)).getD 0 zeroE]).length + 0
        = s.maskRow 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil, hK]
      unfold SingleRows.maskRow
      omega
    rw [← hl, getD_app_right]
    rfl

end OnBytes

#print axioms OnBytes.putRows_inv
#print axioms OnBytes.singleRowsSymbols_eq
#print axioms OnBytes.colB_of
#print axioms OnBytes.memberStep_inv
#print axioms OnBytes.tablesFold_inv
#print axioms OnBytes.tablesAt_all
#print axioms OnBytes.tablesAt_inv
#print axioms OnBytes.symStep_inv
#print axioms OnBytes.symFold_inv
#print axioms OnBytes.singleRowsSymbols_inv
