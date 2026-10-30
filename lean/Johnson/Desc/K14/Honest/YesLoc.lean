--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesLoc.lean: the constraint (loc_x) of the linear claim's shared rounds can
be made, and the group of the folded row takes it.

(loc_x) says that what the message o_u holds, encoded under the committed table's code, has at the
location x the value to which the table's column at x folds (Johnson/Desc/K14/Text.lean: locX). It
is a row on o_u alone: row x of the code's generator matrix, on the folded message (cut below the
message length) and on the folded random tail (cut below the tail's length and placed at the stretch
of entries that holds the tail).

Main names:
  foldlM_maddS_makes  the loop that folds a column returns where the entries are there
  vars_product        a product vector has one variable for each factor
  gen_take_length     a generator row has factors enough for the message and for the tail
  locX_makes          **(loc_x) can be made**, where the column has at least as many words as there
                      are weights
  placed_zero         the summands of a cut, placed at a stretch of entries and laid on a table, add
                      up to 0 at the index of an entry behind the stretch's used part
  locRow_far          (loc_x) reads as 0 on every entry of o_u's main table behind the folded row,
                      on o_u's mask table, and on every other message
  locX_fits           **the group takes it** (Fits)

What is not claimed. That o_u sits in its group at any statement. Nothing on what the constraint
means, on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesRec
import Johnson.Desc.K14.Law.Condition
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Fits)
open OnBytes.Slice (index_entryAt entryAt_lt)
open Desc.K14.Law (locX_inv coefficient_addLaid coefficient_empty le_two_pow_ceilLog2 onTable_entry
  tensorBelow_mem tensorBelow_val le_roundUp)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The loop that folds a column returns where the entries are there. -/
theorem foldlM_maddS_makes (col : Array F) (w : Array E) : ∀ (l : List Nat) (a : E),
    (∀ r ∈ l, r < col.size ∧ r < w.size) →
    ∃ b, l.foldlM (fun s r => do pure (maddS s (← col[r]?) (← w[r]?))) a = some b := by
  intro l
  induction l with
  | nil =>
    intro a _
    exact ⟨a, rfl⟩
  | cons r l ih =>
    intro a h
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    obtain ⟨b, hb⟩ := ih (maddS a col[r] w[r]) fun q hq => h q (List.mem_cons_of_mem _ hq)
    refine ⟨b, ?_⟩
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    exact ⟨_, ⟨col[r], Array.getElem?_eq_getElem h1, w[r], Array.getElem?_eq_getElem h2, rfl⟩, hb⟩

/-- A product vector has one variable for each factor. -/
theorem vars_product (f : List F) (s : E) : (Tensor.product f s).vars = f.length := by
  simp only [Tensor.product, Tensor.vars, List.length_map]

/-- The first k factors of a generator row are k, where 2 ^ logDim reaches a number that k bits
index. -/
theorem gen_take_length (c : Code) (x n : Nat) (hn : n ≤ 2 ^ c.logDim) :
    ((generatorAt c x).f.take (ceilLog2 n)).length = ceilLog2 n := by
  rw [List.length_take, Slice.generatorAt_f, Slice.length_squaresOf]
  exact Nat.min_eq_left (Slice.ceilLog2_le _ _ hn)

/-- The message's product vector has logEll variables; the tail's has logR. -/
theorem vars_message (S : FoldeqShape) (x : Nat) :
    (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
      (ofF (generatorAt S.index.code x).messageScale)).vars = S.index.code.logEll := by
  rw [vars_product]
  exact gen_take_length S.index.code x S.index.code.ell (Slice.ell_le_logDim _)

@[inherit_doc vars_message]
theorem vars_tail (S : FoldeqShape) (x : Nat) :
    (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
      (ofF (generatorAt S.index.code x).tailScale)).vars = S.index.code.logR := by
  rw [vars_product]
  exact gen_take_length S.index.code x S.index.code.r (Slice.r_le_logDim _)

/-- The row (loc_x), from its three makings. -/
def locRow (S : FoldeqShape) (u : FoldedRow) (A tail : List Tensor) (sum : E) : Row :=
  { u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR))) with
        kind := .generator, target := sum }

/-- **(loc_x) can be made.** -/
theorem locX_makes (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (hc : w.size ≤ column.size) : ∃ row, locX S x w column u = some row := by
  obtain ⟨A, hA⟩ := tensorBelow_makes
    (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
      (ofF (generatorAt S.index.code x).messageScale)) rfl 0 S.index.code.logEll S.index.code.ell
    (by rw [vars_message]; omega)
    (le_two_pow_ceilLog2 _)
  obtain ⟨sum, hs⟩ := foldlM_maddS_makes column w (List.range w.size) zeroE (by
    intro r hr
    have hr' := List.mem_range.1 hr
    exact ⟨Nat.lt_of_lt_of_le hr' hc, hr'⟩)
  by_cases hr : (S.index.code.r == 0) = true
  · refine ⟨locRow S u A [] sum, ?_⟩
    unfold locX
    simp only [hr, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq]
    exact ⟨A, hA, [], rfl, sum, hs, rfl⟩
  · obtain ⟨tail, ht⟩ := tensorBelow_makes
      (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
        (ofF (generatorAt S.index.code x).tailScale)) rfl 0 S.index.code.logR S.index.code.r
      (by rw [vars_tail]; omega)
      (le_two_pow_ceilLog2 _)
    refine ⟨locRow S u A tail sum, ?_⟩
    unfold locX
    simp only [hr, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq]
    exact ⟨A, hA, tail, ht, sum, hs, rfl⟩

/-- **The summands of a cut, placed at the stretch of 2 ^ n entries that begins at entry first and
laid on a table, add up to 0 at the index of an entry from first + len on.** -/
theorem placed_zero (lay : VectorLay) (v : Tensor) (hd : v.denseVars = []) (n len first : Nat)
    (tail : List Tensor) (hv : v.vars = n) (ht : tensorBelow v 0 n len = some tail)
    (hn : n ≤ lay.bits) (hal : first % 2 ^ n = 0) (k : Nat) (hk : k < 2 ^ lay.bits)
    (hfar : first + len ≤ k) :
    ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
      ρ.val ((lay.onTable t).entry (lay.index k))).sum = 0 := by
  have hmem := tensorBelow_mem v hd 0 n len tail ht
  have each : ∀ t ∈ tail,
      ((fun t => ρ.val ((lay.onTable t).entry (lay.index k))) ∘
        (fun t : Tensor => t.insertChoice n (lay.bits - n) (first / 2 ^ n))) t =
      (if k / 2 ^ n % 2 ^ (lay.bits - n) = first / 2 ^ n % 2 ^ (lay.bits - n) then 1 else 0) *
        ρ.val (t.entry (unshift n (lay.bits - n) k)) := by
    intro t htm
    obtain ⟨h1, h2⟩ := hmem t htm
    have h3 : t.pairs.length = n := by rw [← hv]; exact h2
    have hd' : (t.insertChoice n (lay.bits - n) (first / 2 ^ n)).denseVars = [] := by
      simp [Tensor.insertChoice, h1]
    have hv' : (t.insertChoice n (lay.bits - n) (first / 2 ^ n)).vars = lay.bits := by
      simp only [Tensor.vars, Tensor.insertChoice, List.length_append, List.length_take,
        List.length_drop, choicePairs_length, h3]
      omega
    show ρ.val ((lay.onTable (t.insertChoice n (lay.bits - n) (first / 2 ^ n))).entry
      (lay.index k)) = _
    rw [onTable_entry ρ lay _ hd' (by rw [hv']) k hk, hv', if_pos hk,
      Tensor.entry_insertChoice ρ t n _ _ _ (by rw [h2, hv])]
  rw [List.map_map, List.map_congr_left each, List.sum_map_mul_left,
    tensorBelow_val ρ v hd 0 n len tail ht]
  by_cases hc : k / 2 ^ n % 2 ^ (lay.bits - n) = first / 2 ^ n % 2 ^ (lay.bits - n)
  · rw [if_pos hc, one_mul]
    have e : 2 ^ lay.bits = 2 ^ n * 2 ^ (lay.bits - n) := by
      rw [← Nat.pow_add]; congr 1; omega
    have hk1 : k / 2 ^ n < 2 ^ (lay.bits - n) := Nat.div_lt_of_lt_mul (by rw [← e]; exact hk)
    have hf1 : first / 2 ^ n < 2 ^ (lay.bits - n) :=
      Nat.div_lt_of_lt_mul (by rw [← e]; omega)
    rw [Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hf1] at hc
    have hz : k / 2 ^ (n + (lay.bits - n)) = 0 := by
      apply Nat.div_eq_of_lt
      rw [Nat.pow_add, ← e]
      exact hk
    have hU : unshift n (lay.bits - n) k = k % 2 ^ n := by
      rw [unshift, hz]
      simp
    have a1 := Nat.div_add_mod k (2 ^ n)
    have a2 := Nat.div_add_mod first (2 ^ n)
    rw [hc] at a1
    have hlt := Nat.mod_lt k (Nat.two_pow_pos n)
    rw [hU, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt, if_neg (by omega)]
  · rw [if_neg hc, zero_mul]

/-- (loc_x)'s coefficient on an entry. -/
theorem locRow_coefficient (S : FoldeqShape) (u : FoldedRow) (A tail : List Tensor) (sum : E)
    (o : Nat) (pt : Part) (idx : Nat) :
    ρ.val ((locRow S u A tail sum).coefficient o pt idx) =
      if u.oracle = o ∧ Part.main = pt then
        (A.map fun t => ρ.val ((u.lay.onTable t).entry idx)).sum +
        ((tail.map (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
          (S.tailFirst / 2 ^ S.index.code.logR))).map fun t =>
            ρ.val ((u.lay.onTable t).entry idx)).sum else 0 := by
  show ρ.val ((u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).coefficient
        o pt idx) = _
  unfold FoldedRow.addAll
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  split_ifs <;> simp

/-- The two makings of (loc_x)'s left side. -/
structure LocMade (S : FoldeqShape) (x : Nat) (A tail : List Tensor) : Prop where
  message : tensorBelow (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
    (ofF (generatorAt S.index.code x).messageScale)) 0 S.index.code.logEll S.index.code.ell = some A
  tail : (if S.index.code.r == 0 then some []
    else tensorBelow (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
      (ofF (generatorAt S.index.code x).tailScale)) 0 S.index.code.logR S.index.code.r) = some tail

/-- (loc_x) reads as 0 on every entry of o_u's main table behind the folded row, and on every other
table. -/
theorem locRow_far (S : FoldeqShape) (x : Nat) (u : FoldedRow) (A tail : List Tensor) (sum : E)
    (hM : LocMade S x A tail) (hroom : S.index.code.logEll ≤ u.lay.bits)
    (hal : S.tailFirst % 2 ^ S.index.code.logR = 0) (o : Nat) (pt : Part) (idx : Nat)
    (hfar : u.oracle = o → Part.main = pt →
      idx < 2 ^ u.lay.bits ∧ S.entries ≤ u.lay.entryAt idx) :
    ρ.val ((locRow S u A tail sum).coefficient o pt idx) = 0 := by
  rw [locRow_coefficient]
  by_cases h : u.oracle = o ∧ Part.main = pt
  · rw [if_pos h]
    obtain ⟨hi, hk⟩ := hfar h.1 h.2
    have e := index_entryAt u.lay idx hi
    have hkl := entryAt_lt u.lay idx hi
    have hE : S.entries = S.tailFirst + S.index.code.r := rfl
    have hT : S.index.code.ell ≤ S.tailFirst := le_roundUp _ _ (Nat.two_pow_pos _)
    have z1 := laid_cut_zero ρ u.lay _ rfl 0 S.index.code.logEll S.index.code.ell A hM.message
      (by rw [vars_message]; exact hroom) (u.lay.entryAt idx) hkl (by
        intro hlt
        rw [vars_message] at hlt
        rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
        omega)
    rw [e] at z1
    have z2 : ((tail.map (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
        (S.tailFirst / 2 ^ S.index.code.logR))).map fun t =>
          ρ.val ((u.lay.onTable t).entry idx)).sum = 0 := by
      have ht := hM.tail
      by_cases hr : S.index.code.r = 0
      · rw [if_pos (by simp [hr])] at ht
        simp only [Option.some.injEq] at ht
        subst ht
        rfl
      · rw [if_neg (by simp [hr])] at ht
        have hn : S.index.code.logR ≤ u.lay.bits := Slice.ceilLog2_le _ _ (by omega)
        have z := placed_zero ρ u.lay _ rfl S.index.code.logR S.index.code.r S.tailFirst tail
          (vars_tail S x) ht hn hal (u.lay.entryAt idx) hkl (by omega)
        rw [e] at z
        exact z
    rw [z1, z2, add_zero]
  · rw [if_neg h]

/-- **The group takes (loc_x).** -/
theorem locX_fits (T : Statement) (G : Group) (S : FoldeqShape) (x : Nat) (w : Array E)
    (column : Array F) (u : FoldedRow) (row : Row) (h : locX S x w column u = some row)
    (hS : Sits T G u.oracle u.lay S.entries) (hroom : S.index.code.logEll ≤ u.lay.bits)
    (hrt : S.tailFirst + S.index.code.r ≤ 2 ^ u.lay.bits)
    (hal : S.tailFirst % 2 ^ S.index.code.logR = 0) : Fits T G row := by
  obtain ⟨A, tail, sum, hA, ht, _, rfl⟩ := locX_inv S x w column u row h
  have hM : LocMade S x A tail := ⟨hA, ht⟩
  have htail : ∀ t ∈ tail, t.denseVars = [] ∧ t.vars = S.index.code.logR := by
    intro t htm
    by_cases hr : S.index.code.r = 0
    · rw [if_pos (by simp [hr])] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      cases htm
    · rw [if_neg (by simp [hr])] at ht
      obtain ⟨d1, d2⟩ := tensorBelow_mem _ rfl _ _ _ _ ht t htm
      exact ⟨d1, d2.trans (vars_tail S x)⟩
  have hn : tail ≠ [] → S.index.code.logR ≤ u.lay.bits := fun _ =>
    Slice.ceilLog2_le _ _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    cases e
  · intro t htm
    have ht' : t ∈ (u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).terms := htm
    unfold FoldedRow.addAll at ht'
    rcases mem_addLaid _ _ _ _ _ ht' with h1 | ⟨v, hvL, rfl⟩
    · rcases mem_addLaid _ _ _ _ _ h1 with h2 | ⟨v, hvL, rfl⟩
      · simp at h2
      · obtain ⟨d1, d2⟩ := tensorBelow_mem _ rfl _ _ _ _ hA v hvL
        exact laid_term_fits hS v d1 (by rw [d2, vars_message]; exact hroom)
    · obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 hvL
      obtain ⟨d1, d2⟩ := htail t0 ht0
      have d3 : t0.pairs.length = S.index.code.logR := d2
      have hb := hn (List.ne_nil_of_mem ht0)
      refine laid_term_fits hS _ (by simp [Tensor.insertChoice, d1]) ?_
      simp only [Tensor.vars, Tensor.insertChoice, List.length_append, List.length_take,
        List.length_drop, choicePairs_length, d3]
      omega
  · intro y hy
    have hy' : y ∈ (u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).units := hy
    unfold FoldedRow.addAll at hy'
    rw [units_addLaid, units_addLaid] at hy'
    simp at hy'
  · show (u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).runs = #[]
    unfold FoldedRow.addAll
    rw [runs_addLaid, runs_addLaid]
  · show (u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
      (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).forms = #[]
    unfold FoldedRow.addAll
    rw [forms_addLaid, forms_addLaid]
  · intro o _ y hy q hq
    refine locRow_far Model.Reading.gl S x u A tail sum hM hroom hal o q.1 q.2 ?_
    intro e1 e2
    subst e1
    exact hS.pad y hy q hq e2.symm

end Desc.K14.Honest

#print axioms Desc.K14.Honest.foldlM_maddS_makes
#print axioms Desc.K14.Honest.vars_product
#print axioms Desc.K14.Honest.gen_take_length
#print axioms Desc.K14.Honest.vars_message
#print axioms Desc.K14.Honest.vars_tail
#print axioms Desc.K14.Honest.locX_makes
#print axioms Desc.K14.Honest.placed_zero
#print axioms Desc.K14.Honest.locRow_coefficient
#print axioms Desc.K14.Honest.locRow_far
#print axioms Desc.K14.Honest.locX_fits
