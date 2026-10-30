-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/MeansLoc.lean: what the constraint (loc_x) says of words.

Main names: entry_product (an entry of Tensor.product reads as the scalar times bitsK),
tensorBelow_some, foldlM_maddS, placed_sum (vectors on a stretch of a vector that begins at a
multiple of its length, laid on a table and applied to it), locX_inv, locMeansW.

What is not claimed. That generatorAt gives the code's generator matrix. Nothing on the column being
the encoded index's. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.MeansRec
import Johnson.Desc.K14.Law.Placed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The pairs of a product vector read as bitsK. -/
theorem pairsVal_product (f : List F) (j : Nat) :
    pairsVal ρ (f.map fun x => (oneE, ofF x)) j = bitsK (f.map fun a => ρ.val (ofF a)) j := by
  induction f generalizing j with
  | nil => rfl
  | cons x f ih =>
    simp only [List.map_cons, pairsVal, bitsK, ih]
    by_cases h : j % 2 = 1 <;> simp [h, ρ.one]

/-- An entry of a product vector reads as the scalar times bitsK. -/
theorem entry_product (f : List F) (s : E) (j : Nat) :
    ρ.val ((Tensor.product f s).entry j) = ρ.val s * bitsK (f.map fun a => ρ.val (ofF a)) j := by
  rw [Tensor.entry_val]
  simp [Tensor.product, Tensor.denseVal, pairsVal_product]

/-- A cut that is made: the vector has the variables, and the length is within them. -/
theorem tensorBelow_some (v : Tensor) (start count len : Nat) (L : List Tensor)
    (h : tensorBelow v start count len = some L) : start + count ≤ v.vars ∧ len ≤ 2 ^ count := by
  unfold tensorBelow at h
  split at h
  · cases h
  · rename_i h1
    simpa only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] using h1

/-- The loop that adds up products of a base-field vector's and a vector's entries. -/
theorem foldlM_maddS (col : Array F) (w : Array E) : ∀ (l : List Nat) (a b : E),
    l.foldlM (fun s r => do pure (maddS s (← col[r]?) (← w[r]?))) a = some b →
    ρ.val b = ρ.val a +
      (l.map fun r => ρ.val (w.getD r zeroE) * ρ.val (ofF (col.getD r 0))).sum := by
  intro l
  induction l with
  | nil =>
    intro a b h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons r l ih =>
    intro a b h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨c, ⟨x, hx, z, hz, rfl⟩, h2⟩ := h
    rw [ih _ b h2, maddS_val]
    simp only [List.map_cons, List.sum_cons, Array.getD_eq_getD_getElem?, hx, hz, Option.getD_some]
    ring

/-- Vectors with n variables on the stretch of 2 ^ n entries that begins at entry first, a multiple
of 2 ^ n: laid on a table and applied to it. -/
theorem placed_sum (lay : VectorLay) (tail : List Tensor) (n first : Nat)
    (hL : ∀ t ∈ tail, t.denseVars = [] ∧ t.vars = n) (hn : n ≤ lay.bits)
    (hal : first % 2 ^ n = 0) (hq : first / 2 ^ n < 2 ^ (lay.bits - n)) (w : Nat → K) :
    ∑ i ∈ Finset.range (2 ^ lay.bits),
        ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
          ρ.val ((lay.onTable t).entry i)).sum * w i =
      ∑ j ∈ Finset.range (2 ^ n),
        (tail.map fun t => ρ.val (t.entry j)).sum * w (lay.index (first + j)) := by
  have hL' : ∀ t ∈ tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n)),
      t.denseVars = [] ∧ t.vars = lay.bits := by
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ht'
    obtain ⟨h1, h2⟩ := hL t ht
    have h3 : t.pairs.length = n := h2
    refine ⟨by simp [Tensor.insertChoice, h1], ?_⟩
    simp only [Tensor.vars, Tensor.insertChoice, List.length_append, List.length_take,
      List.length_drop, choicePairs_length, h3]
    omega
  have e : 2 ^ lay.bits = 2 ^ n * 2 ^ (lay.bits - n) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hfirst : 2 ^ n * (first / 2 ^ n) = first := by
    have := Nat.div_add_mod first (2 ^ n)
    omega
  rw [laid_sum ρ lay _ lay.bits hL' (Nat.le_refl _), e, sum_blocks]
  have hb : ∀ b ∈ Finset.range (2 ^ (lay.bits - n)),
      (∑ j ∈ Finset.range (2 ^ n),
        ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
          ρ.val (t.entry (j + 2 ^ n * b))).sum * w (lay.index (j + 2 ^ n * b))) =
      if first / 2 ^ n = b then ∑ j ∈ Finset.range (2 ^ n),
        (tail.map fun t => ρ.val (t.entry j)).sum * w (lay.index (first + j)) else 0 := by
    intro b hb
    have hb' := Finset.mem_range.1 hb
    have hin : ∀ j ∈ Finset.range (2 ^ n),
        ((tail.map (·.insertChoice n (lay.bits - n) (first / 2 ^ n))).map fun t =>
          ρ.val (t.entry (j + 2 ^ n * b))).sum =
        (if b = first / 2 ^ n then 1 else 0) * (tail.map fun t => ρ.val (t.entry j)).sum := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      refine List.map_congr_left fun t ht => ?_
      have h1 : (j + 2 ^ n * b) / 2 ^ n % 2 ^ (lay.bits - n) = b := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hj', Nat.zero_add,
          Nat.mod_eq_of_lt hb']
      have h2 : unshift n (lay.bits - n) (j + 2 ^ n * b) = j := by
        have h3 : (j + 2 ^ n * b) / 2 ^ (n + (lay.bits - n)) = 0 := by
          apply Nat.div_eq_of_lt
          rw [Nat.pow_add]
          calc j + 2 ^ n * b < 2 ^ n + 2 ^ n * b := by omega
            _ = 2 ^ n * (b + 1) := by ring
            _ ≤ 2 ^ n * 2 ^ (lay.bits - n) := Nat.mul_le_mul_left _ hb'
        rw [unshift, h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj']
        simp
      show ρ.val ((t.insertChoice n (lay.bits - n) (first / 2 ^ n)).entry (j + 2 ^ n * b)) = _
      rw [Tensor.entry_insertChoice ρ t n _ _ _ (by rw [(hL t ht).2]), h1, h2,
        Nat.mod_eq_of_lt hq]
    by_cases hbq : first / 2 ^ n = b
    · rw [if_pos hbq]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hin j hj, if_pos hbq.symm, one_mul, ← hbq, hfirst, Nat.add_comm]
    · rw [if_neg hbq]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [hin j hj, if_neg (Ne.symm hbq), zero_mul, zero_mul]
  rw [Finset.sum_congr rfl hb, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hq)]

/-- What (loc_x) is made of. -/
theorem locX_inv (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (row : Row) (h : locX S x w column u = some row) :
    ∃ (A tail : List Tensor) (sum : E),
      tensorBelow (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
        (ofF (generatorAt S.index.code x).messageScale)) 0 S.index.code.logEll S.index.code.ell =
          some A ∧
      (if S.index.code.r == 0 then some []
        else tensorBelow (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
          (ofF (generatorAt S.index.code x).tailScale)) 0 S.index.code.logR S.index.code.r) =
          some tail ∧
      (List.range w.size).foldlM
        (fun s r => do pure (maddS s (← column[r]?) (← w[r]?))) zeroE = some sum ∧
      row = { u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
        (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR))) with
          kind := .generator, target := sum } := by
  unfold locX at h
  by_cases hr : (S.index.code.r == 0) = true
  · simp only [hr, if_true, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨A, hA, tail, ht, sum, hs, hrow⟩ := h
    exact ⟨A, tail, sum, hA, by rw [if_pos hr, ht], hs, hrow.symm⟩
  · simp only [hr, Bool.false_eq_true, if_false, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨A, hA, tail, ht, sum, hs, hrow⟩ := h
    exact ⟨A, tail, sum, hA, by rw [if_neg hr, ht], hs, hrow.symm⟩

/-- **MEANS**, for (loc_x). -/
theorem locMeansW : LocMeansW ρ := by
  intro T S x w column u row hok h hP m
  obtain ⟨A, tail, sum, hA, ht, hs, rfl⟩ := locX_inv S x w column u row h
  have hvA : (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
      (ofF (generatorAt S.index.code x).messageScale)).vars = S.index.code.logEll := by
    have h1 := (tensorBelow_some _ _ _ _ _ hA).1
    have h2 : (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logEll)
        (ofF (generatorAt S.index.code x).messageScale)).vars ≤ S.index.code.logEll := by
      simp only [Tensor.product, Tensor.vars, List.length_map, List.length_take]
      omega
    omega
  have hc : ∀ o pt idx,
      ρ.val (({ u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
        (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR))) with
          kind := .generator, target := sum } : Row).coefficient o pt idx) =
      if u.oracle = o ∧ Part.main = pt then
        (A.map fun t => ρ.val ((u.lay.onTable t).entry idx)).sum +
        ((tail.map (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
          (S.tailFirst / 2 ^ S.index.code.logR))).map fun t =>
            ρ.val ((u.lay.onTable t).entry idx)).sum else 0 := by
    intro o pt idx
    show ρ.val ((u.addAll (u.addAll {} A) (tail.map (·.insertChoice S.index.code.logR
        (u.lay.bits - S.index.code.logR) (S.tailFirst / 2 ^ S.index.code.logR)))).coefficient
          o pt idx) = _
    unfold FoldedRow.addAll
    rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
    split_ifs <;> simp
  have hsum := foldlM_maddS ρ column w _ _ _ hs
  rw [ρ.zero, zero_add, list_range_sum] at hsum
  have hB : ∑ i ∈ Finset.range (2 ^ u.lay.bits),
      ((tail.map (·.insertChoice S.index.code.logR (u.lay.bits - S.index.code.logR)
        (S.tailFirst / 2 ^ S.index.code.logR))).map fun t =>
          ρ.val ((u.lay.onTable t).entry i)).sum * m u.oracle .main i =
      ∑ j ∈ Finset.range S.index.code.r,
        ρ.val ((Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
          (ofF (generatorAt S.index.code x).tailScale)).entry j) *
            m u.oracle .main (u.lay.index (S.tailFirst + j)) := by
    by_cases hr : S.index.code.r = 0
    · rw [if_pos (by simp [hr])] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      simp [hr]
    · rw [if_neg (by simp [hr])] at ht
      have h1 := (tensorBelow_some _ _ _ _ _ ht).1
      have hvT : (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
          (ofF (generatorAt S.index.code x).tailScale)).vars = S.index.code.logR := by
        have h2 : (Tensor.product ((generatorAt S.index.code x).f.take S.index.code.logR)
            (ofF (generatorAt S.index.code x).tailScale)).vars ≤ S.index.code.logR := by
          simp only [Tensor.product, Tensor.vars, List.length_map, List.length_take]
          omega
        omega
      have hmem := tensorBelow_mem _ rfl _ _ _ _ ht
      rw [hvT] at hmem
      have hrt := hP.roomTail
      have hn : S.index.code.logR ≤ u.lay.bits := ceilLog2_le _ _ (by omega)
      have e : 2 ^ u.lay.bits = 2 ^ S.index.code.logR * 2 ^ (u.lay.bits - S.index.code.logR) := by
        rw [← Nat.pow_add]; congr 1; omega
      have hq : S.tailFirst / 2 ^ S.index.code.logR < 2 ^ (u.lay.bits - S.index.code.logR) :=
        Nat.div_lt_of_lt_mul (by rw [← e]; omega)
      rw [placed_sum ρ u.lay tail _ _ hmem hn hP.aligned hq]
      refine Eq.trans (Finset.sum_congr rfl fun j _ => by
        rw [tensorBelow_val ρ _ rfl _ _ _ _ ht]) ?_
      exact cut0_sum S.index.code.logR S.index.code.r (le_two_pow_ceilLog2 _) _ _
  unfold Means.Says LocEq
  rw [value_one ρ T _ u.oracle u.lay.bits _ hc hP.has hP.bits m]
  simp only [add_mul, Finset.sum_add_distrib]
  rw [hB, cut_laid_sum ρ u.lay _ rfl 0 S.index.code.logEll S.index.code.ell A hA
    (by rw [hvA]; exact hP.room), hvA,
    cut0_sum S.index.code.logEll S.index.code.ell (le_two_pow_ceilLog2 _)]
  show _ = ρ.val sum ↔ _
  rw [hsum]
  have e1 : ∀ (f : List F) (s : E) (n : Nat) (U : Nat → K),
      ∑ j ∈ Finset.range n, ρ.val ((Tensor.product f s).entry j) * U j =
        ρ.val s * ∑ j ∈ Finset.range n, bitsK (f.map fun a => ρ.val (ofF a)) j * U j := by
    intro f s n U
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [entry_product, mul_assoc]
  rw [e1, e1, List.map_take, List.map_take]

end Desc.K14.Law
