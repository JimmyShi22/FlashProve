-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/MeansDot.lean: what the constraint (Dot) of the linear claim's second part says
of words.

(Dot) is the plain function linDotRow: the instance's row weights, cut at the rows of M, on
omega_col, against the equality vector at the shared point on W. Under PlacedDot (the two messages
are two and have main tables of the sizes of their layouts, which hold the vectors) what it says of
words is the equation DotEq.
Main names: value_two, mem_mapM_back, sum_flatten_mapM, PlacedDot, DotMeansW, dotMeansW.

What is not claimed. The row weights are structured vectors WITHOUT a written-out factor: a premise,
WHICH THE PROGRAM's OWN PENDING ROWS DO NOT MEET: the general law, for well-formed row weights, is
in Johnson/Desc/K14/Law/MeansDotOk.lean; value_two, mem_mapM_back, sum_flatten_mapM and PlacedDot
are spent there. Nothing on which group the constraint is laid on, on (Eval), or on soundness.

-/
import Johnson.Desc.K14.Law.MeansRec
import Johnson.Desc.K14.Law.DotCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- A constraint that has coefficients on two main tables alone, applied to words. -/
theorem value_two (T : Statement) (row : Row) (o1 b1 o2 b2 : Nat) (c1 c2 : Nat → K)
    (hne : o1 ≠ o2)
    (hc : ∀ o pt i, ρ.val (row.coefficient o pt i) =
      (if o1 = o ∧ Part.main = pt then c1 i else 0) + (if o2 = o ∧ Part.main = pt then c2 i else 0))
    (h1 : T.has o1 .main = true) (hb1 : T.tableBits o1 .main = b1)
    (h2 : T.has o2 .main = true) (hb2 : T.tableBits o2 .main = b2) (m : Words K) :
    Means.value ρ T row m = (∑ i ∈ Finset.range (2 ^ b1), c1 i * m o1 .main i) +
      ∑ i ∈ Finset.range (2 ^ b2), c2 i * m o2 .main i := by
  have ts1 : Means.tableSize T o1 .main = 2 ^ b1 := by
    unfold Means.tableSize; rw [if_pos h1, hb1]
  have ts2 : Means.tableSize T o2 .main = 2 ^ b2 := by
    unfold Means.tableSize; rw [if_pos h2, hb2]
  have hmask : ∀ o, Means.onTable ρ T row m o .mask = 0 := by
    intro o
    unfold Means.onTable
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hc]; simp
  have hmain : ∀ o, Means.onTable ρ T row m o .main =
      (if o1 = o then ∑ i ∈ Finset.range (2 ^ b1), c1 i * m o1 .main i else 0) +
      (if o2 = o then ∑ i ∈ Finset.range (2 ^ b2), c2 i * m o2 .main i else 0) := by
    intro o
    unfold Means.onTable
    by_cases e1 : o1 = o
    · subst e1
      have e2 : ¬ o2 = o1 := fun e => hne e.symm
      rw [if_pos rfl, if_neg e2, add_zero, ts1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc]; simp [e2]
    · by_cases e2 : o2 = o
      · subst e2
        rw [if_neg e1, if_pos rfl, zero_add, ts2]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc]; simp [e1]
      · rw [if_neg e1, if_neg e2, add_zero]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [hc]; simp [e1, e2]
  unfold Means.value
  simp only [hmask, hmain, add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 (lt_of_has T _ _ h1)),
    if_pos (Finset.mem_range.2 (lt_of_has T _ _ h2))]

/-- A list made item by item: each of its items is some item's own. -/
theorem mem_mapM_back {α β : Type} (f : α → Option β) : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil =>
    intro r h b hb
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; cases hb
  | cons x l ih =>
    intro r h b hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨a, ha, hfa⟩ := ih ys hys b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hfa⟩

/-- A sum over lists made item by item and laid end to end: item by item. -/
theorem sum_flatten_mapM {α β : Type} (f : α → Option (List β)) (F : β → K) (G : α → K) :
    ∀ (l : List α) (r : List (List β)),
    (∀ a ∈ l, ∀ L, f a = some L → (L.map F).sum = G a) →
    l.mapM f = some r → (r.flatten.map F).sum = (l.map G).sum := by
  intro l
  induction l with
  | nil =>
    intro r _ h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; simp
  | cons x l ih =>
    intro r hf h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    simp only [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [hf x List.mem_cons_self y hy, ih ys (fun a ha => hf a (List.mem_cons_of_mem _ ha)) hys]

/-- The two messages of (Dot) are two, and have main tables of the sizes of their layouts, which
hold the vectors. -/
structure PlacedDot (T : Statement) (S : LinShape) (omega : Nat) (omegaLay : VectorLay) (w : Nat)
    (wLay : VectorLay) : Prop where
  two : omega ≠ w
  hasOmega : T.has omega .main = true
  hasW : T.has w .main = true
  bitsOmega : T.tableBits omega .main = omegaLay.bits
  bitsW : T.tableBits w .main = wLay.bits
  roomOmega : S.kRow ≤ omegaLay.bits
  roomW : S.kCol ≤ wLay.bits

/-- **MEANS**, for (Dot), as a proposition. -/
def DotMeansW : Prop :=
  ∀ (T : Statement) (S : LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : Row),
    linDotRow S weights psi omega omegaLay w wLay = some row →
    (∀ g ∈ weights, g.denseVars = []) → PlacedDot T S omega omegaLay w wLay → ∀ m : Words K,
      (Means.Says ρ T row m ↔
        DotEq S.matrixRows S.kCol (fun y => (weights.map fun g => ρ.val (g.entry y)).sum)
          (fun y => m omega .main (omegaLay.index y)) (psi.map ρ.val)
          (fun c => m w .main (wLay.index c)))

/-- **MEANS**, for (Dot). -/
theorem dotMeansW : DotMeansW ρ := by
  intro T S weights psi omega omegaLay w wLay row h hd hP m
  have hR : S.matrixRows ≤ 2 ^ S.kRow := le_two_pow_ceilLog2 _
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨u0, hg, cut, hcut, hrow⟩ := h
  have hok : (psi.length == S.kCol && weights.all (·.vars == S.kRow)) = true := by
    by_contra hne
    simp [guard, hne] at hg
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hok
  obtain ⟨hpsi, hvars⟩ := hok
  have hmem : ∀ t ∈ cut.flatten, t.denseVars = [] ∧ t.vars = S.kRow := by
    intro t ht
    obtain ⟨L, hL, htL⟩ := List.mem_flatten.1 ht
    obtain ⟨g, hgw, hgL⟩ := mem_mapM_back _ _ _ hcut L hL
    have := tensorBelow_mem g (hd g hgw) _ _ _ _ hgL t htL
    exact ⟨this.1, this.2.trans (hvars g hgw)⟩
  have hvW : (Tensor.eq psi (negE oneE)).vars = S.kCol := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, hpsi]
  have hmemW : ∀ t ∈ [Tensor.eq psi (negE oneE)], t.denseVars = [] ∧ t.vars = S.kCol := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨rfl, hvW⟩
  have hc : ∀ o pt i, ρ.val (row.coefficient o pt i) =
      (if omega = o ∧ Part.main = pt then
        (cut.flatten.map fun t => ρ.val ((omegaLay.onTable t).entry i)).sum else 0) +
      (if w = o ∧ Part.main = pt then
        ([Tensor.eq psi (negE oneE)].map fun t => ρ.val ((wLay.onTable t).entry i)).sum
        else 0) := by
    intro o pt i
    rw [← hrow, coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  have ht : row.target = zeroE := by
    rw [← hrow, target_addLaid, target_addLaid]
  have hsum : ∀ j, (cut.flatten.map fun t => ρ.val (t.entry j)).sum =
      if j / 2 ^ 0 % 2 ^ S.kRow < S.matrixRows then (weights.map fun g => ρ.val (g.entry j)).sum
      else 0 := by
    intro j
    rw [← sum_map_ite]
    have hw : ∀ g ∈ weights, ∀ L, tensorBelow g 0 S.kRow S.matrixRows = some L →
        (L.map fun t => ρ.val (t.entry j)).sum =
          if j / 2 ^ 0 % 2 ^ S.kRow < S.matrixRows then ρ.val (g.entry j) else 0 :=
      fun g hgw L hL => tensorBelow_val ρ g (hd g hgw) _ _ _ L hL j
    exact sum_flatten_mapM _ _ _ weights cut hw hcut
  unfold Means.Says DotEq
  rw [value_two ρ T row omega omegaLay.bits w wLay.bits _ _ hP.two hc hP.hasOmega hP.bitsOmega
    hP.hasW hP.bitsW m, laid_sum ρ omegaLay cut.flatten S.kRow hmem hP.roomOmega,
    laid_sum ρ wLay _ S.kCol hmemW hP.roomW, ht, ρ.zero]
  simp only [hsum]
  rw [cut0_sum S.kRow S.matrixRows hR]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, entry_eq, neg_one]
  rw [← sub_eq_zero (b := ∑ c ∈ Finset.range (2 ^ S.kCol), _), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  have e : ∀ c ∈ Finset.range (2 ^ S.kCol),
      -1 * eqK (psi.map ρ.val) c * m w .main (wLay.index c) =
        -(eqK (psi.map ρ.val) c * m w .main (wLay.index c)) := fun c _ => by ring
  rw [Finset.sum_congr rfl e]

end Desc.K14.Law
