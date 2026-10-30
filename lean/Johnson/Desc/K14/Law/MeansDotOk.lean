-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/MeansDotOk.lean: what the constraint (Dot) of the linear claim's second part
says of words, for row weights that may have a written-out factor.

Johnson/Desc/K14/Law/MeansDot.lean shows it under the premise that no row weight has a written-out
factor. The program's own maker of a pending row lays such a factor for every aligned block of more
than one row, so that premise is not met there. Here the premise is that each row weight is a
well-formed vector (Tensor.ok).
Main names: DotMeansOk, dotMeansOk, dotSaysOk.

What is not claimed. That the row weights of a run are well-formed is a premise. Nothing on which
group the constraint is laid on, on (Eval), or on soundness.

-/
import Johnson.Desc.K14.Law.LayDense
import Johnson.Desc.K14.Law.PlacedDot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- **MEANS**, for (Dot), for well-formed row weights, as a proposition. -/
def DotMeansOk : Prop :=
  ∀ (T : Statement) (S : LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : Row),
    linDotRow S weights psi omega omegaLay w wLay = some row →
    (∀ g ∈ weights, g.ok = true) → PlacedDot T S omega omegaLay w wLay → ∀ m : Words K,
      (Means.Says ρ T row m ↔
        DotEq S.matrixRows S.kCol (fun y => (weights.map fun g => ρ.val (g.entry y)).sum)
          (fun y => m omega .main (omegaLay.index y)) (psi.map ρ.val)
          (fun c => m w .main (wLay.index c)))

/-- **MEANS**, for (Dot), for well-formed row weights. -/
theorem dotMeansOk : DotMeansOk ρ := by
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
  have hmem : ∀ t ∈ cut.flatten, (∀ d ∈ t.denseVars, d < t.vars) ∧ t.vars = S.kRow := by
    intro t ht
    obtain ⟨L, hL, htL⟩ := List.mem_flatten.1 ht
    obtain ⟨g, hgw, hgL⟩ := mem_mapM_back _ _ _ hcut L hL
    obtain ⟨e1, e2⟩ := tensorBelow_memG g _ _ _ _ hgL t htL
    refine ⟨fun d hdd => ?_, e2.trans (hvars g hgw)⟩
    rw [e2]
    exact (dense_of_ok g (hd g hgw)).1 d (by rwa [e1] at hdd)
  have hvW : (Tensor.eq psi (negE oneE)).vars = S.kCol := by
    simp only [Tensor.eq, Tensor.vars, List.length_map, hpsi]
  have hmemW : ∀ t ∈ [Tensor.eq psi (negE oneE)],
      (∀ d ∈ t.denseVars, d < t.vars) ∧ t.vars = S.kCol := by
    intro t ht
    rw [List.mem_singleton] at ht
    subst ht
    exact ⟨fun d hdd => absurd hdd (List.not_mem_nil), hvW⟩
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
      fun g hgw L hL => tensorBelow_valG ρ g (dense_of_ok g (hd g hgw)).2 _ _ _ L hL j
    exact sum_flatten_mapM _ _ _ weights cut hw hcut
  unfold Means.Says DotEq
  rw [value_two ρ T row omega omegaLay.bits w wLay.bits _ _ hP.two hc hP.hasOmega hP.bitsOmega
    hP.hasW hP.bitsW m, laid_sumG ρ omegaLay cut.flatten S.kRow hmem hP.roomOmega,
    laid_sumG ρ wLay _ S.kCol hmemW hP.roomW, ht, ρ.zero]
  simp only [hsum]
  rw [cut0_sum S.kRow S.matrixRows hR]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, entry_eq, neg_one]
  rw [← sub_eq_zero (b := ∑ c ∈ Finset.range (2 ^ S.kCol), _), sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  have e : ∀ c ∈ Finset.range (2 ^ S.kCol),
      -1 * eqK (psi.map ρ.val) c * m w .main (wLay.index c) =
        -(eqK (psi.map ρ.val) c * m w .main (wLay.index c)) := fun c _ => by ring
  rw [Finset.sum_congr rfl e]

/-- **What (Dot) means where it lies among constraints that hold of words**, for well-formed row
weights. -/
theorem dotSaysOk (T : Statement) (codes : Codes) (S : LinShape) (weights : List Tensor)
    (psi : List E) (omega w : Nat) (dot : Row) (rows : List Row) (m : Words K)
    (hrow : linDotRow S weights psi omega (linLayOmega codes S) w (linLayW codes S) = some dot)
    (hd : ∀ g ∈ weights, g.ok = true) (hmem : dot ∈ rows)
    (hs : Means.AllSay ρ T rows m) (hSeat : SeatedDot T codes S omega w)
    (hok : linOk codes S = true) :
    DotEq S.matrixRows S.kCol (fun y => (weights.map fun g => ρ.val (g.entry y)).sum)
      (fun y => m omega .main ((linLayOmega codes S).index y)) (psi.map ρ.val)
      (fun c => m w .main ((linLayW codes S).index c)) :=
  (dotMeansOk ρ T S weights psi omega _ w _ dot hrow hd (placedDot_of_seated hSeat hok) m).1
    (hs dot hmem)

end Desc.K14.Law
