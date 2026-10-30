-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WindowLawProofs.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: proofs of
four statements of Johnson/Desc/K8/Honest/WindowLaw.lean: what the program `leaves` finds at every
sequence; that every sequence of the right length with entries -1, 0, 1 is that of a typed matrix;
that a combination, computed on the sequence of a typed matrix, is the library's; and that, run on
such a sequence, the program finds a combination outside its window just if the library's window
event holds.

  `fitsRows_sizeOfPar`   `FitsRows` has a member at every place
  `foldl_range_add`   a sum that is gathered from the left over the numbers below n
  `inWindow_iff`      the window's test, as two inequalities
  `leaves_isSome`     what the program's three searches find
  `cellsSmall_iff`    the test on the cells, cell by cell
  `leaves_none_iff`   `Spec.leaves_none_iff`
  `coefOf`, `coefOf_val`, `listOf_onto`   a coefficient with a given value; `Spec.listOf_onto`
  `comb_eq`           `Spec.comb_eq`
  `leaves_iff`        `Spec.leaves_iff`
Lemmas; none of the library's goals. Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.WindowLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open OnBytes.Model (lbz)

/-- `FitsRows` has a member at every place. -/
theorem fitsRows_sizeOfPar (p : Par) : FitsRows p (sizeOfPar p) :=
  ⟨⟨rfl, fun _ _ => rfl, rfl⟩, fun _ _ => rfl⟩

/-- A sum that is gathered from the left over the numbers below n. -/
theorem foldl_range_add (n : ℕ) (f : ℕ → ℤ) :
    (List.range n).foldl (fun z c => z + f c) 0 = ∑ c : Fin n, f c.val := by
  rw [Fin.sum_univ_eq_sum_range (fun c => f c) n]
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

/-- The window's test, as two inequalities. -/
theorem inWindow_iff (z : ℤ) :
    inWindow z = true ↔ -((2 : ℤ) ^ lbz) ≤ z ∧ z < (2 : ℤ) ^ lbz := by
  unfold inWindow
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

/-- What the program's three searches find. -/
theorem leaves_isSome (p : Par) (cell : CellsAt) (d : Array Int) :
    (leaves p cell d).isSome = true ↔
      ∃ mu, mu < p.ks.length ∧ ∃ i, i < p.ms.getD mu 0 ∧ ∃ u, u < p.tau ∧
        inWindow (comb p cell d mu i u) = false := by
  unfold leaves
  simp only [List.findSome?_isSome_iff, List.mem_range]
  constructor
  · rintro ⟨mu, hmu, i, hi, u, hu, h⟩
    refine ⟨mu, hmu, i, hi, u, hu, ?_⟩
    cases hw : inWindow (comb p cell d mu i u) with
    | false => rfl
    | true => simp [hw] at h
  · rintro ⟨mu, hmu, i, hi, u, hu, h⟩
    exact ⟨mu, hmu, i, hi, u, hu, by simp [h]⟩

/-- The test on the cells, cell by cell. -/
theorem cellsSmall_iff (p : Par) (cell : CellsAt) :
    cellsSmall p cell = true ↔
      ∀ mu, mu < p.ks.length → ∀ i, i < p.ms.getD mu 0 → ∀ c, c < p.ks.getD mu 0 →
        |cell mu i c| ≤ 128 := by
  unfold cellsSmall
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h mu hmu i hi c hc
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h mu hmu i hi c hc
  · intro h mu hmu i hi c hc
    have h1 := h mu hmu i hi c hc
    rw [Int.abs_eq_natAbs] at h1
    exact_mod_cast h1

theorem leaves_none_iff : Spec.leaves_none_iff := by
  intro p cell d
  constructor
  · intro h mu hmu i hi u hu
    cases hw : inWindow (comb p cell d mu i u) with
    | true => rfl
    | false =>
      have h1 := (leaves_isSome p cell d).2 ⟨mu, hmu, i, hi, u, hu, hw⟩
      rw [h] at h1
      exact Bool.noConfusion h1
  · intro h
    cases hl : leaves p cell d with
    | none => rfl
    | some x =>
      obtain ⟨mu, hmu, i, hi, u, hu, hw⟩ := (leaves_isSome p cell d).1 (by rw [hl]; rfl)
      rw [h mu hmu i hi u hu] at hw
      exact Bool.noConfusion hw

/-- A coefficient with the value t, for t among -1, 0, 1. -/
def coefOf (t : ℤ) : Prob.Coef := if t = 0 then (false, false) else (true, decide (t = -1))

theorem coefOf_val (t : ℤ) (h : t = -1 ∨ t = 0 ∨ t = 1) : (coefOf t).val = t := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem listOf_onto : Spec.listOf_onto := by
  intro s l hl hv
  refine ⟨(flatPort s).symm fun j => coefOf (l.getD j.val 0), ?_⟩
  apply Array.ext
  · simp [listOf, hl]
  · intro i h1 h2
    have hi : i < l.length := by simpa using h1
    simp only [listOf, Array.getElem_ofFn, Equiv.apply_symm_apply, List.getElem_toArray]
    rw [coefOf_val _ (hv _ (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)),
      List.getD_eq_getElem _ _ hi]

theorem comb_eq : Spec.comb_eq := by
  intro p s cell β μ i u h
  have hμ : μ.val < p.ks.length := h.fits.nm ▸ μ.isLt
  have hk : p.ks.getD μ.val 0 = s.k μ.val := (h.fits.k μ.val hμ).symm
  unfold comb Prob.comb
  rw [hk, foldl_range_add]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold entry
  rw [firstColumns_get h.fits μ, ← h.fits.tau, listOf_get β μ c u]
  rfl

theorem leaves_iff : Spec.leaves_iff := by
  intro p s cell β h
  rw [leaves_isSome]
  unfold winAt Prob.Win
  constructor
  · rintro ⟨mu, hmu, i, hi, u, hu, hw⟩
    have hmu' : mu < s.NM := h.fits.nm.symm ▸ hmu
    have hi' : i < s.m mu := by rw [h.m mu hmu]; exact hi
    have hu' : u < s.tau := by rw [h.fits.tau]; exact hu
    refine ⟨⟨⟨mu, hmu'⟩, ⟨i, hi'⟩, ⟨u, hu'⟩⟩, fun hin => ?_⟩
    have e := comb_eq p s cell β ⟨mu, hmu'⟩ ⟨i, hi'⟩ ⟨u, hu'⟩ h
    have hin' : -((2 : ℤ) ^ lbz) ≤ comb p cell (listOf β) mu i u ∧
        comb p cell (listOf β) mu i u < (2 : ℤ) ^ lbz := by
      rw [show comb p cell (listOf β) mu i u = _ from e]
      exact hin
    rw [(inWindow_iff _).2 hin'] at hw
    exact Bool.noConfusion hw
  · rintro ⟨⟨μ, i, u⟩, hx⟩
    have hμ : μ.val < p.ks.length := h.fits.nm ▸ μ.isLt
    refine ⟨μ.val, hμ, i.val, by rw [← h.m μ.val hμ]; exact i.isLt, u.val,
      by rw [← h.fits.tau]; exact u.isLt, ?_⟩
    cases hw : inWindow (comb p cell (listOf β) μ.val i.val u.val) with
    | false => rfl
    | true =>
      refine absurd ?_ hx
      have h2 := (inWindow_iff _).1 hw
      rw [comb_eq p s cell β μ i u h] at h2
      exact h2

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fitsRows_sizeOfPar
#print axioms VerifiableInference.Desc.First.K8.Honest.cellsSmall_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.leaves_none_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.listOf_onto
#print axioms VerifiableInference.Desc.First.K8.Honest.comb_eq
#print axioms VerifiableInference.Desc.First.K8.Honest.leaves_iff
