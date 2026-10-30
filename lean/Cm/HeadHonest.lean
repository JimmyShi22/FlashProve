-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/HeadHonest.lean: the plain head: the honest cells, also for a request with counted positions
(`Req.rhoC`, Inst/Model/Head/Index.lean); `hon_cells_le` is under `N.HonIn0`.

The honest cells are the head's part of the cells that the honest prover computes (`trace2`,
Cm/Rel2.lean, has them as its head's cells).

Main names:
  `hon np x H y`: the honest cells, from the stream x after the last layer, the output matrix H and
    what the head reads of the request: the cells of the final normalisation; at a covered position
    (`Req.rho`, Inst/Model/Head/Index.lean) the digits of the plain margins, K_2 = mg mod 2^8, mh =
    ⌊mg / 2^8⌋, K_1 = mh if mh < 2^15 and 2^15 + (mh mod 2^15) otherwise, each less its offset; 0 at
    the other positions. They are the "cells without hidden numbers" (`N.honBase`,
    Inst/Model/Head/HonestBase.lean) at the names that the plain head reads, and 0 at all other
    names of hf and hr.
  `hon_cells_le`: under `N.HonIn0` (the final normalisation has `NormPar.OK` and does not halt at
    any position, |H| ≤ 2^12 and every margin at a covered position is at least 0), every cell that
    the plain head reads is at most 128 in absolute value.

Why also with counted positions: the plain margin holds no hidden number, so the computation
serves every request that meets `N.HonIn0`.
The values, their ranges and the three digits of a margin (`N.digits`), the ledger's honest bytes
and the honest rounding are imported from Inst/Model/Head/HonestBase.lean,
Inst/Model/Common/LedgerHonest.lean and Inst/Model/Common/Site.lean.

Terms: lean/GLOSSARY.md.
-/
import Cm.HeadNoWrap
import Inst.Model.Head.HonestBase

set_option autoImplicit false

namespace Cm.Plain

open Inst.Model Inst.Model.Head Finset

section Values
variable (np : NormPar) (x : ℕ → Vec) (H : Mat) (y : Req)

/-- The honest cells of the plain head. -/
def hon : Cells ℤ where
  x := (N.honBase np x H y).x
  hd := (N.honBase np x H y).hd
  hr := fun n i => if n < nHr then (N.honBase np x H y).hr n i else 0
  hf := fun φ i => if φ < nHf then (N.honBase np x H y).hf φ i else 0

theorem hon_hf {φ : ℕ} (h : φ < nHf) (i : ℕ) :
    (hon np x H y).hf φ i = (N.honBase np x H y).hf φ i := if_pos h
theorem hon_hr {n : ℕ} (h : n < nHr) (i : ℕ) :
    (hon np x H y).hr n i = (N.honBase np x H y).hr n i := if_pos h

/-! the arrays of the honest cells are the honest values -/

theorem hon_bl {l j : ℕ} (hj : j < nD) (i : ℕ) : bl (hon np x H y) l j i = N.bX x i l j :=
  N.hon_bl np x H y hj i
theorem hon_xv {j : ℕ} (hj : j < nD) (i : ℕ) : xv (hon np x H y) j i = x i j :=
  N.hon_xv np x H y hj i
theorem hon_nrm {j : ℕ} (hj : j < nD) (i : ℕ) : nrm (hon np x H y) j i = N.outv np x i j :=
  N.hon_nrm np x H y hj i
theorem hon_lg (i v : ℕ) : Head.lg (hon np x H y) H i v = N.lgv np x H i v := N.hon_lg (y := y) i v
theorem hon_nw {j : ℕ} (hj : j < nD) (i : ℕ) : nw (hon np x H y) j i = N.ywv np x i j := by
  rw [← N.hon_nw np x H y hj i, N.nw_eq, N.nw_eq,
    hon_hf _ _ _ _ (by simp only [fNw, nHf, nD] at *; omega),
    hon_hf _ _ _ _ (by simp only [fNw, nHf, nD] at *; omega)]
theorem hon_rn {j : ℕ} (hj : j < nD) (i : ℕ) : rn (hon np x H y) j i = N.rnv np x i j := by
  rw [← N.hon_rn np x H y hj i, N.rn_eq, N.rn_eq,
    hon_hf _ _ _ _ (by simp only [fRn, nHf, nD] at *; omega),
    hon_hf _ _ _ _ (by simp only [fRn, nHf, nD] at *; omega)]
theorem hon_d1 {v : ℕ} (hv : v < nV) (i : ℕ) : d1 (hon np x H y) v i = N.d1v np x H y i v := by
  rw [← N.hon_d1 np x H y hv i, N.d1_eq, N.d1_eq,
    hon_hf _ _ _ _ (by simp only [fD1, nHf, nV] at *; omega),
    hon_hf _ _ _ _ (by simp only [fD1, nHf, nV] at *; omega)]
theorem hon_d2 {v : ℕ} (hv : v < nV) (i : ℕ) : d2 (hon np x H y) v i = N.d2v np x H y i v := by
  rw [← N.hon_d2 np x H y hv i]
  exact hon_hf _ _ _ _ (by simp only [fD2, nHf, nV] at *; omega) i
theorem hon_led {i : ℕ} :
    ∀ n < 99, Dv (hon np x H y) n i = Ledger.hon np nD (N.bX x i) n := fun n hn => by
  rw [← N.hon_led (np := np) (x := x) (H := H) (y := y) n hn]
  unfold Dv
  rw [hon_hr _ _ _ _ hn]
theorem hon_K1 {v : ℕ} (hv : v < nV) (i : ℕ) :
    K1 (hon np x H y) y v i = if y.r ≤ i ∧ i < y.e then N.K1v np x H y i v else 0 := by
  simp only [K1, hon_d1 np x H y hv, N.d1v, Req.rho, Int.cast_id]
  split_ifs <;> ring
theorem hon_K2 {v : ℕ} (hv : v < nV) (i : ℕ) :
    K2 (hon np x H y) y v i = if y.r ≤ i ∧ i < y.e then N.K2v np x H y i v else 0 := by
  simp only [K2, hon_d2 np x H y hv, N.d2v, Req.rho, Int.cast_id]
  split_ifs <;> ring
/-- the plain margin of the honest cells, at every request -/
theorem hon_mg (v i : ℕ) :
    mg (hon np x H y) H y v i = if y.r ≤ i ∧ i < y.e then N.mgv np x H y i v else 0 := by
  unfold mg Req.rho N.mgv
  split_ifs <;> simp [hon_lg]

end Values

section Main
variable {np : NormPar} {x : ℕ → Vec} {H : Mat} {y : Req} (h : N.HonIn0 np x H y)
include h

/-- under `h`, `hi`: every cell that the plain head reads is at most 128 in absolute value -/
theorem hon_cells_le {i : ℕ} (hi : i < nT) :
    (∀ φ < nHf, |(hon np x H y).hf φ i| ≤ 128) ∧ (∀ φ < nFeat .hd, |(hon np x H y).hd φ i| ≤ 128) ∧
    (∀ φ < nHr, |(hon np x H y).hr φ i| ≤ 128) ∧ ∀ φ < nFeat .x, |(hon np x H y).x φ i| ≤ 128 := by
  obtain ⟨a, b, c, d⟩ := N.base_cells_le h hi
  refine ⟨fun φ hφ => ?_, b, fun n hn => ?_, d⟩
  · rw [hon_hf _ _ _ _ hφ]
    exact a φ (lt_of_lt_of_le hφ (by decide))
  · rw [hon_hr _ _ _ _ hn]
    exact c n (lt_of_lt_of_le hn (by decide))

theorem hon_Rz {i : ℕ} (hi : i < nT) : Ledger.R (fun n => Dv (hon np x H y) n i) = N.Rz np x i := by
  rw [N.R_congr (hon_led np x H y), Ledger.hon_R (N.honHyp h hi), N.xOf_bX]
  rfl

end Main

end Cm.Plain
