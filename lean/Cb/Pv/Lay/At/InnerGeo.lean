-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/InnerGeo.lean: the places of the panels of a group of layers in the cube of the batched
sumcheck, and the names of the pieces of its two sides.

Main names:
  `wrow`, `wid_eq`, `wid_le`, `nP_lt`, `rows_lt`: a panel's block and its rows lie in the cube.
  `kS`: the number of variables, lamS, closed to unfolding.
  `isVirt`, `cntA`, `cntB`, `IA`, `IB`: the pieces of a panel on each side, and their names.
Limits: sizes alone.


-/
import Cb.Pv.Lay.At.PanPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.At
open Finset
open Inst.Model.FFSeg (Dim Pan pans offP lamS)
open Cb.Pv.Lay.End.Sig (off_inside)

/-! ### The panels' places in the cube -/

section Geo
variable (D : Dim)

/-- The bits of a row's number. -/
def wrow (p : Pan) : ℕ := Nat.clog 2 (p.nr D)

theorem wid_eq (p : Pan) : p.wid D = wrow D p + p.wcol D := rfl

theorem wid_le {p : Pan} (hp : p ∈ pans D) : p.wid D ≤ lamS D := by
  have h := off_inside D hp
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_trans (Nat.le_add_left _ _) h)

/-- The panel's block lies in the cube. -/
theorem nP_lt {p : Pan} (hp : p ∈ pans D) : nP D p + 1 ≤ 2 ^ (lamS D - p.wid D) := by
  have h := off_inside D hp
  rw [← nP_mul D p] at h
  have e : 2 ^ lamS D = 2 ^ (lamS D - p.wid D) * 2 ^ p.wid D := by
    rw [← pow_add, Nat.sub_add_cancel (wid_le D hp)]
  rw [e, ← Nat.succ_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos _)

/-- The panel's rows lie in the cube. -/
theorem rows_lt {p : Pan} (hp : p ∈ pans D) :
    nP D p * 2 ^ wrow D p + p.nr D ≤ 2 ^ (lamS D - p.wcol D) := by
  have h1 := nP_lt D hp
  have h2 : p.nr D ≤ 2 ^ wrow D p := Nat.le_pow_clog (by decide) _
  have hw := wid_le D hp
  have e : lamS D - p.wcol D = (lamS D - p.wid D) + wrow D p := by
    rw [wid_eq] at hw ⊢
    omega
  rw [e, pow_add]
  calc nP D p * 2 ^ wrow D p + p.nr D ≤ nP D p * 2 ^ wrow D p + 2 ^ wrow D p :=
        Nat.add_le_add_left h2 _
    _ = (nP D p + 1) * 2 ^ wrow D p := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ (lamS D - p.wid D) * 2 ^ wrow D p := Nat.mul_le_mul_right _ h1

/-- The number of variables of the batched sumcheck: lamS, closed to unfolding. -/
@[irreducible] def kS : ℕ := lamS D

theorem kS_eq : kS D = lamS D := by
  unfold kS
  rfl

/-- The panels whose first factor is never sent and is no form in the cells. -/
def isVirt : Pan → Bool
  | .D | .Dr _ => true
  | _ => false

/-- The number of pieces of a panel on the first side and on the second. -/
def cntA (p : Pan) : ℕ := if isVirt p then 1 else 0
def cntB (p : Pan) : ℕ := if p.weight then (if p.three then 1 else p.nr D) else 0

/-- A panel with two factors has at most one piece a row. -/
theorem cntB_le {p : Pan} (h3 : ¬ p.three = true) : cntB D p ≤ p.nr D := by
  unfold cntB
  by_cases hw : p.weight = true
  · rw [if_pos hw, if_neg h3]
  · rw [if_neg hw]
    exact Nat.zero_le _

/-- The names of the pieces: the form part, and the panels' pieces. -/
abbrev IA : Type := Unit ⊕ (Σ p : {p : Pan // p ∈ pans D}, Fin (cntA p.1))
abbrev IB : Type := Unit ⊕ (Σ p : {p : Pan // p ∈ pans D}, Fin (cntB D p.1))

end Geo

end Cb.Pv.Lay.At
