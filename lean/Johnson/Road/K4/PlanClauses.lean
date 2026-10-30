-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanClauses.lean: THE CLAUSES ON SIZES that the library's records `NormsOk`
(Cb/Pv/Lay/End/LayHEnd.lean) and `GatedOk` (Cb/Pv/Lay/End/LayAll.lean) ask, AT THE NUMBERS OF A
LAYOUT THAT THE PROGRAM's FUNCTION `layout` RETURNS. Statements and proofs. It goes on where
Johnson/Road/K4/PlanSizes.lean ends.

  `LayMore h y`, `layMore_of_base`, `layMore_of_layout`: ten more plain facts on such a layout:
    the two widths are not 0; the padded widths are the powers of two of their bits; a block has
    2^ls features; the widths are whole numbers of blocks; with routed experts an expert's width is
    a power of two, a whole number of blocks, and half the layer's. Five of them (S2, bd, bf, bfe,
    ffe) stand in the record `Laid` too, there for a shape with routed experts.
  `le_clog_of_dvd`: if 2^s divides n, which is not 0, then s is at most the bits of n.
  `norms_sizes`: `NormsOk`'s three clauses hl, hd, hB at s := y.ls, b := y.lPd - y.ls,
    B := hS.d / y.S2; and with them: y.ls ≤ y.lPd, and 2^b = y.Pd / y.S2.
  `gated_sizes`: `GatedOk`'s four clauses h1, hs1, hs2, hfe at sG := y.ls, for a shape with routed
    experts.
  `front_sizes`: seven equations more, for a shape with routed experts and five limbs, as the ports
    of the layers' rows ask them (Johnson/Road/Rows/): the layers of a group and those with
    experts are 2^lL and 2^(lL - 1); the layer's and an expert's numbers of blocks are
    2^(lF - ls) and 2^(lFe - ls); the stream has five limbs; the products' scalars are 7 nNu; the
    norms are nNu.

Premises: the layout is what `layout` returns for a shape hS; the library's sizes D agree with hS
in the nine numbers of `Sized`.

Limits. That K4's text reads its blocks with just these b, s, B and sG is not shown here: it is
a reading of Johnson/Road/FormsKeysIdnL.lean and Johnson/Road/Rows/GatedEnds.lean. The records'
clauses on names and forms (hfm, the good names) are not touched. Equations and bounds between
numbers alone. The script of `layMore_of_base` follows `admitted_of_base`
(Johnson/Road/FormsKeysLaid.lean).
-/
import Johnson.Road.K4.PlanSizes
import Johnson.Road.FormsKeysQK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Shape layout layoutBase layoutLook manyBits)
open Inst.Model.FFSeg (Dim lDd lF lFe)

/-- Ten more plain facts on the numbers of a layout for the shape h. -/
structure LayMore (h : Shape) (y : Lay) : Prop where
  /-- the two widths are not 0 -/
  d0 : h.d ≠ 0
  f0 : h.f ≠ 0
  /-- the padded widths -/
  Pd : y.Pd = 2 ^ y.lPd
  Pf : y.Pf = 2 ^ y.lPf
  /-- a block has 2^ls features -/
  S2 : y.S2 = 2 ^ y.ls
  /-- the widths are whole numbers of blocks -/
  bd : 2 ^ y.ls ∣ h.d
  bf : 2 ^ y.ls ∣ h.f
  /-- with routed experts: an expert's width -/
  bfe : h.p3 = true → 2 ^ y.ls ∣ h.fe
  fePow : h.p3 = true → manyBits h.fe = false
  ffe : h.p3 = true → h.f = 2 * h.fe

/-- The first half of the layout. -/
theorem layMore_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : LayMore h y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e2, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e7, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  -- the test on the shape's words
  have a1 := or_false_split e2
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  have a5 := or_false_split a3.1
  have a6 := or_false_split a5.1
  have d0 : h.d ≠ 0 := by simpa using a6.2
  have f0 : h.f ≠ 0 := by simpa using a5.2
  -- the test on whole blocks
  have b1 := or_false_split e7
  have b2 := or_false_split b1.1
  exact {
    d0 := d0
    f0 := f0
    Pd := rfl
    Pf := rfl
    S2 := rfl
    bd := dvd_of_bne b2.1
    bf := dvd_of_bne b2.2
    bfe := fun hp3 => by
      have b3 := b1.2
      rw [hp3, Bool.true_and] at b3
      exact dvd_of_bne b3
    fePow := fun hp3 => by
      have a4 := a1.2
      rw [hp3, Bool.true_and] at a4
      exact (or_false_split (or_false_split a4).1).1
    ffe := fun hp3 => by
      have a4 := a1.2
      rw [hp3, Bool.true_and] at a4
      simpa using (or_false_split (or_false_split a4).1).2 }

/-- Every layout that the function `layout` returns. -/
theorem layMore_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : LayMore h y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have A := layMore_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact ⟨A.d0, A.f0, A.Pd, A.Pf, A.S2, A.bd, A.bf, A.bfe, A.fePow, A.ffe⟩

/-- If 2^s divides n, which is not 0, then s is at most the bits of n. -/
theorem le_clog_of_dvd {s n : ℕ} (hd : 2 ^ s ∣ n) (h0 : n ≠ 0) : s ≤ Nat.clog 2 n := by
  have h1 : 2 ^ s ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
  have h2 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by decide) _
  exact (Nat.pow_le_pow_iff_right (by decide)).mp (Nat.le_trans h1 h2)

variable {hS : Shape} {pc : List (List String)} {y : Lay} {D : Dim}

/-- **The three clauses on sizes of `NormsOk`** at s := y.ls, b := y.lPd - y.ls, B := hS.d / y.S2,
for a layout that `layout` returns and sizes D that agree with the shape; and with them:
y.ls ≤ y.lPd, and 2^b = y.Pd / y.S2. -/
theorem norms_sizes (hy : layout hS pc = .ok y) (Z : Sized hS D) :
    lDd D = y.lPd - y.ls + y.ls ∧ D.d = hS.d / y.S2 * 2 ^ y.ls ∧
      hS.d / y.S2 ≤ 2 ^ (y.lPd - y.ls) ∧ y.ls ≤ y.lPd ∧ 2 ^ (y.lPd - y.ls) = y.Pd / y.S2 := by
  have L := laySizes_of_layout hy
  have A := layMore_of_layout hy
  have hl : y.lPd = Nat.clog 2 hS.d := by rw [L.lPd, ceilLog2_eq_clog]
  have hls : y.ls ≤ y.lPd := by
    rw [hl]
    exact le_clog_of_dvd A.bd A.d0
  have e : y.ls + (y.lPd - y.ls) = y.lPd := by omega
  have hpow : 2 ^ y.ls * 2 ^ (y.lPd - y.ls) = 2 ^ y.lPd := by rw [← Nat.pow_add, e]
  have hle : hS.d ≤ 2 ^ y.lPd := by
    rw [hl]
    exact Nat.le_pow_clog (by decide) _
  refine ⟨?_, ?_, ?_, hls, ?_⟩
  · show Nat.clog 2 D.P.d = _
    rw [Z.d, ← hl]
    omega
  · show D.P.d = _
    rw [Z.d, A.S2, Nat.div_mul_cancel A.bd]
  · rw [A.S2]
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ y.ls) ?_ (Nat.two_pow_pos _)
    rw [Nat.div_mul_cancel A.bd, Nat.mul_comm, hpow]
    exact hle
  · rw [A.Pd, A.S2, ← hpow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]

/-- **The four clauses on sizes of `GatedOk`** at sG := y.ls, for a layout that `layout` returns for
a shape with routed experts and sizes D that agree with the shape. -/
theorem gated_sizes (hy : layout hS pc = .ok y) (hp3 : hS.p3 = true) (Z : Sized hS D) :
    1 ≤ D.lL ∧ y.ls ≤ lF D ∧ y.ls ≤ lFe D ∧ D.fe = 2 ^ lFe D := by
  have L := laySizes_of_layout hy
  have A := layMore_of_layout hy
  have fe0 : hS.fe ≠ 0 := by
    have h1 := A.ffe hp3
    have h2 := A.f0
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Z.lL]
    exact L.ll
  · show y.ls ≤ Nat.clog 2 D.P.f
    rw [Z.f]
    exact le_clog_of_dvd A.bf A.f0
  · show y.ls ≤ Nat.clog 2 D.P.fe
    rw [Z.fe]
    exact le_clog_of_dvd (A.bfe hp3) fe0
  · show D.P.fe = 2 ^ Nat.clog 2 D.P.fe
    rw [Z.fe, ← ceilLog2_eq_clog]
    exact pow_of_manyBits (A.fePow hp3) fe0

/-- **Seven equations more**, for a layout that `layout` returns for a shape with routed experts and
five limbs, and sizes D that agree with the shape. -/
theorem front_sizes (hy : layout hS pc = .ok y) (hp3 : hS.p3 = true) (hxl : hS.xl = 5)
    (Z : Sized hS D) :
    y.Lam = 2 ^ D.lL ∧ y.h.f / y.S2 = 2 ^ (lF D - y.ls) ∧ y.LamM = 2 ^ (D.lL - 1) ∧
      y.h.fe / y.S2 = 2 ^ (lFe D - y.ls) ∧ y.xb.nl = 5 ∧
      ledNP y.h.xl * y.NI = 7 * D.nNu ∧ y.NI = D.nNu := by
  have L := laySizes_of_layout hy
  have A := layMore_of_layout hy
  obtain ⟨h1, hs1, hs2, hfe⟩ := gated_sizes hy hp3 Z
  have La := (laid_of_layout hy hp3).2
  have efe : hS.fe = 2 ^ lFe D := by
    rw [← Z.fe]
    exact hfe
  have ef : hS.f = 2 ^ (lFe D + 1) := by rw [A.ffe hp3, efe, Nat.pow_succ, Nat.mul_comm]
  have elF : lF D = lFe D + 1 := by
    show Nat.clog 2 D.P.f = _
    rw [Z.f, ef]
    exact Nat.clog_pow 2 _ (by decide)
  have eNI : y.NI = D.nNu := by rw [L.NI, nNu_tie Z]
  have e7 : ledNP 5 = 7 := rfl
  refine ⟨by rw [L.Lam, Z.lL], ?_, ?_, ?_, ?_, ?_, eNI⟩
  · rw [L.shape, A.S2, ef, elF, Nat.pow_div (Nat.le_succ_of_le hs2) (by decide)]
  · rw [L.LamM, Z.lL]
    obtain ⟨k, hk⟩ : ∃ k, hS.ll = k + 1 := ⟨hS.ll - 1, by have := L.ll; omega⟩
    rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel]
  · rw [L.shape, A.S2, efe, Nat.pow_div hs2 (by decide)]
  · rw [La.xb, L.shape]
    exact hxl
  · rw [L.shape, hxl, eNI, e7]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.front_sizes
#print axioms OnBytes.Road.K4.layMore_of_layout
#print axioms OnBytes.Road.K4.norms_sizes
#print axioms OnBytes.Road.K4.gated_sizes
