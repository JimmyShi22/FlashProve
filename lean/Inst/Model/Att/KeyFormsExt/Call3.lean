-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/Call3.lean: call 3 of an attention segment: the key form at the rule
values is the extension of the call's vector of looked-up values.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean). Call 3 of the comments is 2 in `Fin 4`; its
families are 3W, over (χ | g | i | n), and 3X, over (g | i).
Main names:
  `linW`, `linX`: the linear algebra of the two families, by induction on the number of pieces.
  `pieceW`, `pieceX`: the extension of a piece of 3W at u^W, and of a piece of 3X at u^X.
  `kf2`: `KF D C p (rv D C p t) 2 = Blocks.ext (C.a 2) (keyVec D tb t 2) (C.zC 2 p.z)`, for every
    content t of the cells and all challenges p.
Limits: `kf2` stands under `C.OK D` and D.lW ≤ C.a 2. Coordinate 0 of a point belongs to the most
significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.SumZO

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

/-- the linear algebra of family 3W -/
theorem linW (n : ℕ) (W A d O h h' : ℕ → E) (χ : E) :
    (1 - χ) * ((2 * ∑ b ∈ range n, W b * A b + ∑ b ∈ range n, W b * d b - 2 * ∑ b ∈ range n, W b *
        O b) -
        2 ^ 16 * (∑ b ∈ range n, W b * h b + 128 * ∑ b ∈ range n, W b)) +
      χ * (2 * ∑ b ∈ range n, W b * d b - ∑ b ∈ range n, W b -
        (2 * ∑ b ∈ range n, W b * A b + ∑ b ∈ range n, W b * d b - 2 * ∑ b ∈ range n, W b * O b) -
        2 ^ 16 * (∑ b ∈ range n, W b * h' b + 128 * ∑ b ∈ range n, W b)) =
    ∑ b ∈ range n, W b * ((1 - χ) * ((2 * A b + d b - 2 * O b) - 2 ^ 16 * (h b + 128)) +
      χ * (2 * d b - 1 - (2 * A b + d b - 2 * O b) - 2 ^ 16 * (h' b + 128))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linear_combination ih

/-- the linear algebra of family 3X -/
theorem linX (n K : ℕ) (W : ℕ → E) (r : ℕ → ℕ → E) (c I : E) :
    c * ((∑ b ∈ range n, W b) * I - ∑ k ∈ range K, 2 ^ k * ∑ b ∈ range n, W b * r k b) =
      ∑ b ∈ range n, W b * (c * (I - ∑ k ∈ range K, 2 ^ k * r k b)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ, mul_add, Finset.sum_add_distrib]
    have e : ∑ k ∈ range K, (2 : E) ^ k * (W n * r k n) = W n * ∑ k ∈ range K, 2 ^ k * r k n := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    linear_combination ih

variable (D : AttSeg.Dim) (C : AttSeg.Calls) [scl : Scl] (tb : Tables) (p : AttSeg.Pub E)
    (t : AttSeg.Raw → E)

omit scl in
/-- a piece of 3W -/
theorem pieceW (b : ℕ) :
    Blocks.ext D.lW (fun y => AttSeg.key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG)
        (y / D.ch % D.T) (y % D.ch))
        (AttSeg.uW D C p.z) =
      (1 - AttSeg.zChi D C p.z) * ((2 * AttSeg.atY D C p (AttSeg.AC D t b) +
          AttSeg.rd2 D (AttSeg.yg D C p.z) (AttSeg.eqT D (AttSeg.yi D C p.z)) (AttSeg.denV t b) -
              2 * DO D C p t b) -
          2 ^ 16 * (AttSeg.atY D C p (fun g i n => t (.qh b g i n)) + 128)) +
        AttSeg.zChi D C p.z * (2 * AttSeg.rd2 D (AttSeg.yg D C p.z)
            (AttSeg.eqT D (AttSeg.yi D C p.z)) (AttSeg.denV t b) - 1 -
          (2 * AttSeg.atY D C p (AttSeg.AC D t b) +
            AttSeg.rd2 D (AttSeg.yg D C p.z) (AttSeg.eqT D (AttSeg.yi D C p.z)) (AttSeg.denV t b) -
                2 * DO D C p t b) -
          2 ^ 16 * (AttSeg.atY D C p (fun g i n => t (.qh' b g i n)) + 128)) := by
  have h4W : D.lW = 1 + D.l4 := by unfold AttSeg.Dim.lW AttSeg.Dim.l4; omega
  rw [h4W, ext_top]
  have lo : Blocks.ext D.l4 (fun y =>
      AttSeg.key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG) (y / D.ch % D.T)
      (y % D.ch))
      (AttSeg.sh (AttSeg.uW D C p.z) 1) =
      AttSeg.atY D C p (fun g i n => AttSeg.RE D t b g i n - 2 ^ 16 * (t (.qh b g i n) + 128)) := by
    unfold AttSeg.atY
    refine Blocks.ext_congr (fun y hy => ?_) _
    have h := gi_lt D hy
    rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
    unfold AttSeg.key3W AttSeg.qhV
    rw [if_pos rfl]
  have hi : Blocks.ext D.l4 (fun y =>
      AttSeg.key3W D t ((2 ^ D.l4 + y) / D.ch / D.T / D.nG) b ((2 ^ D.l4 + y) / D.ch / D.T % D.nG)
        ((2 ^ D.l4 + y) / D.ch % D.T) ((2 ^ D.l4 + y) % D.ch)) (AttSeg.sh (AttSeg.uW D C p.z) 1) =
      AttSeg.atY D C p (fun g i n => (2 * AttSeg.denV t b g i - 1 - AttSeg.RE D t b g i n) -
          2 ^ 16 * (t (.qh' b g i n) + 128)) := by
    unfold AttSeg.atY
    refine Blocks.ext_congr (fun y hy => ?_) _
    have h := gi_lt D hy
    have pG : 0 < D.nG := Nat.two_pow_pos _
    rw [hi_ch, hi_T, hi_mod_T, hi_mod_ch, Nat.add_div_left _ pG, Nat.div_eq_of_lt h,
        Nat.add_mod_left, Nat.mod_eq_of_lt h]
    unfold AttSeg.key3W AttSeg.qhV'
    rw [if_neg (by omega)]
  rw [lo, hi]
  simp only [atY_sub, atY_add, atY_smul, atY_const]
  rw [atY_RE, atY_gi D C p (AttSeg.denV t b)]
  rfl

omit scl in
/-- a piece of 3X -/
theorem pieceX (b : ℕ) :
    Blocks.ext D.lX (fun y => AttSeg.key3X D t b (y / D.T) (y % D.T)) (AttSeg.uX D C p.z) =
      2 ^ (16 - D.lT) * (AttSeg.idP D.lT (AttSeg.xi D C p.z) -
        ∑ k ∈ range D.lT, 2 ^ k * AttSeg.rd2 D (AttSeg.xg D C p.z)
            (AttSeg.eqT D (AttSeg.xi D C p.z)) (AttSeg.ibV t k b)) := by
  show Blocks.ext (D.lg + D.lT) (fun y => 2 ^ (16 - D.lT) * (((y % D.T : ℕ) : E) -
    ∑ k ∈ range D.lT, 2 ^ k * AttSeg.ibV t k b (y / D.T) (y % D.T))) (AttSeg.uX D C p.z) = _
  rw [Blocks.ext_smul, Blocks.ext_sub, Blocks.ext_sum]
  have h1 : Blocks.ext (D.lg + D.lT) (fun y => ((y % D.T : ℕ) : E)) (AttSeg.uX D C p.z) =
      AttSeg.idP D.lT (AttSeg.xi D C p.z) := by
    rw [D.T_eq, ext_drop_first D.lg D.lT (fun i => (i : E)), ext_id]
    rfl
  have h2 : ∀ k, Blocks.ext (D.lg + D.lT) (fun y => 2 ^ k * AttSeg.ibV t k b (y / D.T) (y % D.T))
      (AttSeg.uX D C p.z) =
      2 ^ k * AttSeg.rd2 D (AttSeg.xg D C p.z) (AttSeg.eqT D (AttSeg.xi D C p.z)) (AttSeg.ibV t k b)
          := by
    intro k
    rw [Blocks.ext_smul, ext_rd2]
    have : AttSeg.xg D C p.z = AttSeg.uX D C p.z := sh_zero _
    rw [this]
    rfl
  rw [h1]
  simp only [h2]

/-- Call 3 of the comments (2 in `Fin 4`). -/
theorem kf2 (hC : C.OK D) (hW : D.lW ≤ C.a 2) :
    AttSeg.KF D C p (AttSeg.rv D C p t) 2 =
        Blocks.ext (C.a 2) (AttSeg.keyVec D tb t 2) (C.zC 2 p.z) := by
  have hl : D.lX ≤ D.lW := by unfold AttSeg.Dim.lX AttSeg.Dim.lW; omega
  have hv : AttSeg.keyVec D tb t 2 = AttSeg.twoFam D.nb D.lW D.lX
      (fun b y => AttSeg.key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG)
          (y / D.ch % D.T) (y % D.ch))
      (fun b y => AttSeg.key3X D t b (y / D.T) (y % D.T)) 0 := by
    have h0 : AttSeg.keyVec D tb t 2 = AttSeg.twoFam D.nb D.lW D.lX
        (fun b y => AttSeg.key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG)
            (y / D.ch % D.T) (y % D.ch))
        (fun b y => AttSeg.key3X D t b (y / D.T) (y % D.T)) (((AttSeg.lut D tb 2).pad : ℤ) : E) :=
            rfl
    have hp : (((AttSeg.lut D tb 2).pad : ℤ) : E) = 0 := by
      show (((tau3).pad : ℤ) : E) = 0
      simp [tau3, R16]
    rw [h0, hp]
  rw [hv, twoFam_ext (C.a 2) D.nb D.lW D.lX hl hW (hC.fits 2), zero_mul, add_zero]
  have pW := pieceW D C p t
  have pX := pieceX D C p t
  have eW : AttSeg.sh (C.zC 2 p.z) (C.a 2 - D.lW) = AttSeg.uW D C p.z := rfl
  have eX : AttSeg.sh (C.zC 2 p.z) (C.a 2 - D.lX) = AttSeg.uX D C p.z := rfl
  rw [eW, eX]
  simp only [pW, pX]
  have hw1 : ∀ b, Blocks.eqN (C.a 2 - D.lW) 0 (C.zC 2 p.z) (0 + b) = AttSeg.wp D C p.z .w3 b :=
      fun _ => rfl
  have hw2 : ∀ b, Blocks.eqN (C.a 2 - D.lX) 0 (C.zC 2 p.z) (D.nb * 2 ^ (D.lW - D.lX) + b) =
      AttSeg.wp D C p.z .x3 b := fun _ => rfl
  simp only [hw1, hw2]
  rw [← linW, ← linX]
  show (1 - AttSeg.zChi D C p.z) *
      (AttSeg.REM (AttSeg.rv D C p t) - 2 ^ 16 *
      (AttSeg.rv D C p t .rh + 128 * AttSeg.LL D C p.z .w3)) +
      AttSeg.zChi D C p.z * (2 * AttSeg.rv D C p t .zc - AttSeg.LL D C p.z .w3 -
          AttSeg.REM (AttSeg.rv D C p t) -
        2 ^ 16 * (AttSeg.rv D C p t .rh' + 128 * AttSeg.LL D C p.z .w3)) +
      2 ^ (16 - D.lT) * (AttSeg.LL D C p.z .x3 * AttSeg.idP D.lT (AttSeg.xi D C p.z) -
        ∑ k ∈ range D.lT, 2 ^ k * AttSeg.rv D C p t (.ib k)) = _
  unfold AttSeg.REM
  have hzo : AttSeg.rv D C p t .zo = ∑ b ∈ range D.nb, AttSeg.wp D C p.z .w3 b * DO D C p t b :=
      zo_eq D C p t
  rw [hzo]
  rfl

end Inst.Model.AttSeg.KeyFormsExt
