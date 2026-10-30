-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/Calls14.lean: calls 1 and 4 of an attention segment: the key form at the
rule values is the extension of the call's vector of looked-up values.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean). The calls 1 to 4 of the comments are 0 to 3
in `Fin 4`, as in Inst/Model/Att/KeyForms.lean.
Main names:
  `inn_tail`: the inner point of a family (`inn`, Inst/Model/Att/Points.lean) is a tail of z_in, if
    a piece of the family is no longer than a tree.
  `twoFam_zero`: a vector of one family, 0 elsewhere, is a block of pieces. `lin3`: three weighted
    sums and the sum of the weights as one weighted sum.
  `kf3`, `kf0`: `KF D C p (rv D C p t) c = Blocks.ext (C.a c) (keyVec D tb t c) (C.zC c p.z)` for c
    = 3 and c = 0, for every content t of the cells and all challenges p.
Limits: `kf0` stands under `C.OK D` and D.lM ≤ C.a 0; `kf3` under `C.OK D` and D.lW ≤ C.Dk, from
which the inner point of family 4 is (y_g | y_i | y_n). Coordinate 0 of a point belongs to the most
significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls)

omit [Field E] in
/-- The inner point of a family is a tail of z_in, if a piece is no longer than a tree. -/
theorem inn_tail (z : ℕ → E) (u : AttSeg.Fam) (hl : u.l D ≤ C.Dk) (ha : C.Dk ≤ C.a u.call) (s : ℕ) :
    AttSeg.inn D C z u s = z (C.Dk - u.l D + s) := by
  unfold AttSeg.inn AttSeg.sh AttSeg.Calls.zC AttSeg.Calls.e
  rw [if_neg (by omega)]
  congr 1
  omega

/-- a vector of one family, 0 elsewhere -/
theorem twoFam_zero (nb l l' : ℕ) (f : ℕ → ℕ → E) :
    AttSeg.twoFam nb l l' f (fun _ _ => 0) 0 = blk l 0 nb f := by
  funext X
  have p1 : 0 < 2 ^ l := Nat.two_pow_pos l
  unfold AttSeg.twoFam blk
  by_cases h1 : X < nb * 2 ^ l
  · rw [if_pos h1, if_pos ⟨Nat.zero_le _, by
    rw [Nat.zero_add]; exact (Nat.div_lt_iff_lt_mul p1).2 h1⟩, Nat.sub_zero]
  · have c1 : ¬ (0 ≤ X / 2 ^ l ∧ X / 2 ^ l < 0 + nb) := fun h => by
      have := h.2
      rw [Nat.zero_add] at this
      exact h1 ((Nat.div_lt_iff_lt_mul p1).1 this)
    rw [if_neg h1, if_neg c1]
    split <;> rfl

/-- three weighted sums and the weights' sum, as one weighted sum -/
theorem lin3 (n : ℕ) (w e0 e1 e2 : ℕ → E) :
    (∑ b ∈ range n, w b * e0 b + 128 * ∑ b ∈ range n, w b) + 2 ^ 20 *
        (∑ b ∈ range n, w b * e1 b + 128 * ∑ b ∈ range n, w b) +
        2 ^ 40 * ∑ b ∈ range n, w b * e2 b =
      ∑ b ∈ range n, w b * ((e0 b + 128) + 2 ^ 20 * (e1 b + 128) + 2 ^ 40 * e2 b) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

variable [scl : Scl] (tb : Tables) (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

/-- Call 4 of the comments (3 in `Fin 4`). -/
theorem kf3 (hC : C.OK D) (hW : D.lW ≤ C.Dk) :
    AttSeg.KF D C p (AttSeg.rv D C p t) 3 =
        Blocks.ext (C.a 3) (AttSeg.keyVec D tb t 3) (C.zC 3 p.z) := by
  have hDk : C.Dk ≤ C.a 3 := hC.le 3
  have h4W : D.lW = 1 + D.l4 := by unfold AttSeg.Dim.lW AttSeg.Dim.l4; omega
  have h4 : D.l4 ≤ C.a 3 := by omega
  have e1 : C.a 3 - D.l4 + D.l4 = C.a 3 := Nat.sub_add_cancel h4
  have fit : 0 + D.nb ≤ 2 ^ (C.a 3 - D.l4) := by
    have h0 : D.nb * 2 ^ D.l4 ≤ 2 ^ C.a 3 := hC.fits 3
    have h : D.nb * 2 ^ D.l4 ≤ 2 ^ (C.a 3 - D.l4) * 2 ^ D.l4 := by rw [← pow_add, e1]; exact h0
    rw [Nat.zero_add]
    exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos _)
  -- the vector
  have hv : AttSeg.keyVec D tb t 3 =
      blk D.l4 0 D.nb fun b y => AttSeg.key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch) := by
    have h0 : AttSeg.keyVec D tb t 3 = AttSeg.twoFam D.nb D.l4 0
        (fun b y => AttSeg.key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
        (fun _ _ => (((AttSeg.lut D tb 3).pad : ℤ) : E)) (((AttSeg.lut D tb 3).pad : ℤ) : E) := rfl
    rw [h0]
    have hp : (((AttSeg.lut D tb 3).pad : ℤ) : E) = 0 := by
      show (((tau4).pad : ℤ) : E) = 0
      simp [tau4]
    rw [hp]
    exact twoFam_zero _ _ _ _
  have B := blk_ext (C.a 3 - D.l4) D.l4 0 D.nb fit
    (fun b y => AttSeg.key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch)) (C.zC 3 p.z)
  rw [e1] at B
  rw [hv, B]
  -- the two points agree on the l4 coordinates that are read
  have hpt : ∀ s < D.l4, AttSeg.sh (C.zC 3 p.z) (C.a 3 - D.l4) s =
      AttSeg.sh (AttSeg.uW D C p.z) 1 s := by
    intro s _
    have a1 := inn_tail D C p.z .f4 (show D.l4 ≤ C.Dk by omega) hDk s
    have a2 := inn_tail D C p.z .w3 hW (hC.le 2) (1 + s)
    have b1 : AttSeg.sh (C.zC 3 p.z) (C.a 3 - D.l4) s = AttSeg.inn D C p.z .f4 s := rfl
    have b2 : AttSeg.sh (AttSeg.uW D C p.z) 1 s = AttSeg.inn D C p.z .w3 (1 + s) := rfl
    rw [b1, b2, a1, a2]
    show p.z (C.Dk - D.l4 + s) = p.z (C.Dk - D.lW + (1 + s))
    congr 1
    omega
  -- a piece's extension, in the rule values' terms
  have piece : ∀ b, Blocks.ext D.l4
      (fun y => AttSeg.key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
        (AttSeg.sh (C.zC 3 p.z) (C.a 3 - D.l4)) =
      (AttSeg.atY D C p (fun g i n => t (.qh b g i n)) + 128) + 2 ^ 20 *
          (AttSeg.atY D C p (fun g i n => t (.qh' b g i n)) + 128) := by
    intro b
    rw [Blocks.ext_congr_point hpt]
    unfold AttSeg.atY AttSeg.key4 AttSeg.qhV AttSeg.qhV'
    rw [Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_add, Blocks.ext_const]
  simp only [piece]
  show (AttSeg.rv D C p t .rg + 128 * AttSeg.LL D C p.z .f4) + 2 ^ 20 *
      (AttSeg.rv D C p t .rg' + 128 * AttSeg.LL D C p.z .f4) = _
  unfold AttSeg.rv AttSeg.LL
  have hw : ∀ b, Blocks.eqN (C.a 3 - D.l4) 0 (C.zC 3 p.z) (0 + b) = AttSeg.wp D C p.z .f4 b :=
      fun _ => rfl
  simp only [hw, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Call 1 of the comments (0 in `Fin 4`). -/
theorem kf0 (hC : C.OK D) (hM : D.lM ≤ C.a 0) :
    AttSeg.KF D C p (AttSeg.rv D C p t) 0 =
        Blocks.ext (C.a 0) (AttSeg.keyVec D tb t 0) (C.zC 0 p.z) := by
  have hl : D.lD ≤ D.lM := by unfold AttSeg.Dim.lD AttSeg.Dim.lM; omega
  have hv : AttSeg.keyVec D tb t 0 =
      AttSeg.twoFam D.nb D.lM D.lD (AttSeg.key1 t .M) (AttSeg.key1 t .D) 0 := by
    have h0 : AttSeg.keyVec D tb t 0 =
        AttSeg.twoFam D.nb D.lM D.lD (AttSeg.key1 t .M) (AttSeg.key1 t .D)
        (((AttSeg.lut D tb 0).pad : ℤ) : E) := rfl
    rw [h0]
    have hp : (((AttSeg.lut D tb 0).pad : ℤ) : E) = 0 := by
      show (((tau1 D.sh).pad : ℤ) : E) = 0
      simp [tau1]
    rw [hp]
  rw [hv, twoFam_ext (C.a 0) D.nb D.lM D.lD hl hM (hC.fits 0), zero_mul, add_zero]
  have piece : ∀ (ρ : AttSeg.Reg) (l : ℕ) (q : ℕ → E) (b : ℕ), Blocks.ext l (AttSeg.key1 t ρ b) q =
      (Blocks.ext l (fun x => t (.c ρ 0 b x)) q + 128) + 2 ^ 20 *
          (Blocks.ext l (fun x => t (.c ρ 1 b x)) q + 128) +
        2 ^ 40 * Blocks.ext l (fun x => t (.c ρ 2 b x)) q := by
    intro ρ l q b
    show Blocks.ext l (fun x => AttSeg.key1 t ρ b x) q = _
    unfold AttSeg.key1 AttSeg.r0 AttSeg.r1 AttSeg.flV
    rw [Blocks.ext_add, Blocks.ext_add, Blocks.ext_add, Blocks.ext_smul, Blocks.ext_smul,
        Blocks.ext_add, Blocks.ext_const]
  simp only [piece]
  show ∑ u ∈ ({.m1, .d1} : Finset AttSeg.Fam),
      ((AttSeg.rv D C p t (.cell u 0) + 128 * AttSeg.LL D C p.z u) +
      2 ^ 20 * (AttSeg.rv D C p t (.cell u 1) + 128 * AttSeg.LL D C p.z u) + 2 ^ 40 *
          AttSeg.rv D C p t (.cell u 2)) = _
  rw [Finset.sum_pair (by decide)]
  have r : ∀ (u : AttSeg.Fam) (jj : ℕ), AttSeg.rv D C p t (.cell u jj) =
      ∑ b ∈ range D.nb, AttSeg.wp D C p.z u b *
          Blocks.ext (u.l D) (fun x => t (.c u.reg jj b x)) (AttSeg.inn D C p.z u) :=
    fun _ _ => rfl
  rw [r, r, r, r, r, r]
  unfold AttSeg.LL
  rw [lin3, lin3]
  rfl

end Inst.Model.AttSeg.KeyFormsExt
