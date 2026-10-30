-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMatProofs.lean: what the proofs for the seven key families of the feed-forward segment that
hold a matrix product with weights (`isMat`, Cm/SegFFMat.lean) share. (Key families of the model's
arithmetisation: what a family, a block and a vertex are is told in the head of Cm/SegFFMat.lean.)


Main names:
  vx_..: the numbers of bits of the index x of the seven families.
  `num_j`, `num_jhi`, `num_jlo`, `num_x`, `num_xlo`, `num_xhi`: see their doc comments.
  `val_cSs`, `val_mXS`, `sum_gVal`: values of forms.
  Of the family over `Cb.Gl.E` (Cm/TargetSegFFMatProofs.lean), not here: `val_split`,
    `val_mblk_dead`, `val_mblk_live`, `val_mblk_zero`, `val_blk1`, `val_blkR`, `val_mlive`:
    values of a family and its blocks at a vertex; `matKey_dead`: the padding at a dead vertex.
The first three rows hold over every field; Cm/TargetSegFFMatProofs.lean and
Cm/TargetSegFFMatProofsA.lean to Cm/TargetSegFFMatProofsE.lean use them as they are.
-/
import Cm.SegFFMat

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset
open Ex

variable [scl : Scl]

/-! ## Numbers -/

theorem vx_G : vxOf .G = 14 := by decide +kernel
theorem vx_U : vxOf .U = 14 := by decide +kernel
theorem vx_QK : vxOf .QK = 13 := by decide +kernel
theorem vx_O : vxOf .O = 13 := by decide +kernel
theorem vx_D : vxOf .D = 13 := by decide +kernel
theorem vx_V : vxOf .V = 10 := by decide +kernel
theorem vx_LR : vxOf .LR = 7 := by decide +kernel

/-! ## Runs of variables at the vertex (b, j), b = (ℓ | x | i) -/

section Runs
variable {v w n m a b j vx l x i : ℕ}

/-- all inner variables: j -/
theorem num_j (ha : a = v) (hj : j < 2 ^ w) :
    Src.num (Src.run a w) (v + w) (b * 2 ^ w + j) = j := by
  subst ha
  rw [num_in (le_refl a) (le_refl _), Nat.add_sub_cancel_left, Nat.sub_self, pow_zero,
    Nat.div_one, Nat.mod_eq_of_lt hj]

/-- the first n of n + m inner variables: j / 2^m -/
theorem num_jhi (ha : a = v) (hw : w = n + m) (hj : j < 2 ^ w) :
    Src.num (Src.run a n) (v + w) (b * 2 ^ w + j) = j / 2 ^ m := by
  subst ha hw
  rw [num_in (le_refl a) (by omega), show a + (n + m) - a - n = m by omega]
  refine Nat.mod_eq_of_lt ?_
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), ← pow_add]
  exact hj

/-- the last m of n + m inner variables: j mod 2^m -/
theorem num_jlo (ha : a = v + n) (hw : w = n + m) :
    Src.num (Src.run a m) (v + w) (b * 2 ^ w + j) = j % 2 ^ m := by
  subst ha hw
  rw [num_in (by omega) (by omega),
    show v + (n + m) - (v + n) - m = 0 by omega, pow_zero, Nat.div_one]

/-- the variables of x -/
theorem num_x (hd : dec3 vx b = (l, x, i)) (hj : j < 2 ^ w) :
    Src.num (Src.run 2 vx) (2 + vx + 10 + w) (b * 2 ^ w + j) = x := by
  rw [num_out (by omega) hj, show 2 + vx + 10 - 2 - vx = 10 by omega]
  exact congrArg (fun q => q.2.1) hd

/-- the last n variables of x: x mod 2^n -/
theorem num_xlo (h2 : 2 ≤ a) (ha : a + n = 2 + vx) (hd : dec3 vx b = (l, x, i)) (hj : j < 2 ^ w) :
    Src.num (Src.run a n) (2 + vx + 10 + w) (b * 2 ^ w + j) = x % 2 ^ n := by
  have hx : b / 2 ^ 10 % 2 ^ vx = x := congrArg (fun q => q.2.1) hd
  rw [num_out (by omega) hj, show 2 + vx + 10 - a - n = 10 by omega, ← hx,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))]

/-- the first n of the n + m variables of x: x / 2^m -/
theorem num_xhi (hv : vx = n + m) (hd : dec3 vx b = (l, x, i)) (hj : j < 2 ^ w) :
    Src.num (Src.run 2 n) (2 + vx + 10 + w) (b * 2 ^ w + j) = x / 2 ^ m := by
  subst hv
  have hx : b / 2 ^ 10 % 2 ^ (n + m) = x := congrArg (fun q => q.2.1) hd
  rw [num_out (by omega) hj, show 2 + (n + m) + 10 - 2 - n = 10 + m by omega, ← hx, pow_add,
    ← Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm (2 ^ n), Nat.mod_mul_right_div_self]

end Runs

/-! ## Forms -/

section Forms
variable {E : Type} [Field E] (g : ℕ) (A : ℕ → ℕ → ℕ → E)

theorem val_cSs (q rh : CForm E) (k : ℕ) :
    (cSs q rh k).val A = Site.ssite 0 (q.val A) (rh.val A) k := by
  rw [Site.ssite_eq]
  simp [cSs]

theorem val_mXS (s j i : ℕ) : (mXS g s j i : CForm E).val A = FFSeg.xS DF (tA g A) s j i :=
  val_cVal g A _ _ _ _

/-- for an array's width ≤ N: the sum over j < N of `gVal` at j times ω j is the sum over the width
of the array's values times ω j -/
theorem sum_gVal (X : FFSeg.Arr) (a i : ℕ) {N : ℕ} (hN : X.width DF ≤ N) (ω : ℕ → E) :
    ∑ j ∈ range N, (gVal g X a j i : CForm E).val A * ω j =
      ∑ j ∈ range (X.width DF), FFSeg.val (tA g A) X a j i * ω j := by
  rw [sum_cut hN _ fun j hj _ => by rw [val_gVal, if_neg (Nat.not_lt.2 hj), zero_mul]]
  exact sum_congr rfl fun j hj => by rw [val_gVal, if_pos (mem_range.1 hj)]

end Forms



end Cm.Seg
