-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/SumZO.lean: the sum ZO of an attention segment in terms of the cells, and
arrays over (g | i | n) at (y_g | y_i | y_n).

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `DO`: the extension over (g | i), at (y_g | y_i), of den_b times the sum over n of eq(y_n, n)
    out_b.
  `zo_eq`: `sumPhi D C p t .s8` (Inst/Model/Att/Sums.lean), the rule value of ZO, is the sum over b
    of wp_b times `DO` b.
  `atY_gi`, `atY_do`, `atY_add`, `atY_sub`, `atY_smul`, `atY_const`, `atY_RE`: `atY`
    (Inst/Model/Att/KeyForms.lean) of an array that ignores n, of den · out, of sums, differences,
    multiples and constants, and of RE_b.
  `gi_lt`, `hi_ch`, `hi_mod_ch`, `hi_T`, `hi_mod_T`: the parts of an index (χ | g | i | n).
Limits: for every content of the cells and all challenges; no hypothesis on sizes. Coordinate 0 of a
point belongs to the most significant bit, as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.Tools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E] (D : AttSeg.Dim) (C : AttSeg.Calls)

omit [Field E] in
theorem sh_zero (u : ℕ → E) : AttSeg.sh u 0 = u := by
  funext t
  unfold AttSeg.sh
  rw [Nat.zero_add]

/-! ### indices (χ | g | i | n) -/

theorem l4_pow : 2 ^ D.l4 = 2 ^ D.lg * 2 ^ D.lT * 2 ^ D.ln := by
  unfold AttSeg.Dim.l4
  rw [pow_add, pow_add]

theorem gi_lt {y : ℕ} (hy : y < 2 ^ D.l4) : y / D.ch / D.T < D.nG := by
  rw [show D.ch = 2 ^ D.ln from rfl, D.T_eq, show D.nG = 2 ^ D.lg from rfl, Nat.div_div_eq_div_mul,
    Nat.div_lt_iff_lt_mul (by positivity)]
  rw [l4_pow] at hy
  calc y < 2 ^ D.lg * 2 ^ D.lT * 2 ^ D.ln := hy
    _ = 2 ^ D.lg * (2 ^ D.ln * 2 ^ D.lT) := by ring

theorem hi_ch (y : ℕ) : (2 ^ D.l4 + y) / D.ch = 2 ^ D.lg * 2 ^ D.lT + y / D.ch := by
  rw [show D.ch = 2 ^ D.ln from rfl, l4_pow, Nat.mul_comm (2 ^ D.lg * 2 ^ D.lT) (2 ^ D.ln),
    Nat.mul_add_div (Nat.two_pow_pos _)]

theorem hi_mod_ch (y : ℕ) : (2 ^ D.l4 + y) % D.ch = y % D.ch := by
  rw [show D.ch = 2 ^ D.ln from rfl, l4_pow, Nat.mul_comm (2 ^ D.lg * 2 ^ D.lT) (2 ^ D.ln),
      Nat.mul_add_mod]

theorem hi_T (r : ℕ) : (2 ^ D.lg * 2 ^ D.lT + r) / D.T = D.nG + r / D.T := by
  rw [D.T_eq, show D.nG = 2 ^ D.lg from rfl, Nat.mul_comm (2 ^ D.lg) (2 ^ D.lT),
      Nat.mul_add_div (Nat.two_pow_pos _)]

theorem hi_mod_T (r : ℕ) : (2 ^ D.lg * 2 ^ D.lT + r) % D.T = r % D.T := by
  rw [D.T_eq, Nat.mul_comm (2 ^ D.lg) (2 ^ D.lT), Nat.mul_add_mod]

variable (p : AttSeg.Pub E) (t : AttSeg.Raw → E)

/-- the point (y_g | y_i | y_n) -/
abbrev q : ℕ → E := AttSeg.sh (AttSeg.uW D C p.z) 1

/-- den_b · ∑_n eq(y_n, n) out_b, extended over (g | i), at (y_g | y_i) -/
def DO (b : ℕ) : E :=
  Blocks.ext (D.lg + D.lT) (fun Y => AttSeg.denV t b (Y / D.T) (Y % D.T) *
    AttSeg.conN D (AttSeg.yn D C p.z) fun n => AttSeg.outV t b (Y / D.T) (Y % D.T) n) (q D C p)

/-- The sum ZO in terms of the cells. -/
theorem zo_eq : AttSeg.sumPhi D C p t .s8 = ∑ b ∈ range D.nb, AttSeg.wp D C p.z .w3 b *
    DO D C p t b := by
  unfold AttSeg.sumPhi AttSeg.Phi
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold DO
  rw [ext_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun X hX => ?_
  have hX' : X < 2 ^ (D.lg + D.lT) := Finset.mem_range.1 hX
  have hA : AttSeg.Aext D C p t .s8 b (Blocks.cubePt (D.lg + D.lT) X) =
      AttSeg.denV t b (X / D.T) (X % D.T) :=
    Blocks.ext_cubePt _ _ hX'
  have hB : AttSeg.Bext D C p t .s8 b (Blocks.cubePt (D.lg + D.lT) X) =
      AttSeg.conN D (AttSeg.yn D C p.z) fun n => AttSeg.outV t b (X / D.T) (X % D.T) n :=
    Blocks.ext_cubePt _ _ hX'
  have hWt : AttSeg.Wb D C p .s8 b (Blocks.cubePt (D.lg + D.lT) X) =
      AttSeg.wp D C p.z .w3 b * Blocks.eqN (D.lg + D.lT) 0 (q D C p) X := by
    show AttSeg.wp D C p.z .w3 b *
        AttSeg.eqPt D.lg (AttSeg.yg D C p.z) (Blocks.cubePt (D.lg + D.lT) X) *
      AttSeg.eqPt D.lT (AttSeg.yi D C p.z) (AttSeg.sh (Blocks.cubePt (D.lg + D.lT) X) D.lg) = _
    rw [eqPt_hi, eqPt_lo]
    have hs : X = X / 2 ^ D.lT * 2 ^ D.lT + X % 2 ^ D.lT := (Nat.div_add_mod' X _).symm
    conv_rhs => rw [hs, Blocks.eqN_append' D.lg D.lT 0 _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
        Nat.zero_add, eqN_sh D.lT D.lg]
    have hyi : AttSeg.yi D C p.z = AttSeg.sh (q D C p) D.lg := (sh_sh _ 1 D.lg).symm
    rw [hyi, mul_assoc]
    rfl
  show AttSeg.Wb D C p .s8 b (Blocks.cubePt (D.lg + D.lT) X) *
      AttSeg.Aext D C p t .s8 b (Blocks.cubePt (D.lg + D.lT) X) *
      AttSeg.Bext D C p t .s8 b (Blocks.cubePt (D.lg + D.lT) X) = _
  rw [hWt, hA, hB]
  ring

/-! ### arrays over (g | i | n) at (y_g | y_i | y_n) -/

/-- an array that ignores n -/
theorem atY_gi (a : ℕ → ℕ → E) :
    AttSeg.atY D C p (fun g i _ => a g i) =
        AttSeg.rd2 D (AttSeg.yg D C p.z) (AttSeg.eqT D (AttSeg.yi D C p.z)) a := by
  unfold AttSeg.atY
  have h := ext_drop_last (D.lg + D.lT) D.ln (fun Y => a (Y / D.T) (Y % D.T)) (q D C p)
  have hyi : AttSeg.yi D C p.z = AttSeg.sh (q D C p) D.lg := (sh_sh _ 1 D.lg).symm
  rw [hyi]
  show Blocks.ext (D.lg + D.lT + D.ln) (fun X => a (X / 2 ^ D.ln / D.T) (X / 2 ^ D.ln % D.T))
      (q D C p) = _
  rw [h, ext_rd2]
  rfl

/-- den · out -/
theorem atY_do (b : ℕ) :
    AttSeg.atY D C p (fun g i n => AttSeg.denV t b g i * AttSeg.outV t b g i n) = DO D C p t b := by
  unfold AttSeg.atY DO
  have h := ext_mul_last (D.lg + D.lT) D.ln (fun Y => AttSeg.denV t b (Y / D.T) (Y % D.T))
    (fun Y n => AttSeg.outV t b (Y / D.T) (Y % D.T) n) (q D C p)
  show Blocks.ext (D.lg + D.lT + D.ln)
      (fun X => AttSeg.denV t b (X / 2 ^ D.ln / D.T) (X / 2 ^ D.ln % D.T) *
    AttSeg.outV t b (X / 2 ^ D.ln / D.T) (X / 2 ^ D.ln % D.T) (X % 2 ^ D.ln)) (q D C p) = _
  rw [h]
  refine Blocks.ext_congr (fun Y _ => ?_) _
  have hyn : AttSeg.yn D C p.z = AttSeg.sh (q D C p) (D.lg + D.lT) := by
    unfold AttSeg.yn
    rw [sh_sh, Nat.add_assoc]
  rw [hyn]
  rfl

theorem atY_add (a a' : ℕ → ℕ → ℕ → E) :
    AttSeg.atY D C p (fun g i n => a g i n + a' g i n) = AttSeg.atY D C p a + AttSeg.atY D C p a' :=
        by
  unfold AttSeg.atY
  exact Blocks.ext_add _ _ _ _

theorem atY_sub (a a' : ℕ → ℕ → ℕ → E) :
    AttSeg.atY D C p (fun g i n => a g i n - a' g i n) = AttSeg.atY D C p a - AttSeg.atY D C p a' :=
        by
  unfold AttSeg.atY
  exact Blocks.ext_sub _ _ _ _

theorem atY_smul (c : E) (a : ℕ → ℕ → ℕ → E) :
    AttSeg.atY D C p (fun g i n => c * a g i n) = c * AttSeg.atY D C p a := by
  unfold AttSeg.atY
  exact Blocks.ext_smul _ _ _ _

theorem atY_const (c : E) : AttSeg.atY D C p (fun _ _ _ => c) = c := by
  unfold AttSeg.atY
  exact Blocks.ext_const _ _ _

/-- RE_b at (y_g | y_i | y_n) -/
theorem atY_RE (b : ℕ) :
    AttSeg.atY D C p (AttSeg.RE D t b) =
      2 * AttSeg.atY D C p (AttSeg.AC D t b) +
        AttSeg.rd2 D (AttSeg.yg D C p.z) (AttSeg.eqT D (AttSeg.yi D C p.z)) (AttSeg.denV t b) - 2 *
            DO D C p t b := by
  have e : AttSeg.RE D t b = fun g i n => (2 * AttSeg.AC D t b g i n + AttSeg.denV t b g i) -
      2 * (AttSeg.denV t b g i * AttSeg.outV t b g i n) := by
    funext g i n
    unfold AttSeg.RE
    ring
  rw [e, atY_sub, atY_add, atY_smul, atY_smul, atY_gi, atY_do]

end Inst.Model.AttSeg.KeyFormsExt
