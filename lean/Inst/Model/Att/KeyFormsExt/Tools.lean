-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/Tools.lean: lemmas on multilinear extensions, and `idP` as the extension
of i ↦ i.

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `ext_top`: the top variable split off. `ext_drop_last`, `ext_drop_first`: a table that ignores its
    last, or its first, variables. `ext_mul_last`: a factor that ignores the last variables comes
    out of the inner extension.
  `ext_id`: `idP g` (Inst/Model/Att/Points.lean) is the multilinear extension of i ↦ i.
  `eqPt_hi`, `eqPt_lo`: `eqPt` (Inst/Model/Att/Sums.lean) at a vertex of the cube is `Blocks.eqN` of
    the upper, or the lower, part of the vertex's number.
  `ext_rd2`: an extension over (g | i) is `rd2` (Inst/Model/Att/Sums.lean).
Limits: nothing here reads the cells. Coordinate 0 of a point belongs to the most significant bit,
as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.Calls14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

theorem eqN_sh (m off : ℕ) (pt : ℕ → E) (y : ℕ) : Blocks.eqN m off pt y =
    Blocks.eqN m 0 (AttSeg.sh pt off) y := by
  unfold Blocks.eqN AttSeg.sh
  exact Finset.prod_congr rfl fun t _ => by rw [Nat.zero_add]

omit [Field E] in
theorem sh_sh (pt : ℕ → E) (a b : ℕ) : AttSeg.sh (AttSeg.sh pt a) b = AttSeg.sh pt (a + b) := by
  funext t
  unfold AttSeg.sh
  rw [Nat.add_assoc]

/-- the top variable -/
theorem ext_top (g : ℕ) (v pt : ℕ → E) :
    Blocks.ext (1 + g) v pt =
      (1 - pt 0) * Blocks.ext g v (AttSeg.sh pt 1) + pt 0 *
          Blocks.ext g (fun y => v (2 ^ g + y)) (AttSeg.sh pt 1) := by
  rw [ext_split' 1 g, ext_def 1]
  have h2 : (2 : ℕ) ^ 1 = 2 := rfl
  rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have e0 : Blocks.eqN 1 0 pt 0 = 1 - pt 0 := by simp [Blocks.eqN]
  have e1 : Blocks.eqN 1 0 pt 1 = pt 0 := by simp [Blocks.eqN]
  rw [e0, e1]
  simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul]

theorem ext_drop_last (g g' : ℕ) (a pt : ℕ → E) :
    Blocks.ext (g + g') (fun X => a (X / 2 ^ g')) pt = Blocks.ext g a pt := by
  rw [ext_split']
  refine Blocks.ext_congr (fun x _ => ?_) pt
  rw [Blocks.ext_congr (w := fun _ => a x) (fun y hy => by rw [div_pow g' x hy]), Blocks.ext_const]

theorem ext_drop_first (g g' : ℕ) (a pt : ℕ → E) :
    Blocks.ext (g + g') (fun X => a (X % 2 ^ g')) pt = Blocks.ext g' a (AttSeg.sh pt g) := by
  rw [ext_split']
  rw [Blocks.ext_congr (w := fun _ => Blocks.ext g' a (AttSeg.sh pt g)) (fun x _ =>
    Blocks.ext_congr (fun y hy => by rw [mod_pow g' x hy]) _), Blocks.ext_const]

/-- a factor that ignores the last variables comes out of the inner extension -/
theorem ext_mul_last (g g' : ℕ) (d : ℕ → E) (o : ℕ → ℕ → E) (pt : ℕ → E) :
    Blocks.ext (g + g') (fun X => d (X / 2 ^ g') * o (X / 2 ^ g') (X % 2 ^ g')) pt =
      Blocks.ext g (fun Y => d Y * Blocks.ext g' (o Y) (AttSeg.sh pt g)) pt := by
  rw [ext_split']
  refine Blocks.ext_congr (fun x _ => ?_) pt
  rw [← Blocks.ext_smul]
  exact Blocks.ext_congr (fun y hy => by rw [div_pow g' x hy, mod_pow g' x hy]) _

/-- `idP` is the multilinear extension of i ↦ i. -/
theorem ext_id (g : ℕ) : ∀ pt : ℕ → E, Blocks.ext g (fun i => (i : E)) pt = AttSeg.idP g pt := by
  induction g with
  | zero =>
    intro pt
    simp [Blocks.ext, AttSeg.idP, Blocks.eqN]
  | succ g ih =>
    intro pt
    rw [Nat.add_comm g 1, ext_top, ih]
    have h1 : Blocks.ext g (fun y => (((2 ^ g + y : ℕ)) : E)) (AttSeg.sh pt 1) = 2 ^ g +
        AttSeg.idP g (AttSeg.sh pt 1) := by
      rw [Blocks.ext_congr (w := fun y => (2 : E) ^ g + (y : E)) (fun y _ => by push_cast; ring),
        Blocks.ext_add, Blocks.ext_const, ih]
    rw [h1]
    unfold AttSeg.idP
    rw [Nat.add_comm 1 g, Finset.sum_range_succ']
    have h2 : ∑ k ∈ range g, (2 : E) ^ (g + 1 - 1 - (k + 1)) * pt (k + 1) =
        ∑ k ∈ range g, (2 : E) ^ (g - 1 - k) * AttSeg.sh pt 1 k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold AttSeg.sh
      rw [Nat.add_comm 1 k]
      congr 2
      omega
    rw [h2]
    simp only [Nat.add_sub_cancel, Nat.sub_zero]
    ring

/-! ### `eqPt` at a vertex of the cube -/

theorem cubePt_apply (g X : ℕ) {k : ℕ} (hk : k < g) :
    (Blocks.cubePt g X : ℕ → E) k = if X.testBit (g - 1 - k) then 1 else 0 := by
  simp [Blocks.cubePt, Blocks.nat, hk, Alg.corner, Alg.bits]

theorem eq1_bit (u : E) (c : Bool) : AttSeg.eq1 u (if c then 1 else 0) = if c then u else 1 - u :=
    by
  cases c <;> simp [AttSeg.eq1]

theorem eqPt_hi (n1 n2 : ℕ) (u : ℕ → E) (X : ℕ) :
    AttSeg.eqPt n1 u (Blocks.cubePt (n1 + n2) X) = Blocks.eqN n1 0 u (X / 2 ^ n2) := by
  unfold AttSeg.eqPt Blocks.eqN
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  rw [cubePt_apply _ _ (by omega), eq1_bit, Nat.testBit_div_two_pow, Nat.zero_add]
  have e : n1 + n2 - 1 - t = n1 - 1 - t + n2 := by omega
  rw [e]

theorem eqPt_lo (n1 n2 : ℕ) (u : ℕ → E) (X : ℕ) :
    AttSeg.eqPt n2 u (AttSeg.sh (Blocks.cubePt (n1 + n2) X) n1) = Blocks.eqN n2 0 u (X % 2 ^ n2) :=
        by
  unfold AttSeg.eqPt Blocks.eqN
  refine Finset.prod_congr rfl fun t ht => ?_
  have ht' := Finset.mem_range.1 ht
  show AttSeg.eq1 (u t) ((Blocks.cubePt (n1 + n2) X : ℕ → E) (n1 + t)) = _
  rw [cubePt_apply _ _ (by omega), eq1_bit, Nat.testBit_mod_two_pow, Nat.zero_add]
  have e : n1 + n2 - 1 - (n1 + t) = n2 - 1 - t := by omega
  have l : n2 - 1 - t < n2 := by omega
  rw [e]
  simp [l]

variable (D : AttSeg.Dim)

/-- an extension over (g | i) is `rd2` -/
theorem ext_rd2 (a : ℕ → ℕ → E) (pt : ℕ → E) :
    Blocks.ext (D.lg + D.lT) (fun X => a (X / D.T) (X % D.T)) pt =
        AttSeg.rd2 D pt (AttSeg.eqT D (AttSeg.sh pt D.lg)) a := by
  rw [Blocks.ext_two]
  unfold AttSeg.rd2 AttSeg.eqT
  rw [show D.nG = 2 ^ D.lg from rfl, D.T_eq]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y hy => ?_
  have hy' := Finset.mem_range.1 hy
  rw [div_pow D.lT x hy', mod_pow D.lT x hy', eqN_sh D.lT D.lg pt y]

end Inst.Model.AttSeg.KeyFormsExt
