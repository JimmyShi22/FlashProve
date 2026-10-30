-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Inst/Model/Att/KeyFormsExt/LessEq.lean: `LE` is the multilinear extension of [x ≤ y].

Part of the proof that the key forms of an attention segment, at the rule values, are the
multilinear extensions of the calls' vectors of looked-up values (`kfExt`,
Inst/Model/Att/KeyFormsExt/All.lean). Statements with their proofs. No protocol and no probability:
algebra of extensions (`Blocks.ext`, Blocks/Ext.lean).
Main names:
  `ext_swap`: two nested extensions may be exchanged.
  `ext_le`: `LE g u v` (Inst/Model/Att/Points.lean) is the extension over x at u of the extension
    over y at v of [x ≤ y].
  `ext_last`: the extension of "c at the last index, G elsewhere" is c times `ones` plus the sum of
    G under the equality weights over the other indices.
Limits: nothing here reads the cells. Coordinate 0 of a point belongs to the most significant bit,
as in Blocks/Ext.lean.
-/
import Inst.Model.Att.KeyFormsExt.Cube

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Inst.Model.AttSeg.KeyFormsExt
open Inst.Model Inst.Model.AttSeg Finset

variable {E : Type} [Field E]

/-- two nested extensions may be exchanged -/
theorem ext_swap (g g' : ℕ) (f : ℕ → ℕ → E) (u v : ℕ → E) :
    Blocks.ext g (fun x => Blocks.ext g' (fun y => f x y) v) u =
        Blocks.ext g' (fun y => Blocks.ext g (fun x => f x y) u) v := by
  simp only [ext_def, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring

/-- `LE` is the multilinear extension of [x ≤ y]. -/
theorem ext_le (g : ℕ) : ∀ u v : ℕ → E,
    Blocks.ext g (fun x => Blocks.ext g (fun y => if x ≤ y then 1 else 0) v) u = AttSeg.LE g u v :=
        by
  induction g with
  | zero =>
    intro u v
    simp [Blocks.ext, AttSeg.LE, Blocks.eqN]
  | succ g ih =>
    intro u v
    rw [Nat.add_comm g 1, ext_top]
    have lo : Blocks.ext g (fun x => Blocks.ext (1 + g) (fun y => if x ≤ y then (1 : E) else 0) v)
        (AttSeg.sh u 1) =
        (1 - v 0) * AttSeg.LE g (AttSeg.sh u 1) (AttSeg.sh v 1) + v 0 := by
      rw [Blocks.ext_congr (w := fun x => (1 - v 0) *
          Blocks.ext g (fun y => if x ≤ y then (1 : E) else 0) (AttSeg.sh v 1) + v 0)
        (fun x hx => by
          rw [ext_top, Blocks.ext_congr (v := fun y => if x ≤ 2 ^ g + y then (1 : E) else 0)
              (w := fun _ => 1)
            (fun y _ => if_pos (by omega)), Blocks.ext_const, mul_one]),
        Blocks.ext_add, Blocks.ext_smul, Blocks.ext_const, ih]
    have hi : Blocks.ext g (fun x =>
        Blocks.ext (1 + g) (fun y => if 2 ^ g + x ≤ y then (1 : E) else 0) v) (AttSeg.sh u 1) =
        v 0 * AttSeg.LE g (AttSeg.sh u 1) (AttSeg.sh v 1) := by
      rw [Blocks.ext_congr (w := fun x => v 0 *
          Blocks.ext g (fun y => if x ≤ y then (1 : E) else 0) (AttSeg.sh v 1))
        (fun x _ => by
          rw [ext_top, Blocks.ext_zero_of_forall
              (v := fun y => if 2 ^ g + x ≤ y then (1 : E) else 0)
              (fun y hy => if_neg (by omega)), mul_zero, zero_add]
          refine congrArg (v 0 * ·) (Blocks.ext_congr (fun y _ => ?_) _)
          by_cases h : x ≤ y
          · rw [if_pos h, if_pos (by omega)]
          · rw [if_neg h, if_neg (by omega)]),
        Blocks.ext_smul, ih]
    rw [lo, hi, Nat.add_comm 1 g]
    show _ = (1 - u 0) * v 0 + AttSeg.eq1 (u 0) (v 0) * AttSeg.LE g (AttSeg.sh u 1) (AttSeg.sh v 1)
    unfold AttSeg.eq1
    ring

/-- the extension of "c at the last index, G elsewhere" -/
theorem ext_last (n : ℕ) (c : E) (G : ℕ → E) (z : ℕ → E) :
    Blocks.ext n (fun s => if s = 2 ^ n - 1 then c else G s) z =
      c * AttSeg.ones n z + ∑ s ∈ range (2 ^ n - 1), Blocks.eqN n 0 z s * G s := by
  rw [ext_def]
  have h : 2 ^ n = (2 ^ n - 1) + 1 := (Nat.sub_add_cancel (Nat.two_pow_pos n)).symm
  conv_lhs => rw [h, Finset.sum_range_succ]
  rw [Nat.add_sub_cancel, if_pos rfl, ones_eq, add_comm, mul_comm]
  refine congrArg (c * Blocks.eqN n 0 z (2 ^ n - 1) + ·) (Finset.sum_congr rfl fun s hs => ?_)
  have := Finset.mem_range.1 hs
  rw [if_neg (by omega)]

end Inst.Model.AttSeg.KeyFormsExt
