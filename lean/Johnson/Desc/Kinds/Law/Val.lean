-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Val.lean: THE VALUE OF A FORM IN A WORLD, sign by sign, and sums that are spread
over entries and positions. val W f: the value of a form (Aff.value, OnBytes/Model/HideLaws.lean)
at the reading of the field, in a world W: a value for each hidden scalar and for each entry of
a read. One law for each sign of HeadParts.lean: Law/Base.lean's laws for cv, which is val at the world
0, with the same proofs at any world. spr: the sum over x < n, t < m of u x * w t * g x t.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Aff Reading World)

/-- The value of a form in a world. -/
def val (W : World K) (f : Form) : K := Aff.value Reading.gl W f

variable (W : World K)

theorem val_add (f g : Form) : val W (f + g) = val W f + val W g := Aff.value_add _ _ f g
theorem val_sub (f g : Form) : val W (f - g) = val W f - val W g := Aff.value_sub _ _ f g
theorem val_scale (f : Form) (k : E) : val W (Aff.scale f k) = rd k * val W f :=
  Aff.value_scale _ _ f k
theorem val_ofConst (x : E) : val W (Aff.ofConst x) = rd x := Aff.value_ofConst _ _ x
theorem val_smulE (k : E) (f : Form) : val W (k • f) = rd k * val W f := val_scale W f k
theorem val_smulN (n : Nat) (f : Form) : val W (n • f) = (n : K) * val W f := by
  show val W (Aff.scale f (natE n)) = _
  rw [val_scale, rd_natE]
theorem val_coe (x : E) : val W ((x : E) : Form) = rd x := val_ofConst W x
theorem val_natCast (n : Nat) : val W ((n : Nat) : Form) = (n : K) := by
  show val W (Aff.ofConst (natE n)) = _
  rw [val_ofConst, rd_natE]
theorem val_ofNat (n : Nat) : val W (@OfNat.ofNat Form n _) = (n : K) := val_natCast W n
theorem val_addE (f : Form) (x : E) :
    val W (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) = val W f + rd x := by
  show val W (f + Aff.ofConst x) = _
  rw [val_add, val_ofConst]
theorem val_Eadd (x : E) (f : Form) :
    val W (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) = rd x + val W f := by
  show val W (Aff.ofConst x + f) = _
  rw [val_add, val_ofConst]
theorem val_subE (f : Form) (x : E) :
    val W (HSub.hSub (α := Form) (β := E) (γ := Form) f x) = val W f - rd x := by
  show val W (f - Aff.ofConst x) = _
  rw [val_sub, val_ofConst]
theorem val_addN (f : Form) (n : Nat) :
    val W (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) = val W f + (n : K) := by
  show val W (f + Aff.ofConst (natE n)) = _
  rw [val_add, val_ofConst, rd_natE]
theorem val_subN (f : Form) (n : Nat) :
    val W (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) = val W f - (n : K) := by
  show val W (f - Aff.ofConst (natE n)) = _
  rw [val_sub, val_ofConst, rd_natE]

theorem val_sumTo (n : Nat) (f : Nat → Form) :
    val W (sumTo n f) = (Finset.range n).sum fun i => val W (f i) := by
  unfold sumTo
  induction n with
  | zero => simpa using val_ofNat W 0
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    exact val_add W _ _

theorem val_foldl_add : ∀ (l : List Form) (s : Form),
    val W (l.foldl (· + ·) s) = val W s + (l.map (val W)).sum
  | [], s => by simp
  | a :: l, s => by
    rw [List.foldl_cons, val_foldl_add l, val_add, List.map_cons, List.sum_cons]
    ring

/-! ## Sums that are spread over entries and positions -/

/-- The sum over x < n and t < m of u x * w t * g x t. -/
def spr (n m : Nat) (u w : Nat → K) (g : Nat → Nat → K) : K :=
  (Finset.range n).sum fun x => (Finset.range m).sum fun t => u x * w t * g x t

variable {n m : Nat} {u w : Nat → K}

theorem spr_add (g h : Nat → Nat → K) :
    spr n m u w g + spr n m u w h = spr n m u w fun x t => g x t + h x t := by
  unfold spr
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem spr_sub (g h : Nat → Nat → K) :
    spr n m u w g - spr n m u w h = spr n m u w fun x t => g x t - h x t := by
  unfold spr
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem spr_mul (a : K) (g : Nat → Nat → K) :
    a * spr n m u w g = spr n m u w fun x t => a * g x t := by
  unfold spr
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- A sum over the entries alone, where the positions' weights add up to 1. -/
theorem spr_entries (hw : (Finset.range m).sum w = 1) (g : Nat → K) :
    ((Finset.range n).sum fun x => u x * g x) = spr n m u w fun x _ => g x := by
  unfold spr
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ((Finset.range m).sum fun t => u x * w t * g x) = u x * g x * (Finset.range m).sum w := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [h, hw, mul_one]

theorem spr_congr {g h : Nat → Nat → K} (e : ∀ x, x < n → ∀ t, t < m → g x t = h x t) :
    spr n m u w g = spr n m u w h := by
  unfold spr
  refine Finset.sum_congr rfl fun x hx => ?_
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [e x (Finset.mem_range.1 hx) t (Finset.mem_range.1 ht)]

end VerifiableInference.Desc.Kinds.Head.Law.Came
