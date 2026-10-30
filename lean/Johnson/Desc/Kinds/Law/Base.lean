-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Base.lean: THE BASE LAYER OF THE HEAD's LAW (L0 of the road): how an element of
the program's field and a form's constant are READ in the field K = Cb.Gl.E.
`rd`: the reading (`Reading.gl`, OnBytes/Model/HideLaws.lean; it is `readE` of
OnBytes/Slice/ProgField.lean). `cv`: the value of a form (`Aff.value`) in the world in which
every hidden scalar and every entry is 0: that is the reading of the form's constant (`cv_const`).
One law for each sign of HeadParts.lean. THE ONLY FILE OF THE PROOFS THAT KNOWS HOW A NATURAL NUMBER
IS LAID INTO E (`natF`, `natE`).
-/
import Mathlib
import OnBytes.Model.HideLaws
import OnBytes.Slice.ProgField
import Johnson.Desc.Kinds.Law.NoWrap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E addE subE mulE powE invE zeroE oneE scaleE)
open OnBytes.Model (Aff Reading World)

/-- The reading of an element. -/
def rd (x : E) : K := Reading.gl.val x

theorem rd_eq_readE (x : E) : rd x = OnBytes.Slice.readE x := rfl

theorem rd_add (a b : E) : rd (a + b) = rd a + rd b := Reading.gl.add a b
theorem rd_sub (a b : E) : rd (a - b) = rd a - rd b := Reading.gl.sub a b
theorem rd_mul (a b : E) : rd (a * b) = rd a * rd b := Reading.gl.mul a b
theorem rd_pow (a : E) (n : Nat) : rd (a ^ n) = rd a ^ n := OnBytes.Slice.readE_pow a n
theorem rd_inv (a : E) : rd (invE a) = (rd a)⁻¹ := OnBytes.Slice.readE_inv a

theorem toF_natF (n : Nat) : OnBytes.Slice.toF (natF n) = (n : Cb.Gl.F) :=
  OnBytes.Slice.toF_red n

theorem rd_natE (n : Nat) : rd (natE n) = (n : K) := by
  unfold natE
  rw [rd_eq_readE, OnBytes.Slice.readE_ofF, toF_natF, map_natCast]

theorem rd_natCast (n : Nat) : rd ((n : Nat) : E) = (n : K) := rd_natE n
theorem rd_ofNat (n : Nat) : rd (@OfNat.ofNat E n _) = (n : K) := rd_natE n
theorem rd_zero : rd (0 : E) = 0 := by rw [rd_ofNat]; simp
theorem rd_one : rd (1 : E) = 1 := by rw [rd_ofNat]; simp

theorem rd_scale (n : Nat) (x : E) : rd (scaleE (natF n) x) = (n : K) * rd x := by
  rw [rd_eq_readE, OnBytes.Slice.readE_scale, toF_natF, Algebra.smul_def, map_natCast]
  rfl

theorem rd_nmul (n : Nat) (x : E) : rd (HMul.hMul (α := Nat) (β := E) (γ := E) n x) = (n : K) * rd x :=
  rd_scale n x
theorem rd_muln (x : E) (n : Nat) : rd (HMul.hMul (α := E) (β := Nat) (γ := E) x n) = rd x * (n : K) := by
  rw [mul_comm]; exact rd_scale n x

theorem rd_sumTo (n : Nat) (f : Nat → E) :
    rd (sumTo n f) = (Finset.range n).sum fun i => rd (f i) := by
  unfold sumTo
  induction n with
  | zero => simpa using rd_zero
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    exact rd_add _ _

theorem rd_ofInt (z : Int) : rd (ofInt z) = (z : K) := by
  unfold ofInt
  split
  · rename_i h
    rw [rd_sub, rd_zero, rd_natCast]
    have hz : z = -((z.natAbs : Nat) : Int) := by omega
    conv_rhs => rw [hz]
    rw [Int.cast_neg, Int.cast_natCast, zero_sub]
  · rename_i h
    rw [rd_natCast]
    have hz : z = ((z.natAbs : Nat) : Int) := by omega
    conv_rhs => rw [hz]
    rw [Int.cast_natCast]

/-! ## Forms -/

/-- The world in which every hidden scalar and every entry is 0. -/
def W0 : World K := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- The value of a form there. -/
def cv (f : Form) : K := Aff.value Reading.gl W0 f

/-- It is the reading of the form's constant. -/
theorem cv_const (f : Form) : cv f = rd f.const := by
  have he : (f.ents.toList.map (OnBytes.Model.Ent.value Reading.gl W0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp [OnBytes.Model.Ent.value, W0]
  have hs : (f.slots.toList.map (OnBytes.Model.slotValue Reading.gl W0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    simp [OnBytes.Model.slotValue, W0]
  unfold cv Aff.value rd
  rw [he, hs, zero_add, zero_add]

theorem cv_add (f g : Form) : cv (f + g) = cv f + cv g := Aff.value_add _ _ f g
theorem cv_sub (f g : Form) : cv (f - g) = cv f - cv g := Aff.value_sub _ _ f g
theorem cv_scale (f : Form) (k : E) : cv (Aff.scale f k) = rd k * cv f := Aff.value_scale _ _ f k
theorem cv_ofConst (x : E) : cv (Aff.ofConst x) = rd x := Aff.value_ofConst _ _ x
theorem cv_smulE (k : E) (f : Form) : cv (k • f) = rd k * cv f := cv_scale f k
theorem cv_smulN (n : Nat) (f : Form) : cv (n • f) = (n : K) * cv f := by
  show cv (Aff.scale f (natE n)) = _
  rw [cv_scale, rd_natE]
theorem cv_coe (x : E) : cv ((x : E) : Form) = rd x := cv_ofConst x
theorem cv_natCast (n : Nat) : cv ((n : Nat) : Form) = (n : K) := by
  show cv (Aff.ofConst (natE n)) = _
  rw [cv_ofConst, rd_natE]
theorem cv_ofNat (n : Nat) : cv (@OfNat.ofNat Form n _) = (n : K) := cv_natCast n
theorem cv_addE (f : Form) (x : E) :
    cv (HAdd.hAdd (α := Form) (β := E) (γ := Form) f x) = cv f + rd x := by
  show cv (f + Aff.ofConst x) = _
  rw [cv_add, cv_ofConst]
theorem cv_Eadd (x : E) (f : Form) :
    cv (HAdd.hAdd (α := E) (β := Form) (γ := Form) x f) = rd x + cv f := by
  show cv (Aff.ofConst x + f) = _
  rw [cv_add, cv_ofConst]
theorem cv_subE (f : Form) (x : E) :
    cv (HSub.hSub (α := Form) (β := E) (γ := Form) f x) = cv f - rd x := by
  show cv (f - Aff.ofConst x) = _
  rw [cv_sub, cv_ofConst]
theorem cv_addN (f : Form) (n : Nat) :
    cv (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) f n) = cv f + (n : K) := by
  show cv (f + Aff.ofConst (natE n)) = _
  rw [cv_add, cv_ofConst, rd_natE]
theorem cv_subN (f : Form) (n : Nat) :
    cv (HSub.hSub (α := Form) (β := Nat) (γ := Form) f n) = cv f - (n : K) := by
  show cv (f - Aff.ofConst (natE n)) = _
  rw [cv_sub, cv_ofConst, rd_natE]

theorem cv_sumTo (n : Nat) (f : Nat → Form) :
    cv (sumTo n f) = (Finset.range n).sum fun i => cv (f i) := by
  unfold sumTo
  induction n with
  | zero => simpa using cv_ofNat 0
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    simp only [List.foldl_cons, List.foldl_nil]
    exact cv_add _ _

end VerifiableInference.Desc.Kinds.Head.Law
