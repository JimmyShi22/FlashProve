-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/SigT.lean: the products in the keys are the sum over the cube of the summand
of the sumcheck over the positions: the library with itself.

A key of a feed-forward segment holds products of two values at one position (term in
Inst/Model/FF/Objects.lean). The library sums them under the weights of the entries to TERM, under
those of the layers and the equality weights of the lookup's token point to TS, and under the
calls' weights to ClT, the honest value of a masked scalar. For the sumcheck over the positions it
has the summand Gpos, a polynomial in a point X of the positions: the same sum with each of the two
factors of a product replaced by its multilinear extension (termHat). This file shows that at a
vertex of the cube the summand is the sum of the products at that position, and so that ClT is the
sum over the cube of Gpos under the equality weights of the token point: the claim with which that
sumcheck begins.

Every statement here compares objects of the library with objects of the library. The file imports
no file of OnBytes/.

Main theorems: clT_gpos; hat_cube (termHat at a vertex is TERM, for every family); gpos_cube.

The hypothesis, and that it can be met. D.f = 2 D.fe: the summand of the routed gate and up
projection runs over fe entries from fe on, the family has f entries. It is the field f of the
library's Dim.OK, which the reference sizes meet (ref_ok).

What is not claimed. Nothing is said of the sumcheck's rounds. What Gpos is at the sumcheck's end
point is the matter of Cb/Pv/Lay/End/SigG.lean. Nothing is a statement on what a verifier's
acceptance shows. The program does not import this file.


-/
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Sig

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW termHat TERM term TS ClT Gpos famsIn len ew sw el wc
  zpos valU xU hhU val xS hh mr AYU AY Aq Ak Ct St Y' kQK Ag Au routed isExpL)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over n + m numbers whose first n terms vanish. -/
theorem sum_tail (n m : ℕ) (f : ℕ → K) (h0 : ∀ x, x < n → f x = 0) :
    ∑ x ∈ range (n + m), f x = ∑ x ∈ range m, f (n + x) := by
  rw [sum_range_add, sum_eq_zero fun x hx => h0 x (mem_range.mp hx), zero_add]

/-- Weights on the columns of a three-fold product, drawn in to the innermost sum; k: a shift. -/
theorem tri_in (k n a b : ℕ) (g s x : ℕ → K) (M : ℕ → ℕ → ℕ → K) :
    ∑ y ∈ range n, g y * Inst.Model.Site.scl k
        (∑ e ∈ range a, s e * ∑ j ∈ range b, x j * M e j y) =
      Inst.Model.Site.scl k
        (∑ e ∈ range a, s e * ∑ j ∈ range b, x j * ∑ y ∈ range n, g y * M e j y) := by
  simp only [Inst.Model.Site.scl_eq, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  exact sum_congr rfl fun y _ => by ring

/-! ## The extensions at a vertex of the cube -/

section Cube

variable (D : Dim) (t : Cell → K) {i : ℕ} (hi : i < 2 ^ D.lT)

include hi

/-- The extension of an array's values. -/
theorem valU_cube (X : Arr) (inst j : ℕ) :
    valU D t X inst j (Blocks.cubePt D.lT i) = val t X inst j i := Blocks.ext_cubePt _ _ hi

/-- The extension of the stream. -/
theorem xU_cube (s j : ℕ) : xU D t s j (Blocks.cubePt D.lT i) = xS D t s j i :=
  Blocks.ext_cubePt _ _ hi

/-- The extension of a gated product. -/
theorem hhU_cube (l j : ℕ) : hhU D t l j (Blocks.cubePt D.lT i) = hh t l j i :=
  Blocks.ext_cubePt _ _ hi

/-- The extension of the rotary cosines. -/
theorem Ct_cube (tb : Tables) (L0 l jj : ℕ) :
    Ct D tb L0 l jj (Blocks.cubePt D.lT i) = (((tb.C (L0 + l) i jj : ℤ) : K)) :=
  Blocks.ext_cubePt _ _ hi

/-- The extension of the rotary sines. -/
theorem St_cube (tb : Tables) (L0 l jj : ℕ) :
    St D tb L0 l jj (Blocks.cubePt D.lT i) = (((tb.S (L0 + l) i jj : ℤ) : K)) :=
  Blocks.ext_cubePt _ _ hi

/-- The extension of AY. -/
theorem AYU_cube (w : ℕ → LW K) (l x : ℕ) :
    AYU D t w l x (Blocks.cubePt D.lT i) = AY D t w l x i := by
  unfold AYU AY Aq Ak
  simp only [valU_cube D t hi]

end Cube

/-! ## The summand at a vertex, family by family -/

section Hat

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z : ℕ → K)

/-- At a vertex of the cube the summand of a family is the sum of the products in its keys at that
position, under the entries' weights. -/
theorem hat_cube (hf : D.f = 2 * D.fe) (s : Fam) (l : ℕ) {i : ℕ} (hi : i < 2 ^ D.lT) :
    termHat D t tb L0 w z s l (Blocks.cubePt D.lT i) = TERM D t tb L0 w z s l i := by
  have hff : D.f = D.fe + D.fe := by omega
  unfold TERM
  cases s with
  | N1 =>
    show Blocks.ext D.lT _ (Blocks.cubePt D.lT i) *
      ∑ x ∈ range D.d, ew D z .N1 x * xU D t (2 * l) x (Blocks.cubePt D.lT i) =
      ∑ x ∈ range D.d, ew D z .N1 x * (xS D t (2 * l) x i * _)
    rw [Blocks.ext_cubePt _ _ hi, mul_sum]
    exact sum_congr rfl fun x _ => by rw [xU_cube D t hi]; ring
  | N2 =>
    show Blocks.ext D.lT _ (Blocks.cubePt D.lT i) *
      ∑ x ∈ range D.d, ew D z .N2 x * xU D t (2 * l + 1) x (Blocks.cubePt D.lT i) =
      ∑ x ∈ range D.d, ew D z .N2 x * (xS D t (2 * l + 1) x i * _)
    rw [Blocks.ext_cubePt _ _ hi, mul_sum]
    exact sum_congr rfl fun x _ => by rw [xU_cube D t hi]; ring
  | QK =>
    refine sum_congr rfl fun x _ => ?_
    simp only [Ct_cube D hi, St_cube D hi, AYU_cube D t hi, term, Y']
  | XR =>
    show valU D t .sc (l / 2) 0 (Blocks.cubePt D.lT i) *
      ∑ x ∈ range D.d, ew D z .XR x * valU D t .m l x (Blocks.cubePt D.lT i) =
      ∑ x ∈ range D.d, ew D z .XR x * (val t .sc (l / 2) 0 i * val t .m l x i)
    rw [valU_cube D t hi, mul_sum]
    exact sum_congr rfl fun x _ => by rw [valU_cube D t hi]; ring
  | DD =>
    show sw D z .DD * ∑ e ∈ range D.nx, valU D t .sel (l / 2) e (Blocks.cubePt D.lT i) *
      valU D t .lr (l / 2) e (Blocks.cubePt D.lT i) =
      ∑ x ∈ range D.nx, ew D z .DD x * mr D t (l / 2) i
    simp only [valU_cube D t hi]
    rw [← sum_mul]
    rfl
  | MR =>
    show ew D z .MR 0 * ∑ e ∈ range D.nx, valU D t .sel (l / 2) e (Blocks.cubePt D.lT i) *
      valU D t .lr (l / 2) e (Blocks.cubePt D.lT i) =
      ∑ x ∈ range 1, ew D z .MR x * mr D t (l / 2) i
    simp only [valU_cube D t hi]
    rw [sum_range_one]
    rfl
  | G =>
    show (if isExpL l then Inst.Model.Site.scl (D.Pl l).kg'
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e (Blocks.cubePt D.lT i) *
          ∑ j ∈ range D.d, valU D t .xr (l / 2) j (Blocks.cubePt D.lT i) *
            ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w l).Eg e j x) else 0) =
      ∑ x ∈ range D.f, ew D z .G x *
        (if routed D l x then Inst.Model.Site.scl (D.Pl l).kg' (Ag D t w l x i) else 0)
    simp only [valU_cube D t hi]
    by_cases he : isExpL l = true
    · have r0 : ∀ x, x < D.fe → routed D l x = false := fun x hx => by
        simp [routed, he, Nat.not_le.mpr hx]
      have r1 : ∀ x, routed D l (D.fe + x) = true := fun x => by simp [routed, he]
      rw [if_pos he, hff, sum_tail D.fe D.fe _ fun x hx => by simp [r0 x hx], ← tri_in]
      refine sum_congr rfl fun x _ => ?_
      simp only [r1 x, if_true, Ag, Nat.add_sub_cancel_left]
    · have r0 : ∀ x, routed D l x = false := fun x => by simp [routed, he]
      rw [if_neg he]
      exact (sum_eq_zero fun x _ => by simp [r0 x]).symm
  | U =>
    show (if isExpL l then Inst.Model.Site.scl (D.Pl l).ku'
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e (Blocks.cubePt D.lT i) *
          ∑ j ∈ range D.d, valU D t .xr (l / 2) j (Blocks.cubePt D.lT i) *
            ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w l).Eu e j x) else 0) =
      ∑ x ∈ range D.f, ew D z .U x *
        (if routed D l x then Inst.Model.Site.scl (D.Pl l).ku' (Au D t w l x i) else 0)
    simp only [valU_cube D t hi]
    by_cases he : isExpL l = true
    · have r0 : ∀ x, x < D.fe → routed D l x = false := fun x hx => by
        simp [routed, he, Nat.not_le.mpr hx]
      have r1 : ∀ x, routed D l (D.fe + x) = true := fun x => by simp [routed, he]
      rw [if_pos he, hff, sum_tail D.fe D.fe _ fun x hx => by simp [r0 x hx], ← tri_in]
      refine sum_congr rfl fun x _ => ?_
      simp only [r1 x, if_true, Au, Nat.add_sub_cancel_left]
    · have r0 : ∀ x, routed D l x = false := fun x => by simp [routed, he]
      rw [if_neg he]
      exact (sum_eq_zero fun x _ => by simp [r0 x]).symm
  | D =>
    show (if isExpL l then Inst.Model.Site.scl (D.Pl l).kd
        (∑ e ∈ range D.nx, valU D t .sel (l / 2) e (Blocks.cubePt D.lT i) *
          ∑ j ∈ range D.fe, hhU D t l (D.fe + j) (Blocks.cubePt D.lT i) *
            ∑ x ∈ range D.d, ew D z .D x * (w l).Ed e j x) else 0) =
      ∑ x ∈ range D.d, ew D z .D x *
        (if isExpL l then Inst.Model.Site.scl (D.Pl l).kd
          (∑ e ∈ range D.nx, val t .sel (l / 2) e i *
            ∑ j ∈ range D.fe, hh t l (D.fe + j) i * (w l).Ed e j x) else 0)
    simp only [valU_cube D t hi, hhU_cube D t hi]
    by_cases he : isExpL l = true
    · simp only [if_pos he]
      rw [← tri_in]
    · simp only [if_neg he, mul_zero, sum_const_zero]
  | _ =>
    exact (sum_eq_zero fun x _ => mul_zero _).symm

/-- Gpos at a vertex of the cube: the products in the keys at that position, under all weights. -/
theorem gpos_cube (hf : D.f = 2 * D.fe) {i : ℕ} (hi : i < 2 ^ D.lT) :
    Gpos D t tb L0 w z (Blocks.cubePt D.lT i) =
      ∑ c, wc D z c * ∑ l ∈ range D.nl, el D z c l *
        ((famsIn c l).map fun s => TERM D t tb L0 w z s l i).sum := by
  unfold Gpos
  simp only [hat_cube D t tb L0 w z hf _ _ hi]

/-- The claim with which the sumcheck over the positions begins: the honest value of the masked
scalar Cl, the products in all keys under all weights, is the sum over the cube of Gpos under the
equality weights of the lookup's token point. -/
theorem clT_gpos (hf : D.f = 2 * D.fe) :
    ClT D t tb L0 w z =
      Blocks.ext D.lT (fun i => Gpos D t tb L0 w z (Blocks.cubePt D.lT i)) (zpos D z) := by
  rw [Blocks.ext_congr (fun i hi => gpos_cube D t tb L0 w z hf hi) (zpos D z), Blocks.ext_sum]
  unfold ClT TS
  exact sum_congr rfl fun c _ => (Blocks.ext_smul _ _ _ _).symm

end Hat

#print axioms hat_cube
#print axioms gpos_cube
#print axioms clT_gpos

end Cb.Pv.Lay.End.Sig
