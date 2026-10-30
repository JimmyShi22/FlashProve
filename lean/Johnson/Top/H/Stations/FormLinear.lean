-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Stations/FormLinear.lean: the coefficients that a change of shape carries are linear
in the form; and a sum over all names of a finite type, under coefficients that are the powers of
one element along a list of all names, is the sum under the powers along the list.

Statements and proofs; no definition.


Main names:
  fm_eq: under the laws of a change of shape (Reshape.Laws, Cb/Ld/LdBatShape.lean) a carried
    coefficient is a fixed linear combination of the form's coefficients.
  fm_sum: so the carried form of a combination is the combination of the carried forms.
  sum_powers: the sum over all names.

What is not claimed: nothing on any shape or code.
-/
import Cb.Ld.LdBatShape
import Johnson.Top.H.BatTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.Stations.TestHead
open Cb OnBytes

section Fm
variable {E P : Type} [Field E] {C C' : LdCode E P} (ρ : Reshape C C')

/-- A carried coefficient is a fixed linear combination of the form's coefficients. -/
theorem fm_eq (h : ρ.Laws) (a : C.J → E) (j : C'.J) :
    ρ.fm a j = ∑ i, a i * (ρ.dn (Pi.single j 1, 0)).1 i := by
  have e := h.val a (Pi.single j 1, 0)
  rw [← e]
  simp [Pi.single_apply]

/-- The carried form of a combination is the combination of the carried forms. -/
theorem fm_sum (h : ρ.Laws) {B : Type} [Fintype B] (c : B → E) (v : B → C.J → E) (j : C'.J) :
    ρ.fm (fun i => ∑ b, v b i * c b) j = ∑ b, c b * ρ.fm (v b) j := by
  rw [fm_eq ρ h]
  simp only [fm_eq ρ h (v _), Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end Fm

/-- A sum over all names, under coefficients that are the powers of y along a list of all names. -/
theorem sum_powers {ι K : Type} [Fintype ι] [CommRing K] (w v : ι → K) (y : K) (l : List ι)
    (hn : l.Nodup) (hall : ∀ ν, ν ∈ l) (hw : ∀ i (h : i < l.length), w l[i] = y ^ i) :
    ∑ ν, w ν * v ν = hornerSum y (l.map v) := by
  classical
  have e2 : (Finset.univ : Finset ι) = l.toFinset := by
    ext ν
    simp [hall ν]
  rw [e2, List.sum_toFinset _ hn,
    VerifiableInference.OnPublicFiles.BatFoldAt.sum_horner w v y l 0
      (fun i hi => by rw [hw i hi, Nat.zero_add]), pow_zero, one_mul]

end KObj.Stations.TestHead
