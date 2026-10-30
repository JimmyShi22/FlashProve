-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/KeyMaps.lean: the two kinds of maps of step 18 of an attention segment are the
library's rule values of its end values.

The summand of step 18 (Phi18 in Inst/Model/Att/Sums.lean) is written on two kinds of maps of the
point ξ = (X_j | X_g | X_i): for each layer the extension of the keys, contracted over the channels,
at (X_g | X_j); and for each pair and bit the extension of that bit of the index at (X_g | X_i). The
library's rule values of the sumcheck's end values (rvKC, rvIBP in Inst/Model/Att/KeyForms.lean) are
reads of the same arrays. This file shows that they are the same polynomials in the point.

Main theorems: gi_rd2 (the extension of an array over the cube (g | i) is its read), rd2_agree,
rvIBP_ext, rvKC_ext.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] (D : Dim)

/-- The extension of an array over the cube (g | i) is the read of the array. -/
theorem gi_rd2 (a : ℕ → ℕ → E) (ξ : ℕ → E) :
    Blocks.ext (D.lg + D.lT) (fun X => a (X / D.T) (X % D.T)) ξ =
      rd2 D ξ (eqT D (sh ξ D.lg)) a := by
  rw [ext_two]
  unfold rd2 eqT
  rw [D.T_eq]
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi => ?_
  have e := Dim.div_step (a := g) (Nat.two_pow_pos D.lT) (mem_range.mp hi)
  rw [e.1, e.2, eqN_sh]

/-- Two reads agree if their points agree on the coordinates that are read. -/
theorem rd2_agree {vg vg' vi vi' : ℕ → E} (hg : ∀ k < D.lg, vg k = vg' k)
    (hi : ∀ k < D.lT, vi k = vi' k) (a : ℕ → ℕ → E) :
    rd2 D vg (eqT D vi) a = rd2 D vg' (eqT D vi') a := by
  unfold rd2 eqT
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [eqN_agree (a := vg) (a' := vg') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g,
    eqN_agree (a := vi) (a' := vi') (off := 0) (off' := 0)
      (fun k hk => by rw [Nat.zero_add]; exact hi k hk) i]

variable (p : Pub E) (t : Raw → E)

/-- **The rule value of the end value for a bit is step 18's map of that bit.** -/
theorem rvIBP_ext (pt : ℕ → E) (b k : ℕ) :
    rvIBP D t pt b k =
      Blocks.ext (D.lg + D.lT) (fun X => ibV t k b (X / D.T) (X % D.T)) (sh pt D.lT) := by
  rw [gi_rd2]
  exact rd2_agree D (fun _ _ => rfl) (fun j _ => by
    show pt (D.lT + D.lg + j) = pt (D.lT + (D.lg + j))
    rw [Nat.add_assoc]) _

/-- **The rule value of the end value of a layer is step 18's map of the layer's keys.** -/
theorem rvKC_ext (pt : ℕ → E) (lam : ℕ) :
    rvKC D p t pt lam =
      Blocks.ext (D.lg + D.lT) (kc D p t lam) (cat D.lg (sh pt D.lT) pt) := by
  have e : kc D p t lam = fun X => (fun g j => conN D p.fn fun n => keyV t lam g j n)
      (X / D.T) (X % D.T) := rfl
  rw [e, gi_rd2 D (fun g j => conN D p.fn fun n => keyV t lam g j n),
    rd2_agree D (vg' := sh pt D.lT) (vi' := pt)
    (fun k hk => by simp only [cat, if_pos hk])
    (fun k _ => by
      show cat D.lg (sh pt D.lT) pt (D.lg + k) = pt k
      have e1 : ¬ D.lg + k < D.lg := by omega
      have e2 : D.lg + k - D.lg = k := by omega
      simp only [cat, if_neg e1, e2])]
  unfold rvKC rd3 rd2 conN
  refine sum_congr rfl fun g _ => sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.rvIBP_ext
#print axioms Cb.Pv.Att.rvKC_ext
