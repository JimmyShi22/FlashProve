-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Coord.lean: the three coordinates of an element of the extension field GE over
the base field GF are additive, a factor from GF passes through each of them, and a coordinate of a
product is a linear form over GF in the coordinates of the second factor.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model"; Johnson/SendSim/At/Sim.lean, "Terms". Limits
of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for the library's two fields, by algebra.
  crd, crdHom         coordinate t of an element of GE; the same as an additive map.
  crd_add, crd_zero, crd_sum   crd t is additive.
  crd_cast            Of an element a of GF, cast into GE, coordinate 0 is a and the others are 0.
  crd_cast_mul        crd t (a * y) = a * crd t y for a in GF.
  ext_crd             Two elements with the same three coordinates are equal.
  against_crd         An element is the sum of its coordinates times 1, θ, θ² (against,
                      Johnson/SendSim/Tie/Basis.lean).
  crd_against         Coordinate t of such a sum is entry t of the triple.
  crd_mul             crd s (w * y) = Σ_t crd s (w * θ^t) * crd t y.

How it fits. The instance of the general model (Johnson/SendSim/At/Bridge.lean) reads a row, a coin
or an answer over GE as three over GF, by crd. Most files of Johnson/SendSim/At/ on the passage to
the model use these lemmas, and so does Johnson/SendSim/Tie/SymF.lean; crd_mul gives the instance's
weights (Johnson/SendSim/At/Answers.lean). That serves rowsExact and rowsFresh. crdHom and
against_crd are used only in this file.
-/
import Johnson.SendSim.Tie.Basis

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes OnBytes.Slice

/-- Coordinate t of an element of GE over GF. -/
def crd (t : Fin 3) (y : GE) : GF := ![y.c0, y.c1, y.c2] t

theorem crd_add (t : Fin 3) (y y' : GE) : crd t (y + y') = crd t y + crd t y' := by
  fin_cases t <;> rfl

theorem crd_zero (t : Fin 3) : crd t 0 = 0 := by
  fin_cases t <;> rfl

/-- Coordinate t as an additive map from GE to GF. -/
def crdHom (t : Fin 3) : GE →+ GF where
  toFun := crd t
  map_zero' := crd_zero t
  map_add' := crd_add t

theorem crd_sum {ι : Type} (t : Fin 3) (s : Finset ι) (f : ι → GE) :
    crd t (∑ i ∈ s, f i) = ∑ i ∈ s, crd t (f i) := map_sum (crdHom t) f s

/-- A factor a from GF passes through a coordinate: crd t (a * y) = a * crd t y. -/
theorem crd_cast_mul (t : Fin 3) (a : GF) (y : GE) :
    crd t (algebraMap GF GE a * y) = a * crd t y := by
  fin_cases t <;> simp [crd]

theorem crd_cast (t : Fin 3) (a : GF) : crd t (algebraMap GF GE a) = if t = 0 then a else 0 := by
  fin_cases t <;> simp [crd]

/-- Two elements of GE with the same three coordinates are equal. -/
theorem ext_crd {y y' : GE} (h : ∀ t, crd t y = crd t y') : y = y' :=
  Code.Cubic.ext (h 0) (h 1) (h 2)

theorem crd_against (t : Fin 3) (a : Fin 3 → GF) : crd t (against a) = a t := by
  rw [against_eq]
  fin_cases t <;> rfl

theorem against_crd (y : GE) : against (fun t => crd t y) = y :=
  ext_crd fun t => crd_against t _

/-- Coordinate s of a product w * y is a linear form over GF in the coordinates of y, with the
weights crd s (w * θ^t). -/
theorem crd_mul (s : Fin 3) (w y : GE) :
    crd s (w * y) = ∑ t : Fin 3, crd s (w * readE (thetaE t.val)) * crd t y := by
  conv_lhs => rw [← against_crd y]
  unfold against
  rw [Finset.mul_sum, crd_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show w * (algebraMap GF GE (crd t y) * readE (thetaE t.val)) =
    algebraMap GF GE (crd t y) * (w * readE (thetaE t.val)) by ring, crd_cast_mul, mul_comm]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.crd_sum
#print axioms OnBytes.SendSim.crd_cast_mul
#print axioms OnBytes.SendSim.against_crd
#print axioms OnBytes.SendSim.crd_mul
