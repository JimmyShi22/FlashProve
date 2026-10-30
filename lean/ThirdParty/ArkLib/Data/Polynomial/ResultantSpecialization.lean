/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/ResultantSpecialization.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 6 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultants with declared degrees under coefficient specialization

Let `φ : R →+* S` be a ring homomorphism and let `f, g : R[X]` have degrees at most `m` and `n`.
This file relates the value `φ (resultant f g m n)` to common roots, coprimality, and
separability of the mapped polynomials `f.map φ` and `g.map φ`. The declared degrees `m` and `n`
are fixed before `φ` is applied, so `φ` may lower the actual degree of `f` or `g`.

## Main statements

* `map_resultant_eq_zero_of_common_root`: a common root of `f.map φ` and `g.map φ` forces
  `φ (resultant f g m n) = 0`. Both `R` and `S` are arbitrary commutative rings.
* `eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`: if
  `φ (resultant f f.derivative m (m - 1)) ≠ 0`, every root of `f.map φ` is a simple root.
* `natDegree_map_eq_of_resultant_derivative_padded_ne_zero`: the same hypothesis forces
  `(f.map φ).natDegree = m`. A specialization that lowers the degree of `f` therefore makes the
  padded derivative resultant vanish.
* `isCoprime_map_of_resultant_padded_ne_zero` and
  `separable_map_of_resultant_derivative_padded_ne_zero`: over a field target, a nonzero image of
  the resultant gives coprimality, and a nonzero image of the padded derivative resultant gives
  separability.
* `resultant_comm_sub_one`: `resultant g f (m - 1) m = resultant f g m (m - 1)`.

## Proof outline

Mathlib's `exists_mul_add_mul_eq_C_resultant` gives `p, q : R[X]` with
`f * p + g * q = C (resultant f g m n)`, provided `f.natDegree ≤ m`, `g.natDegree ≤ n` and
`m ≠ 0 ∨ n ≠ 0`. Mapping this identity through `φ` and evaluating at a common root gives the
first statement. Mapping it into a field and multiplying by the inverse of the constant gives
coprimality. The derivative statements take `g = f.derivative` and `n = m - 1`, which is a valid
degree bound because `f.derivative.natDegree ≤ f.natDegree - 1`. The bound need not be attained:
in characteristic `p` the derivative of `Y ^ p - Y` is `-1`. The actual-degree forms
`isCoprime_map_of_resultant_ne_zero` and `separable_map_of_resultant_derivative_ne_zero` in
`ArkLib.Data.Polynomial.FractionFieldResultant` are derived from the declared-degree forms here.
-/

namespace Polynomial

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K] {m n : ℕ}

/-- A common root of `f.map φ` and `g.map φ` forces `φ (resultant f g m n) = 0`.

The hypotheses `hf` and `hg` bound the degrees of `f` and `g` before `φ` is applied. They are
the hypotheses of the Bezout identity `f * p + g * q = C (resultant f g m n)`. The map `φ` may
lower either degree, including to `0`, and `m`, `n` stay fixed. The hypothesis `hmn` cannot be
dropped: `resultant f g 0 0 = 1`, since the Sylvester matrix is empty, but `f = g = 0` has every
point as a common root. `R` and `S` need not be domains or nontrivial; in the zero ring the
conclusion holds trivially. -/
theorem map_resultant_eq_zero_of_common_root (φ : R →+* S) (f g : R[X])
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) (u : S)
    (hfu : (f.map φ).eval u = 0) (hgu : (g.map φ).eval u = 0) :
    φ (resultant f g m n) = 0 := by
  obtain ⟨p, q, -, -, hbezout⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have heval := congrArg (fun r : R[X] ↦ (r.map φ).eval u) hbezout
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, eval_add, eval_mul, eval_C, hfu, hgu,
    zero_mul, add_zero] at heval
  exact heval.symm

/-- If `φ (resultant f f.derivative m (m - 1)) ≠ 0`, every root `u` of `f.map φ` is a simple
root: the derivative of `f.map φ` does not vanish at `u`.

`hf` makes `m` a degree bound for `f`, and then `m - 1` is a degree bound for `f.derivative`.
`hm` is needed because for `m = 0` the resultant is `1`: a constant `f` with `φ (f.coeff 0) = 0`
maps to `0`, whose derivative vanishes everywhere. The derivative may have degree below `m - 1`,
as in small characteristic, where the derivative of `Y ^ p - Y` is `-1`. If `φ` lowers the
degree of `f` itself, the hypothesis `hres` fails
(`natDegree_map_eq_of_resultant_derivative_padded_ne_zero`). The zero polynomial has a vanishing
resultant for `0 < m`, so it is excluded by `hres`. `R` and `S` are arbitrary commutative rings.
-/
theorem eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (φ : R →+* S)
    (f : R[X]) (hf : f.natDegree ≤ m) (hm : 0 < m)
    (hres : φ (resultant f f.derivative m (m - 1)) ≠ 0) (u : S)
    (hfu : (f.map φ).eval u = 0) : (f.map φ).derivative.eval u ≠ 0 := by
  intro hderivative
  refine hres (map_resultant_eq_zero_of_common_root φ f f.derivative hf
    ((natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)) (Or.inl hm.ne') u hfu ?_)
  rwa [← derivative_map]

end Polynomial
