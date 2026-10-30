-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Stands in for two names of the package CompPoly (https://github.com/Verified-zkEVM/CompPoly, module
CompPoly.ToMathlib.Polynomial.BivariateDegree): Polynomial.Bivariate.degreeX and
Polynomial.Bivariate.coeff_natDegree_le_degreeX.

ArkLib imports the two names from CompPoly. Three theorems in ThirdParty/ArkLib name them.
Polynomial.natDegree_resultant_derivative_padded_le and
PolynomialDifferential.degreeX_ordinaryRootPresentation_le have degreeX in their statements, and
PolynomialDifferential.exists_exceptional_jet_independent_content uses the lemma in its proof.
The names are CompPoly's. The definition and the proof below are written for this library: degreeX
is the degree in the inner variable, that is, the largest natDegree among the coefficients. The
proofs of the three theorems go through with it. Neither name occurs in the statements of the two
theorems that ThirdParty/ArkLibCheck/Axioms.lean names.
-/
import Mathlib.Algebra.Polynomial.Degree.Defs

noncomputable section

namespace Polynomial.Bivariate

/-- The degree in the inner variable of a polynomial whose coefficients are polynomials:
the largest `natDegree` among its coefficients (0 for the zero polynomial). -/
def degreeX {R : Type*} [Semiring R] (f : Polynomial (Polynomial R)) : ℕ :=
  f.support.sup fun n => (f.coeff n).natDegree

/-- Every coefficient has `natDegree` at most `degreeX`. -/
theorem coeff_natDegree_le_degreeX {R : Type*} [Semiring R] (f : Polynomial (Polynomial R))
    (n : ℕ) : (f.coeff n).natDegree ≤ degreeX f := by
  by_cases h : f.coeff n = 0
  · simp [h]
  · exact Finset.le_sup (f := fun n => (f.coeff n).natDegree) (mem_support_iff.mpr h)

end Polynomial.Bivariate
