-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ShapesOk.lean: statements with their proofs; no definition.

What is here. The library's test on a masked sumcheck's call (`shapeOk`,
Johnson/Desc/Part/MaskedSum4.lean) accepts the three kinds of shape of Honest/K4/CubeJob.lean.

  `shapeOk_level`, `shapeOk_token`, `shapeOk_plain`   the three kinds of shape

Limits. A plain or a token sumcheck's shape: where its degree in the further variable and its number
of end values are at least 1. That the row's own numbers are at least 1 is not said here.

Kin. The library has like laws, and this file builds on none of those that are named here. The
nearest of these: `shapeOk_point` (Honest/K6/Law/Segs.lean), on `pointShape lead n ends`
(Honest/K6/Part.lean): any lead, n variables each summed at the point 0 with three coefficients a
round, degree 2 in the further variable, where there is an end value. By reading: `k4LevelShape mu`
has the body of `pointShape 0 mu 2`, and `k4TokenShape lt 2 n` that of `pointShape 1 lt n`: so this
file's first statement, and its second at the degree 2, are cases of that law. `shapeOk_level`
(Honest/K3/Shape/ReturnsAtoms.lean), under the same short name, for the lookup's product level: the
same lead, degrees and ends, at every point; the same statement stands again as `level_shapeOk`
(Johnson/Desc/First/ProdV/LevelKit.lean). Among others, at points that are letters: `shape_callOf`
(Johnson/Desc/Kinds/Law/Returns.lean: any lead, degree 2, where there is an end value),
`shapeOk_callOf` (Johnson/Top/H/P1Tie/Tie2.lean: no lead; the degree and the number of end values
each from 1 on); at variables that are summed plainly, four coefficients a round: `shapeOk_products`
(Johnson/Desc/First/Att/K05MetWit.lean: no lead, degree 2, an even number of end values that is not
0). By statement, to the letter and up to the bound letters: no hit; these were found by the test's
name.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.CubeJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc.Part.MaskedSum (shapeOk)

/-- A product level's shape is accepted. -/
theorem shapeOk_level (mu : Nat) : shapeOk (k4LevelShape mu) = true := by
  simp [shapeOk, k4LevelShape, VerifiableInference.Desc.Part.MaskedSum.Var.d]

/-- A token sumcheck's shape is accepted, where its degree in the further variable and its number of
end values are at least 1. -/
theorem shapeOk_token (lt : Nat) {dY n : Nat} (h1 : 1 ≤ dY) (hn : 1 ≤ n) :
    shapeOk (k4TokenShape lt dY n) = true := by
  simp [shapeOk, k4TokenShape, VerifiableInference.Desc.Part.MaskedSum.Var.d, h1, hn]

/-- So is a plain sumcheck's. -/
theorem shapeOk_plain (lam : Nat) {dY n : Nat} (h1 : 1 ≤ dY) (hn : 1 ≤ n) :
    shapeOk (k4PlainShape lam dY n) = true := by
  simp [shapeOk, k4PlainShape, VerifiableInference.Desc.Part.MaskedSum.Var.d, h1, hn]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shapeOk_level
#print axioms ProofFile.Honest.K4.shapeOk_token
#print axioms ProofFile.Honest.K4.shapeOk_plain
