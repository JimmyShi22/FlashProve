-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Asks Lean which axioms the two theorems adapted from ArkLib depend on. The build fails unless the
answer is propext, Classical.choice and Quot.sound, Lean's three standard axioms. So neither theorem
rests on an unfinished proof.
-/
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds

/--
info: 'ReedSolomon.exists_johnson_line_exactCorrelatedPair' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.exists_johnson_line_exactCorrelatedPair

/--
info: 'ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate
