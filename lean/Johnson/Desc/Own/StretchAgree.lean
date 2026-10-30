-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/StretchAgree.lean: `weightsOnRows` (Johnson/Desc/Own/Stretch.lean) returns what the
program `verify-on-bytes`'s memberWeightsOnRows returns, at all arguments; and just when it returns
something, as a proposition in plain terms. Statements and proofs. No block's text imports this
file.
  `weightsOnRows_agrees`: the equation.
  `weightsOnRows_isSome_iff`: it returns something exactly if the stretch is inside the matrix, the
    matrix has fewer than 63 row variables, the stretch is inside the cube, and the blocks' numbers
    of rows add up to the number of weights.
  `weightsOnRows_some`: what it returns is then the list of blocks.

-/
import Johnson.Desc.Own.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes OnBytes.Params

theorem weightsOnRows_agrees (S : LinShape) (first : Nat) (values : Array E) :
    memberWeightsOnRows S first values = weightsOnRows S first values := rfl

theorem weightsOnRows_isSome_iff (S : LinShape) (first : Nat) (values : Array E) :
    (weightsOnRows S first values).isSome = true ↔
      first + values.size ≤ S.matrixRows ∧ S.kRow < 63 ∧ first + values.size ≤ 2 ^ S.kRow ∧
        ((stretchBlocks S.kRow first values (2 * S.kRow + 2) first).map
          fun t => 2 ^ t.denseVars.length).sum = values.size := by
  unfold weightsOnRows
  by_cases h1 : first + values.size ≤ S.matrixRows
  · by_cases h2 : S.kRow < 63
    · by_cases h3 : first + values.size ≤ 2 ^ S.kRow
      · by_cases h4 : ((stretchBlocks S.kRow first values (2 * S.kRow + 2) first).map
          fun t => 2 ^ t.denseVars.length).sum = values.size
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]
      · simp [h1, h2, h3]
    · simp [h1, h2]
  · simp [h1]

theorem weightsOnRows_some {S : LinShape} {first : Nat} {values : Array E} {g : List Tensor}
    (h : weightsOnRows S first values = some g) :
    g = stretchBlocks S.kRow first values (2 * S.kRow + 2) first := by
  unfold weightsOnRows at h
  split at h
  · split at h
    · dsimp only at h
      split at h
      · exact (Option.some.inj h).symm
      · cases h
    · cases h
  · cases h

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.weightsOnRows_agrees
#print axioms VerifiableInference.Desc.Own.weightsOnRows_isSome_iff
#print axioms VerifiableInference.Desc.Own.weightsOnRows_some
