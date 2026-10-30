-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Small.lean: thirteen names of the namespace ProofFile.Honest.K5 that
stand for the declarations of the same spelling in ProofFile.Honest.Small (Honest/Small/Plays.lean):
twelve laws on the frame's `play` at a part whose moves say scalars, and the definition
`scalarsSaid`. No statement, no proof and no definition stands here: one line `export`. Why: the
callers in this folder write these names short, and their texts stay.

Limits. A name below is no declaration: a list of declared names has it under ProofFile.Honest.Small
alone. What each law says, its premises and its Limits stand in Honest/Small/Plays.lean.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.Plays

namespace ProofFile.Honest.K5

export ProofFile.Honest.Small (lensBy_length plays_said plays_lift_said quietPart_moves lensBy_quiet
  outOf_quiet plays_quiet plays_lift_quiet scalarsSaid scalarsPart_moves scalarsSaid_length
  plays_scalars plays_lift_scalars)

end ProofFile.Honest.K5
