-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/CoreNarrowGuards.lean: the two tests of `linesB` beyond `frontFiveB` at
the closed narrow shape `narrowW` (WNarrowAtW.lean), by Lean's evaluator: two lines, two controls.

Limits. Evaluated lines, no theorem. Nothing on a run. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrow
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WNarrowLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreShapes
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontFile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open H2K.Member (piWFull)
open ProofFile.Honest.K12.AtProof (treesW)
open ProofFile.Honest.K12.Light (manyFitsS tsLenOf)

-- THE LINES. Foretold: yes.
#guard manyFitsS piWFull memsW (treesW piWFull) ⟨narrowW, 0, .nothing, some 198⟩
#guard tsLenOf piWFull ⟨narrowW, 0, .nothing, some 198⟩ == 3

-- CONTROLS. Foretold: no.
#guard !manyFitsS piWFull memsW.reverse (treesW piWFull) ⟨narrowW, 0, .nothing, some 198⟩
#guard tsLenOf piWFull ⟨narrowW, 1, .nothing, some 198⟩ != 3

end ProofFile.Honest.K12.AtFile
