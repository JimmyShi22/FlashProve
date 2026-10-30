-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge.lean: one import for the proof of the statement on agreement of Reed-Solomon codes below
the Johnson radius. After "import Cb.Bridge" these are at hand:
  `Cb.Gl.bchks46At : Cb.BCHKS46At Cb.Gl.F Cb.Gl.E` (Cb/Bridge/GlCodesProved.lean)
  `Cb.Bridge.bchks46At : ∀ F E …, Cb.BCHKS46At F E` and `Cb.Bridge.bchks46 : Cb.BCHKS46`
  (Cb/Bridge/CodeListRSProved.lean)
The proof rests on the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).

-/
import Cb.Bridge.CodeListRSFromLines
import Cb.Bridge.CodeListRSProved
import Cb.Bridge.GlCodesProved
import Cb.Bridge.GlCodesProvedCheck
