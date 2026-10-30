-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FitsA.lean: THE FIRST CHAIN FITS, AT THE WRITTEN VALUES. Calls alone.

`fits_A`: `ChainFits keySends0 keyThree.A.plan.plan [] 1` (TreesKOfRounds.lean), of `offset_A`,
`rounds_A`, `roots_A`, `below_A` and `sent_keySends0`
(Johnson/AtFull/KeyBack/SentKey.lean): `sentAt` returns at each of the chain's six written
sendings.
Limits. It names no m and no public file: that the written values are the planner's at any public
files is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.RoundsA
import Johnson.AtFull.KeyBack.OffsetA
import Johnson.AtFull.KeyBack.BelowA
import Johnson.AtFull.KeyBack.RootsA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G (keySends0)
open VerifiableInference.Number.ByRuns (keyThree)

theorem fits_A : ChainFits keySends0 keyThree.A.plan.plan [] 1 :=
  ⟨offset_A, sent_keySends0 "" 1, by rw [rounds_A]; exact roots_A,
    by rw [rounds_A]; exact below_A⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.fits_A
