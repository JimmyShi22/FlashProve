-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/BlockAtEq.lean: two names of one term: the first chain's block of a proof file as
the program's check lays it is written once in OnBytes/Maker/GoodProof.lean (`blockAt`) and once in
Johnson/Maker/Page/BlockCall.lean (`firstBlockOf`). They are the same, by unfolding.

-/
import OnBytes.Maker.GoodProof
import Johnson.Maker.Page.BlockCall

set_option autoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Maker

/-- One term under two names. -/
theorem blockAt_eq (p : Model.Verify.Planned) (links : Array Model.Stages.LinkH) (y : ℕ) :
    blockAt p links y = firstBlockOf p links y := rfl

end Johnson.Session
