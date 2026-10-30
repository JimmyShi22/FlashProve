-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkLinkSeatToy.lean: a shape of the one tree of the link's message, at the small test
configuration.

OnBytes/Slice/BlkLinkSeat.lean says where the oracle messages of the link's one message sit in the
book of trees, if that message is put in one tree. `toyLinkTree` is a tree of 2^13 leaves, with 12,
12 and 0 words of main rows and 0, 0 and 3 words of mask rows in a column.



Main definition: `toyLinkTree`.
Not claimed. Nothing for other parameter bytes.
-/
import OnBytes.Slice.BlkLinkSeat
import OnBytes.Slice.BlkToySizes

set_option autoImplicit false

namespace OnBytes.Slice

open Params (LinkShape)

/-- The shape of the one tree of the link's message at the small test configuration. -/
def toyLinkTree : TreeShape :=
  { logN := 13, logNzk := 13, mainSymbols := #[12, 12, 0], maskSymbols := #[0, 0, 3] }

end OnBytes.Slice

