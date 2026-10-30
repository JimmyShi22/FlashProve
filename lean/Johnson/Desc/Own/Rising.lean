-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/Rising.lean: one small test on a list of numbers, as a named part of the
description, for every block that asks that the numbers of messages stand in rising order.

  rising l
      EACH NUMBER IS ABOVE THE ONE BEFORE IT. The empty list and a list of one number rise.
How far the text is its own: not far: it is the format's library's Fmt.increasing (Fmt/Rules8.lean)
taken over token for token under a new name. It adds no second, independent eye.
Nothing of another file is called.
That it says just what Fmt.increasing says, at all arguments, and what it checks in plain terms (of
any two places of the list the later holds the greater number), is stated in theorems beside, in
Johnson/Desc/Own/RisingAgree.lean, which no block imports.
No theorem here. Nothing on soundness.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

/-- Each number is above the one before it. -/
def rising : List Nat → Bool
  | a :: b :: l => a < b && rising (b :: l)
  | _ => true

end VerifiableInference.Desc.Own
