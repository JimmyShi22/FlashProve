-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/TailBend.lean: THE TAIL: FOR TESTS ALONE (only CT6id.lean, CT6p1.lean,
CT6p2.lean and CT6p5.lean import it): a function that bends the first code-switch call in a list of
noted calls: its target group and its cube's bits. One definition. A law file; no running text
imports it. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.TailAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- The first code-switch call of the list, with f at its target group and its cube's bits. -/
def bendCs (f : GroupSize → Nat → GroupSize × Nat) : List Call → List Call
  | [] => []
  | .cs x y cube a b c :: t => .cs x (f y cube).1 (f y cube).2 a b c :: t
  | h :: t => h :: bendCs f t

end VerifiableInference.Desc.LinkJoin
