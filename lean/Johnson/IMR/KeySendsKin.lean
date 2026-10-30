-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeySendsKin.lean: A RIGHTING: IM.oneSend (IMR/KeySendsOne.lean) IS A TWIN OF THE
LIBRARY's Johnson.G.oneOf (Johnson/G/SendsListed.lean: «sendsFrom's inner routine "one", by name:
its text»). Here Lean says that the two are one, by
rfl, so that whoever holds a fact on one has it on the other.
One theorem. No soundness.
-/
import Johnson.IMR.KeySendsOne
import Johnson.G.SendsListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

theorem oneSend_is_oneOf : @oneSend = @Johnson.G.oneOf := rfl

end IM

#print axioms IM.oneSend_is_oneOf
